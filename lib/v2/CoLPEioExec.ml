
module LP = CoLPSignature.CoLPSignature 

open Eio.Std


(* let isLazy = false *)
let isLazy = true
let default_depth = 10
(* let use_multi_domain = true *)
let use_multi_domain = false
let use_multi_thread = true
(* let use_multi_thread = false *)

module ELPromise = struct
    type 'a promise = 'a Eio.Promise.t * 'a Eio.Promise.u
    type 'a t = Lazy of {
        request : unit promise;
        requested : bool ref;
        requeted_lock : Eio.Mutex.t;
        response : 'a promise;
    } | Eager of 'a promise


    let create_eager () : 'a t = 
        let (await, resolve) = Eio.Promise.create () in
        Eager (await, resolve)
    let create_lazy () : 'a t = 
        Lazy { request = Eio.Promise.create (); response = Eio.Promise.create () ;
        requested = ref false; requeted_lock = Eio.Mutex.create();
        }

    let create () : 'a t = 
        if isLazy then
            create_lazy ()
        else
            create_eager ()

    let await (p : 'a t) : 'a = 
        match p with
        | Eager (await, _) -> Eio.Promise.await await
        | Lazy { request = (_, resolve); response = (await, _) ; requested; requeted_lock } -> 
            (* if awaiting on lazy, first signal that this has been requested *)
                (
                    Eio.Mutex.lock requeted_lock;
                    if not !requested then (Eio.Promise.resolve resolve ();
                    requested := true;
                    );
                    Eio.Mutex.unlock requeted_lock;
                ) ;
            Eio.Promise.await await

    let wait_if_lazy (p : 'a t) : unit = 
        match p with
        | Eager _ -> ()
        | Lazy { request = (await, _); response = _ ; _} -> 
            (* if wait until someone awaits on this promise *)
            Eio.Promise.await await

    let resolve (p : 'a t) (v : 'a) : unit = 
        match p with
        | Eager (_, resolve) -> Eio.Promise.resolve resolve v
        | Lazy { response = (_, resolve); _ } -> Eio.Promise.resolve resolve v

end

type rt_data = 
    | Pending of rt_data ELPromise.t
    | Ap of string * rt_data 
    | Unit
    | Pair of rt_data * rt_data

let rec show_rt_data (rt_data_p : rt_data) : string = 
    match rt_data_p with
    | Pending _ -> "Pending"
    | Ap (s, arg) -> "(" ^ s ^ " " ^ show_rt_data arg ^ ")"
    | Unit -> "()"
    | Pair (a, b) -> "(" ^ show_rt_data a ^ ", " ^ show_rt_data b ^ ")"

let rec fork_run s env (sw: Switch.t) 
    (rel_clause_name : string) 
    (input_channels : rt_data ELPromise.t list)
    (output_channel : rt_data ELPromise.t) : unit = 
    match use_multi_domain, use_multi_thread with
    | true, false -> failwith "Cannot use multi-domain without multi-threading"
    | true, true ->
        Fiber.fork ~sw:sw (fun _ -> 
            Eio.Executor_pool.submit_exn ~weight:1.0 env (fun _ -> 
                Eio.Switch.run (fun sw -> 
                    interpret_rel_clause s env sw rel_clause_name input_channels output_channel
                )
            )
        )
    | false, true ->
        Fiber.fork ~sw:sw (fun _ -> 
            interpret_rel_clause s env sw rel_clause_name input_channels output_channel
        )
    | false, false ->
        (* no multi-threading, just run the function *)
        interpret_rel_clause s env sw rel_clause_name input_channels output_channel

and interpret_rel_clause 
    (s : LP.t) 
    env (sw : Switch.t) 
    (rel_clause_name : string) 
    (input_channels : rt_data ELPromise.t list)
    (output_channel : rt_data ELPromise.t) : unit =
    (* print_endline ("[lazywait?] executing clause " ^ rel_clause_name); *)
    if isLazy && use_multi_thread then ELPromise.wait_if_lazy output_channel;
    let recur = interpret_rel_clause s env sw in
    let _, rel_clause = ListUtil.lookup_elem_by_key s.relational_sig rel_clause_name in
    (* print_endline ("[start] executing clause " ^ rel_clause_name ^ " : " ^ LP.show_rel_clause rel_clause); *)
    match rel_clause with
    | LP.Id -> (
        match input_channels with
        | [only_input] -> ELPromise.resolve output_channel (ELPromise.await only_input)
        | _ -> failwith "Id clause must have exactly one input"
    )
    | LP.Duplicate -> (
        match input_channels with
        | [only_input] -> 
            ELPromise.resolve output_channel (Pair (Pending only_input, Pending only_input));
        | _ -> failwith "Duplicate clause must have exactly one input"
    )
    | LP.Dealloc -> (
        match input_channels with
        | [_only_input] -> 
            ELPromise.resolve output_channel Unit (* ignore the input as we are deallocating *)
        | _ -> failwith "Dealloc clause must have exactly one input"
    )
    | LP.PlusR { premise_name;data_constructor_name } -> (
        let new_oc = ELPromise.create () in
        ELPromise.resolve output_channel (Ap(data_constructor_name, Pending new_oc));
        recur premise_name input_channels new_oc
    )
    | LP.PlusL {premise_names;idx} -> (
        let data = ELPromise.await (List.nth input_channels idx) in
        match data with
        | Ap(cons_name, Pending arg) -> (
            let premise_name = ListUtil.lookup_elem_by_key premise_names cons_name in
            recur premise_name (ListUtil.replace_idx input_channels idx [arg]) output_channel
        )
        | _ -> (
            failwith ("E18: PlusL clause must have a data constructor as input but got " 
            ^ show_rt_data data ^ " in clause " ^ LP.show_rel_clause rel_clause)
        )
    )
    | LP.Cut {new_chan_tp=_;left_premise;right_premise;split;idx} -> (
        let new_chan = ELPromise.create () in
        fork_run s env sw 
            left_premise (PairSplit.select_left split input_channels) new_chan
        ;
        recur right_premise (
            ListUtil.insert_at_index (PairSplit.select_right split input_channels) idx [new_chan]) output_channel;
    )
    | LP.UnitR -> (
        ELPromise.resolve output_channel Unit;
    )
    | LP.UnitL { premise_name; idx } -> (
        let data = ELPromise.await (List.nth input_channels idx) in
        match data with
        | Unit -> recur premise_name (ListUtil.replace_idx input_channels idx []) output_channel
        | _ -> (
            failwith ("E17: UnitL clause must have unit as input but got " 
            ^ show_rt_data data ^ " in clause " ^ LP.show_rel_clause rel_clause)
        )
    )
    | LP.TensorR { left_premise; right_premise; split } -> (
        let (l_ch) = ELPromise.create () in
        let (r_ch) = ELPromise.create () in
        ELPromise.resolve output_channel (Pair (Pending l_ch, Pending r_ch));
        fork_run s env sw 
            left_premise (PairSplit.select_left split input_channels) l_ch
        ;
        recur right_premise (PairSplit.select_right split input_channels) r_ch
    )
    | LP.TensorL {premise_name;idx} -> (
        let data = ELPromise.await (List.nth input_channels idx) in
        match data with
        | Pair (Pending arg1, Pending arg2) -> (
            recur premise_name (ListUtil.replace_idx input_channels idx [arg1; arg2]) output_channel
        )
        | _ -> (
            failwith ("E18: TensorL clause must have a pair as input but got " 
            ^ show_rt_data data ^ " in clause " ^ LP.show_rel_clause rel_clause)
        )
    )
    | LP.PermL {premise_name;indexes} -> (
        recur premise_name (
            List.map (fun i -> (List.nth input_channels i)) indexes
        ) output_channel
    )


let print_and_flush (s : string) = 
    Format.printf "%s" s;
    Format.pp_print_flush Format.std_formatter ()

let rec print_data_up_to_depth (rt_data_p : rt_data) (depth : int) = 
    match rt_data_p with
    | Unit -> print_and_flush "()"
    | Ap (s, arg) -> 
        (
            (* pretty print: if arg is (), do not print as application, but as a free variable *)
            let arg_peek = (match arg with
            | Pending p -> 
                let data = ELPromise.await p in
                data
            | _ -> arg) in
            match arg_peek with
            | Unit -> print_and_flush s
            | _ -> (
                print_and_flush ("(" ^ s ^ " ");
                if depth > 0 then
                    print_data_up_to_depth arg (depth - 1)
                else 
                    print_and_flush "...";
                print_and_flush ")"
            )
        )
    | Pair (a, b) ->
        print_data_up_to_depth a depth;
        print_and_flush " ";
        print_data_up_to_depth b depth;
    | Pending p ->
        (* print_endline ("Started waiting for pending data"); *)
        let data = ELPromise.await p in
        (* print_endline ("Pending data: " ^ show_rt_data data); *)
        print_data_up_to_depth data depth






let exec_top (s : LP.t) : unit = 
    (* let data_sig = s.data_sig in *)
    let rel_sig = s.relational_sig in
    (* find main function *)
    match (ListUtil.find_elem_by_key rel_sig "main") with
    | None -> failwith "No main function found"
    | Some ((rel_tp, _)) -> (
        if List.length rel_tp.inputs <> 0 then failwith "Main function must have no inputs";
        Eio_main.run ( fun env -> 
            Switch.run (fun sw -> 
                let domain_mgr = Eio.Stdenv.domain_mgr env in
                let pool = Eio.Executor_pool.create ~sw ~domain_count:(Domain.recommended_domain_count()) domain_mgr in
                (* allocate channels for outputs *)
                let ch = ELPromise.create () in 
                Fiber.fork ~sw:sw (fun _ -> 
                    (* separate thread for printing *)
                    print_data_up_to_depth (Pending ch) default_depth;
                );
                (* continue to main thread *)
                interpret_rel_clause s pool sw "main" [] ch;
            )
        )
    )