type nat = +{'zero : 1, 'succ : nat}
type bool = +{'true : 1, 'false : 1}


nat_dup : nat >=> (nat * nat)
    Duplicate
nat_dealloc : nat >=> 1
    Dealloc
bool_dup : bool >=> (bool * bool)
    Duplicate
bool_dealloc : bool >=> 1
    Dealloc
iszero : nat >=> bool
    PlusL {premise_names = 'zero => iszero_L0zero; idx = 0}
    PlusL {premise_names = 'succ => iszero_L0succ; idx = 0}
    PlusL {premise_names = 'succ => iszero_L0succ_1; idx = 0}
iszero_L0succ_1 : nat >=> bool
    Cut {new_chan_tp = nat; left_premise = iszero_L0succ_1_P0; right_premise = iszero_L0succ_1_cut; split = L; idx = 0}
iszero_L0succ_1_cut : nat >=> bool
    Cut {new_chan_tp = bool; left_premise = iszero; right_premise = iszero_L0succ_1_cut_cut; split = L; idx = 0}
iszero_L0succ_1_cut_cut : bool >=> bool
    PlusL {premise_names = 'true => iszero_L0succ_1_cut_cut_L0true; idx = 0}
iszero_L0succ_1_cut_cut_L0true : 1 >=> bool
    UnitL {premise_name = iszero_L0succ_1_cut_cut_L0true_Lunit; idx = 0}
iszero_L0succ_1_cut_cut_L0true_Lunit :  >=> bool
    PlusR {premise_name = iszero_L0succ_1_cut_cut_L0true_Lunit_Rfalse; data_constructor_name = false}
iszero_L0succ_1_cut_cut_L0true_Lunit_Rfalse :  >=> 1
    UnitR
iszero_L0succ_1_P0 : nat >=> nat
    PlusR {premise_name = iszero_L0succ_1_P0_Rsucc; data_constructor_name = succ}
iszero_L0succ_1_P0_Rsucc : nat >=> nat
    Id
iszero_L0succ : nat >=> bool
    Cut {new_chan_tp = nat; left_premise = iszero_L0succ_P0; right_premise = iszero_L0succ_cut; split = L; idx = 0}
iszero_L0succ_cut : nat >=> bool
    Cut {new_chan_tp = bool; left_premise = iszero; right_premise = iszero_L0succ_cut_cut; split = L; idx = 0}
iszero_L0succ_cut_cut : bool >=> bool
    PlusL {premise_names = 'false => iszero_L0succ_cut_cut_L0false; idx = 0}
iszero_L0succ_cut_cut_L0false : 1 >=> bool
    UnitL {premise_name = iszero_L0succ_cut_cut_L0false_Lunit; idx = 0}
iszero_L0succ_cut_cut_L0false_Lunit :  >=> bool
    PlusR {premise_name = iszero_L0succ_cut_cut_L0false_Lunit_Rfalse; data_constructor_name = false}
iszero_L0succ_cut_cut_L0false_Lunit_Rfalse :  >=> 1
    UnitR
iszero_L0succ_P0 : nat >=> nat
    PlusR {premise_name = iszero_L0succ_P0_Rsucc; data_constructor_name = succ}
iszero_L0succ_P0_Rsucc : nat >=> nat
    Id
iszero_L0zero : 1 >=> bool
    UnitL {premise_name = iszero_L0zero_Lunit; idx = 0}
iszero_L0zero_Lunit :  >=> bool
    PlusR {premise_name = iszero_L0zero_Lunit_Rtrue; data_constructor_name = true}
iszero_L0zero_Lunit_Rtrue :  >=> 1
    UnitR
main :  >=> bool
    Cut {new_chan_tp = nat; left_premise = main_P0; right_premise = iszero; split = ; idx = 0}
main_P0 :  >=> nat
    PlusR {premise_name = main_P0_Rzero; data_constructor_name = zero}
main_P0_Rzero :  >=> 1
    UnitR