type nat = +{'zero : 1, 'succ : nat}


add : nat , nat >=> nat
    PlusL {premise_names = 'zero => add_Lzero, 'succ => add_Lsucc; idx = 0}
add_Lsucc : nat , nat >=> nat
    PlusR {premise_name = add; data_constructor_name = succ}
add_Lzero : 1 , nat >=> nat
    UnitL {premise_name = add_Lzero_Lunit; idx = 0}
add_Lzero_Lunit : nat >=> nat
    Id
two :  >=> nat
    PlusR {premise_name = two_Rsucc; data_constructor_name = succ}
two_Rsucc :  >=> nat
    PlusR {premise_name = two_Rsucc_Rsucc; data_constructor_name = succ}
two_Rsucc_Rsucc :  >=> nat
    PlusR {premise_name = two_Rsucc_Rsucc_Rzero; data_constructor_name = zero}
two_Rsucc_Rsucc_Rzero :  >=> 1
    UnitR
add' : nat , nat >=> nat
    PermL {premise_name = add; indexes = 1, 0}
main :  >=> nat
    Cut {new_chan_tp = nat; left_premise = main_P0; right_premise = main_cut; split = ; idx = 0}
main_cut : nat >=> nat
    Cut {new_chan_tp = nat; left_premise = main_cut_P1; right_premise = add'; split = R; idx = 1}
main_cut_P1 :  >=> nat
    PlusR {premise_name = main_cut_P1_Rsucc; data_constructor_name = succ}
main_cut_P1_Rsucc :  >=> nat
    PlusR {premise_name = main_cut_P1_Rsucc_Rsucc; data_constructor_name = succ}
main_cut_P1_Rsucc_Rsucc :  >=> nat
    PlusR {premise_name = main_cut_P1_Rsucc_Rsucc_Rzero; data_constructor_name = zero}
main_cut_P1_Rsucc_Rsucc_Rzero :  >=> 1
    UnitR
main_P0 :  >=> nat
    PlusR {premise_name = main_P0_Rsucc; data_constructor_name = succ}
main_P0_Rsucc :  >=> nat
    PlusR {premise_name = main_P0_Rsucc_Rsucc; data_constructor_name = succ}
main_P0_Rsucc_Rsucc :  >=> nat
    PlusR {premise_name = main_P0_Rsucc_Rsucc_Rzero; data_constructor_name = zero}
main_P0_Rsucc_Rsucc_Rzero :  >=> 1
    UnitR