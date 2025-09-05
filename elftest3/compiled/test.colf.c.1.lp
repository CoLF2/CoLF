type nat = +{'zero : 1, 'succ : nat}


nat_dup : nat >=> (nat * nat)
    Duplicate
nat_dealloc : nat >=> 1
    Dealloc
half : nat >=> nat
    PlusL {premise_names = 'zero => half_L0zero
                         , 'succ => half_L0succ; idx = 0}
half_L0succ_1 : nat >=> nat
    PlusL {premise_names = 'succ => half_L0succ_1_L0succ
                         , 'zero => half_L0succ_L0zero; idx = 0}
half_L0succ_1_L0succ : nat >=> nat
    Id
half_L0succ : nat >=> nat
    PlusL {premise_names = 'zero => half_L0succ_L0zero
                         , 'succ => half_L0succ_1_L0succ; idx = 0}
half_L0succ_L0zero : 1 >=> nat
    UnitL {premise_name = half_L0succ_L0zero_Lunit; idx = 0}
half_L0succ_L0zero_Lunit :  >=> nat
    PlusR {premise_name = half_L0succ_L0zero_Lunit_Rzero; data_constructor_name = zero}
half_L0succ_L0zero_Lunit_Rzero :  >=> 1
    UnitR
half_L0zero : 1 >=> nat
    UnitL {premise_name = half_L0zero_Lunit; idx = 0}
half_L0zero_Lunit :  >=> nat
    PlusR {premise_name = half_L0zero_Lunit_Rzero; data_constructor_name = zero}
half_L0zero_Lunit_Rzero :  >=> 1
    UnitR
two :  >=> nat
    PlusR {premise_name = two_Rsucc; data_constructor_name = succ}
two_Rsucc :  >=> nat
    PlusR {premise_name = two_Rsucc_Rsucc; data_constructor_name = succ}
two_Rsucc_Rsucc :  >=> nat
    PlusR {premise_name = two_Rsucc_Rsucc_Rzero; data_constructor_name = zero}
two_Rsucc_Rsucc_Rzero :  >=> 1
    UnitR
four :  >=> nat
    PlusR {premise_name = four_Rsucc; data_constructor_name = succ}
four_Rsucc :  >=> nat
    PlusR {premise_name = four_Rsucc_Rsucc; data_constructor_name = succ}
four_Rsucc_Rsucc :  >=> nat
    PlusR {premise_name = four_Rsucc_Rsucc_Rsucc; data_constructor_name = succ}
four_Rsucc_Rsucc_Rsucc :  >=> nat
    PlusR {premise_name = four_Rsucc_Rsucc_Rsucc_Rsucc; data_constructor_name = succ}
four_Rsucc_Rsucc_Rsucc_Rsucc :  >=> nat
    PlusR {premise_name = four_Rsucc_Rsucc_Rsucc_Rsucc_Rzero; data_constructor_name = zero}
four_Rsucc_Rsucc_Rsucc_Rsucc_Rzero :  >=> 1
    UnitR
main :  >=> nat
    Cut {new_chan_tp = nat; left_premise = four; right_premise = half; split = ; idx = 0}