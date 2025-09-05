type bin = +{'e : 1, 'b0 : bin, 'b1 : bin}
type stream = +{'scons : (bin * stream)}


get_b0 :  >=> bin
    PlusR {premise_name = get_b0_Re; data_constructor_name = e}
get_b0_Re :  >=> 1
    UnitR
bsucc : bin >=> bin
    PlusL {premise_names = 'e => bsucc_L0e, 'b0 => bsucc_L0b0, 'b1 => bsucc_L0b1; idx = 0}
bsucc_L0b1 : bin >=> bin
    PlusR {premise_name = bsucc; data_constructor_name = b0}
bsucc_L0b0 : bin >=> bin
    PlusR {premise_name = bsucc_L0b0_Rb1; data_constructor_name = b1}
bsucc_L0b0_Rb1 : bin >=> bin
    Id
bsucc_L0e : 1 >=> bin
    UnitL {premise_name = bsucc_L0e_Lunit; idx = 0}
bsucc_L0e_Lunit :  >=> bin
    PlusR {premise_name = bsucc_L0e_Lunit_Rb1; data_constructor_name = b1}
bsucc_L0e_Lunit_Rb1 :  >=> bin
    PlusR {premise_name = bsucc_L0e_Lunit_Rb1_Re; data_constructor_name = e}
bsucc_L0e_Lunit_Rb1_Re :  >=> 1
    UnitR
bpred : bin >=> bin
    PlusL {premise_names = 'e => bpred_L0e, 'b0 => bpred_L0b0, 'b1 => bpred_L0b1, 'b1 => bpred_L0b1.1, 'b1 => bpred_L0b1.1.1; idx = 0}
bpred_L0b1.1.1 : bin >=> bin
    PlusL {premise_names = 'b1 => bpred_L0b1.1.1_L0b1; idx = 0}
bpred_L0b1.1.1_L0b1 : bin >=> bin
    PlusR {premise_name = bpred_L0b1.1.1_L0b1_Rb0; data_constructor_name = b0}
bpred_L0b1.1.1_L0b1_Rb0 : bin >=> bin
    PlusR {premise_name = bpred_L0b1.1.1_L0b1_Rb0_Rb1; data_constructor_name = b1}
bpred_L0b1.1.1_L0b1_Rb0_Rb1 : bin >=> bin
    Id
bpred_L0b1.1 : bin >=> bin
    PlusL {premise_names = 'b0 => bpred_L0b1.1_L0b0; idx = 0}
bpred_L0b1.1_L0b0 : bin >=> bin
    PlusR {premise_name = bpred_L0b1.1_L0b0_Rb0; data_constructor_name = b0}
bpred_L0b1.1_L0b0_Rb0 : bin >=> bin
    PlusR {premise_name = bpred_L0b1.1_L0b0_Rb0_Rb0; data_constructor_name = b0}
bpred_L0b1.1_L0b0_Rb0_Rb0 : bin >=> bin
    Id
bpred_L0b1 : bin >=> bin
    PlusL {premise_names = 'e => bpred_L0b1_L0e; idx = 0}
bpred_L0b1_L0e : 1 >=> bin
    UnitL {premise_name = bpred_L0b1_L0e_Lunit; idx = 0}
bpred_L0b1_L0e_Lunit :  >=> bin
    PlusR {premise_name = bpred_L0b1_L0e_Lunit_Re; data_constructor_name = e}
bpred_L0b1_L0e_Lunit_Re :  >=> 1
    UnitR
bpred_L0b0 : bin >=> bin
    PlusR {premise_name = bpred; data_constructor_name = b1}
bpred_L0e : 1 >=> bin
    UnitL {premise_name = bpred_L0e_Lunit; idx = 0}
bpred_L0e_Lunit :  >=> bin
    PlusR {premise_name = bpred_L0e_Lunit_Re; data_constructor_name = e}
bpred_L0e_Lunit_Re :  >=> 1
    UnitR
bin_dup : bin >=> (bin * bin)
    PlusL {premise_names = 'e => bin_dup_L0e, 'b0 => bin_dup_L0b0, 'b1 => bin_dup_L0b1; idx = 0}
bin_dup_L0b1 : bin >=> (bin * bin)
    Cut {new_chan_tp = (bin * bin); left_premise = bin_dup; right_premise = bin_dup_L0b1_cut; split = L; idx = 0}
bin_dup_L0b1_cut : (bin * bin) >=> (bin * bin)
    TensorL {premise_name = bin_dup_L0b1_cut_Lpair; idx = 0}
bin_dup_L0b1_cut_Lpair : bin , bin >=> (bin * bin)
    TensorR {left_premise = bin_dup_L0b1_cut_Lpair_Rleft; right_premise = bin_dup_L0b1_cut_Lpair_Rright; split = LR}
bin_dup_L0b1_cut_Lpair_Rleft : bin >=> bin
    PlusR {premise_name = bin_dup_L0b1_cut_Lpair_Rleft_Rb1; data_constructor_name = b1}
bin_dup_L0b1_cut_Lpair_Rleft_Rb1 : bin >=> bin
    Id
bin_dup_L0b1_cut_Lpair_Rright : bin >=> bin
    PlusR {premise_name = bin_dup_L0b1_cut_Lpair_Rright_Rb1; data_constructor_name = b1}
bin_dup_L0b1_cut_Lpair_Rright_Rb1 : bin >=> bin
    Id
bin_dup_L0b0 : bin >=> (bin * bin)
    Cut {new_chan_tp = (bin * bin); left_premise = bin_dup; right_premise = bin_dup_L0b0_cut; split = L; idx = 0}
bin_dup_L0b0_cut : (bin * bin) >=> (bin * bin)
    TensorL {premise_name = bin_dup_L0b0_cut_Lpair; idx = 0}
bin_dup_L0b0_cut_Lpair : bin , bin >=> (bin * bin)
    TensorR {left_premise = bin_dup_L0b0_cut_Lpair_Rleft; right_premise = bin_dup_L0b0_cut_Lpair_Rright; split = LR}
bin_dup_L0b0_cut_Lpair_Rleft : bin >=> bin
    PlusR {premise_name = bin_dup_L0b0_cut_Lpair_Rleft_Rb0; data_constructor_name = b0}
bin_dup_L0b0_cut_Lpair_Rleft_Rb0 : bin >=> bin
    Id
bin_dup_L0b0_cut_Lpair_Rright : bin >=> bin
    PlusR {premise_name = bin_dup_L0b0_cut_Lpair_Rright_Rb0; data_constructor_name = b0}
bin_dup_L0b0_cut_Lpair_Rright_Rb0 : bin >=> bin
    Id
bin_dup_L0e : 1 >=> (bin * bin)
    UnitL {premise_name = bin_dup_L0e_Lunit; idx = 0}
bin_dup_L0e_Lunit :  >=> (bin * bin)
    TensorR {left_premise = bin_dup_L0e_Lunit_Rleft; right_premise = bin_dup_L0e_Lunit_Rright; split = }
bin_dup_L0e_Lunit_Rleft :  >=> bin
    PlusR {premise_name = bin_dup_L0e_Lunit_Rleft_Re; data_constructor_name = e}
bin_dup_L0e_Lunit_Rleft_Re :  >=> 1
    UnitR
bin_dup_L0e_Lunit_Rright :  >=> bin
    PlusR {premise_name = bin_dup_L0e_Lunit_Rright_Re; data_constructor_name = e}
bin_dup_L0e_Lunit_Rright_Re :  >=> 1
    UnitR
up : bin >=> stream
    Cut {new_chan_tp = (bin * bin); left_premise = bin_dup; right_premise = up_cut; split = L; idx = 0}
up_cut : (bin * bin) >=> stream
    TensorL {premise_name = up_cut_Lpair; idx = 0}
up_cut_Lpair : bin , bin >=> stream
    Cut {new_chan_tp = bin; left_premise = bsucc; right_premise = up_cut_Lpair_cut; split = LR; idx = 1}
up_cut_Lpair_cut : bin , bin >=> stream
    Cut {new_chan_tp = stream; left_premise = up; right_premise = up_cut_Lpair_cut_cut; split = RL; idx = 1}
up_cut_Lpair_cut_cut : bin , stream >=> stream
    PlusR {premise_name = up_cut_Lpair_cut_cut_Rscons; data_constructor_name = scons}
up_cut_Lpair_cut_cut_Rscons : bin , stream >=> (bin * stream)
    TensorR {left_premise = up_cut_Lpair_cut_cut_Rscons_Rleft; right_premise = up_cut_Lpair_cut_cut_Rscons_Rright; split = LR}
up_cut_Lpair_cut_cut_Rscons_Rleft : bin >=> bin
    Id
up_cut_Lpair_cut_cut_Rscons_Rright : stream >=> stream
    Id
main :  >=> stream
    Cut {new_chan_tp = bin; left_premise = get_b0; right_premise = up; split = ; idx = 0}