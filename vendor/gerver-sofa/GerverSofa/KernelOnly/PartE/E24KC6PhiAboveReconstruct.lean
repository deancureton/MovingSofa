import GerverSofa.KernelOnly.PartE.E24KC4Batch_PhiAbove_F_9_C1LLL_0006
import GerverSofa.KernelOnly.PartE.E24KC4Batch_PhiAbove_F_9_C1LLRLL_0009
import GerverSofa.KernelOnly.PartE.E24KC4Batch_PhiAbove_F_9_C1LLRLRL_0011
import GerverSofa.KernelOnly.PartE.E24KC4Pilot_PhiAbove_F_9_0002
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F0LLR_00112
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F0LRL_00114
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F0RLR_00169
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F0RRL_00171
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F16LLL_00214
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F16LLR_00215
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F16LR_00216
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F16RL_00218
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F16RR_00219
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F24LL_00222
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F24LR_00223
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F24RL_00225
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F24RR_00226
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F32_00227
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F8LLR_00192
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F8LRL_00194
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F8RLR_00209
import GerverSofa.KernelOnly.PartE.E24KC5FrontierBatch_F8RR_00210
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1101101_9_00111
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1101110_9_00145
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1101111_9_00168
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1110000_9_00182
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1110001_9_00191
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1110010_9_00200
import GerverSofa.KernelOnly.PartE.E24KC5Join_e24KC2PhiAboveLeaf1110011_9_00208
import GerverSofa.KernelOnly.PartE.E24KC5TerminalBatch_T0_00001

noncomputable section

namespace GerverSofa
namespace PartE

theorem e24KC2PhiAboveNode100101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1001010 e24KC2PhiAboveLeaf1001011 e24KC2PhiAboveLeaf1001012 e24KC2PhiAboveLeaf1001013

theorem e24KC2PhiAboveNode100110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1001100 e24KC2PhiAboveLeaf1001101 e24KC2PhiAboveLeaf1001102 e24KC2PhiAboveLeaf1001103

theorem e24KC2PhiAboveNode100111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1001110 e24KC2PhiAboveLeaf1001111 e24KC2PhiAboveLeaf1001112 e24KC2PhiAboveLeaf1001113

theorem e24KC2PhiAboveNode101000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1010000 e24KC2PhiAboveLeaf1010001 e24KC2PhiAboveLeaf1010002 e24KC2PhiAboveLeaf1010003

theorem e24KC2PhiAboveNode101001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1010010 e24KC2PhiAboveLeaf1010011 e24KC2PhiAboveLeaf1010012 e24KC2PhiAboveLeaf1010013

theorem e24KC2PhiAboveNode101010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1010100 e24KC2PhiAboveLeaf1010101 e24KC2PhiAboveLeaf1010102 e24KC2PhiAboveLeaf1010103

theorem e24KC2PhiAboveNode101011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1010110 e24KC2PhiAboveLeaf1010111 e24KC2PhiAboveLeaf1010112 e24KC2PhiAboveLeaf1010113

theorem e24KC2PhiAboveNode101100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1011000 e24KC2PhiAboveLeaf1011001 e24KC2PhiAboveLeaf1011002 e24KC2PhiAboveLeaf1011003

theorem e24KC2PhiAboveNode101101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1011010 e24KC2PhiAboveLeaf1011011 e24KC2PhiAboveLeaf1011012 e24KC2PhiAboveLeaf1011013

theorem e24KC2PhiAboveNode101110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1011100 e24KC2PhiAboveLeaf1011101 e24KC2PhiAboveLeaf1011102 e24KC2PhiAboveLeaf1011103

theorem e24KC2PhiAboveNode101111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1011110 e24KC2PhiAboveLeaf1011111 e24KC2PhiAboveLeaf1011112 e24KC2PhiAboveLeaf1011113

theorem e24KC2PhiAboveNode110000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1100000 e24KC2PhiAboveLeaf1100001 e24KC2PhiAboveLeaf1100002 e24KC2PhiAboveLeaf1100003

theorem e24KC2PhiAboveNode110001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1100010 e24KC2PhiAboveLeaf1100011 e24KC2PhiAboveLeaf1100012 e24KC2PhiAboveLeaf1100013

theorem e24KC2PhiAboveNode110010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1100100 e24KC2PhiAboveLeaf1100101 e24KC2PhiAboveLeaf1100102 e24KC2PhiAboveLeaf1100103

theorem e24KC2PhiAboveNode110011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1100110 e24KC2PhiAboveLeaf1100111 e24KC2PhiAboveLeaf1100112 e24KC2PhiAboveLeaf1100113

theorem e24KC2PhiAboveNode110013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1100130 e24KC2PhiAboveLeaf1100131 e24KC2PhiAboveLeaf1100132 e24KC2PhiAboveLeaf1100133

theorem e24KC2PhiAboveNode110100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1101000 e24KC2PhiAboveLeaf1101001 e24KC2PhiAboveLeaf1101002 e24KC2PhiAboveLeaf1101003

theorem e24KC2PhiAboveNode110101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1101010 e24KC2PhiAboveLeaf1101011 e24KC2PhiAboveLeaf1101012 e24KC2PhiAboveLeaf1101013

theorem e24KC2PhiAboveNode110102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1101020 e24KC2PhiAboveLeaf1101021 e24KC2PhiAboveLeaf1101022 e24KC2PhiAboveLeaf1101023

theorem e24KC2PhiAboveNode110103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1101030 e24KC2PhiAboveLeaf1101031 e24KC2PhiAboveLeaf1101032 e24KC2PhiAboveLeaf1101033

theorem e24KC2PhiAboveNode110110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1101100 e24KC2PhiAboveLeaf1101101 e24KC2PhiAboveLeaf1101102 e24KC2PhiAboveLeaf1101103

theorem e24KC2PhiAboveNode110111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1101110 e24KC2PhiAboveLeaf1101111 e24KC2PhiAboveLeaf1101112 e24KC2PhiAboveLeaf1101113

theorem e24KC2PhiAboveNode110112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1101120 e24KC2PhiAboveLeaf1101121 e24KC2PhiAboveLeaf1101122 e24KC2PhiAboveLeaf1101123

theorem e24KC2PhiAboveNode110113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1101130 e24KC2PhiAboveLeaf1101131 e24KC2PhiAboveLeaf1101132 e24KC2PhiAboveLeaf1101133

theorem e24KC2PhiAboveNode111000 :
    adaptiveCoverCheck 10 (childLL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1110000 e24KC2PhiAboveLeaf1110001 e24KC2PhiAboveLeaf1110002 e24KC2PhiAboveLeaf1110003

theorem e24KC2PhiAboveNode111001 :
    adaptiveCoverCheck 10 (childLH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1110010 e24KC2PhiAboveLeaf1110011 e24KC2PhiAboveLeaf1110012 e24KC2PhiAboveLeaf1110013

theorem e24KC2PhiAboveNode111002 :
    adaptiveCoverCheck 10 (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1110020 e24KC2PhiAboveLeaf1110021 e24KC2PhiAboveLeaf1110022 e24KC2PhiAboveLeaf1110023

theorem e24KC2PhiAboveNode111003 :
    adaptiveCoverCheck 10 (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1110030 e24KC2PhiAboveLeaf1110031 e24KC2PhiAboveLeaf1110032 e24KC2PhiAboveLeaf1110033

theorem e24KC2PhiAboveNode111010 :
    adaptiveCoverCheck 10 (childLL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1110100 e24KC2PhiAboveLeaf1110101 e24KC2PhiAboveLeaf1110102 e24KC2PhiAboveLeaf1110103

theorem e24KC2PhiAboveNode111011 :
    adaptiveCoverCheck 10 (childLH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1110110 e24KC2PhiAboveLeaf1110111 e24KC2PhiAboveLeaf1110112 e24KC2PhiAboveLeaf1110113

theorem e24KC2PhiAboveNode111012 :
    adaptiveCoverCheck 10 (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1110120 e24KC2PhiAboveLeaf1110121 e24KC2PhiAboveLeaf1110122 e24KC2PhiAboveLeaf1110123

theorem e24KC2PhiAboveNode111013 :
    adaptiveCoverCheck 10 (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1110130 e24KC2PhiAboveLeaf1110131 e24KC2PhiAboveLeaf1110132 e24KC2PhiAboveLeaf1110133

theorem e24KC2PhiAboveNode111100 :
    adaptiveCoverCheck 10 (childLL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1111000 e24KC2PhiAboveLeaf1111001 e24KC2PhiAboveLeaf1111002 e24KC2PhiAboveLeaf1111003

theorem e24KC2PhiAboveNode111101 :
    adaptiveCoverCheck 10 (childLH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1111010 e24KC2PhiAboveLeaf1111011 e24KC2PhiAboveLeaf1111012 e24KC2PhiAboveLeaf1111013

theorem e24KC2PhiAboveNode111102 :
    adaptiveCoverCheck 10 (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1111020 e24KC2PhiAboveLeaf1111021 e24KC2PhiAboveLeaf1111022 e24KC2PhiAboveLeaf1111023

theorem e24KC2PhiAboveNode111103 :
    adaptiveCoverCheck 10 (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1111030 e24KC2PhiAboveLeaf1111031 e24KC2PhiAboveLeaf1111032 e24KC2PhiAboveLeaf1111033

theorem e24KC2PhiAboveNode111110 :
    adaptiveCoverCheck 10 (childLL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1111100 e24KC2PhiAboveLeaf1111101 e24KC2PhiAboveLeaf1111102 e24KC2PhiAboveLeaf1111103

theorem e24KC2PhiAboveNode111111 :
    adaptiveCoverCheck 10 (childLH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1111110 e24KC2PhiAboveLeaf1111111 e24KC2PhiAboveLeaf1111112 e24KC2PhiAboveLeaf1111113

theorem e24KC2PhiAboveNode111112 :
    adaptiveCoverCheck 10 (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1111120 e24KC2PhiAboveLeaf1111121 e24KC2PhiAboveLeaf1111122 e24KC2PhiAboveLeaf1111123

theorem e24KC2PhiAboveNode111113 :
    adaptiveCoverCheck 10 (childHH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))))
    e24KC2PhiAboveLeaf1111130 e24KC2PhiAboveLeaf1111131 e24KC2PhiAboveLeaf1111132 e24KC2PhiAboveLeaf1111133

theorem e24KC2PhiAboveNode01011 :
    adaptiveCoverCheck 11 (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childLL (childLH (childLL e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf010110 e24KC2PhiAboveLeaf010111 e24KC2PhiAboveLeaf010112 e24KC2PhiAboveLeaf010113

theorem e24KC2PhiAboveNode01100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf011000 e24KC2PhiAboveLeaf011001 e24KC2PhiAboveLeaf011002 e24KC2PhiAboveLeaf011003

theorem e24KC2PhiAboveNode01101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childLH (childLH (childLL e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf011010 e24KC2PhiAboveLeaf011011 e24KC2PhiAboveLeaf011012 e24KC2PhiAboveLeaf011013

theorem e24KC2PhiAboveNode01110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf011100 e24KC2PhiAboveLeaf011101 e24KC2PhiAboveLeaf011102 e24KC2PhiAboveLeaf011103

theorem e24KC2PhiAboveNode01111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childLH (childLH (childLL e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf011110 e24KC2PhiAboveLeaf011111 e24KC2PhiAboveLeaf011112 e24KC2PhiAboveLeaf011113

theorem e24KC2PhiAboveNode10000 :
    adaptiveCoverCheck 11 (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf100000 e24KC2PhiAboveLeaf100001 e24KC2PhiAboveLeaf100002 e24KC2PhiAboveLeaf100003

theorem e24KC2PhiAboveNode10001 :
    adaptiveCoverCheck 11 (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childLL (childLL (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf100010 e24KC2PhiAboveLeaf100011 e24KC2PhiAboveLeaf100012 e24KC2PhiAboveLeaf100013

theorem e24KC2PhiAboveNode10010 :
    adaptiveCoverCheck 11 (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf100100 e24KC2PhiAboveNode100101 e24KC2PhiAboveLeaf100102 e24KC2PhiAboveLeaf100103

theorem e24KC2PhiAboveNode10011 :
    adaptiveCoverCheck 11 (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childLL (childLL (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode100110 e24KC2PhiAboveNode100111 e24KC2PhiAboveLeaf100112 e24KC2PhiAboveLeaf100113

theorem e24KC2PhiAboveNode10100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode101000 e24KC2PhiAboveNode101001 e24KC2PhiAboveLeaf101002 e24KC2PhiAboveLeaf101003

theorem e24KC2PhiAboveNode10101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childLH (childLL (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode101010 e24KC2PhiAboveNode101011 e24KC2PhiAboveLeaf101012 e24KC2PhiAboveLeaf101013

theorem e24KC2PhiAboveNode10110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode101100 e24KC2PhiAboveNode101101 e24KC2PhiAboveLeaf101102 e24KC2PhiAboveLeaf101103

theorem e24KC2PhiAboveNode10111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode101110 e24KC2PhiAboveNode101111 e24KC2PhiAboveLeaf101112 e24KC2PhiAboveLeaf101113

theorem e24KC2PhiAboveNode10113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childLH (childLL (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf101130 e24KC2PhiAboveLeaf101131 e24KC2PhiAboveLeaf101132 e24KC2PhiAboveLeaf101133

theorem e24KC2PhiAboveNode11000 :
    adaptiveCoverCheck 11 (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode110000 e24KC2PhiAboveNode110001 e24KC2PhiAboveLeaf110002 e24KC2PhiAboveLeaf110003

theorem e24KC2PhiAboveNode11001 :
    adaptiveCoverCheck 11 (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode110010 e24KC2PhiAboveNode110011 e24KC2PhiAboveLeaf110012 e24KC2PhiAboveNode110013

theorem e24KC2PhiAboveNode11002 :
    adaptiveCoverCheck 11 (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf110020 e24KC2PhiAboveLeaf110021 e24KC2PhiAboveLeaf110022 e24KC2PhiAboveLeaf110023

theorem e24KC2PhiAboveNode11003 :
    adaptiveCoverCheck 11 (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childLL (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf110030 e24KC2PhiAboveLeaf110031 e24KC2PhiAboveLeaf110032 e24KC2PhiAboveLeaf110033

theorem e24KC2PhiAboveNode11010 :
    adaptiveCoverCheck 11 (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode110100 e24KC2PhiAboveNode110101 e24KC2PhiAboveNode110102 e24KC2PhiAboveNode110103

theorem e24KC2PhiAboveNode11011 :
    adaptiveCoverCheck 11 (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode110110 e24KC2PhiAboveNode110111 e24KC2PhiAboveNode110112 e24KC2PhiAboveNode110113

theorem e24KC2PhiAboveNode11012 :
    adaptiveCoverCheck 11 (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf110120 e24KC2PhiAboveLeaf110121 e24KC2PhiAboveLeaf110122 e24KC2PhiAboveLeaf110123

theorem e24KC2PhiAboveNode11013 :
    adaptiveCoverCheck 11 (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childLL (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf110130 e24KC2PhiAboveLeaf110131 e24KC2PhiAboveLeaf110132 e24KC2PhiAboveLeaf110133

theorem e24KC2PhiAboveNode11100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode111000 e24KC2PhiAboveNode111001 e24KC2PhiAboveNode111002 e24KC2PhiAboveNode111003

theorem e24KC2PhiAboveNode11101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode111010 e24KC2PhiAboveNode111011 e24KC2PhiAboveNode111012 e24KC2PhiAboveNode111013

theorem e24KC2PhiAboveNode11102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf111020 e24KC2PhiAboveLeaf111021 e24KC2PhiAboveLeaf111022 e24KC2PhiAboveLeaf111023

theorem e24KC2PhiAboveNode11103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childLH (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf111030 e24KC2PhiAboveLeaf111031 e24KC2PhiAboveLeaf111032 e24KC2PhiAboveLeaf111033

theorem e24KC2PhiAboveNode11110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode111100 e24KC2PhiAboveNode111101 e24KC2PhiAboveNode111102 e24KC2PhiAboveNode111103

theorem e24KC2PhiAboveNode11111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveNode111110 e24KC2PhiAboveNode111111 e24KC2PhiAboveNode111112 e24KC2PhiAboveNode111113

theorem e24KC2PhiAboveNode11112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf111120 e24KC2PhiAboveLeaf111121 e24KC2PhiAboveLeaf111122 e24KC2PhiAboveLeaf111123

theorem e24KC2PhiAboveNode11113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot))))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childLH (childLH (childLH e24PhiAboveRoot)))))
    e24KC2PhiAboveLeaf111130 e24KC2PhiAboveLeaf111131 e24KC2PhiAboveLeaf111132 e24KC2PhiAboveLeaf111133

theorem e24KC2PhiAboveNode0000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childLL e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLL (childLL (childLL e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf00000 e24KC2PhiAboveLeaf00001 e24KC2PhiAboveLeaf00002 e24KC2PhiAboveLeaf00003

theorem e24KC2PhiAboveNode0001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childLL e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLL (childLL (childLL e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf00010 e24KC2PhiAboveLeaf00011 e24KC2PhiAboveLeaf00012 e24KC2PhiAboveLeaf00013

theorem e24KC2PhiAboveNode0010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childLL e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLH (childLL (childLL e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf00100 e24KC2PhiAboveLeaf00101 e24KC2PhiAboveLeaf00102 e24KC2PhiAboveLeaf00103

theorem e24KC2PhiAboveNode0011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childLL e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLH (childLL (childLL e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf00110 e24KC2PhiAboveLeaf00111 e24KC2PhiAboveLeaf00112 e24KC2PhiAboveLeaf00113

theorem e24KC2PhiAboveNode0100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childLL e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLL (childLH (childLL e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf01000 e24KC2PhiAboveLeaf01001 e24KC2PhiAboveLeaf01002 e24KC2PhiAboveLeaf01003

theorem e24KC2PhiAboveNode0101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childLL e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLL (childLH (childLL e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf01010 e24KC2PhiAboveNode01011 e24KC2PhiAboveLeaf01012 e24KC2PhiAboveLeaf01013

theorem e24KC2PhiAboveNode0110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childLL e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLH (childLH (childLL e24PhiAboveRoot))))
    e24KC2PhiAboveNode01100 e24KC2PhiAboveNode01101 e24KC2PhiAboveLeaf01102 e24KC2PhiAboveLeaf01103

theorem e24KC2PhiAboveNode0111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childLL e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLH (childLH (childLL e24PhiAboveRoot))))
    e24KC2PhiAboveNode01110 e24KC2PhiAboveNode01111 e24KC2PhiAboveLeaf01112 e24KC2PhiAboveLeaf01113

theorem e24KC2PhiAboveNode1000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLL (childLL (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveNode10000 e24KC2PhiAboveNode10001 e24KC2PhiAboveLeaf10002 e24KC2PhiAboveLeaf10003

theorem e24KC2PhiAboveNode1001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLL (childLL (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveNode10010 e24KC2PhiAboveNode10011 e24KC2PhiAboveLeaf10012 e24KC2PhiAboveLeaf10013

theorem e24KC2PhiAboveNode1002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childLL (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf10020 e24KC2PhiAboveLeaf10021 e24KC2PhiAboveLeaf10022 e24KC2PhiAboveLeaf10023

theorem e24KC2PhiAboveNode1003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childLL (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf10030 e24KC2PhiAboveLeaf10031 e24KC2PhiAboveLeaf10032 e24KC2PhiAboveLeaf10033

theorem e24KC2PhiAboveNode1010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLH (childLL (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveNode10100 e24KC2PhiAboveNode10101 e24KC2PhiAboveLeaf10102 e24KC2PhiAboveLeaf10103

theorem e24KC2PhiAboveNode1011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLH (childLL (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveNode10110 e24KC2PhiAboveNode10111 e24KC2PhiAboveLeaf10112 e24KC2PhiAboveNode10113

theorem e24KC2PhiAboveNode1012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childLL (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf10120 e24KC2PhiAboveLeaf10121 e24KC2PhiAboveLeaf10122 e24KC2PhiAboveLeaf10123

theorem e24KC2PhiAboveNode1013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childLL (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf10130 e24KC2PhiAboveLeaf10131 e24KC2PhiAboveLeaf10132 e24KC2PhiAboveLeaf10133

theorem e24KC2PhiAboveNode1100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLL (childLH (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveNode11000 e24KC2PhiAboveNode11001 e24KC2PhiAboveNode11002 e24KC2PhiAboveNode11003

theorem e24KC2PhiAboveNode1101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLL (childLH (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveNode11010 e24KC2PhiAboveNode11011 e24KC2PhiAboveNode11012 e24KC2PhiAboveNode11013

theorem e24KC2PhiAboveNode1102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childLH (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf11020 e24KC2PhiAboveLeaf11021 e24KC2PhiAboveLeaf11022 e24KC2PhiAboveLeaf11023

theorem e24KC2PhiAboveNode1103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childLH (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf11030 e24KC2PhiAboveLeaf11031 e24KC2PhiAboveLeaf11032 e24KC2PhiAboveLeaf11033

theorem e24KC2PhiAboveNode1110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLH (childLH (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveNode11100 e24KC2PhiAboveNode11101 e24KC2PhiAboveNode11102 e24KC2PhiAboveNode11103

theorem e24KC2PhiAboveNode1111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLH (childLH (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveNode11110 e24KC2PhiAboveNode11111 e24KC2PhiAboveNode11112 e24KC2PhiAboveNode11113

theorem e24KC2PhiAboveNode1112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childLH (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf11120 e24KC2PhiAboveLeaf11121 e24KC2PhiAboveLeaf11122 e24KC2PhiAboveLeaf11123

theorem e24KC2PhiAboveNode1113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH (childLH e24PhiAboveRoot)))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childLH (childLH e24PhiAboveRoot))))
    e24KC2PhiAboveLeaf11130 e24KC2PhiAboveLeaf11131 e24KC2PhiAboveLeaf11132 e24KC2PhiAboveLeaf11133

theorem e24KC2PhiAboveNode000 :
    adaptiveCoverCheck 13 (childLL (childLL (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveNode0000 e24KC2PhiAboveNode0001 e24KC2PhiAboveLeaf0002 e24KC2PhiAboveLeaf0003

theorem e24KC2PhiAboveNode001 :
    adaptiveCoverCheck 13 (childLH (childLL (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveNode0010 e24KC2PhiAboveNode0011 e24KC2PhiAboveLeaf0012 e24KC2PhiAboveLeaf0013

theorem e24KC2PhiAboveNode003 :
    adaptiveCoverCheck 13 (childHH (childLL (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childLL (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf0030 e24KC2PhiAboveLeaf0031 e24KC2PhiAboveLeaf0032 e24KC2PhiAboveLeaf0033

theorem e24KC2PhiAboveNode010 :
    adaptiveCoverCheck 13 (childLL (childLH (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveNode0100 e24KC2PhiAboveNode0101 e24KC2PhiAboveLeaf0102 e24KC2PhiAboveLeaf0103

theorem e24KC2PhiAboveNode011 :
    adaptiveCoverCheck 13 (childLH (childLH (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveNode0110 e24KC2PhiAboveNode0111 e24KC2PhiAboveLeaf0112 e24KC2PhiAboveLeaf0113

theorem e24KC2PhiAboveNode012 :
    adaptiveCoverCheck 13 (childHL (childLH (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childLH (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf0120 e24KC2PhiAboveLeaf0121 e24KC2PhiAboveLeaf0122 e24KC2PhiAboveLeaf0123

theorem e24KC2PhiAboveNode013 :
    adaptiveCoverCheck 13 (childHH (childLH (childLL e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childLH (childLL e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf0130 e24KC2PhiAboveLeaf0131 e24KC2PhiAboveLeaf0132 e24KC2PhiAboveLeaf0133

theorem e24KC2PhiAboveNode100 :
    adaptiveCoverCheck 13 (childLL (childLL (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveNode1000 e24KC2PhiAboveNode1001 e24KC2PhiAboveNode1002 e24KC2PhiAboveNode1003

theorem e24KC2PhiAboveNode101 :
    adaptiveCoverCheck 13 (childLH (childLL (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveNode1010 e24KC2PhiAboveNode1011 e24KC2PhiAboveNode1012 e24KC2PhiAboveNode1013

theorem e24KC2PhiAboveNode102 :
    adaptiveCoverCheck 13 (childHL (childLL (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childLL (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf1020 e24KC2PhiAboveLeaf1021 e24KC2PhiAboveLeaf1022 e24KC2PhiAboveLeaf1023

theorem e24KC2PhiAboveNode103 :
    adaptiveCoverCheck 13 (childHH (childLL (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childLL (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf1030 e24KC2PhiAboveLeaf1031 e24KC2PhiAboveLeaf1032 e24KC2PhiAboveLeaf1033

theorem e24KC2PhiAboveNode110 :
    adaptiveCoverCheck 13 (childLL (childLH (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveNode1100 e24KC2PhiAboveNode1101 e24KC2PhiAboveNode1102 e24KC2PhiAboveNode1103

theorem e24KC2PhiAboveNode111 :
    adaptiveCoverCheck 13 (childLH (childLH (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveNode1110 e24KC2PhiAboveNode1111 e24KC2PhiAboveNode1112 e24KC2PhiAboveNode1113

theorem e24KC2PhiAboveNode112 :
    adaptiveCoverCheck 13 (childHL (childLH (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childLH (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf1120 e24KC2PhiAboveLeaf1121 e24KC2PhiAboveLeaf1122 e24KC2PhiAboveLeaf1123

theorem e24KC2PhiAboveNode113 :
    adaptiveCoverCheck 13 (childHH (childLH (childLH e24PhiAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childLH (childLH e24PhiAboveRoot)))
    e24KC2PhiAboveLeaf1130 e24KC2PhiAboveLeaf1131 e24KC2PhiAboveLeaf1132 e24KC2PhiAboveLeaf1133

theorem e24KC2PhiAboveNode00 :
    adaptiveCoverCheck 14 (childLL (childLL e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL (childLL e24PhiAboveRoot))
    e24KC2PhiAboveNode000 e24KC2PhiAboveNode001 e24KC2PhiAboveLeaf002 e24KC2PhiAboveNode003

theorem e24KC2PhiAboveNode01 :
    adaptiveCoverCheck 14 (childLH (childLL e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH (childLL e24PhiAboveRoot))
    e24KC2PhiAboveNode010 e24KC2PhiAboveNode011 e24KC2PhiAboveNode012 e24KC2PhiAboveNode013

theorem e24KC2PhiAboveNode03 :
    adaptiveCoverCheck 14 (childHH (childLL e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH (childLL e24PhiAboveRoot))
    e24KC2PhiAboveLeaf030 e24KC2PhiAboveLeaf031 e24KC2PhiAboveLeaf032 e24KC2PhiAboveLeaf033

theorem e24KC2PhiAboveNode10 :
    adaptiveCoverCheck 14 (childLL (childLH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL (childLH e24PhiAboveRoot))
    e24KC2PhiAboveNode100 e24KC2PhiAboveNode101 e24KC2PhiAboveNode102 e24KC2PhiAboveNode103

theorem e24KC2PhiAboveNode11 :
    adaptiveCoverCheck 14 (childLH (childLH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH (childLH e24PhiAboveRoot))
    e24KC2PhiAboveNode110 e24KC2PhiAboveNode111 e24KC2PhiAboveNode112 e24KC2PhiAboveNode113

theorem e24KC2PhiAboveNode12 :
    adaptiveCoverCheck 14 (childHL (childLH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL (childLH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf120 e24KC2PhiAboveLeaf121 e24KC2PhiAboveLeaf122 e24KC2PhiAboveLeaf123

theorem e24KC2PhiAboveNode13 :
    adaptiveCoverCheck 14 (childHH (childLH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH (childLH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf130 e24KC2PhiAboveLeaf131 e24KC2PhiAboveLeaf132 e24KC2PhiAboveLeaf133

theorem e24KC2PhiAboveNode30 :
    adaptiveCoverCheck 14 (childLL (childHH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL (childHH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf300 e24KC2PhiAboveLeaf301 e24KC2PhiAboveLeaf302 e24KC2PhiAboveLeaf303

theorem e24KC2PhiAboveNode31 :
    adaptiveCoverCheck 14 (childLH (childHH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH (childHH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf310 e24KC2PhiAboveLeaf311 e24KC2PhiAboveLeaf312 e24KC2PhiAboveLeaf313

theorem e24KC2PhiAboveNode33 :
    adaptiveCoverCheck 14 (childHH (childHH e24PhiAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH (childHH e24PhiAboveRoot))
    e24KC2PhiAboveLeaf330 e24KC2PhiAboveLeaf331 e24KC2PhiAboveLeaf332 e24KC2PhiAboveLeaf333

theorem e24KC2PhiAboveNode0 :
    adaptiveCoverCheck 15 (childLL e24PhiAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL e24PhiAboveRoot)
    e24KC2PhiAboveNode00 e24KC2PhiAboveNode01 e24KC2PhiAboveLeaf02 e24KC2PhiAboveNode03

theorem e24KC2PhiAboveNode1 :
    adaptiveCoverCheck 15 (childLH e24PhiAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH e24PhiAboveRoot)
    e24KC2PhiAboveNode10 e24KC2PhiAboveNode11 e24KC2PhiAboveNode12 e24KC2PhiAboveNode13

theorem e24KC2PhiAboveNode3 :
    adaptiveCoverCheck 15 (childHH e24PhiAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHH e24PhiAboveRoot)
    e24KC2PhiAboveNode30 e24KC2PhiAboveNode31 e24KC2PhiAboveLeaf32 e24KC2PhiAboveNode33

theorem e24KC2PhiAboveNodeROOT :
    adaptiveCoverCheck 16 e24PhiAboveRoot = true :=
  adaptiveCoverCheck_succ_of_children 15 e24PhiAboveRoot
    e24KC2PhiAboveNode0 e24KC2PhiAboveNode1 e24KC2PhiAboveLeaf2 e24KC2PhiAboveNode3

theorem e24PhiAboveKernelCheck :
    adaptiveCoverCheck 16 e24PhiAboveRoot = true :=
  e24KC2PhiAboveNodeROOT

end PartE
end GerverSofa

