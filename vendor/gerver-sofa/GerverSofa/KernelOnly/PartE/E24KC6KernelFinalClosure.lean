import GerverSofa.KernelOnly.PartE.E24KC6PhiBelowReconstruct
import GerverSofa.KernelOnly.PartE.E24KC6PhiAboveReconstruct
import GerverSofa.KernelOnly.PartE.E24KC6ThetaBelowReconstruct
import GerverSofa.KernelOnly.PartE.E24KC6ThetaAboveReconstruct

noncomputable section

namespace GerverSofa
namespace PartE

theorem deepMindABPhiTheta_existsUnique :
    ∃! ABphiTheta : ℝ × ℝ × ℝ × ℝ,
      DeepMindABPhiThetaSpec
        ABphiTheta.1 ABphiTheta.2.1 ABphiTheta.2.2.1 ABphiTheta.2.2.2 :=
  deepMindABPhiTheta_existsUnique_of_alignedChecks
    e24PhiBelowKernelCheck
    e24PhiAboveKernelCheck
    e24ThetaBelowKernelCheck
    e24ThetaAboveKernelCheck

end PartE
end GerverSofa
