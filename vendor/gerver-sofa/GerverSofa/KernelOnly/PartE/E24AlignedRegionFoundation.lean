import GerverSofa.KernelOnly.PartE.AdaptiveGlobalCoverClosure

/-!
# E24 aligned region foundation

Four rational rectangles are aligned exactly with the four sides of the
wide E21 local angle cell.  Their union covers every point of the global
physical angle root that is not in the local cell.
-/

noncomputable section

namespace GerverSofa
namespace PartE

def e24PhiBelowRoot : AngleCell :=
  ⟨⟨0, 391 / 10000, by norm_num⟩,
    ⟨0, 4 / 5, by norm_num⟩⟩

def e24PhiAboveRoot : AngleCell :=
  ⟨⟨157 / 4000, 4 / 5, by norm_num⟩,
    ⟨0, 4 / 5, by norm_num⟩⟩

def e24ThetaBelowRoot : AngleCell :=
  ⟨⟨0, 4 / 5, by norm_num⟩,
    ⟨0, 68113 / 100000, by norm_num⟩⟩

def e24ThetaAboveRoot : AngleCell :=
  ⟨⟨0, 4 / 5, by norm_num⟩,
    ⟨34069 / 50000, 4 / 5, by norm_num⟩⟩

end PartE
end GerverSofa
