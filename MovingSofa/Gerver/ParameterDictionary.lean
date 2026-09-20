import MovingSofa.Gerver.Parameters

noncomputable section

namespace MovingSofa

def gerverParameterDictionary :
    (GerverSofa.Reduced.Params → GerverSofa.Romik.Params) ×
      (GerverSofa.Romik.Params → GerverSofa.Reduced.Params) :=
  (GerverSofa.PartF.Phases.dictionary, GerverSofa.PartF.Phases.undictionary)

end MovingSofa
