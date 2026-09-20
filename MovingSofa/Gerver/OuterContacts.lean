import MovingSofa.Gerver.Contacts
import MovingSofa.Gerver.LiteralSets

noncomputable section

namespace MovingSofa

theorem gerver_outer_contact_A (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverContacts t 0 ∈ gerverOuterCap := by
  rw [mem_gerverOuterCap_iff, fromPlane_paperGerverContacts t ht 0]
  exact GerverSofa.PartC.Stage3.supportA_direct t ht

theorem gerver_outer_contact_C (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverContacts t 2 ∈ gerverOuterCap := by
  rw [mem_gerverOuterCap_iff, fromPlane_paperGerverContacts t ht 2]
  exact GerverSofa.PartC.Stage3.supportC_direct t ht

end MovingSofa
