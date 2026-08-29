import Mathlib.Geometry.Manifold.ChartedSpace

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry
namespace Geometry

variable {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M]

theorem exists_chart_head
    {a b : Real} (hab : a < b) {gamma : Real → M}
    (hgamma : ContinuousOn gamma (Icc a b)) {p : M}
    (hp : gamma a ∈ (chartAt H p).source) :
    ∃ c : Real, a < c ∧ c ≤ b ∧
      MapsTo gamma (Icc a c) (chartAt H p).source := by
  have hcont : ContinuousWithinAt gamma (Icc a b) a :=
    hgamma a ⟨le_rfl, hab.le⟩
  have hpre : gamma ⁻¹' (chartAt H p).source ∈ 𝓝[Icc a b] a :=
    hcont ((chartAt H p).open_source.mem_nhds hp)
  rw [nhdsWithin_Icc_eq_nhdsGE hab] at hpre
  have hinter : gamma ⁻¹' (chartAt H p).source ∩ Icc a b ∈ 𝓝[≥] a :=
    inter_mem hpre (Icc_mem_nhdsGE hab)
  obtain ⟨c, hac, hsub⟩ :=
    mem_nhdsGE_iff_exists_Icc_subset.mp hinter
  have hc : c ∈ gamma ⁻¹' (chartAt H p).source ∩ Icc a b :=
    hsub ⟨hac.le, le_rfl⟩
  exact ⟨c, hac, hc.2.2, fun s hs ↦ (hsub hs).1⟩

end Geometry
end DifferentialGeometry
