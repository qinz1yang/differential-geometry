import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Map

open scoped ENNReal

namespace MeasureTheory

theorem isFundamentalDomain_preimage_of_equivariant
    {Γ X Y : Type*} [Group Γ] [MulAction Γ X] [MulAction Γ Y]
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    {p : X → Y} (hp : Measurable p)
    (hequiv : ∀ (γ : Γ) (x : X), p (γ • x) = γ • p x)
    {D : Set Y} (hD : MeasurableSet D)
    (hrep : ∀ y : Y, ∃! γ : Γ, γ • y ∈ D) :
    IsFundamentalDomain Γ (p ⁻¹' D) μ := by
  apply IsFundamentalDomain.mk' (hD.preimage hp).nullMeasurableSet
  intro x
  simpa only [Set.mem_preimage, hequiv] using hrep (p x)

theorem hasFundamentalDomain_and_covolume_ne_top_of_map_eq_smul
    {Γ X Y : Type*} [Group Γ] [MulAction Γ X] [MulAction Γ Y]
    [MeasurableSpace X] [MeasurableSpace Y] [Countable Γ]
    [MeasurableConstSMul Γ X] (μ : Measure X) [SMulInvariantMeasure Γ X μ]
    (ν : Measure Y) {p : X → Y} (hp : Measurable p)
    (hequiv : ∀ (γ : Γ) (x : X), p (γ • x) = γ • p x)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (hmap : Measure.map p μ = c • ν)
    {D : Set Y} (hD : MeasurableSet D)
    (hrep : ∀ y : Y, ∃! γ : Γ, γ • y ∈ D) (hfin : ν D ≠ ⊤) :
    HasFundamentalDomain Γ X μ ∧ covolume Γ X μ ≠ ⊤ := by
  have hF := isFundamentalDomain_preimage_of_equivariant μ hp hequiv hD hrep
  refine ⟨hF.hasFundamentalDomain μ, ?_⟩
  rw [hF.covolume_eq_volume μ, ← Measure.map_apply hp hD, hmap,
    Measure.smul_apply]
  exact ENNReal.mul_ne_top hc hfin

end MeasureTheory
