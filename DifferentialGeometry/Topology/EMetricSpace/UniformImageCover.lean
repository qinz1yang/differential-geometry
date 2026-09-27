import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

section

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace EMetric

universe u v w

theorem TotallyBounded.exists_uniform_finite_image_cover
    {α : Type u} [PseudoEMetricSpace α] {S : Set α} (hS : TotallyBounded S)
    {ι : Type v} {β : ι → Type w} [∀ i, PseudoEMetricSpace (β i)]
    (f : ∀ i, α → β i) (C : ℝ≥0) (hf : ∀ i, LipschitzOnWith C (f i) S)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (N : Nat) (c : Fin N → α), (∀ j, c j ∈ S) ∧
      ∀ i, f i '' S ⊆ ⋃ j, Metric.eball (f i (c j)) ε := by
  classical
  let D : ℝ≥0 := C + 1
  have hDpos : (0 : ℝ≥0∞) < D := by exact_mod_cast (show (0 : ℝ≥0) < D by positivity)
  have hδpos : 0 < ε / (D : ℝ≥0∞) := ENNReal.div_pos hε.ne' ENNReal.coe_ne_top
  obtain ⟨T, hTS, hTfin, hTc⟩ := EMetric.totallyBounded_iff'.mp hS (ε / D) hδpos
  let : Fintype T := hTfin.fintype
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let c : Fin (Fintype.card T) → α := fun j => (e.symm j).1
  refine ⟨Fintype.card T, c, fun j => hTS (e.symm j).2, ?_⟩
  intro i y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxT := hTc hx
  rcases mem_iUnion₂.mp hxT with ⟨z, hz, hxz⟩
  refine mem_iUnion.mpr ⟨e ⟨z, hz⟩, ?_⟩
  have hcz : c (e ⟨z, hz⟩) = z := by simp [c]
  rw [hcz, Metric.mem_eball]
  calc
    edist (f i x) (f i z) ≤ (C : ℝ≥0∞) * edist x z := hf i hx (hTS hz)
    _ ≤ (D : ℝ≥0∞) * edist x z := mul_le_mul (by exact_mod_cast (show C ≤ D by simp [D])) le_rfl zero_le zero_le
    _ < (D : ℝ≥0∞) * (ε / D) :=
      ENNReal.mul_lt_mul_right hDpos.ne' ENNReal.coe_ne_top (Metric.mem_eball.mp hxz)
    _ = ε := ENNReal.mul_div_cancel hDpos.ne' ENNReal.coe_ne_top

end EMetric


end
