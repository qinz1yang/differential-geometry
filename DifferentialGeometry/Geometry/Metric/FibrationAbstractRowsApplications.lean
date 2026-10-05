import DifferentialGeometry.Analysis.Calculus.FibrationCalculusRows
import DifferentialGeometry.Analysis.InnerProductSpace.FibrationGraphRows
import DifferentialGeometry.Geometry.Metric.CloudRows

/-!
# Consumers of the abstract chapter 14 row wrappers (FC05, FC06, FC46, FC32)

* `fc46_two_node_chain`: a two-node chain `c ≺ Δ` with `0 < c < 1` (upper-bound node) and
  `Δ > 1/c` (lower-bound node) has a simultaneous solution.
* `fc06_identity_graph_onto`: the graph `z ↦ (z, 0)` of `ℝ` in `ℝ ⊕ ℝ` with `L = id`, `D = T L`:
  the projected map is onto the plane.
* `fc05_zero_cutoff_pointwise`: FC05's pointwise bound for the zero profile.
* `fc32_trivial_adjustment`: with the cutoff `0` the adjustment is the identity on `Q⊥`
  coordinates (FC32's third clause, concrete subspace `⊤` of `ℝ`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace DifferentialGeometry.Analysis

/-- FC46 on a two-node chain. -/
theorem fc46_two_node_chain :
    ∃ f : Fin 2 → ℝ, (∀ i, 0 < f i) ∧ f 0 < 1 ∧ 1 / f 0 < f 1 := by
  let r : Fin 2 → Fin 2 → Prop := fun j i => j < i
  have hr : ∀ i, ¬ Relation.TransGen r i i := by
    intro i h
    have : ∀ a b, Relation.TransGen r a b → a < b := fun a b hab =>
      Relation.TransGen.trans_induction_on hab (fun h => h) (fun _ _ h₁ h₂ => h₁.trans h₂)
    exact lt_irrefl i (this i i h)
  let A : ∀ i, (∀ j, r j i → ℝ) → Set ℝ := fun i v =>
    if h1 : i = 1 then {x | 0 < x ∧ ∀ b ∈ ({1 / v 0 (by subst h1; decide)} : Finset ℝ), b < x}
    else {x | 0 < x ∧ ∀ b ∈ ({1} : Finset ℝ), x < b}
  obtain ⟨f, hpos, hf⟩ := fc46_row hr A (fun i v _ => by
    by_cases h1 : i = 1
    · subst h1
      exact Or.inr (Or.inl ⟨{1 / v 0 (by decide)}, by simp [A]⟩)
    · exact Or.inl ⟨{1}, by simp, by simp [A, h1]⟩)
  refine ⟨f, hpos, ?_, ?_⟩
  · have h0 : 0 < f 0 ∧ f 0 < 1 := by simpa [A] using hf 0
    exact h0.2
  · have h1 : 0 < f 1 ∧ (f 0)⁻¹ < f 1 := by simpa [A] using hf 1
    simpa using h1.2

/-- FC06 for the identity graph of `ℝ` in `ℝ ⊕ ℝ`. -/
theorem fc06_identity_graph_onto :
    let T : ℝ →L[ℝ] WithLp 2 (ℝ × ℝ) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.id ℝ ℝ).prod 0)
    Function.Surjective (T.range.orthogonalProjectionOnto.comp
      (T.comp (ContinuousLinearMap.id ℝ ℝ))) := by
  intro T
  have h := fc06_row (V := ℝ) (0 : ℝ →L[ℝ] ℝ) T (fun z => rfl) (b := ‖T‖) le_rfl
    (ContinuousLinearMap.id ℝ ℝ) ContinuousLinearMap.norm_id_le one_pos
    (fun z => by simp [ContinuousLinearMap.adjoint_id])
    (T.comp (ContinuousLinearMap.id ℝ ℝ)) (by simp) one_pos
  exact h.1

/-- FC05's pointwise bound for the zero profile (all four constants zero). -/
theorem fc05_zero_cutoff_pointwise (y₁ y₂ : ℝ) (a b : ℝ →L[ℝ] ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ‖y₁ - y₂‖ ≤ ε) (hDclose : ‖a - b‖ ≤ ε) :
    max ‖scaledCutoffBlock 1 (fun _ : ℝ => (0 : ℝ)) y₁ - scaledCutoffBlock 1 (fun _ => 0) y₂‖
      ‖(fderiv ℝ (scaledCutoffBlock 1 (fun _ : ℝ => (0 : ℝ))) y₁).comp a -
        (fderiv ℝ (scaledCutoffBlock 1 (fun _ : ℝ => (0 : ℝ))) y₂).comp b‖ ≤ ε := by
  have h := fc05_row_pointwise (φ := fun _ : ℝ => (0 : ℝ)) contDiff_const (s := 1) (C := 0)
    (L₁ := 0) (L₂ := 0) one_pos le_rfl le_rfl le_rfl (fun _ => by simp)
    (by simp) (fun _ => by simp) (fun _ => by simp)
    y₁ y₂ a b hε (norm_nonneg b) hclose hDclose le_rfl
  simpa using h

/-- FC32's `Q⊥` clause for the whole line `Q = ⊤` and cutoff `0`. -/
theorem fc32_trivial_adjustment (y : ℝ) :
    (⊤ : Submodule ℝ ℝ)ᗮ.starProjection
        (adjustmentMap ⊤ id ((fun _ : ℝ => (0 : ℝ)) ∘ (⊤ : Submodule ℝ ℝ).starProjection) y) =
      (⊤ : Submodule ℝ ℝ)ᗮ.starProjection y :=
  (fc32_row (E := ℝ) ⊤ (P := id) (fun _ => Submodule.mem_top) ⊤ le_rfl (fun _ => 0)
    id).2.2.2.1 y

end DifferentialGeometry.Analysis
