import DifferentialGeometry.Analysis.InnerProductSpace.AdjustmentFactorization
import DifferentialGeometry.Geometry.Metric.RetainedMarkerBindings

/-! CFS29 (master207B, B:3733): one adjustment stage preserves the small originally zero markers.

The stage is FC32's `adjustmentMap Q P ψ`. Outside the cutoff support it is the identity. On the support the cutoff
localizes the ORIGINAL point to the stage core (`π_Q F q ∈ S`), CFS16 puts the projected input in the core ball
`B(x, σ ρ(select x))`, and there the stage projection has zero small blocks (`hnear`, supplied for the actual
CFS14 nearest map by CFS28 → CFS24, see `ActualCloudStageBinding`). A retained block is a blend of two zeros; a block
outside `Q` is unchanged (FC32). The threshold uses the ORIGINAL `ρ(q)`. -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis

namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The blend of two zero `V` blocks: a retained block (`V ≤ Q`) stays zero where the projection has zero `V` block,
and a block orthogonal to `Q` is not moved by the adjustment. -/
theorem actualCloud_adjustment_block_eq_zero (Q V : Submodule ℝ H) {P : H → H} (hP : ∀ z, P z ∈ Q)
    (ψ : H → ℝ) {y : H} (hy : V.starProjection y = 0)
    (hcase : (V ≤ Q ∧ (ψ y ≠ 0 → V.starProjection (P (Q.starProjection y)) = 0)) ∨ V ≤ Qᗮ) :
    V.starProjection (adjustmentMap Q P ψ y) = 0 := by
  rw [adjustmentMap_apply, map_add, map_smul, hy, zero_add]
  rcases hcase with ⟨hVQ, hnear⟩ | hVQ
  · have hproj : V.starProjection (Q.starProjection y) = V.starProjection y := by
      have := congrArg (fun L : H →L[ℝ] H => L y)
        (Submodule.starProjection_comp_starProjection_of_le hVQ)
      simpa using this
    by_cases hψ : ψ y = 0
    · rw [hψ, zero_smul]
    · rw [map_sub, hproj, hy, sub_zero, hnear hψ, smul_zero]
  · have hQV : Q ≤ Vᗮ := (Submodule.le_orthogonal_orthogonal Q).trans (Submodule.orthogonal_le hVQ)
    have hmem : P (Q.starProjection y) - Q.starProjection y ∈ Vᗮ :=
      hQV (Q.sub_mem (hP _) (Q.starProjection_apply_mem y))
    rw [(V.starProjection_apply_eq_zero_iff).mpr hmem, smul_zero]

/-- CFS29: one stage preserves the zero small markers (`R_i < ρ(q)/16`, original `ρ`). -/
theorem actualCloud_stage_small_marker_preservation {M A : Type*}
    (Q : Submodule ℝ H) (Pst : H → H) (hP : ∀ z, Pst z ∈ Q) (ψ : H → ℝ)
    (F f : M → H) (ρ : M → ℝ) (V : A → Submodule ℝ H) (marker : A → H → ℝ) (R : A → ℝ)
    (hR : ∀ i, 0 < R i)
    (hsupport : ∀ i q, 0 < marker i (Q.starProjection (F q)) →
      3 * R i / 4 ≤ ρ q ∧ ρ q ≤ 5 * R i / 4)
    (hfull : ∀ q, ψ (f q) ≠ 0 → ∃ i, marker i (Q.starProjection (F q)) = R i)
    (S : Set H) (select : H → M) (hselect : ∀ x ∈ S, Q.starProjection (F (select x)) = x)
    {σ e : ℝ} (hσ : 0 < σ) (he : e ≤ 3 * σ / 10)
    (hloc : ∀ q, ψ (f q) ≠ 0 → Q.starProjection (F q) ∈ S)
    (herror : ∀ q, ψ (f q) ≠ 0 → ‖f q - F q‖ ≤ e * ρ q)
    (hnear : ∀ x ∈ S, ∀ z ∈ ball x (σ * ρ (select x)), ∀ q, Q.starProjection (F q) = x →
      ∀ i, R i < ρ q / 16 → (V i).starProjection (Pst z) = 0)
    (hretained : ∀ i, V i ≤ Q ∨ V i ≤ Qᗮ)
    (hinput : ∀ q i, R i < ρ q / 16 → (V i).starProjection (f q) = 0) :
    ∀ q i, R i < ρ q / 16 → (V i).starProjection (adjustmentMap Q Pst ψ (f q)) = 0 := by
  intro q i hi
  apply actualCloud_adjustment_block_eq_zero Q (V i) hP ψ (hinput q i hi)
  rcases hretained i with hVQ | hVQ
  · refine Or.inl ⟨hVQ, fun hψ => ?_⟩
    set x := Q.starProjection (F q) with hxdef
    have hx : x ∈ S := hloc q hψ
    obtain ⟨j, hj⟩ := hfull q hψ
    have hbuf := retained_marker_projected_half_buffer Q.starProjection
      (Submodule.starProjection_norm_le Q) F f ρ marker R hR hsupport q (select x)
      (hselect x hx).symm j hj σ e hσ he (herror q hψ)
    obtain ⟨hr, -, -, hd, -⟩ := hbuf
    have hz : Q.starProjection (f q) ∈ ball x (σ * ρ (select x)) := by
      rw [mem_ball, dist_eq_norm]
      exact hd.trans_lt (half_lt_self hr)
    exact hnear x hx _ hz q rfl i hi
  · exact Or.inr hVQ

end GC.MetricGeometry
