import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Matrix

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_pos_mul_dotProduct_le_chartGramMatrix
    (g : SmoothRiemannianMetric I M) (alpha : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (trivializationAt E (TangentSpace I) alpha).baseSet) :
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ K, ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      c * (ξ ⬝ᵥ ξ) ≤ ξ ⬝ᵥ chartGramMatrix g alpha b *ᵥ ξ := by
  classical
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let Q : M × V → ℝ := fun p => p.2.ofLp ⬝ᵥ chartGramMatrix g alpha p.1 *ᵥ p.2.ofLp
  have hcont : ContinuousOn Q (K ×ˢ (Set.univ : Set V)) := by
    apply continuousOn_finsetSum
    intro i _
    apply ContinuousOn.mul
    · exact ((PiLp.continuous_apply 2 _ i).comp continuous_snd).continuousOn
    · change ContinuousOn (fun a : M × V => ∑ j, chartGramMatrix g alpha a.1 i j * a.2 j) _
      apply continuousOn_finsetSum
      intro j _
      exact (((chartGramMatrix_entry_contMDiffOn g alpha i j).continuousOn.mono hKchart).comp
        continuous_fst.continuousOn (fun _ hp => hp.1)).mul
          (((PiLp.continuous_apply 2 _ j).comp continuous_snd).continuousOn)
  have hnorm (v : V) : ‖v‖ ^ 2 = v.ofLp ⬝ᵥ v.ofLp := by
    simpa only [dotProduct, ← sq] using EuclideanSpace.real_norm_sq_eq v
  have hsphere (v : V) (hv : v ≠ 0) : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hQscale (b : M) (v : V) (r : ℝ) : Q (b, r • v) = r ^ 2 * Q (b, v) := by
    change (r • v.ofLp) ⬝ᵥ chartGramMatrix g alpha b *ᵥ (r • v.ofLp) = _
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  by_cases hnonempty : (K ×ˢ Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨p, hp, hmin⟩ := (hK.prod (isCompact_sphere (0 : V) 1)).exists_isMinOn hnonempty
      (hcont.mono (Set.prod_mono_right (Set.subset_univ _)))
    have hpne : p.2.ofLp ≠ 0 := by
      intro heq
      have hz : p.2 = 0 := (WithLp.ofLp_injective 2) heq
      have : (0 : ℝ) = 1 := by simpa only [hz, Metric.mem_sphere, dist_self] using hp.2
      exact zero_ne_one this
    have hpQ : 0 < Q p := by
      simpa only [Q, star_trivial] using
        (chartGramMatrix_posDef g alpha (hKchart hp.1)).dotProduct_mulVec_pos hpne
    refine ⟨Q p, hpQ, fun b hb ξ => ?_⟩
    let v : V := WithLp.toLp 2 ξ
    by_cases hv : v = 0
    · have hξ : ξ = 0 := congrArg WithLp.ofLp hv
      simp only [hξ, dotProduct_zero, mul_zero, Matrix.mulVec_zero, le_refl]
    · have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hlower : Q p ≤ Q (b, ‖v‖⁻¹ • v) :=
        hmin (show (b, ‖v‖⁻¹ • v) ∈ K ×ˢ Metric.sphere (0 : V) 1 from ⟨hb, hsphere v hv⟩)
      rw [hQscale] at hlower
      have hmul := mul_le_mul_of_nonneg_right hlower (sq_nonneg ‖v‖)
      have hcancel : (‖v‖⁻¹ ^ 2 * Q (b, v)) * ‖v‖ ^ 2 = Q (b, v) := by
        field_simp
      rw [hcancel, hnorm] at hmul
      exact hmul
  · refine ⟨1, zero_lt_one, fun b hb ξ => ?_⟩
    let v : V := WithLp.toLp 2 ξ
    have hv : v = 0 := by
      by_contra hv
      exact hnonempty ⟨(b, ‖v‖⁻¹ • v), hb, hsphere v hv⟩
    have hξ : ξ = 0 := congrArg WithLp.ofLp hv
    simp only [hξ, dotProduct_zero, mul_zero, Matrix.mulVec_zero, le_refl]

end DifferentialGeometry.Tensor.Coordinates
