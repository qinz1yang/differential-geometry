import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Projection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem dist_lineProjection_eq_iff_norm_normal_eq
    (e : E) (he : ‖e‖ = 1) (x : Hyperboloid E) (R : ℝ) (hR : 0 ≤ R) :
    dist x (lineProjection e he x) = R ↔
      ‖x.space - inner ℝ x.space e • e‖ = Real.sinh R := by
  have hc := cosh_dist_lineProjection e he x
  have hs := Real.cosh_sq_sub_sinh_sq R
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + ‖x.space - inner ℝ x.space e • e‖ ^ 2 by positivity)
  have hsn : 0 ≤ Real.sinh R := Real.sinh_nonneg_iff.mpr hR
  constructor
  · intro hd
    rw [hd] at hc
    rw [← hc] at hsq
    nlinarith [norm_nonneg (x.space - inner ℝ x.space e • e)]
  · intro hn
    rw [hn] at hc
    have heq : Real.sqrt (1 + Real.sinh R ^ 2) = Real.cosh R := by
      apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.cosh_pos R).le).mp
      rw [Real.sq_sqrt (by positivity)]
      linarith only [hs]
    rw [heq] at hc
    have hh := congrArg Real.arcosh hc
    simpa only [Real.arcosh_cosh dist_nonneg, Real.arcosh_cosh hR] using hh

theorem isPathConnected_setOf_dist_lineProjection_eq
    (e : E) (he : ‖e‖ = 1)
    (hdim : 1 < Module.rank ℝ ((ℝ ∙ e)ᗮ : Submodule ℝ E))
    (R : ℝ) (hR : 0 ≤ R) :
    IsPathConnected {x : Hyperboloid E | dist x (lineProjection e he x) = R} := by
  let N : Submodule ℝ E := (ℝ ∙ e)ᗮ
  let f : ℝ × N → Hyperboloid E := fun z => ofSpace (z.1 • e + (z.2 : E))
  have hf : Continuous f := continuous_ofSpace.comp
    ((continuous_fst.smul continuous_const).add (continuous_subtype_val.comp continuous_snd))
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have himage : f '' ((Set.univ : Set ℝ) ×ˢ Metric.sphere (0 : N) (Real.sinh R)) =
      {x : Hyperboloid E | dist x (lineProjection e he x) = R} := by
    ext x
    constructor
    · rintro ⟨⟨a, u⟩, ⟨_, hu⟩, rfl⟩
      apply (dist_lineProjection_eq_iff_norm_normal_eq e he (f (a, u)) R hR).mpr
      have huorth : inner ℝ (u : E) e = 0 :=
        Submodule.mem_orthogonal_singleton_iff_inner_left.mp u.property
      have hunorm : ‖(u : E)‖ = Real.sinh R := by
        simpa only [Metric.mem_sphere, dist_zero_right, Submodule.norm_coe] using hu
      change ‖(a • e + (u : E)) - inner ℝ (a • e + (u : E)) e • e‖ = _
      rw [inner_add_left, real_inner_smul_left, hee, huorth, mul_one, add_zero]
      simpa only [add_sub_cancel_left] using hunorm
    · intro hx
      have hn := (dist_lineProjection_eq_iff_norm_normal_eq e he x R hR).mp hx
      let v := x.space - inner ℝ x.space e • e
      have hv : v ∈ N := by
        apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
        dsimp only [v]
        rw [inner_sub_left, real_inner_smul_left, hee, mul_one, sub_self]
      let u : N := ⟨v, hv⟩
      refine ⟨(inner ℝ x.space e, u), ⟨Set.mem_univ _, ?_⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_zero_right]
        change ‖x.space - inner ℝ x.space e • e‖ = Real.sinh R
        exact hn
      · apply ext
        change inner ℝ x.space e • e + (x.space - inner ℝ x.space e • e) = x.space
        abel
  rw [← himage]
  exact (isPathConnected_univ.prod
    (isPathConnected_sphere hdim (0 : N) (Real.sinh_nonneg_iff.mpr hR))).image hf

theorem isPathConnected_setOf_dist_lineProjection_eq_of_finrank
    [FiniteDimensional ℝ E] (hdim : 3 ≤ Module.finrank ℝ E)
    (e : E) (he : ‖e‖ = 1) (R : ℝ) (hR : 0 ≤ R) :
    IsPathConnected {x : Hyperboloid E | dist x (lineProjection e he x) = R} := by
  have he0 : e ≠ 0 := by intro hh; rw [hh, norm_zero] at he; norm_num at he
  have hd := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ e)
  rw [finrank_span_singleton he0] at hd
  have hn : 1 < Module.finrank ℝ ((ℝ ∙ e)ᗮ : Submodule ℝ E) := by omega
  apply isPathConnected_setOf_dist_lineProjection_eq e he _ R hR
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hn

end DifferentialGeometry.Hyperboloid
