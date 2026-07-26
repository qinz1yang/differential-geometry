import DifferentialGeometry.Geometry.Metric.Sphere.OrthogonalAction
import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConn
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Extending tangent isometries of the round sphere

This file extends a prescribed isometry between two tangent spaces of the unit
sphere to an ambient orthogonal transformation.
-/

noncomputable section

open Bundle Manifold Set Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- A round-metric isometry between tangent spaces at two points of the unit
sphere is induced by an ambient orthogonal transformation. -/
theorem ambient_iso_of_tan
    (p q : sphere (0 : E) 1)
    (L : TangentSpace (𝓡 n) p ≃L[ℝ] TangentSpace (𝓡 n) q)
    (hL : ∀ v w,
      (roundMetric (E := E) (n := n)).inner q (L v) (L w) =
        (roundMetric (E := E) (n := n)).inner p v w) :
    ∃ e : E ≃ₗᵢ[ℝ] E,
      e (p : E) = (q : E) ∧
        ∀ v, mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) p v = L v := by
  let P : Submodule ℝ E := (ℝ ∙ (p : E))ᗮ
  let Q : Submodule ℝ E := (ℝ ∙ (q : E))ᗮ
  let Tc : P ≃L[ℝ] Q :=
    (dInclEquiv (n := n) p).symm.trans
      (L.trans (dInclEquiv (n := n) q))
  have hTc : ∀ v w : P, inner ℝ (Tc v) (Tc w) = inner ℝ v w := by
    intro v w
    have hv :
        dIncl (n := n) p ((dInclEquiv (n := n) p).symm v) = (v : E) := by
      rw [← dInclEquiv_coe (n := n) p]
      exact congrArg Subtype.val ((dInclEquiv (n := n) p).apply_symm_apply v)
    have hw :
        dIncl (n := n) p ((dInclEquiv (n := n) p).symm w) = (w : E) := by
      rw [← dInclEquiv_coe (n := n) p]
      exact congrArg Subtype.val ((dInclEquiv (n := n) p).apply_symm_apply w)
    change
      inner ℝ
          (dIncl (n := n) q
            (L ((dInclEquiv (n := n) p).symm v)))
          (dIncl (n := n) q
            (L ((dInclEquiv (n := n) p).symm w))) =
        inner ℝ (v : E) (w : E)
    calc
      _ = (roundMetric (E := E) (n := n)).inner q
          (L ((dInclEquiv (n := n) p).symm v))
          (L ((dInclEquiv (n := n) p).symm w)) := by
            rw [roundMetric_inner]
      _ = (roundMetric (E := E) (n := n)).inner p
          ((dInclEquiv (n := n) p).symm v)
          ((dInclEquiv (n := n) p).symm w) :=
            hL _ _
      _ = inner ℝ
          (dIncl (n := n) p ((dInclEquiv (n := n) p).symm v))
          (dIncl (n := n) p ((dInclEquiv (n := n) p).symm w)) := by
            rw [roundMetric_inner]
      _ = _ := by rw [hv, hw]
  let T : P ≃ₗᵢ[ℝ] Q := Tc.toLinearEquiv.isometryOfInner hTc
  let T₀ : P →ₗᵢ[ℝ] E := Q.subtypeₗᵢ.comp T.toLinearIsometry
  let F : E →ₗᵢ[ℝ] E := T₀.extend
  have hFsurj : Function.Surjective F :=
    LinearMap.injective_iff_surjective.mp F.injective
  let e₀ : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.ofSurjective F hFsurj
  have he₀_perp (v : P) : e₀ (v : E) = (T v : Q) := by
    change F (v : E) = (T v : Q)
    simpa only [F, T₀, LinearIsometry.coe_comp, Function.comp_apply,
      Submodule.coe_subtypeₗᵢ] using LinearIsometry.extend_apply T₀ v
  have he₀_span : e₀ (p : E) ∈ ℝ ∙ (q : E) := by
    rw [← Submodule.orthogonal_orthogonal (ℝ ∙ (q : E)),
      Submodule.mem_orthogonal']
    intro w hw
    let wQ : Q := ⟨w, hw⟩
    let vP : P := T.symm wQ
    have hw_eq : e₀ (vP : E) = w := by
      rw [he₀_perp]
      exact congrArg Subtype.val (T.apply_symm_apply wQ)
    rw [← hw_eq, e₀.inner_map_map]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp vP.2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp he₀_span
  have hc_abs : |c| = 1 := by
    have hp_norm : ‖(p : E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
    have hq_norm : ‖(q : E)‖ = 1 := mem_sphere_zero_iff_norm.mp q.2
    have hnorm := congrArg norm hc
    simpa only [norm_smul, Real.norm_eq_abs, hq_norm, mul_one, e₀.norm_map,
      hp_norm] using hnorm
  have he₀_sign : e₀ (p : E) = (q : E) ∨ e₀ (p : E) = -(q : E) := by
    rcases (abs_eq (by positivity : (0 : ℝ) ≤ 1)).mp hc_abs with hc1 | hc1
    · left
      rw [← hc, hc1, one_smul]
    · right
      rw [← hc, hc1, neg_smul, one_smul]
  have he₀_tan (v : TangentSpace (𝓡 n) p) :
      e₀ (dIncl (n := n) p v) = dIncl (n := n) q (L v) := by
    let vP : P := dInclEquiv (n := n) p v
    have hvP : (vP : E) = dIncl (n := n) p v :=
      dInclEquiv_coe (n := n) p v
    rw [← hvP, he₀_perp]
    have hTapp : T vP = dInclEquiv (n := n) q (L v) := by
      change Tc vP = dInclEquiv (n := n) q (L v)
      simp only [Tc, vP, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.symm_apply_apply]
    rw [hTapp]
    exact dInclEquiv_coe (n := n) q (L v)
  rcases he₀_sign with he₀p | he₀p
  · refine ⟨e₀, he₀p, ?_⟩
    intro v
    have hφ : sphereDiffeo (n := n) e₀ p = q := by
      apply Subtype.ext
      simpa only [sphereDiffeo_coe] using he₀p
    apply mfderiv_coe_sphere_injective q
    change dIncl (n := n) q
      (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e₀) p v) =
        dIncl (n := n) q (L v)
    calc
      _ = dIncl (n := n) (sphereDiffeo (n := n) e₀ p)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e₀) p v) := by
            rw [hφ]
      _ = e₀ (dIncl (n := n) p v) :=
        mfderiv_incl_sphereDiffeo e₀ p v
      _ = _ := he₀_tan v
  · let R : E ≃ₗᵢ[ℝ] E := Q.reflection
    let e : E ≃ₗᵢ[ℝ] E := e₀.trans R
    have hep : e (p : E) = (q : E) := by
      dsimp only [e]
      rw [LinearIsometryEquiv.trans_apply, he₀p, map_neg]
      change -Q.reflection (q : E) = (q : E)
      rw [Submodule.reflection_mem_subspace_orthogonal_precomplement_eq_neg
        (Submodule.mem_span_singleton_self (q : E))]
      simp only [neg_neg]
    refine ⟨e, hep, ?_⟩
    intro v
    have hφ : sphereDiffeo (n := n) e p = q := by
      apply Subtype.ext
      simpa only [sphereDiffeo_coe] using hep
    apply mfderiv_coe_sphere_injective q
    change dIncl (n := n) q
      (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) p v) =
        dIncl (n := n) q (L v)
    calc
      _ = dIncl (n := n) (sphereDiffeo (n := n) e p)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) p v) := by
            rw [hφ]
      _ = e (dIncl (n := n) p v) :=
        mfderiv_incl_sphereDiffeo e p v
      _ = R (e₀ (dIncl (n := n) p v)) := rfl
      _ = R (dIncl (n := n) q (L v)) := congrArg R (he₀_tan v)
      _ = _ := by
        rw [← dInclEquiv_coe (n := n) q]
        exact Submodule.reflection_mem_subspace_eq_self
          ((dInclEquiv (n := n) q (L v)).2)

end Geometry
end DifferentialGeometry
