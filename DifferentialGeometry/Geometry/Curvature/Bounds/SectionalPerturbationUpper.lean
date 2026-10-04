import DifferentialGeometry.Geometry.Curvature.SectionalPerturbation
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

/-!
# Sectional curvature under a small C² metric error: upper bounds and pinching (F-a, general)

Foundation F-a of the chapter 14 boundary rows (design D-FOUND, BDRY; WBD Adapter 2), general part.
The tree already transfers LOWER sectional bounds from a reference metric `G` to a metric `g` whose
`G`-covariant derivatives of `g - G` of orders `≤ 2` are at most `ε` at a point
(`metricRm04StandardAt_lower_bound_on_range_of_small_metric_derivatives`,
`Geometry/Curvature/SectionalPerturbation.lean`, constants `240` and `360`). This file adds the
UPPER transfer (`metricRm04StandardAt_upper_bound_of_small_metric_derivatives`), the lower transfer
to a NONPOSITIVE bound (`metricRm04StandardAt_lower_bound_nonpos_of_small_metric_derivatives`; the
tree's lower transfer needs `0 ≤ c'`), and the two-sided pinching at the cusp value `-1/4`:
`ε ≤ 1/4000` and `|R_G| ≤ 10` give `-1/2 ≤ sec_g ≤ -1/8`
(`cusp_sectional_pinching_of_small_metric_derivatives`), in the forms consumed by
`SectionalBoundedBelowAt` and by the negative-plane kernels of
`BoundaryScale/CurvatureBuffers.lean`.
All constants depend on nothing but the stated numbers.
-/

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.SmoothRiemannianMetric (abs_metric_inner_le_sqrt_metric_quadratic)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

/-- Upper transfer of sectional bounds (F-a.G1): if `Rm_G(u,v,v,u) ≤ -c·gram_G(u,v)` and the
`G`-jets of `g - G` of orders `≤ 2` are at most `ε ≤ 1/2` at `x`, then
`Rm_g(u,v,v,u) ≤ -c'·gram_g(u,v)` as soon as `ε (360 + K) + (1 + ε)² c' ≤ c`, where `K` bounds
the Riemann operator of `G`. The mirror of the tree's lower transfer (whose budget has `4 c'`). -/
theorem metricRm04StandardAt_upper_bound_of_small_metric_derivatives
    (g G : SmoothRiemannianMetric I M) (x : M) {ε K c c' : ℝ}
    (hε : ε ≤ 1 / 2) (hc' : 0 ≤ c')
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ ε)
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x r r) ≤
        K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hupper : ∀ u v : TangentSpace I x,
      metricRm04StandardAt G x u v v u ≤
        -(c * (G.inner x u u * G.inner x v v - (G.inner x u v) ^ 2)))
    (hbudget : ε * (360 + K) + (1 + ε) ^ 2 * c' ≤ c) :
    ∀ u v : TangentSpace I x,
      metricRm04StandardAt g x u v v u ≤
        -(c' * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by decide)
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hm (u v : TangentSpace I x) :
      |g.inner x u v - G.inner x u v| ≤
        ε * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) :=
    (metricDifference_abs_le g G G x u v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  have htwo (u : TangentSpace I x) : g.inner x u u ≤ (1 + ε) * G.inner x u u := by
    have h := hm u u
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg G x u)] at h
    have hnonneg := metric_inner_self_nonneg G x u
    nlinarith [(abs_le.mp h).2]
  have hA : IsAlgCurvForm (fun u v w z : TangentSpace I x =>
      metricRm04StandardAt g x u v w z) :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
  have hAn : IsAlgCurvForm (fun u v w z : TangentSpace I x =>
      -metricRm04StandardAt g x u v w z) :=
    { add_left := fun a b y z w => by
        simp only [hA.add_left a b y z w]; ring
      smul_left := fun t a y z w => by
        simp only [hA.smul_left t a y z w]; ring
      anti_first := fun a b z w => by
        simp only [hA.anti_first a b z w]
      anti_last := fun a b z w => by
        simp only [hA.anti_last a b z w]
      bianchi := fun a b z w => by
        have h := hA.bianchi a b z w
        linarith }
  let G' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun u => (G.inner x u).toLinearMap
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  let g' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun u => (g.inner x u).toLinearMap
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hlow := hAn.sectional_lower_bound_of_orthogonal G' g'
    (fun u hu => G.pos x u hu) (fun u v => g.symm x u v) (c := c') (by
      intro u v huv
      change G.inner x u v = 0 at huv
      change c' * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) ≤
        -metricRm04StandardAt g x u v v u
      have hup := hupper u v
      rw [huv, sq, mul_zero, sub_zero] at hup
      have herr := abs_metricRm04StandardAt_sub_le_of_riemannOp_sub_le
        g G x hε0 hm (riemann_difference_bound_of_small_metric_derivatives g G x ε hε hsmall)
        hmodel u v
      have hGu := metric_inner_self_nonneg G x u
      have hGv := metric_inner_self_nonneg G x v
      have hP : 0 ≤ G.inner x u u * G.inner x v v := mul_nonneg hGu hGv
      have hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≤
          (1 + ε) ^ 2 * (G.inner x u u * G.inner x v v) := by
        have hh := mul_le_mul (htwo u) (htwo v) (metric_inner_self_nonneg g x v)
          (mul_nonneg (by linarith) hGu)
        nlinarith [sq_nonneg (g.inner x u v)]
      have hcoef : (1 + ε) * (240 * ε) + ε * K ≤ ε * (360 + K) := by nlinarith
      have herr' := (abs_le.mp herr).2
      have h1 : c' * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) ≤
          c' * ((1 + ε) ^ 2 * (G.inner x u u * G.inner x v v)) :=
        mul_le_mul_of_nonneg_left hgram hc'
      have h2 := mul_le_mul_of_nonneg_right hcoef hP
      have h3 := mul_le_mul_of_nonneg_right hbudget hP
      nlinarith)
  intro u v
  have h := hlow u v
  change c' * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) ≤
    -metricRm04StandardAt g x u v v u at h
  linarith

/-- Lower transfer to a nonpositive bound (F-a.G2): if `c·gram_G ≤ Rm_G(u,v,v,u)` and the
`G`-jets of `g - G` of orders `≤ 2` are at most `ε ≤ 1/2` at `x`, then `c'·gram_g ≤ Rm_g(u,v,v,u)`
for every `c' ≤ 0` with `c' (1 - 2ε) + ε (360 + K) ≤ c`. -/
theorem metricRm04StandardAt_lower_bound_nonpos_of_small_metric_derivatives
    (g G : SmoothRiemannianMetric I M) (x : M) {ε K c c' : ℝ}
    (hε : ε ≤ 1 / 2) (hc' : c' ≤ 0)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ ε)
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x r r) ≤
        K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hlower : ∀ u v : TangentSpace I x,
      c * (G.inner x u u * G.inner x v v - (G.inner x u v) ^ 2) ≤
        metricRm04StandardAt G x u v v u)
    (hbudget : c' * (1 - 2 * ε) + ε * (360 + K) ≤ c) :
    ∀ u v : TangentSpace I x,
      c' * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) ≤
        metricRm04StandardAt g x u v v u := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by decide)
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hm (u v : TangentSpace I x) :
      |g.inner x u v - G.inner x u v| ≤
        ε * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) :=
    (metricDifference_abs_le g G G x u v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  have hA : IsAlgCurvForm (fun u v w z : TangentSpace I x =>
      metricRm04StandardAt g x u v w z) :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
  let G' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun u => (G.inner x u).toLinearMap
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  let g' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun u => (g.inner x u).toLinearMap
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  refine hA.sectional_lower_bound_of_orthogonal G' g'
    (fun u hu => G.pos x u hu) (fun u v => g.symm x u v) ?_
  intro u v huv
  change G.inner x u v = 0 at huv
  change c' * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) ≤
    metricRm04StandardAt g x u v v u
  have hlo := hlower u v
  rw [huv, sq, mul_zero, sub_zero] at hlo
  have herr := abs_metricRm04StandardAt_sub_le_of_riemannOp_sub_le
    g G x hε0 hm (riemann_difference_bound_of_small_metric_derivatives g G x ε hε hsmall)
    hmodel u v
  have hGu := metric_inner_self_nonneg G x u
  have hGv := metric_inner_self_nonneg G x v
  have hP : 0 ≤ G.inner x u u * G.inner x v v := mul_nonneg hGu hGv
  have hself (z : TangentSpace I x) : (1 - ε) * G.inner x z z ≤ g.inner x z z := by
    have h := hm z z
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg G x z)] at h
    nlinarith [(abs_le.mp h).1]
  have hcross : (g.inner x u v) ^ 2 ≤ ε ^ 2 * (G.inner x u u * G.inner x v v) := by
    have h := hm u v
    rw [huv, sub_zero] at h
    have hs := sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
    rw [mul_pow, mul_pow, Real.sq_sqrt hGu, Real.sq_sqrt hGv] at hs
    linarith
  have hprod : (1 - ε) ^ 2 * (G.inner x u u * G.inner x v v) ≤
      g.inner x u u * g.inner x v v := by
    have hh := mul_le_mul (hself u) (hself v) (mul_nonneg (by linarith) hGv)
      ((mul_nonneg (by linarith) hGu).trans (hself u))
    nlinarith
  have hgram : (1 - 2 * ε) * (G.inner x u u * G.inner x v v) ≤
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
    nlinarith
  have hcoef : (1 + ε) * (240 * ε) + ε * K ≤ ε * (360 + K) := by nlinarith
  have herr' := (abs_le.mp herr).1
  have h1 : c' * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) ≤
      c' * ((1 - 2 * ε) * (G.inner x u u * G.inner x v v)) :=
    mul_le_mul_of_nonpos_left hgram hc'
  have h2 := mul_le_mul_of_nonneg_right hcoef hP
  have h3 := mul_le_mul_of_nonneg_right hbudget hP
  nlinarith

/-- Pinching at the cusp value (F-a.G2, cusp numbers of BSA01 / WBD Adapter 2): if the reference
metric has `Rm_G(u,v,v,u) = -¼·gram_G(u,v)` at `x`, its Riemann operator is bounded by `K ≤ 10`, and
the `G`-jets of `g - G` of orders `≤ 2` are at most `ε ≤ 1/4000`, then `sec_g ≥ -1/2` and
`Rm_g(u,v,v,u) ≤ -⅛·gram_g(u,v)` at `x`. -/
theorem cusp_sectional_pinching_of_small_metric_derivatives
    (g G : SmoothRiemannianMetric I M) (x : M) {ε K : ℝ}
    (hε : ε ≤ 1 / 4000) (hK : K ≤ 10)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ ε)
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x r r) ≤
        K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hconst : ∀ u v : TangentSpace I x,
      metricRm04StandardAt G x u v v u =
        -(1 / 4 : ℝ) * (G.inner x u u * G.inner x v v - (G.inner x u v) ^ 2)) :
    SectionalBoundedBelowAt g x (-(1 / 2)) ∧
      ∀ u v : TangentSpace I x,
        metricRm04StandardAt g x u v v u ≤
          -((1 / 8 : ℝ) * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)) := by
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hεK : ε * (360 + K) ≤ 370 * ε := by nlinarith
  refine ⟨metricRm04StandardAt_lower_bound_nonpos_of_small_metric_derivatives g G x
    (c := -(1 / 4)) (c' := -(1 / 2)) (by linarith) (by norm_num) hsmall hmodel
    (fun u v => (hconst u v).ge) (by nlinarith), ?_⟩
  exact metricRm04StandardAt_upper_bound_of_small_metric_derivatives g G x
    (c := 1 / 4) (c' := 1 / 8) (by linarith) (by norm_num) hsmall hmodel
    (fun u v => by rw [hconst u v]; ring_nf; exact le_rfl) (by nlinarith)

end DifferentialGeometry.Geometry.Curvature
