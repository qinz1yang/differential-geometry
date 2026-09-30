import DifferentialGeometry.Geometry.Curvature.Algebraic.SectionalLowerBound
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Geometry.Curvature.RiemannPerturbation
import DifferentialGeometry.Geometry.Curvature.SectionalOrthonormalization
import DifferentialGeometry.Geometry.Curvature.Product

open DifferentialGeometry.SmoothRiemannianMetric
  (abs_metric_inner_le_sqrt_metric_quadratic)

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

section

open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.CheegerGromovCompactness

theorem abs_metricRm04StandardAt_sub_le_of_riemannOp_sub_le
    (g G : SmoothRiemannianMetric I M) (x : M) {delta R K : ℝ}
    (hdelta : 0 ≤ delta)
    (hmetric : ∀ u v : TangentSpace I x,
      |g.inner x u v - G.inner x u v| ≤
        delta * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v))
    (hdiff : ∀ u v w : TangentSpace I x,
      let d := riemannOp (LeviCivita g) x u v w - riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x d d) ≤
        R * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x r r) ≤
        K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (u v : TangentSpace I x) :
    |metricRm04StandardAt g x u v v u - metricRm04StandardAt G x u v v u| ≤
      ((1 + delta) * R + delta * K) * G.inner x u u * G.inner x v v := by
  let N (z : TangentSpace I x) := Real.sqrt (G.inner x z z)
  let r := riemannOp (LeviCivita g) x u v v
  let r0 := riemannOp (LeviCivita G) x u v v
  let d := r - r0
  have hd : N d ≤ R * N u * N v * N v := hdiff u v v
  have hr0 : N r0 ≤ K * N u * N v * N v := hmodel u v v
  have hr : N r ≤ (R + K) * N u * N v * N v := by
    have heq : r = d + r0 := by dsimp [d]; abel
    calc
      N r = N (d + r0) := congrArg N heq
      _ ≤ N d + N r0 := sqrt_inner_add_le G x d r0
      _ ≤ R * N u * N v * N v + K * N u * N v * N v := add_le_add hd hr0
      _ = _ := by ring
  have hmet : |g.inner x u r - G.inner x u r| ≤
      delta * N u * ((R + K) * N u * N v * N v) :=
    (hmetric u r).trans (mul_le_mul_of_nonneg_left hr (mul_nonneg hdelta (Real.sqrt_nonneg _)))
  have hcurv : |G.inner x u r - G.inner x u r0| ≤
      N u * (R * N u * N v * N v) := by
    rw [← map_sub]
    exact (abs_metric_inner_le_sqrt_metric_quadratic G x u d).trans
      (mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _))
  rw [metricRm04StandardAt_eq_inner_riemannOp, metricRm04StandardAt_eq_inner_riemannOp]
  change |g.inner x u r - G.inner x u r0| ≤ _
  calc
    _ ≤ |g.inner x u r - G.inner x u r| + |G.inner x u r - G.inner x u r0| :=
      abs_sub_le _ _ _
    _ ≤ delta * N u * ((R + K) * N u * N v * N v) +
        N u * (R * N u * N v * N v) := add_le_add hmet hcurv
    _ = ((1 + delta) * R + delta * K) * (N u) ^ 2 * (N v) ^ 2 := by ring
    _ = _ := by
      dsimp only [N]
      rw [Real.sq_sqrt (metric_inner_self_nonneg G x u),
        Real.sq_sqrt (metric_inner_self_nonneg G x v)]

theorem metricRm04StandardAt_lower_bound_on_range_of_riemannOp_sub_le
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g G : SmoothRiemannianMetric I M) (x : M)
    (e : V →ₗ[ℝ] TangentSpace I x) (he : Function.Injective e) {delta R K c c' L : ℝ}
    (hdelta : 0 ≤ delta) (hc' : 0 ≤ c') (hL : 0 ≤ L)
    (hmetric : ∀ u v : TangentSpace I x,
      |g.inner x u v - G.inner x u v| ≤
        delta * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v))
    (hdiff : ∀ u v w : TangentSpace I x,
      let d := riemannOp (LeviCivita g) x u v w - riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x d d) ≤
        R * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x r r) ≤
        K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hupper : ∀ u : TangentSpace I x, g.inner x u u ≤ L * G.inner x u u)
    (hlower : ∀ u v : V,
      c * (G.inner x (e u) (e u) * G.inner x (e v) (e v) - (G.inner x (e u) (e v)) ^ 2) ≤
        metricRm04StandardAt G x (e u) (e v) (e v) (e u))
    (hsmall : ((1 + delta) * R + delta * K) + c' * L ^ 2 ≤ c) :
    ∀ u v : V,
      c' * (g.inner x (e u) (e u) * g.inner x (e v) (e v) - (g.inner x (e u) (e v)) ^ 2) ≤
        metricRm04StandardAt g x (e u) (e v) (e v) (e u) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by decide)
  have hA : IsAlgCurvForm (fun u v w z : TangentSpace I x =>
      metricRm04StandardAt g x u v w z) :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
  have hAe : IsAlgCurvForm (fun u v w z : V =>
      metricRm04StandardAt g x (e u) (e v) (e w) (e z)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intros; simp only [map_add]; exact hA.add_left _ _ _ _ _
    · intros; simp only [map_smul]; exact hA.smul_left _ _ _ _ _
    · intros; exact hA.anti_first _ _ _ _
    · intros; exact hA.anti_last _ _ _ _
    · intros; exact hA.bianchi _ _ _ _
  let G' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun := fun u => (G.inner x (e u)).toLinearMap.comp e
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  let g' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun := fun u => (g.inner x (e u)).toLinearMap.comp e
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply hAe.sectional_lower_bound_of_orthogonal G' g'
    (fun u hu => G.pos x (e u) (fun hz => hu (he (by simpa only [map_zero] using hz))))
    (fun u v => g.symm x (e u) (e v))
  intro u v huv
  change G.inner x (e u) (e v) = 0 at huv
  have hlow := hlower u v
  rw [huv, sq, mul_zero, sub_zero] at hlow
  have herr := abs_metricRm04StandardAt_sub_le_of_riemannOp_sub_le
    g G x hdelta hmetric hdiff hmodel (e u) (e v)
  have hgram : g.inner x (e u) (e u) * g.inner x (e v) (e v) - (g.inner x (e u) (e v)) ^ 2 ≤
      L ^ 2 * (G.inner x (e u) (e u) * G.inner x (e v) (e v)) := by
    have hh := mul_le_mul (hupper (e u)) (hupper (e v)) (metric_inner_self_nonneg g x (e v))
      (mul_nonneg hL (metric_inner_self_nonneg G x (e u)))
    calc
      _ ≤ g.inner x (e u) (e u) * g.inner x (e v) (e v) := sub_le_self _ (sq_nonneg _)
      _ ≤ (L * G.inner x (e u) (e u)) * (L * G.inner x (e v) (e v)) := hh
      _ = _ := by ring
  have hsmall' := mul_le_mul_of_nonneg_right hsmall
    (mul_nonneg (metric_inner_self_nonneg G x (e u)) (metric_inner_self_nonneg G x (e v)))
  have herr' := (abs_le.mp herr).1
  change c' * (g.inner x (e u) (e u) * g.inner x (e v) (e v) - (g.inner x (e u) (e v)) ^ 2) ≤ _
  calc
    _ ≤ c' * (L ^ 2 * (G.inner x (e u) (e u) * G.inner x (e v) (e v))) :=
      mul_le_mul_of_nonneg_left hgram hc'
    _ ≤ metricRm04StandardAt g x (e u) (e v) (e v) (e u) := by nlinarith


theorem metricRm04StandardAt_lower_bound_of_riemannOp_sub_le
    (g G : SmoothRiemannianMetric I M) (x : M) {delta R K c c' L : ℝ}
    (hdelta : 0 ≤ delta) (hc' : 0 ≤ c') (hL : 0 ≤ L)
    (hmetric : ∀ u v : TangentSpace I x,
      |g.inner x u v - G.inner x u v| ≤
        delta * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v))
    (hdiff : ∀ u v w : TangentSpace I x,
      let d := riemannOp (LeviCivita g) x u v w - riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x d d) ≤
        R * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x r r) ≤
        K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hupper : ∀ u : TangentSpace I x, g.inner x u u ≤ L * G.inner x u u)
    (hlower : ∀ u v : TangentSpace I x,
      c * (G.inner x u u * G.inner x v v - (G.inner x u v) ^ 2) ≤
        metricRm04StandardAt G x u v v u)
    (hsmall : ((1 + delta) * R + delta * K) + c' * L ^ 2 ≤ c) :
    ∀ u v : TangentSpace I x,
      c' * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) ≤
        metricRm04StandardAt g x u v v u := by
  exact metricRm04StandardAt_lower_bound_on_range_of_riemannOp_sub_le g G x
    (LinearMap.id : TangentSpace I x →ₗ[ℝ] TangentSpace I x) Function.injective_id
    hdelta hc' hL hmetric hdiff hmodel hupper hlower hsmall

theorem metricRm04StandardAt_lower_bound_on_range_of_small_metric_derivatives
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g G : SmoothRiemannianMetric I M) (x : M)
    (e : V →ₗ[ℝ] TangentSpace I x) (he : Function.Injective e) {ε K c c' : ℝ}
    (hε : ε ≤ 1 / 2) (hc' : 0 ≤ c')
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ ε)
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x r r) ≤
        K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hlower : ∀ u v : V,
      c * (G.inner x (e u) (e u) * G.inner x (e v) (e v) - (G.inner x (e u) (e v)) ^ 2) ≤
        metricRm04StandardAt G x (e u) (e v) (e v) (e u))
    (hbudget : ε * (360 + K) + 4 * c' ≤ c) :
    ∀ u v : V,
      c' * (g.inner x (e u) (e u) * g.inner x (e v) (e v) - (g.inner x (e u) (e v)) ^ 2) ≤
        metricRm04StandardAt g x (e u) (e v) (e v) (e u) := by
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hm (u v : TangentSpace I x) :
      |g.inner x u v - G.inner x u v| ≤
        ε * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) :=
    (metricDifference_abs_le g G G x u v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  refine metricRm04StandardAt_lower_bound_on_range_of_riemannOp_sub_le g G x e he
    hε0 hc' (show (0 : ℝ) ≤ 2 by norm_num) hm
    (riemann_difference_bound_of_small_metric_derivatives g G x ε hε hsmall)
    hmodel ?_ hlower ?_
  · intro u
    have h := hm u u
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg G x u)] at h
    have hnonneg := metric_inner_self_nonneg G x u
    nlinarith [(abs_le.mp h).2]
  · nlinarith [mul_nonneg hε0 (show 0 ≤ 1 / 2 - ε by linarith)]


end

section

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian

omit [BoundarylessManifold I M] in
private theorem reference_inner_bounds_of_unit (g G : SmoothRiemannianMetric I M)
    (x : M) {eps : ℝ} (heps : eps ≤ 1 / 2)
    (hsmall : metricDerivNorm 0 g G G x ≤ eps)
    (u : TangentSpace I x) (hu : g.inner x u u = 1) :
    1 - 2 * eps ≤ G.inner x u u ∧ G.inner x u u ≤ 2 := by
  have hnn : 0 ≤ G.inner x u u := metric_inner_self_nonneg G x u
  have hd := (metricDifference_abs_le g G G x u u).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _))
  rw [hu, mul_assoc, Real.mul_self_sqrt hnn] at hd
  have habs := abs_le.mp hd
  have heps0 : 0 ≤ eps := (Real.sqrt_nonneg _).trans hsmall
  constructor <;> nlinarith

private theorem metricRm04_unit_lower_bound_of_small_metric_derivatives
    (g G : SmoothRiemannianMetric I M) (x : M) {eps c K : ℝ}
    (heps : eps ≤ 1 / 2) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ eps)
    (hsec : ∀ u v : TangentSpace I x,
      c * (G.inner x u u * G.inner x v v - G.inner x u v ^ 2) ≤
        metricRm04StandardAt G x u v v u)
    (hRm : ∀ u v w : TangentSpace I x,
      Real.sqrt (G.inner x (riemannOp (LeviCivita G) x u v w)
        (riemannOp (LeviCivita G) x u v w)) ≤
      K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) * Real.sqrt (G.inner x w w))
    (u v : TangentSpace I x) (hu : g.inner x u u = 1) (hv : g.inner x v v = 1)
    (huv : g.inner x u v = 0) :
    c - 4 * eps * (c + 360 + K) ≤ metricRm04StandardAt g x u v v u := by
  have heps0 : 0 ≤ eps := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hA := reference_inner_bounds_of_unit g G x heps (hsmall 0 (by norm_num)) u hu
  have hB := reference_inner_bounds_of_unit g G x heps (hsmall 0 (by norm_num)) v hv
  have hAn := metric_inner_self_nonneg G x u
  have hBn := metric_inner_self_nonneg G x v
  have hAB : G.inner x u u * G.inner x v v ≤ 4 := by nlinarith
  have hABlo : (1 - 2 * eps) ^ 2 ≤ G.inner x u u * G.inner x v v := by
    have hh := mul_le_mul hA.1 hB.1 (by linarith : 0 ≤ 1 - 2 * eps) hAn
    nlinarith
  let N (a : TangentSpace I x) := Real.sqrt (G.inner x a a)
  have hNprod : N u * N v ≤ 2 := by
    have hh : (N u * N v) ^ 2 ≤ 4 := by
      simpa only [mul_pow, N, Real.sq_sqrt hAn, Real.sq_sqrt hBn] using hAB
    nlinarith [mul_nonneg (Real.sqrt_nonneg (G.inner x u u))
      (Real.sqrt_nonneg (G.inner x v v))]
  have hcross : |G.inner x u v| ≤ 2 * eps := by
    have hh := (metricDifference_abs_le g G G x u v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num))
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    rw [huv, zero_sub, abs_neg] at hh
    have hn := mul_le_mul_of_nonneg_left hNprod heps0
    dsimp only [N] at hn
    nlinarith
  have hcrosssq : G.inner x u v ^ 2 ≤ 4 * eps ^ 2 := by
    have hh := sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * eps) |>.mpr hcross
    simpa only [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
  have hgram : 1 - 4 * eps ≤ G.inner x u u * G.inner x v v - G.inner x u v ^ 2 := by
    nlinarith
  have hbackground := (mul_le_mul_of_nonneg_left hgram hc).trans (hsec u v)
  have herr := abs_metricRm04_sub_le_of_small_metric_derivatives g G x heps hsmall u v v u
  have herr' : |metricRm04StandardAt g x u v v u - metricRm04StandardAt G x u v v u| ≤
      4 * eps * (360 + K) := by
    apply herr.trans
    calc
      _ ≤ eps * (360 * N u * N v * N v + K * N u * N v * N v) * N u := by
        gcongr
        exact hRm u v v
      _ = eps * (360 + K) * (G.inner x u u * G.inner x v v) := by
        have hNu : N u ^ 2 = G.inner x u u := Real.sq_sqrt hAn
        have hNv : N v ^ 2 = G.inner x v v := Real.sq_sqrt hBn
        rw [← hNu, ← hNv]
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hAB (by positivity : 0 ≤ eps * (360 + K))
        nlinarith
  have hh := (abs_le.mp herr').1
  nlinarith

theorem metricRm04_lower_bound_of_small_metric_derivatives
    (g G : SmoothRiemannianMetric I M) (x : M) {eps c K : ℝ}
    (heps : eps ≤ 1 / 2) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ eps)
    (hsec : ∀ u v : TangentSpace I x,
      c * (G.inner x u u * G.inner x v v - G.inner x u v ^ 2) ≤
        metricRm04StandardAt G x u v v u)
    (hRm : ∀ u v w : TangentSpace I x,
      Real.sqrt (G.inner x (riemannOp (LeviCivita G) x u v w)
        (riemannOp (LeviCivita G) x u v w)) ≤
      K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) * Real.sqrt (G.inner x w w))
    (u v : TangentSpace I x) :
    (c - 4 * eps * (c + 360 + K)) *
      (g.inner x u u * g.inner x v v - g.inner x u v ^ 2) ≤
      metricRm04StandardAt g x u v v u := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  by_cases hlin : LinearIndependent ℝ ![u, v]
  · obtain ⟨a, b, ha, hb, hab, heq⟩ := exists_orthonormal_pair_sectional_quotient g x u v hlin
    have hh := metricRm04_unit_lower_bound_of_small_metric_derivatives g G x heps hc hK
      hsmall hsec hRm a b ha hb hab
    rw [heq] at hh
    exact (le_div_iff₀ (gram_determinant_pos g x u v hlin)).mp hh
  · rw [metricRm04StandardAt_eq_zero_of_not_linearIndependent g x u v hlin]
    have hgram : g.inner x u u * g.inner x v v - g.inner x u v ^ 2 = 0 := by
      by_cases hu : u = 0
      · simp [hu]
      · rw [LinearIndependent.pair_iff' hu] at hlin
        push Not at hlin
        obtain ⟨a, rfl⟩ := hlin
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
    rw [hgram, mul_zero]

end

section

open DifferentialGeometry.Geometry.Connection DifferentialGeometry.CheegerGromovCompactness

theorem metricRm04_lt_mul_gram_of_curvature_null_pair
    (g G : SmoothRiemannianMetric I M) (x : M) {ε c : ℝ}
    (hε : ε ≤ 1 / 4) (hc : 720 * ε < c)
    (hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g G G x ≤ ε)
    (u v : TangentSpace I x) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : G.inner x u v = 0)
    (hnull : riemannOp (LeviCivita G) x u v v = 0) :
    metricRm04StandardAt g x u v v u <
      c * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  let A := G.inner x u u
  let B := G.inner x v v
  have hA : 0 < A := G.pos x u hu
  have hB : 0 < B := G.pos x v hv
  have hAB : 0 < A * B := mul_pos hA hB
  have hnormA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA.le
  have hnormB : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB.le
  have hmetric (a b : TangentSpace I x) :
      |g.inner x a b - G.inner x a b| ≤
        ε * Real.sqrt (G.inner x a a) * Real.sqrt (G.inner x b b) :=
    (metricDifference_abs_le g G G x a b).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  have hdiagA := hmetric u u
  have hdiagB := hmetric v v
  change |g.inner x u u - A| ≤ ε * Real.sqrt A * Real.sqrt A at hdiagA
  change |g.inner x v v - B| ≤ ε * Real.sqrt B * Real.sqrt B at hdiagB
  rw [mul_assoc, hnormA] at hdiagA
  rw [mul_assoc, hnormB] at hdiagB
  have hlowA : (1 - ε) * A ≤ g.inner x u u := by nlinarith [(abs_le.mp hdiagA).1]
  have hlowB : (1 - ε) * B ≤ g.inner x v v := by nlinarith [(abs_le.mp hdiagB).1]
  have hprod := mul_le_mul hlowA hlowB (mul_nonneg (by linarith) hB.le)
    (metric_inner_self_nonneg g x u)
  have hcross := hmetric u v
  rw [huv, sub_zero] at hcross
  change |g.inner x u v| ≤ ε * Real.sqrt A * Real.sqrt B at hcross
  have hcrosssq : (g.inner x u v) ^ 2 ≤ ε ^ 2 * A * B := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hcross
    rw [sq_abs] at hh
    have he : (ε * Real.sqrt A * Real.sqrt B) ^ 2 = ε ^ 2 * A * B := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
    rwa [he] at hh
  have hgram : (1 - 2 * ε) * (A * B) ≤
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
    nlinarith
  have hhalf : A * B / 2 ≤ g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - 2 * ε by linarith) hAB.le]
  have hzero : metricRm04StandardAt G x u v v u = 0 := by
    rw [metricRm04StandardAt_eq_inner_riemannOp, hnull, map_zero]
  have herr := abs_metricRm04_sub_le_of_small_metric_derivatives g G x
    (show ε ≤ 1 / 2 by linarith) hsmall u v v u
  rw [hzero, sub_zero, hnull, map_zero, Real.sqrt_zero, add_zero] at herr
  change |metricRm04StandardAt g x u v v u| ≤
    ε * (360 * Real.sqrt A * Real.sqrt B * Real.sqrt B) * Real.sqrt A at herr
  have he : ε * (360 * Real.sqrt A * Real.sqrt B * Real.sqrt B) * Real.sqrt A =
      360 * ε * (A * B) := by
    calc
      _ = 360 * ε * ((Real.sqrt A * Real.sqrt A) * (Real.sqrt B * Real.sqrt B)) := by ring
      _ = _ := by rw [hnormA, hnormB]
  rw [he] at herr
  have hupper := (le_abs_self (metricRm04StandardAt g x u v v u)).trans herr
  have hstrict : 360 * ε * (A * B) < c * (A * B / 2) := by
    nlinarith [mul_pos (sub_pos.mpr hc) hAB]
  exact hupper.trans_lt (hstrict.trans_le (mul_le_mul_of_nonneg_left hhalf hc0.le))


theorem metricRm04_lt_mul_gram_product_vertical_of_small_metric_derivatives
    (h : SmoothRiemannianMetric I M)
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ)) (x : M × ℝ)
    {ε c : ℝ} (hε : ε ≤ 1 / 4) (hc : 720 * ε < c)
    (hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g
      (h.prod (euclideanMetric (E := ℝ)))
      (h.prod (euclideanMetric (E := ℝ))) x ≤ ε)
    (u : TangentSpace I x.1) (hu : u ≠ 0) :
    metricRm04StandardAt g x (u, 0) (0, 1) (0, 1) (u, 0) <
      c * (g.inner x (u, 0) (u, 0) * g.inner x (0, 1) (0, 1) -
        (g.inner x (u, 0) (0, 1)) ^ 2) := by
  change E at u
  apply metricRm04_lt_mul_gram_of_curvature_null_pair g
    (h.prod (euclideanMetric (E := ℝ))) x hε hc hsmall (u, 0) (0, 1)
  · intro heq
    exact hu (congrArg Prod.fst heq)
  · intro heq
    have h1 := congrArg Prod.snd heq
    change (1 : ℝ) = 0 at h1
    norm_num at h1
  · erw [SmoothRiemannianMetric.prod_inner]
    change h.inner x.1 u (0 : E) +
      (euclideanMetric (E := ℝ)).inner x.2 (0 : ℝ) 1 = 0
    exact (congrArg₂ (· + ·) (map_zero (h.inner x.1 u))
      (show (euclideanMetric (E := ℝ)).inner x.2 0 1 = 0 from by
        rw [map_zero ((euclideanMetric (E := ℝ)).inner x.2)]
        rfl)).trans (zero_add _)
  · exact riemannOp_productReal_vertical_eq_zero h x (u, 0) (0, 1) 1


end

end DifferentialGeometry.Geometry.Curvature
