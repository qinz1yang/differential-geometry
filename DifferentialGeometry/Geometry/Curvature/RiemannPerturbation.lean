import DifferentialGeometry.Geometry.Connection.Convergence.DifferenceDerivativeBound
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis.Laplacian

namespace DifferentialGeometry.Geometry.Curvature

theorem riemann_difference_bound_of_small_metric_derivatives
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g gRef : SmoothRiemannianMetric I M) (x : M) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g gRef gRef x ≤ ε)
    (u v w : TangentSpace I x) :
    let d := riemannOp (LeviCivita g) x u v w - riemannOp (LeviCivita gRef) x u v w
    Real.sqrt (gRef.inner x d d) ≤
      240 * ε * Real.sqrt (gRef.inner x u u) *
        Real.sqrt (gRef.inner x v v) * Real.sqrt (gRef.inner x w w) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hnn (z : TangentSpace I x) : 0 ≤ gRef.inner x z z := by
    by_cases hz : z = 0
    · simp [hz]
    · exact (gRef.pos x z hz).le
  have hequiv : MetricUniformEquivalentOn (I := I) {x} gRef g 2 := by
    have h := metricUniformEquivalentOn_of_quadFormDiff (I := I)
      (K := {x}) (g := gRef) (h := g) (δ := 1 / 2)
      (by norm_num) (by norm_num) ?_
    · norm_num only at h
      exact h
    · intro y hy z
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      have hb := metricDifference_abs_le g gRef gRef x z z
      rw [mul_assoc, Real.mul_self_sqrt (hnn z)] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right
        ((hsmall 0 (by norm_num)).trans hε) (hnn z))
  have hjet (k : ℕ) (hk : k + 1 ≤ 2) :
      MetricCovDerivOrderBoundOn (I := I) {x} (k + 1) g gRef ε := by
    intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    have h := covNorm_le_add (k + 1) g gRef gRef x
    rw [covNorm_self_succ, zero_add] at h
    exact h.trans (hsmall (k + 1) hk)
  let N (z : TangentSpace I x) := Real.sqrt (gRef.inner x z z)
  let S (z : TangentSpace I x) := smoothExtensionTangent (I := I) x z
  let A := CovariantDerivative.difference (LeviCivita g) (LeviCivita gRef) x
  have hA (a b : TangentSpace I x) : N (A b a) ≤ 12 * ε * N a * N b := by
    have h := connectionDifference_gJet_le (I := I) hequiv (hjet 0 (by norm_num))
      (Set.mem_singleton x) a b
    norm_num only at h
    exact h
  have hD (a b c : TangentSpace I x) :
      N (covDerivConnectionDifference gRef g (S a) (S b) (S c) x) ≤
        48 * ε * N a * N b * N c := by
    have h := covDerivConnectionDifference_gJet_le (I := I) hequiv
      (hjet 0 (by norm_num)) (hjet 1 (by norm_num)) (Set.mem_singleton x) a b c
    apply h.trans
    have hc : 3 / 2 * (2 : ℝ) ^ 4 * (ε + 2 * ε ^ 2) ≤ 48 * ε := by
      nlinarith [mul_le_mul_of_nonneg_left hε hε0]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hQ (a b c : TangentSpace I x) : N (A (A c b) a) ≤ 72 * ε * N a * N b * N c := by
    calc
      _ ≤ 12 * ε * N a * N (A c b) := hA a (A c b)
      _ ≤ 12 * ε * N a * (12 * ε * N b * N c) :=
        mul_le_mul_of_nonneg_left (hA b c) (by dsimp only [N]; positivity)
      _ = (144 * ε ^ 2) * N a * N b * N c := by ring
      _ ≤ _ := by
        have hc : 144 * ε ^ 2 ≤ 72 * ε := by
          nlinarith [mul_le_mul_of_nonneg_left hε hε0]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)
  have hsec (m : SmoothRiemannianMetric I M) :
      riemannOp (LeviCivita m) x u v w = riemannSec (LeviCivita m) (S u) (S v) (S w) x := by
    have h := riemannOp_apply_smooth (cov := LeviCivita m) (x := x)
      (smoothExtensionTangent_contMDiff (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x w)
    simpa only [smoothExtensionTangent_eq] using h
  have hid : riemannOp (LeviCivita g) x u v w - riemannOp (LeviCivita gRef) x u v w =
      (covDerivConnectionDifference gRef g (S u) (S v) (S w) x -
        covDerivConnectionDifference gRef g (S v) (S u) (S w) x) +
      (A (A w v) u - A (A w u) v) := by
    rw [hsec g, hsec gRef,
      riemannSec_difference (LeviCivita gRef) (LeviCivita g)
        (smoothExtensionTangent_contMDiff (I := I) x u)
        (smoothExtensionTangent_contMDiff (I := I) x v)
        (smoothExtensionTangent_contMDiff (I := I) x w)
        (LeviCivita_torsion_eq_zero gRef)]
    dsimp only [diffSec, S]
    simp only [smoothExtensionTangent_eq]
    change _ = (covDerivDiff (LeviCivita gRef) (LeviCivita g) (S u) (S v) (S w) x -
      covDerivDiff (LeviCivita gRef) (LeviCivita g) (S v) (S u) (S w) x) + _
    abel
  have hsub (a b : TangentSpace I x) : N (a - b) ≤ N a + N b := by
    have h := DifferentialGeometry.Geometry.Riemannian.sqrt_inner_add_le gRef x a (-b)
    simpa only [sub_eq_add_neg, map_neg, neg_apply, neg_neg] using h
  dsimp only
  rw [hid]
  apply (DifferentialGeometry.Geometry.Riemannian.sqrt_inner_add_le gRef x _ _).trans
  apply (add_le_add (hsub _ _) (hsub _ _)).trans
  have h := add_le_add (add_le_add (hD u v w) (hD v u w))
    (add_le_add (hQ u v w) (hQ v u w))
  convert h using 1
  dsimp only [N]
  ring

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

theorem abs_metricRm04_sub_le_of_small_metric_derivatives
    (g G : SmoothRiemannianMetric I M) (x : M) {eps : ℝ}
    (heps : eps ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ eps)
    (u v w z : TangentSpace I x) :
    |metricRm04StandardAt g x u v w z - metricRm04StandardAt G x u v w z| ≤
      eps * (360 * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
        Real.sqrt (G.inner x w w) +
        Real.sqrt (G.inner x (riemannOp (LeviCivita G) x u v w)
          (riemannOp (LeviCivita G) x u v w))) * Real.sqrt (G.inner x z z) := by
  have heps0 : 0 ≤ eps := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  let N (a : TangentSpace I x) := Real.sqrt (G.inner x a a)
  let Rg := riemannOp (LeviCivita g) x u v w
  let RG := riemannOp (LeviCivita G) x u v w
  let d := Rg - RG
  let P := N u * N v * N w
  have hP : 0 ≤ P := by dsimp [P, N]; positivity
  have hd : N d ≤ 240 * eps * P := by
    simpa only [N, d, Rg, RG, P, mul_assoc] using
      riemann_difference_bound_of_small_metric_derivatives g G x eps heps hsmall u v w
  have hRg : N Rg ≤ 240 * eps * P + N RG := by
    calc
      N Rg = N (d + RG) := congrArg N (by dsimp only [d]; abel)
      _ ≤ N d + N RG := sqrt_inner_add_le G x d RG
      _ ≤ _ := add_le_add hd le_rfl
  have hmetric : |g.inner x z Rg - G.inner x z Rg| ≤
      eps * N z * (240 * eps * P + N RG) := by
    apply (metricDifference_abs_le g G G x z Rg).trans
    change metricDerivNorm 0 g G G x * N z * N Rg ≤ _
    gcongr
    exact hsmall 0 (by norm_num)
  have hcurv : |G.inner x z Rg - G.inner x z RG| ≤ N z * (240 * eps * P) := by
    rw [← map_sub]
    exact (abs_metric_inner_le_sqrt_metric_quadratic G x z d).trans
      (mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _))
  rw [metricRm04StandardAt_eq_inner_riemannOp, metricRm04StandardAt_eq_inner_riemannOp]
  change |g.inner x z Rg - G.inner x z RG| ≤ _
  calc
    _ ≤ |g.inner x z Rg - G.inner x z Rg| + |G.inner x z Rg - G.inner x z RG| :=
      abs_sub_le _ _ _
    _ ≤ eps * N z * (240 * eps * P + N RG) + N z * (240 * eps * P) :=
      add_le_add hmetric hcurv
    _ = eps * ((240 * eps + 240) * P + N RG) * N z := by ring
    _ ≤ eps * (360 * P + N RG) * N z := by gcongr; linarith
    _ = _ := by dsimp only [P, N, RG]; ring


end DifferentialGeometry.Geometry.Curvature
