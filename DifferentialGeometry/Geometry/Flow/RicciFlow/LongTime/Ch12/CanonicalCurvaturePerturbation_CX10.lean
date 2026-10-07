import DifferentialGeometry.Geometry.Curvature.SectionalPerturbation

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Laplacian
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

/-!
The general perturbation estimate uses equivalence constant 2 and costs 240 eps.
At eps ≤ 1/100, equivalence constant 11/10 instead gives |D∇| ≤ 9 eps / 4,
|∇-∇₀| ≤ 2 eps, and |Rm(1,3)-Rm₀(1,3)| ≤ 5 eps. This keeps the
round positivity argument valid at the existing profile accuracy 1/100.
The proof refines Geometry/Curvature/RiemannPerturbation.lean, using the same
connection-difference identities and their full quantitative bounds.
-/

theorem riemann_difference_bound_CX10
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g gRef : SmoothRiemannianMetric I M) (x : M) (ε : ℝ) (hε : ε ≤ 1 / 100)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g gRef gRef x ≤ ε)
    (u v w : TangentSpace I x) :
    let d := riemannOp (LeviCivita g) x u v w - riemannOp (LeviCivita gRef) x u v w
    Real.sqrt (gRef.inner x d d) ≤
      5 * ε * Real.sqrt (gRef.inner x u u) *
        Real.sqrt (gRef.inner x v v) * Real.sqrt (gRef.inner x w w) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hnn (z : TangentSpace I x) : 0 ≤ gRef.inner x z z := by
    by_cases hz : z = 0
    · simp [hz]
    · exact (gRef.pos x z hz).le
  have hequiv : MetricUniformEquivalentOn (I := I) {x} gRef g (11 / 10) := by
    have h := metricUniformEquivalentOn_of_quadFormDiff (I := I)
      (K := {x}) (g := gRef) (h := g) (δ := 1 / 11)
      (by norm_num) (by norm_num) ?_
    · norm_num only at h
      exact h
    · intro y hy z
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      have hb := metricDifference_abs_le g gRef gRef x z z
      rw [mul_assoc, Real.mul_self_sqrt (hnn z)] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right
        ((hsmall 0 (by norm_num)).trans (show ε ≤ 1 / 11 by linarith)) (hnn z))
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
  have hA (a b : TangentSpace I x) : N (A b a) ≤ 2 * ε * N a * N b := by
    have h := connectionDifference_gJet_le (I := I) hequiv (hjet 0 (by norm_num))
      (Set.mem_singleton x) a b
    apply h.trans
    have hc : (3 / 2 : ℝ) * (11 / 10) ^ 3 * ε ≤ 2 * ε := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hD (a b c : TangentSpace I x) :
      N (covDerivConnectionDifference gRef g (S a) (S b) (S c) x) ≤
        (9 / 4) * ε * N a * N b * N c := by
    have h := covDerivConnectionDifference_gJet_le (I := I) hequiv
      (hjet 0 (by norm_num)) (hjet 1 (by norm_num)) (Set.mem_singleton x) a b c
    apply h.trans
    have hc : 3 / 2 * (11 / 10 : ℝ) ^ 4 * (ε + (11 / 10) * ε ^ 2) ≤ (9 / 4) * ε := by
      nlinarith [mul_le_mul_of_nonneg_left hε hε0]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hQ (a b c : TangentSpace I x) : N (A (A c b) a) ≤ (1 / 4) * ε * N a * N b * N c := by
    calc
      _ ≤ 2 * ε * N a * N (A c b) := hA a (A c b)
      _ ≤ 2 * ε * N a * (2 * ε * N b * N c) :=
        mul_le_mul_of_nonneg_left (hA b c) (by dsimp only [N]; positivity)
      _ = (4 * ε ^ 2) * N a * N b * N c := by ring
      _ ≤ _ := by
        have hc : 4 * ε ^ 2 ≤ (1 / 4) * ε := by
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

/-- Quantitative preservation of a scalar-one round model's sectional lower bound. -/
theorem metricRm04_lower_bound_CX10
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g G : SmoothRiemannianMetric I M) (x : M) {eps : ℝ}
    (heps : eps ≤ 1 / 100)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ eps)
    (hsec : ∀ v w : TangentSpace I x,
      (1 / 6 : ℝ) * (G.inner x v v * G.inner x w w - G.inner x v w ^ 2) ≤
        metricRm04StandardAt G x v w w v)
    (hrm : normSq0S G x 4 (metricRm04At G x) ≤ 1)
    (v w : TangentSpace I x) :
    (1 / 12 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2) ≤
      metricRm04StandardAt g x v w w v := by
  have heps0 : 0 ≤ eps := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hm (a b : TangentSpace I x) :
      |g.inner x a b - G.inner x a b| ≤
        eps * Real.sqrt (G.inner x a a) * Real.sqrt (G.inner x b b) :=
    (metricDifference_abs_le g G G x a b).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  have hmodel (a b c : TangentSpace I x) :
      Real.sqrt (G.inner x (riemannOp (LeviCivita G) x a b c)
        (riemannOp (LeviCivita G) x a b c)) ≤
      1 * Real.sqrt (G.inner x a a) * Real.sqrt (G.inner x b b) *
        Real.sqrt (G.inner x c c) := by
    apply (sqrt_inner_riemannOp_le G x a b c).trans
    have hnorm : Real.sqrt (normSq0S G x 4 (metricRm04At G x)) ≤ 1 :=
      Real.sqrt_le_one.mpr hrm
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  apply metricRm04StandardAt_lower_bound_of_riemannOp_sub_le g G x heps0
    (by norm_num : (0 : ℝ) ≤ 1 / 12) (by norm_num : (0 : ℝ) ≤ 11 / 10) hm
    (riemann_difference_bound_CX10 g G x eps heps hsmall) hmodel ?_ hsec ?_ v w
  · intro a
    have h := hm a a
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg G x a)] at h
    have hnn := metric_inner_self_nonneg G x a
    nlinarith [(abs_le.mp h).2]
  · nlinarith [mul_le_mul_of_nonneg_left heps heps0]

end GC.LongTime.Ch12
