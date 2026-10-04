import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Centered radial normalization of a buffered smooth radial function (LC67, tier 2)

Blueprint `master207A.tex`, LC67 (`lem:collapse-buffered-radial-normalization`,
lines 23899–23986). The existence half of LC67 is the LC28 smoothing (lane W3-LC28) applied with
`Y = {p}`, `U = {1/20 < d(p,·) < 20}` and the compact set `C⁺ = {3/40 ≤ d(p,·) ≤ 11}`. This module
proves the rest of the row for ANY function `η` carrying those output clauses, stated explicitly
(smooth on an open `W ⊇ C⁺`, and `η - d(p,·)` globally `ε`-Lipschitz); no named hypothesis is
introduced.

* `centered_radial_normalization` (metric kernel): for every `λ > 0` and every `q`, with
  `ψ_q = λ (η - η(q))` and `u_q = λ d(p,·) - λ d(p,q)`: `ψ_q(q) = u_q(q) = 0`, the difference
  `ψ_q - u_q` is `ε`-Lipschitz for the distance `λ d`, `|ψ_q - u_q| ≤ ε λ d(q,·)`, and `ψ_q` is
  `(1 + ε)`-Lipschitz for `λ d`. Centering avoids the factor `λ ‖η - d_p‖_∞`; no upper bound on
  `λ` is used.
* `ball_subset_buffer_of_shell`: for `1/10 ≤ d(p,q) ≤ 10` and `λ ≥ 80`, the `λ d`-unit ball about
  `q` lies in `{7/80 < d(p,·) < 10 + 1/80} ⊆ C⁺`.
* `contMDiffOn_centered_radial`: on a compact connected manifold with the distance of `g`, the
  function `ψ_q` is smooth on the unit ball of `λ² g` about `q`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

/-- **LC67, normalization (metric kernel).** -/
theorem centered_radial_normalization {X : Type*} [PseudoMetricSpace X] {p : X} {η : X → ℝ}
    {ε : ℝ} (hlip : ∀ x y, |(η x - dist x p) - (η y - dist y p)| ≤ ε * dist x y)
    (q : X) {lam : ℝ} (hlam : 0 < lam) :
    lam * (η q - η q) = 0 ∧ lam * dist p q - lam * dist p q = 0 ∧
      (∀ x y, |(lam * (η x - η q) - (lam * dist p x - lam * dist p q)) -
          (lam * (η y - η q) - (lam * dist p y - lam * dist p q))| ≤ ε * (lam * dist x y)) ∧
      (∀ x, |lam * (η x - η q) - (lam * dist p x - lam * dist p q)| ≤ ε * (lam * dist q x)) ∧
      ∀ x y, |lam * (η x - η q) - lam * (η y - η q)| ≤ (1 + ε) * (lam * dist x y) := by
  have hdiff (x y : X) : (lam * (η x - η q) - (lam * dist p x - lam * dist p q)) -
      (lam * (η y - η q) - (lam * dist p y - lam * dist p q)) =
      lam * ((η x - dist x p) - (η y - dist y p)) := by
    rw [dist_comm p x, dist_comm p y]
    ring
  have hmain (x y : X) : |(lam * (η x - η q) - (lam * dist p x - lam * dist p q)) -
      (lam * (η y - η q) - (lam * dist p y - lam * dist p q))| ≤ ε * (lam * dist x y) := by
    rw [hdiff, abs_mul, abs_of_pos hlam]
    have := hlip x y
    nlinarith
  refine ⟨by ring, by ring, hmain, fun x => ?_, fun x y => ?_⟩
  · have h := hmain x q
    simp only [sub_self, mul_zero, sub_zero] at h
    rwa [dist_comm x q] at h
  · have h := hmain x y
    have hu : |(lam * dist p x - lam * dist p q) - (lam * dist p y - lam * dist p q)| ≤
        lam * dist x y := by
      have e : (lam * dist p x - lam * dist p q) - (lam * dist p y - lam * dist p q) =
          lam * (dist p x - dist p y) := by ring
      rw [e, abs_mul, abs_of_pos hlam]
      have hd : |dist p x - dist p y| ≤ dist x y := by
        rw [dist_comm p x, dist_comm p y]
        exact abs_dist_sub_le x y p
      exact mul_le_mul_of_nonneg_left hd hlam.le
    have e2 : lam * (η x - η q) - lam * (η y - η q) =
        ((lam * (η x - η q) - (lam * dist p x - lam * dist p q)) -
          (lam * (η y - η q) - (lam * dist p y - lam * dist p q))) +
        ((lam * dist p x - lam * dist p q) - (lam * dist p y - lam * dist p q)) := by ring
    rw [e2]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ ε * (lam * dist x y) + lam * dist x y := add_le_add h hu
      _ = (1 + ε) * (lam * dist x y) := by ring

/-- **LC67, domain check.** For a point of the closed shell and `λ ≥ 80`, the `λ d`-unit ball
lies in the buffered region where the smoothing is smooth. -/
theorem ball_subset_buffer_of_shell {X : Type*} [PseudoMetricSpace X] {p q : X}
    (hq1 : 1 / 10 ≤ dist p q) (hq2 : dist p q ≤ 10) {lam : ℝ} (hlam : 80 ≤ lam) :
    ball q lam⁻¹ ⊆ {x | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} := by
  intro x hx
  have hx' : dist x q < lam⁻¹ := hx
  have hinv : lam⁻¹ ≤ 1 / 80 := by
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlam
  have h1 := dist_triangle x q p
  have h2 := dist_triangle q x p
  rw [dist_comm q p] at h1
  rw [dist_comm q x, dist_comm q p] at h2
  exact ⟨by linarith, by linarith⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **LC67, smoothness.** On a compact connected manifold with the distance of `g`, a function
smooth on an open `W ⊇ C⁺` gives a centered radial function `ψ_q = λ (η - η(q))` smooth on the
unit ball of `λ² g` about every point `q` of the closed shell, for `λ ≥ 80`. -/
theorem contMDiffOn_centered_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
    [ConnectedSpace M] (g : SmoothRiemannianMetric I M) (p : M) {η : M → ℝ} {W : Set M}
    (hW : letI := inducedMetricSpace g; {x | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ W)
    (hη : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) (q : M)
    (hq1 : letI := inducedMetricSpace g; 1 / 10 ≤ dist p q)
    (hq2 : letI := inducedMetricSpace g; dist p q ≤ 10) {lam : ℝ} (hlam : 80 ≤ lam) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => lam * (η x - η q))
      (riemannianBallOf (scaleMetric (lam ^ 2) (by positivity) g) q 1) := by
  let := inducedMetricSpace g
  have hlampos : 0 < lam := by linarith
  have hball : riemannianBallOf (scaleMetric (lam ^ 2) (by positivity) g) q 1 = ball q lam⁻¹ := by
    have h := riemannianBallOf_scaleMetric (lam ^ 2) (by positivity) g q lam⁻¹
    rw [Real.sqrt_sq hlampos.le, mul_inv_cancel₀ hlampos.ne'] at h
    rw [h, inducedMetricSpace_ball g]
  rw [hball]
  have hsub := (ball_subset_buffer_of_shell hq1 hq2 hlam).trans hW
  have hsmooth : ContDiff ℝ ∞ (fun t : ℝ => lam * (t - η q)) := by fun_prop
  exact hsmooth.contMDiff.comp_contMDiffOn (hη.mono hsub)

end DifferentialGeometry.Geometry.Collapse
