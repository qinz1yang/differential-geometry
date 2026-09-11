import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure

set_option autoImplicit false
noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private theorem clamp_gap_bound {r R s : ℝ} (hrR : r ≤ R) (hsR : s ≤ R) :
    |min s r - s| ≤ R - r := by
  by_cases hsr : s ≤ r
  · rw [min_eq_left hsr, sub_self, abs_zero]
    exact sub_nonneg.mpr hrR
  · rw [min_eq_right (not_le.mp hsr).le, abs_of_nonpos (by linarith : r - s ≤ 0)]
    linarith


theorem clamped_ray_parameter_mem {L r s : ℝ} (hL : 0 ≤ L) (hr : 0 < r) (hs : 0 ≤ s) :
    L * (min s r / r) ∈ Icc (0 : ℝ) L := by
  have hmin : 0 ≤ min s r := le_min hs hr.le
  refine ⟨mul_nonneg hL (div_nonneg hmin hr.le), ?_⟩
  have hfrac : min s r / r ≤ 1 := (div_le_one hr).mpr (min_le_right _ _)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac hL


theorem clamped_ray_parameter_monotone {L r : ℝ} (hL : 0 ≤ L) (hr : 0 < r) :
    Monotone (fun s : ℝ => L * (min s r / r)) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (min_le_min_right r hst) hr.le) hL

theorem clamped_ray_parameter_error {L r R s : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) (hs : s ∈ Icc (0 : ℝ) R) :
    |L * (min s r / r) - s| ≤ |L - r| + (R - r) := by
  have hfrac0 : 0 ≤ min s r / r := div_nonneg (le_min hs.1 hr.le) hr.le
  have hfrac1 : min s r / r ≤ 1 := (div_le_one hr).mpr (min_le_right _ _)
  have heq : L * (min s r / r) - s = (L - r) * (min s r / r) + (min s r - s) := by
    field_simp [hr.ne']
    ring
  calc
    _ = |(L - r) * (min s r / r) + (min s r - s)| := congrArg abs heq
    _ ≤ |(L - r) * (min s r / r)| + |min s r - s| := abs_add_le _ _
    _ = |L - r| * (min s r / r) + |min s r - s| := by rw [abs_mul, abs_of_nonneg hfrac0]
    _ ≤ |L - r| + (R - r) := add_le_add
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac1 (abs_nonneg (L - r)))
      (clamp_gap_bound hrR hs.2)

variable {W : Type*} [MetricSpace W]

theorem EndRay.dist_lt_of_clamped_approximation {E : UniformSpace.Completion W}
    (a : EndRay E) {r R L eps : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ a.length)
    (gamma : ℝ → W)
    (happrox : ∀ t ∈ Ioc (0 : ℝ) r, dist (gamma (L * (t / r))) (a.point t) < eps)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) R) :
    dist (gamma (L * (min s r / r))) (a.point s) < eps + (R - r) := by
  have hm : min s r ∈ Ioc (0 : ℝ) r := ⟨lt_min hs.1 hr, min_le_right _ _⟩
  have hma : min s r ∈ Ioc (0 : ℝ) a.length := ⟨hm.1, hm.2.trans (hrR.trans hR)⟩
  have hsa : s ∈ Ioc (0 : ℝ) a.length := ⟨hs.1, hs.2.trans hR⟩
  have hgap : dist (a.point (min s r)) (a.point s) ≤ R - r := by
    rw [a.minimizing _ hma _ hsa]
    exact clamp_gap_bound hrR hs.2
  exact (dist_triangle _ (a.point (min s r)) _).trans_lt
    (add_lt_add_of_lt_of_le (happrox _ hm) hgap)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
