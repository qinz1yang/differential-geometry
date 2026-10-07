import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Curvature.NegativeSectionalStability

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open Filter Set
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
/-- **(G2-radius)** The curvature radius sandwich from a lower sectional bound on a ball and a
single plane violating `-1/8` at the centre: `r₀ ≤ r ≤ √8`. -/
theorem curvatureRadius_bounds_S35 (g : SmoothRiemannianMetric I M) (x : M) {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hlow : ∀ q ∈ riemannianBallOf g x r₀, SectionalBoundedBelowAt g q (-(r₀ ^ 2)⁻¹))
    (hup : ¬ SectionalBoundedBelowAt g x (-(1 / 8 : ℝ)))
    {r : ℝ} (hr : 0 < r) (hcr : curvatureRadius g x = ENNReal.ofReal r) :
    r₀ ≤ r ∧ r ^ 2 ≤ 8 := by
  constructor
  · have h1 : ENNReal.ofReal r₀ ≤ curvatureRadius g x :=
      le_iSup_of_le r₀ (le_iSup_of_le hr₀ (le_iSup_of_le hlow le_rfl))
    rw [hcr] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hr.le).mp h1
  · have h2 : curvatureRadius g x ≤ ENNReal.ofReal (Real.sqrt 8) := by
      unfold curvatureRadius
      refine iSup_le fun r' => iSup_le fun hr' => iSup_le fun hP => ENNReal.ofReal_le_ofReal ?_
      by_contra hcon
      have hlt : Real.sqrt 8 < r' := not_le.mp hcon
      have h8 : (8 : ℝ) < r' ^ 2 := by
        have := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
        nlinarith [Real.sqrt_nonneg 8]
      have hx : x ∈ riemannianBallOf g x r' := by
        change riemannianEDistOf g x x < ENNReal.ofReal r'
        rw [riemannianEDistOf_self]
        exact ENNReal.ofReal_pos.mpr hr'
      refine hup ((hP x hx).mono ?_)
      have : ((r' ^ 2)⁻¹ : ℝ) ≤ 1 / 8 := by
        rw [← one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith
    rw [hcr] at h2
    have h3 := (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg 8)).mp h2
    have h4 := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
    nlinarith [Real.sqrt_nonneg 8]

end GC.LongTime.Ch12
