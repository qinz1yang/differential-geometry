import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.LocalBallRatio
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Collapse.CurvatureScale

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

/-- A volume-tested ball in a complete three-dimensional manifold supplies a
fixed smaller seed at the same center, with its full sectional lower bound.
The volume coefficient is independent of both radii and of the metric. -/
theorem sectional_and_volume_lower_of_tested_ball
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (hdim : Module.finrank ℝ E = 3) (p : M) {b r w : ℝ}
    (hb : 0 < b) (hbr : b ≤ r)
    (hsec : ∀ x ∈ riemannianBallOf g p r,
      SectionalBoundedBelowAt g x (-(r ^ 2)⁻¹))
    (hvol : ENNReal.ofReal (w * r ^ 3) ≤ ballVolume g p r) :
    (∀ x ∈ riemannianBallOf g p b,
      SectionalBoundedBelowAt g x (-(b ^ 2)⁻¹)) ∧
      ENNReal.ofReal ((Real.exp (-2) / 8 * w) * b ^ 3) ≤ ballVolume g p b := by
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hr : 0 < r := hb.trans_le hbr
  constructor
  · intro x hx
    apply (hsec x (riemannianBallOf_mono g p hbr hx)).mono
    exact neg_le_neg ((inv_le_inv₀ (pow_pos hr 2) (pow_pos hb 2)).mpr
      (pow_le_pow_left₀ hb.le hbr 2))
  · have hRic : ∀ x ∈ riemannianBallOf g p r, ∀ v : TangentSpace I x,
        -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (r⁻¹) ^ 2) * g.inner x v v ≤
          ricciTensor g x v v := by
      intro x hx v
      simpa only [inv_pow, mul_neg] using
        ricci_lower_of_sectionalBoundedBelowAt g x (hsec x hx) v
    have hratio := riemannianBallOf_volume_ratio_ge_of_ricci_lower g hg p
      (q := r⁻¹) (inv_nonneg.mpr hr.le) hb hbr hRic
    norm_num [hdim] at hratio
    have hc : 0 ≤ Real.exp (-(r⁻¹ * 2 * r)) * (b / (2 * r)) ^ 3 := by positivity
    have hbound := (mul_le_mul' (le_refl
      (ENNReal.ofReal (Real.exp (-(r⁻¹ * 2 * r)) * (b / (2 * r)) ^ 3)))
      hvol).trans hratio
    rw [← ENNReal.ofReal_mul hc] at hbound
    have he : r⁻¹ * (2 : ℝ) * r = 2 := by field_simp [hr.ne']
    have hcoeff : (Real.exp (-(r⁻¹ * 2 * r)) * (b / (2 * r)) ^ 3) *
        (w * r ^ 3) = (Real.exp (-2) / 8 * w) * b ^ 3 := by
      rw [he]
      field_simp [hr.ne']
      ring
    rwa [hcoeff] at hbound

end DifferentialGeometry.Geometry.Collapse
