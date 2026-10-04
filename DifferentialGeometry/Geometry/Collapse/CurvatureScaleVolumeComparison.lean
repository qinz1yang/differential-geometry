import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusBounds
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.LocalBallRatio

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure
open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem sectional_lower_on_ball_of_le_curvatureRadius
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hR : 0 < R) (hscale : ENNReal.ofReal R ≤ curvatureRadius g p)
    {y : M} (hy : y ∈ riemannianBallOf g p R) :
    SectionalBoundedBelowAt g y (-((R / 2) ^ 2)⁻¹) := by
  change riemannianEDistOf g p y < ENNReal.ofReal R at hy
  have hfinite : riemannianEDistOf g p y ≠ ⊤ := ne_top_of_lt hy
  have hdist : (riemannianEDistOf g p y).toReal < R := by
    apply (ENNReal.ofReal_lt_ofReal_iff hR).mp
    simpa only [ENNReal.ofReal_toReal hfinite] using hy
  let a := max (R / 2) (riemannianEDistOf g p y).toReal
  have haR : a < R := max_lt (half_lt_self hR) hdist
  have harho : ENNReal.ofReal a < curvatureRadius g p :=
    ((ENNReal.ofReal_lt_ofReal_iff hR).mpr haR).trans_le hscale
  unfold curvatureRadius at harho
  obtain ⟨r, hr⟩ := lt_iSup_iff.mp harho
  obtain ⟨hrpos, hr⟩ := lt_iSup_iff.mp hr
  obtain ⟨hsec, hr⟩ := lt_iSup_iff.mp hr
  have har : a < r := (ENNReal.ofReal_lt_ofReal_iff hrpos).mp hr
  have hhalf : R / 2 < r := (le_max_left _ _).trans_lt har
  have hymem : y ∈ riemannianBallOf g p r := by
    change riemannianEDistOf g p y < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff hrpos).mpr
      ((le_max_right _ _).trans_lt har)
  exact (hsec y hymem).mono (neg_le_neg
    (inv_anti₀ (sq_pos_of_pos (half_pos hR)) (by nlinarith)))

omit [CompleteSpace E] in
theorem ballVolume_ratio_at_curvature_scale [I.Boundaryless]
    [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (hg : RiemannianMetricComplete g) (p : M) {a R : ℝ}
    (ha : 0 < a) (haR : a ≤ R)
    (hscale : ENNReal.ofReal R ≤ curvatureRadius g p) :
    ENNReal.ofReal (Real.exp (-4) * (a / (2 * R)) ^ 3) *
        ballVolume g p R ≤ ballVolume g p a := by
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hR : 0 < R := ha.trans_le haR
  have hRic : ∀ y ∈ riemannianBallOf g p R,
      ∀ v : TangentSpace I y,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (2 / R) ^ 2) *
        g.inner y v v ≤
          DifferentialGeometry.Geometry.Curvature.ricciTensor g y v v := by
    intro y hy v
    have h := ricci_lower_of_sectionalBoundedBelowAt g y
      (sectional_lower_on_ball_of_le_curvatureRadius g p hR hscale hy) v
    have heq : -((R / 2) ^ 2)⁻¹ = -((2 / R) ^ 2) := by
      field_simp
    rw [heq] at h
    simpa only [neg_mul, mul_neg] using h
  have h := riemannianBallOf_volume_ratio_ge_of_ricci_lower
    g hg p (q := 2 / R) (by positivity) ha haR hRic
  have hexp : -(2 / R * (2 : ℝ) * R) = -4 := by
    field_simp
    ring
  simpa only [hdim, Nat.reduceSub, Nat.cast_ofNat, hexp, ballVolume] using h


omit [CompleteSpace E] in
/-- A small ball-volume ratio controls the entire original curvature-scale ball.
Only a positive finite real comparison factor is cancelled. -/
theorem ballVolume_le_of_small_ball_at_curvature_scale [I.Boundaryless]
    [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (hg : RiemannianMetricComplete g) (p : M) {a R ε : ℝ}
    (ha : 0 < a) (haR : a ≤ R)
    (hscale : ENNReal.ofReal R ≤ curvatureRadius g p)
    (hsmall : ballVolume g p a ≤ ENNReal.ofReal (ε * a ^ 3)) :
    ballVolume g p R ≤ ENNReal.ofReal (8 * Real.exp 4 * ε * R ^ 3) := by
  have hR : 0 < R := ha.trans_le haR
  let c := Real.exp (-4) * (a / (2 * R)) ^ 3
  have hc : 0 < c := by dsimp only [c]; positivity
  have hratio := ballVolume_ratio_at_curvature_scale g hdim hg p ha haR hscale
  have hexp : Real.exp (-4) * Real.exp 4 = 1 := by
    rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos 4).ne']
  have hfactor : c * (8 * Real.exp 4 * ε * R ^ 3) = ε * a ^ 3 := by
    calc
      _ = (Real.exp (-4) * Real.exp 4) * ε * a ^ 3 := by
        dsimp only [c]
        field_simp
        ring
      _ = _ := by rw [hexp, one_mul]
  apply (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal c * ballVolume g p R ≤ ballVolume g p a := hratio
    _ ≤ ENNReal.ofReal (ε * a ^ 3) := hsmall
    _ = ENNReal.ofReal c * ENNReal.ofReal (8 * Real.exp 4 * ε * R ^ 3) := by
      rw [← ENNReal.ofReal_mul hc.le, hfactor]

end DifferentialGeometry.Geometry.Collapse
