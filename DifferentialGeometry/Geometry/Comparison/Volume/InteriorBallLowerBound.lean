import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.LocalBallRatio
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem riemannianBallOf_volume_lower_of_nearby_center
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p q : M) {s r w : ℝ} (hs : 0 < s) (hr : 0 < r) (hrs : r ≤ s / 2)
    (hq : q ∈ riemannianBallOf g p (s / 4))
    (hsec : ∀ x ∈ riemannianBallOf g p s,
      SectionalBoundedBelowAt g x (-(s ^ 2)⁻¹))
    (hvolume : ENNReal.ofReal (w * s ^ Module.finrank ℝ E) ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g p s)) :
    ENNReal.ofReal (w * Real.exp (-3 * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) / 2) /
        8 ^ Module.finrank ℝ E * r ^ Module.finrank ℝ E) ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g q r) := by
  let _ : T2Space (TangentBundle I M) :=
    DifferentialGeometry.FiberBundle.t2Space_totalSpace (F := E) (E := TangentSpace I)
  let n : ℕ := Module.finrank ℝ E
  let d : ℝ := ((n - 1 : ℕ) : ℝ)
  let c₀ : ℝ := Real.exp (-d) / 8 ^ n
  let c₁ : ℝ := Real.exp (-d / 2) * (r / s) ^ n
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hRic : ∀ x ∈ riemannianBallOf g p s, ∀ v : TangentSpace I x,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (s⁻¹) ^ 2) * g.inner x v v ≤
        ricciTensor g x v v := by
    intro x hx v
    simpa only [inv_pow, mul_neg] using
      ricci_lower_of_sectionalBoundedBelowAt g x (hsec x hx) v
  have hfirst := riemannianBallOf_volume_ratio_ge_of_ricci_lower g hcomplete p
    (q := s⁻¹) (inv_nonneg.mpr hs.le) (by positivity : 0 < s / 4)
    (by linarith : s / 4 ≤ s) hRic
  have he₀ : s⁻¹ * d * s = d := by field_simp [hs.ne']
  have hr₀ : (s / 4) / (2 * s) = (1 / 8 : ℝ) := by field_simp [hs.ne']; ring
  have hcoef₀ : Real.exp (-(s⁻¹ * d * s)) * ((s / 4) / (2 * s)) ^ n = c₀ := by
    rw [he₀, hr₀]
    dsimp only [c₀]
    rw [div_pow, one_pow]
    ring
  change ENNReal.ofReal (Real.exp (-(s⁻¹ * d * s)) * ((s / 4) / (2 * s)) ^ n) *
      riemannianVolumeMeasure I M g (riemannianBallOf g p s) ≤
    riemannianVolumeMeasure I M g (riemannianBallOf g p (s / 4)) at hfirst
  rw [hcoef₀] at hfirst
  have hinner : riemannianBallOf g p (s / 4) ⊆ riemannianBallOf g q (s / 2) := by
    intro x hx
    have hqp : riemannianEDistOf g q p < ENNReal.ofReal (s / 4) := by
      rw [riemannianEDistOf_comm g q p]
      exact hq
    have hdist := (riemannianEDistOf_triangle g q p x).trans_lt (ENNReal.add_lt_add hqp hx)
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ s / 4) (by positivity)] at hdist
    change riemannianEDistOf g q x < ENNReal.ofReal (s / 2)
    simpa only [show s / 4 + s / 4 = s / 2 by ring] using hdist
  have houter : riemannianBallOf g q (s / 2) ⊆ riemannianBallOf g p s := by
    intro x hx
    have hdist := (riemannianEDistOf_triangle g p q x).trans_lt (ENNReal.add_lt_add hq hx)
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ s / 4) (by positivity)] at hdist
    exact hdist.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hsecond := riemannianBallOf_volume_ratio_ge_of_ricci_lower g hcomplete q
    (q := s⁻¹) (inv_nonneg.mpr hs.le) hr hrs
    (fun x hx v => hRic x (houter hx) v)
  have he₁ : s⁻¹ * d * (s / 2) = d / 2 := by field_simp [hs.ne']
  have hr₁ : r / (2 * (s / 2)) = r / s := by congr 1; ring
  have hcoef₁ : Real.exp (-(s⁻¹ * d * (s / 2))) * (r / (2 * (s / 2))) ^ n = c₁ := by
    rw [he₁, hr₁]
    dsimp only [c₁]
    congr 2
    ring
  change ENNReal.ofReal (Real.exp (-(s⁻¹ * d * (s / 2))) *
      (r / (2 * (s / 2))) ^ n) *
      riemannianVolumeMeasure I M g (riemannianBallOf g q (s / 2)) ≤
    riemannianVolumeMeasure I M g (riemannianBallOf g q r) at hsecond
  rw [hcoef₁] at hsecond
  have hquarter : ENNReal.ofReal c₀ * ENNReal.ofReal (w * s ^ n) ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g p (s / 4)) :=
    (mul_le_mul' le_rfl hvolume).trans hfirst
  have hnear := hquarter.trans (MeasureTheory.measure_mono hinner)
  have hresult := (mul_le_mul' (le_refl (ENNReal.ofReal c₁)) hnear).trans hsecond
  rw [← ENNReal.ofReal_mul hc₀, ← ENNReal.ofReal_mul hc₁] at hresult
  have hcoef : c₁ * (c₀ * (w * s ^ n)) =
      w * Real.exp (-3 * d / 2) / 8 ^ n * r ^ n := by
    have hexp : Real.exp (-d / 2) * Real.exp (-d) = Real.exp (-3 * d / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [c₀, c₁]
    rw [div_pow]
    calc
      _ = (Real.exp (-d / 2) * Real.exp (-d)) * w * r ^ n / 8 ^ n := by
        field_simp [hs.ne']
      _ = _ := by rw [hexp]; ring
  rw [hcoef] at hresult
  exact hresult

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
