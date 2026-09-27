import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.CompactBall
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Count
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Distance.Ball

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
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianBallOf_bishop_gromov_of_ricci_lower
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {q r R : ℝ} (hq : 0 ≤ q) (hr : 0 < r) (hrR : r ≤ R)
    (hRic : ∀ y ∈ riemannianBallOf g p R, ∀ v : TangentSpace I y,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner y v v ≤
        ricciTensor (I := I) g y v v) :
    riemannianVolumeMeasure I M g (riemannianBallOf g p R) *
        ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) r) ≤
      ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R) *
        riemannianVolumeMeasure I M g (riemannianBallOf g p r) := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  have hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hcpt : IsCompact (Metric.closedEBall p (ENNReal.ofReal R)) := by
    have hset : Metric.closedEBall p (ENNReal.ofReal R) =
        {x : M | riemannianEDistOf (I := I) g p x ≤ ENNReal.ofReal R} := by
      ext x
      rw [Metric.mem_closedEBall', IsRiemannianManifold.out (I := I) p x]
      rfl
    rw [hset]
    exact hcomplete.closedEBall_isCompact p R
  have hrel := bishop_gromov_of_isCompact_closedEBall g hEnorm p hq hr hrR hcpt
    (fun y v hy => hRic y hy v)
  simpa only [riemannianBallOf, riemannianEDistOf] using hrel

theorem riemannianBallOf_volume_ratio_ge_of_ricci_lower
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {q r R : ℝ} (hq : 0 ≤ q) (hr : 0 < r) (hrR : r ≤ R)
    (hRic : ∀ y ∈ riemannianBallOf g p R, ∀ v : TangentSpace I y,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner y v v ≤
        ricciTensor (I := I) g y v v) :
    ENNReal.ofReal (Real.exp (-(q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * R)) *
        (r / (2 * R)) ^ Module.finrank ℝ E) *
        riemannianVolumeMeasure I M g (riemannianBallOf g p R) ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g p r) := by
  set n : ℕ := Module.finrank ℝ E with hndef
  set d : ℕ := n - 1 with hddef
  have hn : d + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))
  have hR : 0 < R := hr.trans_le hrR
  have hrel := riemannianBallOf_bishop_gromov_of_ricci_lower g hcomplete p hq hr hrR hRic
  set Vr := hyperbolicRadialVolume q d r with hVr
  have hVr_pos : 0 < Vr := (pow_pos (half_pos hr) _).trans_le (hyperbolicRadialVolume_ge d hq hr)
  have hratio := hyperbolicRadialVolume_ratio_le d hq hr hrR
  rw [hn] at hratio
  set c : ℝ := Real.exp (-(q * (d : ℝ) * R)) * (r / (2 * R)) ^ n with hc
  have hc0 : 0 ≤ c := by positivity
  have hkey : c * (Real.exp (q * (d : ℝ) * R) * (R / (r / 2)) ^ n) = 1 := by
    rw [hc, Real.exp_neg]
    have h1 : (r / (2 * R)) ^ n * (R / (r / 2)) ^ n = 1 := by
      rw [← mul_pow]
      have : r / (2 * R) * (R / (r / 2)) = 1 := by field_simp
      rw [this, one_pow]
    have h2 : (Real.exp (q * (d : ℝ) * R))⁻¹ * Real.exp (q * (d : ℝ) * R) = 1 :=
      inv_mul_cancel₀ (Real.exp_pos _).ne'
    calc (Real.exp (q * (d : ℝ) * R))⁻¹ * (r / (2 * R)) ^ n *
          (Real.exp (q * (d : ℝ) * R) * (R / (r / 2)) ^ n)
        = ((Real.exp (q * (d : ℝ) * R))⁻¹ * Real.exp (q * (d : ℝ) * R)) *
          ((r / (2 * R)) ^ n * (R / (r / 2)) ^ n) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have hVR : ENNReal.ofReal (hyperbolicRadialVolume q d R) ≤
      ENNReal.ofReal (Real.exp (q * (d : ℝ) * R) * (R / (r / 2)) ^ n * Vr) :=
    ENNReal.ofReal_le_ofReal hratio
  have hV0 : ENNReal.ofReal Vr ≠ 0 := (ENNReal.ofReal_pos.mpr hVr_pos).ne'
  have hVt : ENNReal.ofReal Vr ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_left hV0 hVt).mp
  calc ENNReal.ofReal c * riemannianVolumeMeasure I M g (riemannianBallOf g p R) *
        ENNReal.ofReal Vr
      = ENNReal.ofReal c * (riemannianVolumeMeasure I M g (riemannianBallOf g p R) *
        ENNReal.ofReal Vr) := by rw [mul_assoc]
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (hyperbolicRadialVolume q d R) *
        riemannianVolumeMeasure I M g (riemannianBallOf g p r)) := mul_le_mul' le_rfl hrel
    _ ≤ ENNReal.ofReal c *
        (ENNReal.ofReal (Real.exp (q * (d : ℝ) * R) * (R / (r / 2)) ^ n * Vr) *
          riemannianVolumeMeasure I M g (riemannianBallOf g p r)) :=
        mul_le_mul' le_rfl (mul_le_mul' hVR le_rfl)
    _ = riemannianVolumeMeasure I M g (riemannianBallOf g p r) * ENNReal.ofReal Vr := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc0, ← mul_assoc, hkey, one_mul, mul_comm]

theorem riemannianBallOf_volume_ratio_ge_of_ricci_nonneg
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRic : ∀ y ∈ riemannianBallOf g p R, ∀ v : TangentSpace I y,
      0 ≤ ricciTensor (I := I) g y v v) :
    ENNReal.ofReal ((r / R) ^ Module.finrank ℝ E) *
        riemannianVolumeMeasure I M g (riemannianBallOf g p R) ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g p r) := by
  set n : ℕ := Module.finrank ℝ E with hndef
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hR : 0 < R := hr.trans_le hrR
  have hrel := riemannianBallOf_bishop_gromov_of_ricci_lower g hcomplete p (q := 0) le_rfl hr hrR
    (fun y hy v => by simpa using hRic y hy v)
  have hmodel (s : ℝ) (hs : 0 ≤ s) :
      ENNReal.ofReal (hyperbolicRadialVolume 0 (n - 1) s) =
        ENNReal.ofReal (s ^ n) * ENNReal.ofReal ((n : ℝ)⁻¹) := by
    have hnR : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub hnpos]
      norm_num
    rw [hyperbolicRadialVolume_zero, Nat.sub_add_cancel hnpos, hnR, div_eq_mul_inv,
      ENNReal.ofReal_mul (pow_nonneg hs n)]
  rw [hmodel r hr.le, hmodel R hR.le] at hrel
  have hp : ENNReal.ofReal ((n : ℝ)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (Nat.cast_pos.mpr hnpos))).ne'
  have hcross : riemannianVolumeMeasure I M g (riemannianBallOf g p R) * ENNReal.ofReal (r ^ n) ≤
      ENNReal.ofReal (R ^ n) * riemannianVolumeMeasure I M g (riemannianBallOf g p r) := by
    apply (ENNReal.mul_le_mul_iff_left hp ENNReal.ofReal_ne_top).mp
    calc riemannianVolumeMeasure I M g (riemannianBallOf g p R) * ENNReal.ofReal (r ^ n) *
          ENNReal.ofReal ((n : ℝ)⁻¹)
        = riemannianVolumeMeasure I M g (riemannianBallOf g p R) *
          (ENNReal.ofReal (r ^ n) * ENNReal.ofReal ((n : ℝ)⁻¹)) := by rw [mul_assoc]
      _ ≤ ENNReal.ofReal (R ^ n) * ENNReal.ofReal ((n : ℝ)⁻¹) *
          riemannianVolumeMeasure I M g (riemannianBallOf g p r) := hrel
      _ = ENNReal.ofReal (R ^ n) * riemannianVolumeMeasure I M g (riemannianBallOf g p r) *
          ENNReal.ofReal ((n : ℝ)⁻¹) := by ring
  have hRn0 : ENNReal.ofReal (R ^ n) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hR n)).ne'
  apply (ENNReal.mul_le_mul_iff_right hRn0 ENNReal.ofReal_ne_top).mp
  calc ENNReal.ofReal (R ^ n) * (ENNReal.ofReal ((r / R) ^ n) *
        riemannianVolumeMeasure I M g (riemannianBallOf g p R))
      = riemannianVolumeMeasure I M g (riemannianBallOf g p R) *
        ENNReal.ofReal (R ^ n * (r / R) ^ n) := by
        rw [ENNReal.ofReal_mul (pow_nonneg hR.le n)]
        ring
    _ = riemannianVolumeMeasure I M g (riemannianBallOf g p R) * ENNReal.ofReal (r ^ n) := by
        rw [← mul_pow, mul_div_cancel₀ r hR.ne']
    _ ≤ ENNReal.ofReal (R ^ n) * riemannianVolumeMeasure I M g (riemannianBallOf g p r) := hcross

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
