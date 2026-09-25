import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.CompactBall
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianBallOf_volume_mul_pow_le
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : RicciBoundedBelow (I := I) g 0) (p : M)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    riemannianVolumeMeasure I M g (riemannianBallOf g p R) *
        ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal (R ^ Module.finrank ℝ E) *
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
  have hrel := bishop_gromov_of_isCompact_closedEBall g hEnorm p
    (q := 0) (by norm_num) hr hrR hcpt
    (fun y v _ => by simpa using hRic y v)
  let n : ℕ := Module.finrank ℝ E
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmodel (s : ℝ) (hs : 0 ≤ s) :
      ENNReal.ofReal (hyperbolicRadialVolume 0 (n - 1) s) =
        ENNReal.ofReal (s ^ n) * ENNReal.ofReal ((n : ℝ)⁻¹) := by
    have hnR : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub hn]
      norm_num
    rw [hyperbolicRadialVolume_zero, Nat.sub_add_cancel hn, hnR, div_eq_mul_inv,
      ENNReal.ofReal_mul (pow_nonneg hs n)]
  rw [show Module.finrank ℝ E - 1 = n - 1 by rfl,
    hmodel r hr.le, hmodel R (hr.trans_le hrR).le] at hrel
  have hp : 0 < ENNReal.ofReal ((n : ℝ)⁻¹) :=
    ENNReal.ofReal_pos.mpr (inv_pos.mpr (Nat.cast_pos.mpr hn))
  apply (ENNReal.mul_le_mul_iff_right hp.ne' ENNReal.ofReal_ne_top).mp
  simpa only [n, riemannianBallOf, riemannianEDistOf, mul_assoc, mul_left_comm, mul_comm] using hrel

theorem riemannianBallOf_volume_le_of_small_ball
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : RicciBoundedBelow (I := I) g 0) (p : M)
    {r R eps : ℝ} (hr : 0 < r) (hrR : r ≤ R) (heps : 0 ≤ eps)
    (hsmall : riemannianVolumeMeasure I M g (riemannianBallOf g p r) ≤
      ENNReal.ofReal (eps * r ^ Module.finrank ℝ E)) :
    riemannianVolumeMeasure I M g (riemannianBallOf g p R) ≤
      ENNReal.ofReal (eps * R ^ Module.finrank ℝ E) := by
  have hcross := riemannianBallOf_volume_mul_pow_le g hcomplete hRic p hr hrR
  have hp : 0 < ENNReal.ofReal (r ^ Module.finrank ℝ E) :=
    ENNReal.ofReal_pos.mpr (pow_pos hr _)
  apply (ENNReal.mul_le_mul_iff_left hp.ne' ENNReal.ofReal_ne_top).mp
  calc
    _ ≤ ENNReal.ofReal (R ^ Module.finrank ℝ E) *
        riemannianVolumeMeasure I M g (riemannianBallOf g p r) := hcross
    _ ≤ ENNReal.ofReal (R ^ Module.finrank ℝ E) *
        ENNReal.ofReal (eps * r ^ Module.finrank ℝ E) := mul_le_mul_right hsmall _
    _ = _ := by
      rw [ENNReal.ofReal_mul heps, ENNReal.ofReal_mul heps]
      ac_rfl


theorem tendsto_riemannianBallOf_volume_zero_of_small_rescaled_balls
    {α : Type*} {l : Filter α}
    (N : α → Type*) [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace H (N i)]
    [∀ i, IsManifold I ∞ (N i)] [∀ i, T2Space (N i)]
    [∀ i, T2Space (TangentBundle I (N i))] [∀ i, SigmaCompactSpace (N i)]
    (g : ∀ i, SmoothRiemannianMetric I (N i))
    (hcomplete : ∀ i, RiemannianMetricComplete (g i))
    (hRic : ∀ i, RicciBoundedBelow (I := I) (g i) 0)
    (p : ∀ i, N i) {Q : α → ℝ} (hQ : Tendsto Q l atTop)
    (hsmall : ∀ eps : ℝ, 0 < eps → ∃ A : ℝ, 0 < A ∧
      ∀ᶠ i in l,
        riemannianVolumeMeasure I (N i) (g i)
          (riemannianBallOf (g i) (p i) (A / Real.sqrt (Q i))) ≤
            ENNReal.ofReal (eps * (A / Real.sqrt (Q i)) ^ Module.finrank ℝ E))
    {D : ℝ} (hD : 0 < D) :
    Tendsto (fun i => riemannianVolumeMeasure I (N i) (g i)
      (riemannianBallOf (g i) (p i) D)) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro eps heps
  obtain ⟨delta, _, hdeltapos, hdeltaeps⟩ := ENNReal.lt_iff_exists_real_btwn.mp heps
  have hdelta : 0 < delta := ENNReal.ofReal_pos.mp hdeltapos
  have hDpow : 0 < D ^ Module.finrank ℝ E := pow_pos hD _
  obtain ⟨A, hA, hsmallA⟩ := hsmall (delta / D ^ Module.finrank ℝ E)
    (div_pos hdelta hDpow)
  have hrzero : Tendsto (fun i => A / Real.sqrt (Q i)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hQ)
  filter_upwards [hsmallA, hQ.eventually_gt_atTop 0,
    hrzero.eventually_lt_const hD] with i hi hQi hrD
  have hr : 0 < A / Real.sqrt (Q i) := div_pos hA (Real.sqrt_pos.mpr hQi)
  have hvol := riemannianBallOf_volume_le_of_small_ball (g i) (hcomplete i) (hRic i)
    (p i) hr hrD.le (div_nonneg hdelta.le hDpow.le) hi
  rw [div_mul_cancel₀ delta hDpow.ne'] at hvol
  exact hvol.trans hdeltaeps.le

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
