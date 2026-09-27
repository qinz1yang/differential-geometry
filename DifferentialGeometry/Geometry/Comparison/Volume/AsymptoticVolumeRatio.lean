import DifferentialGeometry.Geometry.Comparison.Volume.Model
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Ball.EuclideanUpper

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]


def ballVolume (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) : ℝ≥0∞ :=
  riemannianVolumeMeasure (I := I) (M := M) g
    {x : M | riemannianEDist I p x < ENNReal.ofReal r}


def normalizedBallVolume (g : SmoothRiemannianMetric I M) (p : M)
    (R : Set.Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ballVolume g p R.1 /
    ENNReal.ofReal
      (euclideanUnitBallVolume (Module.finrank ℝ E) * R.1 ^ Module.finrank ℝ E)

def asymptoticVolumeRatio (g : SmoothRiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  ⨅ R : Set.Ioi (0 : ℝ), normalizedBallVolume g p R


theorem normalizedBallVolume_antitone [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (hRic : RicciBoundedBelow (I := I) g 0) :
    Antitone (normalizedBallVolume g p) := by
  intro r R hrR
  let n : ℕ := Module.finrank ℝ E
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hω : 0 < euclideanUnitBallVolume n := euclideanUnitBallVolume_pos n
  have hdenR : 0 < ENNReal.ofReal
      (euclideanUnitBallVolume n * R.1 ^ n) :=
    ENNReal.ofReal_pos.mpr (mul_pos hω (pow_pos R.2 n))
  have hdenr : 0 < ENNReal.ofReal
      (euclideanUnitBallVolume n * r.1 ^ n) :=
    ENNReal.ofReal_pos.mpr (mul_pos hω (pow_pos r.2 n))
  have hrel := segmentBall_vol_pow (I := I) g hEnorm p r.2 hrR hRic
  change ballVolume g p R.1 /
      ENNReal.ofReal (euclideanUnitBallVolume n * R.1 ^ n) ≤
    ballVolume g p r.1 /
      ENNReal.ofReal (euclideanUnitBallVolume n * r.1 ^ n)
  apply (ENNReal.div_le_iff hdenR.ne' ENNReal.ofReal_ne_top).2
  rw [← ENNReal.mul_div_right_comm]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hdenr.ne')
    (Or.inl ENNReal.ofReal_ne_top)).2
  calc
    ballVolume g p R.1 * ENNReal.ofReal
        (euclideanUnitBallVolume n * r.1 ^ n) =
        ENNReal.ofReal (euclideanUnitBallVolume n) *
          (ballVolume g p R.1 * ENNReal.ofReal (r.1 ^ n)) := by
      rw [ENNReal.ofReal_mul hω.le]
      ac_rfl
    _ ≤ ENNReal.ofReal (euclideanUnitBallVolume n) *
        (ENNReal.ofReal (R.1 ^ n) * ballVolume g p r.1) := by
      exact mul_le_mul_right hrel _
    _ = ballVolume g p r.1 * ENNReal.ofReal
        (euclideanUnitBallVolume n * R.1 ^ n) := by
      rw [ENNReal.ofReal_mul hω.le]
      ac_rfl

theorem ballVolume_power_ratio [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (hRic : RicciBoundedBelow (I := I) g 0)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ballVolume g p R / ENNReal.ofReal (R ^ Module.finrank ℝ E) ≤
      ballVolume g p r / ENNReal.ofReal (r ^ Module.finrank ℝ E) := by
  let n : ℕ := Module.finrank ℝ E
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hdenR : 0 < ENNReal.ofReal (R ^ n) :=
    ENNReal.ofReal_pos.mpr (pow_pos hR n)
  have hdenr : 0 < ENNReal.ofReal (r ^ n) :=
    ENNReal.ofReal_pos.mpr (pow_pos hr n)
  have hrel := segmentBall_vol_pow (I := I) g hEnorm p hr hrR hRic
  apply (ENNReal.div_le_iff hdenR.ne' ENNReal.ofReal_ne_top).2
  rw [← ENNReal.mul_div_right_comm]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hdenr.ne')
    (Or.inl ENNReal.ofReal_ne_top)).2
  simpa [n, ballVolume, mul_comm] using hrel

theorem ballVolume_radius_transfer [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (hRic : RicciBoundedBelow (I := I) g 0)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ENNReal.ofReal ((r / R) ^ Module.finrank ℝ E) * ballVolume g p R ≤
      ballVolume g p r := by
  let n : ℕ := Module.finrank ℝ E
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hdenR : 0 < ENNReal.ofReal (R ^ n) :=
    ENNReal.ofReal_pos.mpr (pow_pos hR n)
  have hrel := segmentBall_vol_pow (I := I) g hEnorm p hr hrR hRic
  change ENNReal.ofReal ((r / R) ^ n) * ballVolume g p R ≤ ballVolume g p r
  rw [div_pow, ENNReal.ofReal_div_of_pos (pow_pos hR n),
    ← ENNReal.mul_div_right_comm]
  apply (ENNReal.div_le_iff hdenR.ne' ENNReal.ofReal_ne_top).2
  simpa [n, ballVolume, mul_comm, mul_left_comm, mul_assoc] using hrel

theorem tendsto_normalizedBallVolume_atTop [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (hRic : RicciBoundedBelow (I := I) g 0) :
    Tendsto (normalizedBallVolume g p) atTop
      (𝓝 (asymptoticVolumeRatio g p)) := by
  exact tendsto_atTop_iInf (normalizedBallVolume_antitone g hEnorm p hRic)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space (TangentBundle I M)] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
theorem asymptoticVolumeRatio_le_normalizedBallVolume
    (g : SmoothRiemannianMetric I M) (p : M) (R : Set.Ioi (0 : ℝ)) :
    asymptoticVolumeRatio g p ≤ normalizedBallVolume g p R := by
  exact iInf_le (normalizedBallVolume g p) R

theorem ballVolume_le_euclidean [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (hRic : RicciBoundedBelow (I := I) g 0)
    {R : ℝ} (hR : 0 < R) :
    ballVolume g p R ≤ ENNReal.ofReal
      (euclideanUnitBallVolume (Module.finrank ℝ E) *
        R ^ Module.finrank ℝ E) := by
  let n : ℕ := Module.finrank ℝ E
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hRic0 : RicciBoundedBelow (I := I) g
      (-((Module.finrank ℝ E - 1 : ℕ) * (0 : ℝ) ^ 2)) := by
    simpa using hRic
  have hupper := segmentBall_vol_le_euclidean (I := I) g hEnorm p
    (q := 0) (le_refl 0) hR hRic0
  have hmodel :
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ *
          ENNReal.ofReal (hyperbolicRadialVolume 0 (n - 1) R) =
        ENNReal.ofReal (euclideanUnitBallVolume n * R ^ n) := by
    rw [← ofReal_modelVolume_neg_sq 0 R n hn (le_refl 0)]
    norm_num only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero]
    rw [modelVolume_zero n R hn]
  exact hupper.trans_eq hmodel


theorem normalizedBallVolume_le_one [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (hRic : RicciBoundedBelow (I := I) g 0)
    (R : Set.Ioi (0 : ℝ)) :
    normalizedBallVolume g p R ≤ 1 := by
  let n : ℕ := Module.finrank ℝ E
  have hω : 0 < euclideanUnitBallVolume n := euclideanUnitBallVolume_pos n
  have hden : 0 < ENNReal.ofReal
      (euclideanUnitBallVolume n * R.1 ^ n) :=
    ENNReal.ofReal_pos.mpr (mul_pos hω (pow_pos R.2 n))
  apply (ENNReal.div_le_iff hden.ne' ENNReal.ofReal_ne_top).2
  simpa only [one_mul] using ballVolume_le_euclidean g hEnorm p hRic R.2


theorem asymptoticVolumeRatio_mem_Icc [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (hRic : RicciBoundedBelow (I := I) g 0) :
    asymptoticVolumeRatio g p ∈ Set.Icc (0 : ℝ≥0∞) 1 := by
  let R : Set.Ioi (0 : ℝ) := ⟨1, by simp⟩
  refine ⟨bot_le, ?_⟩
  exact (asymptoticVolumeRatio_le_normalizedBallVolume g p R).trans
    (normalizedBallVolume_le_one g hEnorm p hRic R)

theorem asymptoticVolumeRatio_ne_top [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (hRic : RicciBoundedBelow (I := I) g 0) :
    asymptoticVolumeRatio g p ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    (asymptoticVolumeRatio_mem_Icc g hEnorm p hRic).2

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space (TangentBundle I M)] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
theorem asymptoticVolumeRatio_mul_euclidean_le_ballVolume
    (g : SmoothRiemannianMetric I M) (p : M)
    {R : ℝ} (hR : 0 < R) :
    asymptoticVolumeRatio g p * ENNReal.ofReal
        (euclideanUnitBallVolume (Module.finrank ℝ E) *
          R ^ Module.finrank ℝ E) ≤
      ballVolume g p R := by
  let n : ℕ := Module.finrank ℝ E
  have hω : 0 < euclideanUnitBallVolume n := euclideanUnitBallVolume_pos n
  have hden : 0 < ENNReal.ofReal
      (euclideanUnitBallVolume n * R ^ n) :=
    ENNReal.ofReal_pos.mpr (mul_pos hω (pow_pos hR n))
  exact (ENNReal.le_div_iff_mul_le (Or.inl hden.ne')
    (Or.inl ENNReal.ofReal_ne_top)).mp
      (asymptoticVolumeRatio_le_normalizedBallVolume g p ⟨R, hR⟩)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space (TangentBundle I M)] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
theorem ballVolume_lower_of_le_asymptoticVolumeRatio
    (g : SmoothRiemannianMetric I M) (p : M) {v R : ℝ}
    (hv : ENNReal.ofReal v ≤ asymptoticVolumeRatio g p) (hR : 0 < R) :
    ENNReal.ofReal v * ENNReal.ofReal
        (euclideanUnitBallVolume (Module.finrank ℝ E) *
          R ^ Module.finrank ℝ E) ≤
      ballVolume g p R := by
  have hmul :
      ENNReal.ofReal v * ENNReal.ofReal
          (euclideanUnitBallVolume (Module.finrank ℝ E) *
            R ^ Module.finrank ℝ E) ≤
        asymptoticVolumeRatio g p * ENNReal.ofReal
          (euclideanUnitBallVolume (Module.finrank ℝ E) *
            R ^ Module.finrank ℝ E) := by
    simpa only [mul_comm] using
      (mul_le_mul_right hv
        (ENNReal.ofReal (euclideanUnitBallVolume (Module.finrank ℝ E) *
          R ^ Module.finrank ℝ E)))
  exact hmul.trans (asymptoticVolumeRatio_mul_euclidean_le_ballVolume g p hR)

theorem nonnegativeRicciAVR [ConnectedSpace M] [CompleteSpace M]
    [_hNoncompact : NoncompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (hn : 2 ≤ Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    (∀ ⦃r R : ℝ⦄, 0 < r → r ≤ R →
        ballVolume g p R / ENNReal.ofReal (R ^ Module.finrank ℝ E) ≤
          ballVolume g p r / ENNReal.ofReal (r ^ Module.finrank ℝ E)) ∧
    (∀ ⦃r R : ℝ⦄, 0 < r → r ≤ R →
        ENNReal.ofReal ((r / R) ^ Module.finrank ℝ E) * ballVolume g p R ≤
          ballVolume g p r) ∧
    (∀ ⦃R : ℝ⦄, 0 < R →
        ballVolume g p R ≤ ENNReal.ofReal
          (euclideanUnitBallVolume (Module.finrank ℝ E) *
            R ^ Module.finrank ℝ E)) ∧
    Tendsto (normalizedBallVolume g p) atTop
      (𝓝 (asymptoticVolumeRatio g p)) ∧
    asymptoticVolumeRatio g p ∈ Set.Icc (0 : ℝ≥0∞) 1 ∧
    ∀ ⦃R : ℝ⦄, 0 < R →
      asymptoticVolumeRatio g p * ENNReal.ofReal
          (euclideanUnitBallVolume (Module.finrank ℝ E) *
            R ^ Module.finrank ℝ E) ≤
        ballVolume g p R := by
  have _ := hn
  refine ⟨?_, ?_, ?_, tendsto_normalizedBallVolume_atTop g hEnorm p hRic,
    asymptoticVolumeRatio_mem_Icc g hEnorm p hRic, ?_⟩
  · intro r R hr hrR
    exact ballVolume_power_ratio g hEnorm p hRic hr hrR
  · intro r R hr hrR
    exact ballVolume_radius_transfer g hEnorm p hRic hr hrR
  · intro R hR
    exact ballVolume_le_euclidean g hEnorm p hRic hR
  · intro R hR
    exact asymptoticVolumeRatio_mul_euclidean_le_ballVolume g p hR

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
