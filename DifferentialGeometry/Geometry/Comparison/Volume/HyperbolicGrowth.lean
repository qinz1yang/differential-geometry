import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Analysis.Estimates.GaussianSeries
import DifferentialGeometry.Geometry.Comparison.Volume.Model
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Ball.EuclideanUpper
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Count

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ENNReal Manifold

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure


theorem modelVolume_neg_sq_le (n : ℕ) {q R : ℝ} (hn : 1 ≤ n)
    (hq : 0 ≤ q) (hR : 0 ≤ R) :
    modelVolume (-(q ^ 2)) n R ≤
      (n : ℝ) * euclideanUnitBallVolume n * R ^ n *
        Real.exp (q * ((n - 1 : ℕ) : ℝ) * R) := by
  have hmodel := hyperbolicRadialVolume_le (n - 1) hq hR
  have hcoeff : 0 ≤ (n : ℝ) * euclideanUnitBallVolume n :=
    mul_nonneg (Nat.cast_nonneg n) (euclideanUnitBallVolume_pos n).le
  rw [modelVolume_neg_sq q n R hq]
  calc
    (n : ℝ) * euclideanUnitBallVolume n * hyperbolicRadialVolume q (n - 1) R ≤
        (n : ℝ) * euclideanUnitBallVolume n *
          (R ^ ((n - 1) + 1) * Real.exp (q * ((n - 1 : ℕ) : ℝ) * R)) :=
      mul_le_mul_of_nonneg_left hmodel hcoeff
    _ = (n : ℝ) * euclideanUnitBallVolume n * R ^ n *
        Real.exp (q * ((n - 1 : ℕ) : ℝ) * R) := by
      rw [Nat.sub_add_cancel hn]
      ring


def hyperbolicGrowthRate (n : ℕ) (lambda : ℝ) : ℝ :=
  lambda * ((n - 1 : ℕ) : ℝ) + n


def hyperbolicGrowthConstant (n : ℕ) (lambda : ℝ) : ℝ :=
  (n : ℝ) * euclideanUnitBallVolume n *
    Real.exp (lambda * ((n - 1 : ℕ) : ℝ))

theorem hyperbolicGrowthRate_nonneg (n : ℕ) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    0 ≤ hyperbolicGrowthRate n lambda := by
  unfold hyperbolicGrowthRate
  exact add_nonneg (mul_nonneg hlambda (Nat.cast_nonneg (n - 1))) (Nat.cast_nonneg n)

theorem hyperbolicGrowthConstant_pos (n : ℕ) (lambda : ℝ) (hn : 1 ≤ n) :
    0 < hyperbolicGrowthConstant n lambda := by
  unfold hyperbolicGrowthConstant
  exact mul_pos
    (mul_pos (Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one hn))
      (euclideanUnitBallVolume_pos n))
    (Real.exp_pos _)

@[simp] theorem hyperbolicGrowthRate_zero (n : ℕ) :
    hyperbolicGrowthRate n 0 = n := by
  simp [hyperbolicGrowthRate]

@[simp] theorem hyperbolicGrowthConstant_zero (n : ℕ) :
    hyperbolicGrowthConstant n 0 = (n : ℝ) * euclideanUnitBallVolume n := by
  simp [hyperbolicGrowthConstant]

theorem modelVolume_neg_sq_nat_succ_le_exp (n k : ℕ) {lambda : ℝ}
    (hn : 1 ≤ n) (hlambda : 0 ≤ lambda) :
    modelVolume (-(lambda ^ 2)) n ((k : ℝ) + 1) ≤
      hyperbolicGrowthConstant n lambda *
        Real.exp (hyperbolicGrowthRate n lambda * (k : ℝ)) := by
  have hR0 : 0 ≤ (k : ℝ) + 1 := by positivity
  have hcoeff : 0 ≤ (n : ℝ) * euclideanUnitBallVolume n :=
    mul_nonneg (Nat.cast_nonneg n) (euclideanUnitBallVolume_pos n).le
  have hpow : ((k : ℝ) + 1) ^ n ≤ Real.exp ((n : ℝ) * (k : ℝ)) := by
    calc
      ((k : ℝ) + 1) ^ n ≤ Real.exp (k : ℝ) ^ n :=
        pow_le_pow_left₀ hR0 (Real.add_one_le_exp (k : ℝ)) n
      _ = Real.exp ((n : ℝ) * (k : ℝ)) := by
        rw [← Real.exp_nat_mul]
  calc
    modelVolume (-(lambda ^ 2)) n ((k : ℝ) + 1) ≤
        (n : ℝ) * euclideanUnitBallVolume n * ((k : ℝ) + 1) ^ n *
          Real.exp (lambda * ((n - 1 : ℕ) : ℝ) * ((k : ℝ) + 1)) :=
      modelVolume_neg_sq_le n hn hlambda hR0
    _ ≤ (n : ℝ) * euclideanUnitBallVolume n *
          Real.exp ((n : ℝ) * (k : ℝ)) *
          Real.exp (lambda * ((n - 1 : ℕ) : ℝ) * ((k : ℝ) + 1)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hcoeff) (Real.exp_pos _).le
    _ = hyperbolicGrowthConstant n lambda *
        Real.exp (hyperbolicGrowthRate n lambda * (k : ℝ)) := by
      unfold hyperbolicGrowthConstant hyperbolicGrowthRate
      have hexp :
          Real.exp ((n : ℝ) * (k : ℝ)) *
              Real.exp (lambda * ((n - 1 : ℕ) : ℝ) * ((k : ℝ) + 1)) =
            Real.exp (lambda * ((n - 1 : ℕ) : ℝ)) *
              Real.exp
                ((lambda * ((n - 1 : ℕ) : ℝ) + (n : ℝ)) * (k : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        (n : ℝ) * euclideanUnitBallVolume n * Real.exp ((n : ℝ) * (k : ℝ)) *
            Real.exp (lambda * ((n - 1 : ℕ) : ℝ) * ((k : ℝ) + 1)) =
            ((n : ℝ) * euclideanUnitBallVolume n) *
              (Real.exp ((n : ℝ) * (k : ℝ)) *
                Real.exp (lambda * ((n - 1 : ℕ) : ℝ) * ((k : ℝ) + 1))) := by
          ring
        _ = ((n : ℝ) * euclideanUnitBallVolume n) *
              (Real.exp (lambda * ((n - 1 : ℕ) : ℝ)) *
                Real.exp
                  ((lambda * ((n - 1 : ℕ) : ℝ) + (n : ℝ)) * (k : ℝ))) := by
          rw [hexp]
        _ = (n : ℝ) * euclideanUnitBallVolume n *
              Real.exp (lambda * ((n - 1 : ℕ) : ℝ)) *
                Real.exp
                  ((lambda * ((n - 1 : ℕ) : ℝ) + (n : ℝ)) * (k : ℝ)) := by
          ring


theorem modelVolume_zero_nat_succ_le_exp (n k : ℕ) (hn : 1 ≤ n) :
    modelVolume 0 n ((k : ℝ) + 1) ≤
      hyperbolicGrowthConstant n 0 *
        Real.exp (hyperbolicGrowthRate n 0 * (k : ℝ)) := by
  simpa using
    (modelVolume_neg_sq_nat_succ_le_exp n k (lambda := 0) hn (le_refl 0))

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem global_ball_volume_le_hyperbolic_model
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (hn : 2 ≤ Module.finrank ℝ E)
    {lambda R : ℝ} (hlambda : 0 ≤ lambda) (hR : 0 < R)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * lambda ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R} ≤
      ENNReal.ofReal (modelVolume (-(lambda ^ 2)) (Module.finrank ℝ E) R) := by
  have hupper := segmentBall_vol_le_euclidean (I := I) g hEnorm x hlambda hR hRic
  rw [ofReal_modelVolume_neg_sq lambda R (Module.finrank ℝ E)
    (by omega) hlambda]
  exact hupper

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem global_annulus_volume_le_exp
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (hn : 2 ≤ Module.finrank ℝ E)
    {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * lambda ^ 2)))
    (k : ℕ) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ({y : M | riemannianEDist I x y < ENNReal.ofReal ((k : ℝ) + 1)} \
          {y : M | riemannianEDist I x y < ENNReal.ofReal (k : ℝ)}) ≤
      ENNReal.ofReal
        (hyperbolicGrowthConstant (Module.finrank ℝ E) lambda *
          Real.exp (hyperbolicGrowthRate (Module.finrank ℝ E) lambda * (k : ℝ))) := by
  calc
    riemannianVolumeMeasure (I := I) (M := M) g
        ({y : M | riemannianEDist I x y < ENNReal.ofReal ((k : ℝ) + 1)} \
          {y : M | riemannianEDist I x y < ENNReal.ofReal (k : ℝ)}) ≤
        riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal ((k : ℝ) + 1)} :=
      measure_mono Set.sdiff_subset
    _ ≤ ENNReal.ofReal
        (modelVolume (-(lambda ^ 2)) (Module.finrank ℝ E) ((k : ℝ) + 1)) :=
      global_ball_volume_le_hyperbolic_model g hEnorm x hn hlambda (by positivity) hRic
    _ ≤ ENNReal.ofReal
        (hyperbolicGrowthConstant (Module.finrank ℝ E) lambda *
          Real.exp (hyperbolicGrowthRate (Module.finrank ℝ E) lambda * (k : ℝ))) :=
      ENNReal.ofReal_le_ofReal
        (modelVolume_neg_sq_nat_succ_le_exp (Module.finrank ℝ E) k
          (by omega) hlambda)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem global_gaussian_annuli_tsum_lt_top
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (hn : 2 ≤ Module.finrank ℝ E)
    {lambda c : ℝ} (hlambda : 0 ≤ lambda) (hc : 0 < c)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * lambda ^ 2))) :
    (∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (k : ℝ) ^ 2)) *
      riemannianVolumeMeasure (I := I) (M := M) g
        ({y : M | riemannianEDist I x y < ENNReal.ofReal ((k : ℝ) + 1)} \
          {y : M | riemannianEDist I x y < ENNReal.ofReal (k : ℝ)})) < ⊤ := by
  let n := Module.finrank ℝ E
  let C₁ := hyperbolicGrowthConstant n lambda
  let C₂ := hyperbolicGrowthRate n lambda
  have hseries := DifferentialGeometry.Analysis.tsum_ofReal_exp_neg_mul_sq_add_mul_lt_top c C₂ hc
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁, n]
    exact (hyperbolicGrowthConstant_pos (Module.finrank ℝ E) lambda (by omega)).le
  have hpoint (k : ℕ) :
      ENNReal.ofReal (Real.exp (-c * (k : ℝ) ^ 2)) *
          riemannianVolumeMeasure (I := I) (M := M) g
            ({y : M | riemannianEDist I x y < ENNReal.ofReal ((k : ℝ) + 1)} \
              {y : M | riemannianEDist I x y < ENNReal.ofReal (k : ℝ)}) ≤
        ENNReal.ofReal C₁ * ENNReal.ofReal
          (Real.exp (-c * (k : ℝ) ^ 2 + C₂ * (k : ℝ))) := by
    calc
      ENNReal.ofReal (Real.exp (-c * (k : ℝ) ^ 2)) *
          riemannianVolumeMeasure (I := I) (M := M) g
            ({y : M | riemannianEDist I x y < ENNReal.ofReal ((k : ℝ) + 1)} \
              {y : M | riemannianEDist I x y < ENNReal.ofReal (k : ℝ)}) ≤
          ENNReal.ofReal (Real.exp (-c * (k : ℝ) ^ 2)) *
            ENNReal.ofReal (C₁ * Real.exp (C₂ * (k : ℝ))) := by
        gcongr
        exact global_annulus_volume_le_exp g hEnorm x hn hlambda hRic k
      _ = ENNReal.ofReal C₁ * ENNReal.ofReal
          (Real.exp (-c * (k : ℝ) ^ 2 + C₂ * (k : ℝ))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul hC₁]
        congr 1
        rw [Real.exp_add]
        ring
  calc
    (∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (k : ℝ) ^ 2)) *
        riemannianVolumeMeasure (I := I) (M := M) g
          ({y : M | riemannianEDist I x y < ENNReal.ofReal ((k : ℝ) + 1)} \
            {y : M | riemannianEDist I x y < ENNReal.ofReal (k : ℝ)})) ≤
        ∑' k : ℕ, ENNReal.ofReal C₁ * ENNReal.ofReal
          (Real.exp (-c * (k : ℝ) ^ 2 + C₂ * (k : ℝ))) :=
      ENNReal.tsum_le_tsum hpoint
    _ = ENNReal.ofReal C₁ *
        ∑' k : ℕ, ENNReal.ofReal
          (Real.exp (-c * (k : ℝ) ^ 2 + C₂ * (k : ℝ))) :=
      ENNReal.tsum_mul_left
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hseries

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open scoped ContDiff

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianVolumeMeasure_ball_le_exponential
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDistOf (I := I) g p y < ENNReal.ofReal R} ≤
      ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ) *
        ENNReal.ofReal (Real.exp
          ((q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E) * R)) := by
  classical
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R)) := by
    have hc := RiemannianMetricComplete.closedEBall_isCompact (I := I) hcomplete p R
    have hset : Metric.closedEBall p (ENNReal.ofReal R) =
        {y | riemannianEDistOf (I := I) g p y ≤ ENNReal.ofReal R} := by
      ext y
      rw [Metric.mem_closedEBall', IsRiemannianManifold.out (I := I)]
      simp only [mem_ofPred_eq, riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
    rw [hset]
    exact hc
  have hvol := riemannianVolumeMeasure_ball_le_hyperbolic_of_isCompact_closedEBall
    (I := I) g hEnorm p hq hR hcpt (fun y v _ => hRic y v)
  have hn : 1 ≤ Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  have hpow : R ^ Module.finrank ℝ E ≤ Real.exp ((Module.finrank ℝ E : ℝ) * R) := by
    calc
      R ^ Module.finrank ℝ E ≤ Real.exp R ^ Module.finrank ℝ E :=
        pow_le_pow_left₀ hR.le ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp R)) _
      _ = Real.exp ((Module.finrank ℝ E : ℝ) * R) := by rw [← Real.exp_nat_mul]
  have hmodel : hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R ≤
      Real.exp ((q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E) * R) := by
    calc
      hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R ≤
          R ^ Module.finrank ℝ E * Real.exp (q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * R) := by
        simpa only [Nat.sub_add_cancel hn] using hyperbolicRadialVolume_le (Module.finrank ℝ E - 1) hq hR.le
      _ ≤ Real.exp ((Module.finrank ℝ E : ℝ) * R) *
          Real.exp (q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * R) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
      _ = Real.exp ((q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E) * R) := by
        rw [← Real.exp_add]
        congr 1
        ring
  simp only [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
  exact hvol.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hmodel))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
