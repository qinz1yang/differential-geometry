import DifferentialGeometry.Geometry.Metric.IntrinsicInjectivityRadius
import DifferentialGeometry.Geometry.Exponential.IntrinsicBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialReducedLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeSetLower
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Geometry.Riemannian
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

def initialReducedVolumeLowerCoeff (n : ℕ) (H K c : ℝ) : ℝ :=
  let r₀ := min (c / 2) (intrinsicNormalMetricRadius n K)
  let C := compactCurvatureControlTime n K
  let δ := C / 2
  let Q := (n : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)
  let Λ := Real.exp (2 * Q * C)
  let L := max (Λ / 4 + Q * C / 3)
    ((n : ℝ) / 2 + Λ * r₀ ^ 2 / (2 * δ) + Q * δ)
  intrinsicBallVolumeCoeff n *
    min (r₀ ^ n * (4 * Real.pi * H) ^ (-(n : ℝ) / 2))
      ((4 * Real.pi) ^ (-(n : ℝ) / 2)) * Real.exp (-L)

theorem initialReducedVolumeLowerCoeff_pos (n : ℕ) (H K c : ℝ)
    (hH : 0 < H) (hK : 0 < K) (hc : 0 < c) :
    0 < initialReducedVolumeLowerCoeff n H K c := by
  have hr : 0 < min (c / 2) (intrinsicNormalMetricRadius n K) :=
    lt_min (half_pos hc) (intrinsicNormalMetricRadius_pos n K hK.le)
  unfold initialReducedVolumeLowerCoeff
  exact mul_pos
    (mul_pos (intrinsicBallVolumeCoeff_pos n)
      (lt_min
        (mul_pos (pow_pos hr n) (Real.rpow_pos_of_pos (by positivity) _))
        (Real.rpow_pos_of_pos (by positivity) _)))
    (Real.exp_pos _)

private theorem initialVolume_gaussian_sqrt_cancel (n : ℕ) (T : ℝ) (hT : 0 < T) :
    Real.sqrt T ^ n * (4 * Real.pi * T) ^ (-(n : ℝ) / 2) =
      (4 * Real.pi) ^ (-(n : ℝ) / 2) := by
  have hpow : T ^ ((n : ℝ) / 2) = Real.sqrt T ^ n := by
    rw [Real.rpow_div_two_eq_sqrt (n : ℝ) hT.le, Real.rpow_natCast]
  have hcancel : T ^ ((n : ℝ) / 2) * T ^ (-(n : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hT, show (n : ℝ) / 2 + -(n : ℝ) / 2 = 0 by ring,
      Real.rpow_zero]
  rw [Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) hT.le, ← hpow]
  calc
    T ^ ((n : ℝ) / 2) *
        ((4 * Real.pi) ^ (-(n : ℝ) / 2) * T ^ (-(n : ℝ) / 2)) =
        (4 * Real.pi) ^ (-(n : ℝ) / 2) *
          (T ^ ((n : ℝ) / 2) * T ^ (-(n : ℝ) / 2)) := by ring
    _ = (4 * Real.pi) ^ (-(n : ℝ) / 2) := by rw [hcancel, mul_one]

private theorem initialVolume_gaussian_floor
    (n : ℕ) (r₀ H T : ℝ) (hr₀ : 0 < r₀) (hT : 0 < T) (hTH : T ≤ H) :
    min (r₀ ^ n * (4 * Real.pi * H) ^ (-(n : ℝ) / 2))
        ((4 * Real.pi) ^ (-(n : ℝ) / 2)) ≤
      (min r₀ (Real.sqrt T)) ^ n * (4 * Real.pi * T) ^ (-(n : ℝ) / 2) := by
  have hG : (4 * Real.pi * H) ^ (-(n : ℝ) / 2) ≤
      (4 * Real.pi * T) ^ (-(n : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 4 * Real.pi * T)
      (mul_le_mul_of_nonneg_left hTH (by positivity))
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))
  by_cases hrT : r₀ ≤ Real.sqrt T
  · rw [min_eq_left hrT]
    exact (min_le_left _ _).trans
      (mul_le_mul_of_nonneg_left hG (pow_nonneg hr₀.le n))
  · rw [min_eq_right (le_of_not_ge hrT), initialVolume_gaussian_sqrt_cancel n T hT]
    exact min_le_right _ _

variable {E F M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace F] {I : ModelWithCorners ℝ E F} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace F M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem initial_reducedVolume_lower_connected
    (H K c : ℝ) (hH : 0 < H) (hK : 0 < K) (hc : 0 < c)
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hT : 0 < T) (hTH : T ≤ H)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hslab : Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : Ioc (0 : ℝ) T ⊆ D.regular)
    (hbounded : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B)
    (hinit : ∀ z : M,
      Real.sqrt (normSq0S (I := I) (S.base.metric 0) z 4 (S.base.rm04 0 z)) ≤ K)
    (hInj : ∀ p : M, ENNReal.ofReal c ≤
      intrinsicInjectivityRadiusOf (I := I) (S.base.metric 0) hcomplete p)
    (x : M) :
    ENNReal.ofReal (initialReducedVolumeLowerCoeff (Module.finrank ℝ E) H K c) ≤
      DifferentialGeometry.PDE.RicciFlow.redVolume S T x T := by
  let n := Module.finrank ℝ E
  let r₀ := min (c / 2) (intrinsicNormalMetricRadius n K)
  let C := compactCurvatureControlTime n K
  let δ := C / 2
  let Q := (n : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)
  let Λ := Real.exp (2 * Q * C)
  let Learly := Λ / 4 + Q * C / 3
  let Llate := (n : ℝ) / 2 + Λ * r₀ ^ 2 / (2 * δ) + Q * δ
  let L := max Learly Llate
  let omega := intrinsicBallVolumeCoeff n
  let m := min (r₀ ^ n * (4 * Real.pi * H) ^ (-(n : ℝ) / 2))
    ((4 * Real.pi) ^ (-(n : ℝ) / 2))
  have hr₀ : 0 < r₀ :=
    lt_min (half_pos hc) (intrinsicNormalMetricRadius_pos n K hK.le)
  have homega : 0 < omega := intrinsicBallVolumeCoeff_pos n
  have hm : 0 < m := lt_min
    (mul_pos (pow_pos hr₀ n) (Real.rpow_pos_of_pos (by positivity) _))
    (Real.rpow_pos_of_pos (by positivity) _)
  have hi : ∀ z : M,
      normSq0S (I := I) (S.base.metric 0) z 4 (S.base.rm04 0 z) ≤ K ^ 2 :=
    fun z ↦ (Real.sqrt_le_iff.mp (hinit z)).2
  have hfan : ∃ (q : M) (R : ℝ), 0 < R ∧ R ≤ r₀ ∧
      (∀ y : M, riemannianEDistOf (I := I) (S.base.metric 0) q y < ENNReal.ofReal R →
        redLength S T x y T ≤ L) ∧
      m ≤ R ^ n * (4 * Real.pi * T) ^ (-(n : ℝ) / 2) := by
    by_cases hsmall : T ≤ C
    · refine ⟨x, min r₀ (Real.sqrt T), lt_min hr₀ (Real.sqrt_pos.mpr hT),
        min_le_left _ _, ?_, initialVolume_gaussian_floor n r₀ H T hr₀ hT hTH⟩
      intro y hy
      have h : redLength S T x y T ≤ Learly :=
        redLength_initial_ball_early S hS T hT K hsmall hcomplete hslab
          (fun t ht ↦ hregular ⟨ht.1, ht.2.le⟩) hbounded hi x r₀ hr₀ y hy
      exact h.trans (le_max_left _ _)
    · obtain ⟨q, hq⟩ := exists_redLength_initial_ball_late S hS T K
        (le_of_not_ge hsmall) hcomplete hslab hregular hbounded hi x
      refine ⟨q, r₀, hr₀, le_rfl, ?_, ?_⟩
      · intro y hy
        exact (hq r₀ hr₀ y hy).trans (le_max_right _ _)
      · have hG : (4 * Real.pi * H) ^ (-(n : ℝ) / 2) ≤
            (4 * Real.pi * T) ^ (-(n : ℝ) / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 4 * Real.pi * T)
            (mul_le_mul_of_nonneg_left hTH (by positivity))
            (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))
        exact (min_le_left _ _).trans
          (mul_le_mul_of_nonneg_left hG (pow_nonneg hr₀.le n))
  obtain ⟨q, R, hR, hRr₀, hL, hfloor⟩ := hfan
  let U : Set M :=
    {y | riemannianEDistOf (I := I) (S.base.metric 0) q y < ENNReal.ofReal R}
  have hU : MeasurableSet U := by
    have hdist : Continuous (fun y : M ↦
        riemannianEDistOf (I := I) (S.base.metric 0) q y) := by
      simpa only [riemannianEDistOf] using continuous_riemannianEDist (S.base.metric 0) q
    exact (isOpen_lt hdist continuous_const).measurableSet
  have hball : ENNReal.ofReal (omega * R ^ n) ≤
      riemannianVolumeMeasure (I := I) (M := M) (S.base.metric 0) U := by
    let g := S.base.metric 0
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    let : T3Space M := inferInstance
    let : RiemannianBundle (fun p : M ↦ TangentSpace I p) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (fun p : M ↦ TangentSpace I p) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    let metricSpace : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    let : PseudoEMetricSpace M := metricSpace.toPseudoEMetricSpace
    let : @CompleteSpace M metricSpace.toUniformSpace := hcomplete.complete
    have hnorm : ∀ (p : M) (v : TangentSpace I p),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner p v v)) :=
      fun p v ↦ tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g p v
    have hRm : ∀ p : M,
        Real.sqrt (normSq0S (I := I) g p 4 (metricRm04At (I := I) g p)) ≤ K :=
      fun p ↦ hinit p
    have hInj' : ∀ p : M, ENNReal.ofReal c ≤ intrinsicInjRadius (I := I) g hnorm p := hInj
    have h := intrinsicBall_volume_ge_of_rm04_inj (I := I)
      K hK.le c hc g hnorm hRm hInj' q hR hRr₀
    simpa only [smallNormalBall, U, omega, n, g, riemannianEDistOf] using h
  have hset := redVolume_set_lower S T x T L hT hU hL
  have hset' : riemannianVolumeMeasure (I := I) (M := M) (S.base.metric 0) U *
      ENNReal.ofReal ((4 * Real.pi * T) ^ (-(n : ℝ) / 2) * Real.exp (-L)) ≤
        DifferentialGeometry.PDE.RicciFlow.redVolume S T x T := by
    simpa only [sub_self] using hset
  have hmass : omega * m ≤ (omega * R ^ n) * (4 * Real.pi * T) ^ (-(n : ℝ) / 2) := by
    nlinarith only [mul_le_mul_of_nonneg_left hfloor homega.le]
  have hGnonneg : 0 ≤ (4 * Real.pi * T) ^ (-(n : ℝ) / 2) :=
    (Real.rpow_pos_of_pos (by positivity) _).le
  change ENNReal.ofReal (omega * m * Real.exp (-L)) ≤ _
  calc
    ENNReal.ofReal (omega * m * Real.exp (-L)) =
        ENNReal.ofReal (omega * m) * ENNReal.ofReal (Real.exp (-L)) :=
      ENNReal.ofReal_mul (mul_nonneg homega.le hm.le)
    _ ≤ ENNReal.ofReal ((omega * R ^ n) * (4 * Real.pi * T) ^ (-(n : ℝ) / 2)) *
        ENNReal.ofReal (Real.exp (-L)) :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal hmass) _
    _ = ENNReal.ofReal (omega * R ^ n) *
        ENNReal.ofReal ((4 * Real.pi * T) ^ (-(n : ℝ) / 2) * Real.exp (-L)) := by
      rw [ENNReal.ofReal_mul (mul_nonneg homega.le (pow_nonneg hR.le n)),
        ENNReal.ofReal_mul hGnonneg, mul_assoc]
    _ ≤ riemannianVolumeMeasure (I := I) (M := M) (S.base.metric 0) U *
        ENNReal.ofReal ((4 * Real.pi * T) ^ (-(n : ℝ) / 2) * Real.exp (-L)) :=
      mul_le_mul_left hball _
    _ ≤ DifferentialGeometry.PDE.RicciFlow.redVolume S T x T := hset'

end DifferentialGeometry.PDE.RicciFlow

end
