import DifferentialGeometry.Geometry.Exponential.IntrinsicMetricBounds
import DifferentialGeometry.Geometry.Measure.ParametricLower
import DifferentialGeometry.Geometry.Comparison.InjectivityRadius.Intrinsic
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChart
import DifferentialGeometry.Geometry.Comparison.Convexity.Geodesic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

def intrinsicBallVolumeCoeff (n : ℕ) : ℝ :=
  Real.sqrt ((1 / 2 : ℝ) ^ n) *
    (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))

theorem intrinsicBallVolumeCoeff_pos (n : ℕ) : 0 < intrinsicBallVolumeCoeff n := by
  unfold intrinsicBallVolumeCoeff
  exact mul_pos (Real.sqrt_pos.mpr (pow_pos (by norm_num) _))
    (div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _)
      (Real.Gamma_pos_of_pos (by positivity)))

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrinsicBallChart_of_rm04_inj
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (K : ℝ) (hK : 0 ≤ K) (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hRm : ∀ x : M,
      Real.sqrt (normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) ≤ K)
    (hInj : ∀ p : M, ENNReal.ofReal c ≤ intrinsicInjRadius (I := I) g hEnorm p)
    (p : M) {r : ℝ} (hr : 0 < r)
    (hradius : r ≤ min (c / 2) (intrinsicNormalMetricRadius (Module.finrank ℝ E) K)) :
    Nonempty (IntrinsicBallChart (I := I) g hEnorm p r) := by
  have hrmetric : r ≤ intrinsicNormalMetricRadius (Module.finrank ℝ E) K :=
    hradius.trans (min_le_right _ _)
  have hrc : r < c :=
    (hradius.trans (min_le_left _ _)).trans_lt (half_lt_self hc)
  have hinj : InjOn (intrinsicFramedExp (I := I) g hEnorm p)
      (Metric.ball (0 : E) r) :=
    intrinsicInjOn_ball (I := I) g hEnorm p
      (((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr.le).mpr hrc).trans_le (hInj p))
  have hbranch : ∀ z ∈ Metric.ball (0 : E) r,
      ∃ B : ExponentialInverseBranch (I := I) g hEnorm p,
        (normalFrame (I := I) g p z : E) ∈ B.hom.source := by
    intro z hz
    have hzmetric : z ∈ Metric.ball (0 : E)
        (intrinsicNormalMetricRadius (Module.finrank ℝ E) K) :=
      Metric.ball_subset_ball hrmetric hz
    have hlower : ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
        intrinsicFrameMetric (I := I) g hEnorm p z v v :=
      fun v ↦ (intrFrameMetric_bound_of_rm04 K hK g hEnorm hRm p hzmetric v).1
    have hnot := intrinsicFrame_not_conj (I := I) g hEnorm p z
      (by norm_num : (0 : ℝ) < 1 / 2) hlower
    exact branch_of_not_conj (I := I) g hEnorm hnot
  exact exists_intrinsic_ball_chart (I := I) g hEnorm p
    (intrinsicFrame_localOn (I := I) g hEnorm p (Metric.ball (0 : E) r) hbranch) hinj

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrinsicBall_volume_ge_of_rm04_inj
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (K : ℝ) (hK : 0 ≤ K) (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hRm : ∀ x : M,
      Real.sqrt (normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) ≤ K)
    (hInj : ∀ p : M, ENNReal.ofReal c ≤ intrinsicInjRadius (I := I) g hEnorm p)
    (p : M) {r : ℝ} (hr : 0 < r)
    (hradius : r ≤ min (c / 2) (intrinsicNormalMetricRadius (Module.finrank ℝ E) K)) :
    ENNReal.ofReal (intrinsicBallVolumeCoeff (Module.finrank ℝ E) * r ^ Module.finrank ℝ E) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (smallNormalBall (I := I) p r) := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (R := ℝ) (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  obtain ⟨C⟩ := intrinsicBallChart_of_rm04_inj K hK c hc g hEnorm hRm hInj p hr hradius
  let Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
    { toPartialEquiv := C.hom.toPartialEquiv
      open_source := C.hom.open_source
      open_target := C.hom.open_target
      contMDiffOn_toFun := C.hom.contMDiffOn_toFun.of_le (by simp)
      contMDiffOn_invFun := C.hom.contMDiffOn_invFun.of_le (by simp) }
  have hsource : Metric.ball (0 : E) r ⊆ Ψ.source := by
    change Metric.ball (0 : E) r ⊆ C.hom.source
    rw [C.source_eq]
  have hhalf : ∀ z ∈ Metric.ball (0 : E) r, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ g.inner (Ψ z)
        (mfderiv 𝓘(ℝ, E) I Ψ z v) (mfderiv 𝓘(ℝ, E) I Ψ z v) := by
    intro z hz v
    have hev : (Ψ : E → M) =ᶠ[nhds z] intrinsicFramedExp (I := I) g hEnorm p :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz)
        (fun q hq ↦ C.hom_eq hq)
    have hD := Filter.EventuallyEq.mfderiv_eq
      (I := 𝓘(ℝ, E)) (I' := I) hev
    have hpoint : (Ψ.toPartialEquiv z : M) =
        intrinsicFramedExp (I := I) g hEnorm p z := by
      change C.hom z = intrinsicFramedExp (I := I) g hEnorm p z
      exact C.hom_eq hz
    rw [show Ψ z = intrinsicFramedExp (I := I) g hEnorm p z from C.hom_eq hz,
      hD, hpoint]
    have hcast :
        (tangentSpaceCast I (intrinsicFramedExp (I := I) g hEnorm p z)
            (intrinsicFramedExp (I := I) g hEnorm p z) :
          TangentSpace I (intrinsicFramedExp (I := I) g hEnorm p z) →L[ℝ]
            TangentSpace I (intrinsicFramedExp (I := I) g hEnorm p z)) =
        ContinuousLinearMap.id ℝ _ := by
      apply ContinuousLinearMap.ext
      intro w
      rfl
    rw [hcast]
    have hzmetric : z ∈ Metric.ball (0 : E)
        (intrinsicNormalMetricRadius (Module.finrank ℝ E) K) :=
      Metric.ball_subset_ball (hradius.trans (min_le_right _ _)) hz
    simpa only [intrinsicFrameMetric_apply, ContinuousLinearMap.id_comp] using
      (intrFrameMetric_bound_of_rm04 K hK g hEnorm hRm p hzmetric v).1
  have himage := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_ge_of_inner_half
    g Ψ measurableSet_ball hsource hhalf
  have hsub : Ψ '' Metric.ball (0 : E) r ⊆ smallNormalBall (I := I) p r := by
    rintro y ⟨z, hz, rfl⟩
    change C.hom z ∈ smallNormalBall (I := I) p r
    rw [C.hom_eq hz, intrinsicFrame_apply]
    apply smallNormalBall_radial_confined (I := I) g hEnorm p
    · simpa only [normalFrame_sqrt, Metric.mem_ball, dist_zero_right] using hz
    · exact ⟨zero_le_one, le_rfl⟩
  have hfactor :
      ENNReal.ofReal (intrinsicBallVolumeCoeff (Module.finrank ℝ E) * r ^ Module.finrank ℝ E) =
        ENNReal.ofReal (Real.sqrt ((1 / 2 : ℝ) ^ Module.finrank ℝ E)) *
          (volume : Measure E) (Metric.ball (0 : E) r) := by
    rw [ENNReal.ofReal_mul (intrinsicBallVolumeCoeff_pos _).le,
      ENNReal.ofReal_pow hr.le, intrinsicBallVolumeCoeff,
      ENNReal.ofReal_mul (Real.sqrt_nonneg _), InnerProductSpace.volume_ball]
    ac_rfl
  rw [hfactor]
  exact himage.trans (measure_mono hsub)

end DifferentialGeometry.Geometry.Riemannian

end
