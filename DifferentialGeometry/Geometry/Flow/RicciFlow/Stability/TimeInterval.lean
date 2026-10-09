import DifferentialGeometry.Geometry.Flow.RicciFlow.Stability.CauchyCriterion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Stability.Examples
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import DifferentialGeometry.Topology.Manifold.StereographicChart
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open DifferentialGeometry (SmoothRiemannianMetric)
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem localStabilityCauchyConclusion_of_limitFlowConclusion
    {L : ℕ → ℝ} {v : ℕ → ℝ} {hv : ∀ i, 0 < v i}
    {γ : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3))}
    {ℓ : (i : ℕ) → SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))}
    (h : localStabilityLimitFlowConclusion L v hv γ ℓ) :
    localStabilityCauchyConclusion L v hv γ ℓ := by
  obtain ⟨γLim, _h0, hlim⟩ := h
  intro A hA m hm ε hε
  obtain ⟨N, hN⟩ := hlim A hA m hm (ε / 2) (half_pos hε)
  refine ⟨N, fun i j hi hj r hr u hu => ?_⟩
  refine metricDerivNormSupOn_le_of_forall (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r))
    (Subtype.val ⁻¹' A) m _ _ _ ε hε.le (fun a ha x hx => ?_)
  have hr' : r ≤ min (L j) (L i) := by simpa only [min_comm] using hr
  have h1 := hN i j hi hj r hr u hu a ha x hx
  have h2 := hN j i hj hi r hr' u (by simpa only [min_comm] using hu) a ha x hx
  have hsymm := metricDerivNorm_symm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
    (((ℓ j).base.metric u).restrictOpenOfSubset
      (modelBall_mono (le_trans hr (min_le_right (L i) (L j)))))
    ((γLim u).restrictOpen (ModelBall r))
    ((γ.restrictOpen (ModelBall r))) x
  have htri := metricDerivNorm_triangle (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
    (((ℓ i).base.metric u).restrictOpenOfSubset
      (modelBall_mono (le_trans hr (min_le_left (L i) (L j)))))
    ((γLim u).restrictOpen (ModelBall r))
    (((ℓ j).base.metric u).restrictOpenOfSubset
      (modelBall_mono (le_trans hr (min_le_right (L i) (L j)))))
    ((γ.restrictOpen (ModelBall r))) x
  rw [hsymm] at h2
  linarith

private abbrev SphereShrinkAmbient := EuclideanSpace ℝ (Fin 4)

private abbrev SphereShrinkSpace := Metric.sphere (0 : SphereShrinkAmbient) 1

private local instance : Fact (Module.finrank ℝ SphereShrinkAmbient = 3 + 1) := ⟨by simp⟩

private def roundSphereShrinkScale (t : ℝ) : ℝ := if t < 1 / 4 then 1 - 4 * t else 3 / 4

private theorem roundSphereShrinkScale_pos (t : ℝ) : 0 < roundSphereShrinkScale t := by
  unfold roundSphereShrinkScale
  split_ifs with ht
  · linarith
  · norm_num

private noncomputable def roundSphereShrinkMetric (t : ℝ) :
    SmoothRiemannianMetric (𝓡 3) SphereShrinkSpace :=
  scaleMetric (roundSphereShrinkScale t) (roundSphereShrinkScale_pos t)
    (roundMetric (E := SphereShrinkAmbient) (n := 3))

private theorem roundSphereShrinkMetric_inner {t : ℝ} (ht : t < 1 / 4) (x : SphereShrinkSpace)
    (v w : TangentSpace (𝓡 3) x) :
    (roundSphereShrinkMetric t).inner x v w =
      (1 - 4 * t) * (roundMetric (E := SphereShrinkAmbient) (n := 3)).inner x v w := by
  rw [roundSphereShrinkMetric, scaleMetric_inner, roundSphereShrinkScale, ite_eq_left ht]

private theorem ricciTensor_roundSphereShrinkMetric (t : ℝ) (x : SphereShrinkSpace)
    (v w : TangentSpace (𝓡 3) x) :
    ricciTensor (roundSphereShrinkMetric t) x v w =
      2 * (roundMetric (E := SphereShrinkAmbient) (n := 3)).inner x v w := by
  rw [roundSphereShrinkMetric, ricciTensor_scaleMetric, roundMetric_ricciTensor]
  norm_num

private theorem roundSphereShrinkMetric_hasDerivAt {t : ℝ} (ht : t < 1 / 4)
    (x : SphereShrinkSpace)
    (v w : TangentSpace (𝓡 3) x) :
    HasDerivAt (fun s : ℝ => (roundSphereShrinkMetric s).inner x v w)
      (-2 * ricciTensor (roundSphereShrinkMetric t) x v w) t := by
  have hbase : HasDerivAt (fun s : ℝ => 1 - 4 * s) (-4) t := by
    have hraw : HasDerivAt ((fun _ : ℝ => (1 : ℝ)) - fun y : ℝ => 4 * y) (0 - 4 * 1) t :=
      (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub ((hasDerivAt_id t).const_mul 4)
    have hval : (0 : ℝ) - 4 * 1 = (-4 : ℝ) := by norm_num
    rw [hval] at hraw
    refine hraw.congr_of_eventuallyEq ?_
    filter_upwards with s
    simp only [Pi.sub_apply]
  have h : HasDerivAt
      (fun s : ℝ => (1 - 4 * s) * (roundMetric (E := SphereShrinkAmbient) (n := 3)).inner x v w)
      (-4 * (roundMetric (E := SphereShrinkAmbient) (n := 3)).inner x v w) t :=
    hbase.mul_const _
  rw [ricciTensor_roundSphereShrinkMetric]
  have htarget : (-2 : ℝ) * (2 * (roundMetric (E := SphereShrinkAmbient) (n := 3)).inner x v w) =
      -4 * (roundMetric (E := SphereShrinkAmbient) (n := 3)).inner x v w := by ring
  rw [htarget]
  exact h.congr_of_eventuallyEq (by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    exact roundSphereShrinkMetric_inner hs x v w)

private theorem roundSphereShrinkMetric_interpolate {t : ℝ} (ht : t < 1 / 4)
    (x : SphereShrinkSpace)
    (v w : TangentSpace (𝓡 3) x) :
    (roundSphereShrinkMetric t).inner x v w =
      (1 - 8 * t) * (roundMetric (E := SphereShrinkAmbient) (n := 3)).inner x v w +
        (8 * t) * (scaleMetric (1 / 2) (by norm_num)
          (roundMetric (E := SphereShrinkAmbient) (n := 3))).inner x v w := by
  rw [roundSphereShrinkMetric_inner ht, scaleMetric_inner]
  ring

private theorem roundSphereShrinkMetric_jointGram (x₀ : SphereShrinkSpace)
    (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
      (fun p : ℝ × SphereShrinkSpace =>
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (roundSphereShrinkMetric p.1) x₀ p.2 i j)
      (Ico 0 (1 / 4) ×ˢ
        (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet) := by
  let g₀ := roundMetric (E := SphereShrinkAmbient) (n := 3)
  let g₁ := scaleMetric (1 / 2) (by norm_num) g₀
  let U := (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet
  have hstatic (g : SmoothRiemannianMetric (𝓡 3) SphereShrinkSpace) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
        (fun p : ℝ × SphereShrinkSpace =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g x₀ p.2 i j)
        (Ico 0 (1 / 4) ×ˢ U) :=
    (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn g x₀ i j).comp
      contMDiffOn_snd (fun _ hp => hp.2)
  have ha : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
      (fun p : ℝ × SphereShrinkSpace => 1 - 8 * p.1) (Ico 0 (1 / 4) ×ˢ U) :=
    contMDiffOn_const.sub (contMDiffOn_const.mul contMDiffOn_fst)
  have hb : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
      (fun p : ℝ × SphereShrinkSpace => 8 * p.1) (Ico 0 (1 / 4) ×ˢ U) :=
    contMDiffOn_const.mul contMDiffOn_fst
  apply ((ha.mul (hstatic g₀)).add (hb.mul (hstatic g₁))).congr
  intro p hp
  dsimp only [Pi.mul_apply, Pi.add_apply]
  simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
  exact roundSphereShrinkMetric_interpolate hp.1.2 p.2 _ _

private def roundSphereShrinkSolutionOn :
    SolutionOn (I := 𝓡 3) (M := SphereShrinkSpace)
      (RealTimeInterval.closedOpen (0 : ℝ) (1 / 4) (by norm_num)) where
  base := { metric := roundSphereShrinkMetric }

private theorem roundSphereShrinkSolutionOn_isSolutionOn :
    IsSolutionOn (roundSphereShrinkSolutionOn) := by
  apply solutionOn_of_joint (by norm_num : (0 : ℝ) < 1 / 4) roundSphereShrinkMetric
    roundSphereShrinkMetric_jointGram
  intro t ht x v w
  exact (roundSphereShrinkMetric_hasDerivAt ht.2 x v w).hasDerivWithinAt

private noncomputable def counterSphereNorth : SphereShrinkSpace :=
  ⟨EuclideanSpace.single 0 (1 : ℝ), by simp⟩

private noncomputable def counterStereographic :
    (EuclideanSpace ℝ (Fin 3)) ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ↥(Topology.Manifold.stereographicImage counterSphereNorth) :=
  Topology.Manifold.stereographicDiffeomorph counterSphereNorth

private def counterShrinkInterval : RealTimeInterval :=
  RealTimeInterval.closedOpen (0 : ℝ) (1 / 4) (by norm_num)

private noncomputable def counterPunctureSolution :
    SolutionOn (I := 𝓡 3) (M := ↥(Topology.Manifold.stereographicImage counterSphereNorth))
      counterShrinkInterval := by
  haveI : SigmaCompactSpace ↥(Topology.Manifold.stereographicImage counterSphereNorth) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (isSigmaCompact_of_isOpen (𝓡 3)
        (Topology.Manifold.stereographicImage counterSphereNorth).isOpen)
  exact solutionOnRestrictOpen roundSphereShrinkSolutionOn
    (Topology.Manifold.stereographicImage counterSphereNorth)

private theorem counterPunctureSolution_isSolutionOn :
    IsSolutionOn counterPunctureSolution := by
  have : SigmaCompactSpace ↥(Topology.Manifold.stereographicImage counterSphereNorth) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (isSigmaCompact_of_isOpen (𝓡 3)
        (Topology.Manifold.stereographicImage counterSphereNorth).isOpen)
  exact isSolutionOn_restrictOpen roundSphereShrinkSolutionOn
    roundSphereShrinkSolutionOn_isSolutionOn
    (Topology.Manifold.stereographicImage counterSphereNorth)

private noncomputable def counterGlobalSolution :
    SolutionOn (I := 𝓡 3) (M := (EuclideanSpace ℝ (Fin 3))) counterShrinkInterval :=
  solutionOnPullback counterPunctureSolution counterStereographic

private theorem counterGlobalSolution_isSolutionOn : IsSolutionOn counterGlobalSolution :=
  isSolutionOn_pullback counterPunctureSolution counterPunctureSolution_isSolutionOn
    counterStereographic

private def counterBallRadius (i : ℕ) : ℝ := (i : ℝ) + 1

private theorem counterBallRadius_pos (i : ℕ) : 0 < counterBallRadius i := by
  simp only [counterBallRadius]
  positivity

private theorem tendsto_counterBallRadius : Tendsto counterBallRadius atTop atTop :=
  tendsto_atTop_mono (fun i => by simp only [counterBallRadius]; simp)
    tendsto_natCast_atTop_atTop

private def counterTime (_ : ℕ) : ℝ := 1 / 8

private theorem counterTime_pos (i : ℕ) : 0 < counterTime i := by norm_num [counterTime]

private theorem counterTime_le_half (i : ℕ) : counterTime i ≤ 1 / 2 := by norm_num [counterTime]

private theorem counterTime_eq (i : ℕ) : counterTime i = 1 / 8 := rfl

private def counterInterval (i : ℕ) : RealTimeInterval :=
  RealTimeInterval.closed (0 : ℝ) (counterTime i) (le_of_lt (counterTime_pos i))

private noncomputable def counterReferenceMetric : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3)) :=
  counterGlobalSolution.base.metric 0

private noncomputable def counterBallSolution (i : ℕ) :
    SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (counterBallRadius i)))
      (counterInterval i) := by
  haveI : SigmaCompactSpace ↥(ModelBall (counterBallRadius i)) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (isSigmaCompact_of_isOpen (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (ModelBall (counterBallRadius i)).isOpen)
  exact solutionOnRestrictOpen (counterGlobalSolution.timeRestrict (counterInterval i))
    (ModelBall (counterBallRadius i))

private theorem counterInterval_carrier_subset (i : ℕ) :
    (counterInterval i).carrier ⊆ counterShrinkInterval.carrier := by
  intro t ht
  simp only [counterInterval, counterShrinkInterval, RealTimeInterval.closed,
    RealTimeInterval.closedOpen] at ht ⊢
  refine ⟨ht.1, lt_of_le_of_lt ht.2 ?_⟩
  norm_num [counterTime]

private theorem counterInterval_regular_subset (i : ℕ) :
    (counterInterval i).regular ⊆ counterShrinkInterval.regular := by
  intro t ht
  simp only [counterInterval, counterShrinkInterval, RealTimeInterval.closed,
    RealTimeInterval.closedOpen] at ht ⊢
  refine ⟨ht.1, lt_of_lt_of_le ht.2 ?_⟩
  norm_num [counterTime]

private theorem counterBallSolution_isSolutionOn (i : ℕ) :
    IsSolutionOn (counterBallSolution i) := by
  have : SigmaCompactSpace ↥(ModelBall (counterBallRadius i)) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (isSigmaCompact_of_isOpen (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (ModelBall (counterBallRadius i)).isOpen)
  exact isSolutionOn_restrictOpen _
    (isSolutionOn_timeRestrict counterGlobalSolution_isSolutionOn
      (counterInterval_carrier_subset i) (counterInterval_regular_subset i))
    (ModelBall (counterBallRadius i))

private theorem exists_roundSphereShrink_curvatureBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1 / 16 : ℝ) (1 / 8), ∀ x : SphereShrinkSpace,
      Tensor0SBundle.normSq0S (I := 𝓡 3) (M := SphereShrinkSpace)
        (roundSphereShrinkSolutionOn.base.metric t) x 4
        (metricRm04At (I := 𝓡 3) (M := SphereShrinkSpace)
          (roundSphereShrinkSolutionOn.base.metric t) x) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_curvature_bound_on_closed_interval_of_isSolutionOn
    (a := 1 / 16) (b := 1 / 8) roundSphereShrinkSolutionOn
    roundSphereShrinkSolutionOn_isSolutionOn (by
      intro t ht
      exact ⟨lt_of_lt_of_le (by norm_num) ht.1, lt_of_le_of_lt ht.2 (by norm_num)⟩)
  exact ⟨C, hC, fun t ht x => by
    simpa only [SolutionOn.family_metric] using hbound t ht x⟩

private noncomputable def counterCurvatureConstant : ℝ :=
  Classical.choose exists_roundSphereShrink_curvatureBound + 2

private theorem counterCurvatureConstant_ge_bound :
    Classical.choose exists_roundSphereShrink_curvatureBound ≤ counterCurvatureConstant ^ 2 := by
  have hC : (0 : ℝ) ≤ Classical.choose exists_roundSphereShrink_curvatureBound :=
    (Classical.choose_spec exists_roundSphereShrink_curvatureBound).1
  simp only [counterCurvatureConstant]
  nlinarith

private theorem metricDerivNorm_roundSphereShrinkMetric (u : ℝ) (a : ℕ)
    (x : SphereShrinkSpace) :
    metricDerivNorm (I := 𝓡 3) a (roundSphereShrinkMetric u) (roundSphereShrinkMetric 0)
        (roundSphereShrinkMetric 0) x =
      (if a = 0 then |roundSphereShrinkScale u - 1| * Real.sqrt 3 else 0) := by
  have h0 : roundSphereShrinkMetric 0 = roundMetric (E := SphereShrinkAmbient) (n := 3) := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [roundSphereShrinkMetric, scaleMetric_inner,
      show roundSphereShrinkScale 0 = 1 from by norm_num [roundSphereShrinkScale], one_mul]
  rw [h0, roundSphereShrinkMetric,
    DifferentialGeometry.Geometry.Metric.metricDerivNorm_scaleMetric_self]
  simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]

private theorem counterBall_metricDerivNorm_val (i : ℕ) {u : ℝ} (hu : u < 1 / 4) (a : ℕ)
    (x : ↥(ModelBall (counterBallRadius i))) :
    metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) a ((counterBallSolution i).base.metric u)
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i)))
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i))) x =
      (if a = 0 then |1 - 4 * u - 1| * Real.sqrt 3 else 0) := by
  have : SigmaCompactSpace ↥(ModelBall (counterBallRadius i)) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (isSigmaCompact_of_isOpen (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (ModelBall (counterBallRadius i)).isOpen)
  have : SigmaCompactSpace ↥(Topology.Manifold.stereographicImage counterSphereNorth) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (isSigmaCompact_of_isOpen (𝓡 3)
        (Topology.Manifold.stereographicImage counterSphereNorth).isOpen)
  simp only [counterBallSolution, counterReferenceMetric, counterGlobalSolution,
    counterPunctureSolution, roundSphereShrinkSolutionOn, solutionOnRestrictOpen,
    solutionOnPullback, SolutionOn.timeRestrict_base]
  rw [metricDerivNorm_restrictOpen]
  rw [metricDerivNorm_pullback]
  rw [metricDerivNorm_restrictOpen]
  rw [metricDerivNorm_roundSphereShrinkMetric, roundSphereShrinkScale, ite_eq_left hu]

private theorem counterBall_curvature_le (i : ℕ) (x : ↥(ModelBall (counterBallRadius i))) :
    curvatureNormSq ((counterBallSolution i).base.metric (counterTime i)) x
      (metricRm04At (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (counterBallRadius i)))
        ((counterBallSolution i).base.metric (counterTime i)) x) ≤
      counterCurvatureConstant ^ 2 := by
  have : SigmaCompactSpace ↥(ModelBall (counterBallRadius i)) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (isSigmaCompact_of_isOpen (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (ModelBall (counterBallRadius i)).isOpen)
  refine le_trans ?_ counterCurvatureConstant_ge_bound
  simp only [curvatureNormSq, counterBallSolution, counterGlobalSolution,
    counterPunctureSolution, solutionOnRestrictOpen, solutionOnPullback,
    SolutionOn.timeRestrict_base, counterTime_eq]
  rw [DifferentialGeometry.Tensor0SBundle.normSq0S_restrictOpen_apply,
    DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.metricRm04At_restrictOpen]
  rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric, riemannNormSq_cross]
  rw [DifferentialGeometry.Tensor0SBundle.normSq0S_restrictOpen_apply,
    DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.metricRm04At_restrictOpen]
  exact (Classical.choose_spec exists_roundSphereShrink_curvatureBound).2 (1 / 8)
    ⟨by norm_num, le_rfl⟩ _

private theorem counterBall_metricDerivNorm_val_le_sqrt_three (i : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu8 : u ≤ 1 / 8) (a : ℕ)
    (x : ↥(ModelBall (counterBallRadius i))) :
    metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) a ((counterBallSolution i).base.metric u)
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i)))
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i))) x ≤
      Real.sqrt 3 := by
  rw [counterBall_metricDerivNorm_val i (by linarith) a x]
  split_ifs with ha0
  · have habs : |1 - 4 * u - 1| = 4 * u := by
      rw [show (1 : ℝ) - 4 * u - 1 = -(4 * u) from by ring, abs_neg,
        abs_of_nonneg (by positivity)]
    rw [habs]
    calc
      4 * u * Real.sqrt 3 = (4 * u) * Real.sqrt 3 := by ring
      _ ≤ 1 * Real.sqrt 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 := one_mul _
  · exact Real.sqrt_nonneg 3

private theorem counterBall_metricDerivNorm_bddAbove (i : ℕ) :
    BddAbove {r : ℝ | ∃ a : ℕ, a ≤ 4 ∧
      ∃ x ∈ Subtype.val ⁻¹' ({0} : Set (EuclideanSpace ℝ (Fin 3))),
      metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) a ((counterBallSolution i).base.metric (counterTime i))
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i)))
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i))) x = r} := by
  refine ⟨Real.sqrt 3, fun r hr => ?_⟩
  obtain ⟨a, _ha, x, _hx, rfl⟩ := hr
  exact counterBall_metricDerivNorm_val_le_sqrt_three i (le_of_lt (counterTime_pos i))
    (by norm_num [counterTime]) a x

private theorem counterBall_zero_mem (i : ℕ) :
    (0 : (EuclideanSpace ℝ (Fin 3))) ∈ ModelBall (counterBallRadius i) := by
  refine Metric.mem_ball.mpr ?_
  simpa using counterBallRadius_pos i

private theorem counterBall_zero_metricDerivNorm (i : ℕ)
    (x : ↥(ModelBall (counterBallRadius i))) :
    metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) 0
        ((counterBallSolution i).base.metric (counterTime i))
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i)))
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i))) x =
      Real.sqrt 3 / 2 := by
  rw [counterBall_metricDerivNorm_val i (by norm_num [counterTime]) 0 x, ite_eq_left rfl]
  have h1 : (1 : ℝ) - 4 * counterTime i - 1 = -(1 / 2) := by norm_num [counterTime]
  rw [h1, abs_neg]
  ring

private theorem counterSlabDerivativeBound :
    localStabilitySlabDerivativeBound counterBallRadius counterTime counterTime_pos
      counterReferenceMetric counterBallSolution := by
  intro A _hA m _hm
  refine ⟨Real.sqrt 3, Real.sqrt_nonneg 3, fun i u hu => ?_⟩
  refine Real.sSup_le (fun r hr => ?_) (Real.sqrt_nonneg 3)
  obtain ⟨a, _ha, x, _hx, rfl⟩ := hr
  exact counterBall_metricDerivNorm_val_le_sqrt_three i hu.1 (by
    have h := hu.2
    rwa [counterTime_eq i] at h) a x

private theorem counterTimeLowerBound :
    ∀ᶠ i in atTop, ∃ u ∈ Set.Icc (0 : ℝ) (counterTime i),
      Real.sqrt 3 / 2 ≤ metricDerivNormSupOn
        (Subtype.val ⁻¹' ({0} : Set (EuclideanSpace ℝ (Fin 3)))) 4 ((counterBallSolution i).base.metric u)
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i)))
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i))) := by
  filter_upwards with i
  refine ⟨counterTime i, ⟨le_of_lt (counterTime_pos i), le_rfl⟩, ?_⟩
  refine le_csSup (counterBall_metricDerivNorm_bddAbove i)
    ⟨0, by norm_num, ⟨0, counterBall_zero_mem i⟩, ?_, ?_⟩
  · rfl
  · exact counterBall_zero_metricDerivNorm i _

private theorem counterCurvatureConstant_pos : 0 < counterCurvatureConstant := by
  have hC : (0 : ℝ) ≤ Classical.choose exists_roundSphereShrink_curvatureBound :=
    (Classical.choose_spec exists_roundSphereShrink_curvatureBound).1
  simp only [counterCurvatureConstant]
  linarith


private noncomputable def counterLimitMetric (u : ℝ) :
    SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3)) :=
  counterGlobalSolution.base.metric u

private theorem restrictOpenOfSubset_restrictOpen_eq
    (g : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3)))
    (U V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3))) (hVU : V ≤ U) :
    (g.restrictOpen U).restrictOpenOfSubset hVU = g.restrictOpen V := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

private theorem counterInitialJetHypothesis :
    localStabilityInitialJetHypothesis counterBallRadius counterTime counterTime_pos
      counterReferenceMetric counterBallSolution := by
  intro A _hA p
  have hzero : ∀ i : ℕ,
      metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (counterBallRadius i)))
        (Subtype.val ⁻¹' A) p ((counterBallSolution i).base.metric 0)
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i)))
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i))) = 0 := by
    intro i
    simp only [counterBallSolution, counterReferenceMetric, solutionOnRestrictOpen,
      SolutionOn.timeRestrict_base]
    exact metricDerivNormSupOn_self (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))))
      (M := ↥(ModelBall (counterBallRadius i))) (Subtype.val ⁻¹' A) p _ _
  rw [show (fun i : ℕ => metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))))
        (M := ↥(ModelBall (counterBallRadius i))) (Subtype.val ⁻¹' A) p
        ((counterBallSolution i).base.metric 0)
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i)))
        (counterReferenceMetric.restrictOpen (ModelBall (counterBallRadius i))))
      = fun _ : ℕ => (0 : ℝ) from funext hzero]
  exact tendsto_const_nhds

private theorem counterBallSolution_cauchyConclusion :
    localStabilityCauchyConclusion counterBallRadius counterTime counterTime_pos
      counterReferenceMetric counterBallSolution := by
  intro A _hA m _hm ε hε
  refine ⟨0, fun i j _ _ r hr u _hu => ?_⟩
  have hzero : metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r))
      (Subtype.val ⁻¹' A) m
      (((counterBallSolution i).base.metric u).restrictOpenOfSubset
        (modelBall_mono
          (le_trans hr (min_le_left (counterBallRadius i) (counterBallRadius j)))))
      (((counterBallSolution j).base.metric u).restrictOpenOfSubset
        (modelBall_mono
          (le_trans hr (min_le_right (counterBallRadius i) (counterBallRadius j)))))
      ((counterReferenceMetric.restrictOpen (ModelBall r))) = 0 := by
    simp only [counterBallSolution, counterReferenceMetric, solutionOnRestrictOpen,
      SolutionOn.timeRestrict_base]
    rw [restrictOpenOfSubset_restrictOpen_eq, restrictOpenOfSubset_restrictOpen_eq]
    exact metricDerivNormSupOn_self (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r))
      (Subtype.val ⁻¹' A) m _ _
  rw [hzero]
  exact hε.le

private theorem counterBallSolution_limitFlowConclusion :
    localStabilityLimitFlowConclusion counterBallRadius counterTime counterTime_pos
      counterReferenceMetric counterBallSolution := by
  refine ⟨counterLimitMetric, rfl, ?_⟩
  intro A _hA m _hm ε hε
  refine ⟨0, fun i j _ _ r hr u _hu a _ha x _hx => ?_⟩
  have hzero : metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
      (((counterBallSolution i).base.metric u).restrictOpenOfSubset
        (modelBall_mono
          (le_trans hr (min_le_left (counterBallRadius i) (counterBallRadius j)))))
      ((counterLimitMetric u).restrictOpen (ModelBall r))
      ((counterReferenceMetric.restrictOpen (ModelBall r))) x = 0 := by
    simp only [counterBallSolution, counterReferenceMetric, counterLimitMetric,
      solutionOnRestrictOpen, SolutionOn.timeRestrict_base]
    rw [restrictOpenOfSubset_restrictOpen_eq]
    exact metricDerivNorm_self (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a _ _ x
  rw [hzero]
  exact hε.le

private theorem not_tendsto_zero_of_eventually_ge {w : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ i in atTop, c ≤ w i) : ¬ Tendsto w atTop (𝓝 0) := by
  intro ht
  have hlt : ∀ᶠ i in atTop, w i < c := ht.eventually (Iio_mem_nhds hc)
  obtain ⟨i, h1, h2⟩ := (h.and hlt).exists
  exact absurd h1 (not_le.mpr h2)

private theorem counterBallSolution_not_conclusion :
    ¬ localStabilityConclusion counterBallRadius counterTime counterTime_pos
      counterReferenceMetric counterBallSolution := by
  intro h
  have htend := h ({0} : Set (EuclideanSpace ℝ (Fin 3))) isCompact_singleton 4 (by norm_num)
  refine not_tendsto_zero_of_eventually_ge (c := Real.sqrt 3 / 2) (by positivity) ?_ htend
  filter_upwards [counterTimeLowerBound] with i hi
  obtain ⟨u, hu, hle⟩ := hi
  exact hle.trans (le_csSup
    (bddAbove_localStabilityIccValues counterSlabDerivativeBound ({0} : Set (EuclideanSpace ℝ (Fin 3)))
      isCompact_singleton 4 (by norm_num) i) ⟨u, hu, rfl⟩)

theorem exists_localStabilityRepair_witness :
    ∃ (θ K : ℝ), 0 < θ ∧ θ < 1 ∧ 0 < K ∧
      ∃ L : ℕ → ℝ, (∀ i, 0 < L i) ∧ Tendsto L atTop atTop ∧
        ∃ (v : ℕ → ℝ) (hv : ∀ i, 0 < v i), (∀ i, v i ≤ θ) ∧
          ∃ γ : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3)),
            ∃ ℓ : (i : ℕ) → SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
              (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i))),
              (∀ i, IsSolutionOn (ℓ i)) ∧
              (∀ i, ∀ x : ↥(ModelBall (L i)),
                curvatureNormSq ((ℓ i).base.metric (v i)) x
                  (metricRm04At (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
                    ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) ∧
              localStabilityInitialJetHypothesis L v hv γ ℓ ∧
              localStabilityCauchyConclusion L v hv γ ℓ ∧
              localStabilityLimitFlowConclusion L v hv γ ℓ ∧
              ¬ localStabilityConclusion L v hv γ ℓ :=
  ⟨1 / 2, counterCurvatureConstant, by norm_num, by norm_num, counterCurvatureConstant_pos,
    counterBallRadius, counterBallRadius_pos, tendsto_counterBallRadius,
    counterTime, counterTime_pos, counterTime_le_half,
    counterReferenceMetric, counterBallSolution, counterBallSolution_isSolutionOn,
    counterBall_curvature_le, counterInitialJetHypothesis, counterBallSolution_cauchyConclusion,
    counterBallSolution_limitFlowConclusion, counterBallSolution_not_conclusion⟩

theorem localStabilityCauchyConclusion_of_staticJetLimit
    {L : ℕ → ℝ} {v : ℕ → ℝ} {hv : ∀ i, 0 < v i}
    {γ : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3))}
    {ℓ : (i : ℕ) → SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))}
    (h : ∀ A : Set (EuclideanSpace ℝ (Fin 3)), IsCompact A → ∀ m : ℕ, 4 ≤ m → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ i : ℕ, N ≤ i → ∀ r : ℝ, ∀ hr : r ≤ L i,
        ∀ u ∈ Set.Icc (0 : ℝ) (v i), ∀ a : ℕ, a ≤ m →
          ∀ x : ↥(ModelBall r), (x : (EuclideanSpace ℝ (Fin 3))) ∈ A →
            metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
              (((ℓ i).base.metric u).restrictOpenOfSubset
                (modelBall_mono hr))
              ((γ.restrictOpen (ModelBall r)))
              ((γ.restrictOpen (ModelBall r))) x ≤ ε) :
    localStabilityCauchyConclusion L v hv γ ℓ := by
  intro A hA m hm ε hε
  obtain ⟨N, hN⟩ := h A hA m hm (ε / 2) (half_pos hε)
  refine ⟨N, fun i j hi hj r hr u hu => ?_⟩
  have hri : r ≤ L i := le_trans hr (min_le_left (L i) (L j))
  have hrj : r ≤ L j := le_trans hr (min_le_right (L i) (L j))
  have hui : u ∈ Set.Icc (0 : ℝ) (v i) := ⟨hu.1, hu.2.trans (min_le_left (v i) (v j))⟩
  have huj : u ∈ Set.Icc (0 : ℝ) (v j) := ⟨hu.1, hu.2.trans (min_le_right (v i) (v j))⟩
  refine metricDerivNormSupOn_le_of_forall (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r))
    (Subtype.val ⁻¹' A) m _ _ _ ε hε.le (fun a ha x hx => ?_)
  have h1 := hN i hi r hri u hui a ha x hx
  have h2 := hN j hj r hrj u huj a ha x hx
  have hsymm := metricDerivNorm_symm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
    (((ℓ j).base.metric u).restrictOpenOfSubset (modelBall_mono hrj))
    ((γ.restrictOpen (ModelBall r))) ((γ.restrictOpen (ModelBall r))) x
  have htri := metricDerivNorm_triangle (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
    (((ℓ i).base.metric u).restrictOpenOfSubset (modelBall_mono hri))
    ((γ.restrictOpen (ModelBall r)))
    (((ℓ j).base.metric u).restrictOpenOfSubset (modelBall_mono hrj))
    ((γ.restrictOpen (ModelBall r))) x
  rw [hsymm] at h2
  linarith

abbrev IsLocalStabilityCauchyInput : Prop := isLocalStabilityInput

def IsLocalStabilityLimitFlowInput : Prop :=
  ∀ (θ : ℝ), 0 < θ → θ < 1 → ∀ (K : ℝ), 0 < K →
    ∀ (L : ℕ → ℝ) (_hLpos : ∀ i, 0 < L i) (_hLtop : Tendsto L atTop atTop)
      (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (_hvθ : ∀ i, v i ≤ θ)
      (γ : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3)))
      (ℓ : (i : ℕ) → SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
        (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))),
      (∀ i, IsSolutionOn (ℓ i)) →
      (∀ i, ∀ x : ↥(ModelBall (L i)),
        curvatureNormSq ((ℓ i).base.metric (v i)) x
          (metricRm04At (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
            ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) →
      localStabilityInitialJetHypothesis L v hv γ ℓ →
      localStabilityLimitFlowConclusion L v hv γ ℓ

theorem isLocalStabilityCauchyInput_of_limitFlowInput
    (h : IsLocalStabilityLimitFlowInput) : IsLocalStabilityCauchyInput :=
  fun _θ _hθ _hθ1 _K _hK _L _hLpos _hLtop _v _hv _hvθ _γ _ℓ _h1 _h2 _h3 =>
    localStabilityCauchyConclusion_of_limitFlowConclusion
      (h _θ _hθ _hθ1 _K _hK _L _hLpos _hLtop _v _hv _hvθ _γ _ℓ _h1 _h2 _h3)

private theorem flatBallScaledMetric_restrictOpen_eq (L r c : ℝ) (hc : 0 < c) (hr : r ≤ L) :
    (flatBallScaledMetric L c hc).restrictOpenOfSubset (modelBall_mono hr) =
      flatBallScaledMetric r c hc := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

private theorem shortScaledBall_cauchyConclusion :
    localStabilityCauchyConclusion flatBallRadius shortEuclideanBallTime
      shortEuclideanBallTime_pos (euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))) shortScaledBallSolution := by
  intro A _hA m _hm ε hε
  have hev : ∀ᶠ i in atTop,
      |flatBallRescale i - 1| * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) < ε / 2 :=
    tendsto_flatBallScaledFactor.eventually (Iio_mem_nhds (half_pos hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun i j hi hj r hr u _hu => ?_⟩
  have hri : r ≤ flatBallRadius i := le_trans hr (min_le_left _ _)
  have hrj : r ≤ flatBallRadius j := le_trans hr (min_le_right _ _)
  refine metricDerivNormSupOn_le_of_forall (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r))
    (Subtype.val ⁻¹' A) m _ _ _ ε hε.le (fun a _ha x _hx => ?_)
  change metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
    (flatBallScaledMetric r (flatBallRescale i) (flatBallRescale_pos i))
    (flatBallScaledMetric r (flatBallRescale j) (flatBallRescale_pos j))
    (flatBallMetric r) x ≤ ε
  have h1 : metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
      (flatBallScaledMetric r (flatBallRescale i) (flatBallRescale_pos i))
      (flatBallMetric r) (flatBallMetric r) x ≤ ε / 2 :=
    (metricDerivNorm_flatBallScaledMetric_le r (flatBallRescale i) (flatBallRescale_pos i)
      a x).trans (le_of_lt (hN i hi))
  have h2 : metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
      (flatBallMetric r)
      (flatBallScaledMetric r (flatBallRescale j) (flatBallRescale_pos j))
      (flatBallMetric r) x ≤ ε / 2 := by
    rw [← metricDerivNorm_symm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
      (flatBallScaledMetric r (flatBallRescale j) (flatBallRescale_pos j))
      (flatBallMetric r) (flatBallMetric r) x]
    exact (metricDerivNorm_flatBallScaledMetric_le r (flatBallRescale j)
      (flatBallRescale_pos j) a x).trans (le_of_lt (hN j hj))
  have htri := metricDerivNorm_triangle (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
    (flatBallScaledMetric r (flatBallRescale i) (flatBallRescale_pos i))
    (flatBallMetric r)
    (flatBallScaledMetric r (flatBallRescale j) (flatBallRescale_pos j))
    (flatBallMetric r) x
  linarith

private theorem shortScaledBall_limitFlowConclusion :
    localStabilityLimitFlowConclusion flatBallRadius shortEuclideanBallTime
      shortEuclideanBallTime_pos (euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))) shortScaledBallSolution := by
  refine ⟨fun _ => euclideanMetric (E := (EuclideanSpace ℝ (Fin 3))), rfl, ?_⟩
  intro A _hA m _hm ε hε
  have hev : ∀ᶠ i in atTop,
      |flatBallRescale i - 1| * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) < ε :=
    tendsto_flatBallScaledFactor.eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun i j hi _hj r hr u _hu a _ha x _hx => ?_⟩
  change metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
    (flatBallScaledMetric r (flatBallRescale i) (flatBallRescale_pos i))
    (flatBallMetric r) (flatBallMetric r) x ≤ ε
  exact (metricDerivNorm_flatBallScaledMetric_le r (flatBallRescale i) (flatBallRescale_pos i)
    a x).trans (le_of_lt (hN i hi))

private theorem constantBall_cauchyConclusion :
    localStabilityCauchyConclusion flatBallRadius flatBallTime flatBallTime_pos
      (euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))) constantBallSolution := by
  intro A _hA m _hm ε hε
  refine ⟨0, fun i j _ _ r hr u _hu => ?_⟩
  have hri : r ≤ flatBallRadius i := le_trans hr (min_le_left _ _)
  have hrj : r ≤ flatBallRadius j := le_trans hr (min_le_right _ _)
  rw [constantBallSolution_base_metric, constantBallSolution_base_metric, flatBallMetric,
    flatBallMetric, restrictOpenOfSubset_restrictOpen_eq, restrictOpenOfSubset_restrictOpen_eq,
    metricDerivNormSupOn_self]
  exact hε.le

private theorem constantBall_limitFlowConclusion :
    localStabilityLimitFlowConclusion flatBallRadius flatBallTime flatBallTime_pos
      (euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))) constantBallSolution := by
  refine ⟨fun _ => euclideanMetric (E := (EuclideanSpace ℝ (Fin 3))), rfl, ?_⟩
  intro A _hA m _hm ε hε
  refine ⟨0, fun i _hi j _hj r _hr u _hu a _ha x _hx => ?_⟩
  rw [constantBallSolution_base_metric, flatBallMetric, restrictOpenOfSubset_restrictOpen_eq,
    metricDerivNorm_self]
  exact hε.le

theorem localStabilityRepair_holds_on_knownWitnesses :
    localStabilityCauchyConclusion flatBallRadius flatBallTime flatBallTime_pos
        (euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))) constantBallSolution ∧
      localStabilityLimitFlowConclusion flatBallRadius flatBallTime flatBallTime_pos
        (euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))) constantBallSolution ∧
      localStabilityCauchyConclusion flatBallRadius shortEuclideanBallTime
        shortEuclideanBallTime_pos (euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))) shortScaledBallSolution ∧
      localStabilityLimitFlowConclusion flatBallRadius shortEuclideanBallTime
        shortEuclideanBallTime_pos (euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))) shortScaledBallSolution :=
  ⟨constantBall_cauchyConclusion, constantBall_limitFlowConclusion,
    shortScaledBall_cauchyConclusion, shortScaledBall_limitFlowConclusion⟩

theorem not_isLocalStabilityVanishingInput_of_roundSphereShrink :
    ¬ IsLocalStabilityVanishingInput := by
  intro h
  obtain ⟨θ, K, hθ, hθ1, hK, L, hLpos, hLtop, v, hv, hvθ, γ, ℓ, hsol, hcurv, hjet,
    _hcauchy, _hlimit, hnot⟩ := exists_localStabilityRepair_witness
  exact hnot (h θ hθ hθ1 K hK L hLpos hLtop v hv hvθ γ ℓ hsol hcurv hjet)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
