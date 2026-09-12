import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SeedFlowCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SeedFlatLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.FlatNoncollapsedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedBallVolumeConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance seedVolumeTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance seedVolumeCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance seedVolumeSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance seedVolumeC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance seedVolumeT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance seedVolumeSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance seedVolumeTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
private local instance seedVolumeMeasurable {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : MeasurableSpace F.M := borel F.M
private local instance seedVolumeBorel {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : BorelSpace F.M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem not_seed_unit_volume_with_base_scalar_tendsto_zero
    (hdim : Module.finrank ℝ E = 3)
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) (hD : X.D = ancientTimeInterval)
    {kappa : ℝ} (hK : ∀ i, KLim (I := I) kappa (X.term i))
    (hvolume : ∀ i, seedTerminalUnitVolume (X.term i) = euclideanUnitBallVolume 3 / 2)
    (hbase : Tendsto (fun i => (X.term i).S.scalar 0 (X.term i).basepoint)
      atTop (𝓝 0)) : False := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨L, phi, hphi, Phi, hconnected, hcomplete, hconv⟩ :=
    exists_seedFlow_ancient_limit X hD hK hdim hvolume
  let _ : ConnectedSpace L.M := hconnected
  obtain ⟨_hscalarZero, hflat, hNC⟩ :=
    flat_noncollapsed_of_pointed_klim_limit_base_tendsto_zero X L Phi hdim hD hK
      hphi hbase hconnected hcomplete (fun t ht => by
        obtain ⟨Ct, hct, _href⟩ := hconv t ht
        exact ⟨Ct, hct⟩)
  have ht0 : (0 : ℝ) ∈ X.D.carrier := by
    rw [hD]
    exact (le_rfl : (0 : ℝ) ≤ 0)
  obtain ⟨C0, hc0, _hr0⟩ := hconv 0 ht0
  have hg : RiemannianMetricComplete (I := I) (L.S.base.metric 0) :=
    ⟨MetricComplete.complete (I := I) (L.atTime (I := I) 0) (hcomplete 0 ht0)⟩
  have hEuclidean : seedTerminalUnitVolume L = euclideanUnitBallVolume 3 := by
    let time0 : X.D.FlowTime := ⟨0, ht0⟩
    let B : FlowMetricBall L.S time0 := ⟨L.basepoint, 1, zero_lt_one⟩
    have h := flowMetricBall_volume_eq_euclidean_of_flat_noncollapsed
      (I := I) L.S time0 hg (fun y => hflat 0 ht0 y)
      (hK 0).kappa_pos (hNC time0) B
    change seedTerminalUnitVolume L = euclideanUnitBallVolume (Module.finrank ℝ E) *
      ENNReal.ofReal ((1 : ℝ) ^ Module.finrank ℝ E) at h
    simpa only [hdim, one_pow, ENNReal.ofReal_one, mul_one] using h
  have hsourceComplete : SeqMetricComplete (I := I) (X.atZero (I := I)) :=
    ⟨fun i => (hK i).complete 0 ht0⟩
  have hRic : ∀ i : ℕ, RicciBoundedBelow (I := I) ((X.term i).S.base.metric 0) 0 := by
    intro i z v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) ((X.term i).S.base.metric 0) z).mpr
    intro n c u w
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      (hK i).nonnegativeCurvatureOperator 0 ht0 z n c u w
  have hHalf : seedTerminalUnitVolume L = euclideanUnitBallVolume 3 / 2 := by
    exact pointed_ball_volume_eq_of_eventually_eq C0 hc0 (hcomplete 0 ht0)
      hsourceComplete (fun i => (hK i).connected) hRic zero_lt_one
      (euclideanUnitBallVolume 3 / 2) (Eventually.of_forall fun k => hvolume (phi k))
  have hbad : euclideanUnitBallVolume 3 = euclideanUnitBallVolume 3 / 2 :=
    hEuclidean.symm.trans hHalf
  have hreal := congrArg ENNReal.toReal hbad
  rw [ENNReal.toReal_div, ENNReal.toReal_ofNat] at hreal
  have hpos : 0 < (euclideanUnitBallVolume 3).toReal :=
    ENNReal.toReal_pos (euclideanUnitBallVolume_pos 3).ne' (euclideanUnitBallVolume_ne_top 3)
  linarith

theorem exists_normalized_klim_seed_volume
    (hdim : Module.finrank ℝ E = 3) (kappa : ℝ) :
    ∃ v : ℝ, 0 < v ∧
      ∀ F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval,
        KLim (I := I) kappa F → F.S.scalar 0 F.basepoint = 1 →
          ENNReal.ofReal v ≤ seedTerminalUnitVolume F := by
  classical
  by_contra hfailure
  push Not at hfailure
  let epsilon : ℕ → ℝ := fun i => 1 / (i + 1 : ℝ)
  have hepsilon : ∀ i, 0 < epsilon i := fun i => by dsimp only [epsilon]; positivity
  have hcounter := fun i : ℕ => hfailure (epsilon i) (hepsilon i)
  choose F hK hbase hvolume using hcounter
  let X : PointedFlowSeq.{u, uE, uH} (I := I) :=
    { D := ancientTimeInterval, term := F }
  have heps : Tendsto epsilon atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hepsENN : Tendsto (fun i => ENNReal.ofReal (epsilon i)) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp heps
  have hcollapse : Tendsto (fun i => seedTerminalUnitVolume (X.term i)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hepsENN
      (fun _ => bot_le) (fun i => (hvolume i).le)
  obtain ⟨N, delta, hdelta, _hsmall, _hdlim, _hhalf, hY, _hYscalar, hYbase, hYvolume⟩ :=
    exists_seedNormalizedSequence X hdim hK hbase hcollapse
  exact not_seed_unit_volume_with_base_scalar_tendsto_zero hdim
    (seedRescaledFlowSeq (seedFlowTail X N) (fun i => hK (i + N)) delta hdelta)
    rfl hY hYvolume hYbase

theorem exists_klim_seed_volume
    (hdim : Module.finrank ℝ E = 3) (kappa : ℝ) :
    ∃ v : ℝ, 0 < v ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim (I := I) kappa F → ∀ x : F.M, F.S.scalar 0 x = 1 →
          ENNReal.ofReal v ≤ riemannianVolumeMeasure (I := I) (M := F.M)
            (F.S.base.metric 0) (riemannianBallOf (I := I) (F.S.base.metric 0) x 1) := by
  obtain ⟨v, hv, hbound⟩ := exists_normalized_klim_seed_volume (I := I) hdim kappa
  refine ⟨v, hv, ?_⟩
  intro D F hK x hx
  have ht0 : (0 : ℝ) ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  let G := curvatureNormalizedFlow F hK.carrier_eq hK.regular_eq 0 1 zero_lt_one ht0 x
  have hG : KLim (I := I) kappa G :=
    KLim.curvatureNormalizedFlow F hK 0 1 zero_lt_one ht0 x hx
  have hbase : G.S.scalar 0 G.basepoint = 1 :=
    curvatureNormalizedFlow_scalar_base F hK.carrier_eq hK.regular_eq
      0 1 zero_lt_one ht0 x hx
  have hmetric : scaleMetric 1 zero_lt_one (F.S.base.metric 0) =
      F.S.base.metric 0 := by
    apply SmoothRiemannianMetric.ext_inner
    intro y u w
    simp only [scaleMetric_inner, one_mul]
  have h := hbound G hG hbase
  change ENNReal.ofReal v ≤ riemannianVolumeMeasure (I := I) (M := F.M)
    (scaleMetric 1 zero_lt_one (F.S.base.metric (parabolicTime 0 1 0)))
    (riemannianBallOf (I := I)
      (scaleMetric 1 zero_lt_one (F.S.base.metric (parabolicTime 0 1 0))) x 1) at h
  rw [parabolicTime_zero, hmetric] at h
  exact h

theorem exists_normalized_bounded_distance_scalar_constant
    (hdim : Module.finrank ℝ E = 3) (kappa D : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) T),
        KLim (I := I) kappa F → ∀ x : F.M, F.S.scalar 0 x = 1 →
          ∀ y : F.M, riemannianEDistOf (I := I) (F.S.base.metric 0) x y ≤
            ENNReal.ofReal D → F.S.scalar 0 y ≤ C := by
  obtain ⟨v, hv, hseed⟩ := exists_klim_seed_volume (I := I) hdim kappa
  obtain ⟨C, hC, hbound⟩ := exists_anchored_scalar_bound (I := I) hdim
    kappa v (max D 0 + 1) hv (by positivity)
  refine ⟨C, hC, ?_⟩
  intro T F hK x hx y hy
  apply hbound T F hK x (hseed T F hK x hx) y
  exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
    (lt_of_le_of_lt (le_max_left D 0) (lt_add_one (max D 0))))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
