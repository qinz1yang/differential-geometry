import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimHarnackCollapseBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance productionTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance productionCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance productionSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance productionC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance productionT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance productionSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance productionTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
private local instance productionMeasurable {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : MeasurableSpace F.M := borel F.M
private local instance productionBorel {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : BorelSpace F.M := ⟨rfl⟩


def KLimNormalizedSeedVolumeBound (kappa : ℝ) : Prop :=
  ∃ v : ℝ, 0 < v ∧
    ∀ F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval,
      KLim (I := I) kappa F → F.S.scalar 0 F.basepoint = 1 →
        ENNReal.ofReal v ≤ seedTerminalUnitVolume F


omit [I.Boundaryless] in
theorem kLimSeedVolumeBound_of_normalizedSeedVolumeBound {kappa : ℝ}
    (h : KLimNormalizedSeedVolumeBound.{u, uE, uH} (I := I) kappa) :
    KLimSeedVolumeBound.{u, uE, uH} (I := I) kappa := by
  obtain ⟨v, hv, hbound⟩ := h
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


omit [I.Boundaryless] in
theorem kLimSeedVolumeBound_iff_normalizedSeedVolumeBound {kappa : ℝ} :
    KLimSeedVolumeBound.{u, uE, uH} (I := I) kappa ↔
      KLimNormalizedSeedVolumeBound.{u, uE, uH} (I := I) kappa := by
  refine ⟨fun h => ?_, fun h => kLimSeedVolumeBound_of_normalizedSeedVolumeBound h⟩
  obtain ⟨v, hv, hbound⟩ := h
  refine ⟨v, hv, ?_⟩
  intro F hK hbase
  exact hbound ancientTimeInterval F hK F.basepoint hbase


def KLimSeedAncientLimit (kappa : ℝ) : Prop :=
  ∀ (X : PointedFlowSeq.{u, uE, uH} (I := I)),
    X.D = ancientTimeInterval → (∀ i, KLim (I := I) kappa (X.term i)) →
    Module.finrank ℝ E = 3 →
    (∀ i, seedTerminalUnitVolume (X.term i) = euclideanUnitBallVolume 3 / 2) →
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
        (let _ : TopologicalSpace L.M := L.topology
         ConnectedSpace L.M) ∧
        (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
        ∀ t ∈ X.D.carrier,
          ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
            (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I) (Phi.atTime (L := L) t) k) ∧
            (∀ k,
              let D := C.domain k
              let _ : TopologicalSpace
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.topology
              let _ : ChartedSpace H
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.charted
              let _ : IsManifold I ∞
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.smooth
              D.referenceMetric = D.limitMetric)


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem seedAncientLimit_not_seed_unit_volume
    {kappa : ℝ} (h : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa)
    (hdim : Module.finrank ℝ E = 3)
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) (hD : X.D = ancientTimeInterval)
    (hK : ∀ i, KLim (I := I) kappa (X.term i))
    (hvolume : ∀ i, seedTerminalUnitVolume (X.term i) = euclideanUnitBallVolume 3 / 2)
    (hbase : Tendsto (fun i => (X.term i).S.scalar 0 (X.term i).basepoint)
      atTop (𝓝 0)) : False := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨L, phi, hphi, Phi, hconnected, hcomplete, hconv⟩ :=
    h X hD hK hdim hvolume
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


theorem kLimNormalizedSeedVolumeBound_of_seedAncientLimit
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (h : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa) :
    KLimNormalizedSeedVolumeBound.{u, uE, uH} (I := I) kappa := by
  classical
  unfold KLimNormalizedSeedVolumeBound
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
  exact seedAncientLimit_not_seed_unit_volume h hdim
    (seedRescaledFlowSeq (seedFlowTail X N) (fun i => hK (i + N)) delta hdelta)
    rfl hY hYvolume hYbase


theorem kLimSeedVolumeBound_of_seedAncientLimit
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (h : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa) :
    KLimSeedVolumeBound.{u, uE, uH} (I := I) kappa :=
  kLimSeedVolumeBound_of_normalizedSeedVolumeBound (I := I)
    (kLimNormalizedSeedVolumeBound_of_seedAncientLimit (I := I) hdim h)


def KLimThreeCollapseRadius (kappa : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval,
        KLim (I := I) kappa F → PointedFlowScalarAtBase (I := I) F 1 →
        (∀ z : F.M, z ∈ riemannianBallOf (I := I) (F.S.base.metric 0) F.basepoint A →
          F.S.scalar 0 z ≤ 2) →
        riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I) (F.S.base.metric 0) F.basepoint A) ≤
          ENNReal.ofReal epsilon * ENNReal.ofReal (A ^ 3)


def KLimAlmostAncientCollapse (kappa : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ A L : ℝ, 1 ≤ A ∧ A ^ 2 ≤ L ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim (I := I) kappa F → ∀ (x : F.M) (Q r : ℝ),
        0 < Q → F.S.scalar 0 x = Q → 0 < r →
        (∀ t : ℝ, t ≤ 0 → ∀ z : F.M,
          z ∈ riemannianBallOf (I := I) (F.S.base.metric 0) x r →
            F.S.scalar t z ≤ 2 * Q) → L ≤ r ^ 2 * Q →
        riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I) (F.S.base.metric 0) x (A / Real.sqrt Q)) ≤
          ENNReal.ofReal epsilon * ENNReal.ofReal ((A / Real.sqrt Q) ^ 3)


omit [I.Boundaryless] in
theorem kLimAlmostAncientCollapse_of_threeCollapseRadius
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (h : KLimThreeCollapseRadius.{u, uE, uH} (I := I) kappa) :
    KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa := by
  intro epsilon hepsilon
  obtain ⟨A, hA, hcollapse⟩ := h epsilon hepsilon
  refine ⟨A, A ^ 2, hA, le_rfl, ?_⟩
  intro D F hK x Q r hQ hvalue hr hlocal hscale
  let _ : TopologicalSpace F.M := F.topology
  let _ : ChartedSpace H F.M := F.charted
  let _ : IsManifold I ∞ F.M := F.smooth
  have hzero : (0 : ℝ) ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  let G := curvatureNormalizedFlow F hK.carrier_eq hK.regular_eq 0 Q hQ hzero x
  have hGbase : G.basepoint = x := rfl
  have hG : KLim (I := I) kappa G :=
    KLim.curvatureNormalizedFlow F hK 0 Q hQ hzero x hvalue
  have hbase : PointedFlowScalarAtBase (I := I) G 1 :=
    curvatureNormalizedFlow_scalar_base F hK.carrier_eq hK.regular_eq
      0 Q hQ hzero x hvalue
  have hg : G.S.base.metric 0 = scaleMetric Q hQ (F.S.base.metric 0) := by
    change scaleMetric Q hQ (F.S.base.metric (parabolicTime 0 Q 0)) = _
    rw [parabolicTime_zero]
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hAr : A ≤ Real.sqrt Q * r := by
    apply (sq_le_sq₀ hApos.le (mul_pos hsqrt hr).le).1
    rw [mul_pow, Real.sq_sqrt hQ.le]
    nlinarith
  have hnormalized : ∀ z : G.M,
      z ∈ riemannianBallOf (I := I) (G.S.base.metric 0) G.basepoint A →
        G.S.scalar 0 z ≤ 2 := by
    intro z hz
    have hzscaled : z ∈ riemannianBallOf (I := I)
        (scaleMetric Q hQ (F.S.base.metric 0)) x A := by
      rw [hg, hGbase] at hz
      convert hz using 1
      rfl
    have hzsource : z ∈ riemannianBallOf (I := I) (F.S.base.metric 0) x r := by
      rw [← riemannianBallOf_scaleMetric (F.S.base.metric 0) Q hQ x r]
      change riemannianEDistOf (I := I) (scaleMetric Q hQ (F.S.base.metric 0)) x z <
        ENNReal.ofReal (Real.sqrt Q * r)
      exact hzscaled.trans_le (ENNReal.ofReal_le_ofReal hAr)
    change (curvatureNormalizedSolution F.S 0 Q hQ hzero).scalar 0 z ≤ 2
    rw [curvatureNormalizedSolution_scalar]
    change Q⁻¹ * F.S.scalar (parabolicTime 0 Q 0) z ≤ 2
    rw [parabolicTime_zero]
    calc
      Q⁻¹ * F.S.scalar 0 z ≤ Q⁻¹ * (2 * Q) :=
        mul_le_mul_of_nonneg_left (hlocal 0 le_rfl z hzsource) (inv_nonneg.mpr hQ.le)
      _ = 2 := by rw [mul_left_comm, inv_mul_cancel₀ hQ.ne', mul_one]
  have hvolume := hcollapse G hG hbase hnormalized
  have hball : riemannianBallOf (I := I) (scaleMetric Q hQ (F.S.base.metric 0)) x A =
      riemannianBallOf (I := I) (F.S.base.metric 0) x (A / Real.sqrt Q) := by
    simpa only [mul_div_cancel₀ A hsqrt.ne'] using
      riemannianBallOf_scaleMetric (F.S.base.metric 0) Q hQ x (A / Real.sqrt Q)
  change @riemannianVolumeMeasure E _ _ _ H _ I F.M
    F.topology F.charted F.smooth F.t2 F.sigmaCompact (G.S.base.metric 0)
    {z : F.M | @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (G.S.base.metric 0) x z < ENNReal.ofReal A} ≤
      ENNReal.ofReal epsilon * ENNReal.ofReal (A ^ 3) at hvolume
  rw [hg] at hvolume
  change riemannianVolumeMeasure (I := I) (M := F.M)
    (scaleMetric Q hQ (F.S.base.metric 0))
    (riemannianBallOf (I := I) (scaleMetric Q hQ (F.S.base.metric 0)) x A) ≤
      ENNReal.ofReal epsilon * ENNReal.ofReal (A ^ 3) at hvolume
  rw [hball, volume_scale_apply, hdim] at hvolume
  have hpower : ENNReal.ofReal (A ^ 3) =
      ENNReal.ofReal (Real.sqrt Q) ^ 3 * ENNReal.ofReal ((A / Real.sqrt Q) ^ 3) := by
    calc
      ENNReal.ofReal (A ^ 3) =
          ENNReal.ofReal ((Real.sqrt Q * (A / Real.sqrt Q)) ^ 3) := by
        rw [mul_div_cancel₀ A hsqrt.ne']
      _ = _ := by
        rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hsqrt.le _),
          ENNReal.ofReal_pow hsqrt.le]
  rw [hpower] at hvolume
  have hcoef0 : ENNReal.ofReal (Real.sqrt Q) ^ 3 ≠ 0 :=
    pow_ne_zero _ (ENNReal.ofReal_pos.mpr hsqrt).ne'
  have hcoeftop : ENNReal.ofReal (Real.sqrt Q) ^ 3 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_right hcoef0 hcoeftop).1
  calc
    ENNReal.ofReal (Real.sqrt Q) ^ 3 *
        riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
          (riemannianBallOf (I := I) (F.S.base.metric 0) x (A / Real.sqrt Q)) ≤
        ENNReal.ofReal epsilon *
          (ENNReal.ofReal (Real.sqrt Q) ^ 3 * ENNReal.ofReal ((A / Real.sqrt Q) ^ 3)) :=
      hvolume
    _ = ENNReal.ofReal (Real.sqrt Q) ^ 3 *
        (ENNReal.ofReal epsilon * ENNReal.ofReal ((A / Real.sqrt Q) ^ 3)) := by ac_rfl


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem kLimAnchoredScalarBound_of_almostAncientCollapse
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (h : KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa) :
    KLimAnchoredScalarBound.{u, uE, uH} (I := I) kappa := by
  intro v D hv hD
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let eta : ℝ := 1 - 1 / Real.sqrt 2
  have hroot : 0 < Real.sqrt 2 := zero_lt_one.trans Real.one_lt_sqrt_two
  have heta : 0 < eta :=
    sub_pos.mpr ((div_lt_one hroot).2 Real.one_lt_sqrt_two)
  have heta_one : eta < 1 := by
    dsimp only [eta]
    linarith [one_div_pos.mpr hroot]
  let b : ℝ := D + 1
  let B : ℝ := D + 2
  have hb : 0 < b := by dsimp only [b]; linarith only [hD]
  have hB : 0 < B := by dsimp only [B]; linarith only [hD]
  let epsilon : ℝ := v / (2 * B ^ 3)
  have hepsilon : 0 < epsilon := div_pos hv (mul_pos (by norm_num) (pow_pos hB 3))
  obtain ⟨A, L, hA, hAL, hcollapse⟩ := h epsilon hepsilon
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hL : 0 ≤ L := (sq_nonneg A).trans hAL
  have hproduct : 0 ≤ A ^ 2 * b ^ 2 := mul_nonneg (sq_nonneg A) (sq_nonneg b)
  let C : ℝ := (L + A ^ 2 * b ^ 2 + 1) / eta ^ 2
  have hC : 0 < C := div_pos (by linarith) (sq_pos_of_pos heta)
  refine ⟨C, hC, ?_⟩
  intro T F hK p hanchor q hq
  by_contra hqbound
  have hqC : C < F.S.scalar 0 q := lt_of_not_ge hqbound
  have hqpos : 0 < F.S.scalar 0 q := hC.trans hqC
  let _ : ConnectedSpace F.M := hK.connected
  let g := F.S.base.metric 0
  have hzero : (0 : ℝ) ∈ T.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  have hcomplete : RiemannianMetricComplete (I := I) g := ⟨hK.complete 0 hzero⟩
  have hqdist : (riemannianEDistOf (I := I) g p q).toReal < D :=
    ENNReal.toReal_lt_of_lt_ofReal hq
  obtain ⟨w, hw, hsigma, hs, hQ, hweight, hlocal⟩ :=
    exists_anchoredScalarSpatialPointSelection g hcomplete p hD q hqdist hqpos
  let sigma : ℝ := D + 1 - (riemannianEDistOf (I := I) g p w).toReal
  let s : ℝ := eta * sigma
  let Q : ℝ := F.S.scalar 0 w
  change 0 < sigma at hsigma
  change 0 < s at hs
  change 0 < Q at hQ
  change eta ^ 2 * F.S.scalar 0 q ≤ Q * s ^ 2 at hweight
  change ∀ z : F.M, riemannianEDistOf (I := I) g w z < ENNReal.ofReal s →
    F.S.scalar 0 z ≤ 2 * Q at hlocal
  have hthreshold : L + A ^ 2 * b ^ 2 + 1 < eta ^ 2 * F.S.scalar 0 q := by
    have h := (div_lt_iff₀ (sq_pos_of_pos heta)).1 hqC
    simpa only [mul_comm] using h
  have hlarge : L + A ^ 2 * b ^ 2 + 1 < Q * s ^ 2 :=
    hthreshold.trans_le hweight
  have hscale : L ≤ s ^ 2 * Q := by nlinarith only [hlarge, hproduct]
  have hsigma_b : sigma ≤ b := by
    have hd : 0 ≤ (riemannianEDistOf (I := I) g p w).toReal := ENNReal.toReal_nonneg
    dsimp only [sigma, b]
    linarith only [hd]
  have hs_b : s ≤ b :=
    (mul_le_of_le_one_left hsigma.le heta_one.le).trans hsigma_b
  have hs_square : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.le hb.le).2 hs_b
  have hQ_square : A ^ 2 < Q := by
    have hupper : Q * s ^ 2 ≤ Q * b ^ 2 :=
      mul_le_mul_of_nonneg_left hs_square hQ.le
    have hstrict : A ^ 2 * b ^ 2 < Q * b ^ 2 := by
      linarith only [hlarge, hupper, hL]
    exact (mul_lt_mul_iff_left₀ (sq_pos_of_pos hb)).1 hstrict
  let rho : ℝ := A / Real.sqrt Q
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hrho : 0 < rho := div_pos hApos hsqrt
  have hrho_one : rho < 1 :=
    (div_lt_one hsqrt).2 ((Real.lt_sqrt hApos.le).2 hQ_square)
  have hrho_B : rho ≤ B := by dsimp only [B]; linarith only [hrho_one, hD]
  have hpast : ∀ t : ℝ, t ≤ 0 → ∀ z : F.M,
      z ∈ riemannianBallOf (I := I) (F.S.base.metric 0) w s →
        F.S.scalar t z ≤ 2 * Q := by
    intro t ht z hz
    exact (hK.scalar_le_terminal ht z).trans (hlocal z hz)
  have hsmall := hcollapse T F hK w Q s hQ rfl hs hpast hscale
  change riemannianVolumeMeasure (I := I) (M := F.M) g
      (riemannianBallOf (I := I) g w rho) ≤
    ENNReal.ofReal epsilon * ENNReal.ofReal (rho ^ 3) at hsmall
  let _ : RiemannianBundle (fun z : F.M => TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  have hcomm : riemannianEDistOf (I := I) g w p =
      riemannianEDistOf (I := I) g p w := Manifold.riemannianEDist_comm
  have hunit_subset : riemannianBallOf (I := I) g p 1 ⊆
      riemannianBallOf (I := I) g w B := by
    intro z hz
    have hzin := riemannianBallOf_subset_add_distance (I := I) g w p 1 hz
    have hrad : 1 + (riemannianEDistOf (I := I) g w p).toReal ≤ B := by
      rw [hcomm]
      dsimp only [B]
      linarith only [hw]
    exact riemannianBallOf_mono (I := I) g w hrad hzin
  have hbig : ENNReal.ofReal v ≤ riemannianVolumeMeasure (I := I) (M := F.M) g
      (riemannianBallOf (I := I) g w B) := hanchor.trans (measure_mono hunit_subset)
  have hRic : RicciBoundedBelow (I := I) g 0 := by
    intro z v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) g z).mpr
    intro n c u w
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hK.nonnegativeCurvatureOperator 0 hzero z n c u w
  have hbishop := (riemannianBallOf_volume_bishop_nonnegative
    (I := I) g hcomplete hRic w).1 rho B hrho hrho_B
  simp only [hdim] at hbishop
  have hratio : ENNReal.ofReal (rho ^ 3) * ENNReal.ofReal v ≤
      ENNReal.ofReal (rho ^ 3) * (ENNReal.ofReal (B ^ 3) * ENNReal.ofReal epsilon) := by
    calc
      ENNReal.ofReal (rho ^ 3) * ENNReal.ofReal v =
          ENNReal.ofReal v * ENNReal.ofReal (rho ^ 3) := mul_comm _ _
      _ ≤ riemannianVolumeMeasure (I := I) (M := F.M) g
          (riemannianBallOf (I := I) g w B) * ENNReal.ofReal (rho ^ 3) :=
        mul_le_mul_left hbig _
      _ ≤ ENNReal.ofReal (B ^ 3) * riemannianVolumeMeasure (I := I) (M := F.M) g
          (riemannianBallOf (I := I) g w rho) := hbishop
      _ ≤ ENNReal.ofReal (B ^ 3) *
          (ENNReal.ofReal epsilon * ENNReal.ofReal (rho ^ 3)) :=
        mul_le_mul_right hsmall _
      _ = _ := by ac_rfl
  have hrho0 : ENNReal.ofReal (rho ^ 3) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hrho 3)).ne'
  have hbad := (ENNReal.mul_le_mul_iff_right hrho0 ENNReal.ofReal_ne_top).1 hratio
  rw [← ENNReal.ofReal_mul (pow_nonneg hB.le 3)] at hbad
  have hbadReal : v ≤ B ^ 3 * epsilon :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_nonneg hB.le 3) hepsilon.le)).1 hbad
  have hepsilon_value : B ^ 3 * epsilon = v / 2 := by
    dsimp only [epsilon]
    field_simp [hB.ne']
  rw [hepsilon_value] at hbadReal
  linarith only [hbadReal, hv]


theorem kLimAnchoredScalarBound_of_threeCollapseRadius
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (h : KLimThreeCollapseRadius.{u, uE, uH} (I := I) kappa) :
    KLimAnchoredScalarBound.{u, uE, uH} (I := I) kappa :=
  kLimAnchoredScalarBound_of_almostAncientCollapse (I := I) hdim
    (kLimAlmostAncientCollapse_of_threeCollapseRadius (I := I) hdim h)


theorem kLimHarnackCollapseBound_of_normalizedSeedVolumeBound_and_almostAncientCollapse
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimNormalizedSeedVolumeBound.{u, uE, uH} (I := I) kappa)
    (hcollapse : KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa) :
    KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa :=
  ⟨kLimSeedVolumeBound_of_normalizedSeedVolumeBound (I := I) hseed,
    kLimAnchoredScalarBound_of_almostAncientCollapse (I := I) hdim hcollapse⟩


theorem kLimHarnackCollapseBound_of_normalizedSeedVolumeBound_and_threeCollapseRadius
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimNormalizedSeedVolumeBound.{u, uE, uH} (I := I) kappa)
    (hcollapse : KLimThreeCollapseRadius.{u, uE, uH} (I := I) kappa) :
    KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa :=
  kLimHarnackCollapseBound_of_normalizedSeedVolumeBound_and_almostAncientCollapse
    (I := I) hdim hseed
    (kLimAlmostAncientCollapse_of_threeCollapseRadius (I := I) hdim hcollapse)


theorem kLimLocalCurvatureBound_of_normalizedSeedVolumeBound_and_threeCollapseRadius
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimNormalizedSeedVolumeBound.{u, uE, uH} (I := I) kappa)
    (hcollapse : KLimThreeCollapseRadius.{u, uE, uH} (I := I) kappa) :
    KLimLocalCurvatureBound.{u, uE, uH} (I := I) kappa :=
  kLimLocalCurvatureBound_of_harnackCollapseBound (I := I) hdim
    (kLimHarnackCollapseBound_of_normalizedSeedVolumeBound_and_threeCollapseRadius
      (I := I) hdim hseed hcollapse)


theorem kLimHarnackCollapseBound_of_seedAncientLimit_and_threeCollapseRadius
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa)
    (hcollapse : KLimThreeCollapseRadius.{u, uE, uH} (I := I) kappa) :
    KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa :=
  kLimHarnackCollapseBound_of_normalizedSeedVolumeBound_and_threeCollapseRadius
    (I := I) hdim (kLimNormalizedSeedVolumeBound_of_seedAncientLimit (I := I) hdim hseed)
    hcollapse


theorem kLimLocalCurvatureBound_of_seedAncientLimit_and_threeCollapseRadius
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa)
    (hcollapse : KLimThreeCollapseRadius.{u, uE, uH} (I := I) kappa) :
    KLimLocalCurvatureBound.{u, uE, uH} (I := I) kappa :=
  kLimLocalCurvatureBound_of_normalizedSeedVolumeBound_and_threeCollapseRadius (I := I) hdim
    (kLimNormalizedSeedVolumeBound_of_seedAncientLimit (I := I) hdim hseed) hcollapse


omit [I.Boundaryless] in
theorem kLimNormalizedSeedVolumeBound_of_nonpos {kappa : ℝ} (h : kappa ≤ 0) :
    KLimNormalizedSeedVolumeBound.{u, uE, uH} (I := I) kappa := by
  refine ⟨1, one_pos, ?_⟩
  intro F hK
  exact absurd hK.kappa_pos (not_lt.mpr h)


omit [I.Boundaryless] in
theorem kLimThreeCollapseRadius_of_nonpos {kappa : ℝ} (h : kappa ≤ 0) :
    KLimThreeCollapseRadius.{u, uE, uH} (I := I) kappa := by
  intro epsilon hepsilon
  refine ⟨1, le_rfl, ?_⟩
  intro F hK
  exact absurd hK.kappa_pos (not_lt.mpr h)


omit [I.Boundaryless] in
theorem kLimAlmostAncientCollapse_of_nonpos {kappa : ℝ} (h : kappa ≤ 0) :
    KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa := by
  intro epsilon hepsilon
  refine ⟨1, 1, le_rfl, by norm_num, ?_⟩
  intro D F hK
  exact absurd hK.kappa_pos (not_lt.mpr h)


theorem kLimHarnackCollapseBound_of_nonpos
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ} (h : kappa ≤ 0) :
    KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa :=
  kLimHarnackCollapseBound_of_normalizedSeedVolumeBound_and_threeCollapseRadius
    (I := I) hdim (kLimNormalizedSeedVolumeBound_of_nonpos (I := I) h)
    (kLimThreeCollapseRadius_of_nonpos (I := I) h)


omit [I.Boundaryless] in
theorem one_le_of_anchoredScalarBound {kappa : ℝ}
    (h : KLimAnchoredScalarBound.{u, uE, uH} (I := I) kappa)
    {v D : ℝ} (hv : 0 < v) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ 1 ≤ C ∧
      ∀ (T : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) T),
        KLim (I := I) kappa F → ∀ p : F.M,
          ENNReal.ofReal v ≤
            riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
              (riemannianBallOf (I := I) (F.S.base.metric 0) p 1) →
          ∀ q : F.M, q ∈ riemannianBallOf (I := I) (F.S.base.metric 0) p D →
            F.S.scalar 0 q ≤ C := by
  obtain ⟨C, hC, hbound⟩ := h v D hv hD
  exact ⟨max C 1, lt_max_of_lt_left hC, le_max_right C 1,
    fun T F hK p hp q hq => (hbound T F hK p hp q hq).trans (le_max_left C 1)⟩


private theorem productionThreeSpaceFinrank : Module.finrank ℝ ThreeSpace = 3 := by
  simp [ThreeSpace]


theorem
    kLimLocalCurvatureBound_threeSpace_of_normalizedSeedVolumeBound_and_threeCollapseRadius
    (hseed : KLimNormalizedSeedVolumeBound.{u, 0, 0} (I := I3) universalKappaConstant)
    (hcollapse : KLimThreeCollapseRadius.{u, 0, 0} (I := I3) universalKappaConstant) :
    KLimLocalCurvatureBound.{u, 0, 0} (I := I3) universalKappaConstant :=
  kLimLocalCurvatureBound_of_normalizedSeedVolumeBound_and_threeCollapseRadius
    (I := I3) productionThreeSpaceFinrank hseed hcollapse

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
