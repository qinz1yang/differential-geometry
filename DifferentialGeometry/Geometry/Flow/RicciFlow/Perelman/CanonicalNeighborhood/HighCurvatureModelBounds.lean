import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureTimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedMixedCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SelectedCountersequenceAdapter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessStrictStability
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RiemannFromRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MixedCurvatureJet
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeConsequences
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaSourceCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureBounds
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorBounds


set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

def StrictWitness (S : SolutionOn (I := I3) (M := M) D)
    (eps kappa : ℝ) (x : M) (t : ℝ) : Prop :=
  ∃ W : WindowedModelWitness eps kappa S x t,
    ∀ a b : ℕ, a + 2 * b ≤ modelOrder eps →
      ∀ s ∈ Set.Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
          W.model.basepoint (modelRadius eps),
          tensor02CovDerivNormWith (I := I3) a (W.comparison.jet b s)
            (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps

omit [SigmaCompactSpace M] in
theorem oriented_witness_mono (S : SolutionOn (I := I3) (M := M) D)
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    {delta eps kappa : ℝ} (hde : delta ≤ eps) (he : eps < 1)
    {x : M} {t : ℝ}
    (hreg : ∀ s ∈ Set.Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    (hw : OrientedWitness S o delta kappa x t) :
    OrientedWitness S o eps kappa x t := by
  obtain ⟨W, oN, hO⟩ := hw
  exact ⟨W.mono_of_regular hS hde he hreg, oN, hO⟩

theorem strict_model_witness_open (S : SolutionOn (I := I3) (M := M) D)
    (hS : IsSolutionOn S) {eps kappa : ℝ}
    (U : Set (M × ℝ)) (hU : IsOpen U)
    (hadmissible : ∀ q ∈ U,
      Set.Icc (q.2 - (eps * S.scalar q.2 q.1)⁻¹) q.2 ⊆ D.regular) :
    IsOpen (U ∩ {q : M × ℝ | StrictWitness S eps kappa q.1 q.2}) := by
  have hbase := isOpen_setOf_regular_strict_model_witness (S := S) hS eps kappa
  have heq : U ∩ {q : M × ℝ | StrictWitness S eps kappa q.1 q.2} =
      U ∩ {q : M × ℝ |
        Set.Icc (q.2 - (eps * S.scalar q.2 q.1)⁻¹) q.2 ⊆ D.regular ∧
          ∃ W : WindowedModelWitness eps kappa S q.1 q.2,
            ∀ a b : ℕ, a + 2 * b ≤ modelOrder eps →
              ∀ s ∈ Set.Icc (-modelDepth eps) 0,
                ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
                  W.model.basepoint (modelRadius eps),
                  tensor02CovDerivNormWith (I := I3) a (W.comparison.jet b s)
                    (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps} := by
    ext q
    constructor
    · rintro ⟨hq, hW⟩
      exact ⟨hq, hadmissible q hq, hW⟩
    · rintro ⟨hq, _, hW⟩
      exact ⟨hq, hW⟩
  rw [heq]
  exact hU.inter hbase


theorem selected_countersequence_of_radius_failure {eps small kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) (hsmall : 0 < small) (hs : small ≤ eps)
    (failure : ∀ r : ℝ, 0 < r → r ≤ Real.sqrt eps →
      ¬ ModelRadiusWorksClosed.{u} eps kappa sigma Phi r) :
    Nonempty (SelectedCountersequence.{u} small kappa sigma Phi) := by
  exact selected_countersequence_of_radius_failure' heps heps1 hsmall hs failure

theorem witness_of_ancient_extension {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (heps : 0 < eps) (heps1 : eps < 1)
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
    {J : RealTimeInterval} (B : BackwardExtension L J) (A : AncientExtension B) :
    ∀ᶠ i in Filter.atTop,
      OrientedWitness (X.term (L.subseq (A.extension.subseq i))).S
        (X.orientation (L.subseq (A.extension.subseq i))) eps kappa
        (X.term (L.subseq (A.extension.subseq i))).basepoint 0 := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let Fm := subsequenceMaps L.maps A.extension.subseq A.extension.strictMono
  have hzero : (0 : ℝ) ∈ ancientTimeInterval.carrier := by
    simp
  have hmet : RiemannianMetricComplete (I := I3) (A.extension.solution.base.metric 0) :=
    ⟨MetricComplete.complete (I := I3) (A.extension.pointed.atTime (I := I3) 0)
      (A.ancient.complete 0 hzero)⟩
  have hab : -modelDepth eps ≤ 0 := neg_nonpos.mpr (inv_nonneg.mpr heps.le)
  have hmem0 : (0 : ℝ) ∈ Set.Icc (-modelDepth eps) 0 := ⟨hab, le_rfl⟩
  have hsub : Set.Icc (-modelDepth eps) 0 ⊆ ancientTimeInterval.carrier :=
    fun s hs => by rw [ancientTimeInterval_carrier]; exact hs.2
  let Kb := riemannianClosedBallOf (I := I3) (A.extension.solution.base.metric 0)
    A.extension.pointed.basepoint (modelRadius eps + 1)
  let Ks := riemannianClosedBallOf (I := I3) (A.extension.solution.base.metric 0)
    A.extension.pointed.basepoint (modelRadius eps)
  have hKb : IsCompact Kb := RiemannianMetricComplete.closedEBall_isCompact hmet _ _
  have hKs : IsCompact Ks := RiemannianMetricComplete.closedEBall_isCompact hmet _ _
  have hbig := A.extension.convergence Kb hKb (-(modelDepth eps)) 0 hab hsub (modelOrder eps) eps heps
  have hsmall := A.extension.convergence Ks hKs (-(modelDepth eps)) 0 hab hsub (modelOrder eps) eps heps
  have hrad : 0 < modelRadius eps - 1 := by
    have h1 : (1 : ℝ) < modelRadius eps := by
      rw [modelRadius, one_lt_inv_iff₀]
      refine ⟨Real.sqrt_pos.mpr heps, ?_⟩
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
      simpa using heps1
    linarith
  have hd : ∀ᶠ i in Filter.atTop,
      modelDepth eps ≤ 2 * X.depth (L.subseq (A.extension.subseq i)) := by
    have htend : Filter.Tendsto (fun i => X.depth (L.subseq (A.extension.subseq i)))
        Filter.atTop Filter.atTop :=
      X.depth_tendsto.comp (L.strictMono.tendsto_atTop.comp A.extension.strictMono.tendsto_atTop)
    filter_upwards [htend.eventually (Filter.eventually_ge_atTop (modelDepth eps / 2))] with i hi
    linarith
  have hcap : ∀ᶠ i in Filter.atTop,
      riemannianBallOf (I := I3) ((X.term (L.subseq (A.extension.subseq i))).S.base.metric 0)
        (X.term (L.subseq (A.extension.subseq i))).basepoint (modelRadius eps - 1) ⊆
        (Fm.partialDiffeomorph i) '' (Fm.partialDiffeomorph i).source := by
    filter_upwards [A.extension.strictMono.tendsto_atTop.eventually
      (L.capture (modelRadius eps - 1) hrad)] with i hi
    exact hi
  filter_upwards [hd, hbig, hsmall, hcap] with i hdI hbigI hsmallI hcapI
  have hQ1 : (X.term (L.subseq (A.extension.subseq i))).S.scalar 0
      (X.term (L.subseq (A.extension.subseq i))).basepoint = 1 :=
    X.base_one (L.subseq (A.extension.subseq i))
  have hQpos : 0 < (X.term (L.subseq (A.extension.subseq i))).S.scalar 0
      (X.term (L.subseq (A.extension.subseq i))).basepoint := by
    rw [hQ1]; norm_num
  have hbase_eq : (Fm.partialDiffeomorph i) A.extension.pointed.basepoint =
      (X.term (L.subseq (A.extension.subseq i))).basepoint := by
    simpa only [BackwardExtension.pointed, Function.comp_apply, Fm, subsequenceMaps,
      FlowSequence.atTime, PointedFlowData.atTime, SolutionOn.family_metric] using
      Fm.basepoint_map i
  have hg : rescaledMetric (X.term (L.subseq (A.extension.subseq i))).S 0
      ((X.term (L.subseq (A.extension.subseq i))).S.scalar 0
        (X.term (L.subseq (A.extension.subseq i))).basepoint) hQpos
      = (X.term (L.subseq (A.extension.subseq i))).S.base.metric := by
    funext s'
    apply SmoothRiemannianMetric.ext_inner
    intro x' a b
    simp only [rescaledMetric, hQ1, parabolicTime, zero_add, div_one, scaleMetric_inner, one_mul]
  obtain ⟨C⟩ := hsmallI.2.2
  have hC : MetricComparisonOn (fun s => A.extension.solution.base.metric s)
      (rescaledMetric (X.term (L.subseq (A.extension.subseq i))).S 0
        ((X.term (L.subseq (A.extension.subseq i))).S.scalar 0
          (X.term (L.subseq (A.extension.subseq i))).basepoint) hQpos)
      (Fm.partialDiffeomorph i) Ks (Set.Icc (-modelDepth eps) 0) (modelOrder eps) eps := by
    refine ⟨C.pullback, ?_, C.jet, C.jet_zero, C.jet_succ, C.equivalence, C.close⟩
    intro s y hy v
    rw [C.pullback_eq s y hy v, hg]
    simp only [Fm, Function.comp_apply]
  obtain ⟨eta, _heta, hreserve⟩ := MetricComparisonOn.exists_source_capture_reserve
    (fun s => A.extension.solution.base.metric s)
    (rescaledMetric (X.term (L.subseq (A.extension.subseq i))).S 0
      ((X.term (L.subseq (A.extension.subseq i))).S.scalar 0
        (X.term (L.subseq (A.extension.subseq i))).basepoint) hQpos)
    (Fm.partialDiffeomorph i) A.extension.pointed.basepoint hmem0 heps heps1 hC hKs hsmallI.2.1
  refine ⟨{ eps_pos := heps
            eps_lt_one := heps1
            time_mem := ?_
            scalar_pos := hQpos
            window_mem := ?_
            model := A.extension.pointed
            model_ancient := A.ancient
            model_scalar_base := A.normalized
            embedding := Fm.partialDiffeomorph i
            buffered_ball := ?_
            base_map := ?_
            comparison := hC
            source_capture := ?_ }, ?_⟩
  · rw [X.carrier_eq (L.subseq (A.extension.subseq i))]
    exact ⟨by linarith [X.depth_pos (L.subseq (A.extension.subseq i))], le_rfl⟩
  · rw [X.carrier_eq (L.subseq (A.extension.subseq i))]
    intro s hs
    refine ⟨?_, hs.2⟩
    have h1 : (0 : ℝ) - (eps * (X.term (L.subseq (A.extension.subseq i))).S.scalar 0
        (X.term (L.subseq (A.extension.subseq i))).basepoint)⁻¹ = -modelDepth eps := by
      rw [X.base_one (L.subseq (A.extension.subseq i)), modelDepth, mul_one]; ring
    rw [h1] at hs
    linarith [hdI, hs.1]
  · exact hbigI.2.1
  · exact hbase_eq
  · intro q hq
    have hq' : q ∈ riemannianClosedBallOf (I := I3)
        (rescaledMetric (X.term (L.subseq (A.extension.subseq i))).S 0
          ((X.term (L.subseq (A.extension.subseq i))).S.scalar 0
            (X.term (L.subseq (A.extension.subseq i))).basepoint) hQpos 0)
        (X.term (L.subseq (A.extension.subseq i))).basepoint (modelRadius eps - 1 + eta) :=
      (le_of_lt hq).trans (ENNReal.ofReal_le_ofReal (by linarith))
    have hq'' : q ∈ riemannianClosedBallOf (I := I3)
        (rescaledMetric (X.term (L.subseq (A.extension.subseq i))).S 0
          ((X.term (L.subseq (A.extension.subseq i))).S.scalar 0
            (X.term (L.subseq (A.extension.subseq i))).basepoint) hQpos 0)
        ((Fm.partialDiffeomorph i) A.extension.pointed.basepoint)
        (modelRadius eps - 1 + eta) := by
      rw [hbase_eq]
      exact hq'
    obtain ⟨z, hz, hzq⟩ := hreserve hq''
    exact ⟨z, hsmallI.2.1 hz, hzq⟩
  · exact ⟨L.orientation, fun y hy => L.orientation_preserved (A.extension.subseq i) y hy⟩

theorem no_selected_countersequence {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ e : ℝ, 0 < e ∧ ∀ eps : ℝ, 0 < eps → eps < 1 → eps ≤ e →
      ¬ Nonempty (SelectedCountersequence.{u} eps kappa sigma Phi) := by
  obtain ⟨e1, he1, h1⟩ := bounded_curvature_at_distance.{u} hkappa hsigma hPhi
  obtain ⟨e2, he2, h2⟩ := terminal_limit_global_bound.{u} hkappa hsigma hPhi
  obtain ⟨e3, he3, h3⟩ := first_backward_slab.{u} hkappa hsigma hPhi
  obtain ⟨e4, he4, h4⟩ := ancient_extension.{u} hkappa hsigma hPhi
  refine ⟨min (min e1 e2) (min e3 e4), lt_min (lt_min he1 he2) (lt_min he3 he4), ?_⟩
  intro eps hp hp1 he ⟨X⟩
  have hleft := (le_min_iff.mp he).1
  have hright := (le_min_iff.mp he).2
  obtain ⟨hb, hd⟩ := h1 eps hp (le_min_iff.mp hleft).1 X.toNormalizedSequence
  obtain ⟨L⟩ := h2 eps hp (le_min_iff.mp hleft).2 X.toNormalizedSequence hb hd
  obtain ⟨delta, hdelta, ⟨B⟩⟩ := h3 eps hp (le_min_iff.mp hright).1 X.toNormalizedSequence L
  obtain ⟨A⟩ := h4 eps hp (le_min_iff.mp hright).2 X.toNormalizedSequence L delta hdelta B
  obtain ⟨i, hi⟩ := (witness_of_ancient_extension hp hp1 X.toNormalizedSequence L B A).exists
  exact X.bad _ hi

theorem abstract_model_theorem {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) (hkappa : 0 < kappa) (hsigma : 0 < sigma)
    (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.sqrt eps ∧ ModelRadiusWorksClosed.{u} eps kappa sigma Phi r := by
  classical
  by_contra h
  have failure : ∀ r : ℝ, 0 < r → r ≤ Real.sqrt eps →
      ¬ ModelRadiusWorksClosed.{u} eps kappa sigma Phi r := by
    intro r hr hrs hw
    exact h ⟨r, hr, hrs, hw⟩
  obtain ⟨e, he, hno⟩ := no_selected_countersequence.{u} hkappa hsigma hPhi
  have hsmall : 0 < min eps e := lt_min heps he
  exact hno (min eps e) hsmall ((min_le_left _ _).trans_lt heps1) (min_le_right _ _)
    (selected_countersequence_of_radius_failure heps heps1 hsmall (min_le_left _ _)
      failure)

theorem closed_flow_models [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ x t, t ∈ Set.Ico 0 T → Q0 ≤ S.scalar t x →
        OrientedWitness S o eps kappa x t := by
  classical
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨kappa, hkappa, hbelow⟩ :=
    spatial_no_local_collapsing (I := I3) (M := M) hT S hS hdim (rho := 1) one_pos
  refine ⟨kappa, hkappa, fun eps heps heps1 => ?_⟩
  obtain ⟨K, hKpos, hKinit⟩ :=
    DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_curvatureOperatorLowerBoundAt_metricRm04
      (I := I3) (M := M) (S.base.metric 0) hdim
  have hinit : ∀ x : M, curvatureOperatorLowerBoundAt (I := I3) (S.base.metric 0) x
      ⟨S.base.rm04 0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I3) (S.base.metric 0) x⟩ K := by
    intro x
    simpa only [SolutionFamily.rm04, metricRm04_apply] using hKinit x
  obtain ⟨Phi0, hPhi0, hPhi0ge⟩ := exists_admissiblePinchingFunction_ge
    (psi := hamiltonIveyPinchingBound K)
    ((hamiltonIveyPinchingBound_monotone hKpos.le).monotoneOn (Set.Ici 0))
    (fun s _ => hamiltonIveyPinchingBound_nonneg hKpos.le s)
    (hamiltonIveyPinchingBound_quotient_tendsto hKpos.le)
  have hKexp : 0 < K * Real.exp 3 := mul_pos hKpos (Real.exp_pos 3)
  let Phi : ℝ → ℝ := fun s => Phi0 s + K * Real.exp 3
  have hPhi : AdmissiblePinchingFunction Phi := hPhi0.add_const hKexp.le
  let A : ℝ := 2 / T
  have hA : 0 < A := by dsimp only [A]; positivity
  let Phi' : ℝ → ℝ := rescalePinchingFunction A Phi
  have hPhi' : AdmissiblePinchingFunction Phi' := hPhi.rescale hA
  let sigma : ℝ := Real.sqrt A / 2
  have hsigma : 0 < sigma := by dsimp only [sigma]; positivity
  obtain ⟨r, hrpos, hrle, hmodel⟩ :=
    abstract_model_theorem (eps := eps) (kappa := kappa) (sigma := sigma) (Phi := Phi')
      heps heps1 hkappa hsigma hPhi'
  obtain ⟨C2, hC2nn, hC2⟩ := exists_curvature_bound_on_carrier_interval_of_isSolutionOn
    (I := I3) (M := M) S hS (a := 0) (b := T / 2)
    (by intro s hs; exact ⟨hs.1, lt_of_le_of_lt hs.2 (by linarith)⟩)
  let Msc : ℝ := (3:ℝ) ^ 2 * Real.sqrt C2
  have hMsc : ∀ s ∈ Set.Icc 0 (T / 2), ∀ y : M, S.scalar s y ≤ Msc := by
    intro s hs y
    have h1 := scalar_abs_le_rm (I := I3) (S.base.metric s) y
    have h2 : normSq0S (I := I3) (S.base.metric s) y 4
        (metricRm04At (I := I3) (S.base.metric s) y) ≤ C2 := by
      have h := hC2 s hs y
      simpa only [SolutionOn.family_metric] using h
    have h3 : Module.finrank ℝ (TangentSpace I3 y) = Module.finrank ℝ ThreeSpace := rfl
    rw [h3, hdim] at h1
    refine le_trans (le_abs_self _) (le_trans h1 ?_)
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (by positivity)
  let Q0 : ℝ := max Msc (A / r ^ 2) + 1
  have hQ0pos : 0 < Q0 := by
    have h1 : 0 < A / r ^ 2 := div_pos hA (pow_pos hrpos 2)
    have h2 : A / r ^ 2 ≤ max Msc (A / r ^ 2) := le_max_right _ _
    dsimp only [Q0]
    linarith
  refine ⟨Q0, hQ0pos, fun x t ht hscalar => ?_⟩
  have hQ0big : Msc < Q0 := by
    have h2 : Msc ≤ max Msc (A / r ^ 2) := le_max_left _ _
    dsimp only [Q0]
    linarith
  have htgt : T / 2 < t := by
    by_contra hcon
    have hs : t ∈ Set.Icc 0 (T / 2) := ⟨ht.1, not_lt.mp hcon⟩
    have h := hMsc t hs x
    linarith
  have hAt1 : 1 < A * t := by
    have heq : A * (T / 2) = 1 := by dsimp only [A]; field_simp
    have h2 := mul_lt_mul_of_pos_left htgt hA
    linarith
  let T3 : ℝ := (t + T) / 2
  have hT3gt : T / 2 < T3 := by dsimp only [T3]; linarith
  have hT3lt : T3 < T := by dsimp only [T3]; linarith [ht.2]
  have hT3nn : 0 ≤ T3 := by linarith [hT, hT3gt]
  have hT3sub : Set.Icc 0 T3 ⊆ (RealTimeInterval.closedOpen 0 T hT).carrier := by
    intro s hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 hT3lt⟩
  have himpinch : PhiAlmostNonnegative (I := I3) (M := M) S (Set.Icc 0 T3) Phi := by
    have hprop := curvatureOperatorRegionPropagationOn_of_initial_lower_bound (I := I3) (M := M)
      S hS hT3nn hKpos (by simpa using hT3sub)
      (by intro s hs; exact ⟨hs.1, by linarith [hs.2, hT3lt]⟩) hdim hinit
    intro t' ht' y
    obtain ⟨basis, horth, _⟩ := hprop t' (by simpa using ht') y
    have hbound : -leastCurvatureOperatorEigenvalueAt (I := I3) (S.base.metric t') y
        ⟨S.base.rm04 t' y, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I3) (S.base.metric t') y⟩ ≤ hamiltonIveyPinchingBound K (S.scalar t' y) := by
      refine le_csInf ⟨1 * max (S.scalar t' y) 0 + 2 * 1 * K * Real.exp (2 + (2 * (1:ℝ))⁻¹),
        1, one_pos, rfl⟩ ?_
      rintro a ⟨d, hd, rfl⟩
      have hmain := hamilton_ivey_asymptotic_pinching_of_curvatureOperatorRegionPropagationOn
        (I := I3) (M := M) S hKpos hd hprop t' (by simpa using ht') y
      have hpinch : -leastCurvatureOperatorEigenvalueAt (I := I3) (S.base.metric t') y
          ⟨S.base.rm04 t' y, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I3) (S.base.metric t') y⟩ ≤
          DimensionThree.pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I3)
            (S.base.metric t') y ⟨S.base.rm04 t' y,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I3) (S.base.metric t') y⟩) :=
        le_max_left _ _
      have hden : (1 : ℝ) ≤ 1 + 2 * K * (t' - 0) := by
        have h2 : 0 ≤ 2 * K * (t' - 0) :=
          mul_nonneg (mul_nonneg (by norm_num) hKpos.le) (by linarith [ht'.1])
        linarith
      have hfrac : 2 * d * K * Real.exp (2 + (2 * d)⁻¹) / (1 + 2 * K * (t' - 0)) ≤
          2 * d * K * Real.exp (2 + (2 * d)⁻¹) :=
        div_le_self (mul_nonneg (mul_nonneg (by linarith) hKpos.le)
          (le_of_lt (Real.exp_pos _))) hden
      have hmax : d * S.scalar t' y ≤ d * max (S.scalar t' y) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hd.le
      linarith
    have hkey : -leastCurvatureOperatorEigenvalueAt (I := I3) (S.base.metric t') y
        ⟨S.base.rm04 t' y, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I3) (S.base.metric t') y⟩ ≤ Phi (S.scalar t' y) := by
      rcases le_total 0 (S.scalar t' y) with hR | hR
      · have h1 := hPhi0ge (S.scalar t' y) hR
        have hexp : (0:ℝ) ≤ K * Real.exp 3 := hKexp.le
        dsimp only [Phi]
        linarith
      · have h1 := hamiltonIveyPinchingBound_le_of_nonpos hKpos.le hR
        have h2 := hPhi0.pos (S.scalar t' y)
        dsimp only [Phi]
        linarith
    have heq := DimensionThree.leastCurvatureOperatorEigenvalueAt_eq_sectionalMin (I := I3)
      (S.base.metric t') y basis horth ⟨S.base.rm04 t' y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I3) (S.base.metric t') y⟩
    rw [DimensionThree.curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le (I := I3)
      (S.base.metric t') basis horth (A := ⟨S.base.rm04 t' y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I3) (S.base.metric t') y⟩)
      (K := Phi (S.scalar t' y)), ← heq]
    exact hkey
  have hbase0 : (0:ℝ) ∈ (RealTimeInterval.closedOpen 0 T hT).carrier := ⟨le_rfl, hT⟩
  let Dpar : RealTimeInterval := parabolicInterval (RealTimeInterval.closedOpen 0 T hT) 0 A hbase0
  let SI : SolutionOn (I := I3) (M := M) Dpar := parabolicSolution (I := I3) (M := M) S 0 A hA hbase0
  have hcar : Dpar.carrier = Set.Ico 0 (A * T) := by
    dsimp only [Dpar]
    simpa using parabolicInterval_closedOpen_carrier (T := T) (τ := 0) (R := A) hT hA hbase0
  have hregcar : Dpar.regular = Set.Ioo 0 (A * T) := by
    dsimp only [Dpar]
    simpa using parabolicInterval_closedOpen_regular (T := T) (τ := 0) (R := A) hT hA hbase0
  let T'' : ℝ := A * T3
  have hT''1 : 1 ≤ T'' := by
    have h1 : A * (T / 2) = 1 := by dsimp only [A]; field_simp
    have h2 : A * (T / 2) < A * T3 := mul_lt_mul_of_pos_left hT3gt hA
    dsimp only [T'']
    linarith
  have hT''lt : T'' < A * T := by
    dsimp only [T'']
    exact mul_lt_mul_of_pos_left hT3lt hA
  let D'' : RealTimeInterval := RealTimeInterval.closed 0 T'' (by linarith)
  let S'' : SolutionOn (I := I3) (M := M) D'' := SI.timeRestrict D''
  have hsub'' : D''.carrier ⊆ Dpar.carrier := by
    intro s hs
    rw [hcar]
    exact ⟨hs.1, lt_of_le_of_lt hs.2 hT''lt⟩
  have hreg'' : D''.regular ⊆ Dpar.regular := by
    intro s hs
    rw [hregcar]
    exact ⟨hs.1, lt_of_lt_of_le hs.2 hT''lt.le⟩
  have hSI : IsSolutionOn SI := parabolicSolution_isSolutionOn (I := I3) (M := M) S hS 0 A hA hbase0
  have hS'' : IsSolutionOn S'' := isSolutionOn_timeRestrict (I := I3) (M := M) hSI hsub'' hreg''
  have hpin_para : PhiAlmostNonnegative (I := I3) (M := M) SI
      {s : ℝ | parabolicTime 0 A s ∈ Set.Icc 0 T3} Phi' :=
    phiAlmostNonnegative_paraSolution (I := I3) (M := M) S hA hbase0 himpinch
  have hnoncollapse : SpatiallyKappaNoncollapsedBelowScale S'' kappa sigma := by
    have hpara := parabolic_spatial_noncollapse (I := I3) (M := M) S 0 A hA hbase0 kappa 1 hbelow
    have hres := spatiallyKappaNoncollapsed_timeRestrict (S := SI) (D' := D'') hsub'' hpara
    have hle : sigma ≤ Real.sqrt A * 1 := by
      have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
      dsimp only [sigma]
      rw [mul_one]
      linarith
    exact ⟨hsigma, fun t B hB => hres.2 t B (le_trans hB hle)⟩
  have hcurv : ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ D''.carrier → ∃ C : ℝ,
      ∀ s ∈ Set.Icc a b, ∀ y : M, FlowMetricBall.rmNormSq S'' s y ≤ C := by
    intro a b hab hsubab
    obtain ⟨C, hCnn, hC⟩ := exists_curvature_bound_on_carrier_interval_of_isSolutionOn
      (I := I3) (M := M) S'' hS'' hsubab
    refine ⟨C, fun s hs y => ?_⟩
    have h := hC s hs y
    simpa only [FlowMetricBall.rmNormSq, SolutionFamily.rm04, metricRm04_apply,
      SolutionOn.family_metric] using h
  have hpin : PhiAlmostNonnegative (I := I3) (M := M) S'' D''.carrier Phi' := by
    intro s hs y
    have hs' : parabolicTime 0 A s ∈ Set.Icc 0 T3 := by
      have hs2 : s ≤ T'' := hs.2
      dsimp only [T''] at hs2
      have hle : s / A ≤ T3 := by
        rw [div_le_iff₀ hA]
        rwa [mul_comm] at hs2
      exact ⟨by simpa only [parabolicTime, zero_add] using div_nonneg hs.1 hA.le,
        by simpa only [parabolicTime, zero_add] using hle⟩
    exact hpin_para s hs' y
  have hhyp : ClosedModelHypotheses S'' kappa sigma Phi' :=
    { isSolution := hS''
      complete := fun s _ => RiemannianMetricComplete.of_compact (I := I3) (M := M) (S''.base.metric s)
      curvature := hcurv
      pinching := hpin
      noncollapse := hnoncollapse }
  have hmem : A * t ∈ Set.Icc 1 T'' := by
    refine ⟨hAt1.le, ?_⟩
    dsimp only [T'']
    have h1 : t ≤ T3 := by dsimp only [T3]; linarith [ht.2]
    exact mul_le_mul_of_nonneg_left h1 hA.le
  have hthr : r⁻¹ ^ 2 ≤ S''.scalar (A * t) x := by
    have h1 : A / r ^ 2 ≤ Q0 := by
      have h2 : A / r ^ 2 ≤ max Msc (A / r ^ 2) := le_max_right _ _
      dsimp only [Q0]
      linarith
    have hQ0gt : A / r ^ 2 < Q0 := by
      dsimp only [Q0]
      linarith [le_max_right Msc (A / r ^ 2)]
    have h2 : A / r ^ 2 < S.scalar t x := lt_of_lt_of_le hQ0gt hscalar
    have hsc : S''.scalar (A * t) x = A⁻¹ * S.scalar t x := by
      have htime : parabolicTime 0 A (A * t) = t := by
        dsimp only [parabolicTime]
        field_simp
        ring
      dsimp only [S'', SI]
      rw [scalar_timeRestrict, parabolicSolution_scalar]
      simp only [htime]
    rw [hsc]
    calc r⁻¹ ^ 2 = 1 / r ^ 2 := by rw [inv_pow, one_div]
      _ = A⁻¹ * (A / r ^ 2) := by field_simp
      _ ≤ A⁻¹ * S.scalar t x := mul_le_mul_of_nonneg_left h2.le (inv_nonneg.mpr hA.le)
  have hwit0 : OrientedWitness S'' o eps kappa x (A * t) :=
    hmodel M o T'' hT''1 S'' hhyp x (A * t) hmem hthr
  have hwit1 : OrientedWitness SI o eps kappa x (A * t) :=
    orientedWitness_of_timeRestrict (S := SI) (D' := D'') hsub'' hwit0
  have hwit2 := (orientedWitness_paraSolution_iff S o hA hbase0 (A * t) x eps kappa).mp hwit1
  have htime : parabolicTime 0 A (A * t) = t := by
    dsimp only [parabolicTime]
    field_simp
    ring
  rw [htime] at hwit2
  exact hwit2

theorem buffered_canonical_pullback :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
          ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
            IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
            Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
            OrientedWitness S o delta kappa x t → Nonempty (CanonicalWitness S eps C1 C2 x t) := by
  sorry

theorem smooth_canonical_neighborhood :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
          [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
          (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
          (_hS : IsSolutionOn S) (_o : TangentOrientationSection M),
          ∃ Qcan : ℝ, 0 < Qcan ∧ ∀ x t, t ∈ Set.Ico 0 T → Qcan ≤ S.scalar t x →
            Nonempty (CanonicalWitness S eps C1 C2 x t) := by
  obtain ⟨epsCan, hepsCan, hpb⟩ := buffered_canonical_pullback.{u}
  refine ⟨epsCan, hepsCan, ?_⟩
  intro eps heps hsmall
  obtain ⟨C1, C2, hC1, hC2, htransfer⟩ := hpb eps heps hsmall
  refine ⟨C1, C2, hC1, hC2, ?_⟩
  intro M _ _ _ _ _ _ _ T hT S hS o
  obtain ⟨kappa, hkappa, hm⟩ := closed_flow_models hT S hS o
  obtain ⟨delta, hd, hd1, hdelta⟩ := htransfer kappa hkappa
  obtain ⟨Q, hQ, hmodel⟩ := hm delta hd hd1
  refine ⟨Q, hQ, ?_⟩
  intro x t ht hR
  have hw := hmodel x t ht hR
  apply hdelta M _ S hS o x t ?_ hw
  obtain ⟨W, _⟩ := hw
  simpa only [RealTimeInterval.closedOpen, interior_Icc, interior_Ico] using
    interior_mono W.window_mem

theorem fixed_kappa_compactness {kappa : ℝ} (hkappa : 0 < kappa)
    (X : ℕ → PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hX : ∀ i, IsAncientKappaSolution kappa (X i))
    (hbase : ∀ i, PointedFlowScalarAtBase (X i) 1) :
    ∃ (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
      (f : ℕ → ℕ), StrictMono f ∧ IsAncientKappaSolution kappa L ∧
        PointedFlowScalarAtBase L 1 ∧
        ∃ F : PointedRiemannianConvergenceMaps
          (({ interval := fun _ => ancientTimeInterval, term := X } : FlowSequence).atTime 0)
          (L.atTime 0) f, MetricSourceCapture F ∧ ConvergesOn F L.S := by
  exact DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_fixed_kappa_compactness_captured
    hkappa X hX hbase

theorem kappa_universal_derivatives (a b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ kappa : ℝ, 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
        IsAncientKappaSolution kappa P → PointedFlowScalarAtBase P 1 →
        ∀ J : MixedCurvatureJet P.S, J.norm a b 0 P.basepoint ≤ C :=
  DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_kappa_universal_derivatives a b

theorem high_curvature_derivatives (a b : ℕ) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
        [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
        (_hS : IsSolutionOn S) (_o : TangentOrientationSection M),
        ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ J : MixedCurvatureJet S, ∀ x t,
          t ∈ Set.Ioo 0 T → Q0 ≤ S.scalar t x →
          ∀ y ∈ riemannianBallOf (I := I3) (S.base.metric t) x (eta / Real.sqrt (S.scalar t x)),
            0 < S.scalar t y ∧ J.norm a b t y ≤
              C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) := by
  obtain ⟨B, hB, hmodel⟩ :=
    KappaSolutions.exists_universal_normalized_ancient_curvature_bounds.{u}
  obtain ⟨C, eta, hC, heta, hbound⟩ :=
    exists_windowedModelWitness_scalar_weighted_mixedCurvatureNorm_bound
      (Real.sqrt (B 2)) (Real.sqrt_nonneg _) a b
  apply high_curvature_derivatives_of_mixedCurvatureNorm_bound a b
  refine ⟨C, eta, hC, heta, ?_⟩
  intro M _ _ _ _ _ _ _ T hT S hS o
  obtain ⟨kappa, _hkappa, hmodels⟩ := closed_flow_models hT S hS o
  obtain ⟨Q0, hQ0, hwitness⟩ := hmodels (1 / 4) (by norm_num) (by norm_num)
  refine ⟨Q0, hQ0, fun x t ht hQ y hy => ?_⟩
  obtain ⟨W, _orientation, _horiented⟩ := hwitness x t ⟨ht.1.le, ht.2⟩ hQ
  apply hbound hS W le_rfl (by
      simp only [RealTimeInterval.closedOpen, interior_Ico]
      exact Set.Subset.rfl) ht
  · intro s hs z hz
    rw [Real.sq_sqrt (hB 2).le]
    exact hmodel kappa W.model W.model_ancient W.model_scalar_base 2 z hz s hs.2
  · exact (show riemannianEDistOf (I := I3) (S.base.metric t) x y <
      ENNReal.ofReal (eta / Real.sqrt (S.scalar t x)) from hy).le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
