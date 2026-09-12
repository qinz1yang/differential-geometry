import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SelectedCountersequenceAdapter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessStrictStability
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RiemannFromRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MixedCurvatureJet
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeConsequences
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaSourceCapture

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions (SphereAntipodalQuotient)
open scoped Manifold ContDiff ENNReal

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

structure BlowupLimit (S : SolutionOn (I := I3) (M := M) D)
    (o : TangentOrientationSection M) (kappa : ℝ) (x : ℕ → M) (t : ℕ → ℝ) where
  model : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval
  ancient : IsAncientKappaSolution kappa model
  normalized : PointedFlowScalarAtBase model 1
  orientation : TangentOrientationSection model.M
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  scale_pos : ∀ i, 0 < S.scalar (t (subseq i)) (x (subseq i))
  map : ℕ → PartialDiffeomorph I3 I3 model.M M ∞
  exhaustion : ExhaustsByOpen (fun i => (map i).source)
  base_mem : ∀ i, model.basepoint ∈ (map i).source
  base_eq : ∀ i, map i model.basepoint = x (subseq i)
  oriented : ∀ i y, y ∈ (map i).source →
    ∃ hf : Function.Bijective (mfderiv I3 I3 (map i) y),
      PreservesTangentOrientationAt orientation o (map i) y hf
  capture : ∀ r : ℝ, 0 < r → ∀ᶠ i in Filter.atTop,
    riemannianBallOf (I := I3)
      (rescaledMetric S (t (subseq i)) (S.scalar (t (subseq i)) (x (subseq i)))
        (scale_pos i) 0) (x (subseq i)) r ⊆ (map i) '' (map i).source
  convergence : ∀ K : Set model.M, IsCompact K → ∀ A : ℝ, 0 < A →
    ∀ order : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in Filter.atTop,
      Set.Icc (t (subseq i) - A / S.scalar (t (subseq i)) (x (subseq i))) (t (subseq i)) ⊆
        D.carrier ∧ K ⊆ (map i).source ∧
      Nonempty (MetricComparisonOn (fun s => model.S.base.metric s)
        (rescaledMetric S (t (subseq i)) (S.scalar (t (subseq i)) (x (subseq i))) (scale_pos i))
        (map i) K (Set.Icc (-A) 0) order eta)

theorem maximal_point_singularity_model [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
      ∀ (x : ℕ → M) (t : ℕ → ℝ), (∀ i, t i ∈ Set.Ico theta T) →
        (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y, S.scalar s y ≤ S.scalar (t i) (x i)) →
        Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        ∃ L : BlowupLimit S o kappa x t, PointedFlowScalarBounded L.model 1 := by
  sorry


theorem closed_flow_models [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ x t, t ∈ Set.Ico 0 T → Q0 ≤ S.scalar t x →
        OrientedWitness S o eps kappa x t := by
  sorry

theorem arbitrary_high_curvature_blowup [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ (x : ℕ → M) (t : ℕ → ℝ),
      (∀ i, t i ∈ Set.Ico 0 T) →
      Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        Nonempty (BlowupLimit S o kappa x t) := by
  sorry

theorem buffered_canonical_pullback :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
          ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
            (o : TangentOrientationSection M) (x : M) (t : ℝ),
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
  exact ⟨Q, hQ, fun x t ht hR => hdelta M _ S o x t (hmodel x t ht hR)⟩

theorem fixed_kappa_compactness {kappa : ℝ} (hkappa : 0 < kappa)
    (X : ℕ → PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hX : ∀ i, IsAncientKappaSolution kappa (X i))
    (hbase : ∀ i, PointedFlowScalarAtBase (X i) 1)
    (hnoEmbedding : ∀ f : SphereAntipodalQuotient → EuclideanSpace ℝ (Fin 3),
      ¬ _root_.Topology.IsEmbedding f) :
    ∃ (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
      (f : ℕ → ℕ), StrictMono f ∧ IsAncientKappaSolution kappa L ∧
        PointedFlowScalarAtBase L 1 ∧
        ∃ F : PointedRiemannianConvergenceMaps
          (({ interval := fun _ => ancientTimeInterval, term := X } : FlowSequence).atTime 0)
          (L.atTime 0) f, MetricSourceCapture F ∧ ConvergesOn F L.S := by
  exact DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_fixed_kappa_compactness_captured
    hkappa X hX hbase hnoEmbedding

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
        (hS : IsSolutionOn S) (o : TangentOrientationSection M),
        ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ J : MixedCurvatureJet S, ∀ x t,
          t ∈ Set.Ico 0 T → Q0 ≤ S.scalar t x →
          ∀ y ∈ riemannianBallOf (I := I3) (S.base.metric t) x (eta / Real.sqrt (S.scalar t x)),
            0 < S.scalar t y ∧ J.norm a b t y ≤
              C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
