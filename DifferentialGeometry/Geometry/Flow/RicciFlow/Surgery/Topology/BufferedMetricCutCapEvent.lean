import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CappingReparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedSmoothCutCapTransition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedRetainedCoreSmooth
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FullRetainedUnchangedLocus

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [CompactSpace M] [Nonempty M]
  {ι : Type} [Fintype ι] {δ : ι → ℝ} {L : ℝ}
  (hL : 0 < L) (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
  (R : Set (ConnectedComponents (cutCore f)))
  (o : SmoothOrientation ThreeModel M)
  (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))

local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj

private local instance : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
local notation "Ret" => finiteCapRetained hL hδ f hf hdisj R
local notation "Disc" => finiteCapDiscarded hL hδ f hf hdisj R


variable {t₀ t₁ : ℝ}
  (G : (OrientedThreeStage.ofSmoothOrientation M o).IncomingSlab t₀ t₁)
  (gLimit : G.TerminalLimitMetric)

local notation "U" => (TopologicalSpace.Opens.mk
  (fun x : M => OrientedThreeStage.IncomingSlab.terminalRegularRegion G x)
  (OrientedThreeStage.IncomingSlab.terminalRegularRegion_isOpen G) : TopologicalSpace.Opens M)
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
  (fun x : M => G.terminalRegularRegion x))

include hs in
omit [Nonempty M] in
private theorem exists_metricCutCapEvent_boundaryFrameReversing_of_buffered_finite_caps_trace :
    letI : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
    letI : T2Space Q := (finiteCapQuotient_topological_properties ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj).2.1
    letI : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Ret := (finiteCapSelected_isManifold ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).1
    letI : IsManifold ThreeModel ∞ Disc := (finiteCapSelected_isManifold ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).2
    letI : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
    letI : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
    letI : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) :=
      retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (B : (ι × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y))
      (X : SmoothCutCapTransition (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet)
        (OrientedThreeStage.ofSmoothOrientation Disc oDisc)
        (OrientedThreeStage.ofSmoothOrientation Q oQ)),
      X.trace = (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps
        (fun b => (B b).toHomeomorph) (fun b => (a b).toHomeomorph) hboundary →
      X.boundaryFrameReversing →
      ∀ (gRet : SmoothRiemannianMetric ThreeModel Ret),
      (∀ (p : retainedCore f R) (v w : TangentSpace ((𝓡 2).prod (𝓡∂ 1)) p),
        gLimit.metric.inner (retainedCoreDomainMap f R U hRet p)
          (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (retainedCoreDomainMap f R U hRet) p v)
          (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (retainedCoreDomainMap f R U hRet) p w) =
        gRet.inner (finiteRetainedCoreInclusion hL hδ f hf hdisj R p)
          (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (finiteRetainedCoreInclusion hL hδ f hf hdisj R) p v)
          (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (finiteRetainedCoreInclusion hL hδ f hf hdisj R) p w)) →
      ∃ E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
          (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ ∧
        HEq E.transition X ∧ E.incoming = G ∧ HEq E.terminal gLimit ∧ E.outputMetric = gRet ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing := by
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
  let : T2Space Q := (finiteCapQuotient_topological_properties ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj).2.1
  let : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Ret := (finiteCapSelected_isManifold ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).1
  let : IsManifold ThreeModel ∞ Disc := (finiteCapSelected_isManifold ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).2
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
  let : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) := retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
  intro oQ oRet oDisc B a hboundary X htrace hsign gRet hTensor
  let tr := (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps
    (fun b => (B b).toHomeomorph) (fun b => (a b).toHomeomorph) hboundary
  change X.trace = tr at htrace
  rcases X with @⟨trace, hne, htube, ccharts, csmooth, cind, cbound, cincl, bcharts, bsmooth, bind,
    bbound, capsmooth, attach, hat, corepos, cappos, pres, hpreseq, prespos⟩
  dsimp only at htrace
  subst trace
  let X : SmoothCutCapTransition (OrientedThreeStage.ofSmoothOrientation M o)
      (OrientedThreeStage.ofSmoothOrientation Ret oRet)
      (OrientedThreeStage.ofSmoothOrientation Disc oDisc)
      (OrientedThreeStage.ofSmoothOrientation Q oQ) :=
    @SmoothCutCapTransition.mk (OrientedThreeStage.ofSmoothOrientation M o)
      (OrientedThreeStage.ofSmoothOrientation Ret oRet)
      (OrientedThreeStage.ofSmoothOrientation Disc oDisc)
      (OrientedThreeStage.ofSmoothOrientation Q oQ)
      tr hne htube ccharts csmooth cind cbound cincl bcharts bsmooth bind
      bbound capsmooth attach hat corepos cappos pres hpreseq prespos
  let S : Set (T).core := (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj) ⁻¹' retainedCore f R
  let e := bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R
  have hS : tr.retainedCore = S :=
    CutCapTopology.ofBufferedFiniteCaps_retainedCore hL hδ hδ1 f hf hdisj R hnontrivial
  let := bufferedRetainedCoreChartedSpace hδ hδ1 f hf hdisj R
  let : IsManifold (𝓡∂ 3) ∞ S := bufferedRetainedCore_isManifold hδ hδ1 f hf hdisj R hs
  let Ψ : C(S, U) :=
    ⟨retainedCoreDomainMap f R U hRet ∘ e,
      (retainedCoreDomainMap_isSmoothEmbedding ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj hs R U hRet).contMDiff.continuous.comp e.continuous⟩
  let Φ : C(S, Ret) :=
    ⟨finiteRetainedCoreInclusion hL hδ f hf hdisj R ∘ e,
      (finiteRetainedCoreInclusion_isSmoothEmbedding ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).contMDiff.continuous.comp e.continuous⟩
  let E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
      (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁ :=
    { discarded := OrientedThreeStage.ofSmoothOrientation Disc oDisc
      capped := OrientedThreeStage.ofSmoothOrientation Q oQ
      transition := X
      incoming := G
      terminal := gLimit
      outputMetric := gRet
      old := S
      old_compact := isCompact_bufferedRetainedCore hδ hδ1 f hf hdisj R
      old_retained := by
        intro x hx
        change x ∈ tr.retainedCore
        rwa [hS]
      oldCharts := bufferedRetainedCoreChartedSpace hδ hδ1 f hf hdisj R
      oldSmooth := bufferedRetainedCore_isManifold hδ hδ1 f hf hdisj R hs
      old_induced := bufferedRetainedCore_isSmoothEmbedding hδ hδ1 f hf hdisj R hs
      oldTerminal := Ψ
      oldTerminal_eq := fun _ => rfl
      oldOutput := Φ
      oldOutput_eq := by
        intro x
        exact finiteCapSelectedDiffeomorph_symm_retained ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj R
          (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj (e x).val) (e x).property
      old_metric_eq := bufferedRetainedCore_metric_eq hL hδ hδ1 f hf hdisj R hs U hRet gLimit.metric gRet hTensor
      old_contains_outside := fun x hx _ => hS ▸ hx
      every_child_meets_old := by
        intro c
        obtain ⟨q, rfl⟩ := ConnectedComponents.surjective_coe c
        obtain ⟨p, hp⟩ := finiteCapRetained_component_meets_original_core hL hδ f hf hdisj R q
        refine ⟨e.symm p, ?_⟩
        change ConnectedComponents.mk (finiteRetainedCoreInclusion hL hδ f hf hdisj R (e (e.symm p))) = ConnectedComponents.mk q
        rw [e.apply_symm_apply]
        exact ConnectedComponents.coe_eq_coe'.mpr hp }
  exact ⟨E, rfl, rfl, HEq.rfl, rfl, HEq.rfl, rfl, hS.symm, hsign⟩

private theorem smoothCutCapTransition_trace_heq
    {Psrc Qtgt Disc₀ Disc₁ Cap₀ Cap₁ : OrientedThreeStage.{u}}
    {X : SmoothCutCapTransition Psrc Qtgt Disc₀ Cap₀} {Y : SmoothCutCapTransition Psrc Qtgt Disc₁ Cap₁}
    (hD : Disc₀ = Disc₁) (hN : Cap₀ = Cap₁) (h : HEq X Y) : HEq X.trace Y.trace := by
  cases hD
  cases hN
  exact heq_of_eq (congrArg SmoothCutCapTransition.trace (eq_of_heq h))

include hs in
theorem exists_metricCutCapEvent_boundaryFrameReversing_of_buffered_finite_caps :
    letI : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
    letI : T2Space Q := (finiteCapQuotient_topological_properties ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj).2.1
    letI : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Ret := (finiteCapSelected_isManifold ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).1
    letI : IsManifold ThreeModel ∞ Disc := (finiteCapSelected_isManifold ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).2
    letI : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
    letI : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
    letI : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) :=
      retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
    ∀ (gRet : SmoothRiemannianMetric ThreeModel Ret),
      (∀ (p : retainedCore f R) (v w : TangentSpace ((𝓡 2).prod (𝓡∂ 1)) p),
        gLimit.metric.inner (retainedCoreDomainMap f R U hRet p)
          (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (retainedCoreDomainMap f R U hRet) p v)
          (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (retainedCoreDomainMap f R U hRet) p w) =
        gRet.inner (finiteRetainedCoreInclusion hL hδ f hf hdisj R p)
          (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (finiteRetainedCoreInclusion hL hδ f hf hdisj R) p v)
          (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (finiteRetainedCoreInclusion hL hδ f hf hdisj R) p w)) →
      ∃ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (A : (ι × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (B : (ι × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y)),
        (∀ b, A b = LinearIsometryEquiv.refl ℝ ThreeSpace ∨ A b = LinearIsometryEquiv.neg ℝ) ∧
        (∀ b x, (B b x : ThreeSpace) = A b x) ∧
        ∃ E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
          (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁,
          E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
          E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ ∧
          HEq E.transition.trace
            ((CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (a b).toHomeomorph) hboundary) ∧
          E.incoming = G ∧ HEq E.terminal gLimit ∧ E.outputMetric = gRet ∧
          E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing := by
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
  let : T2Space Q := (finiteCapQuotient_topological_properties ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj).2.1
  let : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Ret := (finiteCapSelected_isManifold ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).1
  let : IsManifold ThreeModel ∞ Disc := (finiteCapSelected_isManifold ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj hs R).2
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
  let : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) := retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
  intro gRet hTensor
  obtain ⟨oQ, oRet, oDisc, A, B, a, hboundary, hchoice, hB, X, htrace, hsign⟩ :=
    exists_smoothCutCapTransition_boundaryFrameReversing_of_buffered_finite_caps hL hδ hδ1 f hf hdisj hs R o hnontrivial
  obtain ⟨E, hD, hN, hX, hG, hLimit, hOutput, hOld, hEboundary⟩ :=
    exists_metricCutCapEvent_boundaryFrameReversing_of_buffered_finite_caps_trace hL hδ hδ1 f hf hdisj hs R o hnontrivial
      G gLimit hRet oQ oRet oDisc B a hboundary X htrace hsign gRet hTensor
  have ht : HEq E.transition.trace X.trace := smoothCutCapTransition_trace_heq hD hN hX
  exact ⟨oQ, oRet, oDisc, A, B, a, hboundary, hchoice, hB,
    E, hD, hN, ht.trans (heq_of_eq htrace), hG, hLimit, hOutput, hOld, hEboundary⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open Set Function Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private def retainedOutputSet {M Q D N : Type*}
    [TopologicalSpace M] [TopologicalSpace Q] [TopologicalSpace D] [TopologicalSpace N]
    (T : CutCapTopology M Q D N) : Set Q :=
  {q | ∃ x : T.tubes.core, T.presentation (T.capping.coreInclusion x) = Sum.inl q}

private theorem range_oldOutput_eq_retainedOutputSet
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    range E.oldOutput = retainedOutputSet E.transition.trace := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, E.oldOutput_eq x⟩
  · rintro ⟨x, hx⟩
    have hxold : x ∈ E.old := by
      rw [hOld]
      exact ⟨q, hx⟩
    refine ⟨⟨x, hxold⟩, ?_⟩
    exact Sum.inl_injective ((E.oldOutput_eq ⟨x, hxold⟩).symm.trans hx)

private theorem retainedOutputSet_eq_of_trace_heq
    {P Q D D' N N' : OrientedThreeStage.{u}}
    (hD : D = D') (hN : N = N')
    {T : CutCapTopology P.Carrier Q.Carrier D.Carrier N.Carrier}
    {T' : CutCapTopology P.Carrier Q.Carrier D'.Carrier N'.Carrier}
    (h : HEq T T') : retainedOutputSet T = retainedOutputSet T' := by
  cases hD
  cases hN
  cases eq_of_heq h
  rfl

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [CompactSpace M]
  {ι : Type} [Fintype ι] {δ : ι → ℝ} {L : ℝ}
  (hL : 0 < L) (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))
  (R : Set (ConnectedComponents (cutCore f)))
  (o : SmoothOrientation ThreeModel M)
  (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))

local notation "Q" => FiniteCapQuotient hL hδ f
  (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
private local instance : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
local notation "Ret" => finiteCapRetained hL hδ f hf hdisj R
local notation "Disc" => finiteCapDiscarded hL hδ f hf hdisj R

omit [IsManifold ThreeModel ∞ M] [CompactSpace M] in
private theorem retainedOutputSet_of_buffered_finite_caps :
    retainedOutputSet (CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial) =
      range (finiteRetainedCoreInclusion hL hδ f hf hdisj R) := by
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
  let e := bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj
  ext q
  constructor
  · rintro ⟨x, hx⟩
    have hx' : (finiteCapSelectedDiffeomorph ThreeModel finrank_threeSpace_eq_three
        hL hδ f hf hdisj R).symm
          (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj (e x)) = Sum.inl q := hx
    have heq := congrArg (finiteCapSelectedDiffeomorph ThreeModel finrank_threeSpace_eq_three
      hL hδ f hf hdisj R) hx'
    rw [Diffeomorph.apply_symm_apply, finiteCapSelectedDiffeomorph_inl] at heq
    have hxR : e x ∈ retainedCore f R := by
      change finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj (e x) ∈ Ret
      rw [heq]
      exact q.property
    refine ⟨⟨e x, hxR⟩, ?_⟩
    exact Subtype.ext heq
  · rintro ⟨x, rfl⟩
    refine ⟨e.symm x.val, ?_⟩
    change (finiteCapSelectedDiffeomorph ThreeModel finrank_threeSpace_eq_three
      hL hδ f hf hdisj R).symm
        (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj (e (e.symm x.val))) = _
    rw [e.apply_symm_apply]
    exact finiteCapSelectedDiffeomorph_symm_retained ThreeModel finrank_threeSpace_eq_three
      hL hδ f hf hdisj R
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj x.val) x.property

attribute [local instance] threeBallChartedSpace threeBall_isManifold

theorem MetricCutCapEvent.range_oldOutput_eq_of_buffered_trace :
    let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
    let : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space hL hδ f hf hdisj
    let : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
    let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
    let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
    ∀ (oQ : SmoothOrientation ThreeModel Q) (oRet : SmoothOrientation ThreeModel Ret)
      (oDisc : SmoothOrientation ThreeModel Disc)
      (B : (ι × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
      (a : (ι × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
      (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (a b y))
      {t₀ t₁ : ℝ}
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M o)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁),
      E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc →
      E.capped = OrientedThreeStage.ofSmoothOrientation Q oQ →
      HEq E.transition.trace
        ((CutCapTopology.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj R hnontrivial).reparametrizeCaps
          (fun b => (B b).toHomeomorph) (fun b => (a b).toHomeomorph) hboundary) →
      E.old = E.transition.trace.retainedCore →
      range E.oldOutput = range (finiteRetainedCoreInclusion hL hδ f hf hdisj R) := by
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space hL hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R).2
  dsimp only
  intro oQ oRet oDisc B a hboundary t₀ t₁ E hD hN htrace hOld
  rw [range_oldOutput_eq_retainedOutputSet E hOld]
  have hh := retainedOutputSet_eq_of_trace_heq hD hN htrace
  refine hh.trans ?_
  exact retainedOutputSet_of_buffered_finite_caps hL hδ hδ1 f hf hdisj R hnontrivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
