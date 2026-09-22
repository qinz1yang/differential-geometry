import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedMetricCutCapEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MetricCutCapEvent

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem codRestrict_metric_eq_of_heq
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    {S : Type*} [TopologicalSpace S] [ChartedSpace EuclideanHalfSpaceProdModel S]
    {U V : TopologicalSpace.Opens M} (hUV : U = V)
    {gU : SmoothRiemannianMetric ThreeModel U} {gV : SmoothRiemannianMetric ThreeModel V}
    (hg : HEq gU gV) (F : S → M) (hU : ∀ x, F x ∈ U) (hV : ∀ x, F x ∈ V)
    (x : S) (v w : TangentSpace ((𝓡 2).prod (𝓡∂ 1)) x) :
    gU.inner ⟨F x, hU x⟩
      (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (fun y => (⟨F y, hU y⟩ : U)) x v)
      (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (fun y => (⟨F y, hU y⟩ : U)) x w) =
    gV.inner ⟨F x, hV x⟩
      (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (fun y => (⟨F y, hV y⟩ : V)) x v)
      (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (fun y => (⟨F y, hV y⟩ : V)) x w) := by
  subst V
  have heq : gU = gV := eq_of_heq hg
  subst gV
  rfl

private theorem terminalLimitMetric_metric_heq
    {P : OrientedThreeStage} {a s : ℝ} {G H : P.IncomingSlab a s}
    {L : G.TerminalLimitMetric} {K : H.TerminalLimitMetric}
    (hG : G = H) (h : HEq L K) : HEq L.metric K.metric := by
  subst H
  exact heq_of_eq (congrArg OrientedThreeStage.IncomingSlab.TerminalLimitMetric.metric (eq_of_heq h))

universe u

attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable {M : Type u} [hTopology : TopologicalSpace M] [T2Space M] [hCharts : ChartedSpace ThreeSpace M]
  [hSmooth : IsManifold ThreeModel ∞ M] [CompactSpace M] [Nonempty M]
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

local notation "U₀" => DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion (M := M) (I := ThreeModel)
  (SolutionFamily.metric (SolutionOn.base (OrientedThreeStage.IncomingSlab.flow G))) t₀ t₁
local notation "Uc" => (TopologicalSpace.Opens.mk
  (fun x : M => OrientedThreeStage.IncomingSlab.terminalRegularRegion G x)
  (OrientedThreeStage.IncomingSlab.terminalRegularRegion_isOpen G) : TopologicalSpace.Opens M)
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
  (DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion (M := M) (I := ThreeModel) G.flow.base.metric t₀ t₁))

include hs in
omit [Nonempty M] in
theorem exists_metricCutCapEvent_boundaryFrameReversing_of_metricCutCapEventOn :
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
    ∀ (gBar : SmoothRiemannianMetric ThreeModel U₀)
      (gRet : SmoothRiemannianMetric ThreeModel Ret),
      MetricCutCapEventOn ThreeModel t₀ t₁ G.lt G.flow gBar finrank_threeSpace_eq_three
        hL hδ f hf hdisj hs hδ1 R hRet o gRet →
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
          E.incoming = G ∧ HEq E.terminal.metric gBar ∧ E.outputMetric = gRet ∧
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
  intro gBar gRet hEvent
  obtain ⟨_, hTerminal, hGeometry, _, hTensor, _⟩ := hEvent
  let : Nonempty M := by
    obtain ⟨_, _, _, _, _, _, hFinite, _⟩ := hGeometry
    exact hFinite.1
  let L := G.terminalLimitMetricOfIsTerminalLimitMetric gBar hTerminal
  have hMetric : HEq L.metric gBar :=
    G.terminalLimitMetricOfIsTerminalLimitMetric_metric_heq gBar hTerminal
  have hU := G.terminalRegularOpen_eq
  have hRet' : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
      (fun x : M => G.terminalRegularRegion x) := by
    intro p hp
    change p.val ∈ G.terminalRegularOpen
    rw [hU]
    exact hRet hp
  have hTensor' := fun (p : retainedCore f R) (v w : TangentSpace ((𝓡 2).prod (𝓡∂ 1)) p) =>
    (@codRestrict_metric_eq_of_heq M hTopology hCharts hSmooth (retainedCore f R) _ _ _ _ hU L.metric gBar hMetric (fun q : retainedCore f R => q.val.val)
      (fun q => hRet' q.property) (fun q => hRet q.property) p v w).trans (hTensor p v w)
  obtain ⟨oQ, oRet, oDisc, A, B, a, hboundary, hchoice, hB, E, hD, hN, htrace, hG, hL, hOutput, hOld, hEboundary⟩ :=
    exists_metricCutCapEvent_boundaryFrameReversing_of_buffered_finite_caps hL hδ hδ1 f hf hdisj hs R o hnontrivial
      G L hRet' gRet hTensor'
  exact ⟨oQ, oRet, oDisc, A, B, a, hboundary, hchoice, hB, E, hD, hN, htrace, hG,
    (terminalLimitMetric_metric_heq hG hL).trans hMetric, hOutput, hOld, hEboundary⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
