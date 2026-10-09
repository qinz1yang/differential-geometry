import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ComparisonClassDegreeData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegreeCoreReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MiddleSphereSliceEmbedding

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}

namespace ComparisonSupport

variable {c : ConnectedComponents (H.stage i.succ).Carrier}

theorem localTerminalDistanceControl_of_collapseDegreeLipschitzInput
    {K : G.ComparisonSupport c} (hlip : CollapseDegreeLipschitzInput K) :
    K.LocalTerminalDistanceControl K.canonicalWholeParentMap := by
  intro x hx
  refine ⟨{y : (G.Parent c).Carrier | y.1 ∈ (H.event i).incoming.terminalRegularRegion},
    ((H.event i).incoming.terminalRegularRegion_isOpen.preimage continuous_subtype_val).mem_nhds
      (K.support_terminal x hx), fun _ hy => hy, ?_⟩
  intro y _ z _ hy hz
  exact hlip y z hy hz

theorem rfs_collapse_degree_of_lipschitzInput_and_classGenerator
    {K : G.ComparisonSupport c} (hlip : CollapseDegreeLipschitzInput K)
    (a : IntegralHomology (G.Parent c).Carrier 3) (b : IntegralHomology (G.Child c).Carrier 3)
    {k : ℤ} (hmap : integralHomologyMap 3 K.canonicalWholeParentMap a = k • b)
    (hgen : K.CollapseClassGenerator a) (hk : 0 < k) :
    K.LocalTerminalLengthControl K.canonicalWholeParentMap ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.canonicalWholeParentMap y = K.canonicalWholeParentMap x) ∧
    (∀ x : G.transition.ChildCore c,
      K.canonicalWholeParentMap (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 K.canonicalWholeParentMap a = b ∧
    Function.Surjective K.canonicalWholeParentMap :=
  K.rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator a b
    (K.localTerminalDistanceControl_of_collapseDegreeLipschitzInput hlip) hmap hgen hk

end ComparisonSupport

theorem rfs_child_comparison_of_inputs
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3)
    (h : G.ChildComparisonInputs a b) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.canonicalWholeParentMap) ∧
      (∀ c, integralHomologyMap 3 (f c) (a c) = b c) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨f, hf, hlen⟩ :=
    G.rfs_child_comparison_metric_of_local_length_comparison h.Kc h.localLengthComparison
  refine ⟨f, fun c => ⟨h.Kc c, hf c⟩, fun c => ?_, hlen⟩
  rw [hf c]
  exact h.integralHomologyMap_eq c

end GeometricCutoffRecord

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem middleSphereCuttingSeparation_iff_componentwisePuncturedCoreOfParent :
    E.middleSphereCuttingSeparation ↔ E.ComponentwisePuncturedCoreOfParent :=
  Iff.rfl

theorem child_simplyConnected_of_collaredStarCoverProducer_and_middleSphereCuttingSeparation
    (hcover : E.childCollaredStarCoverProducer) (hsep : E.middleSphereCuttingSeparation)
    (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (Q.component c).Carrier :=
  E.child_simplyConnected_of_puncturedCoreProducer hcover
    (E.componentwisePuncturedCoreOfParent_of_middleSphereCuttingSeparation hsep) c

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localTerminalDistanceControl_of_collapseDegreeLipschitzInput,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_lipschitzInput_and_classGenerator,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_inputs,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.middleSphereCuttingSeparation_iff_componentwisePuncturedCoreOfParent,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_collaredStarCoverProducer_and_middleSphereCuttingSeparation] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected dependencies for {n}: {axs}"
