import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryKernelParent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCapGroups

set_option autoImplicit false

/-!
# CP1-D2 (G2b): a retained core component injects `π₁` into the post-surgery slice
-/

noncomputable section
open Set Manifold DifferentialGeometry.Topology DifferentialGeometry.Topology.VanKampen
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Topology GC.Surgery

namespace GC.LongTime.CuspP1

universe u

/-- The inclusion of a clopen subset `π₁`-injects. -/
theorem injective_clopen_subtype_CPD2 {Y : Type*} [TopologicalSpace Y] (S : Set Y)
    (hS : IsClopen S) (x : S) :
    Function.Injective (FundamentalGroup.map (subsetToAmbient S) x) := by
  classical
  have hcont : Continuous (Set.piecewise S (id : Y → Y) (fun _ => x.1)) := by
    apply Continuous.piecewise
    · intro y hy
      rw [hS.frontier_eq] at hy
      exact hy.elim
    · exact continuous_id
    · exact continuous_const
  let r : C(Y, S) :=
    ⟨fun y => if h : y ∈ S then ⟨y, h⟩ else x, by
      apply continuous_induced_rng.2
      refine hcont.congr fun y => ?_
      by_cases h : y ∈ S <;> simp [h, Set.piecewise]⟩
  refine injective_fundamentalGroup_map_of_leftInverse (subsetToAmbient S) r ?_ x
  intro y
  apply Subtype.ext
  simp [r, subsetToAmbient]

section Child

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

/-- A component of a (locally connected) post-surgery slice is clopen. -/
theorem isClopen_component_CPD2 (c : ConnectedComponents Q.Carrier) :
    IsClopen {y : Q.Carrier | ConnectedComponents.mk y = c} := by
  have : LocallyConnectedSpace Q.Carrier := ChartedSpace.locallyConnectedSpace ThreeSpace Q.Carrier
  have : DiscreteTopology (ConnectedComponents Q.Carrier) := inferInstance
  exact (isClopen_discrete ({c} : Set (ConnectedComponents Q.Carrier))).preimage
    ConnectedComponents.continuous_coe

/-- core component `→` post-surgery slice -/
def childCoreToQ_CPD2 (c : ConnectedComponents Q.Carrier) : C(E.ChildCore c, Q.Carrier) :=
  ⟨fun y => (E.childCoreInclusion c y).1,
    continuous_subtype_val.comp (E.childCoreInclusion c).continuous⟩

theorem injective_childCoreInclusion_CPD2 (c : ConnectedComponents Q.Carrier)
    (x : E.ChildCore c) :
    Function.Injective (FundamentalGroup.map (E.childCoreInclusion c) x) := by
  classical
  let r : ℝ := 1 / 2
  have hr : 0 ≤ r := by norm_num [r]
  have hr1 : r < 1 := by norm_num [r]
  let H := E.childCoreNeighborhoodHomotopyEquiv c hr hr1
  let : PathConnectedSpace (E.ChildCore c) := childCore_pathConnected E c
  let : PathConnectedSpace (E.childCoreNeighborhood c r) :=
    ThreeManifold.pathConnectedSpace_of_homotopyEquiv H
  have hsc : ∀ b : E.ChildCapBoundary c,
      SimplyConnectedSpace ↥(E.childCoreNeighborhood c r ∩ E.childCapInterior c b) :=
    fun b => E.simplyConnectedSpace_childCoreNeighborhood_inter_childCapInterior c b hr1
  let j : C(E.ChildCore c, E.childCoreNeighborhood c r) :=
    E.childCoreInclusionRestrict c (E.range_childCoreInclusion_subset_childCoreNeighborhood c hr1)
  have hU : Function.Injective (FundamentalGroup.map
      (subsetToAmbient (E.childCoreNeighborhood c r)) (j x)) :=
    injective_of_thin_overlap_CPD2 (E.childCoreNeighborhood c r)
      (⋃ b : E.ChildCapBoundary c, E.childCapInterior c b)
      (E.isOpen_childCoreNeighborhood c r)
      (isOpen_iUnion fun b => E.isOpen_childCapInterior c b)
      (E.childCoreNeighborhood_union_iUnion_childCapInterior c hr1)
      (fun b : E.ChildCapBoundary c => E.childCoreNeighborhood c r ∩ E.childCapInterior c b)
      (fun b => (E.isOpen_childCoreNeighborhood c r).inter (E.isOpen_childCapInterior c b))
      (fun b b' hbb => (E.pairwise_disjoint_childCapInterior c hbb).mono inter_subset_right
        inter_subset_right)
      hsc (by rw [inter_iUnion]) (j x)
  have hH : Function.Injective (FundamentalGroup.map j x) :=
    injective_fundamentalGroup_map_of_leftInverse _
      (E.childCoreNeighborhoodRetraction c hr hr1)
      (fun y => E.childCoreNeighborhoodRetraction_childCoreInclusion c hr hr1 y) x
  exact injective_comp_CPD2 j (subsetToAmbient (E.childCoreNeighborhood c r)) x hH hU

theorem injective_childCoreToQ_CPD2 (c : ConnectedComponents Q.Carrier) (x : E.ChildCore c) :
    Function.Injective (FundamentalGroup.map (childCoreToQ_CPD2 E c) x) := by
  have h1 := injective_childCoreInclusion_CPD2 E c x
  have h2 := injective_clopen_subtype_CPD2 {y : Q.Carrier | ConnectedComponents.mk y = c}
    (isClopen_component_CPD2 c) (E.childCoreInclusion c x)
  exact injective_comp_CPD2 (E.childCoreInclusion c)
    (subsetToAmbient {y : Q.Carrier | ConnectedComponents.mk y = c}) x h1 h2

end Child

end GC.LongTime.CuspP1
