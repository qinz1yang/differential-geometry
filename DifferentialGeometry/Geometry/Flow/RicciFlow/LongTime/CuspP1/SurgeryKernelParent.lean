import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryKernelCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TubeFreeFactors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreComponentRetraction
import DifferentialGeometry.Topology.FundamentalGroup.MarkedFundamentalGroup
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding

set_option autoImplicit false

/-!
# CP1-D2 (G2a): a component of the retained core injects `π₁` into the pre-surgery slice
-/

noncomputable section
open Set Manifold DifferentialGeometry.Topology DifferentialGeometry.Topology.VanKampen
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Topology
open scoped Manifold ContDiff unitInterval

namespace GC.LongTime.CuspP1

universe u

theorem injective_comp_CPD2 {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (x : X)
    (hf : Function.Injective (FundamentalGroup.map f x))
    (hg : Function.Injective (FundamentalGroup.map g (f x))) :
    Function.Injective (FundamentalGroup.map (g.comp f) x) := by
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  exact hg.comp hf

section Parent

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

/-- inclusion of a core component into the pre-surgery slice -/
def coreComponentToParent_CPD2 (c : ConnectedComponents E.trace.tubes.core) :
    C(ComponentCarrier c, P.Carrier) :=
  ⟨fun y => (y.1 : P.Carrier), continuous_subtype_val.comp continuous_subtype_val⟩

/-- The core component `C` of the cut (all spheres of `E.tubes` removed) includes
`π₁`-injectively into the pre-surgery slice `P` (cutting along 2-spheres: free product). -/
theorem injective_coreComponent_parent_CPD2 (z : E.trace.tubes.core) :
    Function.Injective (FundamentalGroup.map
      (coreComponentToParent_CPD2 E (ConnectedComponents.mk z))
      (⟨z, rfl⟩ : ComponentCarrier (ConnectedComponents.mk z))) := by
  classical
  let T := E.trace.tubes
  have hopen : ∀ a, IsOpen (T.removedBand a) := E.removedBand_isOpen
  let : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  have hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a) :=
    E.tube_smooth
  let : SimplyConnectedSpace (Sphere 2) := sphereTwoSimplyConnectedSpace
  let : LocallyPathConnectedSpace P.Carrier :=
    ChartedSpace.locallyPathConnectedSpace ThreeSpace P.Carrier
  let : Finite T.Index := T.finiteIndex.finite
  let cc := fun a => T.middleSphereCollar a (hopen a)
  have hdisj := T.pairwise_disjoint_middleSphereCollar_range hopen
  have he : (⋃ a, Set.range (fun y : Sphere 2 =>
      T.tube a (y, (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 2))))ᶜ = T.puncturedCore := by
    rw [T.puncturedCore_eq_compl_iUnion_middleSphereCollar_zero_range hopen]
    simp only [T.middleSphereCollar_zero]
  have hzA : z.1 ∈ (⋃ a, Set.range (fun y : Sphere 2 =>
      T.tube a (y, (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 2))))ᶜ := by
    rw [he]; exact T.core_subset_puncturedCore z.2
  have hK := injective_component_compl_collars_CPD2 cc hdisj z.1 hzA
  set A : Set P.Carrier := (⋃ a, Set.range (fun y : Sphere 2 =>
      T.tube a (y, (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 2))))ᶜ with hAdef
  set K : Set P.Carrier := connectedComponentIn A z.1 with hKdef
  have hAo : IsOpen A :=
    (isClosed_iUnion_of_finite
      (fun a => (isCompact_range (cc a).continuous_e).isClosed)).isOpen_compl
  have hKo : IsOpen K := hAo.connectedComponentIn
  have hKA : K ⊆ A := connectedComponentIn_subset A z.1
  have hAcore : ∀ y ∈ A, T.coreFun ((1 : I), y) ∈ T.core := fun y hy =>
    T.coreFun_mem_core (p := ((1 : I), y)) (he ▸ hy)
  have hzK : z.1 ∈ K := mem_connectedComponentIn hzA
  have : ConnectedSpace K :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr hzA)
  -- the retraction `K → core`
  have hpc : ∀ y : K, y.1 ∈ T.puncturedCore := fun y => he ▸ hKA y.2
  have hmain : Continuous fun y : K => T.coreFun ((1 : I), (y.1 : P.Carrier)) :=
    (T.continuous_coreFun hsm).comp
      ((continuous_const.prodMk (continuous_subtype_val.subtype_mk hpc)) :
        Continuous fun y : K => ((1 : I), (⟨y.1, hpc y⟩ : T.puncturedCore)))
  let g : C(K, T.core) :=
    ⟨fun y => ⟨T.coreFun ((1 : I), y.1), hAcore y.1 (hKA y.2)⟩,
      hmain.subtype_mk fun y => hAcore y.1 (hKA y.2)⟩
  have hgz : g ⟨z.1, hzK⟩ = z := Subtype.ext (T.coreFun_eq_self_of_mem_core z.2 1)
  have hrange : ∀ y : K, ConnectedComponents.mk (g y) = ConnectedComponents.mk z := by
    intro y
    have hpc : IsPreconnected (Set.range g) := isPreconnected_range g.continuous
    have hsub := hpc.subset_connectedComponent (x := g ⟨z.1, hzK⟩) ⟨_, rfl⟩ ⟨y, rfl⟩
    rw [hgz] at hsub
    exact ConnectedComponents.coe_eq_coe'.mpr hsub
  let r : C(K, ComponentCarrier (ConnectedComponents.mk z)) :=
    ⟨fun y => ⟨g y, hrange y⟩, (g.continuous).subtype_mk _⟩
  -- the inclusion `C → K`
  have hCK : ∀ y : ComponentCarrier (ConnectedComponents.mk z), (y.1 : P.Carrier) ∈ K := by
    intro y
    have hy : y.1 ∈ connectedComponent z := ConnectedComponents.coe_eq_coe'.mp y.2
    have hpc : IsPreconnected (Subtype.val '' (connectedComponent z : Set T.core)) :=
      isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn |>.isPreconnected
    have := hpc.subset_connectedComponentIn (x := z.1) ⟨z, mem_connectedComponent, rfl⟩
      (fun w ⟨u, _, hu⟩ => hu ▸ he ▸ T.core_subset_puncturedCore u.2) ⟨y.1, hy, rfl⟩
    exact this
  let ι : C(ComponentCarrier (ConnectedComponents.mk z), K) :=
    ⟨fun y => ⟨y.1.1, hCK y⟩, (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have hri : Function.LeftInverse r ι := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact T.coreFun_eq_self_of_mem_core y.1.2 1
  have h1 : Function.Injective (FundamentalGroup.map ι ⟨z, rfl⟩) :=
    injective_fundamentalGroup_map_of_leftInverse ι r hri _
  have h2 : Function.Injective (FundamentalGroup.map (subsetToAmbient K) (ι ⟨z, rfl⟩)) := hK
  exact injective_comp_CPD2 ι (subsetToAmbient K) _ h1 h2

/-- general-basepoint form -/
theorem injective_coreComponentToParent_CPD2 (c : ConnectedComponents E.trace.tubes.core)
    (y : ComponentCarrier c) :
    Function.Injective (FundamentalGroup.map (coreComponentToParent_CPD2 E c) y) := by
  obtain ⟨z, hz⟩ := y
  subst hz
  exact injective_coreComponent_parent_CPD2 E z

end Parent

end GC.LongTime.CuspP1
