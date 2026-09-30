import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCollaredStarCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MiddleSphereSliceEmbedding
import DifferentialGeometry.Topology.VanKampen.TwoCoverChain
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

noncomputable section

open Set Topology Manifold
open scoped Manifold ContDiff ContinuousMap unitInterval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

namespace TubeSystem

variable {M : Type u} [TopologicalSpace M] (T : TubeSystem M)

theorem tubeTop_inter_tubeBot (a : T.Index) :
    T.tubeTop a ∩ T.tubeBot a = T.middleSphere a := by
  rw [tubeTop, tubeBot, middleSphere, ← Set.image_inter (T.embedding a).injective]
  congr 1
  ext z
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨le_of_eq h.symm, le_of_eq h⟩⟩

theorem tubeTop_union_tubeBot (a : T.Index) :
    T.tubeTop a ∪ T.tubeBot a = Set.range (T.tube a) := by
  have h : ({z : TubeDomain | 0 ≤ z.2.1} ∪ {z : TubeDomain | z.2.1 ≤ 0}) = univ := by
    ext z
    exact ⟨fun _ => trivial, fun _ => (le_total z.2.1 0).elim Or.inr Or.inl⟩
  rw [tubeTop, tubeBot, ← Set.image_union, h, Set.image_univ]

theorem positiveTube_inter_negativeTube (a : T.Index) :
    T.positiveTube a ∩ T.negativeTube a = ∅ := by
  rw [positiveTube, negativeTube, ← Set.image_inter (T.embedding a).injective]
  rw [Set.image_eq_empty]
  ext z
  constructor
  · intro h
    have h1 : (0 : ℝ) < z.2.1 := h.1
    have h2 : (z.2.1 : ℝ) < 0 := h.2
    exact absurd h2 (not_lt.mpr h1.le)
  · intro h
    exact (h : False).elim

section Alignment

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] (T : TubeSystem M)

private theorem eq_of_continuous_bool_of_preconnectedSpace {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {f : X → Bool} (hf : Continuous f) (x y : X) : f x = f y := by
  have hcl : IsClopen (f ⁻¹' ({true} : Set Bool)) := (isClopen_discrete _).preimage hf
  rcases disjoint_or_subset_of_isClopen (isPreconnected_univ (α := X)) hcl with h | h
  · have hx : f x ≠ true := fun hx => Set.disjoint_left.mp h (mem_univ x) hx
    have hy : f y ≠ true := fun hy => Set.disjoint_left.mp h (mem_univ y) hy
    rw [Bool.eq_false_of_not_eq_true hx, Bool.eq_false_of_not_eq_true hy]
  · have hx : f x = true := h (mem_univ x)
    have hy : f y = true := h (mem_univ y)
    rw [hx, hy]

omit [IsManifold ThreeModel ∞ M] in
theorem puncturedCoreComponent_eq_connectedComponent
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    [LocallyConnectedSpace ↥T.core] (c : ConnectedComponents ↥T.core) :
    ∃ u : ↥T.puncturedCore, T.puncturedCoreComponent c = connectedComponent u := by
  classical
  let φ : ↥T.puncturedCore → ConnectedComponents ↥T.core := fun u =>
    ConnectedComponents.mk (T.coreRetraction hsm u)
  have hφ : Continuous φ :=
    ConnectedComponents.continuous_coe.comp (T.coreRetraction hsm).continuous
  have hA : T.puncturedCoreComponent c = φ ⁻¹' {c} := by
    ext u
    simp only [TubeSystem.puncturedCoreComponent, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff, φ, TubeSystem.coreRetraction, ContinuousMap.coe_mk]
  have hclopen : IsClopen (T.puncturedCoreComponent c) := by
    rw [hA]
    exact (isClopen_discrete {c}).preimage hφ
  have hpre : IsPreconnected (T.puncturedCoreComponent c) := by
    refine isPreconnected_of_forall_constant fun f hf x hx y hy => ?_
    have hfr : Continuous fun z : ↥(T.puncturedCoreComponent c) => f (z.1 : ↥T.puncturedCore) :=
      hf.domRestrict
    have hstep : ∀ z : ↥(T.puncturedCoreComponent c),
        f (z.1 : ↥T.puncturedCore) =
          f ((T.coreComponentInclusion c (T.coreComponentRetraction hsm c z)).1 :
            ↥T.puncturedCore) := by
      intro z
      have hcont : Continuous fun t : I =>
          f (((T.coreComponentHomotopy hsm c) (t, z)).1 : ↥T.puncturedCore) :=
        hfr.comp (((T.coreComponentHomotopy hsm c).continuous_toFun).comp
          (continuous_id.prodMk continuous_const))
      have h01 := eq_of_continuous_bool_of_preconnectedSpace hcont (0 : I) 1
      have h0 : (((T.coreComponentHomotopy hsm c) ((0 : I), z)).1 : ↥T.puncturedCore) =
          (z.1 : ↥T.puncturedCore) :=
        congrArg Subtype.val ((T.coreComponentHomotopy hsm c).map_zero_left z)
      have h1 : (((T.coreComponentHomotopy hsm c) ((1 : I), z)).1 : ↥T.puncturedCore) =
          ((T.coreComponentInclusion c (T.coreComponentRetraction hsm c z)).1 :
            ↥T.puncturedCore) := by
        have hmap := (T.coreComponentHomotopy hsm c).map_one_left z
        simp only [ContinuousMap.comp_apply] at hmap
        exact congrArg Subtype.val hmap
      rwa [h0, h1] at h01
    have hR : ∀ v w : ComponentCarrier c,
        f ((T.coreComponentInclusion c v).1 : ↥T.puncturedCore) =
          f ((T.coreComponentInclusion c w).1 : ↥T.puncturedCore) := by
      have hpc : PreconnectedSpace (ComponentCarrier c) := by
        obtain ⟨x₀, rfl⟩ := ConnectedComponents.surjective_coe c
        change PreconnectedSpace
          ↥(ConnectedComponents.mk ⁻¹'
            ({ConnectedComponents.mk x₀} : Set (ConnectedComponents ↥T.core)))
        exact (connectedComponents_preimage_singleton (x := x₀)).symm ▸
          Subtype.preconnectedSpace (isPreconnected_connectedComponent (x := x₀))
      have hcomp : Continuous fun v : ComponentCarrier c =>
          f ((T.coreComponentInclusion c v).1 : ↥T.puncturedCore) :=
        hfr.comp (T.coreComponentInclusion c).continuous
      exact fun v w =>
        @eq_of_continuous_bool_of_preconnectedSpace (ComponentCarrier c) _ hpc _ hcomp v w
    calc f x = f ((T.coreComponentInclusion c
            (T.coreComponentRetraction hsm c ⟨x, hx⟩)).1 : ↥T.puncturedCore) := hstep ⟨x, hx⟩
      _ = f ((T.coreComponentInclusion c
            (T.coreComponentRetraction hsm c ⟨y, hy⟩)).1 : ↥T.puncturedCore) := hR _ _
      _ = f y := (hstep ⟨y, hy⟩).symm
  obtain ⟨x₀, hx₀⟩ := ConnectedComponents.surjective_coe c
  have hu : (⟨(x₀ : M), T.core_subset_puncturedCore x₀.2⟩ : ↥T.puncturedCore) ∈
      T.puncturedCoreComponent c :=
    T.mem_puncturedCoreComponent_of_mem_connectedComponents hx₀
  exact ⟨_, Set.Subset.antisymm (hpre.subset_connectedComponent hu)
    (hclopen.connectedComponent_subset hu)⟩

omit [IsManifold ThreeModel ∞ M] in
theorem simplyConnectedSpace_puncturedCoreComponent_of_simplyConnectedSpace
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    [LocallyConnectedSpace ↥T.core] [SimplyConnectedSpace ↥T.puncturedCore]
    (c : ConnectedComponents ↥T.core) :
    SimplyConnectedSpace ↥(T.puncturedCoreComponent c) := by
  obtain ⟨u, hu⟩ := T.puncturedCoreComponent_eq_connectedComponent hsm c
  rw [hu, PreconnectedSpace.connectedComponent_eq_univ u]
  exact (Homeomorph.Set.univ ↥T.puncturedCore).toHomotopyEquiv.simplyConnectedSpace

omit [IsManifold ThreeModel ∞ M] in
theorem simplyConnectedSpace_puncturedCoreComponent_of_isEmpty_index
    [LocallyConnectedSpace ↥T.core] [IsEmpty T.Index] [SimplyConnectedSpace M]
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    (c : ConnectedComponents ↥T.core) :
    SimplyConnectedSpace ↥(T.puncturedCoreComponent c) :=
  @simplyConnectedSpace_puncturedCoreComponent_of_simplyConnectedSpace M _ _ _
    T hsm inferInstance
    ((simplyConnectedSpace_puncturedCore_iff_of_isEmpty T).mpr inferInstance) c

end Alignment

section CutChain

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] (T : TubeSystem M)

structure PuncturedCoreCutChain (c : ConnectedComponents ↥T.core) where
  n : ℕ
  W : ℕ → Set ↥T.puncturedCore
  L : ℕ → Set ↥T.puncturedCore
  R : ℕ → Set ↥T.puncturedCore
  isOpen_L : ∀ k, IsOpen (L k)
  isOpen_R : ∀ k, IsOpen (R k)
  cover : ∀ k, W k ⊆ L k ∪ R k
  next : ∀ k, W (k + 1) = W k ∩ L k ∨ W (k + 1) = W k ∩ R k
  simplyConnected_overlap : ∀ k, SimplyConnectedSpace ↥(W k ∩ (L k ∩ R k))
  pathConnected_left : ∀ k, PathConnectedSpace ↥(W k ∩ L k)
  pathConnected_right : ∀ k, PathConnectedSpace ↥(W k ∩ R k)
  terminal : W n = T.puncturedCoreComponent c

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem simplyConnectedSpace_puncturedCoreComponent_of_cutChain
    {c : ConnectedComponents ↥T.core} (d : PuncturedCoreCutChain T c)
    (hbase : SimplyConnectedSpace ↥(d.W 0)) :
    SimplyConnectedSpace ↥(T.puncturedCoreComponent c) := by
  rw [← d.terminal]
  exact DifferentialGeometry.Topology.VanKampen.simplyConnectedSpace_of_twoCover_chain
    d.W d.L d.R d.isOpen_L d.isOpen_R d.cover d.next hbase
    d.simplyConnected_overlap d.pathConnected_left d.pathConnected_right d.n

end CutChain

end TubeSystem

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

def PuncturedCoreCutChainProducer : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
      ∃ d : E.trace.tubes.PuncturedCoreCutChain (E.childCoreComponent c),
        SimplyConnectedSpace ↥(d.W 0)

theorem middleSphereCuttingSeparation_of_cutChainProducer
    (h : E.PuncturedCoreCutChainProducer) : E.middleSphereCuttingSeparation :=
  fun c hparent =>
    (h c hparent).elim fun d hbase =>
      E.trace.tubes.simplyConnectedSpace_puncturedCoreComponent_of_cutChain d hbase

theorem componentwisePuncturedCoreOfParent_of_cutChainProducer
    (h : E.PuncturedCoreCutChainProducer) : E.ComponentwisePuncturedCoreOfParent :=
  E.middleSphereCuttingSeparation_of_cutChainProducer h

theorem childCoreSimplyConnectedOfParent_of_cutChainProducer
    (h : E.PuncturedCoreCutChainProducer) : E.childCoreSimplyConnectedOfParent :=
  E.childCoreSimplyConnectedOfParent_of_middleSphereCuttingSeparation
    (E.middleSphereCuttingSeparation_of_cutChainProducer h)

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
