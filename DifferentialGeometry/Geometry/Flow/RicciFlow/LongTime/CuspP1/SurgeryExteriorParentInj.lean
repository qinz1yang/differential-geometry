import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorParentCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryKernelParent

set_option autoImplicit false

/-!
# CP1-D8 (G2a): exterior sphere-cut injectivity
-/

noncomputable section
open Set Manifold DifferentialGeometry.Topology DifferentialGeometry.Topology.VanKampen
open DifferentialGeometry.Topology.ThreeManifold
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Topology
open scoped Manifold ContDiff unitInterval

namespace GC.LongTime.CuspP1

universe u

theorem injective_coreComponent_exterior_CPD8 {P Q D N : OrientedThreeStage.{u}}
    (E : SmoothCutCapTransition P Q D N) (O : Set P.Carrier) (hO : IsOpen O)
    (hOc : O ⊆ E.trace.tubes.core) [LocallyPathConnectedSpace ↥Oᶜ] (z : ↥Oᶜ)
    (hz : z.1 ∈ E.trace.tubes.core) :
    Function.Injective (FundamentalGroup.map
      (subsetToAmbient (connectedComponentIn {y : ↥Oᶜ | y.1 ∈ E.trace.tubes.core} z))
      ⟨z, mem_connectedComponentIn hz⟩) := by
  classical
  let T := E.trace.tubes
  have hopen : ∀ a, IsOpen (T.removedBand a) := E.removedBand_isOpen
  let : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  have hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a) :=
    E.tube_smooth
  let : SimplyConnectedSpace (Sphere 2) := sphereTwoSimplyConnectedSpace
  let : Finite T.Index := T.finiteIndex.finite
  let cc := fun a => T.middleSphereCollar a (hopen a)
  have hnotcore : ∀ a, ∀ y ∈ T.removedBand a, y ∉ T.core := fun a y hy hc =>
    hc (mem_iUnion.mpr ⟨a, hy⟩)
  have hnotO : ∀ a, ∀ p : Sphere 2 × ℝ, (cc a).toFun p ∈ Oᶜ := by
    intro a p h
    have : (cc a).toFun p ∈ T.removedBand a := by
      rw [← T.middleSphereCollar_range a (hopen a)]; exact ⟨p, rfl⟩
    exact hnotcore a _ this (hOc h)
  let e' : T.Index → Sphere 2 → ↥Oᶜ := fun a y => ⟨(cc a).toFun (y, 0), hnotO a _⟩
  let c' : ∀ a, TwoSidedCollar (e' a) := fun a =>
    { toFun := fun p => ⟨(cc a).toFun p, hnotO a p⟩
      isOpenEmbedding_toFun := by
        refine ⟨(cc a).isOpenEmbedding_toFun.isEmbedding.codRestrict _ _, ?_⟩
        have : range (fun p : Sphere 2 × ℝ => (⟨(cc a).toFun p, hnotO a p⟩ : ↥Oᶜ)) =
            Subtype.val ⁻¹' (cc a).range := by
          ext y
          constructor
          · rintro ⟨p, rfl⟩; exact ⟨p, rfl⟩
          · rintro ⟨p, hp⟩; exact ⟨p, Subtype.ext hp⟩
        rw [this]
        exact (cc a).isOpenEmbedding_toFun.isOpen_range.preimage continuous_subtype_val
      zero_eq := fun s => rfl }
  have hrange : ∀ a, ∀ y ∈ (c' a).range, y.1 ∈ T.removedBand a := by
    rintro a y ⟨p, rfl⟩
    rw [← T.middleSphereCollar_range a (hopen a)]; exact ⟨p, rfl⟩
  have hdisj : Pairwise fun a b => Disjoint (c' a).range (c' b).range := by
    intro a b hab
    rw [Set.disjoint_left]
    intro y hya hyb
    exact Set.disjoint_left.mp (T.disjoint hab) (T.removedBand_subset_range a (hrange a y hya))
      (T.removedBand_subset_range b (hrange b y hyb))
  set A : Set ↥Oᶜ := (⋃ i, Set.range (e' i))ᶜ with hAdef
  set coreY : Set ↥Oᶜ := {y | y.1 ∈ T.core} with hcoreY
  have hcoreA : coreY ⊆ A := by
    intro y hy hyU
    obtain ⟨a, u, rfl⟩ := mem_iUnion.mp hyU
    have : (cc a).toFun (u, 0) ∈ T.removedBand a := by
      rw [← T.middleSphereCollar_range a (hopen a)]; exact ⟨_, rfl⟩
    exact hnotcore a _ this hy
  have hK := injective_component_compl_collars_CPD2 c' hdisj z (hcoreA hz)
  set K : Set ↥Oᶜ := connectedComponentIn A z with hKdef
  set C : Set ↥Oᶜ := connectedComponentIn coreY z with hCdef
  have hzK : z ∈ K := mem_connectedComponentIn (hcoreA hz)
  have hzC : z ∈ C := mem_connectedComponentIn hz
  have hCK : C ⊆ K :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn hzC
      ((connectedComponentIn_subset _ _).trans hcoreA)
  have hKA : K ⊆ A := connectedComponentIn_subset A z
  have hCc : C ⊆ coreY := connectedComponentIn_subset _ _
  let ι : C(↥C, ↥K) := ⟨fun y => ⟨y.1, hCK y.2⟩,
    (continuous_subtype_val.subtype_mk _)⟩
  have : ConnectedSpace K :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr (hcoreA hz))
  -- punctured core
  have hpc : ∀ y : K, y.1.1 ∈ T.puncturedCore := by
    intro y hmem
    obtain ⟨a, w, hw, hwy⟩ := mem_iUnion.mp hmem
    apply hKA y.2
    refine mem_iUnion.mpr ⟨a, w.1, ?_⟩
    apply Subtype.ext
    have : (cc a).toFun (w.1, 0) = T.tube a (w.1, ⟨0, by norm_num⟩) :=
      T.middleSphereCollar_zero a (hopen a) w.1
    have hw2 : w = (w.1, ⟨0, by norm_num⟩) := Prod.ext rfl (Subtype.ext hw)
    show (cc a).toFun (w.1, 0) = _
    rw [this, ← hwy, ← hw2]
  have hcoreFun : Continuous fun y : K => T.coreFun ((1 : I), y.1.1) :=
    (T.continuous_coreFun hsm).comp
      ((continuous_const.prodMk ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk hpc)) :
        Continuous fun y : K => ((1 : I), (⟨y.1.1, hpc y⟩ : T.puncturedCore)))
  have hwO : ∀ y : K, T.coreFun ((1 : I), y.1.1) ∈ Oᶜ := fun y =>
    coreFun_one_not_mem_CPD8 T hO hOc (hpc y) y.1.2
  have hwcore : ∀ y : K, T.coreFun ((1 : I), y.1.1) ∈ T.core := fun y =>
    T.coreFun_mem_core (p := ((1 : I), y.1.1)) (hpc y)
  let g : C(↥K, ↥Oᶜ) := ⟨fun y => ⟨T.coreFun ((1 : I), y.1.1), hwO y⟩,
    hcoreFun.subtype_mk _⟩
  have hgz : g ⟨z, hzK⟩ = z :=
    Subtype.ext (T.coreFun_eq_self_of_mem_core hz 1)
  have hgrange : ∀ y : K, g y ∈ C := by
    intro y
    have hpcon : IsPreconnected (Set.range g) := isPreconnected_range g.continuous
    have := hpcon.subset_connectedComponentIn (x := g ⟨z, hzK⟩) ⟨_, rfl⟩
      (show Set.range g ⊆ coreY by rintro _ ⟨w, rfl⟩; exact hwcore w) ⟨y, rfl⟩
    rw [hgz] at this
    exact this
  let r : C(↥K, ↥C) := ⟨fun y => ⟨g y, hgrange y⟩, g.continuous.subtype_mk _⟩
  have hri : Function.LeftInverse r ι := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact T.coreFun_eq_self_of_mem_core (hCc y.2) 1
  have h1 : Function.Injective (FundamentalGroup.map ι ⟨z, hzC⟩) :=
    injective_fundamentalGroup_map_of_leftInverse ι r hri _
  have h2 : Function.Injective (FundamentalGroup.map (subsetToAmbient K) (ι ⟨z, hzC⟩)) := hK
  exact injective_comp_CPD2 ι (subsetToAmbient K) _ h1 h2

end GC.LongTime.CuspP1
