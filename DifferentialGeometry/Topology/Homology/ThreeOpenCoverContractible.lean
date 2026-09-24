import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.Homology.ContractiblePair
import DifferentialGeometry.Topology.Homology.NoncompactTopHomologyVanishing
import DifferentialGeometry.Topology.Homology.SecondHomologyVanishingClosedThreeManifold
import DifferentialGeometry.Topology.Homology.SpherePuncture
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

def ThreeOpenCoverContractible (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ K : Set X, IsCompact K → ∃ U : Fin 3 → Set X,
    (∀ i, IsOpen (U i)) ∧
    (∀ s : Finset (Fin 3), s.Nonempty → ContractibleSpace ↥(⋂ i ∈ s, U i)) ∧
    K ⊆ ⋃ i, U i

theorem threeOpenCoverContractible_of_contractibleSpace [ContractibleSpace X] :
    ThreeOpenCoverContractible X := by
  intro K _
  refine ⟨fun _ => univ, fun _ => isOpen_univ, fun s _ => ?_,
    fun x _ => Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩⟩
  have hEq : (⋂ i ∈ s, (univ : Set X)) = univ := by simp
  exact hEq.symm ▸ (Homeomorph.Set.univ X).contractibleSpace

theorem threeOpenCoverContractible_of_forall_exists_contractible_superset
    (h : ∀ K : Set X, IsCompact K →
      ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ContractibleSpace ↥V) :
    ThreeOpenCoverContractible X := by
  intro K hK
  obtain ⟨V, hVopen, hKV, hV⟩ := h K hK
  refine ⟨fun _ => V, fun _ => hVopen, fun s hs => ?_,
    fun x hx => Set.mem_iUnion.mpr ⟨0, hKV hx⟩⟩
  obtain ⟨i, hi⟩ := hs
  have hEq : (⋂ j ∈ s, V) = V := by
    ext x
    constructor
    · intro hx
      exact (Set.mem_iInter.mp (Set.mem_iInter.mp hx i)) hi
    · intro hx
      exact Set.mem_iInter.mpr fun j => Set.mem_iInter.mpr fun _ => hx
  exact hEq.symm ▸ hV

theorem threeOpenCoverContractible_of_homeomorph {Y : Type u} [TopologicalSpace Y]
    (e : X ≃ₜ Y) (h : ThreeOpenCoverContractible Y) : ThreeOpenCoverContractible X := by
  intro K hK
  obtain ⟨U, hUopen, hUint, hKU⟩ := h (e '' K) (hK.image e.continuous)
  refine ⟨fun i => e ⁻¹' U i, fun i => (hUopen i).preimage e.continuous, fun s hs => ?_,
    fun x hx => ?_⟩
  · have hpre : (⋂ i ∈ s, e ⁻¹' U i) = e ⁻¹' (⋂ i ∈ s, U i) := by
      ext x
      simp
    obtain ⟨hY⟩ := (hUint s hs).hequiv_unit'
    exact ⟨⟨((e.sets hpre).toHomotopyEquiv).trans hY⟩⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hKU ⟨x, hx, rfl⟩)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

theorem threeOpenCoverContractible_iff_of_homeomorph {Y : Type u} [TopologicalSpace Y]
    (e : X ≃ₜ Y) : ThreeOpenCoverContractible X ↔ ThreeOpenCoverContractible Y :=
  ⟨fun h => threeOpenCoverContractible_of_homeomorph e.symm h,
    fun h => threeOpenCoverContractible_of_homeomorph e h⟩

theorem threeOpenCoverContractible_of_three_open_cover_contractible (U : Fin 3 → Set X)
    (hopen : ∀ i, IsOpen (U i))
    (hint : ∀ s : Finset (Fin 3), s.Nonempty → ContractibleSpace ↥(⋂ i ∈ s, U i))
    (hcov : (⋃ i, U i) = univ) : ThreeOpenCoverContractible X := by
  intro K _
  exact ⟨U, hopen, hint, fun x _ => by rw [hcov]; exact Set.mem_univ x⟩

theorem threeOpenCoverContractible_euclideanSpaceThree :
    ThreeOpenCoverContractible (EuclideanSpace ℝ (Fin 3)) :=
  threeOpenCoverContractible_of_contractibleSpace

theorem threeOpenCoverContractible_compl_singleton_sphereThree (v : SphereThree) :
    ThreeOpenCoverContractible ↥({v}ᶜ : Set SphereThree) :=
  @threeOpenCoverContractible_of_contractibleSpace _
    inferInstance (spherePuncture_contractible v)

theorem not_exists_two_open_cover_contractible_sphereThree :
    ¬ ∃ A B : Set SphereThree, IsOpen A ∧ IsOpen B ∧ A ∪ B = univ ∧
      ContractibleSpace ↥A ∧ ContractibleSpace ↥B ∧
      ContractibleSpace ↥(subspaceIntersection A B) := by
  rintro ⟨A, B, hA, hB, hcover, hAc, hBc, hIc⟩
  refine not_subsingleton_integralSingularHomology_three_sphereThree ?_
  have hI : Subsingleton (integralSingularHomology 2 ↥(subspaceIntersection A B)) :=
    @integralSingularHomology_subsingleton_of_contractible 2 (by norm_num)
      ↥(subspaceIntersection A B) inferInstance hIc
  exact ⟨fun a b =>
    (@integralHomologyContractibleCoverEquiv SphereThree _ 1 A B hAc hBc hA hB hcover).injective
      (hI.allEq _ _)⟩

theorem not_forall_exists_contractible_superset_sphereThree :
    ¬ ∀ K : Set SphereThree, IsCompact K → ∃ V : Set SphereThree,
      IsOpen V ∧ K ⊆ V ∧ ContractibleSpace ↥V := by
  intro h
  obtain ⟨V, -, hVuniv, hV⟩ := h univ isCompact_univ
  have hEq : V = univ := Set.Subset.antisymm (Set.subset_univ _) hVuniv
  let e : ↥V ≃ₜ SphereThree :=
    { toFun := fun x => x.1
      invFun := fun y => ⟨y, by rw [hEq]; exact Set.mem_univ y⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun :=
        continuous_id.subtype_mk fun y => by rw [hEq]; exact Set.mem_univ y }
  have hsub : Subsingleton (integralSingularHomology 3 ↥V) :=
    @integralSingularHomology_subsingleton_of_contractible 3 (by norm_num) ↥V inferInstance hV
  exact not_subsingleton_integralSingularHomology_three_sphereThree
    (@subsingleton_integralSingularHomology_of_homotopyEquiv _ _ _ _ 3 e.toHomotopyEquiv hsub)

end DifferentialGeometry.Topology
