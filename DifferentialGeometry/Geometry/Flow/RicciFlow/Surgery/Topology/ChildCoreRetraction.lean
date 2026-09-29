import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreDeformationRetract
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapTransitionSkeleton
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false

noncomputable section

open Set Topology Manifold
open scoped Manifold ContDiff ContinuousMap unitInterval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace TubeSystem

section Retraction

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] (T : TubeSystem M)

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

def coreInclusion : C(↥T.core, ↥T.puncturedCore) where
  toFun x := ⟨x.1, T.core_subset_puncturedCore x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def coreRetraction
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    C(↥T.puncturedCore, ↥T.core) where
  toFun u := ⟨T.coreFun ((1 : I), (u : M)),
    T.coreFun_mem_core (p := ((1 : I), (u : M))) u.2⟩
  continuous_toFun := by
    have hpair : Continuous fun u : ↥T.puncturedCore => ((1 : I), u) :=
      (continuous_const : Continuous fun _ : ↥T.puncturedCore => (1 : I)).prodMk
        (continuous_id : Continuous fun u : ↥T.puncturedCore => u)
    have hmain : Continuous fun u : ↥T.puncturedCore => T.coreFun ((1 : I), (u : M)) :=
      Continuous.comp
        (g := fun p : I × ↥T.puncturedCore => T.coreFun (p.1, (p.2 : M)))
        (f := fun u : ↥T.puncturedCore => ((1 : I), u))
        (T.continuous_coreFun hsm) hpair
    exact hmain.subtype_mk _

omit [IsManifold ThreeModel ∞ M] in
theorem coreRetraction_comp_coreInclusion
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    (coreRetraction T hsm).comp (coreInclusion T) = ContinuousMap.id ↥T.core := by
  ext x
  simpa [ContinuousMap.comp_apply, coreRetraction, coreInclusion]
    using T.coreFun_eq_self_of_mem_core x.2 1

def coreHomotopy
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥T.puncturedCore)
      ((coreInclusion T).comp (coreRetraction T hsm)) where
  toFun p := ⟨T.coreFun (p.1, (p.2 : M)), T.coreFun_mem_puncturedCore p.2.2⟩
  continuous_toFun := (T.continuous_coreFun hsm).subtype_mk _
  map_zero_left u := Subtype.ext (T.coreFun_zero ((0 : I), (u : M)))
  map_one_left u := by
    apply Subtype.ext
    simp [ContinuousMap.comp_apply, coreRetraction, coreInclusion]

omit [IsManifold ThreeModel ∞ M] in
theorem coreInclusion_comp_coreRetraction_homotopic_id
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    ((coreInclusion T).comp (coreRetraction T hsm)).Homotopic
      (ContinuousMap.id ↥T.puncturedCore) :=
  ⟨(coreHomotopy T hsm).symm⟩

noncomputable def puncturedCoreHomotopyEquivCore
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    ↥T.puncturedCore ≃ₕ ↥T.core :=
  (homotopyEquivOfRetraction (coreInclusion T) (coreRetraction T hsm)
    (coreRetraction_comp_coreInclusion T hsm)
    (coreInclusion_comp_coreRetraction_homotopic_id T hsm)).symm

omit [IsManifold ThreeModel ∞ M] in
theorem simplyConnectedSpace_puncturedCore_iff_core
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    SimplyConnectedSpace ↥T.puncturedCore ↔ SimplyConnectedSpace ↥T.core :=
  (puncturedCoreHomotopyEquivCore T hsm).simplyConnectedSpace_iff

omit [IsManifold ThreeModel ∞ M] in
theorem simplyConnectedSpace_puncturedCore_of_core
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    [SimplyConnectedSpace ↥T.core] : SimplyConnectedSpace ↥T.puncturedCore :=
  (simplyConnectedSpace_puncturedCore_iff_core T hsm).mpr inferInstance

omit [IsManifold ThreeModel ∞ M] in
theorem simplyConnectedSpace_core_of_puncturedCore
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    [SimplyConnectedSpace ↥T.puncturedCore] : SimplyConnectedSpace ↥T.core :=
  (simplyConnectedSpace_puncturedCore_iff_core T hsm).mp inferInstance

end Retraction

section EmptyIndex

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem puncturedCore_eq_univ_of_isEmpty [IsEmpty T.Index] : T.puncturedCore = univ := by
  simp [puncturedCore]

noncomputable def puncturedCoreHomeomorphOfIsEmpty [IsEmpty T.Index] : ↥T.puncturedCore ≃ₜ M where
  toFun x := x.1
  invFun x := ⟨x, by rw [puncturedCore_eq_univ_of_isEmpty T]; trivial⟩
  left_inv x := Subtype.ext rfl
  right_inv x := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk fun x => by
    rw [puncturedCore_eq_univ_of_isEmpty T]
    trivial

theorem simplyConnectedSpace_puncturedCore_iff_of_isEmpty [IsEmpty T.Index] :
    SimplyConnectedSpace ↥T.puncturedCore ↔ SimplyConnectedSpace M :=
  (puncturedCoreHomeomorphOfIsEmpty T).toHomotopyEquiv.simplyConnectedSpace_iff

theorem not_simplyConnectedSpace_puncturedCore_of_not_pathConnected [IsEmpty T.Index]
    (h : ¬ PathConnectedSpace M) : ¬ SimplyConnectedSpace ↥T.puncturedCore := by
  intro hsc
  exact h ((puncturedCoreHomeomorphOfIsEmpty T).surjective.pathConnectedSpace
    (puncturedCoreHomeomorphOfIsEmpty T).continuous)

end EmptyIndex

end TubeSystem

theorem subsingleton_of_pathConnectedSpace_of_totallyDisconnectedSpace {X : Type*}
    [TopologicalSpace X] [PathConnectedSpace X] [TotallyDisconnectedSpace X] :
    Subsingleton X :=
  subsingleton_of_preconnected_totallyDisconnected

theorem not_pathConnectedSpace_of_totallyDisconnectedSpace_of_nontrivial {X : Type*}
    [TopologicalSpace X] [TotallyDisconnectedSpace X] [Nontrivial X] :
    ¬ PathConnectedSpace X := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  have hsub : Subsingleton X := subsingleton_of_pathConnectedSpace_of_totallyDisconnectedSpace
  exact hxy (hsub.elim x y)

theorem exists_tubeSystem_not_simplyConnectedSpace_puncturedCore :
    ∃ (M : Type) (_ : TopologicalSpace M) (T : TubeSystem M),
      ¬ SimplyConnectedSpace ↥T.puncturedCore := by
  have hI : IsEmpty (emptyTubeSystem Bool).Index := ⟨fun a => a.elim⟩
  exact ⟨Bool, inferInstance, emptyTubeSystem Bool,
    (emptyTubeSystem Bool).not_simplyConnectedSpace_puncturedCore_of_not_pathConnected
      (not_pathConnectedSpace_of_totallyDisconnectedSpace_of_nontrivial (X := Bool))⟩

private def productNeckTubeSystem : TubeSystem TubeDomain where
  Index := PUnit
  finiteIndex := inferInstance
  tube := fun _ => ContinuousMap.id TubeDomain
  embedding := fun _ => Topology.IsEmbedding.id
  disjoint := fun a b hab => (hab (Subsingleton.elim a b)).elim

private theorem mem_puncturedCore_productNeckTubeSystem (z : TubeDomain) :
    z ∈ productNeckTubeSystem.puncturedCore ↔ z.2.1 ≠ 0 := by
  rw [TubeSystem.mem_puncturedCore_iff]
  constructor
  · intro h h0
    exact h PUnit.unit ⟨z, h0, rfl⟩
  · intro h a
    rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := hwz
    exact h (hwz' ▸ hw)

private theorem not_pathConnectedSpace_productNeckTubeSystem :
    ¬ PathConnectedSpace ↥productNeckTubeSystem.puncturedCore := by
  intro h
  let x₀ : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp [Sphere, PiLp.norm_single]⟩
  let zpos : ↥productNeckTubeSystem.puncturedCore :=
    ⟨(x₀, ⟨1, by norm_num, by norm_num⟩), by
      rw [mem_puncturedCore_productNeckTubeSystem]
      norm_num⟩
  let zneg : ↥productNeckTubeSystem.puncturedCore :=
    ⟨(x₀, ⟨-1, by norm_num, by norm_num⟩), by
      rw [mem_puncturedCore_productNeckTubeSystem]
      norm_num⟩
  have hzpos : ((zpos : TubeDomain).2.1 : ℝ) = 1 := rfl
  have hzneg : ((zneg : TubeDomain).2.1 : ℝ) = -1 := rfl
  have hcoord : Continuous fun z : ↥productNeckTubeSystem.puncturedCore =>
      ((z : TubeDomain).2.1 : ℝ) :=
    (continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val
  have hs : IsOpen {z : ↥productNeckTubeSystem.puncturedCore | 0 < (z : TubeDomain).2.1} :=
    isOpen_lt continuous_const hcoord
  have ht : IsOpen {z : ↥productNeckTubeSystem.puncturedCore | (z : TubeDomain).2.1 < 0} :=
    isOpen_lt hcoord continuous_const
  have hdisj : Disjoint {z : ↥productNeckTubeSystem.puncturedCore |
        0 < (z : TubeDomain).2.1}
      {z : ↥productNeckTubeSystem.puncturedCore | (z : TubeDomain).2.1 < 0} :=
    Set.disjoint_left.mpr fun z h1 h2 => by
      simp only [Set.mem_ofPred_eq] at h1 h2
      linarith
  have hcover : (univ : Set ↥productNeckTubeSystem.puncturedCore) ⊆
      {z : ↥productNeckTubeSystem.puncturedCore | 0 < (z : TubeDomain).2.1} ∪
        {z : ↥productNeckTubeSystem.puncturedCore | (z : TubeDomain).2.1 < 0} := by
    intro z _
    have hz : (z : TubeDomain).2.1 ≠ 0 :=
      (mem_puncturedCore_productNeckTubeSystem z.1).mp z.2
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · exact Or.inr hlt
    · exact Or.inl hgt
  have hne : (univ ∩ {z : ↥productNeckTubeSystem.puncturedCore |
      0 < (z : TubeDomain).2.1}).Nonempty :=
    ⟨zpos, mem_univ zpos, by
      change (0 : ℝ) < ((zpos : TubeDomain).2.1)
      rw [hzpos]
      norm_num⟩
  have hsub := isPreconnected_univ.subset_left_of_subset_union hs ht hdisj hcover hne
  have hbad := hsub (mem_univ zneg)
  simp only [Set.mem_ofPred_eq] at hbad
  rw [hzneg] at hbad
  norm_num at hbad

theorem exists_tubeSystem_nonemptyIndex_not_simplyConnectedSpace_puncturedCore :
    ∃ (M : Type) (_ : TopologicalSpace M) (T : TubeSystem M),
      Nonempty T.Index ∧ ¬ SimplyConnectedSpace ↥T.puncturedCore :=
  ⟨TubeDomain, inferInstance, productNeckTubeSystem, ⟨⟨PUnit.unit⟩,
    fun _ => not_pathConnectedSpace_productNeckTubeSystem inferInstance⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
