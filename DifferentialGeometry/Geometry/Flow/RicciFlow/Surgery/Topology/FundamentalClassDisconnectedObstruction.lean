import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassInputReduction
import DifferentialGeometry.Topology.Homology.SphereTopHomology
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

theorem exists_ne_zero_integralSingularHomology_three_sphereThree :
    ∃ z : integralSingularHomology 3 SphereThree, z ≠ 0 := by
  let e := integralSphereTopHomologyEquiv 2 (EuclideanSpace ℝ (Fin 4)) (by simp)
  exact ⟨e.symm 1, fun h => one_ne_zero (by rw [← e.apply_symm_apply 1, h, map_zero])⟩

theorem not_subsingleton_integralSingularHomology_three_compl_singleton_disjointUnion
    (x : SphereThree) :
    ¬ Subsingleton
      (integralSingularHomology 3 ({Sum.inl x}ᶜ : Set (SphereThree ⊕ SphereThree))) := by
  intro hsub
  obtain ⟨α, hα⟩ := exists_ne_zero_integralSingularHomology_three_sphereThree
  let i : C(SphereThree, ↥({Sum.inl x}ᶜ : Set (SphereThree ⊕ SphereThree))) :=
    ⟨fun y => ⟨Sum.inr y, Sum.inr_ne_inl⟩, continuous_inr.subtype_mk _⟩
  let r : C(↥({Sum.inl x}ᶜ : Set (SphereThree ⊕ SphereThree)), SphereThree) :=
    ⟨fun z => Sum.elim (fun _ => x) (fun y => y) z.1,
      (continuous_const.sumElim continuous_id).comp continuous_subtype_val⟩
  have hri : r.comp i = ContinuousMap.id SphereThree := by
    ext y
    rfl
  have hid : (integralSingularHomologyMap 3 r).comp (integralSingularHomologyMap 3 i)
      = LinearMap.id := by
    rw [← integralSingularHomologyMap_comp 3 i r, hri, integralSingularHomologyMap_id]
  have hinj : Function.Injective (integralSingularHomologyMap 3 i) := by
    intro a b hab
    have ha : integralSingularHomologyMap 3 r (integralSingularHomologyMap 3 i a) = a := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using congrArg (fun f => f a) hid
    have hb : integralSingularHomologyMap 3 r (integralSingularHomologyMap 3 i b) = b := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using congrArg (fun f => f b) hid
    rw [hab] at ha
    exact ha.symm.trans hb
  have hzero : integralSingularHomologyMap 3 i α = 0 := hsub.allEq _ _
  exact hα (hinj (by rw [hzero, map_zero]))

theorem not_subsingleton_integralHomology_three_compl_singleton_disjointUnion
    (x : SphereThree) :
    ¬ Subsingleton
      (IntegralHomology ({Sum.inl x}ᶜ : Set (SphereThree ⊕ SphereThree)) 3) :=
  not_subsingleton_integralSingularHomology_three_compl_singleton_disjointUnion x

theorem not_forall_subsingleton_integralHomology_three_compl_singleton_disjointUnion :
    ¬ (∀ x : SphereThree ⊕ SphereThree,
        Subsingleton (IntegralHomology ({x}ᶜ : Set (SphereThree ⊕ SphereThree)) 3)) :=
  fun h =>
    not_subsingleton_integralHomology_three_compl_singleton_disjointUnion sphereThreeNorth
      (h (Sum.inl sphereThreeNorth))

theorem not_preconnectedSpace_disjointUnion_sphereThree :
    ¬ PreconnectedSpace (SphereThree ⊕ SphereThree) := by
  intro hp
  have hunion : (univ : Set (SphereThree ⊕ SphereThree)) ⊆
      Set.range (Sum.inl : SphereThree → SphereThree ⊕ SphereThree) ∪
        Set.range (Sum.inr : SphereThree → SphereThree ⊕ SphereThree) := by
    intro z _
    rcases z with a | b
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨b, rfl⟩
  have hdisj : Disjoint (Set.range (Sum.inl : SphereThree → SphereThree ⊕ SphereThree))
      (Set.range (Sum.inr : SphereThree → SphereThree ⊕ SphereThree)) := by
    rw [Set.disjoint_left]
    rintro z ⟨a, rfl⟩ ⟨b, hb⟩
    exact Sum.inr_ne_inl hb
  rcases IsPreconnected.subset_or_subset isOpen_range_inl isOpen_range_inr hdisj hunion
      (@isPreconnected_univ _ _ hp) with h1 | h2
  · have hm : (Sum.inr sphereThreeNorth : SphereThree ⊕ SphereThree) ∈
        Set.range (Sum.inl : SphereThree → SphereThree ⊕ SphereThree) := h1 (mem_univ _)
    obtain ⟨a, ha⟩ := hm
    exact Sum.inr_ne_inl ha.symm
  · have hm : (Sum.inl sphereThreeNorth : SphereThree ⊕ SphereThree) ∈
        Set.range (Sum.inr : SphereThree → SphereThree ⊕ SphereThree) := h2 (mem_univ _)
    obtain ⟨b, hb⟩ := hm
    exact Sum.inl_ne_inr hb.symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_ne_zero_integralSingularHomology_three_sphereThree,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_subsingleton_integralSingularHomology_three_compl_singleton_disjointUnion,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_subsingleton_integralHomology_three_compl_singleton_disjointUnion,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_subsingleton_integralHomology_three_compl_singleton_disjointUnion,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_preconnectedSpace_disjointUnion_sphereThree] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
