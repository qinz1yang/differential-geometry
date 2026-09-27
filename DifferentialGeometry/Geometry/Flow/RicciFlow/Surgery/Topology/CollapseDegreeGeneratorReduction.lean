import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegreeCoreReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegreeInputs

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff Topology
universe u

namespace DifferentialGeometry.Topology

theorem surjective_of_bijective_zsmul
    {A B : Type*} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    (f : A →ₗ[ℤ] B) {a : A} (h : Function.Surjective (fun z : ℤ => z • f a)) :
    Function.Surjective f := fun w => by
  obtain ⟨z, hz⟩ := h w
  exact ⟨z • a, by rw [map_zsmul]; simpa using hz⟩

theorem exists_linearMap_eq_one_iff_surjective_of_bijective_zsmul
    {A B : Type*} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    (f : A →ₗ[ℤ] B) {a : A}
    (ha : Function.Bijective (fun z : ℤ => z • a))
    (hb : Function.Bijective (fun z : ℤ => z • f a)) :
    (∃ φ : B →ₗ[ℤ] ℤ, φ (f a) = 1) ↔ Function.Surjective f :=
  ⟨fun _ => surjective_of_bijective_zsmul f hb.2,
   fun hsurj =>
    exists_linearMap_eq_one_of_surjective_of_bijective_zsmul f hsurj
      (by rw [one_smul]) ha hb⟩

theorem not_exists_linearMap_eq_one_of_comp_eq_id_of_eq_zsmul :
    ∃ (f s : ℤ →ₗ[ℤ] ℤ) (a b k : ℤ),
      f.comp s = LinearMap.id ∧ f a = k • b ∧
        Function.Bijective (fun z : ℤ => z • b) ∧ 0 < k ∧
        ¬ ∃ φ : ℤ →ₗ[ℤ] ℤ, φ (f a) = 1 := by
  refine ⟨LinearMap.id, LinearMap.id, 2, 1, 2, LinearMap.id_comp _, ?_, ?_, ?_, ?_⟩
  · norm_num
  · exact ⟨fun x y h => by simpa using h, fun y => ⟨y, by simp⟩⟩
  · norm_num
  · rintro ⟨φ, hφ⟩
    have h : φ 2 = 2 * φ 1 := by
      simpa using φ.map_smul (2 : ℤ) (1 : ℤ)
    have hφ' : 2 * φ 1 = 1 := by
      rw [← h]
      simpa using hφ
    omega

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier}

namespace GeometricCutoffRecord

namespace ComparisonSupport

variable (K : G.ComparisonSupport c)

theorem rfs_whole_parent_map_surjective : Function.Surjective K.rfs_whole_parent_map :=
  K.rfs_whole_parent_map_surjective_of_cover K.rfs_collapse_cover

theorem collapseClassGenerator_iff_surjective
    {a : IntegralHomology (G.Parent c).Carrier 3}
    {b : IntegralHomology (G.Child c).Carrier 3} {k : ℤ}
    (hmap : integralHomologyMap 3 K.rfs_whole_parent_map a = k • b)
    (ha : Function.Bijective (fun z : ℤ => z • a))
    (hb : Function.Bijective (fun z : ℤ => z • b)) :
    K.CollapseClassGenerator a ↔
      Function.Surjective (integralHomologyMap 3 K.rfs_whole_parent_map) := by
  constructor
  · rintro ⟨φ, hφ⟩
    have hk : IsUnit k :=
      DifferentialGeometry.Topology.isUnit_of_exists_linearMap_eq_one _
        ⟨φ, hφ⟩ hmap
    have hgen : Function.Surjective
        (fun z : ℤ => z • integralHomologyMap 3 K.rfs_whole_parent_map a) := by
      intro w
      obtain ⟨m, hm⟩ := hb.2 w
      rcases Int.isUnit_iff.mp hk with hk1 | hk1
      · exact ⟨m, by rw [hmap, hk1, one_smul]; exact hm⟩
      · exact ⟨-m, by
          simp only [hmap, hk1, smul_smul]
          rw [show (-m) * (-1) = m by ring]
          exact hm⟩
    exact DifferentialGeometry.Topology.surjective_of_bijective_zsmul
      (DifferentialGeometry.Topology.integralSingularHomologyMap 3 K.rfs_whole_parent_map) hgen
  · intro hsurj
    exact DifferentialGeometry.Topology.exists_linearMap_eq_one_of_surjective_of_bijective_zsmul
      (DifferentialGeometry.Topology.integralSingularHomologyMap 3 K.rfs_whole_parent_map)
      hsurj hmap ha hb

theorem surjective_integralHomologyMap_of_coreRetraction
    (hρ : G.CollapseCoreRetraction c) :
    Function.Surjective (integralHomologyMap 3 K.rfs_whole_parent_map) := by
  obtain ⟨ρ, hρ⟩ := hρ
  let s : C(G.transition.ChildCarrier c, G.transition.ParentCarrier c) :=
    (G.transition.childCoreIntoParent c).comp ρ
  have hsec : (K.rfs_whole_parent_map.comp s).Homotopic
      (ContinuousMap.id (G.transition.ChildCarrier c)) := by
    have hEq : K.rfs_whole_parent_map.comp s =
        (G.transition.childCoreInclusion c).comp ρ := by
      apply ContinuousMap.ext
      intro y
      exact K.rfs_whole_parent_map_childCore (ρ y)
    rw [hEq]
    exact hρ
  have hcomp : (DifferentialGeometry.Topology.integralSingularHomologyMap 3
        K.rfs_whole_parent_map).comp
        (DifferentialGeometry.Topology.integralSingularHomologyMap 3 s) = LinearMap.id :=
    (DifferentialGeometry.Topology.integralSingularHomologyMap_comp 3 s
        K.rfs_whole_parent_map).symm.trans
      ((DifferentialGeometry.Topology.integralSingularHomologyMap_homotopic 3 hsec).trans
        (DifferentialGeometry.Topology.integralSingularHomologyMap_id 3))
  have hsurj : Function.Surjective
      (DifferentialGeometry.Topology.integralSingularHomologyMap 3 K.rfs_whole_parent_map) := by
    intro y
    exact ⟨(DifferentialGeometry.Topology.integralSingularHomologyMap 3 s) y,
      (congrArg (fun k => k y) hcomp).trans (LinearMap.id_apply y)⟩
  exact hsurj

theorem rfs_collapse_degree_of_localDistanceControl_and_bijective_zsmul
    (hlip : K.LocalTerminalDistanceControl K.rfs_whole_parent_map)
    (hsurj : Function.Surjective (integralHomologyMap 3 K.rfs_whole_parent_map))
    {a : IntegralHomology (G.Parent c).Carrier 3}
    {b : IntegralHomology (G.Child c).Carrier 3} {k : ℤ}
    (hmap : integralHomologyMap 3 K.rfs_whole_parent_map a = k • b)
    (ha : Function.Bijective (fun z : ℤ => z • a))
    (hb : Function.Bijective (fun z : ℤ => z • b))
    (hk : 0 < k) :
    K.LocalTerminalLengthControl K.rfs_whole_parent_map ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.rfs_whole_parent_map y = K.rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      K.rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 K.rfs_whole_parent_map a = b ∧
    Function.Surjective K.rfs_whole_parent_map :=
  K.rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator a b hlip hmap
    ((K.collapseClassGenerator_iff_surjective hmap ha hb).mpr hsurj) hk

end ComparisonSupport

end GeometricCutoffRecord

namespace GeometricCutoffRecord

theorem rfs_collapse_degree_of_localTerminalEDistComparison_and_bijective_zsmul
    (Kc : (c' : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c')
    (a : IntegralHomology (G.Parent c).Carrier 3) (b : IntegralHomology (G.Child c).Carrier 3)
    {k : ℤ} (hcollapse : G.LocalTerminalEDistComparison Kc)
    (hsurj : Function.Surjective (integralHomologyMap 3 (Kc c).rfs_whole_parent_map))
    (hmap : integralHomologyMap 3 (Kc c).rfs_whole_parent_map a = k • b)
    (ha : Function.Bijective (fun z : ℤ => z • a))
    (hb : Function.Bijective (fun z : ℤ => z • b))
    (hk : 0 < k) :
    (Kc c).LocalTerminalLengthControl (Kc c).rfs_whole_parent_map ∧
    (∀ x ∉ (Kc c).support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      (Kc c).rfs_whole_parent_map y = (Kc c).rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      (Kc c).rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 (Kc c).rfs_whole_parent_map a = b ∧
    Function.Surjective (Kc c).rfs_whole_parent_map :=
  ComparisonSupport.rfs_collapse_degree_of_localDistanceControl_and_bijective_zsmul (Kc c)
    (ComparisonSupport.localTerminalDistanceControl_of_localTerminalEDistComparison Kc
      hcollapse) hsurj hmap ha hb hk

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let top := `DifferentialGeometry.Topology
  let record := `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
  let support := record ++ `ComparisonSupport
  for n in [top ++ `surjective_of_bijective_zsmul,
      top ++ `exists_linearMap_eq_one_iff_surjective_of_bijective_zsmul,
      top ++ `not_exists_linearMap_eq_one_of_comp_eq_id_of_eq_zsmul,
      support ++ `rfs_whole_parent_map_surjective,
      support ++ `collapseClassGenerator_iff_surjective,
      support ++ `surjective_integralHomologyMap_of_coreRetraction,
      support ++ `rfs_collapse_degree_of_localDistanceControl_and_bijective_zsmul,
      record ++ `rfs_collapse_degree_of_localTerminalEDistComparison_and_bijective_zsmul] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
