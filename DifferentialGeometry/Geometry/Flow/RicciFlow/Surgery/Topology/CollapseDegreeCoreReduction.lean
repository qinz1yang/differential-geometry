import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegree
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCoreCapCoverFrontier
import DifferentialGeometry.Topology.Homology.Homotopy
import DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

theorem exists_linearMap_eq_one_of_surjective_of_bijective_zsmul
    {A B : Type*} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    (f : A →ₗ[ℤ] B) (hsurj : Function.Surjective f)
    {a : A} {b : B} {k : ℤ} (hmap : f a = k • b)
    (ha : Function.Bijective (fun z : ℤ => z • a))
    (hb : Function.Bijective (fun z : ℤ => z • b)) :
    ∃ φ : B →ₗ[ℤ] ℤ, φ (f a) = 1 := by
  let F : ℤ →+ B :=
    { toFun := fun z : ℤ => z • b
      map_zero' := zero_zsmul b
      map_add' := fun z w => add_zsmul b z w }
  let E : ℤ ≃ₗ[ℤ] B := (AddEquiv.ofBijective F hb).toIntLinearEquiv
  have hE1 : E (1 : ℤ) = b := by
    change F 1 = b
    exact one_smul ℤ b
  have he : E.symm b = 1 := by
    rw [← hE1, LinearEquiv.symm_apply_apply]
  obtain ⟨x, hx⟩ := hsurj b
  obtain ⟨m, hm⟩ := ha.2 x
  have hbm : b = (m * k) • b := by
    calc b = f x := hx.symm
      _ = f (m • a) := by rw [← hm]
      _ = m • f a := by rw [map_zsmul]
      _ = m • (k • b) := by rw [hmap]
      _ = (m * k) • b := by rw [← smul_smul]
  have hmk : m * k = 1 := by
    have h := congrArg E.symm hbm
    simp only [map_zsmul, he, smul_eq_mul, mul_one] at h
    exact h.symm
  have hunit : IsUnit k := isUnit_iff_exists_inv.mpr ⟨m, by rw [mul_comm]; exact hmk⟩
  have hkk : k * k = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h <;> rw [h] <;> norm_num
  let ψ : B →ₗ[ℤ] ℤ := E.symm
  have hψb : ψ b = 1 := he
  have hψa : ψ (f a) = k := by
    rw [hmap, map_zsmul, hψb, smul_eq_mul, mul_one]
  refine ⟨k • ψ, ?_⟩
  rw [LinearMap.smul_apply, hψa, smul_eq_mul]
  exact hkk

theorem exists_linearMap_eq_one_of_homotopySection
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (s : C(Y, X)) (hs : (f.comp s).Homotopic (ContinuousMap.id Y))
    {a : integralSingularHomology 3 X} {b : integralSingularHomology 3 Y} {k : ℤ}
    (hmap : integralSingularHomologyMap 3 f a = k • b)
    (ha : Function.Bijective (fun z : ℤ => z • a))
    (hb : Function.Bijective (fun z : ℤ => z • b)) :
    ∃ φ : integralSingularHomology 3 Y →ₗ[ℤ] ℤ,
      φ (integralSingularHomologyMap 3 f a) = 1 := by
  have hcomp : (integralSingularHomologyMap 3 f).comp (integralSingularHomologyMap 3 s) =
      LinearMap.id := by
    rw [← integralSingularHomologyMap_comp 3 s f, integralSingularHomologyMap_homotopic 3 hs,
      integralSingularHomologyMap_id]
  have hsurj : Function.Surjective (integralSingularHomologyMap 3 f) := fun w =>
    ⟨integralSingularHomologyMap 3 s w, by
      have h := LinearMap.congr_fun hcomp w
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h⟩
  exact exists_linearMap_eq_one_of_surjective_of_bijective_zsmul _ hsurj hmap ha hb

theorem not_exists_linearMap_eq_one_integralSingularHomologyMap_const
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (y : Y)
    (a : integralSingularHomology 3 X) :
    ¬ ∃ φ : integralSingularHomology 3 Y →ₗ[ℤ] ℤ,
      φ (integralSingularHomologyMap 3 (ContinuousMap.const X y) a) = 1 := by
  rw [integralSingularHomologyMap_const 3 (by norm_num) y, LinearMap.zero_apply]
  exact fun h => not_exists_linearMap_eq_one_zero h

theorem exists_linearMap_eq_one_homotopySection_id_liftedSphereGenerator :
    ∃ φ : integralSingularHomology 3 (liftedHomotopySphere.{u} 2) →ₗ[ℤ] ℤ,
      φ (integralSingularHomologyMap 3 (ContinuousMap.id (liftedHomotopySphere.{u} 2))
        (integralLiftedSphereGenerator.{u} 2)) = 1 :=
  exists_linearMap_eq_one_of_homotopySection
    (X := liftedHomotopySphere.{u} 2) (Y := liftedHomotopySphere.{u} 2)
    (f := ContinuousMap.id _) (s := ContinuousMap.id _)
    (a := integralLiftedSphereGenerator.{u} 2) (b := integralLiftedSphereGenerator.{u} 2)
    (k := 1) (ContinuousMap.Homotopic.refl _)
    (by rw [integralSingularHomologyMap_id, LinearMap.id_apply, one_smul])
    ((isSphereHomologyGenerator_iff_bijective_zsmul 2 _).mp
      (integralLiftedSphereGenerator_isGenerator 2))
    ((isSphereHomologyGenerator_iff_bijective_zsmul 2 _).mp
      (integralLiftedSphereGenerator_isGenerator 2))

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  (c : ConnectedComponents (H.stage i.succ).Carrier)

def CollapseCoreRetraction : Prop :=
  ∃ ρ : C(G.transition.ChildCarrier c, G.transition.ChildCore c),
    ((G.transition.childCoreInclusion c).comp ρ).Homotopic
      (ContinuousMap.id (G.transition.ChildCarrier c))

theorem collapseCoreRetraction_of_isEmpty_childCapBoundary
    [IsEmpty (G.transition.ChildCapBoundary c)] : G.CollapseCoreRetraction c := by
  let Φ := G.transition.childCoreHomeomorphOfIsEmptyChildCapBoundary c
  refine ⟨⟨⇑Φ.symm, Φ.symm.continuous⟩, ?_⟩
  have h : (G.transition.childCoreInclusion c).comp
      (⟨⇑Φ.symm, Φ.symm.continuous⟩ : C(G.transition.ChildCarrier c,
        G.transition.ChildCore c)) =
      ContinuousMap.id (G.transition.ChildCarrier c) := by
    apply ContinuousMap.ext
    intro y
    apply Subtype.ext
    exact congrArg Subtype.val (Φ.apply_symm_apply y)
  simpa only [h] using ContinuousMap.Homotopic.refl (ContinuousMap.id (G.transition.ChildCarrier c))

namespace ComparisonSupport

variable {G c} (K : G.ComparisonSupport c)

def CollapseClassGenerator (a : IntegralHomology (G.Parent c).Carrier 3) : Prop :=
  ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
    φ (integralHomologyMap 3 K.rfs_whole_parent_map a) = 1

theorem collapseClassGenerator_of_coreRetraction
    (hρ : G.CollapseCoreRetraction c)
    {a : IntegralHomology (G.Parent c).Carrier 3}
    {b : IntegralHomology (G.Child c).Carrier 3} {k : ℤ}
    (hmap : integralHomologyMap 3 K.rfs_whole_parent_map a = k • b)
    (ha : Function.Bijective (fun z : ℤ => z • a))
    (hb : Function.Bijective (fun z : ℤ => z • b)) :
    K.CollapseClassGenerator a := by
  obtain ⟨ρ, hρ⟩ := hρ
  have hsec : (K.rfs_whole_parent_map.comp
      ((G.transition.childCoreIntoParent c).comp ρ)).Homotopic
      (ContinuousMap.id (G.transition.ChildCarrier c)) := by
    have hEq : K.rfs_whole_parent_map.comp ((G.transition.childCoreIntoParent c).comp ρ) =
        (G.transition.childCoreInclusion c).comp ρ := by
      apply ContinuousMap.ext
      intro y
      exact K.rfs_whole_parent_map_childCore (ρ y)
    rw [hEq]
    exact hρ
  exact DifferentialGeometry.Topology.exists_linearMap_eq_one_of_homotopySection
    K.rfs_whole_parent_map ((G.transition.childCoreIntoParent c).comp ρ) hsec hmap ha hb

theorem rfs_collapse_degree_of_localDistanceControl_and_coreRetraction
    (hlip : K.LocalTerminalDistanceControl K.rfs_whole_parent_map)
    (hρ : G.CollapseCoreRetraction c)
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
    (K.collapseClassGenerator_of_coreRetraction hρ hmap ha hb) hk

end ComparisonSupport

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.Topology.exists_linearMap_eq_one_of_surjective_of_bijective_zsmul,
      ``DifferentialGeometry.Topology.exists_linearMap_eq_one_of_homotopySection,
      ``DifferentialGeometry.Topology.not_exists_linearMap_eq_one_integralSingularHomologyMap_const,
      ``DifferentialGeometry.Topology.exists_linearMap_eq_one_homotopySection_id_liftedSphereGenerator,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.CollapseCoreRetraction,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.collapseCoreRetraction_of_isEmpty_childCapBoundary,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.CollapseClassGenerator,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collapseClassGenerator_of_coreRetraction,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_localDistanceControl_and_coreRetraction] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
