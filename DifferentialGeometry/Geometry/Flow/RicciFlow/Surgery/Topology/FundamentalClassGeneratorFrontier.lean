import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalOrientationClassDegreeReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassRealizationCriterion
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def puncturedAbsoluteToRelativeInjective (M : Type u) [TopologicalSpace M] : Prop :=
  ∃ x : M, Function.Injective (absoluteToRelative M ({x}ᶜ) 3)

noncomputable def fundamentalClassCandidate {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : TangentOrientationSection M) : IntegralHomology M 3 := by
  classical
  exact if h : ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x
    then Classical.choose h else 0

theorem fundamentalClassCandidate_eq_choose {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : TangentOrientationSection M)
    (h : ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) :
    fundamentalClassCandidate o = Classical.choose h := by
  unfold fundamentalClassCandidate
  rw [dif_pos h]

theorem fundamentalClassCandidate_local {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : TangentOrientationSection M)
    (h : ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) :
    ∀ x : M, absoluteToRelative M ({x}ᶜ) 3 (fundamentalClassCandidate o) =
      localOrientationClass o x := by
  intro x
  rw [fundamentalClassCandidate_eq_choose o h]
  exact (Classical.choose_spec h).1 x

theorem injective_of_bijective_zsmul_linearMap {A B : Type*}
    [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    (f : A →ₗ[ℤ] B) (z : A) (c : B) (hz : f z = c)
    (hgen : Function.Bijective (fun k : ℤ => k • z))
    (hlocal : Function.Bijective (fun k : ℤ => k • c)) :
    Function.Injective f := by
  intro a b hab
  obtain ⟨p, rfl⟩ := hgen.surjective a
  obtain ⟨q, rfl⟩ := hgen.surjective b
  have hpq : (p - q) • c = 0 := by
    simp only [map_zsmul, hz] at hab
    rw [sub_zsmul]
    simpa only [sub_eq_add_neg] using (sub_eq_zero.mpr hab : p • c - q • c = 0)
  have hpq' : p = q := by
    have h0 : (p - q) • c = (0 : ℤ) • c := by simpa using hpq
    exact sub_eq_zero.mp (hlocal.injective h0)
  rw [hpq']

theorem bijective_zsmul_choose_iff_injective_absoluteToRelative
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]
    (o : TangentOrientationSection M) (x : M)
    (h : ∃! z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y)
    (hlocal : Function.Bijective (fun k : ℤ => k • localOrientationClass o x)) :
    Function.Bijective (fun k : ℤ => k • Classical.choose h) ↔
      Function.Injective (absoluteToRelative M ({x}ᶜ) 3) := by
  have hz : ∀ y : M, absoluteToRelative M ({y}ᶜ) 3 (Classical.choose h) =
      localOrientationClass o y := (Classical.choose_spec h).1
  constructor
  · intro hgen
    exact injective_of_bijective_zsmul_linearMap
      ((absoluteToRelative M ({x}ᶜ) 3).hom) (Classical.choose h)
      (localOrientationClass o x) (hz x) hgen hlocal
  · intro hinj
    exact bijective_zsmul_of_forall_absoluteToRelative_eq_and_injective o x
      (Classical.choose h) hz hlocal hinj

theorem bijective_zsmul_choose_of_injective_absoluteToRelative
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]
    (o : TangentOrientationSection M) (x : M)
    (h : ∃! z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y)
    (hlocal : Function.Bijective (fun k : ℤ => k • localOrientationClass o x))
    (hinj : Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    Function.Bijective (fun k : ℤ => k • Classical.choose h) :=
  (bijective_zsmul_choose_iff_injective_absoluteToRelative o x h hlocal).mpr hinj

theorem fundamentalClassCandidate_generator_of_injective
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]
    (o : TangentOrientationSection M) (x : M)
    (h : ∃ z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y)
    (hlocal : Function.Bijective (fun k : ℤ => k • localOrientationClass o x))
    (hinj : Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    Function.Bijective (fun k : ℤ => k • fundamentalClassCandidate o) := by
  have h' : ∃! z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y :=
    exists_unique_fundamentalClass_of_exists o h ⟨x, hinj⟩
  rw [fundamentalClassCandidate_eq_choose o h']
  exact bijective_zsmul_choose_of_injective_absoluteToRelative o x h' hlocal hinj

theorem puncturedAbsoluteToRelativeInjective_of_noncompactThreeManifoldTopHomologyVanishing
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [ConnectedSpace M] [T2Space M]
    (h : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    puncturedAbsoluteToRelativeInjective M := by
  refine ⟨Classical.arbitrary M, ?_⟩
  exact absoluteToRelative_compl_singleton_injective_of_subsingleton
    (Classical.arbitrary M)
    (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
      h (Classical.arbitrary M))

theorem bijective_zsmul_choose_of_noncompactThreeManifoldTopHomologyVanishing
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [ConnectedSpace M] [T2Space M]
    (o : TangentOrientationSection M) (x : M)
    (h : ∃! z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y)
    (hlocal : Function.Bijective (fun k : ℤ => k • localOrientationClass o x))
    (hv : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    Function.Bijective (fun k : ℤ => k • Classical.choose h) :=
  bijective_zsmul_choose_of_injective_absoluteToRelative o x h hlocal
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x
      (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
        hv x))

theorem fundamentalClassCandidate_generator_of_noncompactThreeManifoldTopHomologyVanishing
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [ConnectedSpace M] [T2Space M]
    (o : TangentOrientationSection M) (x : M)
    (h : ∃ z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y)
    (hlocal : Function.Bijective (fun k : ℤ => k • localOrientationClass o x))
    (hv : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    Function.Bijective (fun k : ℤ => k • fundamentalClassCandidate o) :=
  fundamentalClassCandidate_generator_of_injective o x h hlocal
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x
      (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
        hv x))

theorem puncturedAbsoluteToRelativeInjective_sphereThree :
    puncturedAbsoluteToRelativeInjective
      DifferentialGeometry.Topology.SphereThree :=
  ⟨DifferentialGeometry.Topology.sphereThreeNorth,
    (absoluteToRelative_punctured_threeSphere_bijective
      DifferentialGeometry.Topology.sphereThreeNorth).1⟩

theorem exists_linearMap_eq_and_bijective_zsmul_not_bijective_zsmul :
    ∃ (A B : Type) (_ : AddCommGroup A) (_ : Module ℤ A)
      (_ : AddCommGroup B) (_ : Module ℤ B)
      (f : A →ₗ[ℤ] B) (z : A) (c : B),
      f z = c ∧ Function.Bijective (fun k : ℤ => k • c) ∧
        ¬ Function.Bijective (fun k : ℤ => k • z) := by
  refine ⟨ℤ × ℤ, ℤ, inferInstance, inferInstance, inferInstance, inferInstance,
    LinearMap.snd ℤ ℤ ℤ, (0, 1), 1, rfl, ?_, ?_⟩
  · constructor
    · intro a b hab
      simpa using hab
    · intro b
      exact ⟨b, by simp⟩
  · intro h
    obtain ⟨p, hp⟩ := h.surjective (1, 0)
    have hfst := congrArg Prod.fst hp
    simp at hfst

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.puncturedAbsoluteToRelativeInjective,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClassCandidate,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClassCandidate_eq_choose,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClassCandidate_local,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.injective_of_bijective_zsmul_linearMap,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijective_zsmul_choose_iff_injective_absoluteToRelative,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijective_zsmul_choose_of_injective_absoluteToRelative,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClassCandidate_generator_of_injective,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.puncturedAbsoluteToRelativeInjective_of_noncompactThreeManifoldTopHomologyVanishing,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijective_zsmul_choose_of_noncompactThreeManifoldTopHomologyVanishing,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClassCandidate_generator_of_noncompactThreeManifoldTopHomologyVanishing,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.puncturedAbsoluteToRelativeInjective_sphereThree,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_linearMap_eq_and_bijective_zsmul_not_bijective_zsmul] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
