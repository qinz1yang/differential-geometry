import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EuclideanSimplexGeneratorCriterion
import DifferentialGeometry.Topology.Homology.EuclideanLocalTop

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Topology

def EuclideanStandardSimplexDegreeOne : Prop :=
  ∃ φ : integralLocalHomology 3 (0 : liftedSphereSpace.{u} 1) →ₗ[ℤ] ℤ,
    φ euclideanStandardSimplexClass.{u} = 1

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

theorem localOrientationClass_generator_of_degreeOne
    (h : EuclideanStandardSimplexDegreeOne.{u}) (o : TangentOrientationSection M) (x : M) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) := by
  obtain ⟨φ, hφ⟩ := h
  exact localOrientationClass_generator_of_euclideanStandardSimplex o x
    (euclideanStandardSimplexClass_generator_of_functional_eq_one φ hφ)

theorem localOrientationClass_generator_iff_simplexLocalClass
    (o : TangentOrientationSection M) (x : M) (S : OrientedChartSimplex o x) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) ↔
      Function.Bijective (fun z : ℤ => z • S.localClass) := by
  rw [localOrientationClass_spec o x S]

theorem euclideanStandardSimplexClass_generator_iff_degreeOne :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) ↔
      EuclideanStandardSimplexDegreeOne.{u} := by
  let e := integralEuclideanLocalTopEquiv (liftedSphereSpace.{u} 1) 1
    (liftedSphereSpace_finrank 1) 0
  constructor
  · intro h
    have hu : IsUnit (e euclideanStandardSimplexClass.{u}) :=
      (euclideanStandardSimplexClass_generator_iff_isUnit_of_linearEquiv e).mp h
    obtain ⟨φ, -, hφ⟩ := (isUnit_apply_iff_exists_surjective_functional e _).mp hu
    exact ⟨φ, hφ⟩
  · intro h
    obtain ⟨φ, hφ⟩ := h
    exact euclideanStandardSimplexClass_generator_of_functional_eq_one φ hφ

theorem exists_generator_with_functional_eq_one :
    ∃ c : integralLocalHomology 3 (0 : liftedSphereSpace.{u} 1),
      (∃ φ : integralLocalHomology 3 (0 : liftedSphereSpace.{u} 1) →ₗ[ℤ] ℤ, φ c = 1) ∧
        Function.Bijective (fun z : ℤ => z • c) := by
  let E := liftedSphereSpace.{u} 1
  let hd : Module.finrank ℝ E = 1 + 2 := liftedSphereSpace_finrank 1
  refine ⟨integralEuclideanLocalTopGenerator E 1 hd 0,
    ⟨(integralEuclideanLocalTopEquiv E 1 hd 0).toLinearMap,
      integralEuclideanLocalTopGenerator_coordinate E 1 hd 0⟩,
    integralEuclideanLocalTopGenerator_zsmul_bijective E 1 hd 0⟩

theorem exists_ne_zero_not_generator :
    ∃ c : integralLocalHomology 3 (0 : liftedSphereSpace.{u} 1), c ≠ 0 ∧
      (∃ φ : integralLocalHomology 3 (0 : liftedSphereSpace.{u} 1) →ₗ[ℤ] ℤ, φ c ≠ 0) ∧
        ¬ Function.Bijective (fun z : ℤ => z • c) := by
  let E := liftedSphereSpace.{u} 1
  let hd : Module.finrank ℝ E = 1 + 2 := liftedSphereSpace_finrank 1
  let e := integralEuclideanLocalTopEquiv E 1 hd 0
  let g := integralEuclideanLocalTopGenerator E 1 hd 0
  have hg : e g = 1 := integralEuclideanLocalTopGenerator_coordinate E 1 hd 0
  refine ⟨(2 : ℤ) • g, ?_, ?_, ?_⟩
  · intro hzero
    have h2 : e ((2 : ℤ) • g) = e 0 := congrArg e hzero
    rw [map_zsmul, hg, map_zero, smul_eq_mul, mul_one] at h2
    exact two_ne_zero h2
  · refine ⟨e.toLinearMap, ?_⟩
    change e ((2 : ℤ) • g) ≠ 0
    rw [map_zsmul, hg, smul_eq_mul, mul_one]
    norm_num
  · rw [← bijective_zsmul_iff_of_linearEquiv e ((2 : ℤ) • g)]
    have he : e ((2 : ℤ) • g) = 2 := by
      rw [map_zsmul, hg, smul_eq_mul, mul_one]
    rw [he]
    intro h
    obtain ⟨k, hk⟩ := h.2 1
    simp only [smul_eq_mul] at hk
    omega

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.EuclideanStandardSimplexDegreeOne,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_generator_of_degreeOne,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_generator_iff_simplexLocalClass,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.euclideanStandardSimplexClass_generator_iff_degreeOne,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_generator_with_functional_eq_one,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_ne_zero_not_generator] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
