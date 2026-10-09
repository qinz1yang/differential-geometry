import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalOrientationClassDegreeReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalOrientationClassGeneratorCriterion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.OrientedDegreeGenerator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassReduction
import DifferentialGeometry.Topology.Homology.EuclideanLocalTop

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Bundle Manifold Set
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Topology

def EuclideanStandardSimplexNormalization : Prop :=
  euclideanStandardSimplexClass.{u} =
      integralEuclideanLocalTopGenerator (liftedSphereSpace.{u} 1) 1
        (liftedSphereSpace_finrank 1) 0 ∨
    euclideanStandardSimplexClass.{u} =
      -integralEuclideanLocalTopGenerator (liftedSphereSpace.{u} 1) 1
        (liftedSphereSpace_finrank 1) 0

theorem euclideanStandardSimplexNormalization_iff_bijective_zsmul :
    EuclideanStandardSimplexNormalization.{u} ↔
      Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) := by
  let E := liftedSphereSpace.{u} 1
  let hd : Module.finrank ℝ E = 1 + 2 := liftedSphereSpace_finrank 1
  let e := integralEuclideanLocalTopEquiv E 1 hd 0
  let g := integralEuclideanLocalTopGenerator E 1 hd 0
  have hgen : e g = 1 := by
    change (integralEuclideanLocalTopEquiv E 1 hd 0)
      ((integralEuclideanLocalTopEquiv E 1 hd 0).symm 1) = 1
    exact LinearEquiv.apply_symm_apply _ 1
  constructor
  · rintro (h | h)
    · rw [h]
      exact (isUnit_apply_iff_bijective_zsmul e g).mp (by rw [hgen]; exact isUnit_one)
    · rw [h]
      exact (isUnit_apply_iff_bijective_zsmul e (-g)).mp
        (by rw [map_neg, hgen]; exact Int.isUnit_iff.mpr (Or.inr rfl))
  · intro hb
    have hu : IsUnit (e euclideanStandardSimplexClass.{u}) :=
      (isUnit_apply_iff_bijective_zsmul e _).mpr hb
    rcases Int.isUnit_iff.mp hu with h | h
    · left
      exact e.injective (by rw [h, hgen])
    · right
      exact e.injective (by rw [h, map_neg, hgen])

theorem euclideanStandardSimplexNormalization_iff_puncturedBoundaryClassDetectingFunctional :
    EuclideanStandardSimplexNormalization.{u} ↔
      PuncturedBoundaryClassDetectingFunctional.{u} :=
  euclideanStandardSimplexNormalization_iff_bijective_zsmul.trans
    euclideanStandardSimplexClass_generator_iff_exists_boundary_functional_eq_one

theorem localOrientationClass_generator_of_euclideanStandardSimplexNormalization
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (o : TangentOrientationSection M) (x : M)
    (h : EuclideanStandardSimplexNormalization.{u}) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) :=
  localOrientationClass_generator_of_euclideanStandardSimplex o x
    (euclideanStandardSimplexNormalization_iff_bijective_zsmul.mp h)

def PuncturedFundamentalClassFrontier {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : TangentOrientationSection M) : Prop :=
  (∃ z : IntegralHomology M 3, IsFundamentalClass o z) ∧
    ∀ w w' : IntegralHomology M 3,
      (∀ x : M, absoluteToRelative M ({x}ᶜ) 3 w =
        absoluteToRelative M ({x}ᶜ) 3 w') → w = w'

theorem exists_unique_fundamentalClass_iff_puncturedFundamentalClassFrontier
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (o : TangentOrientationSection M) :
    (∃! z : IntegralHomology M 3, IsFundamentalClass o z) ↔
      PuncturedFundamentalClassFrontier o := by
  constructor
  · intro h
    obtain ⟨hP, hinj⟩ :=
      (exists_unique_fundamentalClass_iff_exists_and_injective_localization o).mp h
    refine ⟨⟨hP.choose, hP.choose_spec⟩, ?_⟩
    intro w w' hww
    apply hinj
    funext x
    exact hww x
  · rintro ⟨⟨z, hz⟩, hsep⟩
    refine ⟨z, hz, fun z' hz' => hsep z' z fun x => by rw [hz' x, hz x]⟩

theorem injective_localization_of_exists_injective_at
    {M : Type u} [TopologicalSpace M]
    (h : ∃ x : M, Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    ∀ w w' : IntegralHomology M 3,
      (∀ x : M, absoluteToRelative M ({x}ᶜ) 3 w =
        absoluteToRelative M ({x}ᶜ) 3 w') → w = w' := by
  obtain ⟨x, hx⟩ := h
  intro w w' hww
  exact hx (hww x)

theorem exists_unique_fundamentalClass_of_puncturedFundamentalClassFrontier
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (o : TangentOrientationSection M)
    (h : PuncturedFundamentalClassFrontier o) :
    ∃! z : IntegralHomology M 3, IsFundamentalClass o z :=
  (exists_unique_fundamentalClass_iff_puncturedFundamentalClassFrontier o).mpr h

theorem exists_fundamentalClass_generator_of_euclideanStandardSimplexNormalization
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (o : TangentOrientationSection M) (x : M)
    (hN : EuclideanStandardSimplexNormalization.{u})
    (h : ∃ z : IntegralHomology M 3, IsFundamentalClass o z)
    (hinj : Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    ∃ z : IntegralHomology M 3, IsFundamentalClass o z ∧
      Function.Bijective (fun k : ℤ => k • z) :=
  ⟨h.choose, h.choose_spec,
    bijective_zsmul_of_forall_absoluteToRelative_eq_and_injective o x h.choose
      h.choose_spec
      (localOrientationClass_generator_of_euclideanStandardSimplexNormalization o x hN) hinj⟩

theorem puncturedFundamentalClassFrontier_of_realization_and_injective_at
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (o : TangentOrientationSection M)
    (h : ∃ z : IntegralHomology M 3, IsFundamentalClass o z)
    (hinj : ∃ x : M, Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    PuncturedFundamentalClassFrontier o :=
  ⟨h, injective_localization_of_exists_injective_at hinj⟩

theorem puncturedFundamentalClassFrontier_of_subsingleton_punctured
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (o : TangentOrientationSection M) [ConnectedSpace M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (h₂ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 2))
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    PuncturedFundamentalClassFrontier o := by
  have hunique := exists_unique_fundamentalClass_of_subsingleton_punctured o hprop x₀ h₂ h₃
  exact puncturedFundamentalClassFrontier_of_realization_and_injective_at o
    ⟨hunique.choose, fun x => (hunique.choose_spec).1 x⟩
    ⟨x₀, absoluteToRelative_compl_singleton_injective_of_subsingleton x₀ h₃⟩

theorem not_puncturedFundamentalClassFrontier_of_subsingleton_topHomology
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (o : TangentOrientationSection M) (x : M)
    (hsub : Subsingleton (IntegralHomology M 3))
    (hne : localOrientationClass o x ≠ 0) :
    ¬ PuncturedFundamentalClassFrontier o := by
  rintro ⟨⟨z, hz⟩, -⟩
  refine hne ?_
  have hz0 : absoluteToRelative M ({x}ᶜ) 3 z = 0 := by
    rw [hsub.allEq z 0]
    exact map_zero _
  exact (hz x).symm.trans hz0

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
