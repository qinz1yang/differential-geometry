import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorRepresentation
import DifferentialGeometry.Geometry.Metric.ExteriorEndomorphismRegularity
import DifferentialGeometry.Geometry.Metric.SelfAdjointSubbundle
import DifferentialGeometry.Bundle.SmoothSubbundle.VectorBundle

set_option autoImplicit false

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Bundle Manifold ContDiff RealInnerProductSpace

namespace Bundle.ExteriorPower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem contMDiff_traceNormalizedCurvatureEndomorphism (n : ℕ∞ω) (hn : n ≤ ∞)
    (T : ∀ x, Bundle.continuousMultilinearMap ℝ 4 F V x)
    (hT : ∀ x, IsAlgCurvForm (fun a b c d => T x ![a, b, c, d]))
    (hTsmooth : ContMDiff I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)) n
      (fun x => TotalSpace.mk'
        (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
        (E := Bundle.continuousMultilinearMap ℝ 4 F V) x (T x))) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V 2
    letI := fiberBundle F V 2
    letI := vector_bundle F V 2
    ContMDiff I (I.prod 𝓘(ℝ, (⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F)) n
      (fun x => TotalSpace.mk' ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F) x
        (exteriorPower.traceNormalizedCurvatureEndomorphism (T x) (hT x))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V 2
  let := fiberBundle F V 2
  let := vector_bundle F V 2
  apply contMDiff_of_endomorphismTensor F V 2 n hn
  have h := hTsmooth.const_smul_section (a := (-2 : ℝ))
  convert h using 1
  funext x
  congr 1
  exact exteriorPower.endomorphismTensor_traceNormalizedCurvatureEndomorphism (T x) (hT x)

def traceNormalizedCurvatureSelfAdjointSection
    (T : ∀ x, Bundle.continuousMultilinearMap ℝ 4 F V x)
    (hT : ∀ x, IsAlgCurvForm (fun a b c d => T x ![a, b, c, d]))
    (hTsmooth : ContMDiff I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)) ∞
      (fun x => TotalSpace.mk'
        (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
        (E := Bundle.continuousMultilinearMap ℝ 4 F V) x (T x))) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V 2
    letI := fiberBundle F V 2
    letI := vector_bundle F V 2
    letI := contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    letI := isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    let S := selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^2 F)
      (V := fun x => ⋀[ℝ]^2 (V x)) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯ := by
  dsimp only
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V 2
  let := fiberBundle F V 2
  let := vector_bundle F V 2
  let := contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let := isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let S := selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^2 F)
    (V := fun x => ⋀[ℝ]^2 (V x)) (n := ∞)
  let := S.totalSpaceTopology
  let := S.fiberBundle
  let A : ∀ x, S.fiber x := fun x =>
    exteriorPower.traceNormalizedCurvatureSelfAdjoint (T x) (hT x)
  refine ⟨A, ?_⟩
  rw [← contMDiffOn_univ]
  apply (S.contMDiffOn_section_iff Set.univ isOpen_univ A).mpr
  exact (contMDiff_traceNormalizedCurvatureEndomorphism F V ∞ le_rfl T hT hTsmooth).contMDiffOn

theorem traceNormalizedCurvatureSelfAdjointSection_coe
    (T : ∀ x, Bundle.continuousMultilinearMap ℝ 4 F V x)
    (hT : ∀ x, IsAlgCurvForm (fun a b c d => T x ![a, b, c, d]))
    (hTsmooth : ContMDiff I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)) ∞
      (fun x => TotalSpace.mk'
        (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
        (E := Bundle.continuousMultilinearMap ℝ 4 F V) x (T x)))
    (x : M) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := totalSpaceTopology F V 2
    letI := fiberBundle F V 2
    letI := vector_bundle F V 2
    letI := contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    letI := isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    ((traceNormalizedCurvatureSelfAdjointSection F V T hT hTsmooth x) :
        (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x)) =
      exteriorPower.traceNormalizedCurvatureEndomorphism (T x) (hT x) := rfl

end Bundle.ExteriorPower
