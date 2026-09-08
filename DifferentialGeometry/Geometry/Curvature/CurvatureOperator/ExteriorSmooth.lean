import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorRepresentation
import DifferentialGeometry.Geometry.Metric.ExteriorEndomorphismRegularity
import DifferentialGeometry.Geometry.Metric.SelfAdjointSubbundle
import DifferentialGeometry.Bundle.SmoothSubbundle.VectorBundle
import DifferentialGeometry.Bundle.SectionOperations

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

section Map

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {J : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

theorem contMDiffWithinAt_traceNormalizedCurvatureEndomorphism
    (n : ℕ∞ω) (hn : n ≤ ∞) {b : P → M} {p : P} {u : Set P}
    (T : ∀ q, Bundle.continuousMultilinearMap ℝ 4 F V (b q))
    (hT : ∀ q, IsAlgCurvForm (fun a b c d => T q ![a, b, c, d]))
    (hTsmooth : ContMDiffWithinAt J
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)) n
      (fun q => TotalSpace.mk'
        (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
        (E := Bundle.continuousMultilinearMap ℝ 4 F V) (b q) (T q)) u p) :
    let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    let := Bundle.ExteriorPower.totalSpaceTopology F V 2
    let := Bundle.ExteriorPower.fiberBundle F V 2
    let := Bundle.ExteriorPower.vector_bundle F V 2
    ContMDiffWithinAt J (I.prod 𝓘(ℝ, (⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F)) n
      (fun q => TotalSpace.mk' ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F)
        (E := fun x => (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x)) (b q)
        (exteriorPower.traceNormalizedCurvatureEndomorphism (T q) (hT q))) u p := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let := Bundle.ExteriorPower.fiberBundle F V 2
  let := Bundle.ExteriorPower.vector_bundle F V 2
  have hAs : ContMDiffWithinAt J
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)) n
      (fun q => TotalSpace.mk'
        (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
        (E := Bundle.continuousMultilinearMap ℝ 4 F V) (b q)
        (Bundle.ExteriorPower.endomorphismTensorHom F V 2 (b q)
          (exteriorPower.traceNormalizedCurvatureEndomorphism (T q) (hT q)))) u p := by
    have h := (contMDiffWithinAt_const (c := (-2 : ℝ))).smul_bundle hTsmooth
    convert h using 1
    funext q
    congr 1
    exact exteriorPower.endomorphismTensor_traceNormalizedCurvatureEndomorphism (T q) (hT q)
  let : NormedAddCommGroup ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F) := inferInstance
  let : NormedSpace ℝ ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F) := inferInstance
  let : NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin (2 + 2) => F) ℝ) := inferInstance
  let : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin (2 + 2) => F) ℝ) := inferInstance
  let : ∀ x, Module ℝ ((⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x)) := fun x => inferInstance
  have hP := (Bundle.ExteriorPower.contMDiff_endomorphismTensor_hom (I := I) F V 2).of_le hn
  have hPc := (hP (b p)).comp_contMDiffWithinAt p
    (contMDiffWithinAt_totalSpace.mp hTsmooth).1
  exact ContMDiffWithinAt.of_clm_bundle_apply_of_injective
    (F := (⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F)
    (G := ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
    (V := fun x => (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x))
    (W := Bundle.continuousMultilinearMap ℝ 4 F V)
    hPc hAs (exteriorPower.endomorphismTensor_injective 2)

end Map

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
  intro x
  exact contMDiffWithinAt_univ.mp
    (contMDiffWithinAt_traceNormalizedCurvatureEndomorphism F V n hn T hT
      (hTsmooth x).contMDiffWithinAt)

theorem contMDiffOnSpacetimeEndomorphism_traceNormalizedCurvatureEndomorphism
    (T : ℝ → ∀ x, Bundle.continuousMultilinearMap ℝ 4 F V x)
    (hT : ∀ t x, IsAlgCurvForm (fun a b c d => T t x ![a, b, c, d]))
    {U : Set (ℝ × M)}
    (hTsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)) ∞
      (fun p : ℝ × M => TotalSpace.mk'
        (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
        (E := Bundle.continuousMultilinearMap ℝ 4 F V) p.2 (T p.1 p.2)) U) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    ContMDiffOnSpacetimeEndomorphism (I := I) (F := ⋀[ℝ]^2 F)
      (V := fun x => ⋀[ℝ]^2 (V x)) (n := ∞)
      (fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism (T t x) (hT t x)) U := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let := Bundle.ExteriorPower.fiberBundle F V 2
  let := Bundle.ExteriorPower.vector_bundle F V 2
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  apply contMDiffOnSpacetimeEndomorphism_of_contMDiffOn_hom_bundle
  intro p hp
  exact contMDiffWithinAt_traceNormalizedCurvatureEndomorphism F V ∞ le_rfl
    (fun q : ℝ × M => T q.1 q.2) (fun q => hT q.1 q.2)
    (hTsmooth p hp)

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
