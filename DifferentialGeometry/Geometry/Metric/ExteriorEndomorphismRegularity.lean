import DifferentialGeometry.Geometry.Metric.ExteriorEndomorphismBundle
import DifferentialGeometry.Bundle.Hom.InjectiveRegularity
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff Topology RealInnerProductSpace

namespace Bundle.ExteriorPower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

def endomorphismTensorHom (k : ℕ) (x : M) :
    letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
    ((⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x)) →L[ℝ]
      Bundle.continuousMultilinearMap ℝ (k + k) F V x := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  exact
    { exteriorPower.endomorphismTensorLinear (E := V x) k with
      cont := by
        rw [show (instTopologicalSpaceContinuousMultilinearMap ℝ (k + k) F V x) =
          ContinuousMultilinearMap.instTopologicalSpace from
          Bundle.continuousMultilinearMap.topology_eq (k + k) x]
        exact (exteriorPower.endomorphismTensorLinear (E := V x) k).toContinuousLinearMap.continuous }

theorem contMDiff_endomorphismTensor_hom (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    let P : ∀ x, ((⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x)) →L[ℝ]
        Bundle.continuousMultilinearMap ℝ (k + k) F V x :=
      fun x => endomorphismTensorHom F V k x
    ContMDiff I
      (I.prod 𝓘(ℝ, ((⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => F) ℝ)) ∞
      (fun x => TotalSpace.mk'
        (((⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F) →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => F) ℝ) x (P x)) := by
  dsimp only
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  let := contMDiffVectorBundle (IB := I) (n := ∞) F V k
  apply DifferentialGeometry.Geometry.Connection.Realization.contMDiff_clm_section_of_pointwise
    (I := I) (M := M)
    (F₁ := (⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F)
    (V₁ := fun x => (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x))
    (F₂ := ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => F) ℝ)
    (V₂ := Bundle.continuousMultilinearMap ℝ (k + k) F V)
  intro R
  exact contMDiff_endomorphismTensor (IB := I) (n := ∞) F V k R R.contMDiff

theorem contMDiff_of_endomorphismTensor (k : ℕ) (n : ℕ∞ω) (hn : n ≤ ∞) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ∀ (R : ∀ x, (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x)),
    ContMDiff I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => F) ℝ)) n
      (fun x => TotalSpace.mk'
        (ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => F) ℝ)
        (E := Bundle.continuousMultilinearMap ℝ (k + k) F V) x
        (exteriorPower.endomorphismTensor k (R x))) →
    ContMDiff I (I.prod 𝓘(ℝ, (⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F)) n
      (fun x => TotalSpace.mk' ((⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F) x (R x)) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  intro R hR
  exact ContMDiff.of_clm_bundle_apply_of_injective
    ((contMDiff_endomorphismTensor_hom (I := I) F V k).of_le hn)
    hR (fun _ => exteriorPower.endomorphismTensor_injective k)

end Bundle.ExteriorPower
