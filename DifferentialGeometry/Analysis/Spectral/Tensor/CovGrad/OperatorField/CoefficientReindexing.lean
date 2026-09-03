import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.CovariantCalculus
import DifferentialGeometry.Tensor.Multilinear.Basis

noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.Multilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def reindexCoeffFibGen (r s : ℕ) (σ' : Equiv.Perm (Fin r)) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x :=
  A.comp
    ((tensor0SSpaceContinuousLinearEquiv (I := I) r
      x).symm.toContinuousLinearMap.comp
      (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            σ').toContinuousLinearEquiv.toContinuousLinearMap).comp
        (tensor0SSpaceContinuousLinearEquiv (I := I) r x).toContinuousLinearMap))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem reindexCoeffFibGen_apply (r s : ℕ) (σ' : Equiv.Perm (Fin r)) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x)
    (D : Tensor0SSpace r I x) :
    reindexCoeffFibGen (I := I) r s σ' x A D =
      A (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SSpace.toModel D))) := by
  rw [reindexCoeffFibGen, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  congr 1

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem reindexCoeffFibGen_contMDiff (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) x
        (reindexCoeffFibGen (I := I) r s σ' x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SSpace r I x)
    (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
    (φ := fun x => reindexCoeffFibGen (I := I) r s σ' x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x))
  intro Y
  have hYσ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) x
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SSpace.toModel (Y x))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SSpace.toModel (Y x))) : Tensor0SSpace r I x))).mpr ?_
    have hYcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Y x)).mp Y.contMDiff
    intro τ x₀
    refine (hYcoord (τ ∘ σ') x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ'
        (Tensor0SSpace.toModel (Y x)))
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
            ((Module.finBasis ℝ E) (τ j)))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  have hRY := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff hYσ
  refine hRY.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SSpace s I z) x t)
    (reindexCoeffFibGen_apply (I := I) r s σ' x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)).symm

noncomputable def reindexCoeffGen (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    SmoothCcTensor g₀ r s where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace r s I x from
          reindexCoeffFibGen (I := I) r s σ' x
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x))
      contMDiff_toFun := reindexCoeffFibGen_contMDiff (I := I) (M := M) g₀ r s R σ' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
@[simp] theorem reindexCoeffGen_toSection (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) (x : M) :
    (reindexCoeffGen (I := I) (M := M) g₀ r s R σ').toSection x =
      (show TensorRSSpace r s I x from
        reindexCoeffFibGen (I := I) r s σ' x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x)) := rfl

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
