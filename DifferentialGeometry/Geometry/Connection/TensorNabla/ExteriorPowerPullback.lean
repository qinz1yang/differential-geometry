import DifferentialGeometry.Geometry.Metric.ExteriorPowerBundleMaps
import DifferentialGeometry.Geometry.Connection.TensorNabla.ExteriorPower

noncomputable section

open scoped Bundle Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (Bundle.TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, InnerProductSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (Bundle.TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, InnerProductSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]

private instance alternatingFiniteDimensional
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (k : ℕ) :
    FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
    (Module.finBasis ℝ F)).finiteDimensional_of_finite

theorem exteriorPower_map
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun y => V₁ y →L[ℝ] V₂ y))))
    (cov : CovariantDerivative I F₂ V₂) (k : ℕ)
    (u : ∀ x, ⋀[ℝ]^k (V₁ x)) (x : M) (X : TangentSpace I x) :
    letI : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
    letI : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
    letI := Bundle.ExteriorPower.totalSpaceTopology F₁ V₁ k
    letI := Bundle.ExteriorPower.fiberBundle F₁ V₁ k
    letI := Bundle.ExteriorPower.vector_bundle F₁ V₁ k
    letI := Bundle.ExteriorPower.totalSpaceTopology F₂ V₂ k
    letI := Bundle.ExteriorPower.fiberBundle F₂ V₂ k
    letI := Bundle.ExteriorPower.vector_bundle F₂ V₂ k
    MDifferentiableAt I (I.prod 𝓘(ℝ, ⋀[ℝ]^k F₁))
      (fun y => (⟨y, u y⟩ : Bundle.TotalSpace (⋀[ℝ]^k F₁) (fun z => ⋀[ℝ]^k (V₁ z)))) x →
      cov.exteriorPower k
          (fun y => _root_.exteriorPower.map k (φ y).toLinearEquiv.toLinearMap (u y)) x X =
        _root_.exteriorPower.map k (φ x).toLinearEquiv.toLinearMap
          ((pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov).exteriorPower
            k u x X) := by
  let : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
  let : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
  let := Bundle.ExteriorPower.totalSpaceTopology F₁ V₁ k
  let := Bundle.ExteriorPower.fiberBundle F₁ V₁ k
  let := Bundle.ExteriorPower.vector_bundle F₁ V₁ k
  let := Bundle.ExteriorPower.totalSpaceTopology F₂ V₂ k
  let := Bundle.ExteriorPower.fiberBundle F₂ V₂ k
  let := Bundle.ExteriorPower.vector_bundle F₂ V₂ k
  intro hu
  let D := pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov
  let W := fun y => _root_.exteriorPower.map k (φ y).toLinearEquiv.toLinearMap (u y)
  have hmap := Bundle.ExteriorPower.contMDiff_mapContinuousLinearMap k 1
    (fun y => (φ y).toContinuousLinearMap) hφ
  have hW := ((hmap x).mdifferentiableAt one_ne_zero).clm_bundle_apply hu
  apply (_root_.exteriorPower.alternatingDualEquiv k).injective
  apply ContinuousLinearMap.ext
  intro a
  obtain ⟨A, hA⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := F₂ [⋀^Fin k]→L[ℝ] ℝ)
    (V := Bundle.continuousAlternatingMap ℝ (Fin k) F₂ V₂ ℝ (Bundle.Trivial M ℝ))
    (n := (⊤ : ℕ∞)) x a
  let B := fun y => (A y).compContinuousLinearMap (φ y).toContinuousLinearMap
  have hB := A.mdifferentiableAt.alternating_bundle_comp ((hφ x).mdifferentiableAt one_ne_zero)
  have hleft := exteriorPower_alternatingDualEquiv_apply cov k W A x X A.mdifferentiableAt hW
  have hright := (_root_.exteriorPower.alternatingDualEquiv_map_apply k
    (φ x).toContinuousLinearMap (D.exteriorPower k u x X) (A x)).trans
      (exteriorPower_alternatingDualEquiv_apply D k u B x X hB hu)
  have hfun : (fun y => _root_.exteriorPower.alternatingDualEquiv k (W y) (A y)) =
      (fun y => _root_.exteriorPower.alternatingDualEquiv k (u y) (B y)) := by
    funext y
    exact _root_.exteriorPower.alternatingDualEquiv_map_apply k (φ y).toContinuousLinearMap (u y) (A y)
  have hderiv := congrArg (fun f : M → ℝ => mvfderiv (I := I) f x X) hfun
  have hDB := alternating_pullbackFiberwiseLinearEquiv φ hφ cov k A.mdifferentiableAt X
  have hterm : _root_.exteriorPower.alternatingDualEquiv k (W x)
      (alternating cov k A x X) =
        _root_.exteriorPower.alternatingDualEquiv k (u x) (alternating D k B x X) := by
    exact (_root_.exteriorPower.alternatingDualEquiv_map_apply k
      (φ x).toContinuousLinearMap (u x) (alternating cov k A x X)).trans
        (congrArg (_root_.exteriorPower.alternatingDualEquiv k (u x)) hDB.symm)
  have hpair := hleft.trans ((congrArg₂ (· - ·) hderiv hterm).trans hright.symm)
  exact hA ▸ hpair

theorem exteriorPower_pullback_eq_pullback_map
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun y => V₁ y →L[ℝ] V₂ y))))
    (cov : CovariantDerivative I F₂ V₂) (k : ℕ)
    (u : ∀ x, ⋀[ℝ]^k (V₁ x)) (x : M) (X : TangentSpace I x) :
    letI : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
    letI : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
    letI := Bundle.ExteriorPower.totalSpaceTopology F₁ V₁ k
    letI := Bundle.ExteriorPower.fiberBundle F₁ V₁ k
    letI := Bundle.ExteriorPower.vector_bundle F₁ V₁ k
    letI := Bundle.ExteriorPower.totalSpaceTopology F₂ V₂ k
    letI := Bundle.ExteriorPower.fiberBundle F₂ V₂ k
    letI := Bundle.ExteriorPower.vector_bundle F₂ V₂ k
    MDifferentiableAt I (I.prod 𝓘(ℝ, ⋀[ℝ]^k F₁))
      (fun y => (⟨y, u y⟩ : Bundle.TotalSpace (⋀[ℝ]^k F₁) (fun z => ⋀[ℝ]^k (V₁ z)))) x →
      (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv)
        hφ.clm_bundle_map cov).exteriorPower k u x X =
      pullbackFiberwiseLinearEquiv
        (fun y => (_root_.exteriorPower.mapContinuousLinearEquiv k (φ y)).toLinearEquiv)
        (Bundle.ExteriorPower.contMDiff_mapContinuousLinearMap k 1
          (fun y => (φ y).toContinuousLinearMap) hφ).clm_bundle_map
        (cov.exteriorPower k) u x X := by
  let : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
  let : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
  let := Bundle.ExteriorPower.totalSpaceTopology F₁ V₁ k
  let := Bundle.ExteriorPower.fiberBundle F₁ V₁ k
  let := Bundle.ExteriorPower.vector_bundle F₁ V₁ k
  let := Bundle.ExteriorPower.totalSpaceTopology F₂ V₂ k
  let := Bundle.ExteriorPower.fiberBundle F₂ V₂ k
  let := Bundle.ExteriorPower.vector_bundle F₂ V₂ k
  intro hu
  apply (_root_.exteriorPower.mapContinuousLinearEquiv k (φ x)).injective
  exact (exteriorPower_map φ hφ cov k u x X hu).symm.trans
    (map_pullbackFiberwiseLinearEquiv_apply
      (fun y => (_root_.exteriorPower.mapContinuousLinearEquiv k (φ y)).toLinearEquiv)
      (Bundle.ExteriorPower.contMDiff_mapContinuousLinearMap k 1
        (fun y => (φ y).toContinuousLinearMap) hφ).clm_bundle_map
      (cov.exteriorPower k) u x X).symm

end CovariantDerivative
