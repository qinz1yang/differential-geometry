import DifferentialGeometry.Geometry.Connection.TensorNabla.ExteriorPowerPullback
import DifferentialGeometry.Geometry.Connection.PullbackHom

noncomputable section

open CovariantDerivative
open scoped Bundle Manifold ContDiff

namespace DifferentialGeometry.HomConnectionGen

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

theorem homBundleCovariantDerivativeGen_exteriorPower_map
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun y => V₁ y →L[ℝ] V₂ y))))
    (cov : CovariantDerivative I F₂ V₂) (k : ℕ) :
    letI : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
    letI : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
    letI := Bundle.ExteriorPower.totalSpaceTopology F₁ V₁ k
    letI := Bundle.ExteriorPower.fiberBundle F₁ V₁ k
    letI := Bundle.ExteriorPower.vector_bundle F₁ V₁ k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F₁ V₁ k
    letI := Bundle.ExteriorPower.totalSpaceTopology F₂ V₂ k
    letI := Bundle.ExteriorPower.fiberBundle F₂ V₂ k
    letI := Bundle.ExteriorPower.vector_bundle F₂ V₂ k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F₂ V₂ k
    let D := (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov).exteriorPower k
    homBundleCovariantDerivativeGen I M _ _ _ _ D (cov.exteriorPower k)
      (fun y => _root_.exteriorPower.mapContinuousLinearMap k (φ y).toContinuousLinearMap) = 0 := by
  let : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
  let : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
  let := Bundle.ExteriorPower.totalSpaceTopology F₁ V₁ k
  let := Bundle.ExteriorPower.fiberBundle F₁ V₁ k
  let := Bundle.ExteriorPower.vector_bundle F₁ V₁ k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F₁ V₁ k
  let := Bundle.ExteriorPower.totalSpaceTopology F₂ V₂ k
  let := Bundle.ExteriorPower.fiberBundle F₂ V₂ k
  let := Bundle.ExteriorPower.vector_bundle F₂ V₂ k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F₂ V₂ k
  dsimp only
  funext x
  apply ContinuousLinearMap.ext
  intro X
  apply ContinuousLinearMap.ext
  intro a
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := ⋀[ℝ]^k F₁) (V := fun y => ⋀[ℝ]^k (V₁ y)) (n := (⊤ : ℕ∞)) x a
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have hQ := Bundle.ExteriorPower.contMDiff_mapContinuousLinearMap k 1
    (fun y => (φ y).toContinuousLinearMap) hφ
  rw [← hY, ← hZ]
  rw [homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt I M _ _ _ _ _ _ _
    ((hQ x).mdifferentiableAt one_ne_zero) Z.mdifferentiableAt Y.mdifferentiableAt]
  change cov.exteriorPower k
      (fun y => _root_.exteriorPower.map k (φ y).toLinearEquiv.toLinearMap (Y y)) x (Z x) -
    _root_.exteriorPower.map k (φ x).toLinearEquiv.toLinearMap
      ((pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv)
        hφ.clm_bundle_map cov).exteriorPower k Y x (Z x)) = 0
  exact sub_eq_zero.mpr (exteriorPower_map φ hφ cov k Y x (Z x) Y.mdifferentiableAt)

theorem map_homBundleCovariantDerivativeGen_exteriorPower_conjugate
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun y => V₁ y →L[ℝ] V₂ y))))
    (cov : CovariantDerivative I F₂ V₂) (k : ℕ) :
    letI : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
    letI : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
    letI := Bundle.ExteriorPower.totalSpaceTopology F₁ V₁ k
    letI := Bundle.ExteriorPower.fiberBundle F₁ V₁ k
    letI := Bundle.ExteriorPower.vector_bundle F₁ V₁ k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F₁ V₁ k
    letI := Bundle.ExteriorPower.totalSpaceTopology F₂ V₂ k
    letI := Bundle.ExteriorPower.fiberBundle F₂ V₂ k
    letI := Bundle.ExteriorPower.vector_bundle F₂ V₂ k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F₂ V₂ k
    ∀ (A : ∀ y, (⋀[ℝ]^k (V₂ y)) →L[ℝ] ⋀[ℝ]^k (V₂ y)) (x : M),
      MDifferentiableAt I (I.prod 𝓘(ℝ, (⋀[ℝ]^k F₂) →L[ℝ] ⋀[ℝ]^k F₂))
        (fun y => (⟨y, A y⟩ : Bundle.TotalSpace ((⋀[ℝ]^k F₂) →L[ℝ] ⋀[ℝ]^k F₂)
          (fun z => (⋀[ℝ]^k (V₂ z)) →L[ℝ] ⋀[ℝ]^k (V₂ z)))) x →
      ∀ X : TangentSpace I x,
      let Q := fun y => _root_.exteriorPower.mapContinuousLinearEquiv k (φ y)
      let D := (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov).exteriorPower k
      let C := cov.exteriorPower k
      (Q x).toContinuousLinearMap.comp
          (homBundleCovariantDerivativeGen I M _ _ _ _ D D
            (fun y => (Q y).symm.toContinuousLinearMap.comp
              ((A y).comp (Q y).toContinuousLinearMap)) x X) =
        (homBundleCovariantDerivativeGen I M _ _ _ _ C C A x X).comp
          (Q x).toContinuousLinearMap := by
  let : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
  let : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
  let := Bundle.ExteriorPower.totalSpaceTopology F₁ V₁ k
  let := Bundle.ExteriorPower.fiberBundle F₁ V₁ k
  let := Bundle.ExteriorPower.vector_bundle F₁ V₁ k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F₁ V₁ k
  let := Bundle.ExteriorPower.totalSpaceTopology F₂ V₂ k
  let := Bundle.ExteriorPower.fiberBundle F₂ V₂ k
  let := Bundle.ExteriorPower.vector_bundle F₂ V₂ k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F₂ V₂ k
  intro A x hA X
  let Q := fun y => _root_.exteriorPower.mapContinuousLinearEquiv k (φ y)
  let D := (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov).exteriorPower k
  let C := cov.exteriorPower k
  let B := fun y => (Q y).symm.toContinuousLinearMap.comp ((A y).comp (Q y).toContinuousLinearMap)
  let : CompleteSpace F₁ := FiniteDimensional.complete ℝ F₁
  have hφinv : ContMDiff I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₁)) 1
      (fun y => (⟨y, (φ y).symm.toContinuousLinearMap⟩ : Bundle.TotalSpace (F₂ →L[ℝ] F₁)
        (fun z => V₂ z →L[ℝ] V₁ z))) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hφ.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  have hQ := Bundle.ExteriorPower.contMDiff_mapContinuousLinearMap k 1
    (fun y => (φ y).toContinuousLinearMap) hφ
  have hQinv := Bundle.ExteriorPower.contMDiff_mapContinuousLinearMap k 1
    (fun y => (φ y).symm.toContinuousLinearMap) hφinv
  have hQx := (hQ x).mdifferentiableAt one_ne_zero
  have hBx := ((hQinv x).mdifferentiableAt one_ne_zero).clm_bundle_comp
    (hA.clm_bundle_comp hQx)
  have hp := homBundleCovariantDerivativeGen_exteriorPower_map φ hφ cov k
  have hl := homBundleCovariantDerivativeGen_comp D D C hBx hQx X
  have hr := homBundleCovariantDerivativeGen_comp D C C hQx hA X
  have heq : (fun y => (Q y).toContinuousLinearMap.comp (B y)) =
      (fun y => (A y).comp (Q y).toContinuousLinearMap) := by
    funext y
    apply ContinuousLinearMap.ext
    intro w
    exact (Q y).apply_symm_apply (A y (Q y w))
  change homBundleCovariantDerivativeGen I M _ _ _ _ D C
    (fun y => (Q y).toContinuousLinearMap.comp (B y)) x X = _ at hl
  rw [hp] at hl hr
  simp only [Pi.zero_apply, zero_apply, ContinuousLinearMap.zero_comp, zero_add,
    ContinuousLinearMap.comp_zero, add_zero] at hl hr
  change (Q x).toContinuousLinearMap.comp
    (homBundleCovariantDerivativeGen I M _ _ _ _ D D B x X) = _
  exact hl.symm.trans
    ((congrArg (fun s => homBundleCovariantDerivativeGen I M _ _ _ _ D C s x X) heq).trans hr)

theorem homBundleCovariantDerivativeGen_exteriorPower_conjugate
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun y => V₁ y →L[ℝ] V₂ y))))
    (cov : CovariantDerivative I F₂ V₂) (k : ℕ) :
    letI : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
    letI : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
    letI := Bundle.ExteriorPower.totalSpaceTopology F₁ V₁ k
    letI := Bundle.ExteriorPower.fiberBundle F₁ V₁ k
    letI := Bundle.ExteriorPower.vector_bundle F₁ V₁ k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F₁ V₁ k
    letI := Bundle.ExteriorPower.totalSpaceTopology F₂ V₂ k
    letI := Bundle.ExteriorPower.fiberBundle F₂ V₂ k
    letI := Bundle.ExteriorPower.vector_bundle F₂ V₂ k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F₂ V₂ k
    ∀ (A : ∀ y, (⋀[ℝ]^k (V₂ y)) →L[ℝ] ⋀[ℝ]^k (V₂ y)) (x : M),
      MDifferentiableAt I (I.prod 𝓘(ℝ, (⋀[ℝ]^k F₂) →L[ℝ] ⋀[ℝ]^k F₂))
        (fun y => (⟨y, A y⟩ : Bundle.TotalSpace ((⋀[ℝ]^k F₂) →L[ℝ] ⋀[ℝ]^k F₂)
          (fun z => (⋀[ℝ]^k (V₂ z)) →L[ℝ] ⋀[ℝ]^k (V₂ z)))) x →
      ∀ X : TangentSpace I x,
      let Q := fun y => _root_.exteriorPower.mapContinuousLinearEquiv k (φ y)
      let D := (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov).exteriorPower k
      let C := cov.exteriorPower k
      homBundleCovariantDerivativeGen I M _ _ _ _ D D
          (fun y => (Q y).symm.toContinuousLinearMap.comp
            ((A y).comp (Q y).toContinuousLinearMap)) x X =
        (Q x).symm.toContinuousLinearMap.comp
          ((homBundleCovariantDerivativeGen I M _ _ _ _ C C A x X).comp
            (Q x).toContinuousLinearMap) := by
  let : ∀ z, FiniteDimensional ℝ (V₁ z) := fun z => VectorBundle.finiteDimensional ℝ F₁ V₁ z
  let : ∀ z, FiniteDimensional ℝ (V₂ z) := fun z => VectorBundle.finiteDimensional ℝ F₂ V₂ z
  let := Bundle.ExteriorPower.totalSpaceTopology F₁ V₁ k
  let := Bundle.ExteriorPower.fiberBundle F₁ V₁ k
  let := Bundle.ExteriorPower.vector_bundle F₁ V₁ k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F₁ V₁ k
  let := Bundle.ExteriorPower.totalSpaceTopology F₂ V₂ k
  let := Bundle.ExteriorPower.fiberBundle F₂ V₂ k
  let := Bundle.ExteriorPower.vector_bundle F₂ V₂ k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F₂ V₂ k
  intro A x hA X
  exact (ContinuousLinearEquiv.eq_toContinuousLinearMap_symm_comp _ _).mpr
    (map_homBundleCovariantDerivativeGen_exteriorPower_conjugate φ hφ cov k A x hA X)

end DifferentialGeometry.HomConnectionGen
