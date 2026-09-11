import DifferentialGeometry.Geometry.Connection.TensorNabla.ExteriorPowerEndomorphismPullback
import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle

noncomputable section

open CovariantDerivative
open DifferentialGeometry.HomConnectionGen
open DifferentialGeometry.Geometry.Curvature (covApply)
open scoped Bundle Manifold ContDiff

private theorem comp_sub_of_comp_eq {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : U →L[ℝ] V) {A B : U →L[ℝ] U} {C D : V →L[ℝ] V}
    (hA : e.comp A = C.comp e) (hB : e.comp B = D.comp e) :
    e.comp (A - B) = (C - D).comp e := by
  rw [ContinuousLinearMap.comp_sub, hA, hB, ContinuousLinearMap.sub_comp]

namespace DifferentialGeometry.Geometry.Connection

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

private theorem secondCovDeriv_hom_conjugate_of_first
    (Q : ∀ y, V₁ y ≃L[ℝ] V₂ y)
    (D : CovariantDerivative I F₁ V₁) (C : CovariantDerivative I F₂ V₂)
    [ContMDiffCovariantDerivative C ∞]
    (hfirst : ∀ (S : ContMDiffSection I (F₂ →L[ℝ] F₂) ∞ (fun y => V₂ y →L[ℝ] V₂ y))
      (y : M) (v : TangentSpace I y),
      (Q y).toContinuousLinearMap.comp
          (homBundleCovariantDerivativeGen I M F₁ V₁ F₁ V₁ D D
            (fun z => (Q z).symm.toContinuousLinearMap.comp
              ((S z).comp (Q z).toContinuousLinearMap)) y v) =
        (homBundleCovariantDerivativeGen I M F₂ V₂ F₂ V₂ C C S y v).comp
          (Q y).toContinuousLinearMap)
    (base : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : ContMDiffSection I (F₂ →L[ℝ] F₂) ∞ (fun y => V₂ y →L[ℝ] V₂ y))
    (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) (X : TangentSpace I x) :
    let DE := homBundleCovariantDerivativeGen I M F₁ V₁ F₁ V₁ D D
    let CE := homBundleCovariantDerivativeGen I M F₂ V₂ F₂ V₂ C C
    let B := fun y => (Q y).symm.toContinuousLinearMap.comp ((A y).comp (Q y).toContinuousLinearMap)
    (Q x).toContinuousLinearMap.comp (DE (covApply DE Y B) x X - DE B x (base Y x X)) =
      (CE (covApply CE Y (fun y => A y)) x X - CE A x (base Y x X)).comp (Q x).toContinuousLinearMap := by
  let DE := homBundleCovariantDerivativeGen I M F₁ V₁ F₁ V₁ D D
  let CE := homBundleCovariantDerivativeGen I M F₂ V₂ F₂ V₂ C C
  let B := fun y => (Q y).symm.toContinuousLinearMap.comp ((A y).comp (Q y).toContinuousLinearMap)
  let T : ContMDiffSection I (F₂ →L[ℝ] F₂) ∞ (fun y => V₂ y →L[ℝ] V₂ y) :=
    ⟨covApply CE Y (fun y => A y), contMDiffOn_univ.mp
      (Curvature.covApply_contMDiffOn (cov := CE) Y.contMDiff (by simpa using A.contMDiff))⟩
  have hDB : covApply DE Y B = fun y => (Q y).symm.toContinuousLinearMap.comp
      ((T y).comp (Q y).toContinuousLinearMap) := by
    funext y
    exact (ContinuousLinearEquiv.eq_toContinuousLinearMap_symm_comp _ _).mpr (hfirst A y (Y y))
  have hleft := congrArg (fun s => (Q x).toContinuousLinearMap.comp
    (DE s x X - DE B x (base Y x X))) hDB
  exact hleft.trans (comp_sub_of_comp_eq (Q x).toContinuousLinearMap
    (hfirst T x X) (hfirst A x (base Y x X)))

theorem map_secondCovDeriv_hom_exteriorPower_conjugate
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun y => V₁ y →L[ℝ] V₂ y))))
    (cov : CovariantDerivative I F₂ V₂) [ContMDiffCovariantDerivative cov ∞]
    (base : CovariantDerivative I E (TangentSpace I : M → Type _)) (k : ℕ) :
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
    ∀ (A : ContMDiffSection I ((⋀[ℝ]^k F₂) →L[ℝ] ⋀[ℝ]^k F₂) ∞
        (fun y => (⋀[ℝ]^k (V₂ y)) →L[ℝ] ⋀[ℝ]^k (V₂ y)))
      (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) (X : TangentSpace I x),
      let Q := fun y => _root_.exteriorPower.mapContinuousLinearEquiv k (φ y)
      let D := (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov).exteriorPower k
      let C := cov.exteriorPower k
      let DE := homBundleCovariantDerivativeGen I M _ _ _ _ D D
      let CE := homBundleCovariantDerivativeGen I M _ _ _ _ C C
      let B := fun y => (Q y).symm.toContinuousLinearMap.comp ((A y).comp (Q y).toContinuousLinearMap)
      (Q x).toContinuousLinearMap.comp
          (DE (covApply DE Y B) x X - DE B x (base Y x X)) =
        (CE (covApply CE Y (fun y => A y)) x X -
          CE (fun y => A y) x (base Y x X)).comp (Q x).toContinuousLinearMap := by
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
  let := cov.exteriorPower_contMDiff k
  intro A Y x X
  exact secondCovDeriv_hom_conjugate_of_first
    (fun y => _root_.exteriorPower.mapContinuousLinearEquiv k (φ y))
    ((pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov).exteriorPower k)
    (cov.exteriorPower k)
    (fun S y v => map_homBundleCovariantDerivativeGen_exteriorPower_conjugate
      φ hφ cov k S y S.mdifferentiableAt v) base A Y x X

theorem map_rawBundleConnLap_hom_exteriorPower_conjugate
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun y => V₁ y →L[ℝ] V₂ y))))
    (cov : CovariantDerivative I F₂ V₂) [ContMDiffCovariantDerivative cov ∞]
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
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
    ∀ (A : ContMDiffSection I ((⋀[ℝ]^k F₂) →L[ℝ] ⋀[ℝ]^k F₂) ∞
        (fun y => (⋀[ℝ]^k (V₂ y)) →L[ℝ] ⋀[ℝ]^k (V₂ y))) (x : M),
      let Q := fun y => _root_.exteriorPower.mapContinuousLinearEquiv k (φ y)
      let D := (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov).exteriorPower k
      let C := cov.exteriorPower k
      let DE := homBundleCovariantDerivativeGen I M _ _ _ _ D D
      let CE := homBundleCovariantDerivativeGen I M _ _ _ _ C C
      let B := fun y => (Q y).symm.toContinuousLinearMap.comp ((A y).comp (Q y).toContinuousLinearMap)
      (Q x).toContinuousLinearMap.comp (rawBundleConnLap g DE B x) =
        (rawBundleConnLap g CE (fun y => A y) x).comp (Q x).toContinuousLinearMap := by
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
  intro A x
  apply ContinuousLinearMap.ext
  intro a
  simp only [ContinuousLinearMap.comp_apply, rawBundleConnLap_def, _root_.sum_apply,
    sub_apply, map_sum, map_sub]
  apply Finset.sum_congr rfl
  intro i _
  let : NeZero (Module.finrank ℝ E) :=
    ⟨Nat.ne_of_gt ((Nat.zero_le i.val).trans_lt i.isLt)⟩
  have h := map_secondCovDeriv_hom_exteriorPower_conjugate φ hφ cov (LeviCivita g) k A
    ⟨smoothOrthoFrame g x i, smoothOrthoFrame_smooth g x i⟩ x (smoothOrthoFrame g x i x)
  simpa only [ContMDiffSection.coeFn_mk, ContinuousLinearMap.comp_apply, sub_apply, map_sub] using
    congrArg (fun L => L a) h

end DifferentialGeometry.Geometry.Connection
