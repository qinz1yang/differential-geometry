import DifferentialGeometry.Tensor.Alternating.BundleCompSmooth
import DifferentialGeometry.Geometry.Connection.TensorNabla.Alternating
import DifferentialGeometry.Geometry.Connection.Laplacian.PullbackHom

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]

private instance alternatingModelFiniteDimensional
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (k : ℕ) : FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
    (Module.finBasis ℝ F)).finiteDimensional_of_finite

namespace CovariantDerivative

theorem alternating_congrLeft
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) (k : ℕ)
    {a : ∀ x, V₁ x [⋀^Fin k]→L[ℝ] ℝ} {x : M}
    (ha : MDifferentiableAt I (I.prod 𝓘(ℝ, F₁ [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, a y⟩ : TotalSpace (F₁ [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F₁ V₁ ℝ (Bundle.Trivial M ℝ)))) x)
    (X : TangentSpace I x) :
    alternating cov k
        (fun y => (φ y).continuousAlternatingMapCongrLeft (ι := Fin k) (a y)) x X =
      (φ x).continuousAlternatingMapCongrLeft (ι := Fin k)
        (alternating
          (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov)
          k a x X) := by
  let Q := fun y => (φ y).continuousAlternatingMapCongrLeft (ι := Fin k) (F := ℝ)
  have hQ := ContMDiff.alternating_bundle_congrLeft φ hφ k
  have hQa := ((hQ x).mdifferentiableAt (by simp)).clm_bundle_apply ha
  have h := alternating_pullbackFiberwiseLinearEquiv φ hφ cov k hQa X
  change alternating
      (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov)
      k (fun y => (Q y (a y)).compContinuousLinearMap (φ y).toContinuousLinearMap) x X =
    (Q x).symm (alternating cov k (fun y => Q y (a y)) x X) at h
  have hcancel : (fun y => (Q y (a y)).compContinuousLinearMap
      (φ y).toContinuousLinearMap) = a := by
    funext y
    exact (Q y).symm_apply_apply (a y)
  rw [hcancel] at h
  exact ((Q x).eq_symm_apply.mp h).symm

theorem alternating_pullback_eq_pullback_congrLeft
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) (k : ℕ)
    {a : ∀ x, V₁ x [⋀^Fin k]→L[ℝ] ℝ} {x : M}
    (ha : MDifferentiableAt I (I.prod 𝓘(ℝ, F₁ [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, a y⟩ : TotalSpace (F₁ [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F₁ V₁ ℝ (Bundle.Trivial M ℝ)))) x)
    (X : TangentSpace I x) :
    alternating
        (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov)
        k a x X =
      pullbackFiberwiseLinearEquiv
        (fun y => ((φ y).continuousAlternatingMapCongrLeft (ι := Fin k) (F := ℝ)).toLinearEquiv)
        (ContMDiff.alternating_bundle_congrLeft φ hφ k).clm_bundle_map
        (alternating cov k) a x X := by
  let Q := fun y => (φ y).continuousAlternatingMapCongrLeft (ι := Fin k) (F := ℝ)
  change alternating
      (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov)
      k a x X = (Q x).symm (alternating cov k (fun y => Q y (a y)) x X)
  exact ((Q x).eq_symm_apply).mpr (alternating_congrLeft φ hφ cov k ha X).symm

end CovariantDerivative

namespace DifferentialGeometry.HomConnectionGen

theorem homBundleCovariantDerivativeGen_alternating_pullback_eq
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) (k : ℕ)
    {A : ∀ x, (V₁ x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V₁ x [⋀^Fin k]→L[ℝ] ℝ}
    {x : M}
    (hA : MDifferentiableAt I
      (I.prod 𝓘(ℝ, (F₁ [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] F₁ [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, A y⟩ : TotalSpace
        ((F₁ [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] F₁ [⋀^Fin k]→L[ℝ] ℝ)
        (fun y => (V₁ y [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V₁ y [⋀^Fin k]→L[ℝ] ℝ))) x)
    (X : TangentSpace I x) :
    let D := CovariantDerivative.alternating
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
    let P := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => ((φ y).continuousAlternatingMapCongrLeft (ι := Fin k) (F := ℝ)).toLinearEquiv)
      (ContMDiff.alternating_bundle_congrLeft φ hφ k).clm_bundle_map
      (CovariantDerivative.alternating cov k)
    homBundleCovariantDerivativeGen I M _ _ _ _ D D A x X =
      homBundleCovariantDerivativeGen I M _ _ _ _ P P A x X := by
  dsimp only
  ext a
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := F₁ [⋀^Fin k]→L[ℝ] ℝ)
    (V := Bundle.continuousAlternatingMap ℝ (Fin k) F₁ V₁ ℝ (Bundle.Trivial M ℝ))
    (n := (⊤ : ℕ∞)) x a
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  rw [← hY, ← hZ]
  rw [homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
      I M _ _ _ _ _ _ A hA Z.mdifferentiableAt Y.mdifferentiableAt,
    homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
      I M _ _ _ _ _ _ A hA Z.mdifferentiableAt Y.mdifferentiableAt,
    CovariantDerivative.alternating_pullback_eq_pullback_congrLeft φ hφ cov k
      (hA.clm_bundle_apply Y.mdifferentiableAt) (Z x),
    CovariantDerivative.alternating_pullback_eq_pullback_congrLeft φ hφ cov k
      Y.mdifferentiableAt (Z x)]

theorem homBundleCovariantDerivativeGen_alternating_congrLeft
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) (k : ℕ) :
    let D := CovariantDerivative.alternating
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
    homBundleCovariantDerivativeGen I M _ _ _ _ D (CovariantDerivative.alternating cov k)
      (fun y => ((φ y).continuousAlternatingMapCongrLeft (ι := Fin k) (F := ℝ)).toContinuousLinearMap) = 0 := by
  dsimp only
  funext x
  apply ContinuousLinearMap.ext
  intro X
  apply ContinuousLinearMap.ext
  intro a
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := F₁ [⋀^Fin k]→L[ℝ] ℝ)
    (V := Bundle.continuousAlternatingMap ℝ (Fin k) F₁ V₁ ℝ (Bundle.Trivial M ℝ))
    (n := (⊤ : ℕ∞)) x a
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have hQ := ContMDiff.alternating_bundle_congrLeft φ hφ k
  rw [← hY, ← hZ]
  rw [homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt I M _ _ _ _ _ _ _
    ((hQ x).mdifferentiableAt (by simp)) Z.mdifferentiableAt Y.mdifferentiableAt]
  change CovariantDerivative.alternating cov k
      (fun y => (φ y).continuousAlternatingMapCongrLeft (ι := Fin k) (Y y)) x (Z x) -
    (φ x).continuousAlternatingMapCongrLeft (ι := Fin k)
      (CovariantDerivative.alternating
        (CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k Y x (Z x)) = 0
  exact sub_eq_zero.mpr
    (CovariantDerivative.alternating_congrLeft φ hφ cov k Y.mdifferentiableAt (Z x))

theorem map_homBundleCovariantDerivativeGen_alternating_conjugate
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) (k : ℕ)
    {A : ∀ x, (V₂ x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V₂ x [⋀^Fin k]→L[ℝ] ℝ}
    {x : M}
    (hA : MDifferentiableAt I
      (I.prod 𝓘(ℝ, (F₂ [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] F₂ [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, A y⟩ : TotalSpace
        ((F₂ [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] F₂ [⋀^Fin k]→L[ℝ] ℝ)
        (fun y => (V₂ y [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V₂ y [⋀^Fin k]→L[ℝ] ℝ))) x)
    (X : TangentSpace I x) :
    let Q := fun y => (φ y).continuousAlternatingMapCongrLeft (ι := Fin k) (F := ℝ)
    let D := CovariantDerivative.alternating
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
    let C := CovariantDerivative.alternating cov k
    (Q x).toContinuousLinearMap.comp
        (homBundleCovariantDerivativeGen I M _ _ _ _ D D
          (fun y => (Q y).symm.toContinuousLinearMap.comp
            ((A y).comp (Q y).toContinuousLinearMap)) x X) =
      (homBundleCovariantDerivativeGen I M _ _ _ _ C C A x X).comp
        (Q x).toContinuousLinearMap := by
  let Q := fun y => (φ y).continuousAlternatingMapCongrLeft (ι := Fin k) (F := ℝ)
  let _ : CompleteSpace (F₁ [⋀^Fin k]→L[ℝ] ℝ) := FiniteDimensional.complete ℝ _
  have hQ := ContMDiff.alternating_bundle_congrLeft φ hφ k
  have hQinv : ContMDiff I
      (I.prod 𝓘(ℝ, (F₂ [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] F₁ [⋀^Fin k]→L[ℝ] ℝ)) 1
      (fun y => (⟨y, (Q y).symm.toContinuousLinearMap⟩ : TotalSpace
        ((F₂ [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] F₁ [⋀^Fin k]→L[ℝ] ℝ)
        (fun y => (V₂ y [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V₁ y [⋀^Fin k]→L[ℝ] ℝ))) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hQ.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  have hB := ((hQinv x).mdifferentiableAt (by simp)).clm_bundle_comp
    (hA.clm_bundle_comp ((hQ x).mdifferentiableAt (by simp)))
  have heq := homBundleCovariantDerivativeGen_alternating_pullback_eq φ hφ cov k hB X
  have h := map_homBundleCovariantDerivativeGen_conjugate Q hQ
    (CovariantDerivative.alternating cov k) hA X
  exact (congrArg ((Q x).toContinuousLinearMap.comp) heq).trans h

end DifferentialGeometry.HomConnectionGen

namespace DifferentialGeometry.Geometry.Connection

open CovariantDerivative
open DifferentialGeometry.HomConnectionGen
open DifferentialGeometry.Geometry.Curvature (covApply)

theorem map_secondCovDeriv_hom_alternating_conjugate
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) [ContMDiffCovariantDerivative cov ∞]
    (base : CovariantDerivative I E (TangentSpace I : M → Type _)) (k : ℕ)
    (A : ContMDiffSection I
      ((F₂ [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] F₂ [⋀^Fin k]→L[ℝ] ℝ) ∞
      (fun y => (V₂ y [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V₂ y [⋀^Fin k]→L[ℝ] ℝ))
    (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) (X : TangentSpace I x) :
    let Q := fun y => (φ y).continuousAlternatingMapCongrLeft (ι := Fin k) (F := ℝ)
    let D := alternating
      (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
    let C := alternating cov k
    let DE := homBundleCovariantDerivativeGen I M _ _ _ _ D D
    let CE := homBundleCovariantDerivativeGen I M _ _ _ _ C C
    let B := fun y => (Q y).symm.toContinuousLinearMap.comp
      ((A y).comp (Q y).toContinuousLinearMap)
    (Q x).toContinuousLinearMap.comp
        (DE (covApply DE Y B) x X - DE B x (base Y x X)) =
      (CE (covApply CE Y (fun y => A y)) x X -
        CE (fun y => A y) x (base Y x X)).comp (Q x).toContinuousLinearMap := by
  let Q := fun y => (φ y).continuousAlternatingMapCongrLeft (ι := Fin k) (F := ℝ)
  let D := alternating
    (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
  let C := alternating cov k
  let DE := homBundleCovariantDerivativeGen I M _ _ _ _ D D
  let CE := homBundleCovariantDerivativeGen I M _ _ _ _ C C
  let B := fun y => (Q y).symm.toContinuousLinearMap.comp
    ((A y).comp (Q y).toContinuousLinearMap)
  let T : ContMDiffSection I
      ((F₂ [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] F₂ [⋀^Fin k]→L[ℝ] ℝ) ∞
      (fun y => (V₂ y [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V₂ y [⋀^Fin k]→L[ℝ] ℝ) :=
    ⟨covApply CE Y (fun y => A y), contMDiffOn_univ.mp
      (Curvature.covApply_contMDiffOn (cov := CE) Y.contMDiff
        (by simpa using A.contMDiff))⟩
  have hfirst (S : ContMDiffSection I
      ((F₂ [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] F₂ [⋀^Fin k]→L[ℝ] ℝ) ∞
      (fun y => (V₂ y [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V₂ y [⋀^Fin k]→L[ℝ] ℝ))
      (y : M) (v : TangentSpace I y) :
      (Q y).toContinuousLinearMap.comp
          (DE (fun z => (Q z).symm.toContinuousLinearMap.comp
            ((S z).comp (Q z).toContinuousLinearMap)) y v) =
        (CE (fun z => S z) y v).comp (Q y).toContinuousLinearMap :=
    map_homBundleCovariantDerivativeGen_alternating_conjugate φ hφ cov k
      S.mdifferentiableAt v
  have hDB : covApply DE Y B = fun y => (Q y).symm.toContinuousLinearMap.comp
      ((T y).comp (Q y).toContinuousLinearMap) := by
    funext y
    apply ContinuousLinearMap.ext
    intro a
    apply (Q y).injective
    have h := congrArg (fun L => L a) (hfirst A y (Y y))
    change Q y (DE B y (Y y) a) = Q y ((Q y).symm (T y (Q y a)))
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact h
  change (Q x).toContinuousLinearMap.comp
      (DE (covApply DE Y B) x X - DE B x (base Y x X)) = _
  rw [hDB]
  apply ContinuousLinearMap.ext
  intro a
  simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
  exact congrArg₂ (fun u v => u - v)
    (congrArg (fun L => L a) (hfirst T x X))
    (congrArg (fun L => L a) (hfirst A x (base Y x X)))

theorem map_rawBundleConnLap_hom_alternating_conjugate
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) [ContMDiffCovariantDerivative cov ∞]
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (A : ContMDiffSection I
      ((F₂ [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] F₂ [⋀^Fin k]→L[ℝ] ℝ) ∞
      (fun y => (V₂ y [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V₂ y [⋀^Fin k]→L[ℝ] ℝ))
    (x : M) :
    let Q := fun y => (φ y).continuousAlternatingMapCongrLeft (ι := Fin k) (F := ℝ)
    let D := alternating
      (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k
    let C := alternating cov k
    (Q x).toContinuousLinearMap.comp
        (rawBundleConnLap g (homBundleCovariantDerivativeGen I M _ _ _ _ D D)
          (fun y => (Q y).symm.toContinuousLinearMap.comp
            ((A y).comp (Q y).toContinuousLinearMap)) x) =
      (rawBundleConnLap g (homBundleCovariantDerivativeGen I M _ _ _ _ C C)
        (fun y => A y) x).comp (Q x).toContinuousLinearMap := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro a
  simp only [ContinuousLinearMap.comp_apply, rawBundleConnLap_def, _root_.sum_apply,
    sub_apply, map_sum, map_sub]
  apply Finset.sum_congr rfl
  intro i _
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨Nat.ne_of_gt ((Nat.zero_le i.val).trans_lt i.isLt)⟩
  have h := map_secondCovDeriv_hom_alternating_conjugate φ hφ cov (LeviCivita g) k A
    ⟨smoothOrthoFrame g x i, smoothOrthoFrame_smooth g x i⟩ x
    (smoothOrthoFrame g x i x)
  simpa only [ContMDiffSection.coeFn_mk, ContinuousLinearMap.comp_apply, sub_apply, map_sub] using
    congrArg (fun L => L a) h

end DifferentialGeometry.Geometry.Connection
