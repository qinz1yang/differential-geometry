import DifferentialGeometry.Geometry.Connection.Laplacian.SelfAdjointConjugate
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra
import DifferentialGeometry.Analysis.Calculus.InjectiveDerivative

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.HomConnectionGen
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

private theorem reaction_conjugate
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : V ≃L[ℝ] W) (A : selfAdjoint (W →L[ℝ] W))
    (B : selfAdjoint (V →L[ℝ] V))
    (hB : (B : V →L[ℝ] V) = e.symm.toContinuousLinearMap.comp
      ((A : W →L[ℝ] W).comp e.toContinuousLinearMap)) :
    (curvatureOperatorReactionSelfAdjoint3 B : V →L[ℝ] V) =
      e.symm.toContinuousLinearMap.comp
        ((curvatureOperatorReactionSelfAdjoint3 A : W →L[ℝ] W).comp
          e.toContinuousLinearMap) := by
  have hlin : (B : V →L[ℝ] V).toLinearMap =
      e.symm.toLinearEquiv.conj (A : W →L[ℝ] W).toLinearMap := by
    rw [hB]
    rfl
  have h := curvatureOperatorReactionEndomorphism3_conj
    e.symm.toLinearEquiv (A : W →L[ℝ] W).toLinearMap
  ext v
  change curvatureOperatorReactionEndomorphism3 (B : V →L[ℝ] V).toLinearMap v = _
  rw [hlin]
  exact congrArg (fun L => L v) h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, InnerProductSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle ∞ F₁ V₁ I] [IsContMDiffRiemannianBundle I ∞ F₁ V₁]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, InnerProductSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle ∞ F₂ V₂ I] [IsContMDiffRiemannianBundle I ∞ F₂ V₂]

private theorem selfAdjoint_reaction_heat_conjugate_iff
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (D : CovariantDerivative I F₁ V₁) (hD : D.IsMetricCompatible)
    (C : CovariantDerivative I F₂ V₂) (hC : C.IsMetricCompatible)
    [ContMDiffCovariantDerivative D ∞] [ContMDiffCovariantDerivative C ∞]
    (hparallel : homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂ D C
      (fun x => (φ x).toContinuousLinearEquiv.toContinuousLinearMap) = 0)
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) :
    letI : ∀ x, FiniteDimensional ℝ (V₁ x) := fun x => VectorBundle.finiteDimensional ℝ F₁ V₁ x
    letI : ∀ x, FiniteDimensional ℝ (V₂ x) := fun x => VectorBundle.finiteDimensional ℝ F₂ V₂ x
    let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := ∞)
    let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := ∞)
    letI := S₁.totalSpaceTopology
    letI := S₁.fiberBundle
    letI := S₂.totalSpaceTopology
    letI := S₂.fiberBundle
    ∀ (R : ℝ → ∀ x, S₂.fiber x) (J : Set ℝ) (t : ℝ)
      (hR : ContMDiff I (I.prod 𝓘(ℝ, Fin S₂.rank → ℝ)) ∞
        (fun x => TotalSpace.mk' (Fin S₂.rank → ℝ) x (R t x))) (x : M),
      let A : Cₛ^∞⟮I; Fin S₂.rank → ℝ, fun x => S₂.fiber x⟯ := ⟨R t, hR⟩
      let B := ContMDiffSection.selfAdjointConjugate φ hφ A
      HasDerivWithinAt (fun s => (φ x).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((R s x : V₂ x →L[ℝ] V₂ x).comp (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
        ((rawBundleConnLap g (D.selfAdjoint hD) B x : V₁ x →L[ℝ] V₁ x) +
          (curvatureOperatorReactionSelfAdjoint3 (B x) : V₁ x →L[ℝ] V₁ x)) J t ↔
      HasDerivWithinAt (fun s => (R s x : V₂ x →L[ℝ] V₂ x))
        ((rawBundleConnLap g (C.selfAdjoint hC) A x : V₂ x →L[ℝ] V₂ x) +
          (curvatureOperatorReactionSelfAdjoint3 (R t x) : V₂ x →L[ℝ] V₂ x)) J t := by
  let _ : ∀ x, FiniteDimensional ℝ (V₁ x) := fun x => VectorBundle.finiteDimensional ℝ F₁ V₁ x
  let _ : ∀ x, FiniteDimensional ℝ (V₂ x) := fun x => VectorBundle.finiteDimensional ℝ F₂ V₂ x
  let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := ∞)
  let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := ∞)
  let _ := S₁.totalSpaceTopology
  let _ := S₁.fiberBundle
  let _ := S₂.totalSpaceTopology
  let _ := S₂.fiberBundle
  dsimp only
  intro R J t hR x
  let A : Cₛ^∞⟮I; Fin S₂.rank → ℝ, fun x => S₂.fiber x⟯ := ⟨R t, hR⟩
  let B := ContMDiffSection.selfAdjointConjugate φ hφ A
  let e := (φ x).toContinuousLinearEquiv
  let L := e.symm.arrowCongr e.symm
  have hB : (B x : V₁ x →L[ℝ] V₁ x) = L (R t x : V₂ x →L[ℝ] V₂ x) := rfl
  have hLap : (rawBundleConnLap g (D.selfAdjoint hD) B x : V₁ x →L[ℝ] V₁ x) =
      L (rawBundleConnLap g (C.selfAdjoint hC) A x : V₂ x →L[ℝ] V₂ x) := by
    exact (ContinuousLinearEquiv.eq_toContinuousLinearMap_symm_comp _ _).mpr
      (map_rawBundleConnLap_selfAdjoint_conjugate φ hφ D hD C hC hparallel g A x)
  have hQ : (curvatureOperatorReactionSelfAdjoint3 (B x) : V₁ x →L[ℝ] V₁ x) =
      L (curvatureOperatorReactionSelfAdjoint3 (R t x) : V₂ x →L[ℝ] V₂ x) :=
    reaction_conjugate e (R t x) (B x) hB
  have hsum := (congrArg₂ (fun a b : V₁ x →L[ℝ] V₁ x => a + b) hLap hQ).trans
    (L.map_add _ _).symm
  constructor
  · intro hd
    have hmapped := hd.congr_deriv hsum
    have hback := L.symm.hasFDerivAt.comp_hasDerivWithinAt t hmapped
    exact (hback.congr_deriv (L.symm_apply_apply _)).congr
      (fun s _ => (L.symm_apply_apply _).symm) (L.symm_apply_apply _).symm
  · intro hd
    exact (L.hasFDerivAt.comp_hasDerivWithinAt t hd).congr_deriv hsum.symm

theorem selfAdjoint_reaction_heat_eqOn_conjugate_iff
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (D : CovariantDerivative I F₁ V₁) (hD : D.IsMetricCompatible)
    (C : CovariantDerivative I F₂ V₂) (hC : C.IsMetricCompatible)
    [ContMDiffCovariantDerivative D ∞] [ContMDiffCovariantDerivative C ∞]
    (hparallel : homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂ D C
      (fun x => (φ x).toContinuousLinearEquiv.toContinuousLinearMap) = 0)
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) :
    letI : ∀ x, FiniteDimensional ℝ (V₁ x) := fun x => VectorBundle.finiteDimensional ℝ F₁ V₁ x
    letI : ∀ x, FiniteDimensional ℝ (V₂ x) := fun x => VectorBundle.finiteDimensional ℝ F₂ V₂ x
    let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := ∞)
    let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := ∞)
    letI := S₁.totalSpaceTopology
    letI := S₁.fiberBundle
    letI := S₂.totalSpaceTopology
    letI := S₂.fiberBundle
    ∀ (Rhat : ℝ → ∀ x, S₁.fiber x) (R : ℝ → ∀ x, S₂.fiber x)
      (J : Set ℝ) (t : ℝ), t ∈ J →
      ContMDiff I (I.prod 𝓘(ℝ, Fin S₂.rank → ℝ)) ∞
        (fun x => TotalSpace.mk' (Fin S₂.rank → ℝ) x (R t x)) →
      (∀ s ∈ J, ∀ x, (Rhat s x : V₁ x →L[ℝ] V₁ x) =
        (φ x).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((R s x : V₂ x →L[ℝ] V₂ x).comp
            (φ x).toContinuousLinearEquiv.toContinuousLinearMap)) →
      ∀ x, HasDerivWithinAt (fun s => (Rhat s x : V₁ x →L[ℝ] V₁ x))
          ((rawBundleConnLap g (D.selfAdjoint hD) (Rhat t) x : V₁ x →L[ℝ] V₁ x) +
            (curvatureOperatorReactionSelfAdjoint3 (Rhat t x) : V₁ x →L[ℝ] V₁ x)) J t ↔
        HasDerivWithinAt (fun s => (R s x : V₂ x →L[ℝ] V₂ x))
          ((rawBundleConnLap g (C.selfAdjoint hC) (R t) x : V₂ x →L[ℝ] V₂ x) +
            (curvatureOperatorReactionSelfAdjoint3 (R t x) : V₂ x →L[ℝ] V₂ x)) J t := by
  let _ : ∀ x, FiniteDimensional ℝ (V₁ x) := fun x => VectorBundle.finiteDimensional ℝ F₁ V₁ x
  let _ : ∀ x, FiniteDimensional ℝ (V₂ x) := fun x => VectorBundle.finiteDimensional ℝ F₂ V₂ x
  let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := ∞)
  let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := ∞)
  let _ := S₁.totalSpaceTopology
  let _ := S₁.fiberBundle
  let _ := S₂.totalSpaceTopology
  let _ := S₂.fiberBundle
  dsimp only
  intro Rhat R J t ht hR hconj x
  let A : Cₛ^∞⟮I; Fin S₂.rank → ℝ, fun x => S₂.fiber x⟯ := ⟨R t, hR⟩
  let B := ContMDiffSection.selfAdjointConjugate φ hφ A
  have hB : (fun y => B y) = Rhat t := by
    funext y
    exact Subtype.ext (hconj t ht y).symm
  have hiff := selfAdjoint_reaction_heat_conjugate_iff φ hφ
    D hD C hC hparallel g R J t hR x
  have hderiv : (rawBundleConnLap g (D.selfAdjoint hD) B x : V₁ x →L[ℝ] V₁ x) +
        (curvatureOperatorReactionSelfAdjoint3 (B x) : V₁ x →L[ℝ] V₁ x) =
      (rawBundleConnLap g (D.selfAdjoint hD) (Rhat t) x : V₁ x →L[ℝ] V₁ x) +
        (curvatureOperatorReactionSelfAdjoint3 (Rhat t x) : V₁ x →L[ℝ] V₁ x) :=
    congrArg (fun f : ∀ y, S₁.fiber y =>
      (rawBundleConnLap g (D.selfAdjoint hD) f x : V₁ x →L[ℝ] V₁ x) +
        (curvatureOperatorReactionSelfAdjoint3 (f x) : V₁ x →L[ℝ] V₁ x)) hB
  constructor
  · intro h
    apply hiff.mp
    exact (h.congr (fun s hs => (hconj s hs x).symm) (hconj t ht x).symm).congr_deriv hderiv.symm
  · intro h
    exact ((hiff.mpr h).congr (fun s hs => hconj s hs x) (hconj t ht x)).congr_deriv hderiv


theorem hasDerivWithinAt_selfAdjoint_reaction_heat_conjugate_iff
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (D : CovariantDerivative I F₁ V₁) (hD : D.IsMetricCompatible)
    (C : CovariantDerivative I F₂ V₂) (hC : C.IsMetricCompatible)
    [ContMDiffCovariantDerivative D ∞] [ContMDiffCovariantDerivative C ∞]
    (hparallel : homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂ D C
      (fun x => (φ x).toContinuousLinearEquiv.toContinuousLinearMap) = 0)
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) :
    letI : ∀ x, FiniteDimensional ℝ (V₁ x) := fun x => VectorBundle.finiteDimensional ℝ F₁ V₁ x
    letI : ∀ x, FiniteDimensional ℝ (V₂ x) := fun x => VectorBundle.finiteDimensional ℝ F₂ V₂ x
    let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := ∞)
    let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := ∞)
    letI := S₁.totalSpaceTopology
    letI := S₁.fiberBundle
    letI := S₂.totalSpaceTopology
    letI := S₂.fiberBundle
    ∀ (Rhat : ℝ → ∀ x, S₁.fiber x) (R : ℝ → ∀ x, S₂.fiber x)
      (J : Set ℝ) (t : ℝ), t ∈ J →
      ContMDiff I (I.prod 𝓘(ℝ, Fin S₂.rank → ℝ)) ∞
        (fun x => TotalSpace.mk' (Fin S₂.rank → ℝ) x (R t x)) →
      (∀ s ∈ J, ∀ x, (Rhat s x : V₁ x →L[ℝ] V₁ x) =
        (φ x).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((R s x : V₂ x →L[ℝ] V₂ x).comp
            (φ x).toContinuousLinearEquiv.toContinuousLinearMap)) →
      ∀ x,
        let Q₁ : S₁.fiber x := curvatureOperatorReactionSelfAdjoint3 (Rhat t x)
        let Q₂ : S₂.fiber x := curvatureOperatorReactionSelfAdjoint3 (R t x)
        HasDerivWithinAt (fun s => Rhat s x)
          (rawBundleConnLap g (D.selfAdjoint hD) (Rhat t) x +
            Q₁) J t ↔
        HasDerivWithinAt (fun s => R s x)
          (rawBundleConnLap g (C.selfAdjoint hC) (R t) x +
            Q₂) J t := by
  let _ : ∀ x, FiniteDimensional ℝ (V₁ x) := fun x => VectorBundle.finiteDimensional ℝ F₁ V₁ x
  let _ : ∀ x, FiniteDimensional ℝ (V₂ x) := fun x => VectorBundle.finiteDimensional ℝ F₂ V₂ x
  let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := ∞)
  let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := ∞)
  let _ := S₁.totalSpaceTopology
  let _ := S₁.fiberBundle
  let _ := S₂.totalSpaceTopology
  let _ := S₂.fiberBundle
  dsimp only
  intro Rhat R J t ht hR hconj x
  let Q₁ : S₁.fiber x := curvatureOperatorReactionSelfAdjoint3 (Rhat t x)
  let Q₂ : S₂.fiber x := curvatureOperatorReactionSelfAdjoint3 (R t x)
  have hleft := (S₁.fiber x).subtypeL.hasDerivWithinAt_comp_iff_of_injective
    Subtype.val_injective (f := fun s => Rhat s x)
    (f' := rawBundleConnLap g (D.selfAdjoint hD) (Rhat t) x +
      Q₁) (s := J) (x := t)
  have hright := (S₂.fiber x).subtypeL.hasDerivWithinAt_comp_iff_of_injective
    Subtype.val_injective (f := fun s => R s x)
    (f' := rawBundleConnLap g (C.selfAdjoint hC) (R t) x +
      Q₂) (s := J) (x := t)
  exact hleft.symm.trans ((selfAdjoint_reaction_heat_eqOn_conjugate_iff
    φ hφ D hD C hC hparallel g Rhat R J t ht hR hconj x).trans hright)

end DifferentialGeometry.Analysis.Parabolic
