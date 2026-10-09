import DifferentialGeometry.Geometry.Connection.TensorNabla.ExteriorPower
import DifferentialGeometry.Geometry.Connection.SelfAdjointRestriction

noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff

namespace CovariantDerivative

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

theorem multilinear_apply_congr
    (D C : CovariantDerivative I F V) {x : M}
    (hDC : ∀ (σ : ∀ x, V x),
      MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x → D σ x = C σ x)
    (k : ℕ) {T : ∀ x, Bundle.continuousMultilinearMap ℝ k F V x}
    (hT : MDifferentiableAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ))
      (fun y => (⟨y, T y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F V))) x) (X : TangentSpace I x) :
    D.multilinear k T x X = C.multilinear k T x X := by
  classical
  ext v
  choose Y hY using fun i =>
    ContMDiffSection.exists_eq_at (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞)) x (v i)
  have hv : v = fun i => Y i x := funext fun i => (hY i).symm
  rw [hv, multilinear_apply D k (fun i => Y i) hT (fun i => (Y i).mdifferentiableAt),
    multilinear_apply C k (fun i => Y i) hT (fun i => (Y i).mdifferentiableAt)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hDC (Y i) (Y i).mdifferentiableAt]

theorem alternating_apply_congr
    (D C : CovariantDerivative I F V) {x : M}
    (hDC : ∀ (σ : ∀ x, V x),
      MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x → D σ x = C σ x)
    (k : ℕ) {T : ∀ x, V x [⋀^Fin k]→L[ℝ] ℝ}
    (hT : MDifferentiableAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, T y⟩ : TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) x)
    (X : TangentSpace I x) :
    D.alternating k T x X = C.alternating k T x X := by
  rw [alternating_apply, alternating_apply,
    multilinear_apply_congr D C hDC k hT.alternating_bundle_toMultilinear X]

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

private instance alternatingFiniteDimensional (k : ℕ) :
    FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
    (Module.finBasis ℝ F)).finiteDimensional_of_finite

theorem exteriorPower_apply_congr
    (D C : CovariantDerivative I F V) {x : M}
    (hDC : ∀ (σ : ∀ x, V x),
      MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x → D σ x = C σ x)
    (k : ℕ) (u : ∀ x, ⋀[ℝ]^k (V x)) (X : TangentSpace I x) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    MDifferentiableAt I (I.prod 𝓘(ℝ, ⋀[ℝ]^k F))
      (fun y => (⟨y, u y⟩ : TotalSpace (⋀[ℝ]^k F) (fun z => ⋀[ℝ]^k (V z)))) x →
      D.exteriorPower k u x X = C.exteriorPower k u x X := by
  let : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  intro hu
  apply (_root_.exteriorPower.alternatingDualEquiv k).injective
  apply ContinuousLinearMap.ext
  intro a
  obtain ⟨A, hA⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := F [⋀^Fin k]→L[ℝ] ℝ)
    (V := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
    (n := (⊤ : ℕ∞)) x a
  rw [← hA, exteriorPower_alternatingDualEquiv_apply D k u A x X A.mdifferentiableAt hu,
    exteriorPower_alternatingDualEquiv_apply C k u A x X A.mdifferentiableAt hu,
    alternating_apply_congr D C hDC k A.mdifferentiableAt X]

end InnerProduct

end CovariantDerivative

namespace DifferentialGeometry.HomConnectionGen

open CovariantDerivative

section Hom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]

theorem homBundleCovariantDerivativeGen_apply_congr
    (D₁ C₁ : CovariantDerivative I F₁ V₁)
    (D₂ C₂ : CovariantDerivative I F₂ V₂) {x : M}
    (hDC₁ : ∀ (σ : ∀ x, V₁ x),
      MDifferentiableAt I (I.prod 𝓘(ℝ, F₁)) (T% σ) x → D₁ σ x = C₁ σ x)
    (hDC₂ : ∀ (σ : ∀ x, V₂ x),
      MDifferentiableAt I (I.prod 𝓘(ℝ, F₂)) (T% σ) x → D₂ σ x = C₂ σ x)
    {A : ∀ x, V₁ x →L[ℝ] V₂ x}
    (hA : MDifferentiableAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂))
      (fun y => (⟨y, A y⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun y => V₁ y →L[ℝ] V₂ y))) x) (X : TangentSpace I x) :
    DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂
      D₁ D₂ A x X =
    DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂
      C₁ C₂ A x X := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := F₁) (V := V₁)
    (n := (⊤ : ℕ∞)) x v
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x X
  rw [← hY, ← hZ,
    DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
      I M F₁ V₁ F₂ V₂ D₁ D₂ A hA Z.mdifferentiableAt Y.mdifferentiableAt,
    DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
      I M F₁ V₁ F₂ V₂ C₁ C₂ A hA Z.mdifferentiableAt Y.mdifferentiableAt,
    hDC₁ Y Y.mdifferentiableAt,
    hDC₂ (fun y => A y (Y y)) (hA.clm_bundle_apply Y.mdifferentiableAt)]

end Hom

end DifferentialGeometry.HomConnectionGen

namespace CovariantDerivative

section SelfAdjoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem selfAdjoint_apply_congr
    (D C : CovariantDerivative I F V) (hD : D.IsMetricCompatible) (hC : C.IsMetricCompatible)
    {x : M} (hDC : ∀ (σ : ∀ x, V x),
      MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x → D σ x = C σ x) :
    let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (A : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯)
      (X : TangentSpace I x),
      D.selfAdjoint hD A x X = C.selfAdjoint hC A x X := by
  let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  dsimp only
  intro A X
  apply Subtype.ext
  rw [selfAdjoint_subtypeVal D hD, selfAdjoint_subtypeVal C hC]
  apply DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply_congr D C D C hDC hDC
  exact (((S.contMDiff_section_iff A).mp A.contMDiff) x).mdifferentiableAt (by simp)

end SelfAdjoint

end CovariantDerivative
