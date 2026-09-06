import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Bundle.ClmSectionSmooth
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul 𝕜 (V₁ x)] [FiberBundle F₁ V₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [FiniteDimensional 𝕜 F₂]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul 𝕜 (V₂ x)] [∀ x, T2Space (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]

private def mapSection (φ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (σ : ∀ x, V₁ x) : ∀ x, V₂ x :=
  fun x => φ x (σ x)

def pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) 1
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂)))
    (cov : CovariantDerivative I F₂ V₂) :
    CovariantDerivative I F₁ V₁ where
  toFun σ x :=
    letI : FiniteDimensional 𝕜 (V₂ x) :=
      VectorBundle.finiteDimensional 𝕜 F₂ V₂ x
    (LinearMap.toContinuousLinearMap (φ x).symm.toLinearMap).comp
      (cov (mapSection φ σ) x)
  isCovariantDerivativeOnUniv := by
    constructor
    · intro σ σ' x hσ hσ' hx
      have hmap : MDiffAt (T% (mapSection φ σ)) x := by
        exact hφ.mdifferentiableAt (by norm_num) |>.comp x hσ
      have hmap' : MDiffAt (T% (mapSection φ σ')) x := by
        exact hφ.mdifferentiableAt (by norm_num) |>.comp x hσ'
      ext X
      rw [show mapSection φ (σ + σ') = mapSection φ σ + mapSection φ σ' by
        ext y
        simp [mapSection]]
      rw [cov.isCovariantDerivativeOnUniv.add hmap hmap']
      simp [LinearMap.coe_toContinuousLinearMap']
    · intro σ g x hσ hg hx
      have hmap : MDiffAt (T% (mapSection φ σ)) x := by
        exact hφ.mdifferentiableAt (by norm_num) |>.comp x hσ
      ext X
      rw [show mapSection φ (g • σ) = g • mapSection φ σ by
        ext y
        simp [mapSection]]
      rw [cov.isCovariantDerivativeOnUniv.leibniz hmap hg]
      simp only [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
        LinearEquiv.coe_coe, map_add, map_smul, add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [show mapSection φ σ x = φ x (σ x) from rfl,
        LinearEquiv.symm_apply_apply]

@[simp]
theorem pullbackFiberwiseLinearEquiv_apply
    (φ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) 1
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂)))
    (cov : CovariantDerivative I F₂ V₂) (σ : ∀ x, V₁ x) (x : M)
    (X : TangentSpace I x) :
    pullbackFiberwiseLinearEquiv φ hφ cov σ x X =
      (φ x).symm (cov (fun y => φ y (σ y)) x X) := by
  simp only [pullbackFiberwiseLinearEquiv, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
  have hmap : (fun y => φ y (σ y)) = mapSection φ σ := by
    funext y
    rfl
  rw [hmap]

theorem map_pullbackFiberwiseLinearEquiv_apply
    (φ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) 1
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂)))
    (cov : CovariantDerivative I F₂ V₂) (σ : ∀ x, V₁ x) (x : M)
    (X : TangentSpace I x) :
    φ x (pullbackFiberwiseLinearEquiv φ hφ cov σ x X) =
      cov (fun y => φ y (σ y)) x X := by
  simp

theorem pullbackFiberwiseLinearEquiv_eq_zero_iff
    {φ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x}
    (hφ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) 1
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂)))
    {cov : CovariantDerivative I F₂ V₂} {σ : ∀ x, V₁ x} :
    pullbackFiberwiseLinearEquiv φ hφ cov σ = 0 ↔
      cov (fun x => φ x (σ x)) = 0 := by
  constructor
  · intro h
    funext x
    ext X
    rw [← map_pullbackFiberwiseLinearEquiv_apply φ hφ cov σ x X, h]
    simp
  · intro h
    funext x
    ext X
    rw [pullbackFiberwiseLinearEquiv_apply φ hφ cov σ x X, h]
    simp

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

local instance tangentFiberBundle :
    FiberBundle E (TangentSpace I : M → Type _) :=
  TangentSpace.fiberBundle (I := I) (M := M)

local instance tangentVectorBundle :
    VectorBundle ℝ E (TangentSpace I : M → Type _) :=
  TangentSpace.vectorBundle (I := I) (M := M)

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [FiniteDimensional ℝ F₁]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [FiniteDimensional ℝ F₂]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [∀ x, T2Space (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]

local instance covHomV₁Topology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] F₁) (fun x : M => TangentSpace I x →L[ℝ] V₁ x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) F₁ V₁

local instance covHomV₁FiberBundle :
    FiberBundle (E →L[ℝ] F₁) (fun x : M => TangentSpace I x →L[ℝ] V₁ x) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) F₁ V₁

local instance covHomV₁VectorBundle :
    VectorBundle ℝ (E →L[ℝ] F₁) (fun x : M => TangentSpace I x →L[ℝ] V₁ x) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) F₁ V₁

local instance covHomV₂Topology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] F₂) (fun x : M => TangentSpace I x →L[ℝ] V₂ x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) F₂ V₂

local instance covHomV₂FiberBundle :
    FiberBundle (E →L[ℝ] F₂) (fun x : M => TangentSpace I x →L[ℝ] V₂ x) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) F₂ V₂

local instance covHomV₂VectorBundle :
    VectorBundle ℝ (E →L[ℝ] F₂) (fun x : M => TangentSpace I x →L[ℝ] V₂ x) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) F₂ V₂

omit [FiniteDimensional ℝ F₁] in
theorem ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃ₗ[ℝ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) ∞
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂)))
    (hφinv : ContMDiff (I.prod 𝓘(ℝ, F₂)) (I.prod 𝓘(ℝ, F₁)) ∞
      (fun p : TotalSpace F₂ V₂ =>
        (⟨p.1, (φ p.1).symm p.2⟩ : TotalSpace F₁ V₁)))
    (cov : CovariantDerivative I F₂ V₂)
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative
      (pullbackFiberwiseLinearEquiv φ (hφ.of_le (by norm_num)) cov) ∞ where
  contMDiff := by
    constructor
    intro σ hσ
    have hσglobal : ContMDiff I (I.prod 𝓘(ℝ, F₁)) ∞ (T% σ) := by
      rw [← contMDiffOn_univ]
      simpa using hσ
    have hmap : ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
        (T% (mapSection φ σ)) := by
      exact (hφ.comp hσglobal).congr fun x => rfl
    have hcovOn :=
      (inferInstance : ContMDiffCovariantDerivative cov ∞).contMDiff.contMDiff
        hmap.contMDiffOn
    have hcov := contMDiffOn_univ.mp hcovOn
    apply ContMDiff.contMDiffOn
    apply DifferentialGeometry.cotangentCov_clmSection_smooth_aux
    intro Y
    have heval : ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
        (T% (fun x => cov (mapSection φ σ) x (Y x))) :=
      ContMDiff.clm_bundle_apply (b := id) hcov Y.contMDiff
    exact (hφinv.comp heval).congr fun x => by
      simp only [pullbackFiberwiseLinearEquiv_apply]
      have hmapEq : (fun y => φ y (σ y)) = mapSection φ σ := by
        funext y
        rfl
      rw [hmapEq]
      rfl

end CovariantDerivative
