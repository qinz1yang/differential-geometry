import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import DifferentialGeometry.Bundle.Equiv
import DifferentialGeometry.Bundle.Frame
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorExtension
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff


namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

noncomputable local instance modelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance modelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance modelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance modelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance modelTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance modelTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance modelQuadrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance modelQuadrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tangentDualNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tangentDualNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tangentBilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tangentBilinearNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tangentTrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tangentTrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance tangentTrilinearAddCommGroup (x : M) :
    AddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (tangentTrilinearNormedAddCommGroup x).toAddCommGroup

local instance tangentTrilinearModule (x : M) :
    Module ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    tangentTrilinearNormedAddCommGroup x
  letI : NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    tangentTrilinearNormedSpace x
  exact NormedSpace.toModule

local instance tangentTrilinearSMul (x : M) :
    SMul ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (tangentTrilinearModule x).toDistribMulAction.toMulAction.toSemigroupAction.toSMul

local instance tangentTrilinearTopology (x : M) :
    TopologicalSpace
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    tangentTrilinearNormedAddCommGroup x
  infer_instance

noncomputable local instance tangentQuadrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tangentQuadrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

section mkHom₃

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
variable {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [FiniteDimensional ℝ F₃]
variable {V₁ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle 1 F₁ V₁ I]
variable {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle 1 F₂ V₂ I]
variable {V₃ : M → Type*} [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)]
  [∀ x, TopologicalSpace (V₃ x)] [TopologicalSpace (TotalSpace F₃ V₃)]
  [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃] [ContMDiffVectorBundle 1 F₃ V₃ I]

private noncomputable def mkHom₃FirstSlot
    (Φ : (Π x : M, V₁ x) → (Π x : M, V₂ x) → (Π x : M, V₃ x) → ℝ) (x : M)
    (hΦ₁ : ∀ σ₂ σ₃, MDiffAt (T% σ₂) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₁ (Φ · σ₂ σ₃) x)
    (hΦ₂ : ∀ σ₁ σ₃, MDiffAt (T% σ₁) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₂ (Φ σ₁ · σ₃) x)
    (hΦ₃ : ∀ σ₁ σ₂, MDiffAt (T% σ₁) x → MDiffAt (T% σ₂) x →
      TensorialAt I F₃ (Φ σ₁ σ₂) x) :
    V₁ x →ₗ[ℝ] (V₂ x →L[ℝ] V₃ x →L[ℝ] ℝ) where
  toFun v :=
    TensorialAt.mkHom₂ (Φ (FiberBundle.extend F₁ v)) x
      (fun σ₃ hσ₃ => hΦ₂ (FiberBundle.extend F₁ v) σ₃ (mdifferentiableAt_extend ..) hσ₃)
      (fun σ₂ hσ₂ => hΦ₃ (FiberBundle.extend F₁ v) σ₂ (mdifferentiableAt_extend ..) hσ₂)
  map_add' v v' := by
    classical
    ext y z
    set σ₂ : Π x : M, V₂ x := FiberBundle.extend F₂ y
    set σ₃ : Π x : M, V₃ x := FiberBundle.extend F₃ z
    have hσ₂ : MDiffAt (T% σ₂) x := mdifferentiableAt_extend ..
    have hσ₃ : MDiffAt (T% σ₃) x := mdifferentiableAt_extend ..
    have hσ₂x : σ₂ x = y := FiberBundle.extend_apply_self F₂ y
    have hσ₃x : σ₃ x = z := FiberBundle.extend_apply_self F₃ z
    rw [show y = σ₂ x from hσ₂x.symm, show z = σ₃ x from hσ₃x.symm]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    simp only [TensorialAt.mkHom₂_apply _ _ hσ₂ hσ₃]
    have h1 : (FiberBundle.extend F₁ (v + v') : Π x : M, V₁ x) x = v + v' :=
      FiberBundle.extend_apply_self F₁ (v + v')
    have h2 : (FiberBundle.extend F₁ v : Π x : M, V₁ x) x = v :=
      FiberBundle.extend_apply_self F₁ v
    have h3 : (FiberBundle.extend F₁ v' : Π x : M, V₁ x) x = v' :=
      FiberBundle.extend_apply_self F₁ v'
    set τ : Π x : M, V₁ x :=
      (FiberBundle.extend F₁ v : Π x : M, V₁ x) + FiberBundle.extend F₁ v' with hτ_def
    have hτ : MDiffAt (T% τ) x :=
      mdifferentiableAt_add_section (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
    have hτx : τ x = v + v' := by
      change (FiberBundle.extend F₁ v : Π x : M, V₁ x) x
        + (FiberBundle.extend F₁ v' : Π x : M, V₁ x) x = v + v'
      rw [h2, h3]
    have hpt := (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).pointwise
      (mdifferentiableAt_extend ..) hτ (by rw [h1, hτx])
    rw [hpt]
    rw [hτ_def, (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).add (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]
  map_smul' c v := by
    classical
    ext y z
    set σ₂ : Π x : M, V₂ x := FiberBundle.extend F₂ y
    set σ₃ : Π x : M, V₃ x := FiberBundle.extend F₃ z
    have hσ₂ : MDiffAt (T% σ₂) x := mdifferentiableAt_extend ..
    have hσ₃ : MDiffAt (T% σ₃) x := mdifferentiableAt_extend ..
    have hσ₂x : σ₂ x = y := FiberBundle.extend_apply_self F₂ y
    have hσ₃x : σ₃ x = z := FiberBundle.extend_apply_self F₃ z
    rw [show y = σ₂ x from hσ₂x.symm, show z = σ₃ x from hσ₃x.symm]
    rw [RingHom.id_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    simp only [TensorialAt.mkHom₂_apply _ _ hσ₂ hσ₃]
    have h1 : (FiberBundle.extend F₁ (c • v) : Π x : M, V₁ x) x = c • v :=
      FiberBundle.extend_apply_self F₁ (c • v)
    have h2 : (FiberBundle.extend F₁ v : Π x : M, V₁ x) x = v :=
      FiberBundle.extend_apply_self F₁ v
    set τ : Π x : M, V₁ x := (fun _ : M => c) • (FiberBundle.extend F₁ v : Π x : M, V₁ x)
      with hτ_def
    have hτ : MDiffAt (T% τ) x :=
      (mdifferentiableAt_const (c := c)).smul_section (mdifferentiableAt_extend ..)
    have hτx : τ x = c • v := by
      change c • (FiberBundle.extend F₁ v : Π x : M, V₁ x) x = c • v
      rw [h2]
    have hpt := (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).pointwise
      (mdifferentiableAt_extend ..) hτ (by rw [h1, hτx])
    rw [hpt]
    rw [hτ_def, (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).smul (f := fun _ => c) (mdifferentiable_const ..)
        (mdifferentiableAt_extend ..)]

noncomputable def mkHom₃
    (Φ : (Π x : M, V₁ x) → (Π x : M, V₂ x) → (Π x : M, V₃ x) → ℝ) (x : M)
    (hΦ₁ : ∀ σ₂ σ₃, MDiffAt (T% σ₂) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₁ (Φ · σ₂ σ₃) x)
    (hΦ₂ : ∀ σ₁ σ₃, MDiffAt (T% σ₁) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₂ (Φ σ₁ · σ₃) x)
    (hΦ₃ : ∀ σ₁ σ₂, MDiffAt (T% σ₁) x → MDiffAt (T% σ₂) x →
      TensorialAt I F₃ (Φ σ₁ σ₂) x) :
    V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x →L[ℝ] ℝ :=
  have : T2Space (V₁ x) := FiberBundle.t2Space F₁ V₁ x
  have : FiniteDimensional ℝ (V₁ x) := VectorBundle.finiteDimensional ℝ F₁ V₁ x
  have : IsTopologicalAddGroup (V₁ x) :=
    (VectorBundle.continuousLinearEquivAt ℝ F₁ V₁ x).toContinuousAddEquiv.isTopologicalAddGroup
  have : ContinuousSMul ℝ (V₁ x) :=
    (VectorBundle.continuousLinearEquivAt ℝ F₁ V₁ x).continuousSMul
  LinearMap.toContinuousLinearMap (mkHom₃FirstSlot Φ x hΦ₁ hΦ₂ hΦ₃)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mkHom₃_apply
    {Φ : (Π x : M, V₁ x) → (Π x : M, V₂ x) → (Π x : M, V₃ x) → ℝ} {x : M}
    (hΦ₁ : ∀ σ₂ σ₃, MDiffAt (T% σ₂) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₁ (Φ · σ₂ σ₃) x)
    (hΦ₂ : ∀ σ₁ σ₃, MDiffAt (T% σ₁) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₂ (Φ σ₁ · σ₃) x)
    (hΦ₃ : ∀ σ₁ σ₂, MDiffAt (T% σ₁) x → MDiffAt (T% σ₂) x →
      TensorialAt I F₃ (Φ σ₁ σ₂) x)
    {σ₁ : Π x : M, V₁ x} {σ₂ : Π x : M, V₂ x} {σ₃ : Π x : M, V₃ x}
    (hσ₁ : MDiffAt (T% σ₁) x) (hσ₂ : MDiffAt (T% σ₂) x) (hσ₃ : MDiffAt (T% σ₃) x) :
    mkHom₃ Φ x hΦ₁ hΦ₂ hΦ₃ (σ₁ x) (σ₂ x) (σ₃ x) = Φ σ₁ σ₂ σ₃ := by
  classical
  have hcoe : (mkHom₃ Φ x hΦ₁ hΦ₂ hΦ₃) (σ₁ x) =
      mkHom₃FirstSlot Φ x hΦ₁ hΦ₂ hΦ₃ (σ₁ x) := rfl
  rw [hcoe]
  have hstep : (mkHom₃FirstSlot Φ x hΦ₁ hΦ₂ hΦ₃ (σ₁ x)) (σ₂ x) (σ₃ x) =
      Φ (FiberBundle.extend F₁ (σ₁ x)) σ₂ σ₃ := by
    change (TensorialAt.mkHom₂ (Φ (FiberBundle.extend F₁ (σ₁ x))) x
      (fun σ₃ hσ₃ => hΦ₂ (FiberBundle.extend F₁ (σ₁ x)) σ₃ (mdifferentiableAt_extend ..) hσ₃)
      (fun σ₂ hσ₂ => hΦ₃ (FiberBundle.extend F₁ (σ₁ x)) σ₂ (mdifferentiableAt_extend ..) hσ₂))
      (σ₂ x) (σ₃ x) = _
    exact TensorialAt.mkHom₂_apply _ _ hσ₂ hσ₃
  rw [hstep]
  exact (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).pointwise (mdifferentiableAt_extend ..) hσ₁ (by simp)

end mkHom₃

local instance tensor01TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

local instance tensor01FiberBundle :
    FiberBundle (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

local instance tensor01VectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

local instance tensor01ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance tensor02TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

local instance iteratedTensor02FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

local instance iteratedTensor02VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

local instance iteratedTensor02ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance tensor03TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

local instance tensor03FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

local instance tensor03VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

local instance tensor03ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

def MDiffAtTensor03
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ))
    (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (T b)) x

def tensor03Scalar
    (cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M)
    (X Y Z W : Π x : M, TangentSpace I x) : ℝ :=
  extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
    - T x (cov Y x (X x)) (Z x) (W x)
    - T x (Y x) (cov Z x (X x)) (W x)
    - T x (Y x) (Z x) (cov W x (X x))

omit [FiniteDimensional ℝ E] in
lemma mdifferentiableAt_tensor03_apply_one
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hT : MDiffAtTensor03 T x) (hY : MDiffAt (T% Y) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (T b (Y b))) x :=
  MDifferentiableAt.clm_bundle_apply
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (b := fun b : M => b)
    (ϕ := fun b => T b) (v := fun b => Y b) hT hY

omit [FiniteDimensional ℝ E] in
lemma mdifferentiableAt_tensor03_apply_two
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hT : MDiffAtTensor03 T x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (T b (Y b) (Z b))) x :=
  MDifferentiableAt.clm_bundle_apply
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (b := fun b : M => b)
    (ϕ := fun b => T b (Y b)) (v := fun b => Z b)
    (mdifferentiableAt_tensor03_apply_one hT hY) hZ

omit [FiniteDimensional ℝ E] in
lemma mdifferentiableAt_tensor03_pairing
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hT : MDiffAtTensor03 T x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hW : MDiffAt (T% W) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W b)) x := by
  have h2 : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun m => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) m (T m (Y m) (Z m) (W m))) x :=
    MDifferentiableAt.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => ℝ)
      (b := fun b : M => b)
      (ϕ := fun b => T b (Y b) (Z b)) (v := fun b => W b)
      (mdifferentiableAt_tensor03_apply_two hT hY hZ) hW
  rw [mdifferentiableAt_totalSpace] at h2
  exact h2.2

end Connection
end Geometry
end DifferentialGeometry

end

