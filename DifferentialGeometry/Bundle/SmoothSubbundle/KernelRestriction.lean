import DifferentialGeometry.Bundle.SmoothSubbundle.Kernel
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {n : WithTop ℕ∞}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
variable [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
variable [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
variable [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
variable [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I]

omit [CompleteSpace 𝕜] in
 theorem contMDiffOn_restrictOpen_section
    (U : TopologicalSpace.Opens M) (w : (x : M) → V x)
    {W : Set M} (hw : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F x (w x)) W) :
    let c : C^n⟮I, U; I, M⟯ := ⟨Subtype.val, contMDiff_subtype_val⟩
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
      (fun x : U => TotalSpace.mk' F x (w x) : U → TotalSpace F (c *ᵖ V))
      (Subtype.val ⁻¹' W) := by
  let c : C^n⟮I, U; I, M⟯ := ⟨Subtype.val, contMDiff_subtype_val⟩
  change ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
    (fun x : U => TotalSpace.mk' F x (w x) : U → TotalSpace F (c *ᵖ V))
      (Subtype.val ⁻¹' W)
  intro x hx
  let e₀ := trivializationAt F V (x : M)
  let e := e₀.pullback c
  let _ : MemTrivializationAtlas e := ⟨⟨e₀, inferInstance, rfl⟩⟩
  have hx₀ : (x : M) ∈ e₀.baseSet := mem_baseSet_trivializationAt F V (x : M)
  have hxe : x ∈ e.baseSet := hx₀
  apply (e.contMDiffWithinAt_section _ hxe).mpr
  have hcoord : ContMDiffWithinAt I 𝓘(𝕜, F) n
      (fun y : M => (e₀ (TotalSpace.mk' F y (w y))).2) W (x : M) :=
    (e₀.contMDiffWithinAt_section W hx₀).mp (hw (x : M) hx)
  exact hcoord.comp x (c.contMDiff x).contMDiffWithinAt (fun y hy => hy)

namespace ContMDiffVectorSubbundle

variable [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
variable [VectorBundle 𝕜 F₁ V₁] [ContMDiffVectorBundle n F₁ V₁ I]
variable [VectorBundle 𝕜 F₂ V₂] [ContMDiffVectorBundle n F₂ V₂ I]
variable [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]

theorem exists_smooth_kernel_on_open
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (W : TopologicalSpace.Opens M)
    (hA : ContMDiffOn I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)) W)
    (k : ℕ) (hker : ∀ x ∈ W, Module.finrank 𝕜 (A x).ker = k) :
    let c : C^n⟮I, W; I, M⟯ := ⟨Subtype.val, contMDiff_subtype_val⟩
    let V' := fun x : W => V₁ (x : M)
    let _ : ∀ x : W, AddCommGroup (V' x) := fun x => by
      change AddCommGroup (V₁ (x : M)); infer_instance
    let _ : ∀ x : W, Module 𝕜 (V' x) := fun x => by
      change Module 𝕜 (V₁ (x : M)); infer_instance
    let _ : TopologicalSpace (TotalSpace F₁ V') := by
      change TopologicalSpace (TotalSpace F₁ (c *ᵖ V₁)); infer_instance
    let _ : FiberBundle F₁ V' := by
      change FiberBundle F₁ (c *ᵖ V₁); infer_instance
    let _ : VectorBundle 𝕜 F₁ V' := by
      change VectorBundle 𝕜 F₁ (c *ᵖ V₁); infer_instance
    let _ : ContMDiffVectorBundle n F₁ V' I := by
      change ContMDiffVectorBundle n F₁ (c *ᵖ V₁) I; infer_instance
    ∃ S : ContMDiffVectorSubbundle (I := I) (F := F₁) (V := V') (n := n),
      S.rank = k ∧ ∀ x : W, S.fiber x = (A x).ker := by
  let c : C^n⟮I, W; I, M⟯ := ⟨Subtype.val, contMDiff_subtype_val⟩
  let V' := fun x : W => V₁ (x : M)
  let _ : ∀ x : W, AddCommGroup (V' x) := fun x => by
    change AddCommGroup (V₁ (x : M)); infer_instance
  let _ : ∀ x : W, Module 𝕜 (V' x) := fun x => by
    change Module 𝕜 (V₁ (x : M)); infer_instance
  let _ : TopologicalSpace (TotalSpace F₁ V') := by
    change TopologicalSpace (TotalSpace F₁ (c *ᵖ V₁)); infer_instance
  let _ : FiberBundle F₁ V' := by
    change FiberBundle F₁ (c *ᵖ V₁); infer_instance
  let _ : VectorBundle 𝕜 F₁ V' := by
    change VectorBundle 𝕜 F₁ (c *ᵖ V₁); infer_instance
  let _ : ContMDiffVectorBundle n F₁ V' I := by
    change ContMDiffVectorBundle n F₁ (c *ᵖ V₁) I; infer_instance
  refine ⟨⟨(fun x : W => (A x).ker), k, ?_⟩, rfl, (fun _ => rfl)⟩
  intro x₀
  obtain ⟨U, s, hU, hxU, hUW, hs⟩ :=
    exists_kernel_frameOn A W W.isOpen hA k hker x₀ x₀.2
  refine ⟨Subtype.val ⁻¹' U, (fun i x => s i x),
    hU.preimage continuous_subtype_val, hxU, ?_, ?_, ?_⟩
  · intro x hx
    exact hs.linearIndependent hx
  · intro x hx
    exact hs.spans hx
  · intro i x hx
    let e₀ := trivializationAt F₁ V₁ (x : M)
    let e := e₀.pullback c
    let _ : MemTrivializationAtlas e := ⟨⟨e₀, inferInstance, rfl⟩⟩
    have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt F₁ V₁ (x : M)
    apply (e.contMDiffWithinAt_section _ hxe).mpr
    have hscoord := (e₀.contMDiffWithinAt_section U
      (mem_baseSet_trivializationAt F₁ V₁ (x : M))).mp (hs.contMDiffOn i (x : M) hx)
    have hval : ContMDiffWithinAt I I n (Subtype.val : W → M)
        (Subtype.val ⁻¹' U) x :=
      (contMDiff_subtype_val (I := I) (U := W)).contMDiffAt.contMDiffWithinAt
    exact hscoord.comp x hval (fun y hy => hy)

end ContMDiffVectorSubbundle
