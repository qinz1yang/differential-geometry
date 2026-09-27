import DifferentialGeometry.Bundle.ContinuousLinearMapSection.Spacetime
import DifferentialGeometry.Bundle.SmoothSubbundle.KernelRestriction
import Mathlib.Analysis.InnerProductSpace.Symmetric

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace ContMDiffVectorSubbundle

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

theorem exists_smooth_spacetime_kernel_on_open
    (A : ℝ → (x : M) → V x →L[ℝ] V x)
    {J : Set ℝ} (hJopen : IsOpen J)
    (hAspace : ContMDiffOnSpacetimeEndomorphism (I := I) (F := F) (V := V) (n := ∞)
      (fun t x ↦ A t x) (J ×ˢ (Set.univ : Set M)))
    (q : ℕ) (hrange : ∀ t ∈ J, ∀ x, Module.finrank ℝ (A t x).range = q) :
    let B := ℝ × M
    let I' := 𝓘(ℝ, ℝ).prod I
    let V0 : B → Type _ := fun p => V p.2
    let c0 : C^∞⟮I', B; I, M⟯ := ContMDiffMap.snd
    let _ : ∀ p : B, AddCommGroup (V0 p) := fun p => by
      change AddCommGroup (V p.2); infer_instance
    let _ : ∀ p : B, Module ℝ (V0 p) := fun p => by
      change Module ℝ (V p.2); infer_instance
    let _ : ∀ p : B, TopologicalSpace (V0 p) := fun p => by
      change TopologicalSpace (V p.2); infer_instance
    let _ : TopologicalSpace (TotalSpace F V0) := by
      change TopologicalSpace (TotalSpace F (c0 *ᵖ V)); infer_instance
    let _ : FiberBundle F V0 := by
      change FiberBundle F (c0 *ᵖ V); infer_instance
    let _ : VectorBundle ℝ F V0 := by
      change VectorBundle ℝ F (c0 *ᵖ V); infer_instance
    let _ : ContMDiffVectorBundle ∞ F V0 I' := by
      change ContMDiffVectorBundle ∞ F (c0 *ᵖ V) I'; infer_instance
    let W : TopologicalSpace.Opens B := ⟨J ×ˢ (Set.univ : Set M), hJopen.prod isOpen_univ⟩
    let c : C^∞⟮I', W; I', B⟯ := ⟨Subtype.val, contMDiff_subtype_val⟩
    let V' := fun p : W => V0 (p : B)
    let _ : ∀ p : W, AddCommGroup (V' p) := fun p => by
      change AddCommGroup (V0 (p : B)); infer_instance
    let _ : ∀ p : W, Module ℝ (V' p) := fun p => by
      change Module ℝ (V0 (p : B)); infer_instance
    let _ : TopologicalSpace (TotalSpace F V') := by
      change TopologicalSpace (TotalSpace F (c *ᵖ V0)); infer_instance
    let _ : FiberBundle F V' := by
      change FiberBundle F (c *ᵖ V0); infer_instance
    let _ : VectorBundle ℝ F V' := by
      change VectorBundle ℝ F (c *ᵖ V0); infer_instance
    let _ : ContMDiffVectorBundle ∞ F V' I' := by
      change ContMDiffVectorBundle ∞ F (c *ᵖ V0) I'; infer_instance
    ∃ K : ContMDiffVectorSubbundle (I := I') (F := F) (V := V') (n := ∞),
      K.rank = Module.finrank ℝ F - q ∧
        ∀ p : W, K.fiber p = (A (p : B).1 (p : B).2).ker := by
  let B := ℝ × M
  let I' := 𝓘(ℝ, ℝ).prod I
  let V0 : B → Type _ := fun p => V p.2
  let c0 : C^∞⟮I', B; I, M⟯ := ContMDiffMap.snd
  let _ : ∀ p : B, AddCommGroup (V0 p) := fun p => by
    change AddCommGroup (V p.2); infer_instance
  let _ : ∀ p : B, Module ℝ (V0 p) := fun p => by
    change Module ℝ (V p.2); infer_instance
  let _ : ∀ p : B, TopologicalSpace (V0 p) := fun p => by
    change TopologicalSpace (V p.2); infer_instance
  let _ : TopologicalSpace (TotalSpace F V0) := by
    change TopologicalSpace (TotalSpace F (c0 *ᵖ V)); infer_instance
  let _ : FiberBundle F V0 := by
    change FiberBundle F (c0 *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F V0 := by
    change VectorBundle ℝ F (c0 *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle ∞ F V0 I' := by
    change ContMDiffVectorBundle ∞ F (c0 *ᵖ V) I'; infer_instance
  let _ : ∀ p : B, IsTopologicalAddGroup (V0 p) := fun p => by
    change IsTopologicalAddGroup (V p.2); infer_instance
  let _ : ∀ p : B, ContinuousSMul ℝ (V0 p) := fun p => by
    change ContinuousSMul ℝ (V p.2); infer_instance
  let _ : TopologicalSpace (TotalSpace (F →L[ℝ] F)
      (fun p : B => V0 p →L[ℝ] V0 p)) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) F V0 F V0
  let _ : FiberBundle (F →L[ℝ] F)
      (fun p : B => V0 p →L[ℝ] V0 p) :=
    Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ) F V0 F V0
  let _ : VectorBundle ℝ (F →L[ℝ] F)
      (fun p : B => V0 p →L[ℝ] V0 p) :=
    Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ) F V0 F V0
  let _ : ContMDiffVectorBundle ∞ (F →L[ℝ] F)
      (fun p : B => V0 p →L[ℝ] V0 p) I' := by
    infer_instance
  let W : TopologicalSpace.Opens B := ⟨J ×ˢ (Set.univ : Set M), hJopen.prod isOpen_univ⟩
  have hA' : ContMDiffOn I' (I'.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : B => TotalSpace.mk' (F →L[ℝ] F) p (A p.1 p.2)) W := by
    simpa [I', B, W, ContMDiffOnSpacetimeEndomorphism] using hAspace
  have hker' : ∀ p : B, p ∈ W → Module.finrank ℝ (A p.1 p.2).ker = Module.finrank ℝ F - q := by
    intro p hp
    have hr := hrange p.1 hp.1 p.2
    let _ : FiniteDimensional ℝ (V p.2) := VectorBundle.finiteDimensional ℝ F V p.2
    have hsum := (A p.1 p.2).toLinearMap.finrank_range_add_finrank_ker
    have hd := VectorBundle.finrank_eq ℝ F V p.2
    omega
  exact ContMDiffVectorSubbundle.exists_smooth_kernel_on_open
    (I := I') (F₁ := F) (F₂ := F) (V₁ := V0) (V₂ := V0)
    (fun p : B => A p.1 p.2) W hA' (Module.finrank ℝ F - q) hker'

end ContMDiffVectorSubbundle

end

noncomputable section

open Bundle Set
open scoped Manifold ContDiff InnerProductSpace

namespace ContMDiffVectorSubbundle

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]


theorem exists_smooth_spacetime_kernel_orthogonal_range_on_open
    (A : ℝ → (x : M) → V x →L[ℝ] V x)
    {J : Set ℝ} (hJopen : IsOpen J)
    (hAspace : ContMDiffOnSpacetimeEndomorphism (I := I) (F := F) (V := V) (n := ∞)
      (fun t x ↦ A t x) (J ×ˢ (Set.univ : Set M)))
    (q : ℕ) (hrange : ∀ t ∈ J, ∀ x, Module.finrank ℝ (A t x).range = q)
    (hAsymm : ∀ t ∈ J, ∀ x, (A t x).toLinearMap.IsSymmetric) :
    let B := ℝ × M
    let I' := 𝓘(ℝ, ℝ).prod I
    let V0 : B → Type _ := fun p => V p.2
    let c0 : C^∞⟮I', B; I, M⟯ := ContMDiffMap.snd
    let _ : ∀ p : B, AddCommGroup (V0 p) := fun p => by
      change AddCommGroup (V p.2); infer_instance
    let _ : ∀ p : B, Module ℝ (V0 p) := fun p => by
      change Module ℝ (V p.2); infer_instance
    let _ : ∀ p : B, TopologicalSpace (V0 p) := fun p => by
      change TopologicalSpace (V p.2); infer_instance
    let _ : TopologicalSpace (TotalSpace F V0) := by
      change TopologicalSpace (TotalSpace F (c0 *ᵖ V)); infer_instance
    let _ : FiberBundle F V0 := by
      change FiberBundle F (c0 *ᵖ V); infer_instance
    let _ : VectorBundle ℝ F V0 := by
      change VectorBundle ℝ F (c0 *ᵖ V); infer_instance
    let _ : ContMDiffVectorBundle ∞ F V0 I' := by
      change ContMDiffVectorBundle ∞ F (c0 *ᵖ V) I'; infer_instance
    let W : TopologicalSpace.Opens B := ⟨J ×ˢ (Set.univ : Set M), hJopen.prod isOpen_univ⟩
    let c : C^∞⟮I', W; I', B⟯ := ⟨Subtype.val, contMDiff_subtype_val⟩
    let V' := fun p : W => V0 (p : B)
    let _ : ∀ p : W, AddCommGroup (V' p) := fun p => by
      change AddCommGroup (V0 (p : B)); infer_instance
    let _ : ∀ p : W, Module ℝ (V' p) := fun p => by
      change Module ℝ (V0 (p : B)); infer_instance
    let _ : TopologicalSpace (TotalSpace F V') := by
      change TopologicalSpace (TotalSpace F (c *ᵖ V0)); infer_instance
    let _ : FiberBundle F V' := by
      change FiberBundle F (c *ᵖ V0); infer_instance
    let _ : VectorBundle ℝ F V' := by
      change VectorBundle ℝ F (c *ᵖ V0); infer_instance
    let _ : ContMDiffVectorBundle ∞ F V' I' := by
      change ContMDiffVectorBundle ∞ F (c *ᵖ V0) I'; infer_instance
    ∃ K : ContMDiffVectorSubbundle (I := I') (F := F) (V := V') (n := ∞),
      K.rank = Module.finrank ℝ F - q ∧
        (∀ p : W, K.fiber p = (A (p : B).1 (p : B).2).ker) ∧
        ∀ p : W, (K.fiber p)ᗮ = (A (p : B).1 (p : B).2).range := by
  let B := ℝ × M
  let I' := 𝓘(ℝ, ℝ).prod I
  let V0 : B → Type _ := fun p => V p.2
  let c0 : C^∞⟮I', B; I, M⟯ := ContMDiffMap.snd
  let _ : ∀ p : B, AddCommGroup (V0 p) := fun p => by
    change AddCommGroup (V p.2); infer_instance
  let _ : ∀ p : B, Module ℝ (V0 p) := fun p => by
    change Module ℝ (V p.2); infer_instance
  let _ : ∀ p : B, TopologicalSpace (V0 p) := fun p => by
    change TopologicalSpace (V p.2); infer_instance
  let _ : TopologicalSpace (TotalSpace F V0) := by
    change TopologicalSpace (TotalSpace F (c0 *ᵖ V)); infer_instance
  let _ : FiberBundle F V0 := by
    change FiberBundle F (c0 *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F V0 := by
    change VectorBundle ℝ F (c0 *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle ∞ F V0 I' := by
    change ContMDiffVectorBundle ∞ F (c0 *ᵖ V) I'; infer_instance
  let W : TopologicalSpace.Opens B := ⟨J ×ˢ (Set.univ : Set M), hJopen.prod isOpen_univ⟩
  let c : C^∞⟮I', W; I', B⟯ := ⟨Subtype.val, contMDiff_subtype_val⟩
  let V' := fun p : W => V0 (p : B)
  let _ : ∀ p : W, AddCommGroup (V' p) := fun p => by
    change AddCommGroup (V0 (p : B)); infer_instance
  let _ : ∀ p : W, Module ℝ (V' p) := fun p => by
    change Module ℝ (V0 (p : B)); infer_instance
  let _ : TopologicalSpace (TotalSpace F V') := by
    change TopologicalSpace (TotalSpace F (c *ᵖ V0)); infer_instance
  let _ : FiberBundle F V' := by
    change FiberBundle F (c *ᵖ V0); infer_instance
  let _ : VectorBundle ℝ F V' := by
    change VectorBundle ℝ F (c *ᵖ V0); infer_instance
  let _ : ContMDiffVectorBundle ∞ F V' I' := by
    change ContMDiffVectorBundle ∞ F (c *ᵖ V0) I'; infer_instance
  obtain ⟨K, hKrank, hK⟩ := exists_smooth_spacetime_kernel_on_open
    (I := I) (F := F) (V := V) A hJopen hAspace q hrange
  refine ⟨K, hKrank, hK, ?_⟩
  intro p
  let _ : FiniteDimensional ℝ (V (p : B).2) :=
    VectorBundle.finiteDimensional ℝ F V (p : B).2
  rw [hK p, ← (hAsymm (p : B).1 p.2.1 (p : B).2).orthogonal_range,
    Submodule.orthogonal_orthogonal]

end ContMDiffVectorSubbundle
