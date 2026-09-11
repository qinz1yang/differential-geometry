import DifferentialGeometry.Tensor.LinearAlgebra.BlockKernelGraph
import DifferentialGeometry.Analysis.Calculus.Inverse.MatrixSmoothness
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

set_option autoImplicit false
noncomputable section

open Matrix Manifold Set
open scoped BigOperators ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private theorem transformed_matrix_mulVec {d r k : ℕ}
    (V A U : Matrix (Fin d) (Fin d) ℝ)
    (e : Fin d ≃ Fin r ⊕ Fin k) (z : Fin r ⊕ Fin k → ℝ) :
    (V * A * U).submatrix e.symm e.symm *ᵥ z =
      (V *ᵥ (A *ᵥ (U *ᵥ (z ∘ e)))) ∘ e.symm := by
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

theorem exists_smooth_constant_rank_kernel_coordinates
    {d r : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
    {s : Set X} (hs : IsOpen s) (x₀ : X) (hx₀ : x₀ ∈ s)
    (hA : ∀ i j : Fin d, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j) s)
    (hr : ∀ x ∈ s, (A x).rank = r) :
    ∃ (W : Set X)
      (G : X → (Fin (d - r) → ℝ) →ₗ[ℝ] (Fin d → ℝ))
      (Q : (Fin d → ℝ) →ₗ[ℝ] (Fin (d - r) → ℝ)),
      IsOpen W ∧ x₀ ∈ W ∧ W ⊆ s ∧
      (∀ v, ContMDiffOn I 𝓘(ℝ, Fin d → ℝ) ∞ (fun x => G x v) W) ∧
      (∀ x ∈ W, ∀ v, Q (G x v) = v) ∧
      (∀ x ∈ W, LinearMap.range (G x) = LinearMap.ker (A x).mulVecLin) := by
  classical
  have hnormal : ∃ (V U : Matrix (Fin d) (Fin d) ℝ)
      (e : Fin d ≃ Fin r ⊕ Fin (d - r)), IsUnit V ∧ IsUnit U ∧
      V * A x₀ * U = (Matrix.fromBlocks 1 0 0 0).submatrix e e := by
    have hnormal' := (A x₀).exists_rank_normal_form
    rw [hr x₀ hx₀] at hnormal'
    rw [Fintype.card_fin] at hnormal'
    exact hnormal'
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := hnormal
  have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  let N := fun x => (V * A x * U).submatrix e.symm e.symm
  let D := fun x => (N x).toBlocks₁₁
  let B := fun x => (N x).toBlocks₁₂
  let C := fun x => (N x).toBlocks₂₁
  let F := fun x => (N x).toBlocks₂₂
  have hN₀ : N x₀ = Matrix.fromBlocks 1 0 0 0 := by
    ext i j
    have h := congrArg (fun P : Matrix (Fin d) (Fin d) ℝ =>
      P (e.symm i) (e.symm j)) hnormal
    simpa only [N, Matrix.submatrix_apply, Equiv.apply_symm_apply] using h
  have hD₀ : D x₀ = 1 := by
    change (N x₀).toBlocks₁₁ = 1
    rw [hN₀, Matrix.toBlocks_fromBlocks₁₁]
  have hNrank (x : X) (hx : x ∈ s) : (N x).rank = r := by
    change ((V * A x * U).submatrix e.symm e.symm).rank = r
    rw [Matrix.rank_submatrix,
      Matrix.rank_mul_eq_left_of_isUnit_det U (V * A x) hUdet,
      Matrix.rank_mul_eq_right_of_isUnit_det V (A x) hVdet]
    exact hr x hx
  have hblockRank (x : X) (hx : x ∈ s) :
      (Matrix.fromBlocks (D x) (B x) (C x) (F x)).rank = Fintype.card (Fin r) := by
    change (Matrix.fromBlocks (N x).toBlocks₁₁ (N x).toBlocks₁₂
      (N x).toBlocks₂₁ (N x).toBlocks₂₂).rank = Fintype.card (Fin r)
    rw [Matrix.fromBlocks_toBlocks, Fintype.card_fin]
    exact hNrank x hx
  have hNsm (x : X) (hx : x ∈ s) (i j : Fin r ⊕ Fin (d - r)) :
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => N y i j) x := by
    simp only [N, Matrix.submatrix_apply, Matrix.mul_apply]
    refine ContMDiffAt.sum fun a _ => (ContMDiffAt.sum fun b _ => ?_).mul contMDiffAt_const
    exact contMDiffAt_const.mul ((hA b a).contMDiffAt (hs.mem_nhds hx))
  have hDsm (x : X) (hx : x ∈ s) :
      ContMDiffAt I 𝓘(ℝ, Fin r → Fin r → ℝ) ∞ (fun y i j => D y i j) x := by
    apply contMDiffAt_pi_space.2
    intro i
    apply contMDiffAt_pi_space.2
    intro j
    exact hNsm x hx (Sum.inl i) (Sum.inl j)
  have hdet₀ : (D x₀).det ≠ 0 := by
    rw [hD₀, Matrix.det_one]
    exact one_ne_zero
  have hdetCont : ContinuousAt (fun x => (D x).det) x₀ :=
    continuous_id.matrix_det.continuousAt.comp (hDsm x₀ hx₀).continuousAt
  have hne : {x | (D x).det ≠ 0} ∈ 𝓝 x₀ := hdetCont.eventually_ne hdet₀
  obtain ⟨W, hWsub, hWopen, hxW⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem (hs.mem_nhds hx₀) hne)
  have hW (x : X) (hx : x ∈ W) : x ∈ s ∧ (D x).det ≠ 0 := hWsub hx
  let G := fun x => U.mulVecLin.comp ((LinearMap.funLeft ℝ ℝ e).comp
    (blockKernelGraph (D x) (B x)))
  let Q := (LinearMap.funLeft ℝ ℝ (e.symm ∘ Sum.inr)).comp U⁻¹.mulVecLin
  have hzero (x : X) (z : Fin r ⊕ Fin (d - r) → ℝ) :
      N x *ᵥ z = 0 ↔ A x *ᵥ (U *ᵥ (z ∘ e)) = 0 := by
    change (V * A x * U).submatrix e.symm e.symm *ᵥ z = 0 ↔ _
    rw [transformed_matrix_mulVec]
    constructor
    · intro hz
      have hVz : V *ᵥ (A x *ᵥ (U *ᵥ (z ∘ e))) = 0 := by
        funext i
        have h := congrFun hz (e i)
        simpa only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] using h
      apply Matrix.mulVec_injective_of_isUnit hV
      simpa only [Matrix.mulVec_zero] using hVz
    · intro hz
      rw [hz, Matrix.mulVec_zero]
      rfl
  refine ⟨W, G, Q, hWopen, hxW, fun x hx => (hW x hx).1, ?_, ?_, ?_⟩
  · intro v x hx
    have hInv (i j : Fin r) :
        ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (fun y => (D y)⁻¹ i j) W x := by
      have hentries (a b : Fin r) :
          ContDiff ℝ ∞ (fun P : Fin r → Fin r → ℝ => Matrix.of P a b) := by
        change ContDiff ℝ ∞ (fun P : Fin r → Fin r → ℝ => P a b)
        fun_prop
      have hi := DifferentialGeometry.Analysis.contDiffAt_inv_of_entries
        (fun P : Fin r → Fin r → ℝ => Matrix.of P) hentries
        (x₀ := fun a b => D x a b) (hW x hx).2 i j
      exact hi.contMDiffAt.comp_contMDiffWithinAt x
        (hDsm x (hW x hx).1).contMDiffWithinAt
    have hBentry (i : Fin r) (j : Fin (d - r)) :
        ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (fun y => B y i j) W x :=
      (hNsm x (hW x hx).1 (Sum.inl i) (Sum.inr j)).contMDiffWithinAt
    apply contMDiffWithinAt_pi_space.2
    intro i
    change ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
      (fun y => ∑ j, U i j * (blockKernelGraph (D y) (B y) v) (e j)) W x
    refine ContMDiffWithinAt.sum fun j _ => contMDiffWithinAt_const.mul ?_
    rcases e j with k | k
    · change ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
        (fun y => -(∑ l, (D y)⁻¹ k l * (∑ a, B y l a * v a))) W x
      exact (ContMDiffWithinAt.sum fun l _ => (hInv k l).mul
        (ContMDiffWithinAt.sum fun a _ => (hBentry l a).mul contMDiffWithinAt_const)).neg
    · exact contMDiffWithinAt_const
  · intro x hx v
    funext j
    change (U⁻¹ *ᵥ (U *ᵥ (blockKernelGraph (D x) (B x) v ∘ e)))
      (e.symm (Sum.inr j)) = v j
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul U hUdet, Matrix.one_mulVec]
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rfl
  · intro x hx
    have hDunit : IsUnit (D x).det := isUnit_iff_ne_zero.mpr (hW x hx).2
    apply le_antisymm
    · rintro w ⟨v, rfl⟩
      have hz := blockKernelGraph_mem_ker (D x) (B x) (C x) (F x)
        hDunit (hblockRank x (hW x hx).1) v
      change (Matrix.fromBlocks (N x).toBlocks₁₁ (N x).toBlocks₁₂
        (N x).toBlocks₂₁ (N x).toBlocks₂₂) *ᵥ blockKernelGraph (D x) (B x) v = 0 at hz
      rw [Matrix.fromBlocks_toBlocks] at hz
      exact (hzero x (blockKernelGraph (D x) (B x) v)).mp hz
    · intro w hw
      change A x *ᵥ w = 0 at hw
      let z := (U⁻¹ *ᵥ w) ∘ e.symm
      have hzOriginal : U *ᵥ (z ∘ e) = w := by
        dsimp only [z, Function.comp_def]
        simp only [Equiv.symm_apply_apply]
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv U hUdet, Matrix.one_mulVec]
      have hz : z ∈ LinearMap.ker
          (Matrix.fromBlocks (D x) (B x) (C x) (F x)).mulVecLin := by
        change (Matrix.fromBlocks (N x).toBlocks₁₁ (N x).toBlocks₁₂
          (N x).toBlocks₂₁ (N x).toBlocks₂₂) *ᵥ z = 0
        rw [Matrix.fromBlocks_toBlocks]
        exact (hzero x z).mpr (by rw [hzOriginal]; exact hw)
      obtain ⟨v, hv⟩ := (blockKernelGraphEquiv (D x) (B x) (C x) (F x)
        hDunit (hblockRank x (hW x hx).1)).surjective ⟨z, hz⟩
      have hgraph : blockKernelGraph (D x) (B x) v = z := congrArg Subtype.val hv
      refine ⟨v, ?_⟩
      change U *ᵥ (blockKernelGraph (D x) (B x) v ∘ e) = w
      rw [hgraph, hzOriginal]

theorem exists_smooth_local_kernel_section
    {d r : ℕ} (A : X → Matrix (Fin d) (Fin d) ℝ)
    {s : Set X} (hs : IsOpen s) (x₀ : X) (hx₀ : x₀ ∈ s)
    (hA : ∀ i j : Fin d, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j) s)
    (hr : ∀ x ∈ s, (A x).rank = r)
    (v : LinearMap.ker (A x₀).mulVecLin) :
    ∃ (W : Set X) (w : X → Fin d → ℝ),
      IsOpen W ∧ x₀ ∈ W ∧ W ⊆ s ∧
      ContMDiffOn I 𝓘(ℝ, Fin d → ℝ) ∞ w W ∧ w x₀ = v.1 ∧
      ∀ x ∈ W, w x ∈ LinearMap.ker (A x).mulVecLin := by
  obtain ⟨W, G, Q, hW, hxW, hWs, hG, _hQ, hRange⟩ :=
    exists_smooth_constant_rank_kernel_coordinates A hs x₀ hx₀ hA hr
  have hv : v.1 ∈ LinearMap.range (G x₀) := (hRange x₀ hxW).ge v.property
  obtain ⟨c, hc⟩ := hv
  refine ⟨W, fun x => G x c, hW, hxW, hWs, hG c, hc, ?_⟩
  intro x hx
  rw [← hRange x hx]
  exact ⟨c, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
