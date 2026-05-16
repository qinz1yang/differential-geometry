/-
Authors: Jack McCarthy
-/
import RicciFlower.Tensor.Auxiliary.Fin
import RicciFlower.Tensor.Auxiliary.MultiKroneckerDelta
import RicciFlower.Tensor.Auxiliary.Basis
import RicciFlower.Tensor.Alternating.Curry
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Elementary Covectors

This file defines the elementary k-covectors of a vector space, given a basis of the
continuous dual.

## Main Definitions

* `ContinuousAlternatingMap.elementaryCovector b ι` : given a basis `b` of the continuous
  dual `E →L[𝕜] 𝕜` and a multi-index `ι : Fin k → Fin n`, the elementary k-covector
  mapping `(v 0, ..., v (k-1))` to `det (fun i j => b (ι i) (v j))`.
-/

noncomputable section

open scoped BigOperators

namespace ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n k : ℕ}

/-- The elementary k-covector associated to a basis `b` of the continuous dual `E →L[𝕜] 𝕜`
and a multi-index `ι : Fin k → Fin n`. Given vectors `v 0, ..., v (k-1)` in `E`, this map
returns the determinant of the k×k matrix whose `(i, j)` entry is `b (ι i) (v j)`.

Concretely, this is the continuous alternating map
  `v ↦ det (fun i j => b (ι i) (v j))`.
It is alternating in `v` because the determinant is alternating in its columns. -/
noncomputable def elementaryCovector
    (b : Module.Basis (Fin n) 𝕜 (E →L[𝕜] 𝕜))
    (ι : Fin k → Fin n) :
    E [⋀^Fin k]→L[𝕜] 𝕜 :=
  -- φ : E →ₗ[𝕜] (Fin k → 𝕜) sends x ↦ (j ↦ b (ι j) x).
  -- detRowAlternating (φ ∘ v) = det(r,c ↦ b(ι c)(v r)) = det(i,j ↦ b(ι i)(v j))ᵀ
  -- which equals det(i,j ↦ b(ι i)(v j)) since det = det of transpose.
  let φ : E →ₗ[𝕜] (Fin k → 𝕜) := LinearMap.pi (fun i => (b (ι i)).toLinearMap)
  (Matrix.detRowAlternating.compLinearMap φ).mkContinuous
    ((k.factorial : ℝ) * ∏ i : Fin k, ‖b (ι i)‖)
    (fun v => by
      -- Use `change` to rewrite via definitional equality:
      -- (detRowAlternating.compLinearMap φ) v = detRowAlternating (fun r c => b(ι c)(v r))
      change ‖Matrix.detRowAlternating (R := 𝕜) (n := Fin k)
            (fun r c => b (ι c) (v r))‖ ≤
          ((k.factorial : ℝ) * ∏ i : Fin k, ‖b (ι i)‖) * ∏ i : Fin k, ‖v i‖
      -- det(r,c ↦ b(ι c)(v r)) = det(i,j ↦ b(ι i)(v j)) since the two matrices are transposes
      rw [show Matrix.detRowAlternating (R := 𝕜) (n := Fin k) (fun r c => b (ι c) (v r)) =
            Matrix.det (fun i j : Fin k => b (ι i) (v j)) from by
          change Matrix.det (fun r c : Fin k => b (ι c) (v r)) =
            Matrix.det (fun i j : Fin k => b (ι i) (v j))
          rw [← Matrix.det_transpose]; rfl]
      -- Bound via Leibniz: |∑_σ sign(σ) • ∏_i b(ι(σ i))(v i)| ≤ k! * ∏_i ‖b(ι i)‖ * ∏_i ‖v i‖
      rw [Matrix.det_apply]
      calc ‖∑ σ : Equiv.Perm (Fin k),
                Equiv.Perm.sign σ • ∏ i : Fin k, b (ι (σ i)) (v i)‖
          ≤ ∑ σ : Equiv.Perm (Fin k),
                ‖∏ i : Fin k, b (ι (σ i)) (v i)‖ := by
              refine (norm_sum_le _ _).trans (le_of_eq ?_)
              congr 1; ext σ; exact norm_units_zsmul _ _
        _ ≤ ∑ σ : Equiv.Perm (Fin k),
                ∏ i : Fin k, ‖b (ι (σ i))‖ * ‖v i‖ :=
              Finset.sum_le_sum fun σ _ => by
                have h1 : ‖∏ i : Fin k, b (ι (σ i)) (v i)‖ =
                    ∏ i : Fin k, ‖b (ι (σ i)) (v i)‖ := norm_prod _ _
                have h2 : ∏ i : Fin k, ‖b (ι (σ i)) (v i)‖ ≤
                    ∏ i : Fin k, ‖b (ι (σ i))‖ * ‖v i‖ :=
                  Finset.prod_le_prod (fun i _ => norm_nonneg _)
                    (fun i _ => (b (ι (σ i))).le_opNorm _)
                exact h1.le.trans h2
        _ = ((k.factorial : ℝ) * ∏ i : Fin k, ‖b (ι i)‖) * ∏ i : Fin k, ‖v i‖ := by
              have hperm : ∀ σ : Equiv.Perm (Fin k),
                  ∏ i : Fin k, ‖b (ι (σ i))‖ * ‖v i‖ =
                  (∏ i : Fin k, ‖b (ι i)‖) * ∏ i : Fin k, ‖v i‖ := fun σ => by
                rw [Finset.prod_mul_distrib]
                congr 1
                rw [σ.prod_comp Finset.univ (fun i => ‖b (ι i)‖)
                  (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
              rw [Finset.sum_congr rfl (fun σ _ => hperm σ), Finset.sum_const,
                Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
              ring)

@[simp]
theorem elementaryCovector_apply
    (b : Module.Basis (Fin n) 𝕜 (E →L[𝕜] 𝕜))
    (ι : Fin k → Fin n)
    (v : Fin k → E) :
    elementaryCovector b ι v = Matrix.det (fun i j => b (ι i) (v j)) := by
  -- By definitional equality, elementaryCovector b ι v reduces to
  -- detRowAlternating (fun r c => b(ι c)(v r)) = det(fun i j => b(ι i)(v j))
  change Matrix.det (fun r c : Fin k => b (ι c) (v r)) =
    Matrix.det (fun i j : Fin k => b (ι i) (v j))
  rw [← Matrix.det_transpose]; rfl

/-- Cofactor expansion: the interior product `curryFin (elementaryCovector b I) x` expands as a
sum over deleted row indices, via Laplace expansion of the determinant along the first column. -/
theorem curryFin_elementaryCovector
    (b : Module.Basis (Fin n) 𝕜 (E →L[𝕜] 𝕜))
    (I : Fin (k + 1) → Fin n) (x : E) :
    curryFin (elementaryCovector b I) x =
    ∑ i : Fin (k + 1), ((-1 : 𝕜) ^ i.val * b (I i) x) •
      elementaryCovector b (I ∘ Fin.succAbove i) := by
  ext v
  simp only [curryFin_apply, sum_apply, smul_apply, smul_eq_mul]
  rw [elementaryCovector_apply, Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl; intro i _
  simp only [Fin.cons_zero]
  congr 1; rw [elementaryCovector_apply]; congr 1

/-- Evaluating an elementary covector on basis vectors gives the generalized
Kronecker delta. Given a dual basis pair `(B, b)` with `b i (B j) = δ_{ij}`,
we have `elementaryCovector b I (B ∘ J) = multiKroneckerDelta I J`. -/
theorem elementaryCovector_basis_eval
    (B : Module.Basis (Fin n) 𝕜 E)
    (b : Module.Basis (Fin n) 𝕜 (E →L[𝕜] 𝕜))
    (dual : ∀ i j, b i (B j) = if i = j then 1 else 0)
    (I J : Fin k → Fin n) :
    elementaryCovector b I (B ∘ J) = Fin.multiKroneckerDelta I J := by
  unfold Fin.multiKroneckerDelta
  rw [elementaryCovector_apply]
  congr 1
  ext i j
  exact dual (I i) (J j)

/-- If `J` is injective and `I = J ∘ σ`, then evaluating the elementary covector
`elementaryCovector b I` on `(B (J 0), ..., B (J (k-1)))` gives `sign σ`. -/
theorem elementaryCovector_basis_eval_comp_perm
    (B : Module.Basis (Fin n) 𝕜 E)
    (b : Module.Basis (Fin n) 𝕜 (E →L[𝕜] 𝕜))
    (dual : ∀ i j, b i (B j) = if i = j then 1 else 0)
    {J : Fin k → Fin n} (hJ : Function.Injective J)
    (σ : Equiv.Perm (Fin k)) :
    elementaryCovector b (J ∘ ⇑σ) (B ∘ J) = (Equiv.Perm.sign σ : 𝕜) := by
  rw [elementaryCovector_basis_eval B b dual,
    Fin.multiKroneckerDelta_comp_perm hJ]

/-- If no permutation `σ` satisfies `I = J ∘ σ`, then evaluating the elementary
covector `elementaryCovector b I` on `(B (J 0), ..., B (J (k-1)))` gives `0`. -/
theorem elementaryCovector_basis_eval_eq_zero
    (B : Module.Basis (Fin n) 𝕜 E)
    (b : Module.Basis (Fin n) 𝕜 (E →L[𝕜] 𝕜))
    (dual : ∀ i j, b i (B j) = if i = j then 1 else 0)
    {I J : Fin k → Fin n}
    (h : ∀ σ : Equiv.Perm (Fin k), I ≠ J ∘ ⇑σ) :
    elementaryCovector b I (B ∘ J) = 0 := by
  rw [elementaryCovector_basis_eval B b dual,
    Fin.multiKroneckerDelta_eq_zero h]

/-- If `I` is not injective (has a repeated index), then evaluating the elementary
covector `elementaryCovector b I` on any basis vectors gives `0`. -/
theorem elementaryCovector_basis_eval_eq_zero_of_not_injective_left
    (B : Module.Basis (Fin n) 𝕜 E)
    (b : Module.Basis (Fin n) 𝕜 (E →L[𝕜] 𝕜))
    (dual : ∀ i j, b i (B j) = if i = j then 1 else 0)
    {I : Fin k → Fin n} (hI : ¬Function.Injective I)
    (J : Fin k → Fin n) :
    elementaryCovector b I (B ∘ J) = 0 := by
  rw [elementaryCovector_basis_eval B b dual,
    Fin.multiKroneckerDelta_eq_zero_of_not_injective_left hI]

/-- If `J` is not injective (has a repeated index), then evaluating the elementary
covector on `(B (J 0), ..., B (J (k-1)))` gives `0`. -/
theorem elementaryCovector_basis_eval_eq_zero_of_not_injective_right
    (B : Module.Basis (Fin n) 𝕜 E)
    (b : Module.Basis (Fin n) 𝕜 (E →L[𝕜] 𝕜))
    (dual : ∀ i j, b i (B j) = if i = j then 1 else 0)
    {J : Fin k → Fin n} (hJ : ¬Function.Injective J)
    (I : Fin k → Fin n) :
    elementaryCovector b I (B ∘ J) = 0 := by
  rw [elementaryCovector_basis_eval B b dual,
    Fin.multiKroneckerDelta_eq_zero_of_not_injective_right hJ]

/-- If `I = J ∘ σ` for a permutation `σ`, then
`elementaryCovector b I = sign(σ) • elementaryCovector b J`.
This follows from `multiKroneckerDelta_comp_perm_left`. -/
theorem elementaryCovector_comp_perm
    [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (b : Module.Basis (Fin n) 𝕜 (E →L[𝕜] 𝕜))
    (J : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    elementaryCovector b (J ∘ ⇑σ) =
      (Equiv.Perm.sign σ : 𝕜) • elementaryCovector b J := by
  obtain ⟨B, dual⟩ := exists_predual_basis b
  apply toAlternatingMap_injective
  apply B.ext_alternating
  intro v hv
  change elementaryCovector b (J ∘ ⇑σ) (B ∘ v) =
    (Equiv.Perm.sign σ : 𝕜) • elementaryCovector b J (B ∘ v)
  rw [elementaryCovector_basis_eval B b dual,
    elementaryCovector_basis_eval B b dual,
    Fin.multiKroneckerDelta_comp_perm_left, smul_eq_mul]

/-!
## Basis of elementary covectors
-/

section ElementaryCovectorBasis

variable
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
/-- The elementary covectors indexed by strictly increasing
multi-indices are linearly independent. -/
theorem elementaryCovector_linearIndependent
    (B : Module.Basis (Fin n) 𝕜 E)
    (b : Module.Basis (Fin n) 𝕜 (E →L[𝕜] 𝕜))
    (dual : ∀ i j, b i (B j) = if i = j then 1 else 0) :
    LinearIndependent 𝕜
      (fun ι : Fin k ↪o Fin n =>
        elementaryCovector b ι) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc J
  classical
  have heval : (∑ ι : Fin k ↪o Fin n,
      c ι • elementaryCovector b ι) (B ∘ J) = 0 := by
    rw [hc]; rfl
  simp only [ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply,
    elementaryCovector_basis_eval B b dual] at heval
  -- multiKroneckerDelta ι J = if ι = J then 1 else 0
  have hkron : ∀ ι : Fin k ↪o Fin n,
      Fin.multiKroneckerDelta (⇑ι) (⇑J) =
        if ι = J then (1 : 𝕜) else 0 := fun ι => by
    split_ifs with h
    · rw [h]
      have := Fin.multiKroneckerDelta_comp_perm (R := 𝕜)
        (RelEmbedding.injective J) (Equiv.refl (Fin k))
      simpa using this
    · exact Fin.multiKroneckerDelta_eq_zero
        (Equiv.Perm.orderEmb_ne_comp_perm h)
  simp only [hkron, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at heval
  rwa [smul_eq_mul, mul_one] at heval

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
/-- Every continuous alternating map is in the span of the
elementary covectors. -/
theorem elementaryCovector_span
    (B : Module.Basis (Fin n) 𝕜 E)
    (b : Module.Basis (Fin n) 𝕜 (E →L[𝕜] 𝕜))
    (dual : ∀ i j, b i (B j) = if i = j then 1 else 0)
    (F : E [⋀^Fin k]→L[𝕜] 𝕜) :
    F ∈ Submodule.span 𝕜
      (Set.range (fun ι : Fin k ↪o Fin n =>
        elementaryCovector b ι)) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun ι => F (B ∘ ι), ?_⟩
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply B.ext_alternating
  intro v hv
  -- .toAlternatingMap (fun i => B (v i)) = . (B ∘ v) by rfl
  have key : ∀ g : E [⋀^Fin k]→L[𝕜] 𝕜,
      g.toAlternatingMap (fun i => B (v i)) =
        g (B ∘ v) := fun _ => rfl
  simp only [key, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    elementaryCovector_basis_eval B b dual]
  -- Goal: ∑ F(B∘ι) * δ(ι,v) = F(B∘v)
  -- Factor v = ι₀ ∘ σ using Finset.orderEmbOfFin
  set s := Finset.image v Finset.univ
  have hs_card : s.card = k := by
    rw [Finset.card_image_of_injective _ hv,
      Finset.card_fin]
  set ι₀ := s.orderEmbOfFin hs_card
  have hv_mem : ∀ i, v i ∈ s := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  -- Build the permutation σ with v = ι₀ ∘ σ
  let f : Fin k → Fin k := fun i =>
    (s.orderIsoOfFin hs_card).symm ⟨v i, hv_mem i⟩
  have hf_inj : Function.Injective f := fun a b h => by
    have := congr_arg Subtype.val
      ((s.orderIsoOfFin hs_card).symm.injective h)
    exact hv this
  have hf_bij :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hf_inj, rfl⟩
  set σ := Equiv.ofBijective f hf_bij
  have hσ : v = ⇑ι₀ ∘ ⇑σ := funext fun i => by
    change v i = s.orderEmbOfFin hs_card
      ((s.orderIsoOfFin hs_card).symm ⟨v i, _⟩)
    have : s.orderEmbOfFin hs_card =
        Subtype.val ∘ (s.orderIsoOfFin hs_card) := by
      ext j; rfl
    rw [this, Function.comp_apply,
      OrderIso.apply_symm_apply]
  -- For ι ≠ ι₀: delta vanishes
  have hvanish : ∀ ι : Fin k ↪o Fin n, ι ≠ ι₀ →
      Fin.multiKroneckerDelta (R := 𝕜) (⇑ι) v = 0 := by
    intro ι hne
    rw [hσ, Fin.multiKroneckerDelta_symm (R := 𝕜),
      Fin.multiKroneckerDelta_eq_zero]
    intro τ h; apply hne; apply Equiv.Perm.orderEmb_eq_of_range_eq
    have := congr_arg Set.range h
    simp [Set.range_comp] at this
    exact this.symm
  -- For ι₀: delta = sign(σ)
  have hι₀_term :
      Fin.multiKroneckerDelta (R := 𝕜) (⇑ι₀) v =
        (Equiv.Perm.sign σ : 𝕜) := by
    rw [hσ, Fin.multiKroneckerDelta_symm (R := 𝕜),
      Fin.multiKroneckerDelta_comp_perm ι₀.injective]
  -- F(B ∘ v) = sign(σ) * F(B ∘ ι₀)
  have hF_perm : F (B ∘ v) =
      (Equiv.Perm.sign σ : 𝕜) * F (B ∘ ι₀) := by
    conv_lhs => rw [hσ]
    change F ((B ∘ ⇑ι₀) ∘ ⇑σ) = _
    have := F.toAlternatingMap.map_perm (B ∘ ⇑ι₀) σ
    simp only [
      ContinuousAlternatingMap.coe_toAlternatingMap]
      at this
    rw [this, Units.smul_def, zsmul_eq_mul]
  -- Collapse the sum to the single ι₀ term
  symm; rw [hF_perm, Finset.sum_eq_single ι₀]
  · rw [hι₀_term, mul_comm]
  · intro ι _ hne; rw [hvanish ι hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ ι₀) h

/-- The elementary covectors indexed by strictly increasing multi-indices
`Fin k ↪o Fin n` form a basis for the space of continuous alternating `k`-forms
`E [⋀^Fin k]→L[𝕜] 𝕜`. The covectors are built from `B.cDualBasis`, the continuous
dual basis induced by `B`. -/
noncomputable def elementaryCovectorBasis
    (B : Module.Basis (Fin n) 𝕜 E) :
    Module.Basis (Fin k ↪o Fin n) 𝕜
      (E [⋀^Fin k]→L[𝕜] 𝕜) :=
  Module.Basis.mk
    (elementaryCovector_linearIndependent B B.cDualBasis B.cDualBasis_apply_self)
    (fun F _ => elementaryCovector_span B B.cDualBasis B.cDualBasis_apply_self F)

@[simp]
theorem elementaryCovectorBasis_apply
    (B : Module.Basis (Fin n) 𝕜 E) (I : Fin k ↪o Fin n) :
    (elementaryCovectorBasis B : Module.Basis (Fin k ↪o Fin n) 𝕜 _) I =
      elementaryCovector B.cDualBasis ↑I := by
  rw [elementaryCovectorBasis, Module.Basis.mk_apply]

/-- The dimension of `E [⋀^Fin k]→L[𝕜] 𝕜` is `(finrank 𝕜 E).choose k`. -/
theorem finrank_continuousAlternatingMap :
    Module.finrank 𝕜 (E [⋀^Fin k]→L[𝕜] 𝕜) =
      (Module.finrank 𝕜 E).choose k := by
  set d := Module.finrank 𝕜 E
  let B : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  rw [Module.finrank_eq_card_basis
      (elementaryCovectorBasis (k := k) B)]
  -- Fintype.card (Fin k ↪o Fin d) = d.choose k
  rw [Fintype.card_congr
    (Set.powersetCard.ofFinEmbEquiv
      (I := Fin d) (n := k))]
  have h := Set.powersetCard.card
    (α := Fin d) (n := k)
  rw [Nat.card_eq_fintype_card] at h
  simp only [Nat.card_eq_fintype_card,
    Fintype.card_fin] at h
  exact h

end ElementaryCovectorBasis

end ContinuousAlternatingMap

end
