import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Alternating.Permutation
import DifferentialGeometry.Tensor.Exterior.Basic
import DifferentialGeometry.Tensor.Exterior.Defs
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

noncomputable section


open ContinuousAlternatingMap
open scoped Topology Manifold ContDiff Bundle
open Filter

namespace ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n : ℕ}

private def flipAddCongr (m n : ℕ) : Fin (n + m) ≃ Fin (m + n) :=
  Equiv.trans ((finSumFinEquiv (m := n) (n := m)).symm : Fin (n + m) ≃ Fin n ⊕ Fin m)
    (Equiv.trans (Fin.finSumCongr.symm : Fin n ⊕ Fin m ≃ Fin m ⊕ Fin n)
      (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)))

private lemma flipAddCongr_finSumFinEquiv (m n : ℕ) (x : Fin n ⊕ Fin m) :
    flipAddCongr m n (finSumFinEquiv (m := n) (n := m) x) =
      finSumFinEquiv (Fin.finSumCongr x) := by
  cases x with
  | inl i => simp [flipAddCongr, Fin.finSumCongr]
  | inr i => simp [flipAddCongr, Fin.finSumCongr]

private lemma sumCongrPerm_inl (σ : Equiv.Perm (Fin m ⊕ Fin n)) (i : Fin n) :
    Equiv.Perm.sumCongrPerm σ (Sum.inl i) = Fin.finSumCongr (σ (Sum.inr i)) := by
  simp [Equiv.Perm.sumCongrPerm, Equiv.permCongr, Fin.finSumCongr]

private lemma sumCongrPerm_inr (σ : Equiv.Perm (Fin m ⊕ Fin n)) (i : Fin m) :
    Equiv.Perm.sumCongrPerm σ (Sum.inr i) = Fin.finSumCongr (σ (Sum.inl i)) := by
  simp [Equiv.Perm.sumCongrPerm, Equiv.permCongr, Fin.finSumCongr]

private lemma uncurrySum_summand_flip (h : M [⋀^Fin n]→L[𝕜] N') (g : M [⋀^Fin m]→L[𝕜] N)
    (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (n + m) → M)
    (σ : Equiv.Perm (Fin n ⊕ Fin m)) :
    uncurrySum.summand (f.flip.compContinuousAlternatingMap₂ h g) (Quotient.mk'' σ)
        (v ∘ finSumFinEquiv) =
      uncurrySum.summand (f.compContinuousAlternatingMap₂ g h)
        (Quotient.mk'' (Equiv.Perm.sumCongrPerm (m := n) (n := m) σ))
        ((v ∘ flipAddCongr n m) ∘ finSumFinEquiv) := by
  rw [uncurrySum_summand_eval, uncurrySum_summand_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply, Function.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [Equiv.Perm.sign_sumCongrPerm]
  congr 2
  · apply congrArg f
    apply congrArg g
    funext i
    simp [sumCongrPerm_inl, flipAddCongr_finSumFinEquiv, Fin.finSumCongr, Sum.swap_swap]
  · apply congrArg h
    funext i
    simp [sumCongrPerm_inr, flipAddCongr_finSumFinEquiv, Fin.finSumCongr, Sum.swap_swap]

private lemma uncurrySum_summand_flip' (h : M [⋀^Fin n]→L[𝕜] N') (g : M [⋀^Fin m]→L[𝕜] N)
    (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (n + m) → M)
    (σ : Equiv.Perm.ModSumCongr (Fin n) (Fin m)) :
    uncurrySum.summand (f.flip.compContinuousAlternatingMap₂ h g) σ (v ∘ finSumFinEquiv) =
      uncurrySum.summand (f.compContinuousAlternatingMap₂ g h)
        (Equiv.Perm.finAddCongrEquiv (m := n) (n := m) σ)
        ((v ∘ flipAddCongr n m) ∘ finSumFinEquiv) := by
  refine Quotient.inductionOn' σ ?_
  intro σ'
  unfold Equiv.Perm.finAddCongrEquiv
  exact uncurrySum_summand_flip h g f v σ'

private def derivFinCast (m n : ℕ) : Fin (m + n + 1) ≃ Fin (n + m + 1) :=
  finCongr (by omega)

omit [NontriviallyNormedField 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  [NormedAddCommGroup N'] [NormedSpace 𝕜 N'] [NormedAddCommGroup N''] [NormedSpace 𝕜 N''] in
private lemma removeNth_cast (m n : ℕ) (v : Fin (m + n + 1) → M) (k : Fin (m + n + 1)) :
    (derivFinCast m n k).removeNth (v ∘ (derivFinCast m n).symm) =
      (k.removeNth v) ∘ (Fin.finAddCongr (m := n) (n := m)) := by
  ext i
  rw [Fin.removeNth_apply, Function.comp_apply, Function.comp_apply, Fin.removeNth_apply]
  apply congrArg v
  apply Fin.ext
  have hk : ((derivFinCast m n k : Fin (n + m + 1)).val) = k.val := by
    simp [derivFinCast, Fin.val_cast]
  have hi : ((Fin.finAddCongr (m := n) (n := m) i : Fin (m + n)).val) = i.val := by
    simp [Fin.finAddCongr, Fin.val_cast]
  by_cases h : i.val < k.val
  · have hc1 : i.castSucc < (derivFinCast m n k : Fin (n + m + 1)) := by
      rw [Fin.lt_def]
      simp [Fin.val_castSucc, hk, h]
    have hc2 : (Fin.finAddCongr (m := n) (n := m) i).castSucc < k := by
      rw [Fin.lt_def]
      simp [Fin.finAddCongr, Fin.val_cast, Fin.val_castSucc, h]
    rw [Fin.succAbove_of_castSucc_lt _ _ hc1]
    rw [Fin.succAbove_of_castSucc_lt _ _ hc2]
    exact hi.symm
  · have hn1 : ¬ i.castSucc < (derivFinCast m n k : Fin (n + m + 1)) := by
      rw [Fin.lt_def]
      simp [Fin.val_castSucc, hk, h]
    have hn2 : ¬ (Fin.finAddCongr (m := n) (n := m) i).castSucc < k := by
      rw [Fin.lt_def]
      simp [Fin.finAddCongr, Fin.val_cast, Fin.val_castSucc, h]
    rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hn1)]
    rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hn2)]
    simpa [derivFinCast, Fin.val_cast, Fin.val_succ] using hi.symm

private lemma flipAddCongr_eq_addCasesSwapPerm (m n : ℕ) :
    (flipAddCongr m n).trans (Fin.finAddCongr (m := n) (n := m)).symm =
      (finCongr (show m + n = n + m by omega)).permCongr (Equiv.Perm.addCasesSwapPerm m n) := by
  ext i
  simp only [Equiv.Perm.addCasesSwapPerm]
  cases hs : (finSumFinEquiv (m := n) (n := m)).symm i with
  | inl a =>
      have hi : i = finSumFinEquiv (m := n) (n := m) (Sum.inl a) := by
        rw [← hs]
        simp
      rw [hi]
      simp [flipAddCongr, Fin.finAddCongr, finSumFinEquiv_apply_left,
        finSumFinEquiv_symm_apply_castAdd, Fin.finSumCongr, Equiv.permCongr_def, finCongr,
        Fin.val_cast]
      omega
  | inr a =>
      have hi : i = finSumFinEquiv (m := n) (n := m) (Sum.inr a) := by
        rw [← hs]
        simp
      rw [hi]
      simp [flipAddCongr, Fin.finAddCongr, finSumFinEquiv_apply_right,
        finSumFinEquiv_symm_apply_natAdd, Fin.finSumCongr, Equiv.permCongr_def, finCongr,
        Fin.val_cast]

private theorem wedge_flip (h : M [⋀^Fin n]→L[𝕜] N') (g : M [⋀^Fin m]→L[𝕜] N)
    (f : N →L[𝕜] N' →L[𝕜] N'') :
    wedgeProduct h g f.flip = (wedgeProduct g h f).domDomCongr (flipAddCongr n m) := by
  ext v
  rw [wedge_product_def]
  rw [ContinuousAlternatingMap.domDomCongr_apply]
  rw [wedge_product_def]
  rw [uncurryFinAdd, uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply, uncurrySum_apply,
    _root_.sum_apply, _root_.sum_apply]
  refine Finset.sum_bij
    (fun (σ : Equiv.Perm.ModSumCongr (Fin n) (Fin m)) _ =>
      Equiv.Perm.finAddCongrEquiv (m := n) (n := m) σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp
  · intro σ₁ hσ₁ σ₂ hσ₂ h
    exact Equiv.injective (Equiv.Perm.finAddCongrEquiv (m := n) (n := m)) h
  · intro τ hτ
    exact ⟨(Equiv.Perm.finAddCongrEquiv (m := n) (n := m)).symm τ, by simp,
      Equiv.apply_symm_apply _ τ⟩
  · intro σ hσ
    exact uncurrySum_summand_flip' h g f v σ

private lemma map_perm_sign {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : M [⋀^ι]→L[𝕜] N'') (w : ι → M) (sigma : Equiv.Perm ι) :
    A (w ∘ sigma) = Equiv.Perm.sign sigma • A w := by
  exact A.toAlternatingMap.map_perm w sigma

private lemma uncurryFin_reindex (P : M →L[𝕜] (M [⋀^Fin (n + m)]→L[𝕜] N''))
    (v : Fin (m + n + 1) → M) :
    (∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
        P (v k) ((derivFinCast m n k).removeNth (v ∘ (derivFinCast m n).symm))) =
      uncurryFin P (v ∘ (derivFinCast m n).symm) := by
  rw [uncurryFin_apply]
  refine Finset.sum_bij (fun k _ => derivFinCast m n k) ?_ ?_ ?_ ?_
  · intro k hk
    simp
  · intro k₁ hk₁ k₂ hk₂ h
    exact (Equiv.injective (derivFinCast m n)) h
  · intro k' hk'
    exact ⟨(derivFinCast m n).symm k', by simp, by simp⟩
  · intro k hk
    have hk' : ((derivFinCast m n k : Fin (n + m + 1)).val) = k.val := by
      simp [derivFinCast, Fin.val_cast]
    simp [hk']

private lemma sign_flipAddCongr_composite (m n : ℕ) :
    Equiv.Perm.sign ((flipAddCongr m n).trans (Fin.finAddCongr (m := n) (n := m)).symm) =
      (-1 : ℤˣ) ^ (m * n) := by
  rw [flipAddCongr_eq_addCasesSwapPerm, Equiv.Perm.sign_permCongr,
    Equiv.Perm.addCasesSwapPerm_sign]

private lemma flipAddCongr_composite_eq_addCasesSwapPerm_apply (m n : ℕ) (x : Fin (m + n + 1)) :
    (derivFinCast m n).symm
        (Fin.finAddFlipAssoc (m := n) (p := 1) (n := m)
          (flipAddCongr (n + 1) m
            (Fin.cast (show m + n + 1 = m + (n + 1) by omega) x))) =
      Fin.cast (show (n + 1) + m = m + n + 1 by omega)
        (Equiv.Perm.addCasesSwapPerm (n + 1) m
          (Fin.cast (show m + n + 1 = (n + 1) + m by omega) x)) := by
  apply Fin.ext
  simp only [Fin.val_cast, Equiv.Perm.addCasesSwapPerm]
  by_cases h : x.val < m
  · simp [h, flipAddCongr, finSumFinEquiv, Fin.finSumCongr, Fin.finAddFlipAssoc, derivFinCast,
      Fin.val_cast, Fin.addCases, Sum.swap_inl]
    omega
  · simp [h, flipAddCongr, finSumFinEquiv, Fin.finSumCongr, Fin.finAddFlipAssoc, derivFinCast,
      Fin.val_cast, Fin.val_castAdd, Fin.addCases, Sum.swap_inr]

private lemma flipAddCongr_composite_eq_addCasesSwapPerm_apply' (m n : ℕ)
    (x : Fin (m + (n + 1))) :
    (derivFinCast m n).symm (Fin.finAddFlipAssoc (m := n) (p := 1) (n := m)
        (flipAddCongr (n + 1) m x)) =
      Fin.cast (show (n + 1) + m = m + n + 1 by omega)
        (Equiv.Perm.addCasesSwapPerm (n + 1) m
          (Fin.cast (show m + (n + 1) = (n + 1) + m by omega) x)) := by
  apply Fin.ext
  simp only [Fin.val_cast, Equiv.Perm.addCasesSwapPerm]
  by_cases h : x.val < m
  · simp [h, flipAddCongr, finSumFinEquiv, Fin.finSumCongr, Fin.finAddFlipAssoc, derivFinCast,
      Fin.val_cast, Fin.addCases, Sum.swap_inl]
    omega
  · simp [h, flipAddCongr, finSumFinEquiv, Fin.finSumCongr, Fin.finAddFlipAssoc, derivFinCast,
      Fin.val_cast, Fin.val_castAdd, Fin.addCases, Sum.swap_inr]

private lemma addCasesSwapPerm_cast_sign (m n : ℕ) :
    Equiv.Perm.sign (Equiv.trans
        (Equiv.trans (finCongr (show m + n + 1 = (n + 1) + m by omega))
          (Equiv.Perm.addCasesSwapPerm (n + 1) m))
        (finCongr (show (n + 1) + m = m + n + 1 by omega))) =
      (-1 : ℤˣ) ^ ((n + 1) * m) := by
  let e : Fin (m + n + 1) ≃ Fin ((n + 1) + m) :=
    finCongr (show m + n + 1 = (n + 1) + m by omega)
  have h : Equiv.trans (Equiv.trans e (Equiv.Perm.addCasesSwapPerm (n + 1) m)) e.symm =
      e.symm.permCongr (Equiv.Perm.addCasesSwapPerm (n + 1) m) := by
    rw [Equiv.trans_assoc, Equiv.permCongr_def, Equiv.symm_symm]
    rfl
  change Equiv.Perm.sign (Equiv.trans
      (Equiv.trans e (Equiv.Perm.addCasesSwapPerm (n + 1) m)) e.symm) =
    (-1 : ℤˣ) ^ ((n + 1) * m)
  rw [h, Equiv.Perm.sign_permCongr, Equiv.Perm.addCasesSwapPerm_sign]

private lemma units_neg_pow_smul (k₁ k₂ : ℕ) (x : N'') :
    ((-1 : ℤˣ) ^ k₁) • (((-1 : ℤˣ) ^ k₂) • x) = ((-1 : 𝕜) ^ (k₁ + k₂)) • x := by
  rw [smul_smul, ← neg_one_pow_add, Units.smul_def]
  rw [← Int.cast_smul_eq_zsmul (R := 𝕜)]
  rcases Nat.even_or_odd (k₁ + k₂) with h | h
  · have hz : ((-1 : ℤˣ) ^ (k₁ + k₂)) = 1 := h.neg_one_pow
    have hz𝕜 : (-1 : 𝕜) ^ (k₁ + k₂) = 1 := h.neg_one_pow
    simp [hz, hz𝕜]
  · have hz : ((-1 : ℤˣ) ^ (k₁ + k₂)) = -1 := h.neg_one_pow
    have hz𝕜 : (-1 : 𝕜) ^ (k₁ + k₂) = -1 := h.neg_one_pow
    simp [hz, hz𝕜]

private theorem uncurryFin_precompR_eq (f : N →L[𝕜] N' →L[𝕜] N'')
    (a : M [⋀^Fin m]→L[𝕜] N) (L : M →L[𝕜] (M [⋀^Fin n]→L[𝕜] N')) :
    uncurryFin ((wedgeProductL f).precompR M a L) =
      (-1 : 𝕜) ^ m • wedgeProduct a (uncurryFin L) f := by
  ext v
  let C : Fin (m + n + 1) ≃ Fin (n + m + 1) := derivFinCast m n
  let P : M →L[𝕜] (M [⋀^Fin (n + m)]→L[𝕜] N'') :=
    (wedgeProductL f.flip).precompL M L a
  let sigmaPerm : Equiv.Perm (Fin (n + m)) :=
    (flipAddCongr m n).trans (Fin.finAddCongr (m := n) (n := m)).symm
  let tau : Equiv.Perm (Fin (m + n + 1)) :=
    ((finCongr (show m + n + 1 = (n + 1) + m by omega)).trans
      (Equiv.Perm.addCasesSwapPerm (n + 1) m)).trans
      (finCongr (show (n + 1) + m = m + n + 1 by omega))
  have hπ : Equiv.Perm.sign sigmaPerm = (-1 : ℤˣ) ^ (m * n) :=
    sign_flipAddCongr_composite m n
  have hflip (k : Fin (m + n + 1)) :
      wedgeProduct a (L (v k)) f =
        (wedgeProduct (L (v k)) a f.flip).domDomCongr (flipAddCongr m n) := by
    exact wedge_flip (m := n) (n := m) (h := a) (g := L (v k)) (f := f.flip)
  have hbridge (k : Fin (m + n + 1)) :
      (k.removeNth v) ∘ (flipAddCongr m n) =
        ((C k).removeNth (v ∘ C.symm)) ∘ sigmaPerm := by
    rw [removeNth_cast m n v k]
    apply congrArg ((k.removeNth v) ∘ ·)
    ext x
    simp [sigmaPerm, flipAddCongr, Fin.finAddCongr, finCongr]
  calc
    uncurryFin ((wedgeProductL f).precompR M a L) v
        = ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            wedgeProduct a (L (v k)) f (k.removeNth v) := by
          rw [uncurryFin_apply]
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
            ContinuousLinearMap.comp_apply, wedge_productL_apply]
    _ = ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            (wedgeProduct (L (v k)) a f.flip).domDomCongr (flipAddCongr m n) (k.removeNth v) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hflip k]
    _ = ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            wedgeProduct (L (v k)) a f.flip ((k.removeNth v) ∘ (flipAddCongr m n)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [ContinuousAlternatingMap.domDomCongr_apply]
    _ = ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            wedgeProduct (L (v k)) a f.flip (((C k).removeNth (v ∘ C.symm)) ∘ sigmaPerm) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hbridge k]
    _ = Equiv.Perm.sign sigmaPerm • ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            wedgeProduct (L (v k)) a f.flip ((C k).removeNth (v ∘ C.symm)) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [smul_comm]
          congr 1
          exact map_perm_sign (wedgeProduct (L (v k)) a f.flip)
            ((C k).removeNth (v ∘ C.symm)) sigmaPerm
    _ = Equiv.Perm.sign sigmaPerm • uncurryFin P (v ∘ C.symm) := by
          congr 1
          simpa [P] using uncurryFin_reindex P v
    _ = Equiv.Perm.sign sigmaPerm •
          (domDomCongr Fin.finAddFlipAssoc (wedgeProduct (uncurryFin L) a f.flip))
            (v ∘ C.symm) := by
          congr 1
          dsimp only [P]
          exact DFunLike.congr_fun
            (uncurryFin_wedge_productL_precompL_eq_domDomCongr f.flip L a) (v ∘ C.symm)
    _ = Equiv.Perm.sign sigmaPerm •
          wedgeProduct (uncurryFin L) a f.flip ((v ∘ C.symm) ∘ Fin.finAddFlipAssoc) := by
          rw [ContinuousAlternatingMap.domDomCongr_apply]
    _ = Equiv.Perm.sign sigmaPerm •
          (wedgeProduct a (uncurryFin L) f).domDomCongr (flipAddCongr (n + 1) m)
            ((v ∘ C.symm) ∘ Fin.finAddFlipAssoc) := by
          congr 1
          simpa using DFunLike.congr_fun
            (wedge_flip (m := m) (n := n + 1) (h := uncurryFin L) (g := a) (f := f))
            ((v ∘ C.symm) ∘ Fin.finAddFlipAssoc (m := n) (p := 1) (n := m))
    _ = Equiv.Perm.sign sigmaPerm •
          wedgeProduct a (uncurryFin L) f
            (((v ∘ C.symm) ∘ Fin.finAddFlipAssoc (m := n) (p := 1) (n := m)) ∘
              (flipAddCongr (n + 1) m)) := by
          rw [ContinuousAlternatingMap.domDomCongr_apply]
    _ = Equiv.Perm.sign sigmaPerm •
          wedgeProduct a (uncurryFin L) f (v ∘ tau) := by
          congr 1
          congr 1
          funext i
          dsimp [tau]
          exact congrArg v (flipAddCongr_composite_eq_addCasesSwapPerm_apply' m n i)
    _ = Equiv.Perm.sign sigmaPerm •
          (Equiv.Perm.sign tau • wedgeProduct a (uncurryFin L) f v) := by
          exact congrArg (fun z => Equiv.Perm.sign sigmaPerm • z)
            (map_perm_sign (wedgeProduct a (uncurryFin L) f) v tau)
    _ = (-1 : 𝕜) ^ m • wedgeProduct a (uncurryFin L) f v := by
          rw [hπ, show Equiv.Perm.sign tau = (-1 : ℤˣ) ^ ((n + 1) * m) from by
            simpa only [tau] using addCasesSwapPerm_cast_sign m n]
          have hsum : m * n + (n + 1) * m = 2 * (m * n) + m := by nlinarith
          rw [show ((-1 : ℤˣ) ^ (m * n)) • (((-1 : ℤˣ) ^ ((n + 1) * m)) •
              (wedgeProduct a (uncurryFin L) f v)) = ((-1 : 𝕜) ^ m) •
              (wedgeProduct a (uncurryFin L) f v) from by
            rw [units_neg_pow_smul (𝕜 := 𝕜) (m * n) ((n + 1) * m)]
            rw [hsum, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]]

end ContinuousAlternatingMap

namespace DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n k l : ℕ} {x : E}

private theorem extDeriv_eq_uncurryFin (eta : E → E [⋀^Fin n]→L[ℝ] F)
    (hω : DifferentiableAt ℝ eta x) :
    extDeriv eta x = ContinuousAlternatingMap.uncurryFin (fderiv ℝ eta x) := by
  ext v
  rw [extDeriv_apply hω, ContinuousAlternatingMap.uncurryFin_apply]
  refine Finset.sum_congr rfl ?_
  intro i hi
  congr 1
  let Eval : (E [⋀^Fin n]→L[ℝ] F) →L[ℝ] F :=
    { toFun := fun L => L (i.removeNth v)
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }
  have hEval : fderiv ℝ (fun L : E [⋀^Fin n]→L[ℝ] F => L (i.removeNth v)) (eta x) = Eval := by
    simpa [Eval] using (Eval.fderiv : fderiv ℝ (⇑Eval) (eta x) = Eval)
  have hcomp : HasFDerivAt (fun y : E => (eta y) (i.removeNth v))
      (Eval.comp (fderiv ℝ eta x)) x := by
    have hg : HasFDerivAt (fun L : E [⋀^Fin n]→L[ℝ] F => L (i.removeNth v)) Eval (eta x) := by
      simpa [Eval] using Eval.hasFDerivAt
    exact HasFDerivAt.comp x hg hω.hasFDerivAt
  have hmain : fderiv ℝ (fun y : E => (eta y) (i.removeNth v)) x =
      Eval.comp (fderiv ℝ eta x) := by
    simpa using hcomp.fderiv
  rw [hmain]
  rfl

private theorem fderiv_wedge_apply (a : E → E [⋀^Fin k]→L[ℝ] ℝ) (b : E → E [⋀^Fin l]→L[ℝ] ℝ)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    fderiv ℝ (fun y : E => a y ∧[ℝ] b y) x =
      (wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompR E (a x) (fderiv ℝ b x) +
        (wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompL E (fderiv ℝ a x) (b x) := by
  let W : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ]
      (E [⋀^Fin (k + l)]→L[ℝ] ℝ) := wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)
  have hf : HasFDerivAt (fun y : E => (W (a y)) (b y))
      (W.precompR E (a x) (fderiv ℝ b x) +
        W.precompL E (fderiv ℝ a x) (b x)) x :=
    W.hasFDerivAt_of_bilinear ha.hasFDerivAt hb.hasFDerivAt
  simpa [W] using hf.fderiv

theorem extDeriv_wedge (a : E → E [⋀^Fin k]→L[ℝ] ℝ) (b : E → E [⋀^Fin l]→L[ℝ] ℝ)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    (fun x => domDomCongr (finCongr (Nat.add_assoc k l 1))
      (extDeriv (fun y => a y ∧[ℝ] b y) x)) =
      (fun x => domDomCongr Fin.finAddFlipAssoc ((extDeriv a x) ∧[ℝ] (b x)) +
        (-1 : ℝ) ^ k • (a x ∧[ℝ] (extDeriv b x))) := by
  funext x
  let W : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ]
      (E [⋀^Fin (k + l)]→L[ℝ] ℝ) := wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)
  have hda : DifferentiableAt ℝ a x := ha.differentiableAt
  have hdb : DifferentiableAt ℝ b x := hb.differentiableAt
  have hdab : DifferentiableAt ℝ (fun y : E => a y ∧[ℝ] b y) x := by
    simpa [W] using
      (W.hasFDerivAt_of_bilinear hda.hasFDerivAt hdb.hasFDerivAt).differentiableAt
  rw [extDeriv_eq_uncurryFin (fun y : E => a y ∧[ℝ] b y) hdab]
  rw [fderiv_wedge_apply a b hda hdb]
  rw [ContinuousAlternatingMap.uncurryFin_add]
  rw [ContinuousAlternatingMap.uncurryFin_precompR_eq]
  rw [ContinuousAlternatingMap.uncurryFin_wedge_productL_precompL_eq_domDomCongr]
  rw [← extDeriv_eq_uncurryFin a hda, ← extDeriv_eq_uncurryFin b hdb]
  exact add_comm _ _

theorem extDeriv_wedge_at (a : E → E [⋀^Fin k]→L[ℝ] ℝ) (b : E → E [⋀^Fin l]→L[ℝ] ℝ)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    domDomCongr (finCongr (Nat.add_assoc k l 1))
      (extDeriv (fun y : E => a y ∧[ℝ] b y) x) =
      domDomCongr Fin.finAddFlipAssoc ((extDeriv a x) ∧[ℝ] (b x)) +
        (-1 : ℝ) ^ k • (a x ∧[ℝ] (extDeriv b x)) := by
  let W : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ]
      (E [⋀^Fin (k + l)]→L[ℝ] ℝ) := wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)
  have hda : DifferentiableAt ℝ a x := ha
  have hdb : DifferentiableAt ℝ b x := hb
  have hdab : DifferentiableAt ℝ (fun y : E => a y ∧[ℝ] b y) x := by
    simpa [W] using
      (W.hasFDerivAt_of_bilinear hda.hasFDerivAt hdb.hasFDerivAt).differentiableAt
  rw [extDeriv_eq_uncurryFin (fun y : E => a y ∧[ℝ] b y) hdab]
  rw [fderiv_wedge_apply a b hda hdb]
  rw [ContinuousAlternatingMap.uncurryFin_add]
  rw [ContinuousAlternatingMap.uncurryFin_precompR_eq]
  rw [ContinuousAlternatingMap.uncurryFin_wedge_productL_precompL_eq_domDomCongr]
  rw [← extDeriv_eq_uncurryFin a hda, ← extDeriv_eq_uncurryFin b hdb]
  exact add_comm _ _

end DifferentialForm

namespace DifferentialGeometry
namespace DifferentialForm

attribute [local instance] seminormedAddCommGroupTangentSpace
attribute [local instance] normedAddCommGroupTangentSpace
attribute [local instance] normedSpaceTangentSpace

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
  {k l : ℕ}

private def trivialFiberEquiv (x : M) : Bundle.Trivial M ℝ x ≃L[ℝ] ℝ := by
  change ℝ ≃L[ℝ] ℝ
  exact ContinuousLinearEquiv.refl ℝ ℝ

private abbrev ScalarForm (m : ℕ) (x : M) :=
  letI := normedAddCommGroupTangentSpace (EM := EM) (HM := HM) IM M x
  letI := normedSpaceTangentSpace (EM := EM) (HM := HM) IM M x
  TangentSpace IM x [⋀^Fin m]→L[ℝ] ℝ

private def scalarize (m : ℕ) (x : M)
    (L : Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x) : ScalarForm (IM := IM) (M := M) m x := by
  letI := normedAddCommGroupTangentSpace (EM := EM) (HM := HM) IM M x
  letI := normedSpaceTangentSpace (EM := EM) (HM := HM) IM M x
  exact (trivialFiberEquiv x).toContinuousLinearMap.compContinuousAlternatingMap L

private def modelize (m : ℕ) (x : M)
    (L : Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x) : EM [⋀^Fin m]→L[ℝ] ℝ :=
  (scalarize m x L).compContinuousLinearMap
    ((trivializationAt EM (TangentSpace IM) x).symmL ℝ x)

private lemma localRepresentation_eq (m : ℕ) (x : M)
    (L : Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x) :
    (trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x ⟨x, L⟩).2 =
      modelize m x L := by
  rw [continuousAlternatingMap_trivializationAt_apply (m := m) (IM := IM) (M := M)
    (x₀ := x) (x := x) (L := L)]
  ext v
  rfl

private lemma scalarize_wedge {m n : ℕ} (α : DifferentialForm IM M m)
    (β : DifferentialForm IM M n) (x : M) :
    scalarize (m + n) x ((α ∧ β) x) =
      scalarize m x (α x) ∧[ℝ] scalarize n x (β x) := by
  ext v
  rfl

private lemma scalarize_reindex {m n : ℕ} (σ : Fin m ≃ Fin n)
    (α : DifferentialForm IM M m) (x : M) :
    scalarize n x (reindex σ α x) =
      ContinuousAlternatingMap.domDomCongr σ (scalarize m x (α x)) := by
  ext v
  rfl

omit [IsManifold IM ⊤ M] in
private lemma scalarize_add (m : ℕ) (x : M)
    (L K : Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x) :
    scalarize m x (L + K) = scalarize m x L + scalarize m x K := by
  ext v
  rfl

omit [IsManifold IM ⊤ M] in
private lemma scalarize_smul (m : ℕ) (x : M) (c : ℝ)
    (L : Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x) :
    scalarize m x (c • L) = c • scalarize m x L := by
  ext v
  rfl

private lemma modelize_wedge {m n : ℕ} (α : DifferentialForm IM M m)
    (β : DifferentialForm IM M n) (x : M) :
    modelize (m + n) x ((α ∧ β) x) =
      modelize m x (α x) ∧[ℝ] modelize n x (β x) := by
  unfold modelize
  rw [scalarize_wedge]
  exact wedge_product_compContinuousLinearMap (E := TangentSpace IM x) (E' := EM)
    (g := scalarize m x (α x)) (h := scalarize n x (β x))
    (A := (trivializationAt EM (TangentSpace IM) x).symmL ℝ x)

private lemma modelize_reindex {m n : ℕ} (σ : Fin m ≃ Fin n)
    (α : DifferentialForm IM M m) (x : M) :
    modelize n x (reindex σ α x) =
      ContinuousAlternatingMap.domDomCongr σ (modelize m x (α x)) := by
  unfold modelize
  rw [scalarize_reindex]
  exact domDomCongr_compContinuousLinearMap (E := TangentSpace IM x) (E' := EM)
    (σ := σ) (L := scalarize m x (α x))
    (A := (trivializationAt EM (TangentSpace IM) x).symmL ℝ x)

private lemma modelize_add (m : ℕ) (x : M)
    (L K : Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x) :
    modelize m x (L + K) = modelize m x L + modelize m x K := by
  unfold modelize
  rw [scalarize_add]
  exact ContinuousAlternatingMap.compContinuousLinearMap_add _ _ _

private lemma modelize_smul (m : ℕ) (x : M) (c : ℝ)
    (L : Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x) :
    modelize m x (c • L) = c • modelize m x L := by
  unfold modelize
  rw [scalarize_smul]
  exact ContinuousAlternatingMap.compContinuousLinearMap_smul _ _ _

private lemma dalpha_eq_extDeriv [BoundarylessManifold IM M] (α : DifferentialForm IM M k)
    (x : M) :
    (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨x, exteriorDerivativeAt α x⟩).2 =
      extDeriv (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, α ((extChartAt IM x).symm y)⟩).2)
        ((extChartAt IM x) x) := by
  rw [exteriorDerivativeAt]
  exact exteriorDerivative_localRepresentation (IM := IM) (M := M) (α := α) (x₀ := x) (x := x)
    (by simp) (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x))

private lemma repα_eq (α : DifferentialForm IM M k) (x : M) :
    (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, α ((extChartAt IM x).symm y)⟩).2)
      ((extChartAt IM x) x) =
        modelize k x (α x) := by
  change (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x
      ⟨(extChartAt IM x).symm ((extChartAt IM x) x),
        α ((extChartAt IM x).symm ((extChartAt IM x) x))⟩).2 =
      modelize k x (α x)
  rw [(extChartAt IM x).left_inv (by simp)]
  exact localRepresentation_eq k x (α x)

private lemma repβ_eq (β : DifferentialForm IM M l) (x : M) :
    (fun y : EM => (trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, β ((extChartAt IM x).symm y)⟩).2)
      ((extChartAt IM x) x) =
        modelize l x (β x) := by
  change (trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x
      ⟨(extChartAt IM x).symm ((extChartAt IM x) x),
        β ((extChartAt IM x).symm ((extChartAt IM x) x))⟩).2 =
      modelize l x (β x)
  rw [(extChartAt IM x).left_inv (by simp)]
  exact localRepresentation_eq l x (β x)

theorem exteriorDerivative_wedge [BoundarylessManifold IM M]
    (α : DifferentialForm IM M k) (β : DifferentialForm IM M l) :
    reindex (finCongr (Nat.add_assoc k l 1)) (exteriorDerivative (α ∧ β)) =
      reindex (Fin.finAddFlipAssoc (m := k) (p := 1) (n := l)) (exteriorDerivative α ∧ β) +
        (-1 : ℝ) ^ k • (α ∧ exteriorDerivative β) := by
  apply ContMDiffSection.ext
  intro x
  change ContinuousAlternatingMap.domDomCongr (finCongr (Nat.add_assoc k l 1))
      (exteriorDerivativeAt (α ∧ β) x) =
      reindex (Fin.finAddFlipAssoc (m := k) (p := 1) (n := l)) (exteriorDerivative α ∧ β) x +
        (-1 : ℝ) ^ k • (α ∧ exteriorDerivative β) x
  let c₀ := extChartAt IM x
  let eKL1 := trivializationAt (EM [⋀^Fin (k + (l + 1))]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin (k + (l + 1))) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ)) x
  let repα : EM → EM [⋀^Fin k]→L[ℝ] ℝ := fun y =>
    (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, α ((extChartAt IM x).symm y)⟩).2
  let repβ : EM → EM [⋀^Fin l]→L[ℝ] ℝ := fun y =>
    (trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, β ((extChartAt IM x).symm y)⟩).2
  let _ : VectorBundle ℝ (EM [⋀^Fin (k + (l + 1))]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin (k + (l + 1))) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) := inferInstance
  have : eKL1.IsLinear ℝ := trivialization_linear (R := ℝ) (e := eKL1)
  have hbase : x ∈ eKL1.baseSet := mem_baseSet_trivializationAt
    (EM [⋀^Fin (k + (l + 1))]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin (k + (l + 1))) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ)) x
  have hdWedge : modelize (k + l + 1) x (exteriorDerivativeAt (α ∧ β) x) =
      extDeriv (fun y : EM => repα y ∧[ℝ] repβ y) (c₀ x) := by
    rw [← localRepresentation_eq (k + l + 1) x (exteriorDerivativeAt (α ∧ β) x)]
    rw [exteriorDerivativeAt]
    dsimp [c₀, repα, repβ]
    rw [exteriorDerivative_localRepresentation (IM := IM) (M := M) (α := α ∧ β) (x₀ := x)
      (x := x) (by simp) (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x))]
    congr 1
    funext y
    change (trivializationAt (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y,
            α ((extChartAt IM x).symm y) ∧[ℝ] β ((extChartAt IM x).symm y)⟩).2 =
      (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, α ((extChartAt IM x).symm y)⟩).2 ∧[ℝ]
        (trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, β ((extChartAt IM x).symm y)⟩).2
    rw [continuousAlternatingMap_trivializationAt_apply (m := k + l) (IM := IM) (M := M)
      (x₀ := x) (x := (extChartAt IM x).symm y)
        (L := α ((extChartAt IM x).symm y) ∧[ℝ] β ((extChartAt IM x).symm y)),
      continuousAlternatingMap_trivializationAt_apply (m := k) (IM := IM) (M := M) (x₀ := x)
        (x := (extChartAt IM x).symm y)
        (L := α ((extChartAt IM x).symm y)),
      continuousAlternatingMap_trivializationAt_apply (m := l) (IM := IM) (M := M) (x₀ := x)
        (x := (extChartAt IM x).symm y)
        (L := β ((extChartAt IM x).symm y))]
    exact wedge_product_compContinuousLinearMap (E := TangentSpace IM ((extChartAt IM x).symm y))
      (E' := EM) (g := α ((extChartAt IM x).symm y)) (h := β ((extChartAt IM x).symm y))
      (A := (trivializationAt EM (TangentSpace IM) x).symmL ℝ ((extChartAt IM x).symm y))
  have hLHS :
      (eKL1 ⟨x, reindex (finCongr (Nat.add_assoc k l 1))
        (exteriorDerivative (α ∧ β)) x⟩).2 =
        ContinuousAlternatingMap.domDomCongr (finCongr (Nat.add_assoc k l 1))
          (extDeriv (fun y : EM => repα y ∧[ℝ] repβ y) (c₀ x)) := by
    rw [show (eKL1 ⟨x, reindex (finCongr (Nat.add_assoc k l 1))
        (exteriorDerivative (α ∧ β)) x⟩).2 =
        modelize (k + (l + 1)) x
          (reindex (finCongr (Nat.add_assoc k l 1))
            (exteriorDerivative (α ∧ β)) x) from by
      simpa [eKL1] using localRepresentation_eq (k + (l + 1)) x
        (reindex (finCongr (Nat.add_assoc k l 1))
          (exteriorDerivative (α ∧ β)) x)]
    rw [modelize_reindex]
    change ContinuousAlternatingMap.domDomCongr (finCongr (Nat.add_assoc k l 1))
      (modelize (k + l + 1) x (exteriorDerivativeAt (α ∧ β) x)) = _
    rw [hdWedge]
  have hRHS :
      (eKL1 ⟨x, reindex (Fin.finAddFlipAssoc (m := k) (p := 1) (n := l))
        (exteriorDerivative α ∧ β) x + (-1 : ℝ) ^ k •
          (α ∧ exteriorDerivative β) x⟩).2 =
        ContinuousAlternatingMap.domDomCongr
          (Fin.finAddFlipAssoc (m := k) (p := 1) (n := l))
            (extDeriv repα (c₀ x) ∧[ℝ] repβ (c₀ x)) +
          (-1 : ℝ) ^ k • (repα (c₀ x) ∧[ℝ] extDeriv repβ (c₀ x)) := by
    have hdα : modelize (k + 1) x (exteriorDerivative α x) = extDeriv repα (c₀ x) := by
      change modelize (k + 1) x (exteriorDerivativeAt α x) = extDeriv repα (c₀ x)
      rw [← localRepresentation_eq (k + 1) x (exteriorDerivativeAt α x)]
      simpa [c₀, repα] using dalpha_eq_extDeriv α x
    have hdβ : modelize (l + 1) x (exteriorDerivative β x) = extDeriv repβ (c₀ x) := by
      change modelize (l + 1) x (exteriorDerivativeAt β x) = extDeriv repβ (c₀ x)
      rw [← localRepresentation_eq (l + 1) x (exteriorDerivativeAt β x)]
      simpa [c₀, repβ] using dalpha_eq_extDeriv β x
    have hα : modelize k x (α x) = repα (c₀ x) := by
      simpa [c₀, repα] using (repα_eq α x).symm
    have hβ : modelize l x (β x) = repβ (c₀ x) := by
      simpa [c₀, repβ] using (repβ_eq β x).symm
    rw [show (eKL1 ⟨x, reindex (Fin.finAddFlipAssoc (m := k) (p := 1) (n := l))
        (exteriorDerivative α ∧ β) x + (-1 : ℝ) ^ k •
          (α ∧ exteriorDerivative β) x⟩).2 =
        modelize (k + (l + 1)) x
          (reindex (Fin.finAddFlipAssoc (m := k) (p := 1) (n := l))
            (exteriorDerivative α ∧ β) x + (-1 : ℝ) ^ k •
              (α ∧ exteriorDerivative β) x) from by
      simpa [eKL1] using localRepresentation_eq (k + (l + 1)) x
        (reindex (Fin.finAddFlipAssoc (m := k) (p := 1) (n := l))
          (exteriorDerivative α ∧ β) x + (-1 : ℝ) ^ k •
            (α ∧ exteriorDerivative β) x)]
    rw [modelize_add, modelize_smul, modelize_reindex,
      modelize_wedge (α := exteriorDerivative α) (β := β)]
    rw [modelize_wedge (α := α) (β := exteriorDerivative β)]
    rw [hdα, hdβ, hα, hβ]
  have hm : ContinuousAlternatingMap.domDomCongr (finCongr (Nat.add_assoc k l 1))
      (extDeriv (fun y : EM => repα y ∧[ℝ] repβ y) (c₀ x)) =
      ContinuousAlternatingMap.domDomCongr (Fin.finAddFlipAssoc (m := k) (p := 1) (n := l))
          (extDeriv repα (c₀ x) ∧[ℝ] repβ (c₀ x)) +
        (-1 : ℝ) ^ k • (repα (c₀ x) ∧[ℝ] extDeriv repβ (c₀ x)) := by
    have hmem : c₀ x ∈ interior ((extChartAt IM x).target) :=
      (ModelWithCorners.isInteriorPoint_iff (I := IM)).1
        (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x))
    have hcontα : DifferentiableAt ℝ repα (c₀ x) := by
      exact ((localRep_contDiffOn α x).contDiffAt
        (mem_interior_iff_mem_nhds.mp hmem)).differentiableAt
        (by simp)
    have hcontβ : DifferentiableAt ℝ repβ (c₀ x) := by
      exact ((localRep_contDiffOn β x).contDiffAt
        (mem_interior_iff_mem_nhds.mp hmem)).differentiableAt
        (by simp)
    simpa [c₀, repα, repβ] using
      (DifferentialForm.extDeriv_wedge_at (a := repα) (b := repβ) hcontα hcontβ)
  have heq : reindex (finCongr (Nat.add_assoc k l 1))
      (exteriorDerivative (α ∧ β)) x =
      reindex (Fin.finAddFlipAssoc (m := k) (p := 1) (n := l)) (exteriorDerivative α ∧ β) x +
        (-1 : ℝ) ^ k • (α ∧ exteriorDerivative β) x := by
    apply (eKL1.continuousLinearEquivAt ℝ x hbase).injective
    change (eKL1 ⟨x, reindex (finCongr (Nat.add_assoc k l 1))
        (exteriorDerivative (α ∧ β)) x⟩).2 =
      (eKL1 ⟨x, reindex (Fin.finAddFlipAssoc (m := k) (p := 1) (n := l))
        (exteriorDerivative α ∧ β) x + (-1 : ℝ) ^ k •
          (α ∧ exteriorDerivative β) x⟩).2
    rw [hLHS, hRHS, hm]
  exact heq

end DifferentialForm
end DifferentialGeometry

end
