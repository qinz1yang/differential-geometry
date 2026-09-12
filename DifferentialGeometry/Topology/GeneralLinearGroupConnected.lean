import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open Matrix

namespace DifferentialGeometry.Topology

variable {n : ℕ}

private theorem continuous_single (i j : Fin n) :
    Continuous fun x : ℝ => Matrix.single i j x := by
  apply continuous_matrix
  intro k l
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    have hfun : (fun x : ℝ => Matrix.single i j x i j) = fun x : ℝ => x := by
      funext x
      rw [Matrix.single_apply]
      simp only [and_self, if_true]
    rw [hfun]
    exact continuous_id
  · have hfun : (fun x : ℝ => Matrix.single i j x k l) = fun _ : ℝ => 0 := by
      funext x
      rw [Matrix.single_apply, if_neg h]
    rw [hfun]
    exact continuous_const

private def scaledTransvectionProduct :
    List (Matrix.TransvectionStruct (Fin n) ℝ) → ℝ → Matrix (Fin n) (Fin n) ℝ
  | [], _ => 1
  | s :: L, t => Matrix.transvection s.i s.j (t * s.c) * scaledTransvectionProduct L t

private theorem continuous_scaledTransvectionProduct
    (L : List (Matrix.TransvectionStruct (Fin n) ℝ)) :
    Continuous fun t : ℝ => scaledTransvectionProduct L t := by
  induction L with
  | nil =>
      simp only [scaledTransvectionProduct]
      exact continuous_const
  | cons s L ih =>
      simp only [scaledTransvectionProduct]
      have h : Continuous fun t : ℝ => Matrix.transvection s.i s.j (t * s.c) := by
        have hsingle : Continuous fun t : ℝ => Matrix.single s.i s.j (t * s.c) :=
          (continuous_single s.i s.j).comp (continuous_id.mul continuous_const)
        exact (continuous_const.add hsingle).congr fun t => rfl
      exact h.matrix_mul ih

private theorem scaledTransvectionProduct_zero
    (L : List (Matrix.TransvectionStruct (Fin n) ℝ)) :
    scaledTransvectionProduct L 0 = 1 := by
  induction L with
  | nil => simp only [scaledTransvectionProduct]
  | cons s L ih =>
      simp only [scaledTransvectionProduct, zero_mul, Matrix.transvection_zero, ih,
        Matrix.one_mul]

private theorem scaledTransvectionProduct_one
    (L : List (Matrix.TransvectionStruct (Fin n) ℝ)) :
    scaledTransvectionProduct L 1 = (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp only [scaledTransvectionProduct, List.map_nil, List.prod_nil]
  | cons s L ih =>
      simp only [scaledTransvectionProduct, one_mul, ih,
        Matrix.TransvectionStruct.toMatrix, List.map_cons, List.prod_cons]

private theorem scaledTransvectionProduct_det
    (L : List (Matrix.TransvectionStruct (Fin n) ℝ)) (t : ℝ) :
    (scaledTransvectionProduct L t).det = 1 := by
  induction L with
  | nil => simp only [scaledTransvectionProduct, Matrix.det_one]
  | cons s L ih =>
      simp only [scaledTransvectionProduct, Matrix.det_mul,
        Matrix.det_transvection_of_ne s.i s.j s.hij, ih, one_mul]

private def listProdPath (L : List (Matrix.TransvectionStruct (Fin n) ℝ)) :
    Path (1 : Matrix (Fin n) (Fin n) ℝ) (L.map Matrix.TransvectionStruct.toMatrix).prod where
  toFun t := scaledTransvectionProduct L (t : ℝ)
  continuous_toFun := (continuous_scaledTransvectionProduct L).comp continuous_subtype_val
  source' := scaledTransvectionProduct_zero L
  target' := scaledTransvectionProduct_one L

private def negFlipMatrix (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun k => if k = i ∨ k = j then -1 else 1

private theorem negFlipMatrix_eq_sq (i j : Fin n) (hij : i ≠ j) :
    (Matrix.transvection i j (-1) * Matrix.transvection j i 1 * Matrix.transvection i j (-1)) *
    (Matrix.transvection i j (-1) * Matrix.transvection j i 1 * Matrix.transvection i j (-1)) =
    negFlipMatrix i j := by
  simp only [negFlipMatrix, Matrix.transvection]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, ne_eq, hij, hij.symm,
    not_false_eq_true, add_zero]
  ext k l
  by_cases hjk : j = k <;> by_cases hik : i = k <;> by_cases hil : i = l <;> by_cases hjl : j = l <;>
    by_cases hkl : k = l <;>
    simp_all [Matrix.add_apply, eq_comm]

private def negFlipProduct (i j : Fin n) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.transvection i j (t * (-1)) * Matrix.transvection j i (t * 1) *
      Matrix.transvection i j (t * (-1))) *
    (Matrix.transvection i j (t * (-1)) * Matrix.transvection j i (t * 1) *
      Matrix.transvection i j (t * (-1)))

private theorem continuous_negFlipProduct (i j : Fin n) :
    Continuous fun t : ℝ => negFlipProduct i j t := by
  have h1 : Continuous fun t : ℝ => Matrix.transvection i j (t * (-1)) := by
    have hsingle : Continuous fun t : ℝ => Matrix.single i j (t * (-1)) :=
      (continuous_single i j).comp (continuous_id.mul continuous_const)
    exact (continuous_const.add hsingle).congr fun t => rfl
  have h2 : Continuous fun t : ℝ => Matrix.transvection j i (t * 1) := by
    have hsingle : Continuous fun t : ℝ => Matrix.single j i (t * 1) :=
      (continuous_single j i).comp (continuous_id.mul continuous_const)
    exact (continuous_const.add hsingle).congr fun t => rfl
  exact ((h1.matrix_mul h2).matrix_mul h1).matrix_mul ((h1.matrix_mul h2).matrix_mul h1)

private theorem negFlipProduct_zero (i j : Fin n) : negFlipProduct i j 0 = 1 := by
  simp only [negFlipProduct, zero_mul, Matrix.transvection_zero, Matrix.mul_one]

private theorem negFlipProduct_one (i j : Fin n) (hij : i ≠ j) :
    negFlipProduct i j 1 = negFlipMatrix i j := by
  simp only [negFlipProduct, one_mul, negFlipMatrix_eq_sq i j hij]

private theorem negFlipProduct_det (i j : Fin n) (hij : i ≠ j) (t : ℝ) :
    (negFlipProduct i j t).det ≠ 0 := by
  have h : (negFlipProduct i j t).det = 1 := by
    simp only [negFlipProduct, Matrix.det_mul, Matrix.det_transvection_of_ne i j hij,
      Matrix.det_transvection_of_ne j i hij.symm, one_mul]
  rw [h]
  norm_num

private def negFlipPath (i j : Fin n) (hij : i ≠ j) :
    Path (1 : Matrix (Fin n) (Fin n) ℝ) (negFlipMatrix i j) where
  toFun t := negFlipProduct i j (t : ℝ)
  continuous_toFun := (continuous_negFlipProduct i j).comp continuous_subtype_val
  source' := negFlipProduct_zero i j
  target' := negFlipProduct_one i j hij

private theorem diagonal_mul_negFlipMatrix (D : Fin n → ℝ) (i j : Fin n) :
    Matrix.diagonal D * negFlipMatrix i j =
      Matrix.diagonal (fun k => if k = i ∨ k = j then -D k else D k) := by
  ext k l
  rw [Matrix.diagonal_mul]
  by_cases hkl : k = l
  · subst hkl
    rw [negFlipMatrix, Matrix.diagonal_apply, if_pos rfl, Matrix.diagonal_apply, if_pos rfl]
    by_cases h : k = i ∨ k = j
    · simp only [if_pos h, mul_neg, mul_one]
    · simp only [if_neg h, mul_one]
  · rw [negFlipMatrix, Matrix.diagonal_apply, Matrix.diagonal_apply, if_neg hkl, if_neg hkl,
      mul_zero]

private theorem det_negFlipMatrix (i j : Fin n) (hij : i ≠ j) :
    (negFlipMatrix i j).det = 1 := by
  rw [← negFlipProduct_one i j hij, negFlipProduct]
  simp only [Matrix.det_mul, Matrix.det_transvection_of_ne i j hij,
    Matrix.det_transvection_of_ne j i hij.symm, one_mul]

private theorem exists_path_diagonal_of_prod_pos (D : Fin n → ℝ) (hD : ∀ i, D i ≠ 0)
    (hpos : 0 < ∏ i, D i) :
    ∃ γ : Path (1 : Matrix (Fin n) (Fin n) ℝ) (Matrix.diagonal D), ∀ t, (γ t).det ≠ 0 := by
  suffices H : ∀ m : ℕ, ∀ E : Fin n → ℝ, (∀ i, E i ≠ 0) → 0 < ∏ i, E i →
      (Finset.univ.filter (fun i => E i < 0)).card = m →
      ∃ γ : Path (1 : Matrix (Fin n) (Fin n) ℝ) (Matrix.diagonal E), ∀ t, (γ t).det ≠ 0 from
    H _ D hD hpos rfl
  intro m
  refine Nat.strong_induction_on m fun m ih E hE hEpos hcard => ?_
  by_cases hneg : ∃ i, E i < 0
  · obtain ⟨a, ha⟩ := hneg
    have hmem : a ∈ Finset.univ.filter (fun i => E i < 0) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ha]
    have hsecond : ∃ b, E b < 0 ∧ b ≠ a := by
      by_contra hcon
      have hcon' : ∀ b, b ≠ a → 0 ≤ E b := by
        intro b hba
        by_contra hb
        exact hcon ⟨b, lt_of_not_ge hb, hba⟩
      have hsplit : ∏ i, E i = E a * ∏ i ∈ (Finset.univ : Finset (Fin n)) \ {a}, E i :=
        Finset.prod_eq_mul_prod_sdiff_singleton a E (fun h => absurd (Finset.mem_univ a) h)
      rw [hsplit] at hEpos
      have hrest : 0 < ∏ i ∈ (Finset.univ : Finset (Fin n)) \ {a}, E i :=
        Finset.prod_pos fun i hi => by
          have hia : i ≠ a := fun h =>
            (Finset.mem_sdiff.mp hi).2 (Finset.mem_singleton.mpr h)
          exact lt_of_le_of_ne (hcon' i hia) (Ne.symm (hE i))
      have hnegprod : E a * ∏ i ∈ (Finset.univ : Finset (Fin n)) \ {a}, E i < 0 :=
        mul_neg_of_neg_of_pos ha hrest
      linarith
    obtain ⟨b, hb, hba⟩ := hsecond
    have hba' : a ≠ b := fun h => hba h.symm
    have hdiag : Matrix.diagonal E * negFlipMatrix a b =
        Matrix.diagonal (fun i => if i = a ∨ i = b then -E i else E i) :=
      diagonal_mul_negFlipMatrix E a b
    have hflip : Matrix.diagonal E =
        Matrix.diagonal (fun i => if i = a ∨ i = b then -E i else E i) * negFlipMatrix a b := by
      rw [diagonal_mul_negFlipMatrix]
      congr 1
      funext i
      by_cases h : i = a ∨ i = b
      · rw [if_pos h, if_pos h, neg_neg]
      · rw [if_neg h, if_neg h]
    have hE' : ∀ i, (fun i => if i = a ∨ i = b then -E i else E i) i ≠ 0 := by
      intro i
      by_cases h : i = a ∨ i = b
      · simp only [if_pos h, neg_ne_zero]
        exact hE i
      · simp only [if_neg h]
        exact hE i
    have hcard' : (Finset.univ.filter
        (fun i => (fun i => if i = a ∨ i = b then -E i else E i) i < 0)).card < m := by
      have hsub : Finset.univ.filter
          (fun i => (fun i => if i = a ∨ i = b then -E i else E i) i < 0) ⊆
          (Finset.univ.filter (fun i => E i < 0)).erase a := by
        intro i hi
        have hfl : (if i = a ∨ i = b then -E i else E i) < 0 := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
        have hne : i ≠ a := by
          intro hia
          rw [hia, if_pos (Or.inl rfl)] at hfl
          exact absurd hfl (not_lt.mpr (by linarith))
        refine Finset.mem_erase.mpr ⟨hne, ?_⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
        by_cases h : i = a ∨ i = b
        · obtain hia | hib := h
          · exact absurd hia hne
          · rw [hib, if_pos (Or.inr rfl)] at hfl
            linarith
        · rw [if_neg h] at hfl
          exact hfl
      calc (Finset.univ.filter
            (fun i => (fun i => if i = a ∨ i = b then -E i else E i) i < 0)).card
          ≤ ((Finset.univ.filter (fun i => E i < 0)).erase a).card := Finset.card_le_card hsub
        _ = (Finset.univ.filter (fun i => E i < 0)).card - 1 := Finset.card_erase_of_mem hmem
        _ < m := by
          have hm : 0 < m := by
            rw [← hcard]
            exact Finset.card_pos.mpr ⟨a, hmem⟩
          omega
    have hE'pos : 0 < ∏ i, (fun i => if i = a ∨ i = b then -E i else E i) i := by
      have hdet : (∏ i, (fun i => if i = a ∨ i = b then -E i else E i) i) =
          (∏ i, E i) * 1 := by
        rw [← Matrix.det_diagonal, ← hdiag, Matrix.det_mul, Matrix.det_diagonal,
          det_negFlipMatrix a b hba']
      rw [hdet, mul_one]
      exact hEpos
    obtain ⟨γ, hγ⟩ := ih _ hcard' _ hE' hE'pos rfl
    have hsrc : (fun t : unitInterval => γ t * negFlipPath a b hba' t) 0 = 1 := by
      have h1 : γ 0 = 1 := γ.source'
      have h2 : (negFlipPath a b hba') 0 = 1 := (negFlipPath a b hba').source'
      simp only []
      rw [h1, h2, Matrix.one_mul]
    have htgt : (fun t : unitInterval => γ t * negFlipPath a b hba' t) 1 = Matrix.diagonal E := by
      have h1 : γ 1 = Matrix.diagonal (fun i => if i = a ∨ i = b then -E i else E i) :=
        γ.target'
      have h2 : (negFlipPath a b hba') 1 = negFlipMatrix a b := (negFlipPath a b hba').target'
      simp only []
      rw [h1, h2, ← hflip]
    have hdetfun : ∀ t : unitInterval,
        ((fun t : unitInterval => γ t * negFlipPath a b hba' t) t).det ≠ 0 := by
      intro t
      have key : ((fun t : unitInterval => γ t * negFlipPath a b hba' t) t).det =
          (γ t).det * (negFlipPath a b hba' t).det := by
        simp only []
        rw [Matrix.det_mul]
      rw [key]
      exact mul_ne_zero (hγ t) (negFlipProduct_det a b hba' (t : ℝ))
    refine ⟨{
      toFun := fun t => γ t * negFlipPath a b hba' t
      continuous_toFun := γ.continuous.matrix_mul (negFlipPath a b hba').continuous
      source' := hsrc
      target' := htgt }, hdetfun⟩
  · have hnonneg : ∀ i, 0 ≤ E i := fun i => le_of_not_gt fun h => hneg ⟨i, h⟩
    have hpos_entries : ∀ i, 0 < E i := fun i =>
      lt_of_le_of_ne (hnonneg i) (Ne.symm (hE i))
    have hsrc : Matrix.diagonal (fun i => 1 + ((0 : unitInterval) : ℝ) * (E i - 1)) = 1 := by
      have hfun : (fun i => 1 + ((0 : unitInterval) : ℝ) * (E i - 1)) = fun _ => 1 := by
        funext i
        have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
        rw [h0, zero_mul, add_zero]
      rw [hfun]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    have htgt : Matrix.diagonal (fun i => 1 + ((1 : unitInterval) : ℝ) * (E i - 1)) =
        Matrix.diagonal E := by
      congr 1
      funext i
      have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
      rw [h1, one_mul]
      ring
    have hcont : Continuous fun t : unitInterval =>
        Matrix.diagonal fun i => 1 + (t : ℝ) * (E i - 1) := by
      apply Continuous.matrix_diagonal
      apply continuous_pi
      intro i
      fun_prop
    refine ⟨{
      toFun := fun t => Matrix.diagonal fun i => 1 + (t : ℝ) * (E i - 1)
      continuous_toFun := hcont
      source' := hsrc
      target' := htgt }, ?_⟩
    have hdetfun : ∀ t : unitInterval, ((fun t : unitInterval =>
        Matrix.diagonal fun i => 1 + (t : ℝ) * (E i - 1)) t).det ≠ 0 := by
      intro t
      simp only [Matrix.det_diagonal]
      exact ne_of_gt (Finset.prod_pos fun i _ => by
        have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.property.1
        have ht1 : (t : ℝ) ≤ 1 := t.property.2
        rcases eq_or_lt_of_le ht0 with h | h
        · rw [← h]
          norm_num
        · nlinarith [mul_pos h (hpos_entries i)])
    exact hdetfun

private theorem listProdPath_det (L : List (Matrix.TransvectionStruct (Fin n) ℝ))
    (t : unitInterval) : (listProdPath L t).det = 1 :=
  scaledTransvectionProduct_det L (t : ℝ)

private theorem exists_path_one_of_det_pos (A : Matrix (Fin n) (Fin n) ℝ) (hA : 0 < A.det) :
    ∃ γ : Path (1 : Matrix (Fin n) (Fin n) ℝ) A, ∀ t, (γ t).det ≠ 0 := by
  obtain ⟨L, L', D, hAdecomp⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A
  have hdetD : (Matrix.diagonal D).det = A.det := by
    conv_rhs => rw [hAdecomp]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod,
      Matrix.TransvectionStruct.det_toMatrix_prod]
    ring
  have hprod : ∏ i, D i = A.det := by
    rw [← Matrix.det_diagonal, hdetD]
  have hDne : ∀ i, D i ≠ 0 := by
    have hne : ∏ i, D i ≠ 0 := by
      rw [hprod]
      exact ne_of_gt hA
    intro i
    exact Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)
  obtain ⟨γe, hγe⟩ := exists_path_diagonal_of_prod_pos D hDne (by rw [hprod]; exact hA)
  have hsrc : (fun t : unitInterval => listProdPath L t * γe t * listProdPath L' t) 0 = 1 := by
    have h1 : listProdPath L 0 = 1 := Path.source (listProdPath L)
    have h2 : γe 0 = 1 := Path.source γe
    have h3 : listProdPath L' 0 = 1 := Path.source (listProdPath L')
    simp only []
    rw [h1, h2, h3, Matrix.one_mul, Matrix.one_mul]
  have htgt : (fun t : unitInterval => listProdPath L t * γe t * listProdPath L' t) 1 = A := by
    have h1 : listProdPath L 1 = (L.map Matrix.TransvectionStruct.toMatrix).prod :=
      Path.target (listProdPath L)
    have h2 : γe 1 = Matrix.diagonal D := Path.target γe
    have h3 : listProdPath L' 1 = (L'.map Matrix.TransvectionStruct.toMatrix).prod :=
      Path.target (listProdPath L')
    simp only []
    rw [h1, h2, h3, ← hAdecomp]
  have hdetfun : ∀ t : unitInterval,
      ((fun t : unitInterval => listProdPath L t * γe t * listProdPath L' t) t).det ≠ 0 := by
    intro t
    have key : ((fun t : unitInterval => listProdPath L t * γe t * listProdPath L' t) t).det =
        (listProdPath L t).det * (γe t).det * (listProdPath L' t).det := by
      simp only []
      rw [Matrix.det_mul, Matrix.det_mul]
    rw [key, listProdPath_det L t, listProdPath_det L' t, one_mul, mul_one]
    exact hγe t
  exact ⟨{
    toFun := fun t => listProdPath L t * γe t * listProdPath L' t
    continuous_toFun := ((listProdPath L).continuous.matrix_mul γe.continuous).matrix_mul
      (listProdPath L').continuous
    source' := hsrc
    target' := htgt }, hdetfun⟩

private theorem det_pos_of_path_det_ne_zero {A B : Matrix (Fin n) (Fin n) ℝ} (hA : 0 < A.det)
    {γ : Path A B} (hγ : ∀ t, (γ t).det ≠ 0) (t : unitInterval) : 0 < (γ t).det := by
  have hcont : Continuous fun s : unitInterval => (γ s).det := γ.continuous.matrix_det
  have h0 : (γ 0).det = A.det := by
    have hsrc : γ 0 = A := Path.source γ
    rw [hsrc]
  have h0pos : 0 < ((fun s : unitInterval => (γ s).det) 0) := by
    simp only []
    rw [h0]
    exact hA
  rcases lt_trichotomy ((γ t).det) 0 with hlt | heq | hgt
  · exfalso
    have hmem : (0 : ℝ) ∈ Set.Icc ((fun s : unitInterval => (γ s).det) t)
        ((fun s : unitInterval => (γ s).det) 0) := ⟨le_of_lt hlt, le_of_lt h0pos⟩
    rcases le_total (0 : unitInterval) t with ht | ht
    · obtain ⟨s, _, hsv⟩ := intermediate_value_Icc' (a := (0 : unitInterval)) (b := t) ht
        hcont.continuousOn hmem
      exact hγ s hsv
    · obtain ⟨s, _, hsv⟩ := intermediate_value_Icc (a := t) (b := (0 : unitInterval)) ht
        hcont.continuousOn hmem
      exact hγ s hsv
  · exact absurd heq (hγ t)
  · exact hgt

theorem exists_path_of_det_pos (A B : Matrix (Fin n) (Fin n) ℝ) (hA : 0 < A.det)
    (hB : 0 < B.det) : ∃ γ : Path A B, ∀ t, 0 < (γ t).det := by
  obtain ⟨γA, hγA⟩ := exists_path_one_of_det_pos A hA
  obtain ⟨γB, hγB⟩ := exists_path_one_of_det_pos B hB
  have hsymm : ∀ s : unitInterval, (γA.symm s).det ≠ 0 := by
    intro s
    rw [Path.symm_apply]
    exact hγA _
  have hne : ∀ t : unitInterval, ((γA.symm.trans γB) t).det ≠ 0 := by
    intro t
    rw [Path.trans_apply]
    split_ifs with h
    · exact hsymm _
    · exact hγB _
  exact ⟨γA.symm.trans γB, fun t => det_pos_of_path_det_ne_zero hA hne t⟩

theorem isPathConnected_det_pos (n : ℕ) :
    IsPathConnected {A : Matrix (Fin n) (Fin n) ℝ | 0 < A.det} := by
  refine ⟨1, ?_, ?_⟩
  · rw [Set.mem_ofPred_eq]
    simp only [Matrix.det_one]
    norm_num
  · intro B hB
    obtain ⟨γ, hγ⟩ := exists_path_of_det_pos 1 B (by simp only [Matrix.det_one]; norm_num) hB
    exact ⟨γ, fun t => hγ t⟩

end DifferentialGeometry.Topology
