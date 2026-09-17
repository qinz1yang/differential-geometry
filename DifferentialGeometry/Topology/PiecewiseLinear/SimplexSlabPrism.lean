import DifferentialGeometry.Topology.PiecewiseLinear.CellEquivalence
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexHeightInterpolation
import Mathlib.Tactic.FinCases

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem nonneg_of_sign_eq_or_zero {a b : ℝ}
    (h : SignType.sign a = SignType.sign b ∨ SignType.sign a = 0) (hb : 0 ≤ b) : 0 ≤ a := by
  apply sign_nonneg_iff.mp
  rcases h with h | h
  · rw [h]
    exact sign_nonneg_iff.mpr hb
  · rw [h]

private theorem nonpos_of_sign_eq_or_zero {a b : ℝ}
    (h : SignType.sign a = SignType.sign b ∨ SignType.sign a = 0) (hb : b ≤ 0) : a ≤ 0 := by
  apply sign_nonpos_iff.mp
  rcases h with h | h
  · rw [h]
    exact sign_nonpos_iff.mpr hb
  · rw [h]

private theorem sign_eq_of_nonneg_of_zero_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hzero : a = 0 ↔ b = 0) : SignType.sign a = SignType.sign b := by
  by_cases h : a = 0
  · rw [h, hzero.mp h]
  · rw [sign_eq_one_iff.mpr (lt_of_le_of_ne ha (Ne.symm h)),
      sign_eq_one_iff.mpr (lt_of_le_of_ne hb (Ne.symm (hzero.not.mp h)))]

variable {ι : Type} [Fintype ι]

private def simplexSlabArrangement (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (a b : ℝ) :
    ι ⊕ Fin 4 → (ι → ℝ) →ᵃ[ℝ] ℝ :=
  Sum.elim (fun i => (LinearMap.proj i).toAffineMap)
    ![(∑ i, (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)).toAffineMap - AffineMap.const ℝ _ 1,
      0, ℓ.toAffineMap - AffineMap.const ℝ _ a, ℓ.toAffineMap - AffineMap.const ℝ _ b]

private def simplexPrismArrangement (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (a b : ℝ) :
    ι ⊕ Fin 4 → ((ι → ℝ) × ℝ) →ᵃ[ℝ] ℝ :=
  Sum.elim (fun i => ((LinearMap.proj i).comp (LinearMap.fst ℝ (ι → ℝ) ℝ)).toAffineMap)
    ![((∑ i, (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)).comp
        (LinearMap.fst ℝ (ι → ℝ) ℝ)).toAffineMap - AffineMap.const ℝ _ 1,
      (ℓ.comp (LinearMap.fst ℝ (ι → ℝ) ℝ)).toAffineMap - AffineMap.const ℝ _ a,
      (LinearMap.snd ℝ (ι → ℝ) ℝ).toAffineMap - AffineMap.const ℝ _ a,
      (LinearMap.snd ℝ (ι → ℝ) ℝ).toAffineMap - AffineMap.const ℝ _ b]

private theorem simplexSlabArrangement_apply (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (a b : ℝ)
    (x : ι → ℝ) (i : ι ⊕ Fin 4) :
    simplexSlabArrangement ℓ a b i x = Sum.elim x ![∑ j, x j - 1, 0, ℓ x - a, ℓ x - b] i := by
  rcases i with i | i
  · rfl
  · fin_cases i <;> simp [simplexSlabArrangement]

private theorem simplexPrismArrangement_apply (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (a b : ℝ)
    (x : (ι → ℝ) × ℝ) (i : ι ⊕ Fin 4) :
    simplexPrismArrangement ℓ a b i x =
      Sum.elim x.1 ![∑ j, x.1 j - 1, ℓ x.1 - a, x.2 - a, x.2 - b] i := by
  rcases i with i | i
  · rfl
  · fin_cases i <;> simp [simplexPrismArrangement]

private theorem isCellClosed_simplexSlab (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (a b : ℝ) :
    IsCellClosed (simplexSlabArrangement ℓ a b)
      (stdSimplex ℝ ι ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b}) := by
  rintro x ⟨hx, hxa, hxb⟩ y hy
  have hsign (i) := hy i
  simp only [signVec, simplexSlabArrangement_apply] at hsign
  have hsum := hsign (Sum.inr 0)
  simp only [Sum.elim_inr, Matrix.cons_val_zero, hx.2, sub_self, sign_zero] at hsum
  have hyone : ∑ i, y i = 1 := by
    have hz := sign_eq_zero_iff.mp (hsum.elim id id)
    linarith
  refine ⟨⟨fun i => nonneg_of_sign_eq_or_zero (hsign (Sum.inl i)) (hx.1 i), hyone⟩, ?_, ?_⟩
  · have h := nonneg_of_sign_eq_or_zero (hsign (Sum.inr 2)) (sub_nonneg.mpr hxa)
    exact sub_nonneg.mp h
  · have h := nonpos_of_sign_eq_or_zero (hsign (Sum.inr 3)) (sub_nonpos.mpr hxb)
    exact sub_nonpos.mp h

private theorem isCellClosed_simplexPrism (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (a b : ℝ) :
    IsCellClosed (simplexPrismArrangement ℓ a b)
      ((stdSimplex ℝ ι ∩ {x | ℓ x = a}) ×ˢ Icc a b) := by
  rintro x ⟨⟨hx, hxlevel⟩, hxa, hxb⟩ y hy
  change ℓ x.1 = a at hxlevel
  have hsign (i) := hy i
  simp only [signVec, simplexPrismArrangement_apply] at hsign
  have hsum := hsign (Sum.inr 0)
  simp only [Sum.elim_inr, Matrix.cons_val_zero, hx.2, sub_self, sign_zero] at hsum
  have hyone : ∑ i, y.1 i = 1 := by
    have hz := sign_eq_zero_iff.mp (hsum.elim id id)
    linarith
  have hlevel := hsign (Sum.inr 1)
  have hyzero : ℓ y.1 - a = 0 := by
    apply sign_eq_zero_iff.mp
    simpa only [Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero,
      hxlevel, sub_self, sign_zero, or_self] using hlevel
  refine ⟨⟨⟨fun i => nonneg_of_sign_eq_or_zero (hsign (Sum.inl i)) (hx.1 i), hyone⟩,
    sub_eq_zero.mp hyzero⟩, ?_, ?_⟩
  · exact sub_nonneg.mp (nonneg_of_sign_eq_or_zero (hsign (Sum.inr 2)) (sub_nonneg.mpr hxa))
  · exact sub_nonpos.mp (nonpos_of_sign_eq_or_zero (hsign (Sum.inr 3)) (sub_nonpos.mpr hxb))

open Classical in
private theorem cellsOf_simplexSlab_eq_simplexPrism (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) {a b : ℝ}
    (hvertices : ∀ i, ℓ (Pi.single i 1) < a ∨ b < ℓ (Pi.single i 1)) :
    cellsOf (simplexSlabArrangement ℓ a b) (stdSimplex ℝ ι ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b}) =
      cellsOf (simplexPrismArrangement ℓ a b) ((stdSimplex ℝ ι ∩ {x | ℓ x = a}) ×ˢ Icc a b) := by
  ext σ
  constructor
  · rintro ⟨x, ⟨hx, hxa, hxb⟩, rfl⟩
    obtain ⟨y, hy, hya, hsupport⟩ := exists_stdSimplex_same_support_height ℓ hvertices
      hx hxa hxb (r := a) le_rfl (hxa.trans hxb)
    refine ⟨(y, ℓ x), ⟨⟨hy, hya⟩, hxa, hxb⟩, ?_⟩
    funext i
    simp only [signVec, simplexSlabArrangement_apply, simplexPrismArrangement_apply]
    rcases i with i | i
    · exact sign_eq_of_nonneg_of_zero_iff (hy.1 i) (hx.1 i) (hsupport i)
    · fin_cases i <;> simp [hx.2, hy.2, hya]
  · rintro ⟨⟨x, t⟩, ⟨⟨hx, hxa⟩, hta, htb⟩, rfl⟩
    change ℓ x = a at hxa
    obtain ⟨y, hy, hyt, hsupport⟩ := exists_stdSimplex_same_support_height ℓ hvertices
      hx hxa.ge (hxa.le.trans (hta.trans htb)) (r := t) hta htb
    refine ⟨y, ⟨hy, hyt.symm ▸ hta, hyt.symm ▸ htb⟩, ?_⟩
    funext i
    simp only [signVec, simplexSlabArrangement_apply, simplexPrismArrangement_apply]
    rcases i with i | i
    · exact sign_eq_of_nonneg_of_zero_iff (hy.1 i) (hx.1 i) (hsupport i)
    · fin_cases i <;> simp [hx.2, hy.2, hxa, hyt]

open Classical in
theorem exists_isPLHomeomorphOn_stdSimplex_slab_prism
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) {a b : ℝ}
    (hvertices : ∀ i, ℓ (Pi.single i 1) < a ∨ b < ℓ (Pi.single i 1)) :
    ∃ f : (ι → ℝ) → (ι → ℝ) × ℝ,
      IsPLHomeomorphOn f (stdSimplex ℝ ι ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b})
        ((stdSimplex ℝ ι ∩ {x | ℓ x = a}) ×ˢ Icc a b) ∧
      ∀ x ∈ stdSimplex ℝ ι ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b},
        (∀ i, (f x).1 i = 0 ↔ x i = 0) ∧ ((f x).2 = a ↔ ℓ x = a) ∧
          ((f x).2 = b ↔ ℓ x = b) := by
  classical
  have hP : IsCompact (stdSimplex ℝ ι ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b}) :=
    (isCompact_stdSimplex ℝ ι).inter_right ((isClosed_le continuous_const ℓ.continuous_of_finiteDimensional).inter
      (isClosed_le ℓ.continuous_of_finiteDimensional continuous_const))
  have hQ : IsCompact ((stdSimplex ℝ ι ∩ {x | ℓ x = a}) ×ˢ Icc a b) :=
    ((isCompact_stdSimplex ℝ ι).inter_right
      (isClosed_eq ℓ.continuous_of_finiteDimensional continuous_const)).prod isCompact_Icc
  obtain ⟨f, hf, hsign⟩ := exists_isPLHomeomorphOn_of_cellsOf_eq
    (simplexSlabArrangement ℓ a b) _ (simplexPrismArrangement ℓ a b) _
    (isCellClosed_simplexSlab ℓ a b) hP (isCellClosed_simplexPrism ℓ a b) hQ
    (cellsOf_simplexSlab_eq_simplexPrism ℓ hvertices)
  refine ⟨f, hf, ?_⟩
  intro x hx
  have heq (i) := congrFun (hsign x hx) i
  simp only [signVec, simplexSlabArrangement_apply, simplexPrismArrangement_apply] at heq
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact sign_eq_zero_iff.symm.trans ((congrArg (· = 0) (heq (Sum.inl i))).to_iff.trans sign_eq_zero_iff)
  · have h := (congrArg (· = 0) (heq (Sum.inr 2))).to_iff
    simpa [sign_eq_zero_iff, sub_eq_zero] using h
  · have h := (congrArg (· = 0) (heq (Sum.inr 3))).to_iff
    simpa [sign_eq_zero_iff, sub_eq_zero] using h

end DifferentialGeometry.Topology.PiecewiseLinear
