import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompLinear

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Tower-level single-step contraction-Leibniz for `covDerivStepComp`

`ric_bound` (MSM135 Lemma 3.11, Claim 1) needs the m-fold contraction-Leibniz
`∇^m(A∗g) = ∑_c \binom m c ∇^c A ∗ ∇^{m-c} g` at the tower (`covDerivStepComp`) level.
The engine is the single covariant derivative of a natural (upper–lower) contraction
of two component arrays.  This is the rank-uniform, tower-level (add-front-index)
version of `AkContractLeibniz.covD3_starAg_leibniz`, following the product-rule
pattern of `Tensor/Auxiliary/DerivationAlgebra.contractUpper_first_product_of_local_rules`.

The contraction `contrTail A B` contracts the **last** slot of `A` against the last
slot of `B`; `covDerivStepComp` prepends the derivative slot at the front, so the
derivative never collides with the contracted slot.  The first Leibniz term needs
only the rank cast `(p+1)+q = p+q+1` (`omega`); the second term additionally moves
the new derivative slot from position `p` to the front (a `Fin` rotation of the
first `p+1` slots).
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- Natural contraction of the last slots of two component arrays:
`(A ∗ B)_{idx} = ∑_c A (⟨idx₁, c⟩) · B (⟨idx₂, c⟩)`, where `idx` splits into `A`'s
first `p` free slots and `B`'s last `q` free slots. -/
def contrTail {p q : ℕ}
    (A : (Fin (p + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real) :
    (Fin (p + q) → Idx) → Real :=
  fun idx =>
    ∑ c : Idx,
      A (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) *
        B (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c)

@[simp] theorem contrTail_apply {p q : ℕ}
    (A : (Fin (p + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real)
    (idx : Fin (p + q) → Idx) :
    contrTail A B idx =
      ∑ c : Idx,
        A (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) *
          B (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) := rfl

/-- The two free index-blocks of a contraction split via `Fin.append`. -/
private theorem castAdd_append {p q : ℕ} (aPart : Fin p → Idx) (bPart : Fin q → Idx)
    (i : Fin p) : (Fin.append aPart bPart) (Fin.castAdd q i) = aPart i := by
  simp [Fin.append_left]

private theorem natAdd_append {p q : ℕ} (aPart : Fin p → Idx) (bPart : Fin q → Idx)
    (j : Fin q) : (Fin.append aPart bPart) (Fin.natAdd p j) = bPart j := by
  simp [Fin.append_right]

private theorem castAdd_ne_natAdd {p q : ℕ} (i : Fin p) (j : Fin q) :
    Fin.castAdd q i ≠ Fin.natAdd p j := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd] at hv
  have := i.isLt
  omega

/-- Updating the `i`-th `A`-block slot of `append aPart bPart` updates `aPart`. -/
private theorem update_append_castAdd {p q : ℕ} (aPart : Fin p → Idx) (bPart : Fin q → Idx)
    (i : Fin p) (v : Idx) :
    Function.update (Fin.append aPart bPart) (Fin.castAdd q i) v =
      Fin.append (Function.update aPart i v) bPart := by
  funext k
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
  · rw [Fin.append_left]
    rcases eq_or_ne i' i with rfl | h
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun he => h (Fin.castAdd_injective _ _ he)),
        Fin.append_left, Function.update_of_ne h]
  · rw [Fin.append_right, Function.update_of_ne (castAdd_ne_natAdd i j').symm, Fin.append_right]

/-- Updating the `j`-th `B`-block slot of `append aPart bPart` updates `bPart`. -/
private theorem update_append_natAdd {p q : ℕ} (aPart : Fin p → Idx) (bPart : Fin q → Idx)
    (j : Fin q) (v : Idx) :
    Function.update (Fin.append aPart bPart) (Fin.natAdd p j) v =
      Fin.append aPart (Function.update bPart j v) := by
  funext k
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
  · rw [Fin.append_left, Function.update_of_ne (castAdd_ne_natAdd i' j), Fin.append_left]
  · rw [Fin.append_right]
    rcases eq_or_ne j' j with rfl | h
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun he => h (Fin.natAdd_injective _ _ he)),
        Fin.append_right, Function.update_of_ne h]

/-! ### `Fin` `snoc`/`update`/`tail` helpers for the tower Leibniz proof -/

private theorem snoc_cons_zero {p : ℕ} (d : Idx) (Y : Fin p → Idx) (c : Idx) :
    (Fin.snoc (Fin.cons d Y : Fin (p + 1) → Idx) c : Fin (p + 2) → Idx) 0 = d := by
  rw [show (0 : Fin (p + 2)) = Fin.castSucc 0 from by simp, Fin.snoc_castSucc, Fin.cons_zero]

private theorem tail_snoc_cons {p : ℕ} (d : Idx) (Y : Fin p → Idx) (c : Idx) :
    Fin.tail (Fin.snoc (Fin.cons d Y : Fin (p + 1) → Idx) c : Fin (p + 2) → Idx) =
      (Fin.snoc Y c : Fin (p + 1) → Idx) := by
  funext i
  show (Fin.snoc (Fin.cons d Y : Fin (p + 1) → Idx) c : Fin (p + 2) → Idx) i.succ =
    (Fin.snoc Y c : Fin (p + 1) → Idx) i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.cons_succ, Fin.snoc_castSucc]
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_last]

private theorem update_snoc_last {p : ℕ} (Y : Fin p → Idx) (c a : Idx) :
    Function.update (Fin.snoc Y c : Fin (p + 1) → Idx) (Fin.last p) a =
      (Fin.snoc Y a : Fin (p + 1) → Idx) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Function.update_of_ne (Fin.castSucc_lt_last j).ne, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Function.update_self, Fin.snoc_last]

private theorem update_snoc_castSucc {p : ℕ} (Y : Fin p → Idx) (c a : Idx) (j : Fin p) :
    Function.update (Fin.snoc Y c : Fin (p + 1) → Idx) (Fin.castSucc j) a =
      (Fin.snoc (Function.update Y j a) c : Fin (p + 1) → Idx) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    rcases eq_or_ne k j with rfl | hkj
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun h => hkj (Fin.castSucc_injective _ h)),
        Function.update_of_ne hkj, Fin.snoc_castSucc]
  · rw [Function.update_of_ne (Fin.castSucc_lt_last j).ne', Fin.snoc_last, Fin.snoc_last]

/-- The **upper-index** covariant-derivative step: like `covDerivStepComp`, but the
contracted (last) slot of `A` carries the `+Γ` upper correction (`+∑_a chr (n 0) a
(slotval) · A(last ← a)`, the rank-uniform `covD12`/`covDInv` rule) while the first `p`
slots and the new front derivative carry the `−Γ` lower correction.  Used for the factor
whose last slot is the contracted upper index in a natural contraction. -/
def covDerivStepCompU {p : ℕ}
    (ext : (Fin (p + 1) → Idx) → Idx → Real)
    (chr : Idx → Idx → Idx → Real)
    (A : (Fin (p + 1) → Idx) → Real) : (Fin (p + 2) → Idx) → Real :=
  fun n =>
    ext (Fin.tail n) (n 0) -
      (∑ j : Fin p, ∑ a : Idx,
        chr (n 0) (Fin.tail n (Fin.castSucc j)) a *
          A (Function.update (Fin.tail n) (Fin.castSucc j) a)) +
      (∑ a : Idx,
        chr (n 0) a (Fin.tail n (Fin.last p)) *
          A (Function.update (Fin.tail n) (Fin.last p) a))

/-- **The contracted-slot cancellation** (the crux of the tower Leibniz): the `+Γ`
upper correction from `A`'s contracted slot equals the `−Γ` lower correction from `B`'s,
so in the Leibniz sum (`A`'s with `+`, `B`'s with `−`) they cancel.  Pure `Finset`
relabel (`sum_comm` + rename), metric-free. -/
theorem contrTail_contracted_cancel {p q : ℕ}
    (chr : Idx → Idx → Idx → Real) (d : Idx)
    (A : (Fin (p + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real)
    (aPart : Fin p → Idx) (bPart : Fin q → Idx) :
    (∑ c : Idx, (∑ a : Idx, chr d a c * A (Fin.snoc aPart a)) * B (Fin.snoc bPart c)) =
      ∑ c : Idx, A (Fin.snoc aPart c) *
        (∑ e : Idx, chr d c e * B (Fin.snoc bPart e)) := by
  classical
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by ring

/-- **Tower-level single-step contraction-Leibniz** (corrected: `A`'s contracted last
slot is upper, via `covDerivStepCompU`; `B`'s is lower, via `covDerivStepComp`).  The
covariant derivative of the natural last-slot contraction splits by the product rule;
the contracted-slot corrections (`+Γ` from `A`'s upper, `−Γ` from `B`'s lower) cancel by
relabel (`contrTail_contracted_cancel`), metric-free — the rank-uniform version of
`AkContractLeibniz.covD3_starAg_leibniz`. -/
theorem covDerivStepCompU_contrTail_leibniz {p q : ℕ}
    (extA : (Fin (p + 1) → Idx) → Idx → Real)
    (extB : (Fin (q + 1) → Idx) → Idx → Real)
    (ext : (Fin (p + q) → Idx) → Idx → Real)
    (chr : Idx → Idx → Idx → Real)
    (A : (Fin (p + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real)
    (hext : ∀ (idx : Fin (p + q) → Idx) (d : Idx),
      ext idx d =
        ∑ c : Idx,
          (extA (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) d *
              B (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) +
            A (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) *
              extB (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) d))
    (d : Idx) (aPart : Fin p → Idx) (bPart : Fin q → Idx) :
    covDerivStepComp ext chr (contrTail A B) (Fin.cons d (Fin.append aPart bPart)) =
      contrTail (covDerivStepCompU extA chr A) B
          (Fin.append (Fin.cons d aPart) bPart) +
        contrTail A (covDerivStepComp extB chr B)
          (Fin.append aPart (Fin.cons d bPart)) := by
  classical
  -- FULL DERIVATION (verified by hand 2026-06-08; remaining work = transcription).
  -- LHS, unfold covDerivStepComp + Fin.tail_cons/cons_zero + hext + castAdd_append/natAdd_append:
  --   = ∑_c(extA(snoc aPart c)d·B(snoc bPart c) + A(snoc aPart c)·extB(snoc bPart c)d)
  --     − ∑_{s:Fin(p+q)} ∑_{c'} chr d ((append aPart bPart)s) c' · (contrTail A B)(update(append aPart bPart)s c').
  -- firstTerm: contrTail(covDerivStepCompU extA chr A) B (append (cons d aPart) bPart), unfold covDerivStepCompU on
  --   `snoc (cons d aPart) c` (tail(snoc(cons d aPart)c)=snoc aPart c; (·)0=d; snoc_castSucc/snoc_last;
  --   update(snoc aPart c)(castSucc j) a = snoc(update aPart j a)c; update(snoc aPart c)(last) a = snoc aPart a):
  --   = ∑_c extA(snoc aPart c)d·B(snoc bPart c)
  --     − ∑_c(∑_j ∑_a chr d (aPart j) a · A(snoc(update aPart j a)c))·B(snoc bPart c)        [A-free, lower]
  --     + ∑_c(∑_a chr d a c · A(snoc aPart a))·B(snoc bPart c).                                [A contracted, UPPER +Γ]
  -- secondTerm: contrTail A (covDerivStepComp extB chr B)(append aPart (cons d bPart)), unfold covDerivStepComp on
  --   `snoc(cons d bPart)c`, split ∑_{s'':Fin(q+1)} via Fin.sum_univ_castSucc:
  --   = ∑_c A(snoc aPart c)·extB(snoc bPart c)d
  --     − ∑_c A(snoc aPart c)·(∑_j ∑_e chr d (bPart j) e · B(snoc(update bPart j e)c))         [B-free, lower]
  --     − ∑_c A(snoc aPart c)·(∑_e chr d c e · B(snoc bPart e)).                                [B contracted, LOWER −Γ]
  -- MATCH: ext halves ✓. A-contracted(+) + B-contracted(−) = 0 by `contrTail_contracted_cancel`.
  --   LHS Christoffel split via Fin.sum_univ_add (addCases): A-block(s=castAdd i) = firstTerm A-free
  --   (update(append..)(castAdd i)c'∘castAdd = update aPart i c', ∘natAdd = bPart; reorder ∑_c inside);
  --   B-block(s=natAdd j) = secondTerm B-free. ⇒ LHS = ext − A-block − B-block = RHS.
  -- Fin lemmas: Fin.tail_cons, Fin.cons_zero, Fin.snoc_castSucc, Fin.snoc_last, Fin.tail_snoc(?funext),
  --   Fin.update_snoc_last/_castSucc(?funext), Fin.sum_univ_add, Fin.sum_univ_castSucc, append_left/right.
  simp only [covDerivStepComp, covDerivStepCompU, contrTail, Fin.tail_cons, Fin.cons_zero,
    castAdd_append, natAdd_append, snoc_cons_zero, tail_snoc_cons,
    Fin.snoc_castSucc, Fin.snoc_last, update_snoc_castSucc, update_snoc_last]
  rw [hext]
  simp only [castAdd_append, natAdd_append]
  rw [Fin.sum_univ_add]
  simp only [castAdd_append, natAdd_append, update_append_castAdd, update_append_natAdd,
    Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, update_snoc_castSucc, update_snoc_last]
  -- A-block of the LHS Christoffel sum = first-term's free corrections (triple-sum reorder).
  have hA :
      (∑ x : Fin p, ∑ x_1 : Idx, chr d (aPart x) x_1 *
          ∑ x_2 : Idx, A (Fin.snoc (Function.update aPart x x_1) x_2) * B (Fin.snoc bPart x_2)) =
        ∑ x : Idx, (∑ x_1 : Fin p, ∑ x_2 : Idx, chr d (aPart x_1) x_2 *
            A (Fin.snoc (Function.update aPart x_1 x_2) x)) * B (Fin.snoc bPart x) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm (f := fun x_1 x_2 =>
      chr d (aPart x) x_1 * (A (Fin.snoc (Function.update aPart x x_1) x_2) * B (Fin.snoc bPart x_2))),
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun x2 _ => Finset.sum_congr rfl fun xs _ =>
      Finset.sum_congr rfl fun x1 _ => by ring
  -- B-block = second-term's free corrections.
  have hB :
      (∑ x : Fin q, ∑ x_1 : Idx, chr d (bPart x) x_1 *
          ∑ x_2 : Idx, A (Fin.snoc aPart x_2) * B (Fin.snoc (Function.update bPart x x_1) x_2)) =
        ∑ x : Idx, A (Fin.snoc aPart x) *
          ∑ x_1 : Fin q, ∑ x_2 : Idx, chr d (bPart x_1) x_2 *
            B (Fin.snoc (Function.update bPart x_1 x_2) x) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm (f := fun x_1 x_2 =>
      chr d (bPart x) x_1 * (A (Fin.snoc aPart x_2) * B (Fin.snoc (Function.update bPart x x_1) x_2))),
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun x2 _ => Finset.sum_congr rfl fun xs _ =>
      Finset.sum_congr rfl fun x1 _ => by ring
  -- contracted corrections cancel.
  have hcancel := contrTail_contracted_cancel (Idx := Idx) chr d A B aPart bPart
  rw [hA, hB]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
    mul_sub, mul_add, sub_mul, add_mul]
  simp only [← Finset.sum_mul, ← Finset.mul_sum] at hcancel ⊢
  linarith [hcancel]

end DifferentialGeometry.PDE.RicciFlow
