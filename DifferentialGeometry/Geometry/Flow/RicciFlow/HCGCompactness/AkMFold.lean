import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompContr
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompContrNorm
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSectionsLocal
import DifferentialGeometry.Tensor.RSTensor.NablaDomDomCongr

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The field-level upper covariant-derivative tower for `A_k` (Claim 1 m-fold, route i)

`ric_bound` (MSM135 Lemma 3.11) Claim 1 `|∇^m A_k| ≤ C_m(1+|∇^{m+1}g_k|)`, with
`A_k := connectionDifferenceTensorAt (LC g_k) (LC gRef) = ∇_k − ∇_ref` (so the lowered
`A_k∗g_k` is the Koszul combination of `∇g_k` with coefficients `+½,+½,−½` — the
`hkoszul` input of `claim1`).  The route differentiates the lowered relation `m` times
(component route, user-resolved). The natural last-slot contraction `∗` (`contrTail`)
has the proven single-step tower Leibniz `covDerivStepCompU_contrTail_leibniz`:
`A_k`'s contracted UPPER slot steps by `covDerivStepCompU` (`+Γ`), `g_k`'s lower slot
by `covDerivStepComp` (`−Γ`).

This file builds the FIELD-level iterated upper tower `iterCovCompU` — the
`covDerivStepCompU` analogue of `iterCovComp` (whose step's `ext` is `frameExtData`
of the whole running field, NOT a single-point function). The `+1` (the contracted
upper slot) is kept LAST in the rank so the recursion ranks `(r+a)+1` stay defeq.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-! ## The tower shift `∇^{m+1} = reindex(∇^m ∘ ∇)` (bottom-pull, the m-fold engine) -/

/-- The recursive rank-cast equiv `Fin ((r+1)+m) ≃ Fin (r+(m+1))` threading the
component-tower shift (mirror of the bundled `HCGCompactness.shiftEquiv`). -/
def shiftEquivC (r : ℕ) : (m : ℕ) → Fin ((r + 1) + m) ≃ Fin (r + (m + 1))
  | 0 => Equiv.refl _
  | (m + 1) => frontExtendEquiv (shiftEquivC r m)

/-- **`covDerivStepComp` commutes with a free-slot reindex** (the component analogue of
`covStep_domDomCongr`): reindexing both the `ext` data and the array by `e` on the `s`
free slots, then stepping, equals stepping then reindexing by `frontExtendEquiv e` (which
fixes the new leading derivative slot).  Pure component identity: the new slot and the
contracted Christoffel sum reindex by `e`. -/
theorem covDerivStepComp_compReindex {s s' : ℕ} (e : Fin s ≃ Fin s')
    (ext : (Fin s → Idx) → Idx → Real) (chr : Idx → Idx → Idx → Real)
    (A : (Fin s → Idx) → Real) (n : Fin (s' + 1) → Idx) :
    covDerivStepComp (fun m' d => ext (fun i => m' (e i)) d) chr
        (fun n' => A (fun i => n' (e i))) n =
      covDerivStepComp ext chr A (fun j => n (frontExtendEquiv e j)) := by
  classical
  have htail : Fin.tail (fun j => n (frontExtendEquiv e j)) = fun i => Fin.tail n (e i) := by
    funext i; simp only [Fin.tail, frontExtendEquiv_succ]
  unfold covDerivStepComp
  simp only [frontExtendEquiv_zero, htail]
  congr 1
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun p _ => ?_
  have hupd : (fun i => Function.update (Fin.tail n) (e t) p (e i)) =
      Function.update (fun i => Fin.tail n (e i)) t p := by
    funext i
    by_cases h : i = t
    · subst h; simp only [Function.update_self]
    · rw [Function.update_of_ne (fun he => h (e.injective he)),
        Function.update_of_ne h]
  rw [hupd]

/-- **The component-tower shift** (`∇^{m+1} = reindex(∇^m ∘ ∇)`, bottom-pull):
`iterCovComp base (m+1)` equals the `m`-fold tower of the single derivative
`∇base = iterCovComp base 1`, reindexed by the rank-cast `shiftEquivC` (which absorbs the
non-defeq `(r+1)+m = r+(m+1)`).  Induction on `m` from `iterCovComp_succ` +
`covDerivStepComp_compReindex` (the `frameExtData` reindex being definitional).  This is
the engine that turns the m-fold contraction-Leibniz into a clean recursion (the component
analogue of the bundled `iterCov_shift`). -/
theorem iterCovComp_shift {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real) (m : ℕ) (x : M) :
    iterCovComp (I := I) frame chr base (m + 1) x =
      fun n : Fin (r + (m + 1)) → Idx =>
        iterCovComp (I := I) frame chr (fun y => iterCovComp (I := I) frame chr base 1 y) m x
          (fun j => n (shiftEquivC r m j)) := by
  induction m generalizing x with
  | zero =>
    funext n
    simp only [shiftEquivC, iterCovComp_zero, Equiv.refl_apply]
  | succ m ih =>
    funext n
    rw [iterCovComp_succ,
      show iterCovComp (I := I) frame chr base (m + 1) =
          (fun y (nn : Fin (r + (m + 1)) → Idx) =>
            iterCovComp (I := I) frame chr (fun z => iterCovComp (I := I) frame chr base 1 z) m y
              (fun j => nn (shiftEquivC r m j))) from funext ih,
      show frameExtData (I := I) frame
            (fun y (nn : Fin (r + (m + 1)) → Idx) =>
              iterCovComp (I := I) frame chr (fun z => iterCovComp (I := I) frame chr base 1 z) m y
                (fun j => nn (shiftEquivC r m j))) x =
          fun (m' : Fin (r + (m + 1)) → Idx) d =>
            frameExtData (I := I) frame
              (iterCovComp (I := I) frame chr
                (fun z => iterCovComp (I := I) frame chr base 1 z) m) x
              (fun i => m' (shiftEquivC r m i)) d from rfl,
      covDerivStepComp_compReindex (shiftEquivC r m), ← iterCovComp_succ]
    rfl

/-- **Norm-level tower shift.**  `|∇^{m+1} base| = |∇^m (∇base)|`: the rank-cast is absorbed
by the permutation-invariance of `compL2` (`compL2_comp_equiv`), the payoff of
`iterCovComp_shift` for the bottom-pull norm inductions. -/
theorem compL2_iterCovComp_shift {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real) (m : ℕ) (x : M) :
    compL2 (iterCovComp (I := I) frame chr base (m + 1) x) =
      compL2 (iterCovComp (I := I) frame chr
        (fun y => iterCovComp (I := I) frame chr base 1 y) m x) := by
  rw [iterCovComp_shift]
  exact compL2_comp_equiv
    (iterCovComp (I := I) frame chr (fun y => iterCovComp (I := I) frame chr base 1 y) m x)
    (shiftEquivC r m)

/-- The `m`-fold front extension of a slot equiv (mirror of the bundled `frontExtendIter`). -/
def frontExtendIterC {s s' : ℕ} (e : Fin s ≃ Fin s') :
    (m : ℕ) → Fin (s + m) ≃ Fin (s' + m)
  | 0 => e
  | (m + 1) => frontExtendEquiv (frontExtendIterC e m)

/-- The slot rotation `[d, a, b] ↦ [a, d, b]`: moves the leading slot `0` to position `p`
(the B-block single-step puts the new derivative into the B-block, i.e. position `p`).
This is the `e₂` reindex of the field single-step's second (B) term. -/
def rotEquiv (p q : ℕ) : Fin (p + (q + 1)) ≃ Fin (p + q + 1) :=
  (finCongr (by omega)).trans (Fin.cycleRange ⟨p, by omega⟩)

/-- Slot identity for the field single-step's first (A) term: `[d, a, b]` regrouped from
`(p+1)+q` to `(p+q)+1` is the same sequence, i.e. precomposition by the rank cast. -/
private theorem slotId1 {p q : ℕ} (d : Idx) (aPart : Fin p → Idx) (bPart : Fin q → Idx) :
    (Fin.append (Fin.cons d aPart) bPart : Fin (p + 1 + q) → Idx) =
      fun j => (Fin.cons d (Fin.append aPart bPart) : Fin (p + q + 1) → Idx)
        (Fin.cast (show p + 1 + q = p + q + 1 by omega) j) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · rw [Fin.append_left]
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [Fin.cons_zero]
      rw [show (Fin.cast (by omega) (Fin.castAdd q (0 : Fin (p + 1))) : Fin (p + q + 1)) = 0 by
        apply Fin.ext; simp, Fin.cons_zero]
    · rw [Fin.cons_succ]
      rw [show (Fin.cast (by omega) (Fin.castAdd q i'.succ) : Fin (p + q + 1)) =
          (Fin.castAdd q i').succ by apply Fin.ext; simp, Fin.cons_succ, Fin.append_left]
  · rw [Fin.append_right]
    rw [show (Fin.cast (by omega) (Fin.natAdd (p + 1) k) : Fin (p + q + 1)) =
        (Fin.natAdd p k).succ by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
      omega, Fin.cons_succ, Fin.append_right]

/-- Slot identity for the field single-step's second (B) term: `[a, d, b]` regrouped from
`p+(q+1)` to `(p+q)+1` is the canonical word `[d, (a,b)]` precomposed by the rotation
`rotEquiv` that pushes the new leading derivative slot past the `A`-block. -/
private theorem slotId2 {p q : ℕ} (d : Idx) (aPart : Fin p → Idx) (bPart : Fin q → Idx) :
    (Fin.append aPart (Fin.cons d bPart) : Fin (p + (q + 1)) → Idx) =
      fun i => (Fin.cons d (Fin.append aPart bPart) : Fin (p + q + 1) → Idx)
        (rotEquiv p q i) := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun k => ?_) i
  · -- A-block: i = castAdd (q+1) i' (value i' < p); rotEquiv shifts it to (castAdd q i').succ
    rw [Fin.append_left,
      show rotEquiv p q (Fin.castAdd (q + 1) i') = (Fin.castAdd q i').succ by
        apply Fin.ext
        simp only [rotEquiv, Equiv.trans_apply, Fin.val_succ, Fin.val_castAdd]
        rw [Fin.coe_cycleRange_of_lt (by rw [Fin.lt_def]; simp)]
        simp,
      Fin.cons_succ, Fin.append_left]
  · refine Fin.cases ?_ (fun j => ?_) k
    · -- B-block head: i = natAdd p 0 (value p); rotEquiv sends it to 0 ↦ d
      rw [Fin.append_right, Fin.cons_zero,
        show rotEquiv p q (Fin.natAdd p (0 : Fin (q + 1))) = 0 by
          simp only [rotEquiv, Equiv.trans_apply]
          rw [Fin.cycleRange_of_eq (by apply Fin.ext; simp)],
        Fin.cons_zero]
    · -- B-block tail: i = natAdd p j.succ (value > p); rotEquiv fixes it to (natAdd p j).succ
      rw [Fin.append_right, Fin.cons_succ,
        show rotEquiv p q (Fin.natAdd p j.succ) = (Fin.natAdd p j).succ by
          simp only [rotEquiv, Equiv.trans_apply]
          rw [Fin.cycleRange_of_gt (by rw [Fin.lt_def]; simp)]
          apply Fin.ext
          simp only [finCongr_apply_coe, Fin.val_natAdd, Fin.val_succ]
          omega,
        Fin.cons_succ, Fin.append_right]

/-- Extend a slot equiv `e₀ : Fin p ≃ Fin p'` to `Fin (p+1) ≃ Fin (p'+1)` fixing the LAST
slot (the contracted upper index of the `covDerivStepCompU` step). -/
def extendLastEquiv {p p' : ℕ} (e₀ : Fin p ≃ Fin p') : Fin (p + 1) ≃ Fin (p' + 1) :=
  finSuccEquivLast.trans (e₀.optionCongr.trans finSuccEquivLast.symm)

@[simp] theorem extendLastEquiv_castSucc {p p' : ℕ} (e₀ : Fin p ≃ Fin p') (i : Fin p) :
    extendLastEquiv e₀ (Fin.castSucc i) = Fin.castSucc (e₀ i) := by
  simp [extendLastEquiv, finSuccEquivLast_castSucc]

@[simp] theorem extendLastEquiv_last {p p' : ℕ} (e₀ : Fin p ≃ Fin p') :
    extendLastEquiv e₀ (Fin.last p) = Fin.last p' := by
  simp [extendLastEquiv, finSuccEquivLast_last]

@[simp] theorem extendLastEquiv_refl {p : ℕ} :
    extendLastEquiv (Equiv.refl (Fin p)) = Equiv.refl (Fin (p + 1)) := by
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [extendLastEquiv_last]; rfl
  · rw [extendLastEquiv_castSucc]; rfl

/-- Front-extension and last-fixing extension of a slot equiv commute. -/
theorem extendLast_frontExtend_comm {p p' : ℕ} (e : Fin p ≃ Fin p') :
    frontExtendEquiv (extendLastEquiv e) = extendLastEquiv (frontExtendEquiv e) := by
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [extendLastEquiv_last,
      show (Fin.last (p + 1) : Fin (p + 1 + 1)) = (Fin.last p).succ from (Fin.succ_last p).symm,
      frontExtendEquiv_succ, extendLastEquiv_last, Fin.succ_last]
  · refine Fin.cases ?_ (fun j' => ?_) j
    · conv_lhs => rw [Fin.castSucc_zero, frontExtendEquiv_zero]
      rw [extendLastEquiv_castSucc, frontExtendEquiv_zero, Fin.castSucc_zero]
    · rw [extendLastEquiv_castSucc, frontExtendEquiv_succ,
        show (Fin.castSucc j'.succ : Fin (p + 1 + 1)) = (Fin.castSucc j').succ from
          (Fin.succ_castSucc j').symm,
        frontExtendEquiv_succ, extendLastEquiv_castSucc, Fin.succ_castSucc]

/-- `Function.update` commutes with precomposition by a bijection (with the image slot
supplied explicitly so it matches a `simp`-reduced goal). -/
private theorem update_comp_equiv' {α β : Type*} [DecidableEq α] [DecidableEq β]
    (g : β → Idx) (e : α ≃ β) (s : α) (sv : β) (hsv : e s = sv) (a : Idx) :
    (fun i => Function.update g sv a (e i)) = Function.update (fun i => g (e i)) s a := by
  subst hsv
  funext i
  by_cases h : i = s
  · subst h; simp only [Function.update_self]
  · rw [Function.update_of_ne (fun he => h (e.injective he)), Function.update_of_ne h]

/-- **`covDerivStepCompU` commutes with a free-slot reindex fixing the upper (last) slot.**
The upper analogue of `covDerivStepComp_compReindex`: the `−Γ` sum over the first `p` (lower)
slots reindexes by `e₀`, while the `+Γ` upper correction on the last slot is fixed
(`extendLastEquiv` fixes `Fin.last`). -/
theorem covDerivStepCompU_compReindex {p p' : ℕ} (e₀ : Fin p ≃ Fin p')
    (ext : (Fin (p + 1) → Idx) → Idx → Real) (chr : Idx → Idx → Idx → Real)
    (A : (Fin (p + 1) → Idx) → Real) (n : Fin (p' + 1 + 1) → Idx) :
    covDerivStepCompU (fun m' d => ext (fun i => m' (extendLastEquiv e₀ i)) d) chr
        (fun n' => A (fun i => n' (extendLastEquiv e₀ i))) n =
      covDerivStepCompU ext chr A (fun j => n (frontExtendEquiv (extendLastEquiv e₀) j)) := by
  classical
  have htail : Fin.tail (fun j => n (frontExtendEquiv (extendLastEquiv e₀) j)) =
      fun i => Fin.tail n (extendLastEquiv e₀ i) := by
    funext i; simp only [Fin.tail, frontExtendEquiv_succ]
  unfold covDerivStepCompU
  simp only [frontExtendEquiv_zero, htail, extendLastEquiv_castSucc, extendLastEquiv_last]
  congr 1
  · congr 1
    rw [← Equiv.sum_comp e₀]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a _ => ?_
    rw [update_comp_equiv' (Fin.tail n) (extendLastEquiv e₀) (Fin.castSucc t)
      (Fin.castSucc (e₀ t)) (extendLastEquiv_castSucc e₀ t) a]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [update_comp_equiv' (Fin.tail n) (extendLastEquiv e₀) (Fin.last p)
      (Fin.last p') (extendLastEquiv_last e₀) a]

/-- **`iterCovComp` commutes with a free-slot reindex** (iterated naturality, the component
analogue of `iterCov_domDomCongr`): reindexing the base field by `e` then taking the `m`-fold
tower equals the `m`-fold tower reindexed by `frontExtendIterC e m`.  Same induction as
`iterCovComp_shift` (the reindex grows by `frontExtendEquiv` per level). -/
theorem iterCovComp_compReindex {s s' : ℕ} (e : Fin s ≃ Fin s')
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (F : M → (Fin s → Idx) → Real) (m : ℕ) (x : M) :
    iterCovComp (I := I) frame chr (fun y (nn : Fin s' → Idx) => F y (fun i => nn (e i))) m x =
      fun n : Fin (s' + m) → Idx =>
        iterCovComp (I := I) frame chr F m x (fun j => n (frontExtendIterC e m j)) := by
  induction m generalizing x with
  | zero =>
    funext n
    rfl
  | succ m ih =>
    funext n
    rw [iterCovComp_succ,
      show iterCovComp (I := I) frame chr (fun y (nn : Fin s' → Idx) => F y (fun i => nn (e i)))
            m =
          (fun y (nn : Fin (s' + m) → Idx) =>
            iterCovComp (I := I) frame chr F m y (fun j => nn (frontExtendIterC e m j)))
        from funext ih,
      show frameExtData (I := I) frame
            (fun y (nn : Fin (s' + m) → Idx) =>
              iterCovComp (I := I) frame chr F m y (fun j => nn (frontExtendIterC e m j))) x =
          fun (m' : Fin (s' + m) → Idx) d =>
            frameExtData (I := I) frame (iterCovComp (I := I) frame chr F m) x
              (fun i => m' (frontExtendIterC e m i)) d from rfl,
      covDerivStepComp_compReindex (frontExtendIterC e m), ← iterCovComp_succ]
    rfl

/-- The field-level iterated **upper** covariant-derivative component tower: `a`
applications of `covDerivStepCompU` to a base array whose LAST slot is the contracted
upper index, with the running field's frame directional derivative as `ext` and fixed
Christoffel data.  The `covDerivStepCompU` analogue of `iterCovComp`; the upper slot is
kept last so ranks `(r+a)+1` stay definitionally equal across the recursion. -/
def iterCovCompU {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) :
    (a : ℕ) → M → (Fin ((r + a) + 1) → Idx) → Real
  | 0 => base
  | (a + 1) => fun x =>
      covDerivStepCompU
        (frameExtData (I := I) frame
          (fun y : M => iterCovCompU frame chr base a y) x)
        (chr x)
        (iterCovCompU frame chr base a x)

@[simp] theorem iterCovCompU_zero {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) :
    iterCovCompU (I := I) frame chr base 0 = base := rfl

@[simp] theorem iterCovCompU_succ {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) (a : ℕ) (x : M) :
    iterCovCompU (I := I) frame chr base (a + 1) x =
      covDerivStepCompU
        (frameExtData (I := I) frame
          (fun y : M => iterCovCompU (I := I) frame chr base a y) x)
        (chr x)
        (iterCovCompU (I := I) frame chr base a x) := rfl

/-- **The upper-tower shift** (`∇_U^{m+1} = reindex(∇_U^m ∘ ∇_U)`): the `covDerivStepCompU`
analogue of `iterCovComp_shift`, with the reindex `extendLastEquiv (shiftEquivC r m)` fixing the
upper (last) slot.  The succ step uses `covDerivStepCompU_compReindex` and the commute
`extendLast_frontExtend_comm`. -/
theorem iterCovCompU_shift {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) (m : ℕ) (x : M) :
    iterCovCompU (I := I) frame chr base (m + 1) x =
      fun n : Fin (r + (m + 1) + 1) → Idx =>
        iterCovCompU (I := I) frame chr (fun y => iterCovCompU (I := I) frame chr base 1 y) m x
          (fun j => n (extendLastEquiv (shiftEquivC r m) j)) := by
  induction m generalizing x with
  | zero =>
    funext n
    simp only [shiftEquivC, extendLastEquiv_refl, iterCovCompU_zero, Equiv.refl_apply]
  | succ m ih =>
    funext n
    rw [iterCovCompU_succ,
      show iterCovCompU (I := I) frame chr base (m + 1) =
          (fun y (nn : Fin (r + (m + 1) + 1) → Idx) =>
            iterCovCompU (I := I) frame chr (fun z => iterCovCompU (I := I) frame chr base 1 z) m y
              (fun j => nn (extendLastEquiv (shiftEquivC r m) j))) from funext ih,
      show frameExtData (I := I) frame
            (fun y (nn : Fin (r + (m + 1) + 1) → Idx) =>
              iterCovCompU (I := I) frame chr (fun z => iterCovCompU (I := I) frame chr base 1 z) m y
                (fun j => nn (extendLastEquiv (shiftEquivC r m) j))) x =
          fun (m' : Fin (r + (m + 1) + 1) → Idx) d =>
            frameExtData (I := I) frame
              (iterCovCompU (I := I) frame chr
                (fun z => iterCovCompU (I := I) frame chr base 1 z) m) x
              (fun i => m' (extendLastEquiv (shiftEquivC r m) i)) d from rfl,
      covDerivStepCompU_compReindex (shiftEquivC r m), ← iterCovCompU_succ,
      extendLast_frontExtend_comm]
    rfl

/-- Norm-level upper-tower shift: `|∇_U^{m+1} base| = |∇_U^m (∇_U base)|`. -/
theorem compL2_iterCovCompU_shift {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) (m : ℕ) (x : M) :
    compL2 (iterCovCompU (I := I) frame chr base (m + 1) x) =
      compL2 (iterCovCompU (I := I) frame chr
        (fun y => iterCovCompU (I := I) frame chr base 1 y) m x) := by
  rw [iterCovCompU_shift]
  exact compL2_comp_equiv
    (iterCovCompU (I := I) frame chr (fun y => iterCovCompU (I := I) frame chr base 1 y) m x)
    (extendLastEquiv (shiftEquivC r m))

/-! ## The frameExtData product rule for the natural contraction (the field-level `hext`) -/

/-- **The frame directional derivative of a natural contraction is the Leibniz sum.**
This is the field-level `hext` that discharges the hypothesis of the tower single-step
`covDerivStepCompU_contrTail_leibniz`: the directional derivative of `contrTail (A ·) (B ·)`
splits by the product rule (`extDerivFun_finset_sum_mul_at`), with the directional
derivatives of the two factors becoming `frameExtData A`/`frameExtData B`.  Requires
component-wise manifold-differentiability of the two fields at `x`. -/
theorem frameExtData_contrTail {p q : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (x : M)
    (hA : ∀ m : Fin (p + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => A y m) x)
    (hB : ∀ m : Fin (q + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => B y m) x)
    (idx : Fin (p + q) → Idx) (d : Idx) :
    frameExtData (I := I) frame (fun y : M => contrTail (A y) (B y)) x idx d =
      ∑ c : Idx,
        (frameExtData (I := I) frame A x
              (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) d *
            B x (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) +
          A x (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) *
            frameExtData (I := I) frame B x
              (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) d) := by
  classical
  unfold frameExtData
  rw [show (fun y : M => contrTail (A y) (B y) idx) =
      (fun y : M => ∑ c : Idx,
        A y (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) *
          B y (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c)) from by
    funext y; rw [contrTail_apply]]
  rw [extDerivFun_finset_sum_mul_at (I := I) Finset.univ
    (fun c y => A y (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c))
    (fun c y => B y (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c))
    (frame d x)
    (fun c _ => hA (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c))
    (fun c _ => hB (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c))]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- `frameExtData` is additive in the (differentiable) base field.  The `∂`-part of
`covDerivStepComp`'s linearity, the field-level analogue used by the bottom-pull m-fold
induction. -/
theorem frameExtData_add {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (f₁ f₂ : M → (Fin r → Idx) → Real) (x : M)
    (hf₁ : ∀ m : Fin r → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => f₁ y m) x)
    (hf₂ : ∀ m : Fin r → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => f₂ y m) x)
    (m : Fin r → Idx) (d : Idx) :
    frameExtData (I := I) frame (fun y k => f₁ y k + f₂ y k) x m d =
      frameExtData (I := I) frame f₁ x m d + frameExtData (I := I) frame f₂ x m d := by
  unfold frameExtData
  rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv I (fun y : M => f₁ y m + f₂ y m) x
      (frame d x),
    DifferentialGeometry.extDerivFun_real_eq_mfderiv I (fun y : M => f₁ y m) x (frame d x),
    DifferentialGeometry.extDerivFun_real_eq_mfderiv I (fun y : M => f₂ y m) x (frame d x),
    show (fun y : M => f₁ y m + f₂ y m) = (fun y : M => f₁ y m) + (fun y : M => f₂ y m) from rfl,
    mfderiv_add (hf₁ m) (hf₂ m)]
  rfl

/-- `frameExtData` is scalar-homogeneous in the (differentiable) base field. -/
theorem frameExtData_smul {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (c : Real) (f : M → (Fin r → Idx) → Real) (x : M)
    (hf : ∀ m : Fin r → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => f y m) x)
    (m : Fin r → Idx) (d : Idx) :
    frameExtData (I := I) frame (fun y k => c * f y k) x m d =
      c * frameExtData (I := I) frame f x m d := by
  unfold frameExtData
  rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv I (fun y : M => c * f y m) x (frame d x),
    DifferentialGeometry.extDerivFun_real_eq_mfderiv I (fun y : M => f y m) x (frame d x),
    show (fun y : M => c * f y m) = c • (fun y : M => f y m) from rfl,
    const_smul_mfderiv (hf m) c]
  rfl

/-! ## Differentiability of the component towers

Each tower level is `extDerivFun` of the previous level along the frame minus
Christoffel corrections, so smoothness on the frame domain propagates by induction:
the analytic input is `contMDiffAt_extDerivFun_apply` (`SmoothSectionsLocal`), the
rest is closure of `ContMDiffOn` under products, finite sums, and differences.  The
`MDifferentiableAt` corollaries discharge the `hA`/`hB` hypotheses of the field-level
single-step (`covDerivStepComp_frameExtData_contrTail`) at every tower level. -/

private theorem contMDiffOn_finsetSum {ι : Type*} {u : Set M} (t : Finset ι)
    (F : ι → M → Real)
    (hF : ∀ i ∈ t, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (F i) u) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => ∑ i ∈ t, F i y) u := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using contMDiffOn_const (c := (0 : ℝ))
  | insert a s has ih =>
    have hsum : (fun y => ∑ i ∈ insert a s, F i y) =
        fun y => F a y + ∑ i ∈ s, F i y := by
      funext y; rw [Finset.sum_insert has]
    rw [hsum]
    exact (hF a (by simp)).add (ih fun i hi => hF i (by simp [hi]))

/-- **Differentiability of the `(0,s)` tower.**  If the frame, the Christoffel data,
and the base components are `C^∞` on the open frame domain `u`, then every level of
`iterCovComp` has `C^∞` components on `u`. -/
theorem iterCovComp_contMDiffOn {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hbase : ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => base y m) u)
    (a : ℕ) :
    ∀ n : Fin (r + a) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => iterCovComp (I := I) frame chr base a y n) u := by
  induction a with
  | zero => exact hbase
  | succ a ih =>
    intro n
    have hstep : (fun y => iterCovComp (I := I) frame chr base (a + 1) y n) =
        fun y =>
          extDerivFun (I := I)
              (fun z => iterCovComp (I := I) frame chr base a z (Fin.tail n)) y
              (frame (n 0) y) -
            ∑ s : Fin (r + a), ∑ p : Idx,
              chr y (n 0) (Fin.tail n s) p *
                iterCovComp (I := I) frame chr base a y
                  (Function.update (Fin.tail n) s p) := by
      funext y
      rw [iterCovComp_succ]
      rfl
    rw [hstep]
    refine ContMDiffOn.sub ?_ ?_
    · intro z hz
      exact (contMDiffAt_extDerivFun_apply hu hz (ih (Fin.tail n))
        (hframe (n 0))).contMDiffWithinAt
    · refine contMDiffOn_finsetSum _ _ fun s _ => ?_
      refine contMDiffOn_finsetSum _ _ fun p _ => ?_
      exact (hchr (n 0) (Fin.tail n s) p).mul (ih (Function.update (Fin.tail n) s p))

/-- **Differentiability of the upper tower.**  Same induction as
`iterCovComp_contMDiffOn` for the `covDerivStepCompU` tower (the upper contracted
slot's `+Γ` correction is one more finite sum of products). -/
theorem iterCovCompU_contMDiffOn {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hbase : ∀ m : Fin (r + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => base y m) u)
    (a : ℕ) :
    ∀ n : Fin ((r + a) + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => iterCovCompU (I := I) frame chr base a y n) u := by
  induction a with
  | zero => exact hbase
  | succ a ih =>
    intro n
    have hstep : (fun y => iterCovCompU (I := I) frame chr base (a + 1) y n) =
        fun y =>
          extDerivFun (I := I)
              (fun z => iterCovCompU (I := I) frame chr base a z (Fin.tail n)) y
              (frame (n 0) y) -
            ∑ j : Fin (r + a), ∑ c : Idx,
              chr y (n 0) (Fin.tail n (Fin.castSucc j)) c *
                iterCovCompU (I := I) frame chr base a y
                  (Function.update (Fin.tail n) (Fin.castSucc j) c) +
            ∑ c : Idx,
              chr y (n 0) c (Fin.tail n (Fin.last (r + a))) *
                iterCovCompU (I := I) frame chr base a y
                  (Function.update (Fin.tail n) (Fin.last (r + a)) c) := by
      funext y
      rw [iterCovCompU_succ]
      rfl
    rw [hstep]
    refine ContMDiffOn.add (ContMDiffOn.sub ?_ ?_) ?_
    · intro z hz
      exact (contMDiffAt_extDerivFun_apply hu hz (ih (Fin.tail n))
        (hframe (n 0))).contMDiffWithinAt
    · refine contMDiffOn_finsetSum _ _ fun j _ => ?_
      refine contMDiffOn_finsetSum _ _ fun c _ => ?_
      exact (hchr (n 0) (Fin.tail n (Fin.castSucc j)) c).mul
        (ih (Function.update (Fin.tail n) (Fin.castSucc j) c))
    · refine contMDiffOn_finsetSum _ _ fun c _ => ?_
      exact (hchr (n 0) c (Fin.tail n (Fin.last (r + a)))).mul
        (ih (Function.update (Fin.tail n) (Fin.last (r + a)) c))

/-- The `(0,s)` tower's components are `MDifferentiableAt` at every point of the
frame domain — the `hB` input of the field-level single-step at every level. -/
theorem iterCovComp_mdiffAt {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hbase : ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => base y m) u)
    {x : M} (hx : x ∈ u) (a : ℕ) (n : Fin (r + a) → Idx) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => iterCovComp (I := I) frame chr base a y n) x :=
  ((iterCovComp_contMDiffOn hu frame chr base hframe hchr hbase a n).contMDiffAt
    (hu.mem_nhds hx)).mdifferentiableAt (by simp)

/-- The upper tower's components are `MDifferentiableAt` at every point of the
frame domain — the `hA` input of the field-level single-step at every level. -/
theorem iterCovCompU_mdiffAt {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hbase : ∀ m : Fin (r + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => base y m) u)
    {x : M} (hx : x ∈ u) (a : ℕ) (n : Fin ((r + a) + 1) → Idx) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => iterCovCompU (I := I) frame chr base a y n) x :=
  ((iterCovCompU_contMDiffOn hu frame chr base hframe hchr hbase a n).contMDiffAt
    (hu.mem_nhds hx)).mdifferentiableAt (by simp)

/-- `frameExtData` respects germ equality of the differentiated field. -/
private theorem frameExtData_congr_nhds {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    {F₁ F₂ : M → (Fin r → Idx) → Real} {y : M}
    (h : ∀ᶠ z in nhds y, F₁ z = F₂ z) :
    frameExtData (I := I) frame F₁ y = frameExtData (I := I) frame F₂ y := by
  funext m d
  refine extDerivFun_eventuallyEq_congr (I := I) (frame d y) ?_
  filter_upwards [h] with z hz
  rw [hz]

/-- **Field-level linearity of the tower.**  On the smooth frame domain `u`, the `a`-fold
tower of a sum of fields is the sum of the towers.  Induction: the step's `∂`-part splits by
`frameExtData_add` (after a germ-congruence to the summed field, valid since `u` is open and
the levels are smooth, `iterCovComp_mdiffAt`), the Christoffel part by `covDerivStepComp_add`. -/
theorem iterCovComp_add {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (f₁ f₂ : M → (Fin r → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hf₁ : ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => f₁ y m) u)
    (hf₂ : ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => f₂ y m) u)
    (a : ℕ) :
    ∀ y ∈ u, ∀ n : Fin (r + a) → Idx,
      iterCovComp (I := I) frame chr (fun z k => f₁ z k + f₂ z k) a y n =
        iterCovComp (I := I) frame chr f₁ a y n + iterCovComp (I := I) frame chr f₂ a y n := by
  induction a with
  | zero => intro y _ n; rfl
  | succ a ih =>
    intro y hy n
    have hfield : ∀ᶠ z in nhds y,
        iterCovComp (I := I) frame chr (fun z k => f₁ z k + f₂ z k) a z =
          fun k => iterCovComp (I := I) frame chr f₁ a z k +
            iterCovComp (I := I) frame chr f₂ a z k := by
      filter_upwards [hu.mem_nhds hy] with z hz
      funext k; exact ih z hz k
    have hext : frameExtData (I := I) frame
          (iterCovComp (I := I) frame chr (fun z k => f₁ z k + f₂ z k) a) y =
        fun m d => frameExtData (I := I) frame (iterCovComp (I := I) frame chr f₁ a) y m d +
          frameExtData (I := I) frame (iterCovComp (I := I) frame chr f₂ a) y m d := by
      rw [frameExtData_congr_nhds frame hfield]
      funext m d
      exact frameExtData_add frame (iterCovComp (I := I) frame chr f₁ a)
        (iterCovComp (I := I) frame chr f₂ a) y
        (fun m => iterCovComp_mdiffAt hu frame chr f₁ hframe hchr hf₁ hy a m)
        (fun m => iterCovComp_mdiffAt hu frame chr f₂ hframe hchr hf₂ hy a m) m d
    have harr : iterCovComp (I := I) frame chr (fun z k => f₁ z k + f₂ z k) a y =
        fun k => iterCovComp (I := I) frame chr f₁ a y k +
          iterCovComp (I := I) frame chr f₂ a y k := funext (ih y hy)
    rw [iterCovComp_succ, iterCovComp_succ, iterCovComp_succ, hext, harr,
      covDerivStepComp_add]

/-- **Field-level scalar homogeneity of the tower** (mirror of `iterCovComp_add`): on the
smooth frame domain `u`, the `a`-fold tower of `c • f` is `c •` the tower. -/
theorem iterCovComp_smul {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (c : Real) (f : M → (Fin r → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hf : ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => f y m) u)
    (a : ℕ) :
    ∀ y ∈ u, ∀ n : Fin (r + a) → Idx,
      iterCovComp (I := I) frame chr (fun z k => c * f z k) a y n =
        c * iterCovComp (I := I) frame chr f a y n := by
  induction a with
  | zero => intro y _ n; rfl
  | succ a ih =>
    intro y hy n
    have hfield : ∀ᶠ z in nhds y,
        iterCovComp (I := I) frame chr (fun z k => c * f z k) a z =
          fun k => c * iterCovComp (I := I) frame chr f a z k := by
      filter_upwards [hu.mem_nhds hy] with z hz
      funext k; exact ih z hz k
    have hext : frameExtData (I := I) frame
          (iterCovComp (I := I) frame chr (fun z k => c * f z k) a) y =
        fun m d => c * frameExtData (I := I) frame (iterCovComp (I := I) frame chr f a) y m d := by
      rw [frameExtData_congr_nhds frame hfield]
      funext m d
      exact frameExtData_smul frame c (iterCovComp (I := I) frame chr f a) y
        (fun m => iterCovComp_mdiffAt hu frame chr f hframe hchr hf hy a m) m d
    have harr : iterCovComp (I := I) frame chr (fun z k => c * f z k) a y =
        fun k => c * iterCovComp (I := I) frame chr f a y k := funext (ih y hy)
    rw [iterCovComp_succ, iterCovComp_succ, hext, harr, covDerivStepComp_smul]

/-- **The field-level single-step contraction-Leibniz.**  One covariant-derivative step of
the contraction field `y ↦ contrTail (A y) (B y)` (with `ext = frameExtData` of that field)
splits into the upper step on `A` and the lower step on `B`.  This is
`covDerivStepCompU_contrTail_leibniz` (the tower single-step) with its `hext` discharged by
`frameExtData_contrTail`; it is the inductive engine of the m-fold binomial. -/
theorem covDerivStepComp_frameExtData_contrTail {p q : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (x : M)
    (hA : ∀ m : Fin (p + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => A y m) x)
    (hB : ∀ m : Fin (q + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => B y m) x)
    (d : Idx) (aPart : Fin p → Idx) (bPart : Fin q → Idx) :
    covDerivStepComp (frameExtData (I := I) frame (fun y : M => contrTail (A y) (B y)) x)
        (chr x) (contrTail (A x) (B x)) (Fin.cons d (Fin.append aPart bPart)) =
      contrTail (covDerivStepCompU (frameExtData (I := I) frame A x) (chr x) (A x)) (B x)
          (Fin.append (Fin.cons d aPart) bPart) +
        contrTail (A x) (covDerivStepComp (frameExtData (I := I) frame B x) (chr x) (B x))
          (Fin.append aPart (Fin.cons d bPart)) :=
  covDerivStepCompU_contrTail_leibniz
    (frameExtData (I := I) frame A x) (frameExtData (I := I) frame B x)
    (frameExtData (I := I) frame (fun y : M => contrTail (A y) (B y)) x)
    (chr x) (A x) (B x)
    (frameExtData_contrTail (I := I) frame A B x hA hB)
    d aPart bPart

/-- **The field-level single-step contraction-Leibniz, in `compReindex` form** (general
index `n`).  The first covariant derivative of `y ↦ contrTail (A y) (B y)` splits, as a
field, into the upper step on `A` paired with `B` (reindexed by the rank-cast `e₁`, since
`[d,a,b]` is the same word regrouped `(p+1)+q ↔ (p+q)+1`) plus `A` paired with the lower
step on `B` (reindexed by the rotation `rotEquiv` moving the new derivative past the
`A`-block).  This is the field equality the bottom-pull m-fold feeds into
`iterCovComp ⋯ m` after `iterCovComp_shift`. -/
theorem covStep_contrTail_field {p q : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (x : M)
    (hA : ∀ m : Fin (p + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => A y m) x)
    (hB : ∀ m : Fin (q + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => B y m) x) :
    iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) 1 x =
      fun n : Fin (p + q + 1) → Idx =>
        contrTail (iterCovCompU (I := I) frame chr A 1 x) (B x)
            (fun j => n (finCongr (show p + 1 + q = p + q + 1 by omega) j)) +
          contrTail (A x) (iterCovComp (I := I) frame chr B 1 x)
            (fun i => n (rotEquiv p q i)) := by
  funext n
  simp only [iterCovComp_succ, iterCovComp_zero, iterCovCompU_succ, iterCovCompU_zero]
  set d : Idx := n 0 with hd
  set aPart : Fin p → Idx := fun i => Fin.tail n (Fin.castAdd q i) with haP
  set bPart : Fin q → Idx := fun j => Fin.tail n (Fin.natAdd p j) with hbP
  have hn : n = Fin.cons d (Fin.append aPart bPart) := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · rw [Fin.cons_zero]
    · rw [Fin.cons_succ]
      change Fin.tail n i' = Fin.append aPart bPart i'
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i'
      · rw [Fin.append_left]
      · rw [Fin.append_right]
  conv_lhs => rw [hn]
  rw [covDerivStepComp_frameExtData_contrTail frame chr A B x hA hB d aPart bPart,
    slotId1 d aPart bPart, slotId2 d aPart bPart, ← hn]
  simp only [finCongr_apply]

/-! ## The m-fold binomial norm bound `P(m)` (bottom-pull) -/

/-- **Reindex norm-invariance through the tower.**  `compL2` of the `m`-fold tower of a
free-slot-reindexed base field equals `compL2` of the un-reindexed tower (the reindex
`frontExtendIterC e m` is a slot permutation, killed by `compL2_comp_equiv`).  The payoff
of `iterCovComp_compReindex` for the m-fold binomial. -/
theorem compL2_iterCovComp_compReindex {s s' : ℕ} (e : Fin s ≃ Fin s')
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (F : M → (Fin s → Idx) → Real) (m : ℕ) (x : M) :
    compL2 (iterCovComp (I := I) frame chr
        (fun y (nn : Fin s' → Idx) => F y (fun i => nn (e i))) m x) =
      compL2 (iterCovComp (I := I) frame chr F m x) := by
  rw [iterCovComp_compReindex]
  exact compL2_comp_equiv (iterCovComp (I := I) frame chr F m x) (frontExtendIterC e m)

/-- **Germ-congruence of the tower.**  Two base fields agreeing on the open `u` have equal
`m`-fold towers at every point of `u` (the step's `∂`-part only sees the germ,
`frameExtData_congr_nhds`; the Christoffel part only the value).  Used to replace the inner
single-derivative field by its single-step expansion (valid on `u`). -/
theorem iterCovComp_congr_on {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    {F₁ F₂ : M → (Fin r → Idx) → Real}
    (h : ∀ y ∈ u, F₁ y = F₂ y) (a : ℕ) :
    ∀ x ∈ u, iterCovComp (I := I) frame chr F₁ a x = iterCovComp (I := I) frame chr F₂ a x := by
  induction a with
  | zero => intro x hx; exact h x hx
  | succ a ih =>
    intro x hx
    have hfield : ∀ᶠ z in nhds x, iterCovComp (I := I) frame chr F₁ a z =
        iterCovComp (I := I) frame chr F₂ a z := by
      filter_upwards [hu.mem_nhds hx] with z hz
      exact ih z hz
    rw [iterCovComp_succ, iterCovComp_succ, frameExtData_congr_nhds frame hfield, ih x hx]

/-- The natural contraction of two fields with smooth components is smooth on `u`
(`contrTail` is a finite sum of products of components). -/
theorem contMDiffOn_contrTail {p q : ℕ} {u : Set M}
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (hA : ∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    (hB : ∀ k : Fin (q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) u)
    (m : Fin (p + q) → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => contrTail (A y) (B y) m) u := by
  classical
  rw [show (fun y => contrTail (A y) (B y) m) =
      (fun y => ∑ c : Idx, A y (Fin.snoc (fun i : Fin p => m (Fin.castAdd q i)) c) *
        B y (Fin.snoc (fun j : Fin q => m (Fin.natAdd p j)) c)) from by funext y; rw [contrTail_apply]]
  exact contMDiffOn_finsetSum Finset.univ _ (fun c _ => (hA _).mul (hB _))

/-- **`P(m)`: the m-fold binomial `ℓ²` bound for the natural contraction** (bottom-pull).
On the smooth frame domain `u`, `|∇^m(A ∗ B)| ≤ ∑_c (m choose c) |∇_U^c A| |∇^{m-c} B|`
(component `compL2` norms; `∇_U` is the upper tower of `A`, `∇` the tower of `B`).  Proof:
shift the bottom derivative (`compL2_iterCovComp_shift`), split it by the field single-step
(`covStep_contrTail_field`, valid on `u` via `iterCovComp_congr_on`), split the tower by
linearity (`iterCovComp_add` + `compL2_add_le`), kill the slot reindexes
(`compL2_iterCovComp_compReindex`), recurse on the two halves (each tower-shifted by
`compL2_iterCov*_shift`), and close with `pascal_sum`.  Universally quantified over the two
fields (the recursion changes them). -/
theorem compL2_iterCovComp_contrTail_le {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (m : ℕ) : ∀ {p q : ℕ}
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real),
    (∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u) →
    (∀ k : Fin (q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) u) →
    ∀ {x : M}, x ∈ u →
    compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) m x) ≤
      ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
        compL2 (iterCovCompU (I := I) frame chr A c x) *
        compL2 (iterCovComp (I := I) frame chr B (m - c) x) := by
  induction m with
  | zero =>
    intro p q A B _ _ x _
    rw [Finset.sum_range_one]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero,
      iterCovComp_zero, iterCovCompU_zero]
    exact compL2_contrTail_le (A x) (B x)
  | succ m ih =>
    intro p q A B hA hB x hx
    -- The two recursed fields' component smoothness on `u`.
    have hAU : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => iterCovCompU (I := I) frame chr A 1 y k) u :=
      iterCovCompU_contMDiffOn hu frame chr A hframe hchr hA 1
    have hB1 : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => iterCovComp (I := I) frame chr B 1 y k) u :=
      iterCovComp_contMDiffOn hu frame chr B hframe hchr hB 1
    -- Abbreviate the two branch contraction fields `HL = ∇_U A ∗ B`, `HR = A ∗ ∇B`, and their
    -- reindexed forms `LF`, `RF` (the field single-step output), so the calc stays small-term.
    set HL : M → (Fin (p + 1 + q) → Idx) → Real :=
      fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (B z) with hHL
    set HR : M → (Fin (p + (q + 1)) → Idx) → Real :=
      fun z => contrTail (A z) (iterCovComp (I := I) frame chr B 1 z) with hHR
    set LF : M → (Fin (p + q + 1) → Idx) → Real :=
      fun y nn => HL y (fun j => nn (finCongr (show p + 1 + q = p + q + 1 by omega) j)) with hLF
    set RF : M → (Fin (p + q + 1) → Idx) → Real :=
      fun y nn => HR y (fun i => nn (rotEquiv p q i)) with hRF
    have hLsm : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => LF y k) u := by
      intro k; simp only [hLF, hHL]; exact contMDiffOn_contrTail _ _ hAU hB _
    have hRsm : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => RF y k) u := by
      intro k; simp only [hRF, hHR]; exact contMDiffOn_contrTail _ _ hA hB1 _
    -- The field single-step, valid on `u`: `∇(A∗B) = LF + RF` (reindexed branch fields).
    have hsplit : ∀ y ∈ u, iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) 1 y =
        fun nn => LF y nn + RF y nn := by
      intro y hy
      rw [covStep_contrTail_field frame chr A B y
        (fun k => ((hA k).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt (by simp))
        (fun k => ((hB k).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt (by simp))]
    -- L-branch: bound `|∇^m(∇_U A ∗ B)|` by IH on `(∇_U A, B)`, then shift the A-tower norm.
    have hL : compL2 (iterCovComp (I := I) frame chr HL m x) ≤
        ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A (c + 1) x) *
          compL2 (iterCovComp (I := I) frame chr B (m - c) x) := by
      rw [hHL]
      refine le_trans (ih (fun y => iterCovCompU (I := I) frame chr A 1 y) B hAU hB hx)
        (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [compL2_iterCovCompU_shift frame chr A c x]
    -- R-branch: bound `|∇^m(A ∗ ∇B)|` by IH on `(A, ∇B)`, then shift the B-tower norm.
    have hR : compL2 (iterCovComp (I := I) frame chr HR m x) ≤
        ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr B (m - c + 1) x) := by
      rw [hHR]
      refine le_trans (ih A (fun y => iterCovComp (I := I) frame chr B 1 y) hA hB1 hx)
        (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [compL2_iterCovComp_shift frame chr B (m - c) x]
    -- Assemble: shift, single-step (on `u`), linearity, reindex, then the two branches + Pascal.
    calc compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) (m + 1) x)
        = compL2 (iterCovComp (I := I) frame chr
            (fun y => iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) 1 y) m x) :=
          compL2_iterCovComp_shift frame chr (fun z => contrTail (A z) (B z)) m x
      _ = compL2 (iterCovComp (I := I) frame chr (fun y nn => LF y nn + RF y nn) m x) :=
          congrArg compL2 (iterCovComp_congr_on hu frame chr hsplit m x hx)
      _ = compL2 (fun n : Fin (p + q + 1 + m) → Idx =>
            iterCovComp (I := I) frame chr LF m x n + iterCovComp (I := I) frame chr RF m x n) :=
          congrArg compL2 (funext fun n =>
            iterCovComp_add hu frame chr LF RF hframe hchr hLsm hRsm m x hx n)
      _ ≤ compL2 (iterCovComp (I := I) frame chr LF m x) +
          compL2 (iterCovComp (I := I) frame chr RF m x) := compL2_add_le _ _
      _ = compL2 (iterCovComp (I := I) frame chr HL m x) +
          compL2 (iterCovComp (I := I) frame chr HR m x) := by
          rw [hLF, hRF,
            compL2_iterCovComp_compReindex (finCongr (show p + 1 + q = p + q + 1 by omega))
              frame chr HL m x,
            compL2_iterCovComp_compReindex (rotEquiv p q) frame chr HR m x]
      _ ≤ (∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
              compL2 (iterCovCompU (I := I) frame chr A (c + 1) x) *
              compL2 (iterCovComp (I := I) frame chr B (m - c) x)) +
            ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
              compL2 (iterCovCompU (I := I) frame chr A c x) *
              compL2 (iterCovComp (I := I) frame chr B (m - c + 1) x) := add_le_add hL hR
      _ = ∑ c ∈ Finset.range (m + 1 + 1), ((m + 1).choose c : Real) *
            (compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr B (m + 1 - c) x)) := by
          rw [← pascal_sum m (fun c => compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr B (m + 1 - c) x))]
          congr 1
          · refine Finset.sum_congr rfl fun c _ => ?_
            have hsub : m + 1 - (c + 1) = m - c := by omega
            rw [hsub]; ring
          · refine Finset.sum_congr rfl fun c hc => ?_
            have hsub : m - c + 1 = m + 1 - c := by
              simp only [Finset.mem_range] at hc; omega
            rw [hsub]; ring
      _ = ∑ c ∈ Finset.range (m + 1 + 1), ((m + 1).choose c : Real) *
            compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr B (m + 1 - c) x) :=
          Finset.sum_congr rfl fun c _ => (mul_assoc _ _ _).symm

/-! ## The bottom-pull array IDENTITY (the linchpin of `ISO(m)`) -/

/-- **The bottom-pull array identity** (`P(m)`'s calc steps 1-3+5 kept as an `=`, not `≤`):
on the open `u`, the `(m+1)`-fold tower of `A∗B` splits into the `m`-fold towers of the two
branch contractions `(∇_U A)∗B` and `A∗(∇B)`, each precomposed by an explicit slot reindex.
The reindexes are the bottom-pull composites `frontExtendIterC e ▸ shiftEquivC` (`e = finCongr`
for the A-branch, `e = rotEquiv` for the B-branch).  This is the identity `ISO(m)`'s residual
recursion differences across (the `(∇_U^{m+1}A)∗g` terms cancel against the recursive `Top`). -/
theorem iterCovComp_contrTail_succ {p q : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (hA : ∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    (hB : ∀ k : Fin (q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) u)
    (m : ℕ) {x : M} (hx : x ∈ u) :
    iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) (m + 1) x =
      fun n : Fin (p + q + (m + 1)) → Idx =>
        iterCovComp (I := I) frame chr
            (fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (B z)) m x
            (fun j => n ((frontExtendIterC (finCongr (show p + 1 + q = p + q + 1 by omega)) m).trans
              (shiftEquivC (p + q) m) j)) +
          iterCovComp (I := I) frame chr
            (fun z => contrTail (A z) (iterCovComp (I := I) frame chr B 1 z)) m x
            (fun j => n ((frontExtendIterC (rotEquiv p q) m).trans (shiftEquivC (p + q) m) j)) := by
    set HL : M → (Fin (p + 1 + q) → Idx) → Real :=
      fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (B z) with hHL
    set HR : M → (Fin (p + (q + 1)) → Idx) → Real :=
      fun z => contrTail (A z) (iterCovComp (I := I) frame chr B 1 z) with hHR
    set LF : M → (Fin (p + q + 1) → Idx) → Real :=
      fun y nn => HL y (fun j => nn (finCongr (show p + 1 + q = p + q + 1 by omega) j)) with hLF
    set RF : M → (Fin (p + q + 1) → Idx) → Real :=
      fun y nn => HR y (fun i => nn (rotEquiv p q i)) with hRF
    have hLsm : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => LF y k) u := by
      intro k; simp only [hLF, hHL]; exact contMDiffOn_contrTail _ _
        (iterCovCompU_contMDiffOn hu frame chr A hframe hchr hA 1) hB _
    have hRsm : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => RF y k) u := by
      intro k; simp only [hRF, hHR]; exact contMDiffOn_contrTail _ _
        hA (iterCovComp_contMDiffOn hu frame chr B hframe hchr hB 1) _
    have hsplit : ∀ y ∈ u, iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) 1 y =
        fun nn => LF y nn + RF y nn := by
      intro y hy
      rw [covStep_contrTail_field frame chr A B y
        (fun k => ((hA k).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt (by simp))
        (fun k => ((hB k).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt (by simp))]
    rw [iterCovComp_shift frame chr (fun z => contrTail (A z) (B z)) m x]
    funext n
    rw [iterCovComp_congr_on hu frame chr hsplit m x hx,
      iterCovComp_add hu frame chr LF RF hframe hchr hLsm hRsm m x hx,
      hLF, hRF, iterCovComp_compReindex (finCongr (show p + 1 + q = p + q + 1 by omega)) frame chr HL m x,
      iterCovComp_compReindex (rotEquiv p q) frame chr HR m x]
    simp only [Equiv.trans_apply]

/-! ## `ISO(m)`: the residual (isolated-top) bound -/

/-- The bottom-pull L-branch reindex (the composite from `iterCovComp_contrTail_succ`). -/
def isoReindex (p q m : ℕ) : Fin (p + 1 + q + m) ≃ Fin (p + q + (m + 1)) :=
  (frontExtendIterC (finCongr (show p + 1 + q = p + q + 1 by omega)) m).trans (shiftEquivC (p + q) m)

/-- **The recursively-isolated top term** `Top_m[A] ≈ (∇_U^m A)∗g`, defined to MATCH the
bottom-pull L-branch reindex (so `ISO(m)`'s recursion `D_{m+1} = D_m[∇_U A]∘e_L + ∇^m(A∗∇g)∘e_R`
holds with NO U-shift bookkeeping — that is deferred to the inversion step `isoTop_eq`). -/
def isoTop {q : ℕ} (g : M → (Fin (q + 1) → Idx) → Real)
    (frame : Idx → (x : M) → TangentSpace I x) (chr : M → Idx → Idx → Idx → Real) :
    (m : ℕ) → {p : ℕ} → (A : M → (Fin (p + 1) → Idx) → Real) → (x : M) →
      (Fin (p + q + m) → Idx) → Real
  | 0, p, A, x => contrTail (p := p) (q := q) (A x) (g x)
  | (m + 1), p, A, x => fun n =>
      isoTop g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x
        (fun j => n (isoReindex p q m j))

@[simp] theorem isoTop_zero {q : ℕ} (g : M → (Fin (q + 1) → Idx) → Real)
    (frame : Idx → (x : M) → TangentSpace I x) (chr : M → Idx → Idx → Idx → Real)
    {p : ℕ} (A : M → (Fin (p + 1) → Idx) → Real) (x : M) :
    isoTop (I := I) g frame chr 0 A x = contrTail (A x) (g x) := rfl

@[simp] theorem isoTop_succ {q : ℕ} (g : M → (Fin (q + 1) → Idx) → Real)
    (frame : Idx → (x : M) → TangentSpace I x) (chr : M → Idx → Idx → Idx → Real)
    {p : ℕ} (A : M → (Fin (p + 1) → Idx) → Real) (m : ℕ) (x : M) :
    isoTop (I := I) g frame chr (m + 1) A x =
      fun n => isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x
        (fun j => n (isoReindex p q m j)) := rfl

/-- **`ISO(m)`: the residual bound.**  The deviation of the `m`-fold tower of the
contraction from the recursively-isolated top word `isoTop ≈ (∇_U^m A)∗g` is bounded by
the binomial sum WITHOUT its top (`c = m`) term — the isolation that powers the
invert-trick.  Bottom-pull: the `(m+1)`-residual decomposes (via the array identity
`iterCovComp_contrTail_succ` and `isoTop`'s matching reindex) into the `m`-residual of
`∇_U A` plus the FULL `m`-binomial of `(A, ∇g)` (`P(m)`); `pascal_sum_notop` reassembles. -/
theorem compL2_isoResidual_le {q : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (g : M → (Fin (q + 1) → Idx) → Real)
    (hg : ∀ k : Fin (q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u)
    (m : ℕ) : ∀ {p : ℕ}
    (A : M → (Fin (p + 1) → Idx) → Real),
    (∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u) →
    ∀ {x : M}, x ∈ u →
    compL2 (fun n : Fin (p + q + m) → Idx =>
        iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m x n -
          isoTop (I := I) g frame chr m A x n) ≤
      ∑ c ∈ Finset.range m, (m.choose c : Real) *
        compL2 (iterCovCompU (I := I) frame chr A c x) *
        compL2 (iterCovComp (I := I) frame chr g (m - c) x) := by
  induction m with
  | zero =>
    intro p A _ x _
    rw [Finset.sum_range_zero]
    have hzero : (fun n : Fin (p + q + 0) → Idx =>
        iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) 0 x n -
          isoTop (I := I) g frame chr 0 A x n) = fun _ => (0 : Real) := by
      funext n
      rw [iterCovComp_zero, isoTop_zero]
      exact sub_self _
    rw [hzero]
    simp [compL2, compL2Sq]
  | succ m ih =>
    intro p A hA x hx
    have hAU : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => iterCovCompU (I := I) frame chr A 1 y k) u :=
      iterCovCompU_contMDiffOn hu frame chr A hframe hchr hA 1
    have hg1 : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => iterCovComp (I := I) frame chr g 1 y k) u :=
      iterCovComp_contMDiffOn hu frame chr g hframe hchr hg 1
    -- the array decomposition `D_{m+1} = D_m[∇_U A]∘ψ + ∇^m(A∗∇g)∘ψ_R`
    have hdec : (fun n : Fin (p + q + (m + 1)) → Idx =>
        iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) (m + 1) x n -
          isoTop (I := I) g frame chr (m + 1) A x n) =
        fun n =>
          (iterCovComp (I := I) frame chr
              (fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (g z)) m x
              (fun j => n (isoReindex p q m j)) -
            isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x
              (fun j => n (isoReindex p q m j))) +
          iterCovComp (I := I) frame chr
              (fun z => contrTail (A z) (iterCovComp (I := I) frame chr g 1 z)) m x
              (fun j => n ((frontExtendIterC (rotEquiv p q) m).trans (shiftEquivC (p + q) m) j)) := by
      funext n
      rw [iterCovComp_contrTail_succ hu frame chr hframe hchr A g hA hg m hx, isoTop_succ]
      exact add_sub_right_comm _ _ _
    rw [hdec]
    refine le_trans (compL2_add_le _ _) ?_
    have hψ : compL2 (fun n : Fin (p + q + (m + 1)) → Idx =>
          iterCovComp (I := I) frame chr
              (fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (g z)) m x
              (fun j => n (isoReindex p q m j)) -
            isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x
              (fun j => n (isoReindex p q m j))) =
        compL2 (fun nn : Fin (p + 1 + q + m) → Idx =>
          iterCovComp (I := I) frame chr
              (fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (g z)) m x nn -
            isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x nn) :=
      compL2_comp_equiv
        (fun nn : Fin (p + 1 + q + m) → Idx =>
          iterCovComp (I := I) frame chr
              (fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (g z)) m x nn -
            isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x nn)
        (isoReindex p q m)
    have hψR : compL2 (fun n : Fin (p + q + (m + 1)) → Idx =>
          iterCovComp (I := I) frame chr
              (fun z => contrTail (A z) (iterCovComp (I := I) frame chr g 1 z)) m x
              (fun j => n ((frontExtendIterC (rotEquiv p q) m).trans (shiftEquivC (p + q) m) j))) =
        compL2 (iterCovComp (I := I) frame chr
          (fun z => contrTail (A z) (iterCovComp (I := I) frame chr g 1 z)) m x) :=
      compL2_comp_equiv
        (iterCovComp (I := I) frame chr
          (fun z => contrTail (A z) (iterCovComp (I := I) frame chr g 1 z)) m x)
        ((frontExtendIterC (rotEquiv p q) m).trans (shiftEquivC (p + q) m))
    rw [hψ, hψR]
    -- L: the ISO induction hypothesis at `∇_U A`, then shift the A-tower norms
    have hL : compL2 (fun nn : Fin (p + 1 + q + m) → Idx =>
          iterCovComp (I := I) frame chr
              (fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (g z)) m x nn -
            isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x nn) ≤
        ∑ c ∈ Finset.range m, (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A (c + 1) x) *
          compL2 (iterCovComp (I := I) frame chr g (m - c) x) := by
      refine le_trans (ih (fun y => iterCovCompU (I := I) frame chr A 1 y) hAU hx)
        (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [compL2_iterCovCompU_shift frame chr A c x]
    -- R: `P(m)` at `(A, ∇g)`, then shift the g-tower norms
    have hR : compL2 (iterCovComp (I := I) frame chr
          (fun z => contrTail (A z) (iterCovComp (I := I) frame chr g 1 z)) m x) ≤
        ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m - c + 1) x) := by
      refine le_trans (compL2_iterCovComp_contrTail_le hu frame chr hframe hchr m A
        (fun y => iterCovComp (I := I) frame chr g 1 y) hA hg1 hx) (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [compL2_iterCovComp_shift frame chr g (m - c) x]
    refine le_trans (add_le_add hL hR) (le_of_eq ?_)
    -- Pascal without the top term
    have hregroup : (∑ c ∈ Finset.range (m + 1), ((m + 1).choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m + 1 - c) x)) =
        ∑ c ∈ Finset.range (m + 1), ((m + 1).choose c : Real) *
          (compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m + 1 - c) x)) :=
      Finset.sum_congr rfl fun c _ => mul_assoc _ _ _
    rw [hregroup,
      ← pascal_sum_notop m (fun c => compL2 (iterCovCompU (I := I) frame chr A c x) *
        compL2 (iterCovComp (I := I) frame chr g (m + 1 - c) x))]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      have hsub : m + 1 - (c + 1) = m - c := by omega
      rw [hsub]; ring
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hsub : m - c + 1 = m + 1 - c := by
        simp only [Finset.mem_range] at hc; omega
      rw [hsub]; ring

/-! ## Identifying `isoTop` with the honest top word `(∇_U^m A)∗g` (norm level) -/

/-- Block extension of a slot equiv: act as `e₀` on the first (castAdd) block, identity on
the second (natAdd) block. -/
def blockLeftEquiv {a a' : ℕ} (e₀ : Fin a ≃ Fin a') (b : ℕ) : Fin (a + b) ≃ Fin (a' + b) :=
  finSumFinEquiv.symm.trans ((e₀.sumCongr (Equiv.refl (Fin b))).trans finSumFinEquiv)

@[simp] theorem blockLeftEquiv_castAdd {a a' : ℕ} (e₀ : Fin a ≃ Fin a') (b : ℕ) (i : Fin a) :
    blockLeftEquiv e₀ b (Fin.castAdd b i) = Fin.castAdd b (e₀ i) := by
  simp [blockLeftEquiv]

@[simp] theorem blockLeftEquiv_natAdd {a a' : ℕ} (e₀ : Fin a ≃ Fin a') (b : ℕ) (j : Fin b) :
    blockLeftEquiv e₀ b (Fin.natAdd a j) = Fin.natAdd a' j := by
  simp [blockLeftEquiv]

/-- `contrTail` intertwines a last-slot-fixing reindex of its FIRST factor with the block
reindex of the contraction (the contracted slot is untouched, the free `A`-block moves by
`e₀`, the `B`-block stays). -/
theorem contrTail_extendLast {pT pF q : ℕ} (e₀ : Fin pT ≃ Fin pF)
    (T : (Fin (pT + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real) :
    contrTail (fun n : Fin (pF + 1) → Idx => T (fun j => n (extendLastEquiv e₀ j))) B =
      fun idx : Fin (pF + q) → Idx =>
        contrTail T B (fun j => idx (blockLeftEquiv e₀ q j)) := by
  funext idx
  rw [contrTail_apply, contrTail_apply]
  have hAvec : (fun i : Fin pT => idx (blockLeftEquiv e₀ q (Fin.castAdd q i))) =
      fun i => idx (Fin.castAdd q (e₀ i)) := by
    funext i; rw [blockLeftEquiv_castAdd]
  have hBvec : (fun j : Fin q => idx (blockLeftEquiv e₀ q (Fin.natAdd pT j))) =
      fun j => idx (Fin.natAdd pF j) := by
    funext j; rw [blockLeftEquiv_natAdd]
  rw [hAvec, hBvec]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [extendLastEquiv_last, Fin.snoc_last, Fin.snoc_last]
  · rw [extendLastEquiv_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- **`isoTop` is the honest top word, in norm**: `|isoTop_m[A]| = |(∇_U^m A)∗g|`.  The
recursive reindexes are slot permutations (`compL2_comp_equiv`); the U-tower shift enters
through the first factor of `contrTail` via `contrTail_extendLast`. -/
theorem compL2_isoTop_eq {q : ℕ}
    (g : M → (Fin (q + 1) → Idx) → Real)
    (frame : Idx → (x : M) → TangentSpace I x) (chr : M → Idx → Idx → Idx → Real)
    (m : ℕ) : ∀ {p : ℕ} (A : M → (Fin (p + 1) → Idx) → Real) (x : M),
    compL2 (isoTop (I := I) g frame chr m A x) =
      compL2 (contrTail (iterCovCompU (I := I) frame chr A m x) (g x)) := by
  induction m with
  | zero => intro p A x; rfl
  | succ m ih =>
    intro p A x
    rw [isoTop_succ,
      show compL2 (fun n : Fin (p + q + (m + 1)) → Idx =>
          isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x
            (fun j => n (isoReindex p q m j))) =
        compL2 (isoTop (I := I) g frame chr m
          (fun z => iterCovCompU (I := I) frame chr A 1 z) x) from
        compL2_comp_equiv
          (isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x)
          (isoReindex p q m),
      ih (fun z => iterCovCompU (I := I) frame chr A 1 z) x,
      show contrTail (iterCovCompU (I := I) frame chr A (m + 1) x) (g x) =
        fun idx : Fin (p + (m + 1) + q) → Idx =>
          contrTail (iterCovCompU (I := I) frame chr
              (fun y => iterCovCompU (I := I) frame chr A 1 y) m x) (g x)
            (fun j => idx (blockLeftEquiv (shiftEquivC p m) q j)) from by
        rw [iterCovCompU_shift frame chr A m x, contrTail_extendLast]]
    exact (compL2_comp_equiv
      (contrTail (iterCovCompU (I := I) frame chr
        (fun y => iterCovCompU (I := I) frame chr A 1 y) m x) (g x))
      (blockLeftEquiv (shiftEquivC p m) q)).symm

/-- **The isolated-top bound**: `|(∇_U^m A)∗g| ≤ |∇^m(A∗g)| + (the no-top binomial)`.
`isoTop = ∇^m(A∗g) − D_m`, so triangle (`compL2_sub_le`) + `ISO(m)` + `compL2_isoTop_eq`. -/
theorem compL2_contrTail_topU_le {q : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (g : M → (Fin (q + 1) → Idx) → Real)
    (hg : ∀ k : Fin (q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u)
    (m : ℕ) {p : ℕ}
    (A : M → (Fin (p + 1) → Idx) → Real)
    (hA : ∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    {x : M} (hx : x ∈ u) :
    compL2 (contrTail (iterCovCompU (I := I) frame chr A m x) (g x)) ≤
      compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m x) +
        ∑ c ∈ Finset.range m, (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m - c) x) := by
  rw [← compL2_isoTop_eq g frame chr m A x,
    show isoTop (I := I) g frame chr m A x =
      fun n : Fin (p + q + m) → Idx =>
        iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m x n -
          (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m x n -
            isoTop (I := I) g frame chr m A x n) from
      funext fun n => (sub_sub_cancel _ _).symm]
  exact le_trans (compL2_sub_le _ _)
    (add_le_add le_rfl (compL2_isoResidual_le hu frame chr hframe hchr g hg m A hA hx))

/-! ## The inverse-metric cancellation and the invert bound -/

/-- **The inverse cancellation**: contracting `T∗G` back with the inverse array recovers
`T` — `(T∗G)∗Ginv = T` when `∑_l G[l,c]·Ginv[e,l] = δ_{ce}` (the only fact about the
inverse metric the whole Claim-1 chain uses; no `∇Ginv` ever appears). -/
theorem contrTail_contrTail_inv {P : ℕ}
    (T : (Fin (P + 1) → Idx) → Real) (G Ginv : (Fin (1 + 1) → Idx) → Real)
    (hinv : ∀ c e : Idx,
      (∑ l : Idx, G (Fin.snoc (fun _ : Fin 1 => l) c) * Ginv (Fin.snoc (fun _ : Fin 1 => e) l)) =
        if c = e then 1 else 0) :
    contrTail (contrTail T G) Ginv = T := by
  classical
  funext v
  rw [contrTail_apply]
  have hinner : ∀ l : Idx,
      contrTail T G (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) l) =
        ∑ c : Idx, T (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) c) *
          G (Fin.snoc (fun _ : Fin 1 => l) c) := by
    intro l
    rw [contrTail_apply]
    have h1 : (fun i : Fin P =>
        (Fin.snoc (fun i' : Fin P => v (Fin.castAdd 1 i')) l : Fin (P + 1) → Idx)
          (Fin.castAdd 1 i)) = fun i : Fin P => v (Fin.castAdd 1 i) := by
      funext i
      rw [show (Fin.castAdd 1 i : Fin (P + 1)) = Fin.castSucc i from rfl, Fin.snoc_castSucc]
      rfl
    have h2 : (fun j : Fin 1 =>
        (Fin.snoc (fun i' : Fin P => v (Fin.castAdd 1 i')) l : Fin (P + 1) → Idx)
          (Fin.natAdd P j)) = fun _ : Fin 1 => l := by
      funext j
      rw [show (Fin.natAdd P j : Fin (P + 1)) = Fin.last P from
          Fin.ext (by simp [Subsingleton.elim j (0 : Fin 1)]),
        Fin.snoc_last]
    rw [h1, h2]
  simp only [hinner]
  have hvN : (fun j : Fin 1 => v (Fin.natAdd P j)) = fun _ : Fin 1 => v (Fin.natAdd P 0) := by
    funext j; rw [Subsingleton.elim j (0 : Fin 1)]
  rw [hvN]
  calc (∑ l : Idx, (∑ c : Idx, T (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) c) *
            G (Fin.snoc (fun _ : Fin 1 => l) c)) *
          Ginv (Fin.snoc (fun _ : Fin 1 => v (Fin.natAdd P 0)) l))
      = ∑ c : Idx, T (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) c) *
          (∑ l : Idx, G (Fin.snoc (fun _ : Fin 1 => l) c) *
            Ginv (Fin.snoc (fun _ : Fin 1 => v (Fin.natAdd P 0)) l)) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ c : Idx, T (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) c) *
          (if c = v (Fin.natAdd P 0) then 1 else 0) :=
        Finset.sum_congr rfl fun c _ => by rw [hinv c (v (Fin.natAdd P 0))]
    _ = T (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) (v (Fin.natAdd P 0))) := by
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ (v (Fin.natAdd P 0))
          (fun c => T (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) c))]
        simp
    _ = T v := by
        congr 1
        funext k
        refine Fin.lastCases ?_ (fun i => ?_) k
        · rw [Fin.snoc_last,
            show (Fin.natAdd P 0 : Fin (P + 1)) = Fin.last P from Fin.ext (by simp)]
        · rw [Fin.snoc_castSucc]
          rfl

/-- **The invert bound**: `|T| ≤ |T∗G|·|Ginv|` (recover `T` by the inverse cancellation,
then the contraction Cauchy–Schwarz). -/
theorem compL2_le_contrTail_inv {P : ℕ}
    (T : (Fin (P + 1) → Idx) → Real) (G Ginv : (Fin (1 + 1) → Idx) → Real)
    (hinv : ∀ c e : Idx,
      (∑ l : Idx, G (Fin.snoc (fun _ : Fin 1 => l) c) * Ginv (Fin.snoc (fun _ : Fin 1 => e) l)) =
        if c = e then 1 else 0) :
    compL2 T ≤ compL2 (contrTail T G) * compL2 Ginv := by
  calc compL2 T = compL2 (contrTail (contrTail T G) Ginv) := by
        rw [contrTail_contrTail_inv T G Ginv hinv]
    _ ≤ compL2 (contrTail T G) * compL2 Ginv := compL2_contrTail_le _ _

/-! ## The abstract Claim 1 -/

/-- The data-independent constant in the abstract Claim 1 induction. -/
noncomputable def claim1Const (C0 KR K : Real) (m : ℕ) : Real :=
  Nat.strongRecOn' m fun n C =>
    max C0 0 * (max KR 0 +
      ∑ c : Fin n, (n.choose c : Real) *
        (C c c.isLt * (1 + max K 0)) * max K 0)

/-- Unfolding equation for `claim1Const`. -/
theorem claim1Const_eq (C0 KR K : Real) (m : ℕ) :
    claim1Const C0 KR K m =
      max C0 0 * (max KR 0 +
        ∑ c ∈ Finset.range m, (m.choose c : Real) *
          (claim1Const C0 KR K c * (1 + max K 0)) * max K 0) := by
  rw [claim1Const, Nat.strongRecOn'_beta, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- The abstract Claim 1 constant is nonnegative. -/
theorem claim1Const_nonneg (C0 KR K : Real) (m : ℕ) :
    0 ≤ claim1Const C0 KR K m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      rw [claim1Const_eq]
      refine mul_nonneg (le_max_right C0 0) (add_nonneg (le_max_right KR 0) ?_)
      exact Finset.sum_nonneg fun c hc =>
        mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (ih c (Finset.mem_range.mp hc)) (by linarith [le_max_right K 0])))
          (le_max_right K 0)

/-- **Abstract Claim 1**: on the smooth frame domain, if the contraction field `A∗g`
norm-realizes the metric derivative up to a constant (`hrelB`, the Koszul/eq-3.7 input:
`|∇^{m'}(A∗g)| ≤ KR·|∇^{m'+1}g|` — geometrically `Ǎ = A∗g` is a constant slot-permutation
combination of `∇g`), `Ginv` is the pointwise inverse array of `g` (`hinv`), and the window
bounds `|Ginv| ≤ C0`, `|∇^j g| ≤ K (1 ≤ j ≤ m)` hold, then
`|∇_U^m A| ≤ C·(1 + |∇^{m+1} g|)` for a constant `C = C(m, C0, KR, K)`.  Strong induction:
invert (`compL2_le_contrTail_inv`) + isolated-top (`compL2_contrTail_topU_le`) + `hrelB`
turn `|∇_U^m A|` into `C0·(KR·|∇^{m+1}g| + Σ_{c<m} binom·|∇_U^c A|·|∇^{m-c}g|)`; the IH
bounds each `|∇_U^c A|`. -/
theorem claim1_abstract_bound {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    {p : ℕ} (C0 KR K : Real) (m : ℕ) :
    ∀ (g : M → (Fin (1 + 1) → Idx) → Real),
      (∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u) →
    ∀ (Ginv : M → (Fin (1 + 1) → Idx) → Real)
      (A : M → (Fin (p + 1) → Idx) → Real),
      (∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u) →
      (∀ x ∈ u, ∀ c e : Idx,
        (∑ l : Idx, g x (Fin.snoc (fun _ : Fin 1 => l) c) *
          Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0) →
      (∀ x ∈ u, compL2 (Ginv x) ≤ C0) →
      (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m →
        compL2 (iterCovComp (I := I) frame chr g j x) ≤ K) →
      (∀ x ∈ u, ∀ m', m' ≤ m →
        compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m' x) ≤
          KR * compL2 (iterCovComp (I := I) frame chr g (m' + 1) x)) →
      ∀ x ∈ u,
        compL2 (iterCovCompU (I := I) frame chr A m x) ≤
          claim1Const C0 KR K m *
            (1 + compL2 (iterCovComp (I := I) frame chr g (m + 1) x)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    classical
    have hK'0 : (0 : Real) ≤ max K 0 := le_max_right K 0
    have hKR0 : (0 : Real) ≤ max KR 0 := le_max_right KR 0
    intro g hg Ginv A hA hinv hGinv hK hrelB x hx
    set S := ∑ c ∈ Finset.range m,
      (m.choose c : Real) * (claim1Const C0 KR K c * (1 + max K 0)) *
        max K 0 with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun c hc =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (claim1Const_nonneg C0 KR K c) (by linarith))) hK'0
    have hgm1 : (0 : Real) ≤ compL2 (iterCovComp (I := I) frame chr g (m + 1) x) :=
      compL2_nonneg _
    -- the relation bound (with the nonneg-ized constant)
    have hrel3 : compL2 (iterCovComp (I := I) frame chr
          (fun z => contrTail (A z) (g z)) m x) ≤
        max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) :=
      le_trans (hrelB x hx m le_rfl)
        (mul_le_mul_of_nonneg_right (le_max_left KR 0) hgm1)
    -- the core chain: invert + isolated top + the relation
    have hcore : compL2 (iterCovCompU (I := I) frame chr A m x) ≤
        compL2 (Ginv x) *
          (max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
          ∑ c ∈ Finset.range m, (m.choose c : Real) *
            compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr g (m - c) x)) := by
      calc compL2 (iterCovCompU (I := I) frame chr A m x)
          ≤ compL2 (contrTail (iterCovCompU (I := I) frame chr A m x) (g x)) *
              compL2 (Ginv x) :=
            compL2_le_contrTail_inv _ (g x) (Ginv x) (hinv x hx)
        _ ≤ (compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m x) +
              ∑ c ∈ Finset.range m, (m.choose c : Real) *
                compL2 (iterCovCompU (I := I) frame chr A c x) *
                compL2 (iterCovComp (I := I) frame chr g (m - c) x)) * compL2 (Ginv x) :=
            mul_le_mul_of_nonneg_right
              (compL2_contrTail_topU_le hu frame chr hframe hchr g hg m A hA hx)
              (compL2_nonneg _)
        _ ≤ (max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
              ∑ c ∈ Finset.range m, (m.choose c : Real) *
                compL2 (iterCovCompU (I := I) frame chr A c x) *
                compL2 (iterCovComp (I := I) frame chr g (m - c) x)) * compL2 (Ginv x) :=
            mul_le_mul_of_nonneg_right (add_le_add hrel3 le_rfl) (compL2_nonneg _)
        _ = compL2 (Ginv x) *
              (max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
              ∑ c ∈ Finset.range m, (m.choose c : Real) *
                compL2 (iterCovCompU (I := I) frame chr A c x) *
                compL2 (iterCovComp (I := I) frame chr g (m - c) x)) := mul_comm _ _
    -- numeric: the lower-order block is ≤ S
    have hsum : (∑ c ∈ Finset.range m, (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m - c) x)) ≤ S := by
      refine Finset.sum_le_sum fun c hc => ?_
      have hc' := Finset.mem_range.mp hc
      have hgc1 : compL2 (iterCovComp (I := I) frame chr g (c + 1) x) ≤ max K 0 :=
        le_trans (hK x hx (c + 1) (by omega) (by omega)) (le_max_left K 0)
      have hAc : compL2 (iterCovCompU (I := I) frame chr A c x) ≤
          claim1Const C0 KR K c * (1 + max K 0) := by
        refine le_trans (ih c hc' g hg Ginv A hA hinv hGinv
          (fun x' hx' j h1 h2 => hK x' hx' j h1 (by omega))
          (fun x' hx' m' h' => hrelB x' hx' m' (by omega)) x hx) ?_
        exact mul_le_mul_of_nonneg_left (by linarith) (claim1Const_nonneg C0 KR K c)
      have hgmc : compL2 (iterCovComp (I := I) frame chr g (m - c) x) ≤ max K 0 :=
        le_trans (hK x hx (m - c) (by omega) (by omega)) (le_max_left K 0)
      calc (m.choose c : Real) * compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr g (m - c) x)
          ≤ (m.choose c : Real) * (claim1Const C0 KR K c * (1 + max K 0)) *
              compL2 (iterCovComp (I := I) frame chr g (m - c) x) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hAc (Nat.cast_nonneg _)) (compL2_nonneg _)
        _ ≤ (m.choose c : Real) * (claim1Const C0 KR K c * (1 + max K 0)) *
              max K 0 :=
            mul_le_mul_of_nonneg_left hgmc
              (mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (claim1Const_nonneg C0 KR K c) (by linarith)))
    -- assemble
    have hbr : max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
          (∑ c ∈ Finset.range m, (m.choose c : Real) *
            compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr g (m - c) x)) ≤
        (max KR 0 + S) * (1 + compL2 (iterCovComp (I := I) frame chr g (m + 1) x)) := by
      nlinarith [hsum, mul_nonneg hS0 hgm1]
    have hbr0 : (0 : Real) ≤
        max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
        ∑ c ∈ Finset.range m, (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m - c) x) := by
      refine add_nonneg (mul_nonneg hKR0 hgm1) (Finset.sum_nonneg fun c _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (compL2_nonneg _)) (compL2_nonneg _))
    have hGx : compL2 (Ginv x) ≤ max C0 0 := le_trans (hGinv x hx) (le_max_left C0 0)
    calc compL2 (iterCovCompU (I := I) frame chr A m x)
        ≤ compL2 (Ginv x) *
            (max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
            ∑ c ∈ Finset.range m, (m.choose c : Real) *
              compL2 (iterCovCompU (I := I) frame chr A c x) *
              compL2 (iterCovComp (I := I) frame chr g (m - c) x)) := hcore
      _ ≤ max C0 0 * ((max KR 0 + S) *
            (1 + compL2 (iterCovComp (I := I) frame chr g (m + 1) x))) :=
          mul_le_mul hGx hbr hbr0 (le_max_right C0 0)
      _ = claim1Const C0 KR K m *
            (1 + compL2 (iterCovComp (I := I) frame chr g (m + 1) x)) := by
          rw [claim1Const_eq, hSdef]
          ring

/-- Existential compatibility form of `claim1_abstract_bound`. -/
theorem claim1_abstract {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    {p : ℕ} (C0 KR K : Real) (m : ℕ) :
    ∃ C, 0 ≤ C ∧
      ∀ (g : M → (Fin (1 + 1) → Idx) → Real),
        (∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u) →
      ∀ (Ginv : M → (Fin (1 + 1) → Idx) → Real)
        (A : M → (Fin (p + 1) → Idx) → Real),
        (∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u) →
        (∀ x ∈ u, ∀ c e : Idx,
          (∑ l : Idx, g x (Fin.snoc (fun _ : Fin 1 => l) c) *
            Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0) →
        (∀ x ∈ u, compL2 (Ginv x) ≤ C0) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m →
          compL2 (iterCovComp (I := I) frame chr g j x) ≤ K) →
        (∀ x ∈ u, ∀ m', m' ≤ m →
          compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m' x) ≤
            KR * compL2 (iterCovComp (I := I) frame chr g (m' + 1) x)) →
        ∀ x ∈ u,
          compL2 (iterCovCompU (I := I) frame chr A m x) ≤
            C * (1 + compL2 (iterCovComp (I := I) frame chr g (m + 1) x)) := by
  exact ⟨claim1Const C0 KR K m, claim1Const_nonneg C0 KR K m,
    claim1_abstract_bound hu frame chr hframe hchr C0 KR K m⟩

/-- **Claim 1** (component form, with the lowered-Koszul relation explicit).  The connection
difference `A` lowered by `g` (`contrTail A g`) is, on `u`, a fixed three-term slot
combination of `∇g` (`hkoszul` — the eq-3.7 / `connDiffCompEq` content in this frame, with
coefficients `½,½,−½` and the Koszul slot permutations).  Together with the pointwise
inverse property of `g`/`Ginv` (`hinv`) and the window bounds, this gives the textbook
estimate `|∇^m A| ≤ C·(1 + |∇^{m+1}g|)`.  Proof: discharge `claim1_abstract`'s `hrelB`
(`|∇^{m'}(A∗g)| ≤ KR·|∇^{m'+1}g|`, `KR = |c₁|+|c₂|+|c₃| = 3/2`) from `hkoszul` via tower
linearity (`iterCovComp_smul`/`_add`), the reindex norm-invariance, and the bottom shift. -/
theorem claim1_bound {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (c₁ c₂ c₃ : Real) (P₁ P₂ P₃ : Fin 3 ≃ Fin 3)
    (C0 K : Real) (m : ℕ) :
    ∀ (g : M → (Fin (1 + 1) → Idx) → Real),
      (∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u) →
    ∀ (Ginv : M → (Fin (1 + 1) → Idx) → Real)
      (A : M → (Fin (2 + 1) → Idx) → Real),
      (∀ k : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u) →
      (∀ x ∈ u, ∀ c e : Idx,
        (∑ l : Idx, g x (Fin.snoc (fun _ : Fin 1 => l) c) *
          Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0) →
      (∀ y ∈ u, contrTail (A y) (g y) =
        fun idx : Fin 3 → Idx =>
          c₁ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₁ j)) +
          (c₂ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₂ j)) +
            c₃ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₃ j)))) →
      (∀ x ∈ u, compL2 (Ginv x) ≤ C0) →
      (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m →
        compL2 (iterCovComp (I := I) frame chr g j x) ≤ K) →
      ∀ x ∈ u,
        compL2 (iterCovCompU (I := I) frame chr A m x) ≤
          claim1Const C0 (|c₁| + |c₂| + |c₃|) K m *
            (1 + compL2 (iterCovComp (I := I) frame chr g (m + 1) x)) := by
  intro g hg Ginv A hA hinv hkoszul hGinv hK
  refine claim1_abstract_bound (p := 2) hu frame chr hframe hchr C0
    (|c₁| + |c₂| + |c₃|) K m g hg Ginv A hA hinv hGinv hK ?_
  intro x hx m' _
  -- the single-term norm: |∇^{m'}(c • (∇g ∘ P))| = |c| · |∇^{m'+1}g|
  have hterm : ∀ (ci : Real) (Pi : Fin 3 ≃ Fin 3),
      compL2 (iterCovComp (I := I) frame chr
        (fun z (k : Fin 3 → Idx) => ci * iterCovComp (I := I) frame chr g 1 z (fun j => k (Pi j)))
        m' x) = |ci| * compL2 (iterCovComp (I := I) frame chr g (m' + 1) x) := by
    intro ci Pi
    rw [show iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => ci * iterCovComp (I := I) frame chr g 1 z (fun j => k (Pi j)))
          m' x =
        fun n => ci * iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => iterCovComp (I := I) frame chr g 1 z (fun j => k (Pi j)))
          m' x n from
        funext (iterCovComp_smul hu frame chr ci
          (fun z (k : Fin 3 → Idx) => iterCovComp (I := I) frame chr g 1 z (fun j => k (Pi j)))
          hframe hchr
          (fun k => iterCovComp_contMDiffOn hu frame chr g hframe hchr hg 1 (fun j => k (Pi j)))
          m' x hx),
      compL2_smul,
      compL2_iterCovComp_compReindex Pi frame chr (iterCovComp (I := I) frame chr g 1) m' x,
      ← compL2_iterCovComp_shift frame chr g m' x]
  -- smoothness of the three smul'd reindexed fields
  have hFsm : ∀ (ci : Real) (Pi : Fin 3 ≃ Fin 3), ∀ k : Fin 3 → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => ci * iterCovComp (I := I) frame chr g 1 y (fun j => k (Pi j))) u :=
    fun ci Pi k =>
      contMDiffOn_const.mul
        (iterCovComp_contMDiffOn hu frame chr g hframe hchr hg 1 (fun j => k (Pi j)))
  -- decompose the koszul tower and bound term-by-term
  rw [iterCovComp_congr_on hu frame chr hkoszul m' x hx,
    show iterCovComp (I := I) frame chr
        (fun y (idx : Fin 3 → Idx) =>
          c₁ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₁ j)) +
          (c₂ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₂ j)) +
            c₃ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₃ j)))) m' x =
      fun n => iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => c₁ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₁ j)))
          m' x n +
        iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) =>
            c₂ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₂ j)) +
            c₃ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₃ j))) m' x n from
      funext (iterCovComp_add hu frame chr _ _ hframe hchr (hFsm c₁ P₁)
        (fun k => (hFsm c₂ P₂ k).add (hFsm c₃ P₃ k)) m' x hx)]
  refine le_trans (compL2_add_le _ _) ?_
  rw [hterm c₁ P₁,
    show iterCovComp (I := I) frame chr
        (fun z (k : Fin 3 → Idx) =>
          c₂ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₂ j)) +
          c₃ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₃ j))) m' x =
      fun n => iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => c₂ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₂ j)))
          m' x n +
        iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => c₃ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₃ j)))
          m' x n from
      funext (iterCovComp_add hu frame chr _ _ hframe hchr (hFsm c₂ P₂) (hFsm c₃ P₃) m' x hx)]
  have h23 := compL2_add_le
    (iterCovComp (I := I) frame chr
      (fun z (k : Fin 3 → Idx) => c₂ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₂ j))) m' x)
    (iterCovComp (I := I) frame chr
      (fun z (k : Fin 3 → Idx) => c₃ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₃ j))) m' x)
  rw [hterm c₂ P₂, hterm c₃ P₃] at h23
  have hG0 : (0 : Real) ≤ compL2 (iterCovComp (I := I) frame chr g (m' + 1) x) := compL2_nonneg _
  nlinarith [abs_nonneg c₁, abs_nonneg c₂, abs_nonneg c₃, hG0, h23]

/-- Existential compatibility form of `claim1_bound`. -/
theorem claim1 {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (c₁ c₂ c₃ : Real) (P₁ P₂ P₃ : Fin 3 ≃ Fin 3)
    (C0 K : Real) (m : ℕ) :
    ∃ C, 0 ≤ C ∧
      ∀ (g : M → (Fin (1 + 1) → Idx) → Real),
        (∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u) →
      ∀ (Ginv : M → (Fin (1 + 1) → Idx) → Real)
        (A : M → (Fin (2 + 1) → Idx) → Real),
        (∀ k : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u) →
        (∀ x ∈ u, ∀ c e : Idx,
          (∑ l : Idx, g x (Fin.snoc (fun _ : Fin 1 => l) c) *
            Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0) →
        (∀ y ∈ u, contrTail (A y) (g y) =
          fun idx : Fin 3 → Idx =>
            c₁ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₁ j)) +
            (c₂ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₂ j)) +
              c₃ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₃ j)))) →
        (∀ x ∈ u, compL2 (Ginv x) ≤ C0) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m →
          compL2 (iterCovComp (I := I) frame chr g j x) ≤ K) →
        ∀ x ∈ u,
          compL2 (iterCovCompU (I := I) frame chr A m x) ≤
            C * (1 + compL2 (iterCovComp (I := I) frame chr g (m + 1) x)) := by
  exact ⟨claim1Const C0 (|c₁| + |c₂| + |c₃|) K m,
    claim1Const_nonneg C0 (|c₁| + |c₂| + |c₃|) K m,
    claim1_bound hu frame chr hframe hchr c₁ c₂ c₃ P₁ P₂ P₃ C0 K m⟩

end DifferentialGeometry.PDE.RicciFlow
