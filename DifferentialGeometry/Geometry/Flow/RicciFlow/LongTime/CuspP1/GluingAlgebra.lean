import Mathlib.GroupTheory.PushoutI
import Mathlib.GroupTheory.HNNExtension

set_option autoImplicit false

/-!
# Finite graph of groups: vertex groups inject (algebraic core of P1b)

Frozen shape (see `build-logs/ch15/DELIVERIES.md`, lane CP1-B).  A finite graph of groups is
given by vertex groups `Gv : Fin (n+1) → Type u`, a spanning tree encoded by a parent function
(`par k < k.succ`, tree-edge groups `T k` with injections `ta k` into the parent vertex group and
`tb k` into the vertex group of `k.succ`), and finitely many further edges `e : N` (self-loops
allowed) with edge groups `E e` and injections `ea e`, `eb e` into the vertex groups of `src e`,
`tgt e`.  A group `G` with vertex maps `ι v` that is *weakly universal* (every compatible family
`f v`, `x e` in a group `K` factors through `ι`) has all `ι v` injective.

Tree-edge relation: `f (par k) (ta k a) = f k.succ (tb k a)`.
Non-tree relation:  `x e * f (src e) (ea e a) = f (tgt e) (eb e a) * x e`.
-/

universe u w

namespace GC.LongTime.CuspP1

open Monoid

/-- Amalgam step (two pieces): injective edge maps give injective vertex maps. -/
theorem amalgam_injective_CPB {P Q A : Type u} [Group P] [Group Q] [Group A]
    (f : A →* P) (g : A →* Q) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ (R : Type u) (_ : Group R) (p : P →* R) (q : Q →* R),
      Function.Injective p ∧ Function.Injective q ∧ p.comp f = q.comp g := by
  let G : Bool → Type u := fun b => Bool.rec (motive := fun _ => Type u) P Q b
  let instG : ∀ b, Group (G b) := fun b => Bool.rec (motive := fun b => Group (G b)) ‹Group P› ‹Group Q› b
  let φ : ∀ b, A →* G b := fun b => Bool.rec (motive := fun b => A →* G b) f g b
  have hφ : ∀ b, Function.Injective (φ b) := fun b => by cases b <;> assumption
  refine ⟨PushoutI φ, inferInstance, PushoutI.of (φ := φ) false, PushoutI.of (φ := φ) true,
    PushoutI.of_injective hφ false, PushoutI.of_injective hφ true, ?_⟩
  ext a
  have h1 := PushoutI.of_apply_eq_base φ false a
  have h2 := PushoutI.of_apply_eq_base φ true a
  exact h1.trans h2.symm

/-- HNN step: the base group injects into the HNN extension, and the stable letter conjugates. -/
theorem hnn_injective_CPB {P : Type u} [Group P] (A B : Subgroup P) (φ : A ≃* B) :
    ∃ (R : Type u) (_ : Group R) (p : P →* R) (x : R),
      Function.Injective p ∧ ∀ a : A, x * p (a : P) = p (φ a : P) * x :=
  ⟨HNNExtension P A B φ, inferInstance, HNNExtension.of, HNNExtension.t,
    HNNExtension.of_injective φ, fun a => HNNExtension.t_mul_of a⟩

section Model

variable {n : ℕ} (Gv : Fin (n + 1) → Type u) [∀ v, Group (Gv v)]
  (T : Fin n → Type u) [∀ k, Group (T k)] (par : Fin n → Fin (n + 1))
  (ta : ∀ k, T k →* Gv (par k)) (tb : ∀ k, T k →* Gv k.succ)

/-- Stage 1: the tree part, by induction on the number of vertices placed. -/
theorem tree_model_CPB (hpar : ∀ k, par k < k.succ)
    (hta : ∀ k, Function.Injective (ta k)) (htb : ∀ k, Function.Injective (tb k)) :
    ∀ m : ℕ, m ≤ n + 1 → ∃ (P : Type u) (_ : Group P) (ι : ∀ v, Gv v →* P),
      (∀ v : Fin (n + 1), v.val < m → Function.Injective (ι v)) ∧
      (∀ (k : Fin n), k.val + 1 < m → ∀ a, ι (par k) (ta k a) = ι k.succ (tb k a)) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨PUnit, inferInstance, fun v => 1, fun v hv => absurd hv (Nat.not_lt_zero _),
      fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨P, instP, ι, hinj, hrel⟩ := ih (Nat.le_of_succ_le hm)
    have build : ∀ (w : Fin (n + 1)), w.val = m →
        ∀ (Q : Type u) (_ : Group Q) (p : P →* Q) (q : Gv w →* Q),
        Function.Injective p → Function.Injective q →
        (∀ k : Fin n, ∀ h : k.succ = w, ∀ a,
          p (ι (par k) (ta k a)) = q (h ▸ tb k a)) →
        ∃ (Q : Type u) (_ : Group Q) (ι' : ∀ v, Gv v →* Q),
          (∀ v : Fin (n + 1), v.val < m + 1 → Function.Injective (ι' v)) ∧
          (∀ (k : Fin n), k.val + 1 < m + 1 → ∀ a,
            ι' (par k) (ta k a) = ι' k.succ (tb k a)) := by
      intro w hw Q _ p q hp hq hrelw
      refine ⟨Q, inferInstance, Function.update (fun v => p.comp (ι v)) w q, ?_, ?_⟩
      · intro v hv
        by_cases h : v = w
        · subst h
          simpa using hq
        · rw [Function.update_of_ne h]
          have : v.val < m := by
            have hne : v.val ≠ m := fun e => h (Fin.ext (e.trans hw.symm))
            omega
          exact hp.comp (hinj v this)
      · intro k hk a
        have hpk : par k ≠ w := by
          have := hpar k
          intro h
          rw [h] at this
          rw [Fin.lt_def] at this
          simp only [Fin.val_succ] at this
          omega
        by_cases h : k.succ = w
        · subst h
          rw [Function.update_of_ne hpk, Function.update_self]
          have := hrelw k rfl a
          simpa using this
        · have hlt : k.val + 1 < m := by
            have hne : k.val + 1 ≠ m := fun e => h (Fin.ext (by simpa [hw] using e))
            omega
          rw [Function.update_of_ne hpk, Function.update_of_ne h]
          simp [hrel k hlt a]
    by_cases h0 : m = 0
    · -- first vertex: amalgamate over the trivial group
      let w : Fin (n + 1) := ⟨m, hm⟩
      obtain ⟨Q, instQ, p, q, hp, hq, _⟩ := amalgam_injective_CPB
        (A := PUnit) (1 : PUnit →* P) (1 : PUnit →* Gv w)
        (fun x y _ => Subsingleton.elim x y) (fun x y _ => Subsingleton.elim x y)
      refine build w rfl Q instQ p q hp hq ?_
      intro k hk
      exfalso
      have := congrArg Fin.val hk
      simp [w] at this
      omega
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
      have hk : m' < n := by omega
      let k : Fin n := ⟨m', hk⟩
      obtain ⟨Q, instQ, p, q, hp, hq, hc⟩ := amalgam_injective_CPB
        ((ι (par k)).comp (ta k)) (tb k)
        ((hinj (par k) (by have := hpar k; rw [Fin.lt_def] at this; simpa [k] using this)).comp
          (hta k)) (htb k)
      refine build k.succ (by simp [k]) Q instQ p q hp hq ?_
      intro k' h a
      have hk' : k' = k := Fin.succ_injective _ h
      subst hk'
      have := congrArg (fun φ => φ a) hc
      simpa using this

/-- Stage 2: non-tree edges (including self-loops) by HNN extensions, by `Finset` induction. -/
theorem nontree_model_CPB {N : Type*} [DecidableEq N]
    (E : N → Type u) [∀ e, Group (E e)] (src tgt : N → Fin (n + 1))
    (ea : ∀ e, E e →* Gv (src e)) (eb : ∀ e, E e →* Gv (tgt e))
    (hea : ∀ e, Function.Injective (ea e)) (heb : ∀ e, Function.Injective (eb e))
    (P : Type u) (_ : Group P) (ι : ∀ v, Gv v →* P) (hinj : ∀ v, Function.Injective (ι v))
    (S : Finset N) :
    ∃ (Q : Type u) (_ : Group Q) (ι' : ∀ v, Gv v →* Q) (x : N → Q),
      (∀ v, Function.Injective (ι' v)) ∧
      (∀ (k : Fin n) a, ι (par k) (ta k a) = ι k.succ (tb k a) →
        ι' (par k) (ta k a) = ι' k.succ (tb k a)) ∧
      (∀ e ∈ S, ∀ a, x e * ι' (src e) (ea e a) = ι' (tgt e) (eb e a) * x e) := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨P, inferInstance, ι, fun _ => 1, hinj, fun _ _ h => h, fun e he => absurd he (by simp)⟩
  | insert e0 S he0 ih =>
    obtain ⟨Q, instQ, ι', x, hinj', htree, hrel⟩ := ih
    have h1 : Function.Injective ((ι' (src e0)).comp (ea e0)) := (hinj' _).comp (hea e0)
    have h2 : Function.Injective ((ι' (tgt e0)).comp (eb e0)) := (hinj' _).comp (heb e0)
    let A : Subgroup Q := ((ι' (src e0)).comp (ea e0)).range
    let B : Subgroup Q := ((ι' (tgt e0)).comp (eb e0)).range
    let φ : A ≃* B := (MonoidHom.ofInjective h1).symm.trans (MonoidHom.ofInjective h2)
    refine ⟨HNNExtension Q A B φ, inferInstance, fun v => HNNExtension.of.comp (ι' v),
      fun e => if e = e0 then HNNExtension.t else HNNExtension.of (x e), ?_, ?_, ?_⟩
    · intro v
      exact (HNNExtension.of_injective φ).comp (hinj' v)
    · intro k a h
      simp [htree k a h]
    · intro e he a
      by_cases hee : e = e0
      · subst hee
        simp only [ite_true, MonoidHom.comp_apply]
        have := HNNExtension.t_mul_of (φ := φ)
          (MonoidHom.ofInjective h1 a)
        have hφ : φ (MonoidHom.ofInjective h1 a) = MonoidHom.ofInjective h2 a := by
          simp [φ]
        rw [hφ] at this
        exact this
      · have he' : e ∈ S := by
          rcases Finset.mem_insert.1 he with h | h
          · exact absurd h hee
          · exact h
        simp only [hee, ite_false, MonoidHom.comp_apply]
        rw [← map_mul, ← map_mul, hrel e he' a]

/-- A faithful model of the finite graph of groups: vertex maps injective, all relations hold. -/
theorem exists_faithful_model_CPB (hpar : ∀ k, par k < k.succ)
    (hta : ∀ k, Function.Injective (ta k)) (htb : ∀ k, Function.Injective (tb k))
    {N : Type*} [Finite N]
    (E : N → Type u) [∀ e, Group (E e)] (src tgt : N → Fin (n + 1))
    (ea : ∀ e, E e →* Gv (src e)) (eb : ∀ e, E e →* Gv (tgt e))
    (hea : ∀ e, Function.Injective (ea e)) (heb : ∀ e, Function.Injective (eb e)) :
    ∃ (K : Type u) (_ : Group K) (f : ∀ v, Gv v →* K) (x : N → K),
      (∀ v, Function.Injective (f v)) ∧
      (∀ (k : Fin n) a, f (par k) (ta k a) = f k.succ (tb k a)) ∧
      (∀ e a, x e * f (src e) (ea e a) = f (tgt e) (eb e a) * x e) := by
  classical
  have := Fintype.ofFinite N
  obtain ⟨P, instP, ι, hinj, hrel⟩ := tree_model_CPB Gv T par ta tb hpar hta htb (n + 1) le_rfl
  have hinj' : ∀ v, Function.Injective (ι v) := fun v => hinj v (by omega)
  have hrel' : ∀ (k : Fin n) a, ι (par k) (ta k a) = ι k.succ (tb k a) :=
    fun k a => hrel k (by omega) a
  obtain ⟨Q, instQ, ι', x, h1, h2, h3⟩ :=
    nontree_model_CPB Gv T par ta tb E src tgt ea eb hea heb P instP ι hinj' Finset.univ
  exact ⟨Q, instQ, ι', x, h1, fun k a => h2 k a (hrel' k a),
    fun e a => h3 e (Finset.mem_univ e) a⟩

/-- **Frozen deliverable.**  If `G` with vertex maps `ι` is weakly universal for the finite
graph of groups (every relation-satisfying family in a group `K : Type u` factors through `ι`),
and all edge maps are injective, then every vertex map `ι v` is injective. -/
theorem vertex_injective_CPB (hpar : ∀ k, par k < k.succ)
    (hta : ∀ k, Function.Injective (ta k)) (htb : ∀ k, Function.Injective (tb k))
    {N : Type*} [Finite N]
    (E : N → Type u) [∀ e, Group (E e)] (src tgt : N → Fin (n + 1))
    (ea : ∀ e, E e →* Gv (src e)) (eb : ∀ e, E e →* Gv (tgt e))
    (hea : ∀ e, Function.Injective (ea e)) (heb : ∀ e, Function.Injective (eb e))
    {G : Type w} [Group G] (ι : ∀ v, Gv v →* G)
    (hU : ∀ (K : Type u) [Group K] (f : ∀ v, Gv v →* K) (x : N → K),
      (∀ (k : Fin n) a, f (par k) (ta k a) = f k.succ (tb k a)) →
      (∀ e a, x e * f (src e) (ea e a) = f (tgt e) (eb e a) * x e) →
      ∃ h : G →* K, ∀ v, h.comp (ι v) = f v)
    (v : Fin (n + 1)) : Function.Injective (ι v) := by
  obtain ⟨K, instK, f, x, hf, ht, hn⟩ :=
    exists_faithful_model_CPB Gv T par ta tb hpar hta htb E src tgt ea eb hea heb
  obtain ⟨h, hh⟩ := hU K f x ht hn
  have : Function.Injective (h.comp (ι v)) := by rw [hh v]; exact hf v
  exact Function.Injective.of_comp this

end Model

end GC.LongTime.CuspP1
