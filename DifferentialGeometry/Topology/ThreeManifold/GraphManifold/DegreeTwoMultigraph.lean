import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Sym.Sym2
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.BigOperators.Fin

/-!
# A finite multigraph in which every vertex has degree two is a disjoint union of cycles

Frozen blueprint master207B, FC42 (`prop:fibration-static-assembly`, lines 7509–7544): "FC40 gives
degree two at each vertex, counting loop incidences twice. A finite graph all of whose vertices
have degree two is a disjoint union of cycles, allowing loops and parallel edges." The same step is
used by the boundary decomposition BCF03/BCF04.

A finite multigraph is a vertex type `V`, a finite edge type `Ed` and the two ends
`src tgt : Ed → V` of every edge (loops `src e = tgt e` and parallel edges are allowed; the order of
the two ends is arbitrary). The degree of `v` is `#{e | src e = v} + #{e | tgt e = v}`, so a loop
counts twice (finiteness of `V` follows from the degree condition, so it is not assumed).
`exists_cycle_decomposition_of_degree_two` produces finitely many cycles `c : C` of
lengths `n c ≥ 1` and bijections `vtx : (Σ c, Fin (n c)) ≃ V`, `edg : (Σ c, Fin (n c)) ≃ Ed` such that
the edge `edg ⟨c, k⟩` joins `vtx ⟨c, k⟩` and `vtx ⟨c, k + 1 mod n c⟩` (as an unordered pair). A
cycle of length one is a loop, one of length two is a pair of parallel edges.

Proof: on the half-edges (darts) `Ed × Bool` the flip `σ` (other end of the same edge) and the
other dart `τ` at the same vertex are fixed-point-free involutions; the cycles of `φ = τ ∘ σ` trace
the graph's cycles, and `σ` pairs the two orientations of each cycle. A cycle of `φ` is never
`σ`-invariant: that would give a fixed point of `σ` or of `τ` (`dartFlip_ne_iterate`). One
orientation is selected from each pair.
-/

set_option autoImplicit false

noncomputable section

open Function Finset

namespace GC.GraphManifold

universe u v

namespace DegreeTwoMultigraph

variable {V : Type v} {Ed : Type u}

/-- The vertex of a dart: `false` is the source end, `true` the target end. -/
def dartHead (src tgt : Ed → V) (d : Ed × Bool) : V := bif d.2 then tgt d.1 else src d.1

/-- The other dart of the same edge. -/
def dartFlip (d : Ed × Bool) : Ed × Bool := (d.1, !d.2)

theorem dartFlip_dartFlip (d : Ed × Bool) : dartFlip (dartFlip d) = d := by
  simp [dartFlip]

theorem dartFlip_ne (d : Ed × Bool) : dartFlip d ≠ d := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [dartFlip] at h2

theorem card_dartHead_eq [Fintype Ed] [DecidableEq V] (src tgt : Ed → V) (w : V) :
    (univ.filter (fun d : Ed × Bool => dartHead src tgt d = w)).card =
      (univ.filter (fun e => src e = w)).card + (univ.filter (fun e => tgt e = w)).card := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, dartHead, Bool.cond_true, Bool.cond_false]
  rw [Finset.sum_add_distrib, add_comm]
  congr 1

variable [Fintype Ed] [DecidableEq V] (src tgt : Ed → V)
  (hdeg : ∀ w, (univ.filter (fun d : Ed × Bool => dartHead src tgt d = w)).card = 2)

include hdeg in
theorem exists_dartOther (d : Ed × Bool) :
    ∃ d', d' ≠ d ∧ dartHead src tgt d' = dartHead src tgt d := by
  classical
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp (hdeg (dartHead src tgt d))
  have hmem : ∀ z, z ∈ ({x, y} : Finset (Ed × Bool)) ↔ dartHead src tgt z = dartHead src tgt d := by
    intro z
    rw [← hs]
    simp
  have hd := (hmem d).mpr rfl
  rcases Finset.mem_insert.mp hd with hdx | hdy
  · subst hdx
    exact ⟨y, hxy.symm, (hmem y).mp (by simp)⟩
  · rw [Finset.mem_singleton] at hdy
    subst hdy
    exact ⟨x, hxy, (hmem x).mp (by simp)⟩

include hdeg in
theorem eq_of_ne_of_dartHead_eq {d a b : Ed × Bool} (ha : a ≠ d) (hb : b ≠ d)
    (ha' : dartHead src tgt a = dartHead src tgt d) (hb' : dartHead src tgt b = dartHead src tgt d) :
    a = b := by
  classical
  by_contra hab
  have hsub : ({d, a, b} : Finset (Ed × Bool)) ⊆
      univ.filter (fun z : Ed × Bool => dartHead src tgt z = dartHead src tgt d) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp [ha', hb']
  have hcard : ({d, a, b} : Finset (Ed × Bool)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha, Ne.symm hb⟩
  have hle := Finset.card_le_card hsub
  rw [hcard, hdeg] at hle
  omega

/-- The other dart at the same vertex. -/
def dartOther (d : Ed × Bool) : Ed × Bool := Classical.choose (exists_dartOther src tgt hdeg d)

theorem dartOther_ne (d : Ed × Bool) : dartOther src tgt hdeg d ≠ d :=
  (Classical.choose_spec (exists_dartOther src tgt hdeg d)).1

theorem dartHead_dartOther (d : Ed × Bool) :
    dartHead src tgt (dartOther src tgt hdeg d) = dartHead src tgt d :=
  (Classical.choose_spec (exists_dartOther src tgt hdeg d)).2

theorem dartOther_dartOther (d : Ed × Bool) :
    dartOther src tgt hdeg (dartOther src tgt hdeg d) = d :=
  eq_of_ne_of_dartHead_eq src tgt hdeg (dartOther_ne src tgt hdeg _)
    (Ne.symm (dartOther_ne src tgt hdeg d)) (dartHead_dartOther src tgt hdeg _)
    (dartHead_dartOther src tgt hdeg d).symm

/-- The permutation `φ = τ ∘ σ` of the darts. -/
def dartStep : Equiv.Perm (Ed × Bool) :=
  (Function.Involutive.toPerm dartFlip dartFlip_dartFlip).trans
    (Function.Involutive.toPerm (dartOther src tgt hdeg) (dartOther_dartOther src tgt hdeg))

theorem dartStep_apply (d : Ed × Bool) :
    dartStep src tgt hdeg d = dartOther src tgt hdeg (dartFlip d) := rfl

theorem dartStep_dartFlip (z : Ed × Bool) :
    dartStep src tgt hdeg (dartFlip z) = dartOther src tgt hdeg z := by
  rw [dartStep_apply, dartFlip_dartFlip]

theorem dartStep_dartFlip_dartStep (z : Ed × Bool) :
    dartStep src tgt hdeg (dartFlip (dartStep src tgt hdeg z)) = dartFlip z := by
  rw [dartStep_dartFlip, dartStep_apply, dartOther_dartOther]

theorem dartHead_dartFlip_iterate (x : Ed × Bool) (k : ℕ) :
    dartHead src tgt (dartFlip ((dartStep src tgt hdeg)^[k] x)) =
      dartHead src tgt ((dartStep src tgt hdeg)^[k + 1] x) := by
  rw [iterate_succ_apply', dartStep_apply, dartHead_dartOther]

theorem iterate_dartFlip_iterate (i : ℕ) (z : Ed × Bool) :
    (dartStep src tgt hdeg)^[i] (dartFlip ((dartStep src tgt hdeg)^[i] z)) = dartFlip z := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [iterate_succ_apply, iterate_succ_apply', dartStep_dartFlip_dartStep, ih]

theorem dartFlip_iterate_eq (y : Ed × Bool) (m : ℕ)
    (h : dartFlip y = (dartStep src tgt hdeg)^[m] y) :
    ∀ k ≤ m, dartFlip ((dartStep src tgt hdeg)^[k] y) = (dartStep src tgt hdeg)^[m - k] y := by
  intro k
  induction k with
  | zero => intro _; simpa using h
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    apply (dartStep src tgt hdeg).injective
    rw [iterate_succ_apply', dartStep_dartFlip_dartStep, h1]
    have hm : m - k = (m - (k + 1)) + 1 := by omega
    rw [hm, iterate_succ_apply']

/-- No cycle of `φ` is `σ`-invariant. -/
theorem dartFlip_ne_iterate (y : Ed × Bool) (m : ℕ) :
    dartFlip y ≠ (dartStep src tgt hdeg)^[m] y := by
  intro h
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' m
  · subst hj
    have h2 := dartFlip_iterate_eq src tgt hdeg y (2 * j) h j (by omega)
    rw [show 2 * j - j = j by omega] at h2
    exact dartFlip_ne _ h2
  · subst hj
    have h2 := dartFlip_iterate_eq src tgt hdeg y (2 * j + 1) h (j + 1) (by omega)
    rw [show 2 * j + 1 - (j + 1) = j by omega] at h2
    apply dartOther_ne src tgt hdeg ((dartStep src tgt hdeg)^[j + 1] y)
    rw [← dartStep_dartFlip, h2]
    exact (iterate_succ_apply' _ _ _).symm

theorem mem_periodicPts_dartStep (x : Ed × Bool) : x ∈ periodicPts (dartStep src tgt hdeg) := by
  refine mem_periodicPts.mpr ⟨orderOf (dartStep src tgt hdeg), orderOf_pos _, ?_⟩
  change (dartStep src tgt hdeg)^[orderOf (dartStep src tgt hdeg)] x = x
  rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
  rfl

theorem sameCycle_iterate (x : Ed × Bool) (k : ℕ) :
    (dartStep src tgt hdeg).SameCycle x ((dartStep src tgt hdeg)^[k] x) :=
  ⟨(k : ℤ), by rw [zpow_natCast, Equiv.Perm.coe_pow]⟩

theorem sameCycle_dartFlip {x y : Ed × Bool} (h : (dartStep src tgt hdeg).SameCycle x y) :
    (dartStep src tgt hdeg).SameCycle (dartFlip x) (dartFlip y) := by
  obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hi
  subst hi
  have h2 := iterate_dartFlip_iterate src tgt hdeg i x
  rw [← h2]
  exact (sameCycle_iterate src tgt hdeg _ i).symm

end DegreeTwoMultigraph

open DegreeTwoMultigraph in
theorem val_finRotate_of_pos {n : ℕ} (hn : 0 < n) (k : Fin n) :
    (finRotate n k : ℕ) = (k + 1) % n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [finRotate_apply, Fin.val_add_one]
  split_ifs with hk
  · subst hk
    simp
  · have hlt : (k : ℕ) + 1 < m + 1 := by
      have h1 : (k : ℕ) ≠ m := fun h => hk (Fin.ext (by simpa using h))
      omega
    rw [Nat.mod_eq_of_lt hlt]

open DegreeTwoMultigraph in
/-- **Degree-two multigraphs are disjoint unions of cycles.** A finite multigraph (loops and
parallel edges allowed) in which every vertex has degree two, a loop counting twice, is a disjoint
union of finitely many cycles: there are cycles `c : C` of lengths `n c ≥ 1` and bijections of
`Σ c, Fin (n c)` with the vertices and with the edges such that the edge `edg ⟨c, k⟩` joins
`vtx ⟨c, k⟩` and `vtx ⟨c, k + 1 mod n c⟩`. -/
theorem exists_cycle_decomposition_of_degree_two {V : Type v} {Ed : Type u}
    [Fintype Ed] [DecidableEq V] (src tgt : Ed → V)
    (hdeg : ∀ w, (univ.filter (fun e => src e = w)).card +
      (univ.filter (fun e => tgt e = w)).card = 2) :
    ∃ (C : Type u) (n : C → ℕ), Finite C ∧ (∀ c, 0 < n c) ∧
      ∃ (vtx : (Σ c, Fin (n c)) ≃ V) (edg : (Σ c, Fin (n c)) ≃ Ed),
        ∀ c k, s(src (edg ⟨c, k⟩), tgt (edg ⟨c, k⟩)) =
          s(vtx ⟨c, k⟩, vtx ⟨c, finRotate (n c) k⟩) := by
  classical
  have hd : ∀ w, (univ.filter (fun d : Ed × Bool => dartHead src tgt d = w)).card = 2 :=
    fun w => by rw [card_dartHead_eq]; exact hdeg w
  set φ := dartStep src tgt hd with hφ
  let S := Equiv.Perm.SameCycle.setoid φ
  let Q := Quotient S
  have hQ : ∀ a b : Ed × Bool, (Quotient.mk S a = Quotient.mk S b) ↔ φ.SameCycle a b :=
    fun a b => Quotient.eq
  let fbar : Q → Q := Quotient.map dartFlip (fun _ _ h => sameCycle_dartFlip src tgt hd h)
  have fbar_mk : ∀ x, fbar (Quotient.mk S x) = Quotient.mk S (dartFlip x) := fun _ => rfl
  have fbar_fbar : ∀ q, fbar (fbar q) = q := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => rw [fbar_mk, fbar_mk, dartFlip_dartFlip]
  have fbar_ne : ∀ q, fbar q ≠ q := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      rw [fbar_mk]
      intro h
      obtain ⟨i, hi⟩ := ((hQ _ _).mp h).symm.exists_nat_pow_eq
      rw [Equiv.Perm.coe_pow] at hi
      exact dartFlip_ne_iterate src tgt hd x i hi.symm
  let idx : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let C := {q : Q // idx q < idx (fbar q)}
  let r : C → Ed × Bool := fun c => c.1.out
  have hr : ∀ c : C, Quotient.mk S (r c) = c.1 := fun c => Quotient.out_eq c.1
  let n : C → ℕ := fun c => minimalPeriod φ (r c)
  have hn : ∀ c, 0 < n c := fun c =>
    minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts_dartStep src tgt hd (r c))
  -- the selected orientation of every pair
  have hsel : ∀ c c' : C, c'.1 ≠ fbar c.1 := by
    intro c c' h
    have h1 := c.2
    have h2 := c'.2
    rw [h, fbar_fbar] at h2
    exact absurd (h1.trans h2) (lt_irrefl _)
  -- one dart in a selected cycle
  have hsame : ∀ (c c' : C) (k k' : ℕ), k < n c → k' < n c' →
      φ^[k] (r c) = φ^[k'] (r c') → c = c' ∧ k = k' := by
    intro c c' k k' hk hk' h
    have hcc : c.1 = c'.1 := by
      rw [← hr c, ← hr c', hQ]
      exact (sameCycle_iterate src tgt hd (r c) k).trans
        (h ▸ (sameCycle_iterate src tgt hd (r c') k').symm)
    have hc : c = c' := Subtype.ext hcc
    subst hc
    exact ⟨rfl, iterate_injOn_Iio_minimalPeriod hk hk' h⟩
  have hflipclass : ∀ (c c' : C) (k k' : ℕ),
      φ.SameCycle (φ^[k'] (r c')) (dartFlip (φ^[k] (r c))) → False := by
    intro c c' k k' h
    apply hsel c c'
    rw [← hr c, ← hr c', fbar_mk, hQ]
    exact ((sameCycle_iterate src tgt hd (r c') k').trans h).trans
      (sameCycle_dartFlip src tgt hd (sameCycle_iterate src tgt hd (r c) k)).symm
  -- every dart, or its flip, is on a selected cycle
  have hcover : ∀ d : Ed × Bool, ∃ (c : C) (k : ℕ), k < n c ∧
      (φ^[k] (r c) = d ∨ φ^[k] (r c) = dartFlip d) := by
    intro d
    have hreach : ∀ (c : C) (z : Ed × Bool), Quotient.mk S z = c.1 →
        ∃ k, k < n c ∧ φ^[k] (r c) = z := by
      intro c z hz
      rw [← hr c, hQ] at hz
      obtain ⟨i, hi⟩ := hz.symm.exists_nat_pow_eq
      rw [Equiv.Perm.coe_pow] at hi
      refine ⟨i % n c, Nat.mod_lt _ (hn c), ?_⟩
      rw [iterate_mod_minimalPeriod_eq]
      exact hi
    by_cases hq : idx (Quotient.mk S d) < idx (fbar (Quotient.mk S d))
    · obtain ⟨k, hk, hk'⟩ := hreach ⟨_, hq⟩ d rfl
      exact ⟨⟨_, hq⟩, k, hk, Or.inl hk'⟩
    · have hne : idx (Quotient.mk S d) ≠ idx (fbar (Quotient.mk S d)) :=
        fun h => fbar_ne _ (idx.injective h).symm
      have hq' : idx (fbar (Quotient.mk S d)) < idx (fbar (fbar (Quotient.mk S d))) := by
        rw [fbar_fbar]
        omega
      obtain ⟨k, hk, hk'⟩ := hreach ⟨_, hq'⟩ (dartFlip d) (fbar_mk d).symm
      exact ⟨⟨_, hq'⟩, k, hk, Or.inr hk'⟩
  let dart : (Σ c : C, Fin (n c)) → Ed × Bool := fun p => φ^[p.2] (r p.1)
  let E : (Σ c : C, Fin (n c)) → Ed := fun p => (dart p).1
  let Vt : (Σ c : C, Fin (n c)) → V := fun p => dartHead src tgt (dart p)
  have hdart_eq : ∀ p p' : (Σ c : C, Fin (n c)), dart p = dart p' → p = p' := by
    rintro ⟨c, k⟩ ⟨c', k'⟩ h
    obtain ⟨hc, hk⟩ := hsame c c' k k' k.2 k'.2 h
    subst hc
    rw [Fin.ext hk]
  have hdart_ex : ∀ d : Ed × Bool, ∃ p, dart p = d ∨ dart p = dartFlip d := by
    intro d
    obtain ⟨c, k, hk, h⟩ := hcover d
    exact ⟨⟨c, ⟨k, hk⟩⟩, h⟩
  have hnext : ∀ (c : C) (k : Fin (n c)),
      dartHead src tgt (dartFlip (dart ⟨c, k⟩)) = Vt ⟨c, finRotate (n c) k⟩ := by
    intro c k
    change dartHead src tgt (dartFlip (φ^[k] (r c))) = dartHead src tgt (φ^[finRotate (n c) k] (r c))
    rw [dartHead_dartFlip_iterate, val_finRotate_of_pos (hn c), iterate_mod_minimalPeriod_eq]
  have hE : Function.Bijective E := by
    constructor
    · intro p p' h
      have h' : (dart p).1 = (dart p').1 := h
      have hb : dart p' = dart p ∨ dart p' = dartFlip (dart p) := by
        revert h'
        generalize dart p = a
        generalize dart p' = a'
        intro h'
        obtain ⟨e, b⟩ := a
        obtain ⟨e', b'⟩ := a'
        simp only at h'
        subst h'
        cases b <;> cases b' <;> simp [dartFlip]
      rcases hb with hb | hb
      · exact (hdart_eq p' p hb).symm
      · obtain ⟨c, k⟩ := p
        obtain ⟨c', k'⟩ := p'
        exact (hflipclass c c' k k' (hb ▸ Equiv.Perm.SameCycle.refl _ _)).elim
    · intro e
      obtain ⟨p, hp | hp⟩ := hdart_ex (e, false)
      · exact ⟨p, by simp only [E, hp]⟩
      · exact ⟨p, by simp only [E, hp, dartFlip]⟩
  have hV : Function.Bijective Vt := by
    constructor
    · intro p p' h
      by_cases hpp : dart p' = dart p
      · exact (hdart_eq p' p hpp).symm
      · have hother : dart p' = dartOther src tgt hd (dart p) :=
          eq_of_ne_of_dartHead_eq src tgt hd hpp (dartOther_ne src tgt hd _) h.symm
            (dartHead_dartOther src tgt hd _)
        rw [← dartStep_dartFlip] at hother
        obtain ⟨c, k⟩ := p
        obtain ⟨c', k'⟩ := p'
        refine (hflipclass c c' k k' ?_).elim
        change φ.SameCycle (dart ⟨c', k'⟩) (dartFlip (dart ⟨c, k⟩))
        rw [hother]
        exact (sameCycle_iterate src tgt hd _ 1).symm
    · intro w
      have hne : (univ.filter (fun d : Ed × Bool => dartHead src tgt d = w)).Nonempty := by
        rw [← Finset.card_pos, hd w]
        norm_num
      obtain ⟨d, hdw⟩ := hne
      rw [Finset.mem_filter] at hdw
      obtain ⟨p, hp | hp⟩ := hdart_ex d
      · exact ⟨p, by simp only [Vt, hp, hdw.2]⟩
      · obtain ⟨c, k⟩ := p
        refine ⟨⟨c, finRotate (n c) k⟩, ?_⟩
        rw [← hnext, hp, dartFlip_dartFlip, hdw.2]
  refine ⟨C, n, inferInstance, hn, Equiv.ofBijective Vt hV, Equiv.ofBijective E hE, ?_⟩
  intro c k
  simp only [Equiv.ofBijective_apply]
  rw [← hnext]
  change s(src (dart ⟨c, k⟩).1, tgt (dart ⟨c, k⟩).1) =
    s(dartHead src tgt (dart ⟨c, k⟩), dartHead src tgt (dartFlip (dart ⟨c, k⟩)))
  obtain ⟨e, b⟩ := dart ⟨c, k⟩
  cases b
  · rfl
  · exact Sym2.eq_swap

end GC.GraphManifold
