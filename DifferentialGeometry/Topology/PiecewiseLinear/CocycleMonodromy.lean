import DifferentialGeometry.Topology.PiecewiseLinear.BranchSignChain
import DifferentialGeometry.Topology.PiecewiseLinear.DoubleCoverComplex
import DifferentialGeometry.Topology.SimplicialComplex.EdgeGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

namespace DifferentialGeometry.Topology.PiecewiseLinear

open SimpleGraph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Geometry.SimplicialComplex ℝ E}

def boolZMod2 (b : Bool) : ZMod 2 := cond b 1 0

theorem boolZMod2_xor (a b : Bool) :
    boolZMod2 (Bool.xor a b) = boolZMod2 a + boolZMod2 b := by
  cases a <;> cases b <;> decide

theorem boolZMod2_injective : Function.Injective (boolZMod2 : Bool → ZMod 2) := by
  decide

def zmod2Bool (x : ZMod 2) : Bool := decide (x = 1)

theorem boolZMod2_zmod2Bool (x : ZMod 2) : boolZMod2 (zmod2Bool x) = x := by
  revert x
  decide

namespace SimplicialBoolCocycle

variable (ε : SimplicialBoolCocycle K)

def dartJump (d : (SimplicialComplex.edgeGraph K).Dart) : ZMod 2 :=
  boolZMod2 (ε.parity (d.fst : E) (d.snd : E))

def walkMonodromy {u w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w) : ZMod 2 :=
  (p.darts.map ε.dartJump).sum

theorem walkMonodromy_nil {u : K.vertices} :
    ε.walkMonodromy (Walk.nil : (SimplicialComplex.edgeGraph K).Walk u u) = 0 := rfl

theorem walkMonodromy_cons {u v w : K.vertices}
    (h : (SimplicialComplex.edgeGraph K).Adj u v)
    (p : (SimplicialComplex.edgeGraph K).Walk v w) :
    ε.walkMonodromy (Walk.cons h p) =
      boolZMod2 (ε.parity (u : E) (v : E)) + ε.walkMonodromy p := by
  simp [walkMonodromy, dartJump]

theorem walkMonodromy_append {u v w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u v)
    (q : (SimplicialComplex.edgeGraph K).Walk v w) :
    ε.walkMonodromy (p.append q) = ε.walkMonodromy p + ε.walkMonodromy q := by
  simp [walkMonodromy]

open Classical in
theorem parity_symm_of_adj {u v : K.vertices}
    (h : (SimplicialComplex.edgeGraph K).Adj u v) :
    ε.parity (v : E) (u : E) = ε.parity (u : E) (v : E) :=
  (ε.symm (u : E) (v : E) ((SimplicialComplex.edgeGraph_adj K u v).mp h).2).symm

theorem walkMonodromy_reverse {u w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w) :
    ε.walkMonodromy p.reverse = ε.walkMonodromy p := by
  induction p with
  | nil => rfl
  | cons h q ih =>
      rw [Walk.reverse_cons, ε.walkMonodromy_append, ih, ε.walkMonodromy_cons,
        ε.walkMonodromy_cons, ε.walkMonodromy_nil, add_zero, ε.parity_symm_of_adj h.symm,
        add_comm]

open Classical in
theorem walkMonodromy_eq_of_coboundary {δ : E → Bool}
    (hδ : ∀ a b, {a, b} ∈ K.faces → ε.parity a b = Bool.xor (δ a) (δ b))
    {u w : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk u w) :
    ε.walkMonodromy p = boolZMod2 (δ (u : E)) + boolZMod2 (δ (w : E)) := by
  induction p with
  | nil => rw [ε.walkMonodromy_nil, CharTwo.add_self_eq_zero]
  | cons h q ih =>
      rename_i a b _
      rw [ε.walkMonodromy_cons, ih,
        hδ (a : E) (b : E) ((SimplicialComplex.edgeGraph_adj K a b).mp h).2, boolZMod2_xor,
        add_assoc, ← add_assoc (boolZMod2 (δ (b : E))), CharTwo.add_self_eq_zero, zero_add]

theorem walkMonodromy_eq_zero_of_isCoboundary (hε : ε.IsCoboundary) {u : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u u) : ε.walkMonodromy p = 0 := by
  obtain ⟨δ, hδ⟩ := hε
  rw [ε.walkMonodromy_eq_of_coboundary hδ p, CharTwo.add_self_eq_zero]

open Classical in
theorem isCoboundary_of_forall_walkMonodromy_eq_zero (v₀ : K.vertices)
    (hconn : ∀ v : K.vertices, (SimplicialComplex.edgeGraph K).Reachable v₀ v)
    (hzero : ∀ p : (SimplicialComplex.edgeGraph K).Walk v₀ v₀, ε.walkMonodromy p = 0) :
    ε.IsCoboundary := by
  let m : K.vertices → ZMod 2 := fun v => ε.walkMonodromy (hconn v).some
  have hedge : ∀ u v : K.vertices, (SimplicialComplex.edgeGraph K).Adj u v →
      boolZMod2 (ε.parity (u : E) (v : E)) = m u + m v := by
    intro u v huv
    have hloop := hzero
      (((hconn u).some.append (Walk.cons huv Walk.nil)).append (hconn v).some.reverse)
    rw [ε.walkMonodromy_append, ε.walkMonodromy_append, ε.walkMonodromy_cons,
      ε.walkMonodromy_nil, add_zero, ε.walkMonodromy_reverse] at hloop
    have hm : m u + boolZMod2 (ε.parity (u : E) (v : E)) + m v = 0 := hloop
    have hj : boolZMod2 (ε.parity (u : E) (v : E)) = -m u - m v := by linear_combination hm
    rw [hj, sub_eq_add_neg, CharTwo.neg_eq, CharTwo.neg_eq]
  refine ⟨fun a => if ha : a ∈ K.vertices then zmod2Bool (m ⟨a, ha⟩) else false, ?_⟩
  intro a b hab
  have ha : a ∈ K.vertices := K.down_closed hab (by simp) (Finset.singleton_nonempty a)
  have hb : b ∈ K.vertices := K.down_closed hab (by simp) (Finset.singleton_nonempty b)
  apply boolZMod2_injective
  rw [boolZMod2_xor]
  dsimp only
  rw [dif_pos ha, dif_pos hb, boolZMod2_zmod2Bool, boolZMod2_zmod2Bool]
  by_cases hne : a = b
  · subst hne
    rw [ε.self a ha]
    exact (CharTwo.add_self_eq_zero (m ⟨a, ha⟩)).symm
  · exact hedge ⟨a, ha⟩ ⟨b, hb⟩ ⟨fun h => hne (congrArg Subtype.val h), hab⟩

open Classical in
theorem isCoboundary_of_preconnected
    (hconn : (SimplicialComplex.edgeGraph K).Preconnected)
    (hzero : ∀ (u : K.vertices) (p : (SimplicialComplex.edgeGraph K).Walk u u),
      ε.walkMonodromy p = 0) :
    ε.IsCoboundary := by
  rcases isEmpty_or_nonempty K.vertices with hempty | hne
  · refine ⟨fun _ => false, ?_⟩
    intro a b hab
    exact (hempty.false ⟨a, K.down_closed hab (by simp) (Finset.singleton_nonempty a)⟩).elim
  · obtain ⟨v₀⟩ := hne
    exact ε.isCoboundary_of_forall_walkMonodromy_eq_zero v₀ (hconn v₀) (hzero v₀)

open Classical in
theorem isCoboundary_iff_forall_walkMonodromy_eq_zero
    (hconn : (SimplicialComplex.edgeGraph K).Preconnected) :
    ε.IsCoboundary ↔ ∀ (u : K.vertices) (p : (SimplicialComplex.edgeGraph K).Walk u u),
      ε.walkMonodromy p = 0 :=
  ⟨fun hε _ p => ε.walkMonodromy_eq_zero_of_isCoboundary hε p,
    fun hzero => ε.isCoboundary_of_preconnected hconn hzero⟩

open Classical in
theorem isCoboundary_of_walkMonodromy_generated
    (hconn : (SimplicialComplex.edgeGraph K).Preconnected) {v₀ : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀)
    (hgen : ∀ (u : K.vertices) (p : (SimplicialComplex.edgeGraph K).Walk u u),
      ε.walkMonodromy p = 0 ∨ ε.walkMonodromy p = ε.walkMonodromy γ)
    (hγ : ε.walkMonodromy γ = 0) : ε.IsCoboundary := by
  refine ε.isCoboundary_of_preconnected hconn fun u p => ?_
  rcases hgen u p with h | h
  · exact h
  · rw [h, hγ]

open Classical in
def ofLe {L : Geometry.SimplicialComplex ℝ E} (hLK : L ≤ K) : SimplicialBoolCocycle L where
  parity := ε.parity
  symm a b h := ε.symm a b (hLK h)
  self a h := ε.self a (hLK h)
  cocycle a b c h := ε.cocycle a b c (hLK h)

open Classical in
theorem ofLe_parity {L : Geometry.SimplicialComplex ℝ E} (hLK : L ≤ K) (a b : E) :
    (ε.ofLe hLK).parity a b = ε.parity a b := rfl

def loopMonodromy {m : ℕ} [NeZero m] (c : Fin m → E) : ZMod 2 :=
  ∑ i, boolZMod2 (ε.parity (c i) (c (i + 1)))

theorem loopMonodromy_eq_sum {m : ℕ} [NeZero m] (c : Fin m → E) :
    ε.loopMonodromy c = ∑ i, boolZMod2 (ε.parity (c i) (c (i + 1))) := rfl

open Classical in
theorem loopMonodromy_eq_zero_of_isCoboundary {m : ℕ} [NeZero m] (c : Fin m → E)
    (hface : ∀ i : Fin m, {c i, c (i + 1)} ∈ K.faces) (hε : ε.IsCoboundary) :
    ε.loopMonodromy c = 0 := by
  obtain ⟨δ, hδ⟩ := hε
  rw [ε.loopMonodromy_eq_sum c]
  refine sum_sideJump_eq_zero_of_cycle (fun i => boolZMod2 (ε.parity (c i) (c (i + 1))))
    (fun i => boolZMod2 (δ (c i))) fun i => ?_
  rw [hδ _ _ (hface i), boolZMod2_xor]

open Classical in
theorem not_isCoboundary_of_loopMonodromy_ne_zero {m : ℕ} [NeZero m] (c : Fin m → E)
    (hface : ∀ i : Fin m, {c i, c (i + 1)} ∈ K.faces) (hne : ε.loopMonodromy c ≠ 0) :
    ¬ ε.IsCoboundary := by
  intro hε
  obtain ⟨δ, hδ⟩ := hε
  rw [ε.loopMonodromy_eq_sum c] at hne
  refine not_exists_sideChoice_of_cycle
    (fun i => boolZMod2 (ε.parity (c i) (c (i + 1)))) hne
    ⟨fun i => boolZMod2 (δ (c i)), fun i => ?_⟩
  rw [hδ _ _ (hface i), boolZMod2_xor]

theorem exists_sideChain {m : ℕ} (c : Fin (m + 1) → E) (s₀ : ZMod 2) :
    ∃ s : Fin (m + 1) → ZMod 2, s 0 = s₀ ∧
      ∀ i : Fin m,
        s i.succ = s i.castSucc + boolZMod2 (ε.parity (c i.castSucc) (c i.succ)) := by
  obtain ⟨t, ht⟩ :=
    exists_sideChoice_of_chain fun i : Fin m => boolZMod2 (ε.parity (c i.castSucc) (c i.succ))
  refine ⟨fun i => t i + (s₀ - t 0), ?_, fun i => ?_⟩
  · change t 0 + (s₀ - t 0) = s₀
    ring
  · change t i.succ + (s₀ - t 0) =
      t i.castSucc + (s₀ - t 0) + boolZMod2 (ε.parity (c i.castSucc) (c i.succ))
    rw [ht i]
    ring

end SimplicialBoolCocycle

end DifferentialGeometry.Topology.PiecewiseLinear
