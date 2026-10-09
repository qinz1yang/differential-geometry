/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CocycleMonodromy

namespace DifferentialGeometry.Topology.PiecewiseLinear

open SimpleGraph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Geometry.SimplicialComplex ℝ E}

theorem ofNat_fin_zero (m : ℕ) [NeZero m] : Fin.ofNat m 0 = (0 : Fin m) := rfl

theorem ofNat_fin_self (m : ℕ) [NeZero m] : Fin.ofNat m m = (0 : Fin m) :=
  Fin.ext (by simp)

theorem ofNat_fin_val {m : ℕ} [NeZero m] (i : Fin m) : Fin.ofNat m (i : ℕ) = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem ofNat_fin_add_one (m : ℕ) [NeZero m] (k : ℕ) :
    Fin.ofNat m (k + 1) = Fin.ofNat m k + 1 :=
  Fin.ext (Nat.add_mod k 1 m)

theorem ofNat_fin_last (m : ℕ) : Fin.ofNat (m + 1) m = Fin.last m :=
  Fin.ext (Nat.mod_eq_of_lt (Nat.lt_succ_self m))

theorem last_add_one_eq_zero (m : ℕ) : (Fin.last m) + 1 = (0 : Fin (m + 1)) := by
  rw [← ofNat_fin_last, ← ofNat_fin_add_one]
  exact ofNat_fin_self (m + 1)

open Classical in
theorem mem_vertices_of_mem_pair_left {a b : E} (h : ({a, b} : Finset E) ∈ K.faces) :
    a ∈ K.vertices :=
  K.down_closed h (by simp) (Finset.singleton_nonempty a)

def natChainWalk (d : ℕ → E) (hmem : ∀ k, d k ∈ K.vertices)
    (hadj : ∀ k, (SimplicialComplex.edgeGraph K).Adj ⟨d k, hmem k⟩ ⟨d (k + 1), hmem (k + 1)⟩) :
    (k : ℕ) → (SimplicialComplex.edgeGraph K).Walk ⟨d 0, hmem 0⟩ ⟨d k, hmem k⟩
  | 0 => Walk.nil
  | k + 1 => (natChainWalk d hmem hadj k).concat (hadj k)

def walkChain : {u w : K.vertices} → (p : (SimplicialComplex.edgeGraph K).Walk u w) →
    Fin (p.length + 1) → E
  | u, _, Walk.nil => fun _ => (u : E)
  | u, _, Walk.cons _ q => Fin.cons (α := fun _ => E) (u : E) (walkChain q)

theorem walkChain_zero {u w : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk u w) :
    walkChain p 0 = (u : E) := by
  cases p with
  | nil => rfl
  | cons h q =>
      change Fin.cons (α := fun _ => E) (u : E) (walkChain q) 0 = (u : E)
      rw [Fin.cons_zero]

theorem walkChain_last {u w : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk u w) :
    walkChain p (Fin.last p.length) = (w : E) := by
  induction p with
  | nil => rfl
  | cons h q ih => exact ih

theorem walkMonodromy_copy (ε : SimplicialBoolCocycle K) {u w u₁ w₁ : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w) (hu : u = u₁) (hw : w = w₁) :
    ε.walkMonodromy (p.copy hu hw) = ε.walkMonodromy p := by
  subst hu
  subst hw
  rfl

theorem walkMonodromy_natChainWalk (ε : SimplicialBoolCocycle K) (d : ℕ → E)
    (hmem : ∀ k, d k ∈ K.vertices)
    (hadj : ∀ k, (SimplicialComplex.edgeGraph K).Adj ⟨d k, hmem k⟩ ⟨d (k + 1), hmem (k + 1)⟩)
    (k : ℕ) :
    ε.walkMonodromy (natChainWalk d hmem hadj k) =
      ∑ j ∈ Finset.range k, boolZMod2 (ε.parity (d j) (d (j + 1))) := by
  induction k with
  | zero => simp [natChainWalk, ε.walkMonodromy_nil]
  | succ k ih =>
      rw [natChainWalk, Walk.concat_eq_append, ε.walkMonodromy_append, ih, ε.walkMonodromy_cons,
        ε.walkMonodromy_nil, add_zero, Finset.sum_range_succ]

namespace SimplicialBoolCocycle

variable (ε : SimplicialBoolCocycle K)

def chainMonodromy {m : ℕ} (c : Fin (m + 1) → E) : ZMod 2 :=
  ∑ i : Fin m, boolZMod2 (ε.parity (c i.castSucc) (c i.succ))

theorem chainMonodromy_eq_sum {m : ℕ} (c : Fin (m + 1) → E) :
    ε.chainMonodromy c = ∑ i : Fin m, boolZMod2 (ε.parity (c i.castSucc) (c i.succ)) := rfl

theorem chainMonodromy_cons {m : ℕ} (x : E) (d : Fin (m + 1) → E) :
    ε.chainMonodromy (Fin.cons (α := fun _ => E) x d) =
      boolZMod2 (ε.parity x (d 0)) + ε.chainMonodromy d := by
  rw [ε.chainMonodromy_eq_sum, ε.chainMonodromy_eq_sum, Fin.sum_univ_succ]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun i _ => ?_)
  · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
  · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]

theorem loopMonodromy_eq_chainMonodromy_add {m : ℕ} (c : Fin (m + 1) → E) :
    ε.loopMonodromy c = ε.chainMonodromy c + boolZMod2 (ε.parity (c (Fin.last m)) (c 0)) := by
  rw [ε.loopMonodromy_eq_sum, Fin.sum_univ_castSucc, last_add_one_eq_zero, ε.chainMonodromy_eq_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) rfl
  rw [Fin.coeSucc_eq_succ]

theorem chainMonodromy_walkChain {u w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w) :
    ε.chainMonodromy (walkChain p) = ε.walkMonodromy p := by
  induction p with
  | nil =>
      rw [ε.chainMonodromy_eq_sum, ε.walkMonodromy_nil]
      exact Fin.sum_univ_zero _
  | cons h q ih =>
      rename_i a b _
      have hcons := ε.chainMonodromy_cons (a : E) (walkChain q)
      rw [walkChain_zero] at hcons
      refine hcons.trans ?_
      rw [ih, ε.walkMonodromy_cons]

theorem loopMonodromy_walkChain {u : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u u) :
    ε.loopMonodromy (walkChain p) = ε.walkMonodromy p := by
  rw [ε.loopMonodromy_eq_chainMonodromy_add, ε.chainMonodromy_walkChain, walkChain_last,
    walkChain_zero, ε.self (u : E) u.2]
  exact add_zero _

end SimplicialBoolCocycle

open Classical in
theorem walkChain_castSucc_succ_mem_faces {u w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w) (j : Fin p.length) :
    ({walkChain p j.castSucc, walkChain p j.succ} : Finset E) ∈ K.faces := by
  induction p with
  | nil => exact j.elim0
  | cons h q ih =>
      rename_i a b _
      revert j
      change ∀ j : Fin (q.length + 1),
        ({Fin.cons (α := fun _ => E) (a : E) (walkChain q) j.castSucc,
          Fin.cons (α := fun _ => E) (a : E) (walkChain q) j.succ} : Finset E) ∈ K.faces
      refine Fin.cases ?_ ?_
      · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, walkChain_zero]
        exact ((SimplicialComplex.edgeGraph_adj K a b).mp h).2
      · intro i
        rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact ih i

open Classical in
theorem walkChain_mem_faces {u : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u u) (i : Fin (p.length + 1)) :
    ({walkChain p i, walkChain p (i + 1)} : Finset E) ∈ K.faces := by
  refine Fin.lastCases ?_ ?_ i
  · rw [last_add_one_eq_zero, walkChain_last, walkChain_zero,
      Finset.insert_eq_self.mpr (Finset.mem_singleton_self _)]
    exact u.2
  · intro j
    rw [Fin.coeSucc_eq_succ]
    exact walkChain_castSucc_succ_mem_faces p j

section Cycle

variable {m : ℕ} [NeZero m] {c : Fin m → E}

open Classical in
theorem mem_vertices_of_cycleFaces
    (hface : ∀ i : Fin m, ({c i, c (i + 1)} : Finset E) ∈ K.faces) (i : Fin m) :
    c i ∈ K.vertices :=
  mem_vertices_of_mem_pair_left (hface i)

open Classical in
theorem cycleAdj (hface : ∀ i : Fin m, ({c i, c (i + 1)} : Finset E) ∈ K.faces)
    (hne : ∀ i : Fin m, c i ≠ c (i + 1)) (k : ℕ) :
    (SimplicialComplex.edgeGraph K).Adj
      ⟨c (Fin.ofNat m k), mem_vertices_of_cycleFaces hface (Fin.ofNat m k)⟩
      ⟨c (Fin.ofNat m (k + 1)), mem_vertices_of_cycleFaces hface (Fin.ofNat m (k + 1))⟩ := by
  have hk : c (Fin.ofNat m (k + 1)) = c (Fin.ofNat m k + 1) :=
    congrArg c (ofNat_fin_add_one m k)
  refine (SimplicialComplex.edgeGraph_adj K _ _).mpr ⟨fun h => hne (Fin.ofNat m k) ?_, ?_⟩
  · rw [← hk]
    exact congrArg Subtype.val h
  · change ({c (Fin.ofNat m k), c (Fin.ofNat m (k + 1))} : Finset E) ∈ K.faces
    rw [hk]
    exact hface _

open Classical in
def cycleWalk (hface : ∀ i : Fin m, ({c i, c (i + 1)} : Finset E) ∈ K.faces)
    (hne : ∀ i : Fin m, c i ≠ c (i + 1)) :
    (SimplicialComplex.edgeGraph K).Walk ⟨c 0, mem_vertices_of_cycleFaces hface 0⟩
      ⟨c 0, mem_vertices_of_cycleFaces hface 0⟩ :=
  (natChainWalk (fun k => c (Fin.ofNat m k))
      (fun k => mem_vertices_of_cycleFaces hface (Fin.ofNat m k)) (cycleAdj hface hne) m).copy
    (Subtype.ext (congrArg c (ofNat_fin_zero m))) (Subtype.ext (congrArg c (ofNat_fin_self m)))

open Classical in
theorem walkMonodromy_cycleWalk (ε : SimplicialBoolCocycle K)
    (hface : ∀ i : Fin m, ({c i, c (i + 1)} : Finset E) ∈ K.faces)
    (hne : ∀ i : Fin m, c i ≠ c (i + 1)) :
    ε.walkMonodromy (cycleWalk hface hne) = ε.loopMonodromy c := by
  rw [cycleWalk, walkMonodromy_copy, walkMonodromy_natChainWalk, ε.loopMonodromy_eq_sum,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofNat_fin_add_one, ofNat_fin_val]

end Cycle

end DifferentialGeometry.Topology.PiecewiseLinear
