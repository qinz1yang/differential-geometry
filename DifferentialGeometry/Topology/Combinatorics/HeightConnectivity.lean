import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Max

open Set

namespace DifferentialGeometry.Topology.Combinatorics

variable {V α : Type*}

theorem preconnected_induce_of_preconnected_insert
    (G : SimpleGraph V) (s : Set V) (p : V)
    (hG : (G.induce (insert p s)).Preconnected)
    (hneighbors : ∀ u v : s, G.Adj p u → G.Adj p v → (G.induce s).Reachable u v) :
    (G.induce s).Preconnected := by
  classical
  let H := G.induce (insert p s)
  let D := G.induce s
  have hwalk {a b : (insert p s : Set V)} (w : H.Walk a b) :
      ∀ hb : (b : V) ∈ s,
        (∀ ha : (a : V) ∈ s, D.Reachable ⟨a, ha⟩ ⟨b, hb⟩) ∧
        ((a : V) = p → ∀ u : s, G.Adj p u → D.Reachable u ⟨b, hb⟩) := by
    induction w with
    | nil =>
      intro hb
      refine ⟨fun _ => .rfl, ?_⟩
      intro hap u hpu
      apply SimpleGraph.Adj.reachable
      change G.Adj (u : V) _
      simpa only [Function.Embedding.subtype_apply, hap] using hpu.symm
    | @cons a b c hab w ih =>
      intro hc
      obtain ⟨ihs, ihp⟩ := ih hc
      by_cases hb : (b : V) ∈ s
      · have hbc := ihs hb
        refine ⟨fun ha => (SimpleGraph.Adj.reachable
          (show D.Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab)).trans hbc, ?_⟩
        intro hap u hpu
        exact (hneighbors u ⟨b, hb⟩ hpu (by simpa only [hap] using (show G.Adj (a : V) (b : V) from hab))).trans hbc
      · have hbp : (b : V) = p := b.2.resolve_right hb
        refine ⟨fun ha => ihp hbp ⟨a, ha⟩ (by simpa only [hbp] using (show G.Adj (b : V) (a : V) from hab.symm)), ?_⟩
        intro hap
        exact (hab.ne (Subtype.ext (hap.trans hbp.symm))).elim
  intro u v
  obtain ⟨w⟩ := hG ⟨u, Or.inr u.2⟩ ⟨v, Or.inr v.2⟩
  exact (hwalk w v.2).1 u.2

theorem preconnected_induce_lt_of_lower_neighbors_reachable
    [Finite V] [LinearOrder α] (G : SimpleGraph V) (hG : G.Preconnected)
    (f : V → α) (hf : Function.Injective f)
    (hlower : ∀ p (u v : {x : V | f x < f p}), G.Adj p u → G.Adj p v →
      (G.induce {x : V | f x < f p}).Reachable u v) (r : α) :
    (G.induce {x | f x < r}).Preconnected := by
  classical
  have hfinite (s : Finset V) :
      (∀ u ∈ s, ∀ v, f v ≤ f u → v ∈ s) → (G.induce (s : Set V)).Preconnected →
        ∀ r : α, (G.induce ((s : Set V) ∩ {x | f x < r})).Preconnected := by
    induction s using Finset.induction_on_max_value f with
    | empty =>
      intro _ _ r u
      exact (Finset.notMem_empty _ u.2.1).elim
    | insert p s hps hmax ih =>
      intro hdown hconn r
      have hlt (u : V) (hu : u ∈ s) : f u < f p :=
        lt_of_le_of_ne (hmax u hu) (fun heq => hps (hf heq ▸ hu))
      have hdown' : ∀ u ∈ s, ∀ v, f v ≤ f u → v ∈ s := by
        intro u hu v hv
        have hvin := hdown u (Finset.mem_insert_of_mem hu) v hv
        rcases Finset.mem_insert.mp hvin with rfl | hvs
        · exact (not_le_of_gt (hlt u hu) hv).elim
        · exact hvs
      have hlowerSub : {x : V | f x < f p} ⊆ (s : Set V) := by
        intro x hx
        have hx' : f x < f p := hx
        have hxin := hdown p (Finset.mem_insert_self p s) x hx'.le
        exact (Finset.mem_insert.mp hxin).resolve_left (fun heq => hx'.ne (congrArg f heq))
      have hconn' : (G.induce (s : Set V)).Preconnected := by
        apply preconnected_induce_of_preconnected_insert G (s : Set V) p
        · rw [← Finset.coe_insert]
          exact hconn
        · intro u v hpu hpv
          let φ : (G.induce {x : V | f x < f p}) →g G.induce (s : Set V) := {
            toFun x := ⟨x, hlowerSub x.2⟩
            map_rel' h := h
          }
          exact (hlower p ⟨u, hlt u u.2⟩ ⟨v, hlt v v.2⟩ hpu hpv).map φ
      by_cases hpr : f p < r
      · have heq : ((insert p s : Finset V) : Set V) ∩ {x | f x < r} =
            ((insert p s : Finset V) : Set V) := by
          apply inter_eq_left.mpr
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxs
          · exact hpr
          · exact (hlt x hxs).trans hpr
        rw [heq]
        exact hconn
      · have heq : ((insert p s : Finset V) : Set V) ∩ {x | f x < r} =
            (s : Set V) ∩ {x | f x < r} := by
          ext x
          constructor
          · rintro ⟨hx, hxr⟩
            exact ⟨(Finset.mem_insert.mp hx).resolve_left (fun heq => hpr (heq ▸ hxr)), hxr⟩
          · exact fun hx => ⟨Finset.mem_insert_of_mem hx.1, hx.2⟩
        rw [heq]
        exact ih hdown' hconn' r
  let _ : Fintype V := Fintype.ofFinite V
  have hconn : (G.induce ((Finset.univ : Finset V) : Set V)).Preconnected := by
    intro u v
    let φ : G →g G.induce ((Finset.univ : Finset V) : Set V) := {
      toFun x := ⟨x, Finset.mem_univ x⟩
      map_rel' h := h
    }
    exact (hG u v).map φ
  have hresult := hfinite Finset.univ (fun _ _ v _ => Finset.mem_univ v) hconn r
  rw [Finset.coe_univ, univ_inter] at hresult
  exact hresult

end DifferentialGeometry.Topology.Combinatorics
