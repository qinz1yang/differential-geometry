import DifferentialGeometry.Topology.Algebra.Group.IndexBound
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace MulAction

open scoped Topology

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [PseudoMetricSpace X] [MulAction G X] [IsIsometricSMul G X]

theorem exists_index_bound_small_displacement (x : X)
    (hK : IsCompact {g : G | dist (g • x) x ≤ 1})
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ Γ : Subgroup G,
      let L := Subgroup.closure {g : Γ | dist ((g : G) • x) x < ε}
      ENat.card (L ⧸ Subgroup.closure {g : L | ((g : Γ) : G) ∈ U}) ≤ (N : ℕ∞) := by
  classical
  obtain ⟨W, hW, hWone, hWW⟩ := exists_open_nhds_one_split hU
  let V : Set G := W ∩ Inv.inv ⁻¹' W
  have hV : IsOpen V := hW.inter (hW.preimage continuous_inv)
  have hVone : (1 : G) ∈ V := ⟨hWone, by
    change (1 : G)⁻¹ ∈ W
    simpa only [inv_one] using hWone⟩
  have hVdiff (v w : G) (hv : v ∈ V) (hw : w ∈ V) : v⁻¹ * w ∈ U :=
    hWW _ hv.2 _ hw.1
  have hcover : {g : G | dist (g • x) x ≤ 1} ⊆
      ⋃ c : G, (fun v : G => c * v) '' V := by
    intro g _
    exact Set.mem_iUnion.mpr ⟨g, 1, hVone, mul_one g⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c : G => (fun v : G => c * v) '' V)
    (fun c => isOpenMap_mul_left c V hV) hcover
  let N := t.card
  let ε : ℝ := 1 / ((N : ℝ) + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hNε : (N : ℝ) * ε ≤ 1 := by
    dsimp [ε]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hmul (g h : G) : dist ((g * h) • x) x ≤ dist (g • x) x + dist (h • x) x := by
    rw [mul_smul]
    calc
      _ ≤ dist (g • (h • x)) (g • x) + dist (g • x) x := dist_triangle _ _ _
      _ = _ := by rw [dist_smul, add_comm]
  have hinv (g : G) : dist (g⁻¹ • x) x = dist (g • x) x := by
    rw [← dist_smul g (g⁻¹ • x) x, smul_inv_smul, dist_comm]
  refine ⟨ε, hε, N, ?_⟩
  intro Γ
  let S : Set Γ := {g : Γ | dist ((g : G) • x) x < ε}
  let L : Subgroup Γ := Subgroup.closure S
  let j : L →* G := Γ.subtype.comp L.subtype
  let H : Subgroup L := Subgroup.closure {g : L | j g ∈ U}
  change ENat.card (L ⧸ H) ≤ (N : ℕ∞)
  let T : Set L := Subtype.val ⁻¹' S
  have hT : Subgroup.closure T = ⊤ := Subgroup.closure_closure_coe_preimage
  let P : Group.Generators L T := Group.Generators.ofSet hT
  have hgen (i : T) : dist (j (P.val i) • x) x < ε := i.property
  have hletter (a : T × Bool) : dist (j (P.wordProd [a]) • x) x ≤ ε := by
    rcases a with ⟨i, b⟩
    cases b
    · simpa [P.wordProd_singleton, hinv] using (hgen i).le
    · simpa [P.wordProd_singleton] using (hgen i).le
  have hword (l : List (T × Bool)) :
      dist (j (P.wordProd l) • x) x ≤ (l.length : ℝ) * ε := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have hprod : P.wordProd (a :: l) = P.wordProd [a] * P.wordProd l :=
        P.wordProd_append [a] l
      rw [hprod, map_mul]
      calc
        _ ≤ dist (j (P.wordProd [a]) • x) x + dist (j (P.wordProd l) • x) x := hmul _ _
        _ ≤ ε + (l.length : ℝ) * ε := add_le_add (hletter a) ih
        _ = ((a :: l).length : ℝ) * ε := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
  have hball (g : L) (hg : P.wordLength g ≤ N) : dist (j g • x) x ≤ 1 := by
    obtain ⟨l, hl, rfl⟩ := (P.wordLength_le_iff g).mp hg
    refine (hword l).trans ((mul_le_mul_of_nonneg_right ?_ hε.le).trans hNε)
    exact_mod_cast hl
  let Q : Set (L ⧸ H) := (QuotientGroup.mk : L → L ⧸ H) '' {g | P.wordLength g ≤ N}
  let r (q : Q) : L := Classical.choose q.property
  have hr (q : Q) : P.wordLength (r q) ≤ N ∧ QuotientGroup.mk (r q) = (q : L ⧸ H) :=
    Classical.choose_spec q.property
  have hchoice (q : Q) : ∃ c : t, j (r q) ∈ (fun v : G => (c : G) * v) '' V := by
    have hmem := ht (hball (r q) (hr q).1)
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨hct, hcV⟩ := Set.mem_iUnion.mp hc
    exact ⟨⟨c, hct⟩, hcV⟩
  let c (q : Q) : t := Classical.choose (hchoice q)
  have hc (q : Q) : j (r q) ∈ (fun v : G => (c q : G) * v) '' V :=
    Classical.choose_spec (hchoice q)
  have hcinj : Function.Injective c := by
    intro q q' heq
    obtain ⟨v, hv, hvq⟩ := hc q
    obtain ⟨w, hw, hwq⟩ := hc q'
    have hdiff : (j (r q))⁻¹ * j (r q') ∈ U := by
      rw [← hvq, ← hwq, ← heq]
      simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hVdiff v w hv hw
    have hmemH : (r q)⁻¹ * r q' ∈ H := by
      apply Subgroup.subset_closure
      change j ((r q)⁻¹ * r q') ∈ U
      simpa only [map_mul, map_inv] using hdiff
    have hq : (QuotientGroup.mk (r q) : L ⧸ H) = QuotientGroup.mk (r q') :=
      QuotientGroup.eq.mpr hmemH
    exact Subtype.ext ((hr q).2.symm.trans (hq.trans (hr q').2))
  have hQ : Q.encard ≤ (N : ℕ∞) := by
    change ENat.card Q ≤ (N : ℕ∞)
    calc
      _ ≤ ENat.card t := ENat.card_le_card_of_injective hcinj
      _ = _ := by simp [N]
  exact Subgroup.enat_card_quotient_le_of_encard_wordLength_le P H N hQ

end MulAction
