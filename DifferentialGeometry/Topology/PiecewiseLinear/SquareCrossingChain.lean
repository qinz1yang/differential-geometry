/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Thickening
import DifferentialGeometry.Topology.Connected.SeparatingComponent

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_dist_lt_chain_of_isPreconnected {α : Type*} [PseudoMetricSpace α] {C : Set α}
    (hC : IsPreconnected C) {x y : α} (hx : x ∈ C) (hy : y ∈ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (c : ℕ → α), c 0 = x ∧ c m = y ∧ (∀ i ≤ m, c i ∈ C) ∧
      ∀ i < m, dist (c i) (c (i + 1)) < ε := by
  classical
  let A : Set α := {z | z ∈ C ∧ ∃ (m : ℕ) (c : ℕ → α), c 0 = x ∧ c m = z ∧
    (∀ i ≤ m, c i ∈ C) ∧ ∀ i < m, dist (c i) (c (i + 1)) < ε}
  have hxA : x ∈ A := ⟨hx, 0, fun _ => x, rfl, rfl, fun _ _ => hx, fun i hi => absurd hi
    (Nat.not_lt_zero i)⟩
  have hext : ∀ z ∈ A, ∀ z' ∈ C, dist z z' < ε → z' ∈ A := by
    rintro z ⟨-, m, c, hc0, hcm, hcC, hcd⟩ z' hz' hzz'
    refine ⟨hz', m + 1, fun i => if i ≤ m then c i else z', ?_, ?_, ?_, ?_⟩
    · simp only [Nat.zero_le, ↓reduceIte, hc0]
    · simp only [Nat.not_succ_le_self, ↓reduceIte]
    · intro i hi
      by_cases him : i ≤ m
      · simp only [him, ↓reduceIte]
        exact hcC i him
      · simp only [him, ↓reduceIte]
        exact hz'
    · intro i hi
      by_cases him : i + 1 ≤ m
      · simp only [him, ↓reduceIte, show i ≤ m by omega]
        exact hcd i (by omega)
      · have hieq : i = m := by omega
        subst hieq
        simp only [le_refl, ↓reduceIte, Nat.not_succ_le_self]
        rw [hcm]
        exact hzz'
  have hsub : C ⊆ A := by
    have hcov : C ⊆ Metric.thickening ε A ∪ (closure A)ᶜ := by
      intro z hz
      by_cases hzc : z ∈ closure A
      · obtain ⟨a, ha, hza⟩ := Metric.mem_closure_iff.mp hzc ε hε
        exact Or.inl (Metric.mem_thickening_iff.mpr ⟨a, ha, hza⟩)
      · exact Or.inr hzc
    have hdis : C ∩ (Metric.thickening ε A ∩ (closure A)ᶜ) = ∅ := by
      apply eq_empty_of_forall_notMem
      rintro z ⟨hz, hzt, hzc⟩
      obtain ⟨a, ha, hza⟩ := Metric.mem_thickening_iff.mp hzt
      exact hzc (subset_closure (hext a ha z hz (by rw [dist_comm]; exact hza)))
    rcases isPreconnected_iff_subset_of_disjoint.mp hC _ _ Metric.isOpen_thickening
      isClosed_closure.isOpen_compl hcov hdis with h | h
    · intro z hz
      obtain ⟨a, ha, hza⟩ := Metric.mem_thickening_iff.mp (h hz)
      exact hext a ha z hz (by rw [dist_comm]; exact hza)
    · exact absurd (subset_closure hxA) (h hx)
  obtain ⟨-, m, c, hc0, hcm, hcC, hcd⟩ := hsub hy
  exact ⟨m, c, hc0, hcm, hcC, hcd⟩

theorem finite_connectedComponents_of_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*}
    [Finite ι] {A : ι → Set X} (hA : ∀ i, IsPreconnected (A i)) :
    Finite (ConnectedComponents ↥(⋃ i, A i)) := by
  classical
  by_cases hne : (⋃ i, A i).Nonempty
  · let c₀ : ↥(⋃ i, A i) := ⟨hne.some, hne.some_mem⟩
    let f : ι → ConnectedComponents ↥(⋃ i, A i) := fun i =>
      if h : (A i).Nonempty then
        ConnectedComponents.mk (⟨h.some, mem_iUnion.mpr ⟨i, h.some_mem⟩⟩ : ↥(⋃ i, A i))
      else ConnectedComponents.mk c₀
    refine Finite.of_surjective f fun c => ?_
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨i, hzi⟩ := mem_iUnion.mp z.2
    have hAi : (A i).Nonempty := ⟨z, hzi⟩
    refine ⟨i, ?_⟩
    simp only [f, dite_eq_left hAi]
    apply ConnectedComponents.coe_eq_coe'.mpr
    have hsubA : A i ⊆ connectedComponentIn (⋃ i, A i) z.1 :=
      (hA i).subset_connectedComponentIn hzi (subset_iUnion A i)
    have hmem := hsubA hAi.some_mem
    rw [connectedComponentIn_eq_image z.2] at hmem
    obtain ⟨w, hw, hweq⟩ := hmem
    have hw' : w = ⟨hAi.some, mem_iUnion.mpr ⟨i, hAi.some_mem⟩⟩ := Subtype.ext hweq
    rw [← hw']
    exact hw
  · have hemp : (⋃ i, A i) = ∅ := not_nonempty_iff_eq_empty.mp hne
    have : Finite ↥(⋃ i, A i) := by
      rw [hemp]
      exact Finite.of_subsingleton
    exact Finite.of_surjective _ ConnectedComponents.surjective_coe

theorem exists_nat_lt_div_le_le_succ_div {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ i < n, (i : ℝ) / n ≤ x ∧ x ≤ ((i : ℝ) + 1) / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · refine ⟨n - 1, by omega, ?_, ?_⟩
    · rw [h1, div_le_one hnpos]
      exact_mod_cast Nat.sub_le n 1
    · rw [h1, le_div_iff₀ hnpos, one_mul]
      have : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel]
      rw [this]
  · have hxn : 0 ≤ x * n := mul_nonneg hx.1 hnpos.le
    refine ⟨⌊x * n⌋₊, (Nat.floor_lt hxn).mpr (by nlinarith), ?_, ?_⟩
    · rw [div_le_iff₀ hnpos]
      exact Nat.floor_le hxn
    · rw [le_div_iff₀ hnpos]
      exact (Nat.lt_floor_add_one (x * n)).le

theorem exists_chain_left_right_of_no_crossing {G : Set (ℝ × ℝ)}
    (hGQ : G ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    (hL : ∀ u ∈ Icc (0 : ℝ) 1, ((0 : ℝ), u) ∈ G) (hR : ∀ u ∈ Icc (0 : ℝ) 1, ((1 : ℝ), u) ∈ G)
    (hno : ∀ c : Set (ℝ × ℝ), IsPreconnected c → c ⊆ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ G →
      ∀ a ∈ c, ∀ b ∈ c, a.2 = 0 → b.2 = 1 → False)
    {η : ℝ} (hη : 0 < η) :
    ∃ (m : ℕ) (g : ℕ → ℝ × ℝ), g 0 = (0, 0) ∧ g m = (1, 0) ∧ (∀ i ≤ m, g i ∈ G) ∧
      ∀ i < m, dist (g i) (g (i + 1)) < η := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / η)
  have h3η : 0 < 3 / η := by positivity
  have hnR : (0 : ℝ) < n := h3η.trans hn
  have hnpos : 0 < n := by exact_mod_cast hnR
  have hn' : (1 : ℝ) / n < η / 3 := by
    rw [div_lt_div_iff₀ hnR (by norm_num : (0 : ℝ) < 3)]
    rw [div_lt_iff₀ hη] at hn
    linarith
  let sq : ℕ → ℕ → Set (ℝ × ℝ) := fun i j =>
    Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n) ×ˢ Icc ((j : ℝ) / n) (((j : ℝ) + 1) / n)
  have hsqQ : ∀ i < n, ∀ j < n, sq i j ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    intro i hi j hj p hp
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    refine ⟨⟨le_trans (by positivity) hp.1.1, le_trans hp.1.2 ?_⟩,
      ⟨le_trans (by positivity) hp.2.1, le_trans hp.2.2 ?_⟩⟩
    · rw [div_le_one hnR]
      exact hi'
    · rw [div_le_one hnR]
      exact hj'
  let BL : Set (ℝ × ℝ) := Iic (0 : ℝ) ×ˢ Icc (0 : ℝ) 1
  let BR : Set (ℝ × ℝ) := Ici (1 : ℝ) ×ˢ Icc (0 : ℝ) 1
  let P : (Fin n × Fin n) ⊕ Bool → Set (ℝ × ℝ) := fun k => match k with
    | Sum.inl p => if (sq p.1 p.2 ∩ G).Nonempty then sq p.1 p.2 else ∅
    | Sum.inr false => BL
    | Sum.inr true => BR
  have hPconn : ∀ k, IsPreconnected (P k) := by
    intro k
    rcases k with p | b
    · by_cases hp : (sq p.1 p.2 ∩ G).Nonempty
      · simp only [P, ite_eq_left hp]
        exact ((convex_Icc _ _).prod (convex_Icc _ _)).isPreconnected
      · simp only [P, ite_eq_right hp]
        exact isPreconnected_empty
    · cases b
      · exact ((convex_Iic _).prod (convex_Icc _ _)).isPreconnected
      · exact ((convex_Ici _).prod (convex_Icc _ _)).isPreconnected
  have hPcl : ∀ k, IsClosed (P k) := by
    intro k
    rcases k with p | b
    · by_cases hp : (sq p.1 p.2 ∩ G).Nonempty
      · simp only [P, ite_eq_left hp]
        exact isClosed_Icc.prod isClosed_Icc
      · simp only [P, ite_eq_right hp]
        exact isClosed_empty
    · cases b
      · exact isClosed_Iic.prod isClosed_Icc
      · exact isClosed_Ici.prod isClosed_Icc
  have hPy : ∀ k, ∀ p ∈ P k, p.2 ∈ Icc (0 : ℝ) 1 := by
    intro k p hp
    rcases k with q | b
    · by_cases hq : (sq q.1 q.2 ∩ G).Nonempty
      · simp only [P, ite_eq_left hq] at hp
        exact (hsqQ q.1 q.1.2 q.2 q.2.2 hp).2
      · simp only [P, ite_eq_right hq] at hp
        exact absurd hp (notMem_empty p)
    · cases b
      · exact hp.2
      · exact hp.2
  let Cp : Set (ℝ × ℝ) := ⋃ k, P k
  have hCpcl : IsClosed Cp := isClosed_iUnion_of_finite hPcl
  have hBLCp : BL ⊆ Cp := subset_iUnion P (Sum.inr false)
  have hBRCp : BR ⊆ Cp := subset_iUnion P (Sum.inr true)
  have hGCp : G ⊆ Cp := by
    intro z hz
    obtain ⟨i, hi, hi1, hi2⟩ := exists_nat_lt_div_le_le_succ_div hnpos (hGQ hz).1
    obtain ⟨j, hj, hj1, hj2⟩ := exists_nat_lt_div_le_le_succ_div hnpos (hGQ hz).2
    have hzsq : z ∈ sq i j := ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩
    refine mem_iUnion.mpr ⟨Sum.inl (⟨i, hi⟩, ⟨j, hj⟩), ?_⟩
    have hne : (sq i j ∩ G).Nonempty := ⟨z, hzsq, hz⟩
    simp only [P, ite_eq_left hne]
    exact hzsq
  have hnear : ∀ z ∈ Cp, 0 < z.1 → z.1 < 1 → ∃ g ∈ G, dist z g ≤ 1 / n := by
    intro z hz hz0 hz1
    obtain ⟨k, hzk⟩ := mem_iUnion.mp hz
    rcases k with p | b
    · by_cases hp : (sq p.1 p.2 ∩ G).Nonempty
      · simp only [P, ite_eq_left hp] at hzk
        obtain ⟨g, hgsq, hgG⟩ := hp
        refine ⟨g, hgG, ?_⟩
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
        have e1 : ((p.1 : ℝ) + 1) / n - (p.1 : ℝ) / n = 1 / n := by ring
        have e2 : ((p.2 : ℝ) + 1) / n - (p.2 : ℝ) / n = 1 / n := by ring
        constructor
        · rw [abs_le]
          constructor <;> linarith [hzk.1.1, hzk.1.2, hgsq.1.1, hgsq.1.2]
        · rw [abs_le]
          constructor <;> linarith [hzk.2.1, hzk.2.2, hgsq.2.1, hgsq.2.2]
      · simp only [P, ite_eq_right hp] at hzk
        exact absurd hzk (notMem_empty z)
    · cases b
      · exact absurd hzk.1 (not_le.mpr hz0)
      · exact absurd hzk.1 (not_le.mpr hz1)
  have hHC : {p : ℝ × ℝ | p.2 < 0} ⊆ Cpᶜ := by
    intro p hp hpC
    obtain ⟨k, hk⟩ := mem_iUnion.mp hpC
    exact absurd (hPy k p hk).1 (not_le.mpr hp)
  have hKC : {p : ℝ × ℝ | 1 < p.2} ⊆ Cpᶜ := by
    intro p hp hpC
    obtain ⟨k, hk⟩ := mem_iUnion.mp hpC
    exact absurd (hPy k p hk).2 (not_le.mpr hp)
  have hsep : DifferentialGeometry.Topology.Separates Cp {p : ℝ × ℝ | p.2 < 0}
      {p : ℝ × ℝ | 1 < p.2} := by
    refine DifferentialGeometry.Topology.separates_of_not_joinedIn hCpcl hHC hKC ?_
    intro x hx y hy hj
    let γ := hj.somePath
    have hγC : ∀ t, γ t ∈ Cpᶜ := hj.somePath_mem
    let f : ℝ → ℝ := fun t => (γ.extend t).2
    have hfc : Continuous f := continuous_snd.comp γ.continuous_extend
    have hf0 : f 0 < 0 := by
      change (γ.extend 0).2 < 0
      rw [Path.extend_zero]
      exact hx
    have hf1 : 1 < f 1 := by
      change 1 < (γ.extend 1).2
      rw [Path.extend_one]
      exact hy
    obtain ⟨c, hc, hfc0⟩ := intermediate_value_Icc zero_le_one hfc.continuousOn
      ⟨hf0.le, by linarith⟩
    obtain ⟨d, hd, hfd1⟩ := intermediate_value_Icc hc.2 hfc.continuousOn
      ⟨by rw [hfc0]; exact zero_le_one, hf1.le⟩
    let A₀ : Set ℝ := {t | t ∈ Icc c d ∧ f t ≤ 0}
    have hA₀c : IsClosed A₀ := isClosed_Icc.inter (isClosed_le hfc continuous_const)
    have hA₀ne : A₀.Nonempty := ⟨c, ⟨le_rfl, hd.1⟩, hfc0.le⟩
    have hA₀bdd : BddAbove A₀ := ⟨d, fun t ht => ht.1.2⟩
    let a := sSup A₀
    have haA : a ∈ A₀ := hA₀c.csSup_mem hA₀ne hA₀bdd
    have hfa : f a = 0 := by
      apply le_antisymm haA.2
      by_contra hneg
      push Not at hneg
      have had : a < d := by
        rcases eq_or_lt_of_le haA.1.2 with h | h
        · exfalso
          rw [h, hfd1] at hneg
          linarith
        · exact h
      obtain ⟨e, he, hfe⟩ := intermediate_value_Icc had.le hfc.continuousOn
        ⟨hneg.le, by rw [hfd1]; exact zero_le_one⟩
      have heA : e ∈ A₀ := ⟨⟨haA.1.1.trans he.1, he.2⟩, hfe.le⟩
      have hea : e ≤ a := le_csSup hA₀bdd heA
      have hae : e = a := le_antisymm hea he.1
      rw [hae] at hfe
      linarith
    let B₀ : Set ℝ := {t | t ∈ Icc a d ∧ 1 ≤ f t}
    have hB₀c : IsClosed B₀ := isClosed_Icc.inter (isClosed_le continuous_const hfc)
    have hB₀ne : B₀.Nonempty := ⟨d, ⟨haA.1.2, le_rfl⟩, hfd1.ge⟩
    have hB₀bdd : BddBelow B₀ := ⟨a, fun t ht => ht.1.1⟩
    let b := sInf B₀
    have hbB : b ∈ B₀ := hB₀c.csInf_mem hB₀ne hB₀bdd
    have hfb : f b = 1 := by
      apply le_antisymm _ hbB.2
      by_contra hbig
      push Not at hbig
      have hab : a < b := by
        rcases eq_or_lt_of_le hbB.1.1 with h | h
        · exfalso
          rw [← h, hfa] at hbig
          linarith
        · exact h
      obtain ⟨e, he, hfe⟩ := intermediate_value_Icc hab.le hfc.continuousOn
        ⟨by rw [hfa]; exact zero_le_one, hbig.le⟩
      have heB : e ∈ B₀ := ⟨⟨he.1, he.2.trans hbB.1.2⟩, hfe.ge⟩
      have hbe : b ≤ e := csInf_le hB₀bdd heB
      have heb : e = b := le_antisymm he.2 hbe
      rw [heb] at hfe
      linarith
    have hrange : ∀ t ∈ Icc a b, f t ∈ Icc (0 : ℝ) 1 := by
      intro t ht
      constructor
      · by_contra hneg
        push Not at hneg
        rcases eq_or_lt_of_le ht.1 with h | h
        · rw [← h, hfa] at hneg
          linarith
        · have htA : t ∈ A₀ := ⟨⟨haA.1.1.trans ht.1, ht.2.trans hbB.1.2⟩, hneg.le⟩
          exact absurd (le_csSup hA₀bdd htA) (not_le.mpr h)
      · by_contra hbig
        push Not at hbig
        rcases eq_or_lt_of_le ht.2 with h | h
        · rw [h, hfb] at hbig
          linarith
        · have htB : t ∈ B₀ := ⟨⟨ht.1, ht.2.trans hbB.1.2⟩, hbig.le⟩
          exact absurd (csInf_le hB₀bdd htB) (not_le.mpr h)
    have hsub01 : Icc a b ⊆ Icc (0 : ℝ) 1 := fun t ht =>
      ⟨hc.1.trans (haA.1.1.trans ht.1), ht.2.trans (hbB.1.2.trans hd.2)⟩
    apply hno (γ.extend '' Icc a b) (isPreconnected_Icc.image _ γ.continuous_extend.continuousOn)
    · rintro _ ⟨t, ht, rfl⟩
      have hγt : γ.extend t = γ ⟨t, hsub01 ht⟩ := Path.extend_extends' γ ⟨t, hsub01 ht⟩
      have hnotC : γ.extend t ∉ Cp := by
        rw [hγt]
        exact hγC _
      have hy01 := hrange t ht
      have hx0 : 0 < (γ.extend t).1 := by
        by_contra hle
        push Not at hle
        exact hnotC (hBLCp ⟨hle, hy01⟩)
      have hx1 : (γ.extend t).1 < 1 := by
        by_contra hle
        push Not at hle
        exact hnotC (hBRCp ⟨hle, hy01⟩)
      exact ⟨⟨⟨hx0.le, hx1.le⟩, hy01⟩, fun hG => hnotC (hGCp hG)⟩
    · exact ⟨a, ⟨le_rfl, hbB.1.1⟩, rfl⟩
    · exact ⟨b, ⟨hbB.1.1, le_rfl⟩, rfl⟩
    · exact hfa
    · exact hfb
  have : Finite (ConnectedComponents ↥Cp) := finite_connectedComponents_of_iUnion hPconn
  have hHeq : {p : ℝ × ℝ | p.2 < 0} = univ ×ˢ Iio 0 := by
    ext p
    simp
  have hKeq : {p : ℝ × ℝ | 1 < p.2} = univ ×ˢ Ioi 1 := by
    ext p
    simp
  have hHconn : IsConnected {p : ℝ × ℝ | p.2 < 0} := by
    rw [hHeq]
    exact ⟨⟨(0, -1), mem_univ _, by norm_num⟩, (convex_univ.prod (convex_Iio 0)).isPreconnected⟩
  have hKconn : IsConnected {p : ℝ × ℝ | 1 < p.2} := by
    rw [hKeq]
    exact ⟨⟨(0, 2), mem_univ _, by norm_num⟩, (convex_univ.prod (convex_Ioi 1)).isPreconnected⟩
  obtain ⟨z₀, -, hsep₁⟩ :=
    DifferentialGeometry.Topology.exists_separating_component hCpcl hHconn hKconn hsep
  have hC₁Cp : connectedComponentIn Cp z₀ ⊆ Cp := connectedComponentIn_subset Cp z₀
  have hyC : ∀ p ∈ Cp, p.2 ∈ Icc (0 : ℝ) 1 := fun p hp => by
    obtain ⟨k, hk⟩ := mem_iUnion.mp hp
    exact hPy k p hk
  have hbarrier : ∀ B : Set (ℝ × ℝ), B ⊆ Cp → IsPreconnected B → ∀ x₀ : ℝ,
      (∀ s ∈ Icc (0 : ℝ) 1, (x₀, s) ∈ B) → B ⊆ connectedComponentIn Cp z₀ := by
    intro B hBCp hB x₀ hxB
    by_cases hmeet : (B ∩ connectedComponentIn Cp z₀).Nonempty
    · obtain ⟨w, hwB, hwC⟩ := hmeet
      rw [connectedComponentIn_eq hwC]
      exact hB.subset_connectedComponentIn hwB hBCp
    · exfalso
      have hV : IsPreconnected ((fun s : ℝ => (x₀, s)) '' Icc (-1) 2) :=
        isPreconnected_Icc.image _ (by fun_prop : Continuous fun s : ℝ => (x₀, s)).continuousOn
      have hVC : (fun s : ℝ => (x₀, s)) '' Icc (-1) 2 ⊆ (connectedComponentIn Cp z₀)ᶜ := by
        rintro _ ⟨s, hs, rfl⟩ hsC
        by_cases hs01 : s ∈ Icc (0 : ℝ) 1
        · exact hmeet ⟨(x₀, s), hxB s hs01, hsC⟩
        · exact hs01 (hyC _ (hC₁Cp hsC))
      have hmem := hV.subset_connectedComponentIn (x := (x₀, -1))
        ⟨-1, ⟨le_rfl, by norm_num⟩, rfl⟩ hVC ⟨2, ⟨by norm_num, le_rfl⟩, rfl⟩
      exact hsep₁.not_mem_connectedComponentIn
        (show (x₀, (-1 : ℝ)) ∈ {p : ℝ × ℝ | p.2 < 0} by norm_num)
        (show (x₀, (2 : ℝ)) ∈ {p : ℝ × ℝ | 1 < p.2} by norm_num) hmem
  have hBLC : BL ⊆ connectedComponentIn Cp z₀ := hbarrier BL hBLCp
    ((convex_Iic _).prod (convex_Icc _ _)).isPreconnected (-1) fun s hs => ⟨by norm_num, hs⟩
  have hBRC : BR ⊆ connectedComponentIn Cp z₀ := hbarrier BR hBRCp
    ((convex_Ici _).prod (convex_Icc _ _)).isPreconnected 2 fun s hs => ⟨by norm_num, hs⟩
  have hhalf : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨m, c, hc0, hcm, hcC, hcd⟩ := exists_dist_lt_chain_of_isPreconnected
    isPreconnected_connectedComponentIn (hBLC (show ((0 : ℝ), (0 : ℝ)) ∈ BL from
      ⟨show (0 : ℝ) ≤ 0 from le_rfl, hhalf⟩)) (hBRC (show ((1 : ℝ), (0 : ℝ)) ∈ BR from
      ⟨show (1 : ℝ) ≤ 1 from le_rfl, hhalf⟩))
    (by positivity : 0 < η / 3)
  let cl : ℝ × ℝ → ℝ × ℝ := fun p => (max (min p.1 1) 0, p.2)
  have hcl_lip : ∀ p q : ℝ × ℝ, dist (cl p) (cl q) ≤ dist p q := by
    intro p q
    rw [Prod.dist_eq, Prod.dist_eq]
    refine max_le_max ?_ le_rfl
    rw [Real.dist_eq, Real.dist_eq]
    calc |max (min p.1 1) 0 - max (min q.1 1) 0| ≤ |min p.1 1 - min q.1 1| :=
          abs_max_sub_max_le_abs _ _ _
      _ ≤ max |p.1 - q.1| |1 - 1| := abs_min_sub_min_le_max _ _ _ _
      _ = |p.1 - q.1| := by simp
  have hclG : ∀ p ∈ Cp, cl p ∈ G ∨ (cl p ∈ Cp ∧ 0 < (cl p).1 ∧ (cl p).1 < 1) := by
    intro p hp
    have hy := hyC p hp
    by_cases h0 : p.1 ≤ 0
    · left
      have hcl : cl p = (0, p.2) := by
        simp only [cl, min_eq_left (h0.trans zero_le_one), max_eq_right h0]
      rw [hcl]
      exact hL _ hy
    by_cases h1 : 1 ≤ p.1
    · left
      have hcl : cl p = (1, p.2) := by
        simp only [cl, min_eq_right h1, max_eq_left zero_le_one]
      rw [hcl]
      exact hR _ hy
    push Not at h0 h1
    have hcl : cl p = p := by
      simp only [cl, min_eq_left h1.le, max_eq_left h0.le]
    right
    rw [hcl]
    exact ⟨hp, h0, h1⟩
  let pr : ℝ × ℝ → ℝ × ℝ := fun q =>
    if q ∈ G then q else if h : ∃ g ∈ G, dist q g ≤ 1 / n then h.choose else q
  have hprG : ∀ p ∈ Cp, pr (cl p) ∈ G ∧ dist (pr (cl p)) (cl p) ≤ 1 / n := by
    intro p hp
    by_cases hG : cl p ∈ G
    · simp only [pr, ite_eq_left hG]
      exact ⟨hG, by rw [dist_self]; positivity⟩
    · rcases hclG p hp with hG' | ⟨hC, h0, h1⟩
      · exact absurd hG' hG
      · have hex := hnear (cl p) hC h0 h1
        simp only [pr, ite_eq_right hG, dite_eq_left hex]
        exact ⟨hex.choose_spec.1, by rw [dist_comm]; exact hex.choose_spec.2⟩
  have hG0 : ((0 : ℝ), (0 : ℝ)) ∈ G := hL _ hhalf
  have hG1 : ((1 : ℝ), (0 : ℝ)) ∈ G := hR _ hhalf
  have hcl0 : cl ((0 : ℝ), (0 : ℝ)) = ((0 : ℝ), 0) := by
    simp only [cl, min_eq_left zero_le_one, max_self]
  have hcl1 : cl ((1 : ℝ), (0 : ℝ)) = ((1 : ℝ), 0) := by
    simp only [cl, min_self, max_eq_left zero_le_one]
  refine ⟨m, fun i => pr (cl (c i)), ?_, ?_, ?_, ?_⟩
  · simp only [hc0, hcl0, pr, ite_eq_left hG0]
  · simp only [hcm, hcl1, pr, ite_eq_left hG1]
  · intro i hi
    exact (hprG (c i) (hC₁Cp (hcC i hi))).1
  · intro i hi
    have h1 := hprG (c i) (hC₁Cp (hcC i hi.le))
    have h2 := hprG (c (i + 1)) (hC₁Cp (hcC (i + 1) hi))
    have h3 := hcl_lip (c i) (c (i + 1))
    have h4 := hcd i hi
    have h5 := dist_triangle4 (pr (cl (c i))) (cl (c i)) (cl (c (i + 1)))
      (pr (cl (c (i + 1))))
    rw [dist_comm (cl (c (i + 1)))] at h5
    change dist (pr (cl (c i))) (pr (cl (c (i + 1)))) < η
    linarith [h1.2, h2.2]

end DifferentialGeometry.Topology.PiecewiseLinear
