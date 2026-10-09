import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonJordan

/-!
# Innermost bigons of a periodic curve family

A height function `g : ℝ → ℝ` of period one crosses the integer levels at the points of
`crossSet g`. An upper arc is a pair of consecutive crossings at the same level `k` with the
heights in `(k, k + 1)` in between. If the crossings are transverse and some crossing exists,
an upper arc exists: around a global maximum of `g` the largest attained integer level is left
and re-entered. Transversality also makes the crossings in a period finite, so among the upper
arcs (up to integer shifts) one with minimal horizontal extent exists.

For a lift `Φ` of a torus diffeomorphism with matrix one, `γ t = Φ (t, 0)` and the lifted curve
family `Φ '' (ℝ × ℤ)`, the bigon of a minimal upper arc is empty (it meets the family only in its
own arc) and is disjoint from all its non-zero integer translates.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace GC.Seifert

def crossSet (g : ℝ → ℝ) : Set ℝ := {t | ∃ k : ℤ, g t = k}

structure IsUpperArc (g : ℝ → ℝ) (a b : ℝ) : Prop where
  lt : a < b
  level : ∃ k : ℤ, g a = k
  same : g b = g a
  between : ∀ t ∈ Ioo a b, g a < g t ∧ g t < g a + 1

section Periodic

variable {g : ℝ → ℝ}

theorem isClosed_crossSet (hg : Continuous g) : IsClosed (crossSet g) := by
  have : crossSet g = g ⁻¹' range ((↑) : ℤ → ℝ) := by
    ext t
    simp only [crossSet, mem_preimage, mem_range, mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
    · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
  rw [this]
  exact Real.isClosed_range_intCast.preimage hg

theorem crossSet_add_int (hper : ∀ t, g (t + 1) = g t) (t : ℝ) (m : ℤ) :
    g (t + m) = g t := by
  have hp : Function.Periodic g 1 := hper
  have := hp.int_mul m t
  rwa [mul_one] at this

theorem IsUpperArc.shift (hper : ∀ t, g (t + 1) = g t) {a b : ℝ} (h : IsUpperArc g a b)
    (m : ℤ) : IsUpperArc g (a + m) (b + m) := by
  refine ⟨by linarith [h.lt], ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := h.level
    exact ⟨k, by rw [crossSet_add_int hper, hk]⟩
  · rw [crossSet_add_int hper, crossSet_add_int hper, h.same]
  · intro t ht
    have ht' : t - m ∈ Ioo a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := h.between (t - m) ht'
    rw [show t = (t - m) + m by ring, crossSet_add_int hper, crossSet_add_int hper]
    exact this

theorem IsUpperArc.not_mem_crossSet {a b : ℝ} (h : IsUpperArc g a b) {t : ℝ}
    (ht : t ∈ Ioo a b) : t ∉ crossSet g := by
  rintro ⟨j, hj⟩
  obtain ⟨k, hk⟩ := h.level
  have h1 := h.between t ht
  rw [hj, hk] at h1
  have h2 : k < j := by exact_mod_cast h1.1
  have h3 : j < k + 1 := by exact_mod_cast h1.2
  omega

theorem IsUpperArc.right_eq {a b b' : ℝ} (h : IsUpperArc g a b) (h' : IsUpperArc g a b') :
    b = b' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.not_mem_crossSet ⟨h.lt, hlt⟩ ⟨_, (h.same.trans h.level.choose_spec)⟩
  · exact h.not_mem_crossSet ⟨h'.lt, hlt⟩ ⟨_, (h'.same.trans h'.level.choose_spec)⟩

theorem exists_upperArc (hg : Continuous g) (hper : ∀ t, g (t + 1) = g t)
    (htr : ∀ t ∈ crossSet g, deriv g t ≠ 0)
    (hne : (crossSet g).Nonempty) : ∃ a b, IsUpperArc g a b := by
  obtain ⟨t₀, ⟨k₀, hk₀⟩⟩ := hne
  obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr
    (show (0 : ℝ) ≤ 1 by norm_num)) hg.continuousOn
  have hglob : ∀ t, g t ≤ g tm := by
    intro t
    have h1 := hmax (show t - ⌊t⌋ ∈ Icc (0 : ℝ) 1 from
      ⟨by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩)
    have h2 : g (t - ⌊t⌋) = g t := by
      rw [show t - ⌊t⌋ = t + ((-⌊t⌋ : ℤ) : ℝ) by push_cast; ring, crossSet_add_int hper]
    rw [← h2]
    exact h1
  set K : ℤ := ⌊g tm⌋ with hKdef
  have hKle : (K : ℝ) ≤ g tm := Int.floor_le _
  have hKlt : g tm < K + 1 := Int.lt_floor_add_one _
  have hk₀K : k₀ ≤ K := Int.le_floor.mpr (hk₀ ▸ hglob t₀)
  have hKatt : ∃ u, g u = K := by
    rcases le_total t₀ tm with hle | hle
    · obtain ⟨u, -, hu⟩ := intermediate_value_Icc hle hg.continuousOn
        ⟨by rw [hk₀]; exact_mod_cast hk₀K, hKle⟩
      exact ⟨u, hu⟩
    · obtain ⟨u, -, hu⟩ := intermediate_value_Icc' hle hg.continuousOn
        ⟨by rw [hk₀]; exact_mod_cast hk₀K, hKle⟩
      exact ⟨u, hu⟩
  have hgt : (K : ℝ) < g tm := by
    rcases eq_or_lt_of_le hKle with heq | hlt
    · exfalso
      have hloc : IsLocalMax g tm := Filter.Eventually.of_forall hglob
      exact htr tm ⟨K, heq.symm⟩ hloc.deriv_eq_zero
    · exact hlt
  obtain ⟨u₀, hu₀⟩ := hKatt
  have hshift (u : ℝ) (m : ℤ) : g (u + m) = g u := crossSet_add_int hper u m
  set A := {u | u ≤ tm ∧ g u ≤ K}
  have hAne : A.Nonempty := by
    refine ⟨u₀ + ((-⌈u₀ - tm⌉ : ℤ) : ℝ), ?_, ?_⟩
    · push_cast
      linarith [Int.le_ceil (u₀ - tm)]
    · rw [hshift, hu₀]
  have hAbdd : BddAbove A := ⟨tm, fun u hu => hu.1⟩
  have hAcl : IsClosed A := (isClosed_le continuous_id continuous_const).inter
    (isClosed_le hg continuous_const)
  set a := sSup A
  have haA : a ∈ A := hAcl.csSup_mem hAne hAbdd
  set B := {u | tm ≤ u ∧ g u ≤ K}
  have hBne : B.Nonempty := by
    refine ⟨u₀ + ((⌈tm - u₀⌉ : ℤ) : ℝ), ?_, ?_⟩
    · linarith [Int.le_ceil (tm - u₀)]
    · rw [hshift, hu₀]
  have hBbdd : BddBelow B := ⟨tm, fun u hu => hu.1⟩
  have hBcl : IsClosed B := (isClosed_le continuous_const continuous_id).inter
    (isClosed_le hg continuous_const)
  set b := sInf B
  have hbB : b ∈ B := hBcl.csInf_mem hBne hBbdd
  have hatm : a < tm := lt_of_le_of_ne haA.1 (fun h => by
    have := haA.2; rw [h] at this; linarith)
  have hbtm : tm < b := lt_of_le_of_ne hbB.1 (fun h => by
    have := hbB.2; rw [← h] at this; linarith)
  have habove : ∀ t ∈ Ioo a b, (K : ℝ) < g t := by
    intro t ht
    by_contra hle
    push Not at hle
    rcases le_total t tm with h | h
    · exact absurd (le_csSup hAbdd ⟨h, hle⟩) (not_le.mpr ht.1)
    · exact absurd (csInf_le hBbdd ⟨h, hle⟩) (not_le.mpr ht.2)
  have hga : g a = K := by
    refine le_antisymm haA.2 ?_
    have hcl : a ∈ closure (Ioo a b) := by
      rw [closure_Ioo (hatm.trans hbtm).ne]
      exact ⟨le_rfl, (hatm.trans hbtm).le⟩
    exact ContinuousWithinAt.closure_le hcl continuousWithinAt_const hg.continuousWithinAt
      (fun t ht => (habove t ht).le)
  have hgb : g b = K := by
    refine le_antisymm hbB.2 ?_
    have hcl : b ∈ closure (Ioo a b) := by
      rw [closure_Ioo (hatm.trans hbtm).ne]
      exact ⟨(hatm.trans hbtm).le, le_rfl⟩
    exact ContinuousWithinAt.closure_le hcl continuousWithinAt_const hg.continuousWithinAt
      (fun t ht => (habove t ht).le)
  refine ⟨a, b, ⟨hatm.trans hbtm, ⟨K, hga⟩, hgb.trans hga.symm, fun t ht => ?_⟩⟩
  rw [hga]
  exact ⟨habove t ht, lt_of_le_of_lt (hglob t) hKlt⟩

theorem finite_of_isCompact_of_isolated {S : Set ℝ} (hS : IsCompact S)
    (hiso : ∀ t ∈ S, ∀ᶠ u in 𝓝[≠] t, u ∉ S) : S.Finite := by
  have hU : ∀ t ∈ S, ∃ U ∈ 𝓝 t, ∀ u ∈ U, u ∈ S → u = t := by
    intro t ht
    obtain ⟨U, hUo, htU, hUs⟩ := mem_nhdsWithin.mp (hiso t ht)
    refine ⟨U, hUo.mem_nhds htU, fun u hu huS => ?_⟩
    by_contra hne
    exact hUs ⟨hu, hne⟩ huS
  choose! U hUn hUs using hU
  obtain ⟨F, hFS, hcover⟩ := hS.elim_nhds_subcover U hUn
  apply F.finite_toSet.subset
  intro u hu
  obtain ⟨t, ht, hut⟩ := mem_iUnion₂.mp (hcover hu)
  rw [hUs t (hFS t ht) u hut hu]
  exact ht

theorem finite_crossSet_Icc (hg : Continuous g) (hdiff : Differentiable ℝ g)
    (htr : ∀ t ∈ crossSet g, deriv g t ≠ 0) (a b : ℝ) : (crossSet g ∩ Icc a b).Finite := by
  refine finite_of_isCompact_of_isolated (isCompact_Icc.inter_left (isClosed_crossSet hg)) ?_
  · rintro t ⟨⟨k, hk⟩, -⟩
    have hne := (hdiff t).hasDerivAt.eventually_ne (c := g t) (htr t ⟨k, hk⟩)
    have hnear : ∀ᶠ u in 𝓝 t, |g u - g t| < 1 / 2 := by
      have := hg.continuousAt (x := t)
      exact (Metric.tendsto_nhds.mp this) (1 / 2) (by norm_num) |>.mono fun u hu => by
        rwa [Real.dist_eq] at hu
    filter_upwards [hne, nhdsWithin_le_nhds hnear] with u hu hu'
    rintro ⟨⟨j, hj⟩, -⟩
    apply hu
    rw [hj, hk] at hu' ⊢
    have h1 : |((j - k : ℤ) : ℝ)| < 1 / 2 := by push_cast; exact hu'
    have h2 : j - k = 0 := by
      by_contra hjk
      have : (1 : ℝ) ≤ |((j - k : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hjk
      linarith
    have : j = k := by omega
    rw [this]

theorem exists_minimal_upperArc (hg : Continuous g) (hper : ∀ t, g (t + 1) = g t)
    (hdiff : Differentiable ℝ g) (htr : ∀ t ∈ crossSet g, deriv g t ≠ 0)
    (hne : (crossSet g).Nonempty) {x : ℝ → ℝ} (hx : ∀ t, x (t + 1) = x t + 1) :
    ∃ a b, IsUpperArc g a b ∧ ∀ a' b', IsUpperArc g a' b' → |x b - x a| ≤ |x b' - x a'| := by
  have hxm : ∀ t (m : ℤ), x (t + m) = x t + m := by
    have hp : Function.Periodic (fun t => x t - t) 1 := fun t => by
      simp only; rw [hx]; ring
    intro t m
    have := hp.int_mul m t
    simp only [mul_one] at this
    linarith
  set S₀ : Set (ℝ × ℝ) := {p | IsUpperArc g p.1 p.2 ∧ p.1 ∈ Ico 0 1}
  have hfin : S₀.Finite := by
    refine Set.Finite.of_finite_image (f := Prod.fst)
      ((finite_crossSet_Icc hg hdiff htr 0 1).subset ?_) ?_
    · rintro _ ⟨p, hp, rfl⟩
      exact ⟨⟨_, hp.1.level.choose_spec⟩, hp.2.1, hp.2.2.le⟩
    · intro p hp q hq he
      have he' : p.1 = q.1 := he
      have hb := hp.1.right_eq (he' ▸ hq.1)
      exact Prod.ext he' hb
  obtain ⟨a₀, b₀, h₀⟩ := exists_upperArc hg hper htr hne
  have hS₀ : S₀.Nonempty := by
    refine ⟨(a₀ + ((-⌊a₀⌋ : ℤ) : ℝ), b₀ + ((-⌊a₀⌋ : ℤ) : ℝ)), h₀.shift hper _, ?_, ?_⟩
    · push_cast; linarith [Int.floor_le a₀]
    · push_cast; linarith [Int.lt_floor_add_one a₀]
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image S₀ (fun p => |x p.2 - x p.1|) hfin hS₀
  refine ⟨p.1, p.2, hp.1, fun a' b' h' => ?_⟩
  have hmem : (a' + ((-⌊a'⌋ : ℤ) : ℝ), b' + ((-⌊a'⌋ : ℤ) : ℝ)) ∈ S₀ := by
    refine ⟨h'.shift hper _, ?_, ?_⟩
    · push_cast; linarith [Int.floor_le a']
    · push_cast; linarith [Int.lt_floor_add_one a']
  have := hmin _ hmem
  simp only [hxm] at this
  rwa [show x b' + ((-⌊a'⌋ : ℤ) : ℝ) - (x a' + ((-⌊a'⌋ : ℤ) : ℝ)) = x b' - x a' by ring] at this

end Periodic

end GC.Seifert
