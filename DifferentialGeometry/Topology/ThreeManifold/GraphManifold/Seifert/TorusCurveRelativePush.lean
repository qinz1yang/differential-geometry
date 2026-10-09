import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusCurveStraightening

/-!
# Torus curves: the relative bigon push for the second circle

Chapter 6, packet K08, lane MC4 of the `TorusMappingClassLinear` programme: the hypothesis
`hrel` of `exists_isotopic_eqOn_nhds_axes_of_push` (review 12, §4.3, §4.6).

Let `φ` have matrix `1`, be the identity on an open `U ⊇ α`, and let `s` be a regular value of
`w ↦ (φ (β w)).1` attained along `β`. The lift `Φ` normalised at the origin is the identity on a
band `|y| < ε`; the arc `x (t) = (Φ (0, t)).1` stays in `0 < y < 1` for `t ∈ (0, 1)` and is
`0` at the ends. A max (or min) argument on `[0, 1]` (`exists_upperArc_Icc`) gives an arc of
`± (x - θ)` between consecutive crossings of one vertical line inside `(0, 1)`.

In the coordinates `A (x, y) = (y, ± x)` the vertical lines become horizontal and the lifted
family `t ↦ Φ (n, t)` becomes `t ↦ Ψ (t, n)` with `Ψ = A Φ A⁻¹` commuting with `ℤ²` and equal to
the identity near the vertical integer lines. Among the upper arcs inside `(0, 1)` one of minimal
extent bounds an empty bigon (`IsUpperBigon.family_mem_region`: arcs of the family inside the
bigon have their parameters in `(0, 1)` because the bigon lies in the strip `0 < y < 1`); the
bigon lies in the box `(0, 1) × [c, c + 1)`, so it is disjoint from its integer translates, and
its neighbourhood `N` is taken inside the strip (`exists_relative_bigon`). The torus push
`exists_torus_bigon_push_vertical` of MC2 then removes the two corners with support in a
compact subset of the projection of `N`, which misses `α`; so a neighbourhood of `α` stays
pointwise fixed and the crossing count drops by exactly two (`exists_isotopic_beta_push`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

theorem exists_upperArc_Icc {g : ℝ → ℝ} (hg : Continuous g)
    (htr : ∀ t, (∃ k : ℤ, g t = k) → deriv g t ≠ 0)
    {j : ℤ} (h0 : g 0 < j) (h1 : g 1 < j) {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1)
    (hj : (j : ℝ) ≤ g t₁) : ∃ a b, 0 < a ∧ b < 1 ∧ IsUpperArc g a b := by
  obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr
    (show (0 : ℝ) ≤ 1 by norm_num)) hg.continuousOn
  set M := g tm with hM
  have hMj : (j : ℝ) ≤ M := hj.trans (hmax ht₁)
  set K : ℤ := ⌊M⌋ with hKdef
  have hKle : (K : ℝ) ≤ M := Int.floor_le _
  have hKlt : M < K + 1 := Int.lt_floor_add_one _
  have hjK : j ≤ K := Int.le_floor.mpr hMj
  have hjK' : (j : ℝ) ≤ K := by exact_mod_cast hjK
  have htm0 : 0 < tm := by
    rcases eq_or_lt_of_le htm.1 with he | hlt
    · rw [hM, ← he] at hMj; linarith
    · exact hlt
  have htm1 : tm < 1 := by
    rcases eq_or_lt_of_le htm.2 with he | hlt
    · rw [hM, he] at hMj; linarith
    · exact hlt
  have hMK : (K : ℝ) < M := by
    refine lt_of_le_of_ne hKle fun he => ?_
    have hloc : IsLocalMax g tm := by
      filter_upwards [Ioo_mem_nhds htm0 htm1] with u hu
      exact hmax ⟨hu.1.le, hu.2.le⟩
    exact htr tm ⟨K, he.symm⟩ hloc.deriv_eq_zero
  set Z₁ := {t | t ∈ Icc 0 tm ∧ g t = K} with hZ₁
  have hZ₁c : IsCompact Z₁ :=
    isCompact_Icc.inter_right (isClosed_eq hg continuous_const)
  have hZ₁n : Z₁.Nonempty := by
    obtain ⟨u, hu, hu'⟩ := intermediate_value_Icc htm.1 hg.continuousOn
      ⟨by linarith, hKle⟩
    exact ⟨u, hu, hu'⟩
  set Z₂ := {t | t ∈ Icc tm 1 ∧ g t = K} with hZ₂
  have hZ₂c : IsCompact Z₂ :=
    isCompact_Icc.inter_right (isClosed_eq hg continuous_const)
  have hZ₂n : Z₂.Nonempty := by
    obtain ⟨u, hu, hu'⟩ := intermediate_value_Icc' htm.2 hg.continuousOn
      ⟨by linarith, hKle⟩
    exact ⟨u, hu, hu'⟩
  set a := sSup Z₁
  set b := sInf Z₂
  have ha : a ∈ Z₁ := hZ₁c.sSup_mem hZ₁n
  have hb : b ∈ Z₂ := hZ₂c.sInf_mem hZ₂n
  have hatm : a < tm := lt_of_le_of_ne ha.1.2 fun he => by
    have := ha.2; rw [he] at this; linarith
  have hbtm : tm < b := lt_of_le_of_ne hb.1.1 fun he => by
    have := hb.2; rw [← he] at this; linarith
  have hleft : ∀ t ∈ Ioc a tm, (K : ℝ) < g t := by
    intro t ht
    by_contra hn
    push Not at hn
    obtain ⟨u, hu, hu'⟩ := intermediate_value_Icc ht.2 hg.continuousOn ⟨hn, hKle⟩
    have : u ≤ a := le_csSup hZ₁c.bddAbove ⟨⟨by linarith [ha.1.1, ht.1, hu.1], hu.2⟩, hu'⟩
    linarith [ht.1, hu.1]
  have hright : ∀ t ∈ Ico tm b, (K : ℝ) < g t := by
    intro t ht
    by_contra hn
    push Not at hn
    obtain ⟨u, hu, hu'⟩ := intermediate_value_Icc' ht.1 hg.continuousOn ⟨hn, hKle⟩
    have : b ≤ u := csInf_le hZ₂c.bddBelow ⟨⟨hu.1, by linarith [hb.1.2, ht.2, hu.2]⟩, hu'⟩
    linarith [ht.2, hu.2]
  have ha0 : 0 < a := lt_of_le_of_ne ha.1.1 fun he => by
    have := ha.2; rw [← he] at this; linarith
  have hb1 : b < 1 := lt_of_le_of_ne hb.1.2 fun he => by
    have := hb.2; rw [he] at this; linarith
  refine ⟨a, b, ha0, hb1, ⟨hatm.trans hbtm, ⟨K, ha.2⟩, hb.2.trans ha.2.symm, fun t ht => ?_⟩⟩
  rw [ha.2]
  refine ⟨?_, lt_of_le_of_lt (hmax ⟨by linarith [ha0, ht.1], by linarith [hb1, ht.2]⟩) hKlt⟩
  rcases le_total t tm with hle | hle
  · exact hleft t ⟨ht.1, hle⟩
  · exact hright t ⟨hle, ht.2⟩

theorem fst_mem_Ioo_of_band (Ψ : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    (hdeck : ∀ (p : ℝ × ℝ) (m n : ℤ), Ψ (p.1 + m, p.2 + n) = ((Ψ p).1 + m, (Ψ p).2 + n))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hband : ∀ p : ℝ × ℝ, |p.1| < ε₀ → Ψ p = p) :
    (∀ t ∈ Ioo (0 : ℝ) 1, (Ψ (t, 0)).1 ∈ Ioo (0 : ℝ) 1) ∧
      ∀ t, (Ψ (t, 0)).1 ∈ Ioo (0 : ℝ) 1 → t ∈ Ioo (0 : ℝ) 1 := by
  have hΨc : ContDiff ℝ ∞ Ψ := contMDiff_iff_contDiff.mp Ψ.contMDiff
  have hline : ∀ (k : ℤ) (y : ℝ), Ψ ((k : ℝ), y) = ((k : ℝ), y) := by
    intro k y
    have := hdeck (0, y) k 0
    simp only [Int.cast_zero, add_zero, zero_add] at this
    rw [this, hband (0, y) (by simpa using hε₀)]
    simp
  have hshift : ∀ (t : ℝ) (m : ℤ), (Ψ (t + m, 0)).1 = (Ψ (t, 0)).1 + m := by
    intro t m
    have := hdeck (t, 0) m 0
    simp only [Int.cast_zero, add_zero] at this
    rw [this]
  have hL1 : ∀ t ∈ Ioo (0 : ℝ) 1, (Ψ (t, 0)).1 ∈ Ioo (0 : ℝ) 1 := by
    have hni : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ k : ℤ, (Ψ (t, 0)).1 ≠ k := by
      intro t ht k hk
      have he : Ψ (t, 0) = Ψ (k, (Ψ (t, 0)).2) := by
        rw [hline]
        exact Prod.ext hk rfl
      have := congrArg Prod.fst (Ψ.injective he)
      simp only at this
      have h1 : (0 : ℝ) < k := this ▸ ht.1
      have h2 : (k : ℝ) < 1 := this ▸ ht.2
      have h1' : 0 < k := by exact_mod_cast h1
      have h2' : k < 1 := by exact_mod_cast h2
      omega
    set t₀ := min (ε₀ / 2) (1 / 2)
    have ht₀ : t₀ ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_min (by linarith) (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
    have ht₀ε : |t₀| < ε₀ := by
      rw [abs_of_pos ht₀.1]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine mem_Ioo_of_forall_ne (f := fun t => (Ψ (t, 0)).1) isPreconnected_Ioo
      (hΨc.continuous.fst.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun t ht => ⟨by exact_mod_cast hni t ht 0, by exact_mod_cast hni t ht 1⟩) ht₀ ?_
    rw [hband (t₀, 0) ht₀ε]
    exact ht₀
  refine ⟨hL1, fun t ht => ?_⟩
  set m := ⌊t⌋
  set u := t - m
  have hu : u ∈ Ico (0 : ℝ) 1 := ⟨by simp only [u]; linarith [Int.floor_le t],
    by simp only [u]; linarith [Int.lt_floor_add_one t]⟩
  have htu : (Ψ (t, 0)).1 = (Ψ (u, 0)).1 + m := by
    rw [← hshift]
    simp only [u, sub_add_cancel]
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · have h00 : Ψ (0, 0) = (0, 0) := hband (0, 0) (by simpa using hε₀)
    rw [← h0, h00] at htu
    rw [htu] at ht
    simp only [zero_add] at ht
    have h1 : (0 : ℝ) < m := ht.1
    have h2 : (m : ℝ) < 1 := ht.2
    have h1' : 0 < m := by exact_mod_cast h1
    have h2' : m < 1 := by exact_mod_cast h2
    omega
  · have hu' := hL1 u ⟨h0, hu.2⟩
    rw [htu] at ht
    have h1 : (m : ℝ) < 1 := by linarith [ht.2, hu'.1]
    have h2 : (-1 : ℝ) < m := by linarith [ht.1, hu'.2]
    have h1' : m < 1 := by exact_mod_cast h1
    have h2' : -1 < m := by exact_mod_cast h2
    have hm : m = 0 := by omega
    have : t = u := by simp only [u, hm, Int.cast_zero, sub_zero]
    rw [this]
    exact ⟨h0, hu.2⟩

theorem exists_relative_bigon (Ψ : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    (hdeck : ∀ (p : ℝ × ℝ) (m n : ℤ), Ψ (p.1 + m, p.2 + n) = ((Ψ p).1 + m, (Ψ p).2 + n))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hband : ∀ p : ℝ × ℝ, |p.1| < ε₀ → Ψ p = p)
    (σ : ℝ) (γ : ℝ → ℝ × ℝ) (hγ : ∀ t, γ t = Ψ (t, 0))
    (htr : ∀ t (k : ℤ), (γ t).2 = σ + k → deriv (fun u => (γ u).2) t ≠ 0)
    (harc : ∃ a b, 0 < a ∧ b < 1 ∧ IsUpperArc (fun t => (γ t).2 - σ) a b) :
    ∃ (c a b ε : ℝ) (N : Set (ℝ × ℝ)), a < b ∧ 0 < ε ∧ (∃ k : ℤ, c = σ + k) ∧
      (γ a).2 = c ∧ (γ b).2 = c ∧ (∀ t ∈ Ioo a b, c < (γ t).2) ∧
      (∀ t ∈ Icc (a - ε) (b + ε), t < a ∨ b < t → (γ t).2 < c) ∧
      IsOpen N ∧ bigonRegion γ a b ⊆ N ∧ (∀ y ∈ N, |y.2 - c| < 1) ∧
      (∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ N → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ N →
        m = 0 ∧ n = 0) ∧
      (∀ (t : ℝ) (n : ℤ), Ψ (t, n) ∈ N → n = 0 ∧ t ∈ Ioo (a - ε) (b + ε)) ∧
      ∀ y ∈ N, y.1 ∈ Ioo (0 : ℝ) 1 := by
  have hΨc : ContDiff ℝ ∞ Ψ := contMDiff_iff_contDiff.mp Ψ.contMDiff
  have hγe : γ = fun t => Ψ (t, 0) := funext hγ
  have hγs : ContDiff ℝ ∞ γ := by
    rw [hγe]
    exact hΨc.comp (contDiff_id.prodMk contDiff_const)
  obtain ⟨hL1, hL2⟩ := fst_mem_Ioo_of_band Ψ hdeck hε₀ hband
  have hΓ (t : ℝ) (n : ℤ) : Ψ (t, n) = ((γ t).1, (γ t).2 + n) := by
    have := hdeck (t, 0) 0 n
    simp only [Int.cast_zero, add_zero, zero_add] at this
    rw [this, hγ]
  have hshift (t : ℝ) (m : ℤ) : γ (t + m) = ((γ t).1 + m, (γ t).2) := by
    have := hdeck (t, 0) m 0
    simp only [Int.cast_zero, add_zero] at this
    rw [hγ, this, hγ]
  set g : ℝ → ℝ := fun t => (γ t).2 - σ with hgdef
  set x : ℝ → ℝ := fun t => (γ t).1 with hxdef
  have hgc : Continuous g := hγs.continuous.snd.sub continuous_const
  have hgd : Differentiable ℝ g := (hγs.snd.differentiable (by simp)).sub_const σ
  have hper (t : ℝ) : g (t + 1) = g t := by
    have := hshift t 1
    simp only [Int.cast_one] at this
    simp only [hgdef, this]
  have hderiv (t : ℝ) : deriv g t = deriv (fun u => (γ u).2) t := deriv_sub_const σ
  have htr' : ∀ t ∈ crossSet g, deriv g t ≠ 0 := by
    rintro t ⟨k, hk⟩
    rw [hderiv]
    exact htr t k (by simp only [hgdef] at hk; linarith)
  set S₀ : Set (ℝ × ℝ) := {p | IsUpperArc g p.1 p.2 ∧ p.1 ∈ Ioo 0 1 ∧ p.2 < 1} with hS₀
  have hfin : S₀.Finite := by
    refine Set.Finite.of_finite_image (f := Prod.fst)
      ((finite_crossSet_Icc hgc hgd htr' 0 1).subset ?_) ?_
    · rintro _ ⟨p, hp, rfl⟩
      exact ⟨hp.1.level, hp.2.1.1.le, (hp.1.lt.trans hp.2.2).le⟩
    · intro p hp q hq he
      have he' : p.1 = q.1 := he
      have hb := hp.1.right_eq (he' ▸ hq.1)
      exact Prod.ext he' hb
  have hS₀n : S₀.Nonempty := by
    obtain ⟨a, b, ha, hb, hab⟩ := harc
    exact ⟨(a, b), hab, ⟨ha, by linarith [hab.lt]⟩, hb⟩
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image S₀ (fun p => |x p.2 - x p.1|) hfin hS₀n
  set a := p.1
  set b := p.2
  have hab : IsUpperArc g a b := hp.1
  have ha0 : 0 < a := hp.2.1.1
  have hb1 : b < 1 := hp.2.2
  obtain ⟨k, hk⟩ := hab.level
  set c := σ + (k : ℝ) with hcdef
  have hga : (γ a).2 = c := by simp only [hgdef] at hk; linarith
  have hgb : (γ b).2 = c := by
    have := hab.same
    simp only [hgdef] at this hk
    linarith
  have hHd (t : ℝ) : HasDerivAt g (deriv g t) t := (hgd t).hasDerivAt
  have hcross_a : a ∈ crossSet g := ⟨k, hk⟩
  have hcross_b : b ∈ crossSet g := ⟨k, hab.same.trans hk⟩
  have hdpos : 0 < deriv g a := by
    by_contra hle
    push Not at hle
    have hlt : deriv g a < 0 := lt_of_le_of_ne hle (htr' a hcross_a)
    have hn : HasDerivAt (fun u => -g u) (-deriv g a) a := (hHd a).neg
    obtain ⟨u, hu, hu'⟩ := ((eventually_lt_right_of_hasDerivAt_pos hn (by linarith)).and
      (Ioo_mem_nhdsGT hab.lt)).exists
    have := (hab.between u hu').1
    linarith
  have hdneg : deriv g b < 0 := by
    by_contra hle
    push Not at hle
    have hpos : 0 < deriv g b := lt_of_le_of_ne hle (Ne.symm (htr' b hcross_b))
    obtain ⟨u, hu, hu'⟩ := ((eventually_lt_left_of_hasDerivAt_pos (hHd b) hpos).and
      (Ioo_mem_nhdsLT hab.lt)).exists
    have := (hab.between u hu').1
    rw [hab.same] at hu
    linarith
  have hgl : ∀ᶠ u in 𝓝[<] a, g u < g a := eventually_lt_left_of_hasDerivAt_pos (hHd a) hdpos
  have hgr : ∀ᶠ u in 𝓝[>] b, g u < g b := by
    have hn : HasDerivAt (fun u => -g u) (-deriv g b) b := (hHd b).neg
    filter_upwards [eventually_lt_right_of_hasDerivAt_pos hn (by linarith)] with u hu
    linarith
  have hl : ∀ᶠ u in 𝓝[<] a, (γ u).2 < c := by
    filter_upwards [hgl] with u hu
    simp only [hgdef] at hu
    linarith
  have hr : ∀ᶠ u in 𝓝[>] b, (γ u).2 < c := by
    filter_upwards [hgr] with u hu
    simp only [hgdef] at hu
    linarith
  have habove : ∀ t ∈ Ioo a b, c < (γ t).2 := by
    intro t ht
    have := (hab.between t ht).1
    simp only [hgdef] at this
    linarith
  have hbelow : ∀ t ∈ Ioo a b, (γ t).2 < c + 1 := by
    intro t ht
    have := (hab.between t ht).2
    simp only [hgdef] at this
    linarith
  have hγinj : Function.Injective γ := by
    intro t u he
    rw [hγ, hγ] at he
    exact congrArg Prod.fst (Ψ.injective he)
  have hbig : IsUpperBigon γ c a b :=
    ⟨hab.lt, hγs.continuous.continuousOn, hga, hgb, habove, hγinj.injOn⟩
  have hM : ∀ t ∈ Icc a b, (γ t).2 < c + 1 := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with he | hlt
    · rw [← he, hga]; linarith
    · rcases eq_or_lt_of_le ht.2 with he' | hlt'
      · rw [he', hgb]; linarith
      · exact hbelow t ⟨hlt, hlt'⟩
  have hxab : ∀ t ∈ Icc a b, x t ∈ Ioo (0 : ℝ) 1 := by
    intro t ht
    simp only [hxdef]
    rw [hγ]
    exact hL1 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set D := bigonRegion γ a b with hDdef
  have hDx : ∀ q ∈ D, q.1 ∈ Ioo (0 : ℝ) 1 := by
    have hcurve : ∀ q ∈ bigonCurveSet γ a b, q.1 ∈ Ioo (0 : ℝ) 1 := by
      rintro q (⟨t, ht, rfl⟩ | hq)
      · exact hxab t ht
      · rw [hbig.segment_eq] at hq
        have h1 := segment_subset_uIcc (γ a).1 (γ b).1 hq.1
        have ha' := hxab a ⟨le_rfl, hab.lt.le⟩
        have hb' := hxab b ⟨hab.lt.le, le_rfl⟩
        rw [mem_uIcc] at h1
        constructor
        · rcases h1 with h1 | h1
          · linarith [h1.1, ha'.1]
          · linarith [h1.1, hb'.1]
        · rcases h1 with h1 | h1
          · linarith [h1.2, hb'.2]
          · linarith [h1.2, ha'.2]
    intro q hq
    constructor
    · by_contra hn
      push Not at hn
      refine not_mem_bigonRegion_of_connected hbig.jordan (Z := {q : ℝ × ℝ | q.1 ≤ 0})
        ((convex_halfSpace_le (f := Prod.fst) ⟨fun _ _ => rfl, fun _ _ => rfl⟩ 0).isPreconnected)
        ?_ ?_ hn hq
      · rw [Set.disjoint_left]
        intro z hz hzJ
        exact absurd (hcurve z hzJ).1 (not_lt.mpr hz)
      · intro R
        refine ⟨(-|R| - 1, 0), show -|R| - 1 ≤ (0 : ℝ) by linarith [abs_nonneg R], ?_⟩
        have h1 : |(-|R| - 1 : ℝ)| ≤ ‖((-|R| - 1 : ℝ), (0 : ℝ))‖ := by
          rw [← Real.norm_eq_abs]; exact norm_fst_le ((-|R| - 1 : ℝ), (0 : ℝ))
        rw [abs_of_neg (by linarith [abs_nonneg R])] at h1
        linarith [le_abs_self R]
    · by_contra hn
      push Not at hn
      refine not_mem_bigonRegion_of_connected hbig.jordan (Z := {q : ℝ × ℝ | 1 ≤ q.1})
        ((convex_halfSpace_ge (f := Prod.fst) ⟨fun _ _ => rfl, fun _ _ => rfl⟩ 1).isPreconnected)
        ?_ ?_ hn hq
      · rw [Set.disjoint_left]
        intro z hz hzJ
        exact absurd (hcurve z hzJ).2 (not_lt.mpr hz)
      · intro R
        refine ⟨(|R| + 2, 0), show (1 : ℝ) ≤ |R| + 2 by linarith [abs_nonneg R], ?_⟩
        have h1 : |(|R| + 2 : ℝ)| ≤ ‖((|R| + 2 : ℝ), (0 : ℝ))‖ := by
          rw [← Real.norm_eq_abs]; exact norm_fst_le ((|R| + 2 : ℝ), (0 : ℝ))
        rw [abs_of_pos (by linarith [abs_nonneg R])] at h1
        linarith [le_abs_self R]
  set Γ : ℤ → ℝ → ℝ × ℝ := fun n t => Ψ (t, n) with hΓdef
  have hΓ0 : Γ 0 = γ := funext fun t => by simp only [hΓdef, Int.cast_zero, hγ]
  have hfam : ∀ (n : ℤ) t, Ψ (t, n) ∈ D → n = 0 ∧ t ∈ Icc a b := by
    intro n t ht
    refine IsUpperBigon.family_mem_region' (Γ := Γ) hΓ0 hbig hM hl hr
      (fun i => hΨc.continuous.comp (continuous_id.prodMk continuous_const))
      (fun i j t u he => ?_) (fun i t R => ?_) (fun i t ht δ hδ => ?_)
      (fun i a' b' hab' ha' hb' hbetw hsub => ?_) ht
    · have he' := Ψ.injective he
      simp only [Prod.mk.injEq] at he'
      exact ⟨Int.cast_injective he'.2, he'.1⟩
    · set X := (Ψ (t, i)).1
      set m : ℤ := ⌈|R| + |X|⌉ + 1
      have hm : |R| + |X| < m := by
        have := Int.le_ceil (|R| + |X|)
        simp only [m, Int.cast_add, Int.cast_one]
        linarith
      have hf (j : ℤ) : Ψ (t + j, i) = (X + j, (Ψ (t, i)).2) := by
        have := hdeck (t, i) j 0
        simp only [Int.cast_zero, add_zero] at this
        exact this
      have hnorm (y : ℝ × ℝ) : |y.1| ≤ ‖y‖ := by
        rw [← Real.norm_eq_abs]; exact norm_fst_le y
      refine ⟨⟨t + m, by linarith [abs_nonneg R, abs_nonneg X], ?_⟩,
        ⟨t + ((-m : ℤ) : ℝ), by push_cast; linarith [abs_nonneg R, abs_nonneg X], ?_⟩⟩
      · change R < ‖Ψ (t + m, i)‖
        rw [hf]
        have h1 := hnorm (X + m, (Ψ (t, i)).2)
        have h2 : |X + (m : ℝ)| ≥ X + m := le_abs_self _
        linarith [le_abs_self R, neg_abs_le X]
      · change R < ‖Ψ (t + ((-m : ℤ) : ℝ), i)‖
        rw [hf]
        push_cast
        have h1 := hnorm (X + -(m : ℝ), (Ψ (t, i)).2)
        have h2 : |X + -(m : ℝ)| ≥ -(X + -(m : ℝ)) := neg_le_abs _
        linarith [le_abs_self R, le_abs_self X]
    · change (Ψ (t, i)).2 = c at ht
      rw [hΓ] at ht
      have hk' : (γ t).2 = σ + ((k - i : ℤ) : ℝ) := by push_cast; simp only at ht; linarith
      have hd := htr t (k - i) hk'
      obtain ⟨u, hu, hu'⟩ := exists_lt_of_hasDerivAt_ne
        ((hγs.snd.differentiable (by simp) t).hasDerivAt) hd hδ
      refine ⟨u, hu, ?_⟩
      change c < (Ψ (u, i)).2
      rw [hΓ]
      simp only at ht hu' ⊢
      linarith
    · change (Ψ (a', i)).2 = c at ha'
      change (Ψ (b', i)).2 = c at hb'
      have ha'D : Ψ (a', i) ∈ D := hsub ⟨a', ⟨le_rfl, hab'.le⟩, rfl⟩
      have hb'D : Ψ (b', i) ∈ D := hsub ⟨b', ⟨hab'.le, le_rfl⟩, rfl⟩
      have ha'x := hDx _ ha'D
      have hb'x := hDx _ hb'D
      rw [hΓ] at ha' hb' ha'x hb'x
      simp only at ha' hb' ha'x hb'x
      have ha'I := hL2 a' (by rw [← hγ]; exact ha'x)
      have hb'I := hL2 b' (by rw [← hγ]; exact hb'x)
      have hup : IsUpperArc g a' b' := by
        refine ⟨hab', ⟨k - i, by simp only [hgdef]; push_cast; linarith⟩,
          by simp only [hgdef]; linarith, fun u hu => ?_⟩
        have := hbetw u hu
        change c < (Ψ (u, i)).2 ∧ (Ψ (u, i)).2 < c + 1 at this
        rw [hΓ] at this
        simp only at this
        simp only [hgdef]
        constructor <;> linarith [this.1, this.2]
      have := hmin (a', b') ⟨hup, ha'I, hb'I.2⟩
      change |(γ b).1 - (γ a).1| ≤ |(Ψ (b', i)).1 - (Ψ (a', i)).1|
      rw [hΓ, hΓ]
      exact this
  obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.lt.le)
    hγs.continuous.snd.continuousOn
  set M := (γ tm).2
  have hMle : ∀ s ∈ Icc a b, (γ s).2 ≤ M := fun s hs => hmax hs
  have hMc : M < c + 1 := hM tm htm
  have hDy : ∀ q ∈ D, c ≤ q.2 ∧ q.2 < c + 1 := fun q hq =>
    ⟨hbig.region_snd_ge q hq, (hbig.region_snd_le hMle q hq).trans_lt hMc⟩
  have hsepD : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ D → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ D →
      m = 0 ∧ n = 0 := by
    intro m n z hz hz'
    have h1 := hDy z hz
    have h2 := hDy _ hz'
    have h3 := hDx z hz
    have h4 := hDx _ hz'
    simp only at h2 h4
    exact ⟨bigonInt_eq_zero_of_abs_lt_one (by rw [abs_lt]; constructor <;> linarith [h3.1, h3.2,
      h4.1, h4.2]), bigonInt_eq_zero_of_abs_lt_one (by rw [abs_lt]; constructor <;> linarith)⟩
  have hinjD : InjOn torusCover D := by
    intro z hz z' hz' he
    obtain ⟨m, n, hmn⟩ := torusCover_eq_torusCover_iff.mp he
    obtain ⟨rfl, rfl⟩ := hsepD m n z' hz' (hmn ▸ hz)
    simpa using hmn
  obtain ⟨T, hTo, hDT, hTinj⟩ := hinjD.exists_isOpen_superset hbig.isCompact_region
    (fun _ _ => continuous_torusCover.continuousAt)
    (fun z _ => ⟨ball z (1 / 2), ball_mem_nhds z (by norm_num), injOn_torusCover_ball z⟩)
  obtain ⟨δ₁, hδ₁, hδ₁P⟩ := exists_Ioo_of_eventually_nhdsLT hl
  obtain ⟨δ₂, hδ₂, hδ₂P⟩ := exists_Ioo_of_eventually_nhdsGT hr
  set ε := min δ₁ δ₂ / 2
  have hε : 0 < ε := half_pos (lt_min hδ₁ hδ₂)
  set F : Set (ℝ × ℝ) := {p | ∃ n : ℤ, p.2 = n} ∩
    (Ioo (a - ε) (b + ε) ×ˢ Ioo (-1 / 2 : ℝ) (1 / 2))ᶜ
  have hFc : IsClosed F := by
    refine IsClosed.inter ?_ (isOpen_Ioo.prod isOpen_Ioo).isClosed_compl
    have : {p : ℝ × ℝ | ∃ n : ℤ, p.2 = n} = Prod.snd ⁻¹' range ((↑) : ℤ → ℝ) := by
      ext p
      simp only [mem_ofPred_eq, mem_preimage, mem_range]
      exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩
    rw [this]
    exact Real.isClosed_range_intCast.preimage continuous_snd
  set P := Ψ '' F
  have hPc : IsClosed P := Ψ.toHomeomorph.isClosedMap F hFc
  have hDP : ∀ y ∈ D, y ∉ P := by
    rintro y hy ⟨p, ⟨⟨n, hn⟩, hpF⟩, rfl⟩
    have hp : p = (p.1, (n : ℝ)) := Prod.ext rfl hn
    rw [hp] at hy
    obtain ⟨rfl, ht⟩ := hfam n p.1 hy
    apply hpF
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [hn, Int.cast_zero]
    norm_num
  set N := T ∩ {y : ℝ × ℝ | |y.2 - c| < 1} ∩ Pᶜ ∩ {y : ℝ × ℝ | y.1 ∈ Ioo (0 : ℝ) 1}
  have hNo : IsOpen N :=
    ((hTo.inter (isOpen_lt (continuous_abs.comp (continuous_snd.sub continuous_const))
      continuous_const)).inter hPc.isOpen_compl).inter (isOpen_Ioo.preimage continuous_fst)
  refine ⟨c, a, b, ε, N, hab.lt, hε, ⟨k, rfl⟩, hga, hgb, habove, ?_, hNo, ?_, ?_, ?_, ?_,
    fun y hy => hy.2⟩
  · intro t ht hside
    have h1 : ε < δ₁ := by have := min_le_left δ₁ δ₂; simp only [ε]; linarith
    have h2 : ε < δ₂ := by have := min_le_right δ₁ δ₂; simp only [ε]; linarith
    rcases hside with h | h
    · exact hδ₁P t ⟨by linarith [ht.1], h⟩
    · exact hδ₂P t ⟨h, by linarith [ht.2]⟩
  · intro y hy
    obtain ⟨h1, h2⟩ := hDy y hy
    exact ⟨⟨⟨hDT hy, show |y.2 - c| < 1 by rw [abs_lt]; constructor <;> linarith⟩, hDP y hy⟩,
      hDx y hy⟩
  · exact fun y hy => hy.1.1.2
  · intro m n z hz hz'
    have he := hTinj hz.1.1.1 hz'.1.1.1 (by rw [torusCover_add_int])
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only at h1 h2
    exact ⟨by exact_mod_cast (show (m : ℝ) = 0 by linarith),
      by exact_mod_cast (show (n : ℝ) = 0 by linarith)⟩
  · intro t n ht
    by_contra hcon
    apply ht.1.2
    refine ⟨(t, n), ⟨⟨n, rfl⟩, fun hm => hcon ?_⟩, rfl⟩
    have hn : n = 0 := by
      refine bigonInt_eq_zero_of_abs_lt_one ?_
      rw [abs_lt]
      constructor <;> linarith [hm.2.1, hm.2.2]
    exact ⟨hn, hm.1⟩

def sgnSwap (ζ : ℤ) (hζ : ζ * ζ = 1) : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) where
  toFun p := (p.2, (ζ : ℝ) * p.1)
  invFun q := ((ζ : ℝ) * q.2, q.1)
  left_inv p := by
    have h : (ζ : ℝ) * ζ = 1 := by exact_mod_cast hζ
    exact Prod.ext (by simp only [← mul_assoc, h, one_mul]) rfl
  right_inv q := by
    have h : (ζ : ℝ) * ζ = 1 := by exact_mod_cast hζ
    exact Prod.ext rfl (by simp only [← mul_assoc, h, one_mul])
  contMDiff_toFun := (contDiff_snd.prodMk (contDiff_const.mul contDiff_fst)).contMDiff
  contMDiff_invFun := ((contDiff_const.mul contDiff_snd).prodMk contDiff_fst).contMDiff

section SgnSwap

variable {ζ : ℤ} {hζ : ζ * ζ = 1}

theorem sgnSwap_apply (p : ℝ × ℝ) : sgnSwap ζ hζ p = (p.2, (ζ : ℝ) * p.1) := rfl

theorem sgnSwap_symm_apply (q : ℝ × ℝ) : (sgnSwap ζ hζ).symm q = ((ζ : ℝ) * q.2, q.1) := rfl

theorem sgnSwap_image_segment (u v : ℝ × ℝ) :
    sgnSwap ζ hζ '' segment ℝ u v = segment ℝ (sgnSwap ζ hζ u) (sgnSwap ζ hζ v) := by
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap, image_image]
  refine image_congr fun r _ => ?_
  simp only [sgnSwap_apply, AffineMap.lineMap_apply_module]
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    ring

theorem sgnSwap_bigonRegion (γ : ℝ → ℝ × ℝ) (a b : ℝ) :
    sgnSwap ζ hζ '' bigonRegion γ a b = bigonRegion (fun t => sgnSwap ζ hζ (γ t)) a b := by
  refine bigonRegion_image (sgnSwap ζ hζ).toHomeomorph ?_
  unfold bigonCurveSet
  rw [image_union]
  congr 1
  · rw [image_image]
    rfl
  · exact sgnSwap_image_segment _ _

end SgnSwap

theorem exists_isotopic_beta_push_of_sign (φ : TDiff)
    {Φ : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)} (hlift : ∀ p, φ (torusCover p) = torusCover (Φ p))
    (hper : ∀ (p : ℝ × ℝ) (m n : ℤ), Φ (p.1 + m, p.2 + n) = ((Φ p).1 + m, (Φ p).2 + n))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hband : ∀ p : ℝ × ℝ, |p.2| < ε₀ → Φ p = p)
    {s : Circle} {θ : ℝ} (hθs : cexp θ = s)
    (htr : ∀ t, (∃ k : ℤ, (Φ (0, t)).1 = θ + k) → deriv (fun u => (Φ (0, u)).1) t ≠ 0)
    (hfin : {w | (φ (betaCircle w)).1 = s}.Finite)
    {ζ : ℤ} (hζ : ζ * ζ = 1)
    (harc : ∃ a b, 0 < a ∧ b < 1 ∧ IsUpperArc (fun t => (ζ : ℝ) * ((Φ (0, t)).1 - θ)) a b) :
    ∃ Q : TDiff, IsotopicDiffeomorph torusRefl Q ∧
      (∃ C : Set Torus, IsCompact C ∧ (∀ p ∉ C, Q p = p) ∧
        (∀ x : ℝ, torusCover (x, 0) ∉ C) ∧
        ∀ w, (Q (φ (betaCircle w))).1 = s → φ (betaCircle w) ∉ C) ∧
      (∀ w, (Q (φ (betaCircle w))).1 = s → (φ (betaCircle w)).1 = s) ∧
      {w | (Q (φ (betaCircle w))).1 = s}.ncard + 2 = {w | (φ (betaCircle w)).1 = s}.ncard := by
  have hζr : (ζ : ℝ) * ζ = 1 := by exact_mod_cast hζ
  have hζ2 : (ζ : ℝ) ^ 2 = 1 := by rw [sq]; exact hζr
  set A := sgnSwap ζ hζ with hA
  set Ψ : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) := A.symm.trans (Φ.trans A) with hΨ
  have hΨapp (q : ℝ × ℝ) : Ψ q = A (Φ (A.symm q)) := rfl
  have hΦc : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.mp Φ.contMDiff
  have hΨdeck : ∀ (p : ℝ × ℝ) (m n : ℤ),
      Ψ (p.1 + m, p.2 + n) = ((Ψ p).1 + m, (Ψ p).2 + n) := by
    intro p m n
    rw [hΨapp, hΨapp, sgnSwap_symm_apply, sgnSwap_symm_apply]
    have h1 := hper ((ζ : ℝ) * p.2, p.1) (ζ * n) m
    simp only at h1
    have he : ((ζ : ℝ) * (p.2 + n), p.1 + m) =
        ((ζ : ℝ) * p.2 + ((ζ * n : ℤ) : ℝ), p.1 + m) := by
      push_cast; ring_nf
    rw [he, h1, sgnSwap_apply, sgnSwap_apply]
    refine Prod.ext rfl ?_
    simp only
    push_cast
    rw [mul_add, ← mul_assoc, hζr, one_mul]
  have hΨband : ∀ p : ℝ × ℝ, |p.1| < ε₀ → Ψ p = p := by
    intro p hp
    rw [hΨapp, hband (A.symm p) (by rw [sgnSwap_symm_apply]; exact hp), A.apply_symm_apply]
  set γo : ℝ → ℝ × ℝ := fun t => Φ (0, t) with hγodef
  set γA : ℝ → ℝ × ℝ := fun t => Ψ (t, 0) with hγAdef
  have hγA (t : ℝ) : γA t = A (γo t) := by
    change A (Φ (A.symm (t, 0))) = A (Φ (0, t))
    have : A.symm (t, 0) = (0, t) := Prod.ext (mul_zero _) rfl
    rw [this]
  have hγA2 (t : ℝ) : (γA t).2 = (ζ : ℝ) * (γo t).1 := by rw [hγA, sgnSwap_apply]
  have hγo : ContDiff ℝ ∞ γo := hΦc.comp (contDiff_const.prodMk contDiff_id)
  have hxo : ContDiff ℝ ∞ (fun t => (γo t).1) := hγo.fst
  have hdγo (t : ℝ) : HasDerivAt γo (fderiv ℝ Φ (0, t) (0, 1)) t :=
    hasDerivAt_diffeomorph_vertical Φ 0 t
  have hdγo1 (t : ℝ) : (deriv γo t).1 = deriv (fun u => (γo u).1) t := by
    rw [(hdγo t).deriv]
    exact ((hasDerivAt_fst_comp (hdγo t)).deriv).symm
  have hcrossA : ∀ t (k : ℤ), (γA t).2 = (ζ : ℝ) * θ + k → ∃ j : ℤ, (γo t).1 = θ + j := by
    intro t k hk
    refine ⟨ζ * k, ?_⟩
    rw [hγA2] at hk
    have := congrArg (fun r => (ζ : ℝ) * r) hk
    simp only [← mul_assoc, hζr, one_mul, mul_add] at this
    push_cast
    linarith
  have htrA : ∀ t (k : ℤ), (γA t).2 = (ζ : ℝ) * θ + k →
      deriv (fun u => (γA u).2) t ≠ 0 := by
    intro t k hk
    have he : (fun u => (γA u).2) = fun u => (ζ : ℝ) * (γo u).1 := funext hγA2
    rw [he, deriv_const_mul _ ((hxo.differentiable (by simp)) t)]
    exact mul_ne_zero (by intro h0; rw [h0, zero_mul] at hζr; exact zero_ne_one hζr)
      (htr t (hcrossA t k hk))
  have harcA : ∃ a b, 0 < a ∧ b < 1 ∧ IsUpperArc (fun t => (γA t).2 - (ζ : ℝ) * θ) a b := by
    obtain ⟨a, b, ha, hb, hab⟩ := harc
    refine ⟨a, b, ha, hb, ?_⟩
    have he : (fun t => (γA t).2 - (ζ : ℝ) * θ) = fun t => (ζ : ℝ) * ((Φ (0, t)).1 - θ) := by
      funext t
      rw [hγA2]
      ring
    rw [he]
    exact hab
  obtain ⟨c, a, b, ε, N, hab, hε, ⟨k, hck⟩, ha, hb, hin, hout, hNo, hDN, hNc, hsep, hempN,
    hNx⟩ := exists_relative_bigon Ψ hΨdeck hε₀ hΨband ((ζ : ℝ) * θ) γA (fun _ => rfl) htrA harcA
  set co : ℝ := (ζ : ℝ) * c with hco
  have hcoθ : co = θ + ((ζ * k : ℤ) : ℝ) := by
    rw [hco, hck, mul_add, ← mul_assoc, hζr, one_mul]
    push_cast
    ring
  have hcos : cexp co = s := by rw [hcoθ, cexp_add_int, hθs]
  have hxa : (γo a).1 = co := by
    have := congrArg (fun r => (ζ : ℝ) * r) ((hγA2 a).symm.trans ha)
    simp only [← mul_assoc, hζr, one_mul] at this
    exact this
  have hxb : (γo b).1 = co := by
    have := congrArg (fun r => (ζ : ℝ) * r) ((hγA2 b).symm.trans hb)
    simp only [← mul_assoc, hζr, one_mul] at this
    exact this
  have hsgn (t : ℝ) : (ζ : ℝ) * ((γo t).1 - co) = (γA t).2 - c := by
    rw [hγA2, hco, mul_sub, ← mul_assoc, hζr, one_mul]
  have hinjo : Function.Injective γo := fun t u he => by
    have := congrArg Prod.snd (Φ.injective he)
    exact this
  have himm (t : ℝ) : deriv γo t ≠ 0 := by
    rw [(hdγo t).deriv]
    intro h0
    have := fderiv_injective_of_diffeomorph Φ (0, t) (h0.trans (map_zero _).symm)
    simp at this
  set No : Set (ℝ × ℝ) := A ⁻¹' N with hNodef
  have hNoo : IsOpen No := hNo.preimage A.continuous
  have hDNo : bigonRegion γo a b ⊆ No := by
    intro z hz
    change A z ∈ N
    apply hDN
    have : A z ∈ A '' bigonRegion γo a b := mem_image_of_mem A hz
    rw [sgnSwap_bigonRegion] at this
    have hfun : (fun t => A (γo t)) = γA := funext fun t => (hγA t).symm
    rw [hfun] at this
    exact this
  have hNoc : ∀ y ∈ No, |y.1 - co| < 1 := by
    intro y hy
    have h1 := hNc _ hy
    rw [sgnSwap_apply] at h1
    have he : (ζ : ℝ) * y.1 - c = (ζ : ℝ) * (y.1 - co) := by
      rw [hco, mul_sub, ← mul_assoc, hζr, one_mul]
    rw [he, abs_mul] at h1
    have hz1 : |(ζ : ℝ)| = 1 := by
      have := abs_mul_abs_self (ζ : ℝ)
      rw [hζr] at this
      rcases mul_self_eq_one_iff.mp this with h | h
      · exact h
      · linarith [abs_nonneg (ζ : ℝ)]
    rwa [hz1, one_mul] at h1
  have hNosep : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ No → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ No →
      m = 0 ∧ n = 0 := by
    intro m n z hz hz'
    have hz'' : ((A z).1 + (n : ℝ), (A z).2 + ((ζ * m : ℤ) : ℝ)) ∈ N := by
      have : A (z.1 + (m : ℝ), z.2 + (n : ℝ)) =
          ((A z).1 + (n : ℝ), (A z).2 + ((ζ * m : ℤ) : ℝ)) := by
        rw [sgnSwap_apply, sgnSwap_apply]
        push_cast
        ring_nf
      rw [← this]
      exact hz'
    obtain ⟨h1, h2⟩ := hsep n (ζ * m) (A z) hz hz''
    refine ⟨?_, h1⟩
    have := congrArg (fun r => ζ * r) h2
    simp only [← mul_assoc, hζ, one_mul, mul_zero] at this
    exact this
  set f : Circle → Torus := fun w => φ (betaCircle w) with hfdef
  have hfγ (t : ℝ) : f (cexp t) = torusCover (γo t) := by
    simp only [f, betaCircle_cexp', hlift, γo]
  have hemp : ∀ z (y : ℝ × ℝ), y ∈ No → f z = torusCover y →
      ∃ t ∈ Ioo (a - ε) (b + ε), cexp t = z ∧ γo t = y := by
    intro z y hy hzy
    obtain ⟨t, rfl⟩ := cexp_surjective z
    have he : torusCover y = torusCover (γo t) := by rw [← hzy, hfγ]
    obtain ⟨m, n, hmn⟩ := torusCover_eq_torusCover_iff.mp he
    have hyΦ : y = Φ (m, t + n) := by
      rw [hmn]
      have := hper (0, t) m n
      simp only [zero_add] at this
      rw [this]
    have hAy : A y = Ψ (t + n, ((ζ * m : ℤ) : ℝ)) := by
      rw [hyΦ, hΨapp, sgnSwap_symm_apply]
      congr 2
      refine Prod.ext ?_ rfl
      simp only
      push_cast
      rw [← mul_assoc, hζr, one_mul]
    have hmem : Ψ (t + n, ((ζ * m : ℤ) : ℝ)) ∈ N := hAy ▸ hy
    obtain ⟨h1, ht⟩ := hempN (t + n) (ζ * m) hmem
    have hm : m = 0 := by
      have := congrArg (fun r => ζ * r) h1
      simp only [← mul_assoc, hζ, one_mul, mul_zero] at this
      exact this
    refine ⟨t + n, ht, cexp_add_int t n, ?_⟩
    rw [hyΦ, hm, Int.cast_zero]
  obtain ⟨Q, hQ, ⟨C, hCc, hCN, hQC, -, hCcross⟩, hiff, h12, h1, h2⟩ :=
    exists_torus_bigon_push_vertical (f := f) hγo hfγ (σ := (ζ : ℝ)) hζ2 hab hε hxa hxb
      (fun t ht => by rw [hsgn]; linarith [hin t ht])
      (fun t ht hs' => by rw [hsgn]; linarith [hout t ht hs'])
      (by rw [hdγo1]; exact htr a ⟨ζ * k, hxa.trans hcoθ⟩)
      (by rw [hdγo1]; exact htr b ⟨ζ * k, hxb.trans hcoθ⟩)
      (fun t _ => himm t) hinjo.injOn hNoo hDNo hNoc hNosep hemp
  rw [hcos] at hiff h1 h2 hCcross
  have hNo2 : ∀ q ∈ No, ∀ j : ℤ, q.2 ≠ j := by
    intro q hq j hj
    have h := hNx _ hq
    rw [sgnSwap_apply] at h
    simp only at h
    rw [hj] at h
    have h3 : (0 : ℝ) < j := h.1
    have h4 : (j : ℝ) < 1 := h.2
    have h3' : 0 < j := by exact_mod_cast h3
    have h4' : j < 1 := by exact_mod_cast h4
    omega
  refine ⟨Q, hQ, ⟨C, hCc, hQC, fun x hx => ?_, hCcross⟩, fun w => ?_,
    ncard_add_two_of_forall_iff hfin h12 h1 h2 hiff⟩
  · exact torusCover_not_mem_image_of_int hNo2 (k := 0) (by simp) (hCN hx)
  · exact fun hw => ((hiff w).mp hw).1

theorem exists_isotopic_beta_push_add_two (φ : TDiff) (h : torusMatrix φ = 1) {U : Set Torus}
    (hU : IsOpen U) (hαU : range alphaCircle ⊆ U) (hφU : ∀ p ∈ U, φ p = p) {s : Circle}
    (hs : ∀ w, (φ (betaCircle w)).1 = s →
      mfderiv (𝓡 1) (𝓡 1) (fun w => (φ (betaCircle w)).1) w ≠ 0)
    (hne : ∃ w, (φ (betaCircle w)).1 = s) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧
      (∃ U' : Set Torus, IsOpen U' ∧ range alphaCircle ⊆ U' ∧ ∀ p ∈ U', ψ p = p) ∧
      (∀ w, (ψ (betaCircle w)).1 = s →
        mfderiv (𝓡 1) (𝓡 1) (fun w => (ψ (betaCircle w)).1) w ≠ 0) ∧
      {w | (ψ (betaCircle w)).1 = s}.ncard + 2 = {w | (φ (betaCircle w)).1 = s}.ncard := by
  obtain ⟨ε, hε, hεU, Φ, hlift, hdeck, hband⟩ := exists_torusLiftDiffeomorph_band φ hU hαU hφU
  have hper := lift_add_int_of_eq_one h hdeck
  have hΦc : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.mp Φ.contMDiff
  set xo : ℝ → ℝ := fun t => (Φ (0, t)).1 with hxodef
  have hxo : ContDiff ℝ ∞ xo := hΦc.fst.comp (contDiff_const.prodMk contDiff_id)
  have hfx (t : ℝ) : (φ (betaCircle (cexp t))).1 = cexp (xo t) := by
    rw [betaCircle_cexp', hlift, torusCover_eq]
  have hxo0 : xo 0 = 0 := by
    change (Φ (0, 0)).1 = 0
    rw [hband (0, 0) (by simpa using hε)]
  have hxo1 : xo 1 = 0 := by
    change (Φ (0, 1)).1 = 0
    have h1 := hper (0, 0) 0 1
    simp only [Int.cast_zero, add_zero, Int.cast_one, zero_add] at h1
    rw [h1, hband (0, 0) (by simpa using hε)]
  have hs1 : s ≠ 1 := by
    intro hs1
    have hd := deriv_lift_ne_zero (contMDiff_betaHeight φ) hxo hfx (t := 0)
      (hs _ (by rw [hfx, hxo0, cexp_zero, hs1]))
    apply hd
    have he : xo =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhds (neg_neg_iff_pos.mpr hε) hε] with t ht
      change (Φ (0, t)).1 = 0
      rw [hband (0, t) (abs_lt.mpr ht)]
    rw [he.deriv_eq, deriv_const]
  set θ : ℝ := Int.fract (rep s) with hθdef
  have hθs : cexp θ = s := cexp_fract_rep s
  have hθ : θ ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne (Int.fract_nonneg _) (fun h0 => hs1 (by rw [← hθs, ← h0, cexp_zero])),
      Int.fract_lt_one _⟩
  have htr : ∀ t, (∃ k : ℤ, (Φ (0, t)).1 = θ + k) → deriv (fun u => (Φ (0, u)).1) t ≠ 0 := by
    rintro t ⟨k, hk⟩
    exact deriv_lift_ne_zero (contMDiff_betaHeight φ) hxo hfx
      (hs _ (by rw [hfx]; change cexp (Φ (0, t)).1 = s; rw [hk, cexp_add_int, hθs]))
  obtain ⟨w₁, hw₁⟩ := hne
  set t₁ : ℝ := Int.fract (rep w₁) with ht₁def
  have ht₁ : t₁ ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, xo t₁ = θ + k := by
    have he : cexp (xo t₁) = cexp θ := by rw [← hfx, cexp_fract_rep, hw₁, hθs]
    obtain ⟨n, hn⟩ := cexp_eq_cexp_iff.mp he
    exact ⟨n, hn⟩
  have hfin := circle_finite_fiber_of_regular (contMDiff_betaHeight φ) hs
  have key : ∀ ζ : ℤ, ζ * ζ = 1 → ∀ j : ℤ, (ζ : ℝ) * (xo 0 - θ) < j →
      (j : ℝ) ≤ (ζ : ℝ) * (xo t₁ - θ) →
      ∃ a b, 0 < a ∧ b < 1 ∧ IsUpperArc (fun t => (ζ : ℝ) * ((Φ (0, t)).1 - θ)) a b := by
    intro ζ hζ j hj0 hj1
    have hζr : (ζ : ℝ) * ζ = 1 := by exact_mod_cast hζ
    refine exists_upperArc_Icc (g := fun t => (ζ : ℝ) * ((Φ (0, t)).1 - θ))
      ((hxo.continuous.sub continuous_const).const_mul _) ?_ (j := j) hj0 ?_ ht₁ hj1
    · rintro t ⟨k', hk'⟩
      have hcr : ∃ k : ℤ, (Φ (0, t)).1 = θ + k := by
        refine ⟨ζ * k', ?_⟩
        have := congrArg (fun r => (ζ : ℝ) * r) hk'
        simp only [← mul_assoc, hζr, one_mul] at this
        push_cast
        linarith
      have hd : deriv (fun t => (ζ : ℝ) * ((Φ (0, t)).1 - θ)) t =
          (ζ : ℝ) * deriv (fun u => (Φ (0, u)).1) t := by
        rw [deriv_const_mul _ (((hxo.differentiable (by simp)) t).sub_const θ), deriv_sub_const]
      rw [hd]
      exact mul_ne_zero (fun h0 => by rw [h0, zero_mul] at hζr; exact zero_ne_one hζr)
        (htr t hcr)
    · change (ζ : ℝ) * (xo 1 - θ) < j
      rw [hxo1, ← hxo0]
      exact hj0
  have harc : ∃ ζ : ℤ, ζ * ζ = 1 ∧
      ∃ a b, 0 < a ∧ b < 1 ∧ IsUpperArc (fun t => (ζ : ℝ) * ((Φ (0, t)).1 - θ)) a b := by
    rcases le_or_gt 0 k with hk0 | hk0
    · refine ⟨1, rfl, key 1 rfl 0 ?_ ?_⟩
      · rw [hxo0]; push_cast; linarith [hθ.1]
      · rw [hk]; push_cast
        have : (0 : ℝ) ≤ k := by exact_mod_cast hk0
        linarith
    · refine ⟨-1, rfl, key (-1) rfl 1 ?_ ?_⟩
      · rw [hxo0]; push_cast; linarith [hθ.2]
      · rw [hk]; push_cast
        have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        linarith
  obtain ⟨ζ, hζ, hab⟩ := harc
  obtain ⟨Q, hQ, ⟨C, hCc, hQC, hCα, hCcross⟩, himp, hcard⟩ :=
    exists_isotopic_beta_push_of_sign φ hlift hper hε hband hθs htr hfin hζ hab
  have hfc : Continuous (fun w : Circle => φ (betaCircle w)) :=
    φ.continuous.comp (continuous_const.prodMk continuous_id)
  refine ⟨φ.trans Q, isotopicDiffeomorph_trans_of_refl φ hQ,
    ⟨U ∩ Cᶜ, hU.inter hCc.isClosed.isOpen_compl, ?_, ?_⟩, fun w hw => ?_, hcard⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨hαU ⟨z, rfl⟩, ?_⟩
    have hz : alphaCircle z = torusCover (rep z, 0) := by
      rw [← alphaCircle_cexp', cexp_rep]
    rw [hz]
    exact hCα _
  · rintro p ⟨hpU, hpC⟩
    change Q (φ p) = p
    rw [hφU p hpU, hQC p hpC]
  · have hwC := hCcross w hw
    have hev : (fun w => ((φ.trans Q) (betaCircle w)).1) =ᶠ[𝓝 w]
        fun w => (φ (betaCircle w)).1 :=
      (eventuallyEq_of_not_mem_support hCc hQC hfc hwC).fun_comp Prod.fst
    rw [hev.mfderiv_eq]
    exact hs w (himp w hw)

theorem exists_isotopic_beta_push (φ : TDiff) (h : torusMatrix φ = 1) (U : Set Torus)
    (hU : IsOpen U) (hαU : range alphaCircle ⊆ U) (hφU : ∀ p ∈ U, φ p = p) (s : Circle)
    (hs : ∀ w, (φ (betaCircle w)).1 = s →
      mfderiv (𝓡 1) (𝓡 1) (fun w => (φ (betaCircle w)).1) w ≠ 0)
    (hss : HasSameSideArcIn (fun w => (φ (betaCircle w)).1) s (Icc 0 1)) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧
      (∃ U' : Set Torus, IsOpen U' ∧ range alphaCircle ⊆ U' ∧ ∀ p ∈ U', ψ p = p) ∧
      (∀ w, (ψ (betaCircle w)).1 = s →
        mfderiv (𝓡 1) (𝓡 1) (fun w => (ψ (betaCircle w)).1) w ≠ 0) ∧
      {w | (ψ (betaCircle w)).1 = s}.ncard < {w | (φ (betaCircle w)).1 = s}.ncard := by
  obtain ⟨g, σ, t₁, -, -, hfg, hσ, -, -, -, hg₁, -, -⟩ := hss
  obtain ⟨ψ, hψ, hU', hreg, hcard⟩ := exists_isotopic_beta_push_add_two φ h hU hαU hφU hs
    ⟨cexp t₁, by
      have := hfg t₁
      simp only at this
      rw [this, hg₁, hσ]⟩
  exact ⟨ψ, hψ, hU', hreg, by omega⟩

theorem exists_isotopic_eqOn_nhds_axes (φ : TDiff) (h : torusMatrix φ = 1) {U : Set Torus}
    (hU : IsOpen U) (hαU : range alphaCircle ⊆ U) (hφU : ∀ p ∈ U, φ p = p) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∃ V : Set Torus, IsOpen V ∧
      range alphaCircle ∪ range betaCircle ⊆ V ∧ ∀ p ∈ V, ψ p = p :=
  exists_isotopic_eqOn_nhds_axes_of_push exists_isotopic_beta_push φ h hU hαU hφU

end GC.Seifert
