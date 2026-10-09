import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigon
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonInnermost
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonLift

/-!
# Removing two crossings with a level circle

For `φ` with matrix one and a regular height `s` attained by `φ ∘ alphaCircle`, the number of
crossings of `φ (α)` with the level circle `α_s` drops by exactly two after composing with a
diffeomorphism isotopic to the identity, and `s` stays regular (`exists_isotopic_height_push`);
the frozen `exists_isotopic_ncard_lt` follows.

Proof. Lift `φ` to `Φ` commuting with `ℤ²`, put `γ t = Φ (t, 0)`, `σ` a real angle of `s` and
`g = γ₂ - σ`, a periodic function crossing the integers transversally. A minimal upper arc
`[a, b]` of `g` (`exists_minimal_upperArc`, minimal horizontal extent) bounds an upper bigon at
level `c = σ + k`; it is empty for the lifted family `t ↦ Φ (t, n)`
(`IsUpperBigon.family_mem_region`), has `b - a < 1`, and is disjoint from its non-zero integer
translates (`IsUpperBigon.disjoint_region` for horizontal ones, the strip `c ≤ y < c + 1` for the
others). So `torusCover` is injective near the bigon, which gives the neighbourhood `N` of the
torus push `exists_torus_bigon_push`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

theorem injOn_torusCover_ball (x : ℝ × ℝ) : InjOn torusCover (ball x (1 / 2)) := by
  intro z hz z' hz' he
  obtain ⟨m, n, hmn⟩ := torusCover_eq_torusCover_iff.mp he
  have hd : dist z z' < 1 := by
    have := dist_triangle_right z z' x
    rw [mem_ball] at hz hz'
    linarith
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, hmn] at hd
  simp only [add_sub_cancel_left] at hd
  have hm : m = 0 := by
    have : |(m : ℝ)| < 1 := hd.1
    rw [← Int.cast_abs] at this
    have : |m| < 1 := by exact_mod_cast this
    rw [abs_lt] at this
    omega
  have hn : n = 0 := by
    have : |(n : ℝ)| < 1 := hd.2
    rw [← Int.cast_abs] at this
    have : |n| < 1 := by exact_mod_cast this
    rw [abs_lt] at this
    omega
  rw [hmn, hm, hn]
  simp

theorem bigonInt_eq_zero_of_abs_lt_one {m : ℤ} (h : |(m : ℝ)| < 1) : m = 0 := by
  rw [← Int.cast_abs] at h
  have : |m| < 1 := by exact_mod_cast h
  rw [abs_lt] at this
  omega

theorem IsUpperBigon.family_mem_region' {ι : Type*} {Γ : ι → ℝ → ℝ × ℝ} {i₀ : ι}
    {γ : ℝ → ℝ × ℝ} {c t₁ t₂ : ℝ} (hΓ0 : Γ i₀ = γ)
    (h : IsUpperBigon γ c t₁ t₂) (hM : ∀ t ∈ Icc t₁ t₂, (γ t).2 < c + 1)
    (hl : ∀ᶠ u in 𝓝[<] t₁, (γ u).2 < c) (hr : ∀ᶠ u in 𝓝[>] t₂, (γ u).2 < c)
    (hΓc : ∀ i, Continuous (Γ i))
    (hinj : ∀ i j t u, Γ i t = Γ j u → i = j ∧ t = u)
    (hunb : ∀ i t (R : ℝ), (∃ u, t ≤ u ∧ R < ‖Γ i u‖) ∧ ∃ u, u ≤ t ∧ R < ‖Γ i u‖)
    (htr : ∀ i t, (Γ i t).2 = c → ∀ δ > 0, ∃ u ∈ Ioo (t - δ) (t + δ), c < (Γ i u).2)
    (hmin : ∀ i a b, a < b → (Γ i a).2 = c → (Γ i b).2 = c →
      (∀ u ∈ Ioo a b, c < (Γ i u).2 ∧ (Γ i u).2 < c + 1) →
      Γ i '' Icc a b ⊆ bigonRegion γ t₁ t₂ →
      |(γ t₂).1 - (γ t₁).1| ≤ |(Γ i b).1 - (Γ i a).1|)
    {i : ι} {t : ℝ} (ht : Γ i t ∈ bigonRegion γ t₁ t₂) : i = i₀ ∧ t ∈ Icc t₁ t₂ := by
  subst hΓ0
  exact h.family_mem_region hM hl hr hΓc hinj hunb htr hmin ht

theorem bigonRegion_add (γ : ℝ → ℝ × ℝ) (t₁ t₂ : ℝ) (v : ℝ × ℝ) :
    bigonRegion (fun t => γ t + v) t₁ t₂ = (fun z => z + v) '' bigonRegion γ t₁ t₂ := by
  refine (bigonRegion_image (Homeomorph.addRight v) ?_).symm
  unfold bigonCurveSet
  rw [image_union]
  congr 1
  · rw [image_image]
    rfl
  · change (fun z => z + v) '' segment ℝ (γ t₁) (γ t₂) = _
    have he : (fun z : ℝ × ℝ => z + v) = fun z => v + z := funext fun z => add_comm z v
    rw [he, segment_translate_image, add_comm v, add_comm v]

theorem exists_height_bigon (Φ : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    (hdeck : ∀ (p : ℝ × ℝ) (m n : ℤ), Φ (p.1 + m, p.2 + n) = ((Φ p).1 + m, (Φ p).2 + n))
    (σ : ℝ) (γ : ℝ → ℝ × ℝ) (hγ : ∀ t, γ t = Φ (t, 0))
    (htr : ∀ t (k : ℤ), (γ t).2 = σ + k → deriv (fun u => (γ u).2) t ≠ 0)
    (hne : ∃ t : ℝ, ∃ k : ℤ, (γ t).2 = σ + k) :
    ∃ (c a b ε : ℝ) (N : Set (ℝ × ℝ)), a < b ∧ 0 < ε ∧ (∃ k : ℤ, c = σ + k) ∧
      (γ a).2 = c ∧ (γ b).2 = c ∧ (∀ t ∈ Ioo a b, c < (γ t).2) ∧
      (∀ t ∈ Icc (a - ε) (b + ε), t < a ∨ b < t → (γ t).2 < c) ∧
      IsOpen N ∧ bigonRegion γ a b ⊆ N ∧ (∀ y ∈ N, |y.2 - c| < 1) ∧
      (∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ N → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ N →
        m = 0 ∧ n = 0) ∧
      ∀ (t : ℝ) (n : ℤ), Φ (t, n) ∈ N → n = 0 ∧ t ∈ Ioo (a - ε) (b + ε) := by
  have hΦc : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.mp Φ.contMDiff
  have hγe : γ = fun t => Φ (t, 0) := funext hγ
  have hγs : ContDiff ℝ ∞ γ := by
    rw [hγe]
    exact hΦc.comp (contDiff_id.prodMk contDiff_const)
  have hΓ (t : ℝ) (n : ℤ) : Φ (t, n) = ((γ t).1, (γ t).2 + n) := by
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
  have hx (t : ℝ) : x (t + 1) = x t + 1 := by
    have := hshift t 1
    simp only [Int.cast_one] at this
    simp only [hxdef, this]
  have hderiv (t : ℝ) : deriv g t = deriv (fun u => (γ u).2) t := deriv_sub_const σ
  have htr' : ∀ t ∈ crossSet g, deriv g t ≠ 0 := by
    rintro t ⟨k, hk⟩
    rw [hderiv]
    exact htr t k (by simp only [hgdef] at hk; linarith)
  have hne' : (crossSet g).Nonempty := by
    obtain ⟨t, k, hk⟩ := hne
    exact ⟨t, k, by simp only [hgdef]; linarith⟩
  obtain ⟨a, b, hab, hmin⟩ := exists_minimal_upperArc hgc hper hgd htr' hne' hx
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
    exact congrArg Prod.fst (Φ.injective he)
  have hbig : IsUpperBigon γ c a b :=
    ⟨hab.lt, hγs.continuous.continuousOn, hga, hgb, habove, hγinj.injOn⟩
  have hM : ∀ t ∈ Icc a b, (γ t).2 < c + 1 := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with he | hlt
    · rw [← he, hga]; linarith
    · rcases eq_or_lt_of_le ht.2 with he' | hlt'
      · rw [he', hgb]; linarith
      · exact hbelow t ⟨hlt, hlt'⟩
  set D := bigonRegion γ a b with hDdef
  set Γ : ℤ → ℝ → ℝ × ℝ := fun n t => Φ (t, n) with hΓdef
  have hΓ0 : Γ 0 = γ := funext fun t => by simp only [hΓdef, Int.cast_zero, hγ]
  have hfam : ∀ (n : ℤ) t, Φ (t, n) ∈ D → n = 0 ∧ t ∈ Icc a b := by
    intro n t ht
    refine IsUpperBigon.family_mem_region' (Γ := Γ) hΓ0 hbig hM hl hr
      (fun i => hΦc.continuous.comp (continuous_id.prodMk continuous_const))
      (fun i j t u he => ?_) (fun i t R => ?_) (fun i t ht δ hδ => ?_)
      (fun i a' b' hab' ha' hb' hbetw _ => ?_) ht
    · have he' := Φ.injective he
      simp only [Prod.mk.injEq] at he'
      exact ⟨Int.cast_injective he'.2, he'.1⟩
    · set X := (Φ (t, i)).1
      set m : ℤ := ⌈|R| + |X|⌉ + 1
      have hm : |R| + |X| < m := by
        have := Int.le_ceil (|R| + |X|)
        simp only [m, Int.cast_add, Int.cast_one]
        linarith
      have hf (j : ℤ) : Φ (t + j, i) = (X + j, (Φ (t, i)).2) := by
        have := hdeck (t, i) j 0
        simp only [Int.cast_zero, add_zero] at this
        exact this
      have hnorm (y : ℝ × ℝ) : |y.1| ≤ ‖y‖ := by
        rw [← Real.norm_eq_abs]; exact norm_fst_le y
      refine ⟨⟨t + m, by linarith [abs_nonneg R, abs_nonneg X], ?_⟩,
        ⟨t + ((-m : ℤ) : ℝ), by push_cast; linarith [abs_nonneg R, abs_nonneg X], ?_⟩⟩
      · change R < ‖Φ (t + m, i)‖
        rw [hf]
        have h1 := hnorm (X + m, (Φ (t, i)).2)
        have h2 : |X + (m : ℝ)| ≥ X + m := le_abs_self _
        linarith [le_abs_self R, neg_abs_le X]
      · change R < ‖Φ (t + ((-m : ℤ) : ℝ), i)‖
        rw [hf]
        push_cast
        have h1 := hnorm (X + -(m : ℝ), (Φ (t, i)).2)
        have h2 : |X + -(m : ℝ)| ≥ -(X + -(m : ℝ)) := neg_le_abs _
        linarith [le_abs_self R, le_abs_self X]
    · change (Φ (t, i)).2 = c at ht
      rw [hΓ] at ht
      have hk' : (γ t).2 = σ + ((k - i : ℤ) : ℝ) := by push_cast; simp only at ht; linarith
      have hd := htr t (k - i) hk'
      obtain ⟨u, hu, hu'⟩ := exists_lt_of_hasDerivAt_ne
        ((hγs.snd.differentiable (by simp) t).hasDerivAt) hd hδ
      refine ⟨u, hu, ?_⟩
      change c < (Φ (u, i)).2
      rw [hΓ]
      simp only at ht hu' ⊢
      linarith
    · change (Φ (a', i)).2 = c at ha'
      change (Φ (b', i)).2 = c at hb'
      rw [hΓ] at ha' hb'
      simp only at ha' hb'
      have hup : IsUpperArc g a' b' := by
        refine ⟨hab', ⟨k - i, by simp only [hgdef]; push_cast; linarith⟩,
          by simp only [hgdef]; linarith, fun u hu => ?_⟩
        have := hbetw u hu
        change c < (Φ (u, i)).2 ∧ (Φ (u, i)).2 < c + 1 at this
        rw [hΓ] at this
        simp only at this
        simp only [hgdef]
        constructor <;> linarith [this.1, this.2]
      have := hmin a' b' hup
      change |(γ b).1 - (γ a).1| ≤ |(Φ (b', i)).1 - (Φ (a', i)).1|
      rw [hΓ, hΓ]
      exact this
  have hfam0 : ∀ t, γ t ∈ D → t ∈ Icc a b := by
    intro t ht
    have : Φ (t, ((0 : ℤ) : ℝ)) ∈ D := by rw [Int.cast_zero, ← hγ]; exact ht
    exact (hfam 0 t this).2
  have hba : b - a < 1 := by
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with he | hlt
    · obtain ⟨δ, hδ, hδP⟩ := exists_Ioo_of_eventually_nhdsLT hgl
      set δ' := min δ 1
      have hδ' : 0 < δ' := lt_min hδ one_pos
      have hδ'1 : δ' ≤ 1 := min_le_right _ _
      have hδ'δ : δ' ≤ δ := min_le_left _ _
      set u := a + 1 - δ' / 2
      have h1 := hδP (u - 1) ⟨by simp only [u]; linarith, by simp only [u]; linarith⟩
      have h2 := (hab.between u ⟨by simp only [u]; linarith, by simp only [u]; linarith⟩).1
      have h3 : g u = g (u - 1) := by
        have := hper (u - 1)
        rwa [sub_add_cancel] at this
      linarith
    · have := (hab.between (a + 1) ⟨by linarith, by linarith⟩).1
      rw [hper] at this
      exact lt_irrefl _ this
  obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.lt.le)
    hγs.continuous.snd.continuousOn
  set M := (γ tm).2
  have hMle : ∀ s ∈ Icc a b, (γ s).2 ≤ M := fun s hs => hmax hs
  have hMc : M < c + 1 := hM tm htm
  have hDy : ∀ p ∈ D, c ≤ p.2 ∧ p.2 < c + 1 := fun p hp =>
    ⟨hbig.region_snd_ge p hp, (hbig.region_snd_le hMle p hp).trans_lt hMc⟩
  have hsepD : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ D → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ D →
      m = 0 ∧ n = 0 := by
    intro m n z hz hz'
    have hn : n = 0 := by
      have h1 := hDy z hz
      have h2 := hDy _ hz'
      simp only at h2
      exact bigonInt_eq_zero_of_abs_lt_one (by rw [abs_lt]; constructor <;> linarith)
    subst hn
    refine ⟨?_, rfl⟩
    by_contra hm
    set v : ℝ × ℝ := ((m : ℝ), 0)
    set γ' : ℝ → ℝ × ℝ := fun t => γ t + v
    have hγ'e (t : ℝ) : γ' t = γ (t + m) := by
      rw [hshift]
      exact Prod.ext (by simp [γ', v]) (by simp [γ', v])
    have hbig' : IsUpperBigon γ' c a b := by
      refine ⟨hab.lt, (hγs.continuous.add continuous_const).continuousOn, ?_, ?_, ?_, ?_⟩
      · simp only [γ', v, Prod.snd_add, add_zero, hga]
      · simp only [γ', v, Prod.snd_add, add_zero, hgb]
      · intro t ht
        simp only [γ', v, Prod.snd_add, add_zero]
        exact habove t ht
      · intro t _ u _ he
        exact hγinj (add_right_cancel he)
    have hmfar : ∀ t ∈ Icc a b, t + (m : ℝ) ∉ Icc a b := by
      intro t ht ht'
      apply hm
      exact bigonInt_eq_zero_of_abs_lt_one (by
        rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2])
    have hreg' : bigonRegion γ' a b = (fun w => w + v) '' D := bigonRegion_add γ a b v
    have hdisj := hbig.disjoint_region hbig' ?_ ?_
    · refine Set.disjoint_left.mp hdisj hz' ?_
      rw [hreg']
      exact ⟨z, hz, Prod.ext (by simp [v]) (by simp [v])⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨t, ht, rfl⟩ hmem
      rw [hreg'] at hmem
      obtain ⟨w, hw, hwe⟩ := hmem
      have hw' : w = γ (t + ((-m : ℤ) : ℝ)) := by
        rw [hshift]
        have := congrArg (fun y => y - v) hwe
        simp only [add_sub_cancel_right] at this
        rw [this]
        refine Prod.ext ?_ ?_ <;> simp [v, sub_eq_add_neg]
      rw [hw'] at hw
      have := hfam0 _ hw
      apply hmfar (t + ((-m : ℤ) : ℝ)) this
      push_cast
      simpa using ht
    · rw [Set.disjoint_left]
      rintro _ ⟨t, ht, rfl⟩ hmem
      rw [hγ'e] at hmem
      exact hmfar t ht (hfam0 _ hmem)
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
  have hεδ₁ : ε < δ₁ := by
    have := min_le_left δ₁ δ₂; simp only [ε]; linarith
  have hεδ₂ : ε < δ₂ := by
    have := min_le_right δ₁ δ₂; simp only [ε]; linarith
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
  set P := Φ '' F
  have hPc : IsClosed P := Φ.toHomeomorph.isClosedMap F hFc
  have hDP : ∀ y ∈ D, y ∉ P := by
    rintro y hy ⟨p, ⟨⟨n, hn⟩, hpF⟩, rfl⟩
    have hp : p = (p.1, (n : ℝ)) := Prod.ext rfl hn
    rw [hp] at hy
    obtain ⟨rfl, ht⟩ := hfam n p.1 hy
    apply hpF
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [hn, Int.cast_zero]
    norm_num
  set N := T ∩ {y : ℝ × ℝ | |y.2 - c| < 1} ∩ Pᶜ
  have hNo : IsOpen N :=
    (hTo.inter (isOpen_lt (continuous_abs.comp (continuous_snd.sub continuous_const))
      continuous_const)).inter hPc.isOpen_compl
  refine ⟨c, a, b, ε, N, hab.lt, hε, ⟨k, rfl⟩, hga, hgb, habove, ?_, hNo, ?_, ?_, ?_, ?_⟩
  · intro t ht hside
    rcases hside with h | h
    · exact hδ₁P t ⟨by linarith [ht.1], h⟩
    · exact hδ₂P t ⟨h, by linarith [ht.2]⟩
  · intro y hy
    obtain ⟨h1, h2⟩ := hDy y hy
    exact ⟨⟨hDT hy, show |y.2 - c| < 1 by rw [abs_lt]; constructor <;> linarith⟩, hDP y hy⟩
  · exact fun y hy => hy.1.2
  · intro m n z hz hz'
    have he := hTinj hz.1.1 hz'.1.1 (by rw [torusCover_add_int])
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only at h1 h2
    exact ⟨by exact_mod_cast (show (m : ℝ) = 0 by linarith),
      by exact_mod_cast (show (n : ℝ) = 0 by linarith)⟩
  · intro t n ht
    by_contra hcon
    apply ht.2
    refine ⟨(t, n), ⟨⟨n, rfl⟩, fun hm => hcon ?_⟩, rfl⟩
    have hn : n = 0 := by
      refine bigonInt_eq_zero_of_abs_lt_one ?_
      rw [abs_lt]
      constructor <;> linarith [hm.2.1, hm.2.2]
    exact ⟨hn, hm.1⟩

theorem exists_isotopic_height_push (φ : TDiff) (h : torusMatrix φ = 1) {s : Circle}
    (hs : IsRegularHeight φ s) (hne : ∃ z, heightOnCircle φ z = s) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ IsRegularHeight ψ s ∧
      {z | heightOnCircle ψ z = s}.ncard + 2 = {z | heightOnCircle φ z = s}.ncard := by
  obtain ⟨Φ, hlift, hdeck⟩ := exists_lift_of_torusMatrix_eq_one φ h
  set σ := rep s
  set γ : ℝ → ℝ × ℝ := fun t => Φ (t, 0) with hγdef
  have hΦc : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.mp Φ.contMDiff
  have hγs : ContDiff ℝ ∞ γ := hΦc.comp (contDiff_id.prodMk contDiff_const)
  have hfγ (t : ℝ) : φ (alphaCircle (cexp t)) = torusCover (γ t) := by
    rw [alphaCircle_cexp, hlift]
  have hfg (t : ℝ) : heightOnCircle φ (cexp t) = cexp (γ t).2 := by
    rw [heightOnCircle, hfγ, torusCover_eq]
  have htr : ∀ t (k : ℤ), (γ t).2 = σ + k → deriv (fun u => (γ u).2) t ≠ 0 := by
    intro t k hk
    refine deriv_lift_ne_zero (contMDiff_heightOnCircle φ) hγs.snd hfg (hs _ ?_)
    rw [hfg, hk, cexp_add_int, cexp_rep]
  have hne' : ∃ t : ℝ, ∃ k : ℤ, (γ t).2 = σ + k := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨t, rfl⟩ := cexp_surjective z
    rw [hfg, ← cexp_rep s] at hz
    obtain ⟨k, hk⟩ := cexp_eq_cexp_iff.mp hz
    exact ⟨t, k, hk⟩
  obtain ⟨c, a, b, ε, N, hab, hε, ⟨k, hck⟩, ha, hb, hin, hout, hNo, hDN, hNc, hsep, hempN⟩ :=
    exists_height_bigon Φ hdeck σ γ (fun _ => rfl) htr hne'
  have hcs : cexp c = s := by rw [hck, cexp_add_int, cexp_rep]
  have hdγ (t : ℝ) : HasDerivAt γ (fderiv ℝ Φ (t, 0) (1, 0)) t :=
    hasDerivAt_diffeomorph_horizontal Φ 0 t
  have hdγ2 (t : ℝ) : (deriv γ t).2 = deriv (fun u => (γ u).2) t := by
    rw [(hdγ t).deriv]
    exact ((hasDerivAt_snd_comp (hdγ t)).deriv).symm
  have himm (t : ℝ) : deriv γ t ≠ 0 := by
    rw [(hdγ t).deriv]
    intro h0
    have := fderiv_injective_of_diffeomorph Φ (t, 0) (h0.trans (map_zero _).symm)
    simp at this
  have hγinj : Function.Injective γ := fun t u he => congrArg Prod.fst (Φ.injective he)
  set f : Circle → Torus := fun z => φ (alphaCircle z)
  have hemp : ∀ z (y : ℝ × ℝ), y ∈ N → f z = torusCover y →
      ∃ t ∈ Ioo (a - ε) (b + ε), cexp t = z ∧ γ t = y := by
    intro z y hy hzy
    obtain ⟨t, rfl⟩ := cexp_surjective z
    have he : torusCover y = torusCover (γ t) := by rw [← hzy]; exact hfγ t
    obtain ⟨m, n, hmn⟩ := torusCover_eq_torusCover_iff.mp he
    have hyΦ : y = Φ (t + m, n) := by
      rw [hmn]
      have := hdeck (t, 0) m n
      simp only [zero_add] at this
      rw [this]
    obtain ⟨rfl, ht⟩ := hempN (t + m) n (hyΦ ▸ hy)
    refine ⟨t + m, ht, cexp_add_int t m, ?_⟩
    rw [hyΦ, Int.cast_zero]
  obtain ⟨Q, hQ, ⟨C, hCc, -, hQC, -, hCcross⟩, hiff, h12, h1, h2⟩ :=
    exists_torus_bigon_push (f := f) hγs hfγ (σ := 1) (by norm_num) hab hε ha hb
      (fun t ht => by rw [one_mul]; linarith [hin t ht])
      (fun t ht hs' => by rw [one_mul]; linarith [hout t ht hs'])
      (by rw [hdγ2]; exact htr a k (ha.trans hck))
      (by rw [hdγ2]; exact htr b k (hb.trans hck))
      (fun t _ => himm t) hγinj.injOn hNo hDN hNc hsep hemp
  rw [hcs] at hiff h1 h2 hCcross
  have hfc : Continuous f := φ.continuous.comp (continuous_id.prodMk continuous_const)
  refine ⟨φ.trans Q, isotopicDiffeomorph_trans_of_refl φ hQ, fun z hz => ?_,
    ncard_add_two_of_forall_iff hs.finite h12 h1 h2 hiff⟩
  have hzC := hCcross z hz
  have hev : heightOnCircle (φ.trans Q) =ᶠ[𝓝 z] heightOnCircle φ :=
    (eventuallyEq_of_not_mem_support hCc hQC hfc hzC).fun_comp Prod.snd
  rw [hev.mfderiv_eq]
  exact hs z ((hiff z).mp hz).1

theorem exists_isotopic_ncard_lt (φ : TDiff) (h : torusMatrix φ = 1) {s : Circle}
    (hs : IsRegularHeight φ s) (hne : ∃ z, heightOnCircle φ z = s) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ IsRegularHeight ψ s ∧
      {z | heightOnCircle ψ z = s}.ncard < {z | heightOnCircle φ z = s}.ncard := by
  obtain ⟨ψ, hψ, hreg, hcard⟩ := exists_isotopic_height_push φ h hs hne
  exact ⟨ψ, hψ, hreg, by omega⟩

end GC.Seifert
