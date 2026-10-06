import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# A point of an arc in a curve: sides, off-arc points, and a local defining functional
(lane S-BCF02-G4, group G4a; companion of `ArcInteriorOpenG6C`)

Let `B` be locally a topological curve near `y₀ = γ t₀`: an embedding `s : ℝ → H` with
`s 0 = y₀` and `range s = B ∩ O` (`O` open) and a nonzero derivative `w = s'(0)`; and let
`γ : [0, 1] → B` be a continuous injective arc. Then there are a continuous linear functional `ℓ`
(`ℓ w = 1`), a sign `σ = ±1`, `δ > 0` and an open `V ∋ y₀` such that every point `z ∈ B ∩ V` is

* `y₀`, or an arc point `γ t` with `0 < |t - t₀| < δ`, `t < t₀ ⟹ σ ℓ(z - y₀) < 0` and
  `t₀ < t ⟹ 0 < σ ℓ(z - y₀)`, or
* off the arc (only at an end of the arc: `t₀ = 0` with `σ ℓ(z - y₀) < 0`, `t₀ = 1` with `> 0`),

the arc points of `V` have parameter within `δ` of `t₀`, and at an end of the arc every
neighbourhood of `y₀` contains a point of `B` off the arc (the end of an arc is not an interior
point of the arc in `B`).

* `arc_point_classification_core_BG4`: the case of an increasing parametrization `c = s⁻¹ ∘ γ`;
* `arc_point_classification_BG4`: the general case (`c` monotone: reflect `s` and `ℓ`).
-/

set_option autoImplicit false

open Set Function Topology Filter Metric
open scoped Real

namespace DifferentialGeometry.Topology

/-- **The classification for an increasing parametrization** (see the module docstring). -/
theorem arc_point_classification_core_BG4 {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {s : ℝ → H} {B O : Set H} (hs : IsEmbedding s) (hO : IsOpen O) (hsr : range s = B ∩ O)
    {γ : ℝ → H} (hγi : InjOn γ (Icc 0 1)) (hγc : ContinuousOn γ (Icc 0 1))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hs0 : s 0 = γ t₀)
    {c : ℝ → ℝ} {a b θ : ℝ} (hab : a ≤ t₀ ∧ t₀ ≤ b) (hJ : Icc a b ⊆ Icc 0 1) (hθ : 0 < θ)
    (hcov : ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < θ → t ∈ Icc a b)
    (hcc : ContinuousOn c (Icc a b)) (hcm : StrictMonoOn c (Icc a b))
    (hsc : ∀ t ∈ Icc a b, s (c t) = γ t) (hc0 : c t₀ = 0)
    (ha0 : a = t₀ → t₀ = 0) (hb1 : b = t₀ → t₀ = 1)
    {ℓ : H →L[ℝ] ℝ} {η : ℝ} (hη : 0 < η)
    (hpos : ∀ x : ℝ, 0 < x → x < η → 0 < ℓ (s x - s 0))
    (hneg : ∀ x : ℝ, -η < x → x < 0 → ℓ (s x - s 0) < 0) :
    ∃ (V : Set H) (δ : ℝ), IsOpen V ∧ γ t₀ ∈ V ∧ 0 < δ ∧ δ ≤ θ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ V → |t - t₀| < δ) ∧
      (∀ z ∈ B ∩ V, z = γ t₀ ∨
        (∃ t ∈ Icc (0 : ℝ) 1, 0 < |t - t₀| ∧ |t - t₀| < δ ∧ z = γ t ∧
          ((t < t₀ ∧ ℓ (z - γ t₀) < 0) ∨ (t₀ < t ∧ 0 < ℓ (z - γ t₀)))) ∨
        (z ∉ γ '' Icc 0 1 ∧ ((t₀ = 0 ∧ ℓ (z - γ t₀) < 0) ∨ (t₀ = 1 ∧ 0 < ℓ (z - γ t₀))))) ∧
      ((t₀ = 0 ∨ t₀ = 1) → ∀ N : Set H, IsOpen N → γ t₀ ∈ N → ∃ z ∈ B ∩ N, z ∉ γ '' Icc 0 1) := by
  classical
  have hy₀ : γ t₀ ∈ B ∩ O := by
    rw [← hs0, ← hsr]
    exact mem_range_self 0
  have hat₀ : t₀ ∈ Icc a b := ⟨hab.1, hab.2⟩
  have haJ : a ∈ Icc a b := ⟨le_rfl, hab.1.trans hab.2⟩
  have hbJ : b ∈ Icc a b := ⟨hab.1.trans hab.2, le_rfl⟩
  have hm₁neg : a < t₀ → c a < 0 := fun h => by
    rw [← hc0]
    exact hcm haJ hat₀ h
  have hm₂pos : t₀ < b → 0 < c b := fun h => by
    rw [← hc0]
    exact hcm hat₀ hbJ h
  -- the radius `r` of the parameter window
  obtain ⟨r, hr0, hrη, hr₁, hr₂⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ η ∧ (a < t₀ → r ≤ -c a) ∧
      (t₀ < b → r ≤ c b) := by
    refine ⟨min η (min (if a < t₀ then -c a else η) (if t₀ < b then c b else η)), ?_, ?_, ?_, ?_⟩
    · refine lt_min hη (lt_min ?_ ?_)
      · split_ifs with h
        · linarith [hm₁neg h]
        · exact hη
      · split_ifs with h
        · exact hm₂pos h
        · exact hη
    · exact min_le_left _ _
    · intro h
      refine (min_le_right _ _).trans ((min_le_left _ _).trans ?_)
      simp [h]
    · intro h
      refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
      simp [h]
  -- the far part of the arc
  have hKc : IsCompact (γ '' (Icc 0 1 ∩ {t | θ ≤ |t - t₀|})) :=
    (isCompact_Icc.inter_right (isClosed_le continuous_const
      (continuous_abs.comp (continuous_id.sub continuous_const)))).image_of_continuousOn
      (hγc.mono inter_subset_left)
  have hy₀K : γ t₀ ∉ γ '' (Icc 0 1 ∩ {t | θ ≤ |t - t₀|}) := by
    rintro ⟨t, ⟨ht, htθ⟩, hteq⟩
    have : t = t₀ := hγi ht ht₀ hteq
    have h1 : θ ≤ |t - t₀| := htθ
    rw [this, sub_self, abs_zero] at h1
    linarith
  obtain ⟨ρ, hρ, hρK⟩ := Metric.mem_nhds_iff.mp (hKc.isClosed.isOpen_compl.mem_nhds hy₀K)
  obtain ⟨N', hN', hN'r⟩ := hs.isInducing.isOpen_iff.mp (isOpen_Ioo (a := -r) (b := r))
  have h0r : (0 : ℝ) ∈ s ⁻¹' N' := by
    rw [hN'r]
    exact ⟨by linarith, hr0⟩
  have hiso : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ N' ∩ O ∩ Metric.ball (γ t₀) ρ → |t - t₀| < θ := by
    intro t ht htV
    by_contra hge
    push Not at hge
    exact hρK htV.2 ⟨t, ⟨ht, hge⟩, rfl⟩
  -- arc points with prescribed parameter
  have harcR : ∀ x : ℝ, 0 < x → x < r → t₀ < b → ∃ t ∈ Icc t₀ b, c t = x := by
    intro x hx hxr hb
    have h1 : x ≤ c b := hxr.le.trans (hr₂ hb)
    have := intermediate_value_Icc hab.2 (hcc.mono (Icc_subset_Icc_left hab.1))
      (show x ∈ Icc (c t₀) (c b) from ⟨by rw [hc0]; exact hx.le, h1⟩)
    exact this
  have harcL : ∀ x : ℝ, -r < x → x < 0 → a < t₀ → ∃ t ∈ Icc a t₀, c t = x := by
    intro x hx hxr ha
    have h1 : c a ≤ x := by linarith [hr₁ ha]
    have := intermediate_value_Icc hab.1 (hcc.mono (Icc_subset_Icc_right hab.2))
      (show x ∈ Icc (c a) (c t₀) from ⟨h1, by rw [hc0]; exact hxr.le⟩)
    exact this
  -- off-arc points beyond an end of the arc
  have hoffR : ∀ x : ℝ, 0 < x → ¬ t₀ < b → s x ∈ N' ∩ O ∩ Metric.ball (γ t₀) ρ →
      s x ∉ γ '' Icc 0 1 := by
    intro x hx hb hsV
    rintro ⟨t', ht', hγt'⟩
    have h1 : |t' - t₀| < θ := hiso t' ht' (by rw [hγt']; exact hsV)
    have ht'J : t' ∈ Icc a b := hcov t' ht' h1
    have hct : c t' = x := hs.injective (by rw [hsc t' ht'J, hγt'])
    have hbt : b = t₀ := le_antisymm (not_lt.mp hb) hab.2
    have : c t' ≤ c t₀ := hcm.monotoneOn ht'J hat₀ (by rw [← hbt]; exact ht'J.2)
    rw [hct, hc0] at this
    linarith
  have hoffL : ∀ x : ℝ, x < 0 → ¬ a < t₀ → s x ∈ N' ∩ O ∩ Metric.ball (γ t₀) ρ →
      s x ∉ γ '' Icc 0 1 := by
    intro x hx ha hsV
    rintro ⟨t', ht', hγt'⟩
    have h1 : |t' - t₀| < θ := hiso t' ht' (by rw [hγt']; exact hsV)
    have ht'J : t' ∈ Icc a b := hcov t' ht' h1
    have hct : c t' = x := hs.injective (by rw [hsc t' ht'J, hγt'])
    have hat : a = t₀ := le_antisymm hab.1 (not_lt.mp ha)
    have : c t₀ ≤ c t' := hcm.monotoneOn hat₀ ht'J (by rw [← hat]; exact ht'J.1)
    rw [hct, hc0] at this
    linarith
  refine ⟨N' ∩ O ∩ Metric.ball (γ t₀) ρ, θ, (hN'.inter hO).inter Metric.isOpen_ball,
    ⟨⟨by rw [← hs0]; exact h0r, hy₀.2⟩, Metric.mem_ball_self hρ⟩, hθ, le_rfl, hiso, ?_, ?_⟩
  · -- the classification
    rintro z ⟨hzB, hzV⟩
    obtain ⟨⟨hzN', hzO⟩, hzball⟩ := hzV
    have hzr : z ∈ range s := by
      rw [hsr]
      exact ⟨hzB, hzO⟩
    obtain ⟨x, rfl⟩ := hzr
    have hx : x ∈ Ioo (-r) r := by
      rw [← hN'r]
      exact hzN'
    have hsV : s x ∈ N' ∩ O ∩ Metric.ball (γ t₀) ρ := ⟨⟨hzN', hzO⟩, hzball⟩
    rcases lt_trichotomy x 0 with hx0 | hx0 | hx0
    · have hℓ : ℓ (s x - γ t₀) < 0 := by
        rw [← hs0]
        exact hneg x (by linarith [hx.1, hrη]) hx0
      by_cases hat : a < t₀
      · obtain ⟨t, ht, htx⟩ := harcL x hx.1 hx0 hat
        have htJ : t ∈ Icc a b := ⟨ht.1, ht.2.trans hab.2⟩
        have hzt : s x = γ t := by rw [← htx, hsc t htJ]
        have hne : t ≠ t₀ := by
          rintro rfl
          rw [hc0] at htx
          linarith
        have hlt : t < t₀ := lt_of_le_of_ne ht.2 hne
        have hIcc : t ∈ Icc (0 : ℝ) 1 := hJ htJ
        have hth : |t - t₀| < θ := hiso t hIcc (by rw [← hzt]; exact hsV)
        exact Or.inr (Or.inl ⟨t, hIcc, abs_pos.mpr (sub_ne_zero.mpr hne), hth, hzt,
          Or.inl ⟨hlt, hℓ⟩⟩)
      · have ht0 : t₀ = 0 := ha0 (le_antisymm hab.1 (not_lt.mp hat))
        exact Or.inr (Or.inr ⟨hoffL x hx0 hat hsV, Or.inl ⟨ht0, hℓ⟩⟩)
    · exact Or.inl (by rw [hx0, hs0])
    · have hℓ : 0 < ℓ (s x - γ t₀) := by
        rw [← hs0]
        exact hpos x hx0 (by linarith [hx.2, hrη])
      by_cases hbt : t₀ < b
      · obtain ⟨t, ht, htx⟩ := harcR x hx0 hx.2 hbt
        have htJ : t ∈ Icc a b := ⟨hab.1.trans ht.1, ht.2⟩
        have hzt : s x = γ t := by rw [← htx, hsc t htJ]
        have hne : t ≠ t₀ := by
          rintro rfl
          rw [hc0] at htx
          linarith
        have hlt : t₀ < t := lt_of_le_of_ne ht.1 (Ne.symm hne)
        have hIcc : t ∈ Icc (0 : ℝ) 1 := hJ htJ
        have hth : |t - t₀| < θ := hiso t hIcc (by rw [← hzt]; exact hsV)
        exact Or.inr (Or.inl ⟨t, hIcc, abs_pos.mpr (sub_ne_zero.mpr hne), hth, hzt,
          Or.inr ⟨hlt, hℓ⟩⟩)
      · have ht1 : t₀ = 1 := hb1 (le_antisymm hab.2 (not_lt.mp hbt)).symm
        exact Or.inr (Or.inr ⟨hoffR x hx0 hbt hsV, Or.inr ⟨ht1, hℓ⟩⟩)
  · -- an end of the arc is not an interior point of the arc in `B`
    intro hend N hN hyN
    have hG : IsOpen (s ⁻¹' (N ∩ (N' ∩ O ∩ Metric.ball (γ t₀) ρ))) :=
      (hN.inter (((hN'.inter hO).inter Metric.isOpen_ball))).preimage hs.continuous
    have hγN' : γ t₀ ∈ N' := by
      have := h0r
      rwa [Set.mem_preimage, hs0] at this
    have h0G : (0 : ℝ) ∈ s ⁻¹' (N ∩ (N' ∩ O ∩ Metric.ball (γ t₀) ρ)) := by
      change s 0 ∈ N ∩ (N' ∩ O ∩ Metric.ball (γ t₀) ρ)
      rw [hs0]
      exact ⟨hyN, ⟨⟨hγN', hy₀.2⟩, Metric.mem_ball_self hρ⟩⟩
    obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.mp hG 0 h0G
    have hxε : ∀ x : ℝ, |x| < ε → s x ∈ N ∩ (N' ∩ O ∩ Metric.ball (γ t₀) ρ) := fun x hx =>
      hεG (by rwa [Metric.mem_ball, Real.dist_eq, sub_zero])
    have hsB : ∀ x : ℝ, s x ∈ B := fun x => by
      have : s x ∈ range s := mem_range_self x
      rw [hsr] at this
      exact this.1
    rcases hend with h0 | h1
    · -- `t₀ = 0`: points `s x` with `x < 0` small
      have hat : ¬ a < t₀ := by
        rintro hlt
        have := (hJ haJ).1
        linarith
      set x : ℝ := -(min ε r) / 2 with hxdef
      have hmin : 0 < min ε r := lt_min hε hr0
      have hxneg : x < 0 := by rw [hxdef]; linarith
      have hxabs : |x| < ε := by
        rw [hxdef, abs_div, abs_neg, abs_of_pos hmin, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith [min_le_left ε r]
      exact ⟨s x, ⟨hsB x, (hxε x hxabs).1⟩, hoffL x hxneg hat (hxε x hxabs).2⟩
    · -- `t₀ = 1`: points `s x` with `x > 0` small
      have hbt : ¬ t₀ < b := by
        rintro hlt
        have := (hJ hbJ).2
        linarith
      set x : ℝ := (min ε r) / 2 with hxdef
      have hmin : 0 < min ε r := lt_min hε hr0
      have hxpos : 0 < x := by rw [hxdef]; linarith
      have hxabs : |x| < ε := by
        rw [abs_of_pos hxpos, hxdef]
        linarith [min_le_left ε r]
      exact ⟨s x, ⟨hsB x, (hxε x hxabs).1⟩, hoffR x hxpos hbt (hxε x hxabs).2⟩

/-- **The classification for a general parametrization** (see the module docstring): the
orientation of `c = s⁻¹ ∘ γ` is handled by reflecting `s` and `ℓ`. -/
theorem arc_point_classification_BG4 {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {s : ℝ → H} {B O : Set H} (hs : IsEmbedding s) (hO : IsOpen O) (hsr : range s = B ∩ O)
    {γ : ℝ → H} (hγi : InjOn γ (Icc 0 1)) (hγc : ContinuousOn γ (Icc 0 1))
    (hγB : γ '' Icc 0 1 ⊆ B) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hs0 : s 0 = γ t₀) {w : H}
    (hsd : HasDerivAt s w 0) (hw : w ≠ 0) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ (ℓ : H →L[ℝ] ℝ) (V : Set H) (δ : ℝ), ℓ w ≠ 0 ∧ IsOpen V ∧ γ t₀ ∈ V ∧ 0 < δ ∧ δ ≤ δ₀ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ V → |t - t₀| < δ) ∧
      (∀ z ∈ B ∩ V, z = γ t₀ ∨
        (∃ t ∈ Icc (0 : ℝ) 1, 0 < |t - t₀| ∧ |t - t₀| < δ ∧ z = γ t ∧
          ((t < t₀ ∧ ℓ (z - γ t₀) < 0) ∨ (t₀ < t ∧ 0 < ℓ (z - γ t₀)))) ∨
        (z ∉ γ '' Icc 0 1 ∧ ((t₀ = 0 ∧ ℓ (z - γ t₀) < 0) ∨ (t₀ = 1 ∧ 0 < ℓ (z - γ t₀))))) ∧
      ((t₀ = 0 ∨ t₀ = 1) → ∀ N : Set H, IsOpen N → γ t₀ ∈ N → ∃ z ∈ B ∩ N, z ∉ γ '' Icc 0 1) := by
  classical
  have hy₀ : γ t₀ ∈ B ∩ O := by
    rw [← hs0, ← hsr]
    exact mem_range_self 0
  -- a functional with `ℓ w = 1` and the sign of `ℓ (s x - s 0)` near `0`
  obtain ⟨ℓ, hℓw⟩ := SeparatingDual.exists_eq_one (R := ℝ) hw
  have hg : HasDerivAt (fun x => ℓ (s x - s 0)) 1 0 := by
    have h1 : HasDerivAt (fun x => s x - s 0) w 0 := hsd.sub_const (s 0)
    have := ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rwa [hℓw] at this
  have hslope : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 0 < slope (fun x => ℓ (s x - s 0)) 0 x :=
    (hasDerivAt_iff_tendsto_slope.mp hg).eventually_const_lt zero_lt_one
  obtain ⟨η, hη, hηP⟩ := Metric.mem_nhdsWithin_iff.mp hslope
  have hgx : ∀ x : ℝ, |x| < η → x ≠ 0 → 0 < ℓ (s x - s 0) / x := by
    intro x hx hx0
    have := hηP ⟨by rwa [Metric.mem_ball, Real.dist_eq, sub_zero], hx0⟩
    change 0 < slope (fun x => ℓ (s x - s 0)) 0 x at this
    rwa [slope_def_field, sub_zero, sub_self, map_zero, sub_zero] at this
  have hpos : ∀ x : ℝ, 0 < x → x < η → 0 < ℓ (s x - s 0) := by
    intro x hx hxη
    have := hgx x (by rwa [abs_of_pos hx]) hx.ne'
    rcases div_pos_iff.mp this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd h2 (not_lt.mpr hx.le)
  have hneg : ∀ x : ℝ, -η < x → x < 0 → ℓ (s x - s 0) < 0 := by
    intro x hxη hx
    have := hgx x (by rw [abs_of_neg hx]; linarith) hx.ne
    rcases div_pos_iff.mp this with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact absurd h2 (not_lt.mpr hx.le)
    · exact h1
  -- the arc near `t₀` lies in `O`
  obtain ⟨δ₁, hδ₁, hδ₁le, hδ₁O⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < δ₁ → γ t ∈ O := by
    have h1 : γ ⁻¹' O ∈ 𝓝[Icc 0 1] t₀ :=
      (hγc t₀ ht₀).preimage_mem_nhdsWithin (hO.mem_nhds hy₀.2)
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp h1
    exact ⟨min δ δ₀, lt_min hδ hδ₀, min_le_right _ _, fun t ht htδ =>
      hsub ⟨by rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le htδ (min_le_left _ _), ht⟩⟩
  -- the parameter `c = s⁻¹ ∘ γ` near `t₀`
  have hrange : ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < δ₁ → γ t ∈ range s := by
    intro t ht htδ
    rw [hsr]
    exact ⟨hγB ⟨t, ht, rfl⟩, hδ₁O t ht htδ⟩
  let c : ℝ → ℝ := fun t => if h : γ t ∈ range s then Classical.choose h else 0
  have hsc₁ : ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < δ₁ → s (c t) = γ t := by
    intro t ht htδ
    simp only [c, hrange t ht htδ, ↓reduceDIte]
    exact Classical.choose_spec (hrange t ht htδ)
  have hc0 : c t₀ = 0 := by
    apply hs.injective
    rw [hsc₁ t₀ ht₀ (by simpa using hδ₁), hs0]
  set a : ℝ := max 0 (t₀ - δ₁ / 2) with ha
  set b : ℝ := min 1 (t₀ + δ₁ / 2) with hb
  have hab : a ≤ t₀ ∧ t₀ ≤ b :=
    ⟨max_le ht₀.1 (by linarith), le_min ht₀.2 (by linarith)⟩
  have hJ : Icc a b ⊆ Icc 0 1 := fun t ht =>
    ⟨(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)⟩
  have hJδ : ∀ t ∈ Icc a b, |t - t₀| < δ₁ := by
    intro t ht
    have h1 : t₀ - δ₁ / 2 ≤ t := (le_max_right _ _).trans ht.1
    have h2 : t ≤ t₀ + δ₁ / 2 := ht.2.trans (min_le_right _ _)
    rw [abs_lt]
    constructor <;> linarith
  have hcov : ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < δ₁ / 2 → t ∈ Icc a b := by
    intro t ht htθ
    rw [abs_lt] at htθ
    exact ⟨max_le ht.1 (by linarith [htθ.1]), le_min ht.2 (by linarith [htθ.2])⟩
  have hcc : ContinuousOn c (Icc a b) := by
    have h1 : ContinuousOn (s ∘ c) (Icc a b) :=
      (hγc.mono hJ).congr fun t ht => hsc₁ t (hJ ht) (hJδ t ht)
    exact hs.isInducing.continuousOn_iff.mpr h1
  have hci : InjOn c (Icc a b) := fun t ht t' ht' h =>
    hγi (hJ ht) (hJ ht') (by rw [← hsc₁ t (hJ ht) (hJδ t ht), ← hsc₁ t' (hJ ht') (hJδ t' ht'), h])
  have ha0 : a = t₀ → t₀ = 0 := by
    intro h
    rcases le_total 0 (t₀ - δ₁ / 2) with h1 | h1
    · rw [ha, max_eq_right h1] at h
      linarith
    · rw [ha, max_eq_left h1] at h
      exact h.symm
  have hb1 : b = t₀ → t₀ = 1 := by
    intro h
    rcases le_total 1 (t₀ + δ₁ / 2) with h1 | h1
    · rw [hb, min_eq_left h1] at h
      exact h.symm
    · rw [hb, min_eq_right h1] at h
      linarith
  rcases hcc.strictMonoOn_of_injOn_Icc' (hab.1.trans hab.2) hci with hmono | hanti
  · obtain ⟨V, δ, hV, hy, hδ, hδθ, hiso, hcls, hend⟩ := arc_point_classification_core_BG4 hs hO hsr
      hγi
      hγc ht₀ hs0 hab hJ (by linarith : 0 < δ₁ / 2) hcov hcc hmono
      (fun t ht => hsc₁ t (hJ ht) (hJδ t ht)) hc0 ha0 hb1 hη hpos hneg
    exact ⟨ℓ, V, δ, by rw [hℓw]; exact one_ne_zero, hV, hy, hδ, by linarith, hiso, hcls, hend⟩
  · have hs' : IsEmbedding (fun x : ℝ => s (-x)) := hs.comp (Homeomorph.neg ℝ).isEmbedding
    have hsr' : range (fun x : ℝ => s (-x)) = B ∩ O := by
      rw [← hsr]
      exact Function.Surjective.range_comp (g := s) neg_surjective
    obtain ⟨V, δ, hV, hy, hδ, hδθ, hiso, hcls, hend⟩ := arc_point_classification_core_BG4
      (s := fun x : ℝ => s (-x)) (c := fun t => -c t) (ℓ := -ℓ) hs' hO hsr' hγi hγc ht₀
      (by simpa using hs0) hab hJ (by linarith : 0 < δ₁ / 2) hcov hcc.neg
      (fun x hx y hy hxy => neg_lt_neg (hanti hx hy hxy))
      (fun t ht => by simpa using hsc₁ t (hJ ht) (hJδ t ht)) (by simp [hc0]) ha0 hb1 hη
      (fun x hx hxη => by
        have := hneg (-x) (by linarith) (by linarith)
        simpa using this)
      (fun x hxη hx => by
        have := hpos (-x) (by linarith) (by linarith)
        simpa using this)
    exact ⟨-ℓ, V, δ, by simp [hℓw], hV, hy, hδ, by linarith, hiso, hcls, hend⟩


end DifferentialGeometry.Topology
