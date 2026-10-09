import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonHeight
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusCurveCrossing

/-!
# Removing two crossings with a vertical cut inside the annulus

Let `φ` have matrix one with `φ (α)` disjoint from the level circle `α_s`, so `φ (α)` lies in the
annulus `T² ∖ α_s`, and let `θ` be a regular value of the first coordinate along `φ (α)`. If
`φ (α)` has a same-side arc against the vertical circle `β_θ = {θ} × S¹` (two crossings with no
crossing in between, in the shape of `HasSameSideArcIn`), then composing with a diffeomorphism
`Q` isotopic to the identity removes exactly two crossings with `β_θ`, keeps `θ` regular, keeps
`φ (α)` off `α_s`, and `Q` is the identity on an open set containing `α_s`
(`exists_isotopic_annulus_push`).

Proof. The lift `γ t = Φ (t, 0)` lies in one strip `lo < y < lo + 1`. The same-side arc has a
side `τ = ±1`; `G = τ (γ₁ - θ)` satisfies `G (t + 1) = G t + τ`, and a minimal upper arc of `G`
(vertical extent minimal, `exists_minimal_upperArc_add`) bounds a bigon. In the chart
`(x, y) ↦ (y, τ x)` (`cutChart`) it is an upper bigon, empty for the family `Φ (·, n)`
(`IsUpperBigon.family_mem_region'`); it lies in the strip and in a band `0 ≤ τ (x - c) < 1`, so
it is disjoint from its non-zero integer translates, and `exists_push_nbhd` gives the
neighbourhood for `exists_torus_bigon_push_vertical`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

def cutChart (τ : ℝ) (hτ : τ * τ = 1) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.2, τ * p.1)
  invFun q := (τ * q.2, q.1)
  left_inv p := by
    change (τ * (τ * p.1), p.2) = p
    rw [← mul_assoc, hτ, one_mul]
  right_inv q := by
    change (q.1, τ * (τ * q.2)) = q
    rw [← mul_assoc, hτ, one_mul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem cutChart_apply {τ : ℝ} (hτ : τ * τ = 1) (p : ℝ × ℝ) :
    cutChart τ hτ p = (p.2, τ * p.1) := rfl

theorem cutChart_image_segment {τ : ℝ} (hτ : τ * τ = 1) (a b : ℝ × ℝ) :
    cutChart τ hτ '' segment ℝ a b = segment ℝ (cutChart τ hτ a) (cutChart τ hτ b) := by
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap, image_image]
  refine image_congr fun s _ => ?_
  simp only [cutChart_apply, AffineMap.lineMap_apply_module, Prod.smul_mk, Prod.mk_add_mk,
    smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  refine Prod.ext rfl ?_
  simp only
  ring

theorem bigonRegion_cutChart {τ : ℝ} (hτ : τ * τ = 1) (γ : ℝ → ℝ × ℝ) (t₁ t₂ : ℝ) :
    bigonRegion (fun t => cutChart τ hτ (γ t)) t₁ t₂ = cutChart τ hτ '' bigonRegion γ t₁ t₂ := by
  refine (bigonRegion_image (cutChart τ hτ) ?_).symm
  unfold bigonCurveSet
  rw [image_union, image_image, cutChart_image_segment]

theorem IsUpperBigon.region_fst {γ : ℝ → ℝ × ℝ} {c t₁ t₂ : ℝ} (h : IsUpperBigon γ c t₁ t₂)
    {lo hi : ℝ} (hA : ∀ t ∈ Icc t₁ t₂, lo < (γ t).1 ∧ (γ t).1 < hi) :
    ∀ p ∈ bigonRegion γ t₁ t₂, lo < p.1 ∧ p.1 < hi := by
  have hJ : ∀ p ∈ bigonCurveSet γ t₁ t₂, lo < p.1 ∧ p.1 < hi := by
    rintro p (⟨t, ht, rfl⟩ | hp)
    · exact hA t ht
    · rw [h.segment_eq, segment_eq_uIcc] at hp
      have h1 := hA t₁ ⟨le_rfl, h.lt.le⟩
      have h2 := hA t₂ ⟨h.lt.le, le_rfl⟩
      have hm := hp.1
      rw [uIcc, mem_Icc] at hm
      constructor
      · exact lt_of_lt_of_le (lt_min h1.1 h2.1) hm.1
      · exact lt_of_le_of_lt hm.2 (max_lt h1.2 h2.2)
  have hnorm (q : ℝ × ℝ) : |q.1| ≤ ‖q‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le q
  intro p hp
  constructor
  · by_contra hle
    push Not at hle
    refine not_mem_bigonRegion_of_connected h.jordan (Z := {q : ℝ × ℝ | q.1 ≤ lo})
      ((convex_halfSpace_le (f := Prod.fst) ⟨fun _ _ => rfl, fun _ _ => rfl⟩ lo).isPreconnected)
      ?_ ?_ hle hp
    · rw [Set.disjoint_left]
      intro q hq hqJ
      exact absurd (hJ q hqJ).1 (not_lt.mpr hq)
    · intro R
      refine ⟨(-|lo| - |R| - 1, 0), show -|lo| - |R| - 1 ≤ lo by
        linarith [neg_abs_le lo, abs_nonneg R], ?_⟩
      have := hnorm (-|lo| - |R| - 1, 0)
      simp only at this
      have h3 : |(-|lo| - |R| - 1)| = |lo| + |R| + 1 := by
        rw [show -|lo| - |R| - 1 = -(|lo| + |R| + 1) by ring, abs_neg,
          abs_of_pos (by positivity)]
      rw [h3] at this
      linarith [le_abs_self R, abs_nonneg lo]
  · by_contra hle
    push Not at hle
    refine not_mem_bigonRegion_of_connected h.jordan (Z := {q : ℝ × ℝ | hi ≤ q.1})
      ((convex_halfSpace_ge (f := Prod.fst) ⟨fun _ _ => rfl, fun _ _ => rfl⟩ hi).isPreconnected)
      ?_ ?_ hle hp
    · rw [Set.disjoint_left]
      intro q hq hqJ
      exact absurd (hJ q hqJ).2 (not_lt.mpr hq)
    · intro R
      refine ⟨(|hi| + |R| + 1, 0), show hi ≤ |hi| + |R| + 1 by
        linarith [le_abs_self hi, abs_nonneg R], ?_⟩
      have := hnorm (|hi| + |R| + 1, 0)
      simp only at this
      rw [abs_of_pos (by positivity)] at this
      linarith [le_abs_self R, abs_nonneg hi]

theorem exists_push_nbhd {D P : Set (ℝ × ℝ)} (hD : IsCompact D) (hP : IsClosed P)
    (hDP : Disjoint D P)
    (hsepD : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ D → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ D →
      m = 0 ∧ n = 0)
    {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hDW : D ⊆ W) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ D ⊆ N ∧ N ⊆ W ∧ Disjoint N P ∧
      ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ N → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ N →
        m = 0 ∧ n = 0 := by
  have hinjD : InjOn torusCover D := by
    intro z hz z' hz' he
    obtain ⟨m, n, hmn⟩ := torusCover_eq_torusCover_iff.mp he
    obtain ⟨rfl, rfl⟩ := hsepD m n z' hz' (hmn ▸ hz)
    simpa using hmn
  obtain ⟨T, hTo, hDT, hTinj⟩ := hinjD.exists_isOpen_superset hD
    (fun _ _ => continuous_torusCover.continuousAt)
    (fun z _ => ⟨ball z (1 / 2), ball_mem_nhds z (by norm_num), injOn_torusCover_ball z⟩)
  refine ⟨T ∩ W ∩ Pᶜ, (hTo.inter hW).inter hP.isOpen_compl,
    fun z hz => ⟨⟨hDT hz, hDW hz⟩, Set.disjoint_left.mp hDP hz⟩,
    fun z hz => hz.1.2, Set.disjoint_left.mpr fun z hz => hz.2, fun m n z hz hz' => ?_⟩
  have he := hTinj hz.1.1 hz'.1.1 (by rw [torusCover_add_int])
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  simp only at h1 h2
  exact ⟨by exact_mod_cast (show (m : ℝ) = 0 by linarith),
    by exact_mod_cast (show (n : ℝ) = 0 by linarith)⟩

theorem mem_Ioo_floor_of_ne_int {S : Set ℝ} (hS : IsPreconnected S) {h : ℝ → ℝ}
    (hc : ContinuousOn h S) (hne : ∀ t ∈ S, ∀ n : ℤ, h t ≠ n) {t₀ : ℝ} (ht₀ : t₀ ∈ S)
    {t : ℝ} (ht : t ∈ S) : (⌊h t₀⌋ : ℝ) < h t ∧ h t < ⌊h t₀⌋ + 1 := by
  set j := ⌊h t₀⌋
  have hj : (j : ℝ) < h t₀ := lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hne t₀ ht₀ j))
  have hj' : h t₀ < j + 1 := Int.lt_floor_add_one _
  constructor
  · by_contra hle
    push Not at hle
    obtain ⟨u, hu, hue⟩ := hS.intermediate_value ht ht₀ hc ⟨hle, hj.le⟩
    exact hne u hu j hue
  · by_contra hle
    push Not at hle
    obtain ⟨u, hu, hue⟩ := hS.intermediate_value ht₀ ht hc ⟨hj'.le, hle⟩
    exact hne u hu (j + 1) (by rw [hue]; push_cast; ring)

theorem exists_sign_of_no_cross {x : ℝ → ℝ} (hx : Continuous x) {t₁ t₂ : ℝ} (ht : t₁ < t₂)
    (hno : ∀ t ∈ Ioo t₁ t₂, ∀ j : ℤ, x t ≠ x t₁ + j) :
    ∃ d : ℤ, (d = 1 ∨ d = -1) ∧
      ∀ t ∈ Ioo t₁ t₂, 0 < (d : ℝ) * (x t - x t₁) ∧ (d : ℝ) * (x t - x t₁) < 1 := by
  have hne : ∀ t ∈ Ioo t₁ t₂, ∀ n : ℤ, (fun u => x u - x t₁) t ≠ n := fun t ht n he =>
    hno t ht n (by simp only at he; linarith)
  set t₀ := (t₁ + t₂) / 2
  have ht₀ : t₀ ∈ Ioo t₁ t₂ := ⟨by simp only [t₀]; linarith, by simp only [t₀]; linarith⟩
  obtain ⟨J, hJdef⟩ : ∃ J : ℤ, J = ⌊x t₀ - x t₁⌋ := ⟨_, rfl⟩
  have hb : ∀ t ∈ Ioo t₁ t₂, (J : ℝ) < x t - x t₁ ∧ x t - x t₁ < J + 1 := by
    intro t ht
    have := mem_Ioo_floor_of_ne_int (h := fun u => x u - x t₁) isPreconnected_Ioo
      (hx.sub continuous_const).continuousOn hne ht₀ ht
    rw [hJdef]
    exact this
  have hlim : Tendsto (fun u => x u - x t₁) (𝓝[>] t₁) (𝓝 (x t₁ - x t₁)) :=
    ((hx.sub continuous_const).tendsto t₁).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] t₁, t ∈ Ioo t₁ t₂ := Ioo_mem_nhdsGT ht
  have hJ1 : (J : ℝ) ≤ x t₁ - x t₁ :=
    ge_of_tendsto hlim (hev.mono fun t ht => (hb t ht).1.le)
  have hJ2 : x t₁ - x t₁ ≤ J + 1 :=
    le_of_tendsto hlim (hev.mono fun t ht => (hb t ht).2.le)
  rw [sub_self] at hJ1 hJ2
  have hJ1' : J ≤ 0 := by exact_mod_cast hJ1
  have hJ2' : -1 ≤ J := by
    have : (-1 : ℝ) ≤ J := by linarith
    exact_mod_cast this
  rcases (show J = 0 ∨ J = -1 by omega) with hJ | hJ
  · refine ⟨1, Or.inl rfl, fun t ht => ?_⟩
    have := hb t ht
    rw [hJ] at this
    simp only [Int.cast_zero, Int.cast_one, one_mul, zero_add] at this ⊢
    exact this
  · refine ⟨-1, Or.inr rfl, fun t ht => ?_⟩
    have := hb t ht
    rw [hJ] at this
    simp only [Int.cast_neg, Int.cast_one] at this ⊢
    constructor <;> linarith [this.1, this.2]

theorem sub_eq_of_cexp_eq {g x : ℝ → ℝ} (hg : Continuous g) (hx : Continuous x)
    (h : ∀ t, cexp (g t) = cexp (x t)) (t₁ t₂ : ℝ) : g t₁ - x t₁ = g t₂ - x t₂ := by
  have hint (t : ℝ) : ∃ n : ℤ, g t - x t = n := by
    obtain ⟨n, hn⟩ := cexp_eq_cexp_iff.mp (h t)
    exact ⟨n, by linarith⟩
  obtain ⟨n₁, hn₁⟩ := hint t₁
  obtain ⟨n₂, hn₂⟩ := hint t₂
  by_contra hne
  have hne' : n₁ ≠ n₂ := fun he => hne (by rw [hn₁, hn₂, he])
  have hc : ContinuousOn (fun t => g t - x t) (uIcc t₁ t₂) := (hg.sub hx).continuousOn
  have hivt := intermediate_value_uIcc hc
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · have hmem : (n₁ : ℝ) + 1 / 2 ∈ uIcc (g t₁ - x t₁) (g t₂ - x t₂) := by
      rw [hn₁, hn₂, uIcc_of_le (by exact_mod_cast hlt.le)]
      have : (n₁ : ℝ) + 1 ≤ n₂ := by exact_mod_cast hlt
      constructor <;> linarith
    obtain ⟨u, -, hu⟩ := hivt hmem
    obtain ⟨m, hm⟩ := hint u
    simp only at hu
    rw [hm] at hu
    have : (2 * m : ℝ) = 2 * n₁ + 1 := by linarith
    have : 2 * m = 2 * n₁ + 1 := by exact_mod_cast this
    omega
  · have hmem : (n₂ : ℝ) + 1 / 2 ∈ uIcc (g t₁ - x t₁) (g t₂ - x t₂) := by
      rw [hn₁, hn₂, uIcc_of_ge (by exact_mod_cast hlt.le)]
      have : (n₂ : ℝ) + 1 ≤ n₁ := by exact_mod_cast hlt
      constructor <;> linarith
    obtain ⟨u, -, hu⟩ := hivt hmem
    obtain ⟨m, hm⟩ := hint u
    simp only at hu
    rw [hm] at hu
    have : (2 * m : ℝ) = 2 * n₂ + 1 := by linarith
    have : 2 * m = 2 * n₂ + 1 := by exact_mod_cast this
    omega

section ArcShift

variable {g : ℝ → ℝ}

theorem bigon_add_mul_int {d : ℤ} (hper : ∀ t, g (t + 1) = g t + d) (t : ℝ) (m : ℤ) :
    g (t + m) = g t + d * m := by
  have hp : Function.Periodic (fun u => g u - d * u) 1 := fun u => by
    simp only
    rw [hper]
    ring
  have := hp.int_mul m t
  simp only [mul_one] at this
  linarith

theorem IsUpperArc.shift_add {d : ℤ} (hper : ∀ t, g (t + 1) = g t + d) {a b : ℝ}
    (h : IsUpperArc g a b) (m : ℤ) : IsUpperArc g (a + m) (b + m) := by
  refine ⟨by linarith [h.lt], ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := h.level
    exact ⟨k + d * m, by rw [bigon_add_mul_int hper, hk]; push_cast; ring⟩
  · rw [bigon_add_mul_int hper, bigon_add_mul_int hper, h.same]
  · intro t ht
    have ht' : t - m ∈ Ioo a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := h.between (t - m) ht'
    rw [show t = (t - m) + m by ring, bigon_add_mul_int hper, bigon_add_mul_int hper]
    constructor <;> linarith [this.1, this.2]

theorem exists_minimal_upperArc_add (hg : Continuous g) {d : ℤ}
    (hper : ∀ t, g (t + 1) = g t + d) (hdiff : Differentiable ℝ g)
    (htr : ∀ t ∈ crossSet g, deriv g t ≠ 0) {a₀ b₀ : ℝ} (h₀ : IsUpperArc g a₀ b₀)
    {y : ℝ → ℝ} (hy : ∀ t, y (t + 1) = y t) :
    ∃ a b, IsUpperArc g a b ∧ ∀ a' b', IsUpperArc g a' b' → |y b - y a| ≤ |y b' - y a'| := by
  have hym : ∀ t (m : ℤ), y (t + m) = y t := by
    intro t m
    have := (show Function.Periodic y 1 from hy).int_mul m t
    rwa [mul_one] at this
  set S₀ : Set (ℝ × ℝ) := {p | IsUpperArc g p.1 p.2 ∧ p.1 ∈ Ico 0 1}
  have hfin : S₀.Finite := by
    refine Set.Finite.of_finite_image (f := Prod.fst)
      ((finite_crossSet_Icc hg hdiff htr 0 1).subset ?_) ?_
    · rintro _ ⟨p, hp, rfl⟩
      exact ⟨⟨_, hp.1.level.choose_spec⟩, hp.2.1, hp.2.2.le⟩
    · intro p hp q hq he
      have he' : p.1 = q.1 := he
      exact Prod.ext he' (hp.1.right_eq (he' ▸ hq.1))
  have hS₀ : S₀.Nonempty := by
    refine ⟨(a₀ + ((-⌊a₀⌋ : ℤ) : ℝ), b₀ + ((-⌊a₀⌋ : ℤ) : ℝ)), h₀.shift_add hper _, ?_, ?_⟩
    · push_cast; linarith [Int.floor_le a₀]
    · push_cast; linarith [Int.lt_floor_add_one a₀]
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image S₀ (fun p => |y p.2 - y p.1|) hfin hS₀
  refine ⟨p.1, p.2, hp.1, fun a' b' h' => ?_⟩
  have hmem : (a' + ((-⌊a'⌋ : ℤ) : ℝ), b' + ((-⌊a'⌋ : ℤ) : ℝ)) ∈ S₀ := by
    refine ⟨h'.shift_add hper _, ?_, ?_⟩
    · push_cast; linarith [Int.floor_le a']
    · push_cast; linarith [Int.lt_floor_add_one a']
  have := hmin _ hmem
  simp only [hym] at this
  exact this

theorem exists_minimal_upperArc_Ioo (hg : Continuous g) (hdiff : Differentiable ℝ g)
    (htr : ∀ t ∈ crossSet g, deriv g t ≠ 0) {a₀ b₀ : ℝ} (h₀ : IsUpperArc g a₀ b₀)
    (ha₀ : a₀ ∈ Ioo (0 : ℝ) 1) (hb₀ : b₀ ∈ Ioo (0 : ℝ) 1) (y : ℝ → ℝ) :
    ∃ a b, IsUpperArc g a b ∧ a ∈ Ioo (0 : ℝ) 1 ∧ b ∈ Ioo (0 : ℝ) 1 ∧
      ∀ a' b', IsUpperArc g a' b' → a' ∈ Ioo (0 : ℝ) 1 → b' ∈ Ioo (0 : ℝ) 1 →
        |y b - y a| ≤ |y b' - y a'| := by
  set S₀ : Set (ℝ × ℝ) := {p | IsUpperArc g p.1 p.2 ∧ p.1 ∈ Ioo (0 : ℝ) 1 ∧
    p.2 ∈ Ioo (0 : ℝ) 1}
  have hfin : S₀.Finite := by
    refine Set.Finite.of_finite_image (f := Prod.fst)
      ((finite_crossSet_Icc hg hdiff htr 0 1).subset ?_) ?_
    · rintro _ ⟨p, hp, rfl⟩
      exact ⟨⟨_, hp.1.level.choose_spec⟩, hp.2.1.1.le, hp.2.1.2.le⟩
    · intro p hp q hq he
      have he' : p.1 = q.1 := he
      exact Prod.ext he' (hp.1.right_eq (he' ▸ hq.1))
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image S₀ (fun p => |y p.2 - y p.1|) hfin
    ⟨(a₀, b₀), h₀, ha₀, hb₀⟩
  exact ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2, fun a' b' h' ha' hb' => hmin (a', b') ⟨h', ha', hb'⟩⟩

end ArcShift

theorem exists_annulus_bigon (Φ : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    (hdeck : ∀ (p : ℝ × ℝ) (m n : ℤ), Φ (p.1 + m, p.2 + n) = ((Φ p).1 + m, (Φ p).2 + n))
    (γ : ℝ → ℝ × ℝ) (hγ : ∀ t, γ t = Φ (t, 0)) {lo : ℝ}
    (hlo : ∀ t, lo < (γ t).2 ∧ (γ t).2 < lo + 1) (θ : ℝ)
    (htr : ∀ t (k : ℤ), (γ t).1 = θ + k → deriv (fun u => (γ u).1) t ≠ 0)
    {t₁ t₂ : ℝ} {k₀ : ℤ} (h₁₂ : t₁ < t₂) (h₁ : (γ t₁).1 = θ + k₀) (h₂ : (γ t₂).1 = θ + k₀)
    (hno : ∀ t ∈ Ioo t₁ t₂, ∀ j : ℤ, (γ t).1 ≠ θ + k₀ + j) :
    ∃ (τ c a b ε : ℝ) (N : Set (ℝ × ℝ)), τ ^ 2 = 1 ∧ a < b ∧ 0 < ε ∧ (∃ k : ℤ, c = θ + k) ∧
      (γ a).1 = c ∧ (γ b).1 = c ∧ (∀ t ∈ Ioo a b, 0 < τ * ((γ t).1 - c)) ∧
      (∀ t ∈ Icc (a - ε) (b + ε), t < a ∨ b < t → τ * ((γ t).1 - c) < 0) ∧
      IsOpen N ∧ bigonRegion γ a b ⊆ N ∧ (∀ y ∈ N, |y.1 - c| < 1) ∧
      (∀ y ∈ N, lo < y.2 ∧ y.2 < lo + 1) ∧
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
  have hγinj : Function.Injective γ := by
    intro t u he
    rw [hγ, hγ] at he
    exact congrArg Prod.fst (Φ.injective he)
  obtain ⟨d, hd, hsgn⟩ := exists_sign_of_no_cross (x := fun t => (γ t).1)
    hγs.continuous.fst h₁₂ (fun t ht j => by
      show (γ t).1 ≠ (γ t₁).1 + j
      rw [h₁]
      exact hno t ht j)
  set τ : ℝ := (d : ℝ) with hτdef
  have hτ2 : τ * τ = 1 := by rcases hd with hd | hd <;> rw [hτdef, hd] <;> norm_num
  have hτsq : τ ^ 2 = 1 := by rw [sq]; exact hτ2
  have hτabs : |τ| = 1 := by rcases hd with hd | hd <;> rw [hτdef, hd] <;> norm_num
  have hτ0 : τ ≠ 0 := by intro h0; rw [h0] at hτ2; norm_num at hτ2
  set G : ℝ → ℝ := fun t => τ * ((γ t).1 - θ) with hGdef
  have hGc : Continuous G := continuous_const.mul (hγs.continuous.fst.sub continuous_const)
  have hxd (t : ℝ) : HasDerivAt (fun u => (γ u).1) (deriv (fun u => (γ u).1) t) t :=
    (hγs.fst.differentiable (by simp) t).hasDerivAt
  have hGd' (t : ℝ) : HasDerivAt G (τ * deriv (fun u => (γ u).1) t) t :=
    ((hxd t).sub_const θ).const_mul τ
  have hGd : Differentiable ℝ G := fun t => (hGd' t).differentiableAt
  have hderivG (t : ℝ) : deriv G t = τ * deriv (fun u => (γ u).1) t := (hGd' t).deriv
  have hGper (t : ℝ) : G (t + 1) = G t + d := by
    have := hshift t 1
    simp only [Int.cast_one] at this
    simp only [hGdef, this]
    ring
  have hGx (t : ℝ) : (γ t).1 = θ + τ * G t := by
    simp only [hGdef]
    linear_combination (-((γ t).1 - θ)) * hτ2
  have htrG : ∀ t ∈ crossSet G, deriv G t ≠ 0 := by
    rintro t ⟨j, hj⟩
    rw [hderivG]
    refine mul_ne_zero hτ0 (htr t (d * j) ?_)
    rw [hGx, hj]
    push_cast
    ring
  have hup : IsUpperArc G t₁ t₂ := by
    refine ⟨h₁₂, ⟨d * k₀, ?_⟩, ?_, fun t ht => ?_⟩
    · simp only [hGdef, h₁]
      push_cast
      ring
    · simp only [hGdef, h₁, h₂]
    · obtain ⟨hp, hq⟩ := hsgn t ht
      simp only [h₁] at hp hq
      have e1 : G t = τ * ((γ t).1 - (θ + k₀)) + τ * k₀ := by simp only [hGdef]; ring
      have e2 : G t₁ = τ * k₀ := by simp only [hGdef, h₁]; ring
      rw [e1, e2]
      constructor <;> linarith
  have hy (t : ℝ) : (fun u => (γ u).2) (t + 1) = (fun u => (γ u).2) t := by
    have := hshift t 1
    simp only [Int.cast_one] at this
    simp only [this]
  obtain ⟨a, b, hab, hmin⟩ :=
    exists_minimal_upperArc_add hGc hGper hGd htrG hup (y := fun u => (γ u).2) hy
  obtain ⟨K, hK⟩ := hab.level
  set c := θ + τ * K with hcdef
  have hτc (t : ℝ) : τ * ((γ t).1 - c) = G t - K := by
    simp only [hGdef, hcdef]
    linear_combination (-(K : ℝ)) * hτ2
  have hga : (γ a).1 = c := by rw [hGx, hK]
  have hgb : (γ b).1 = c := by rw [hGx, hab.same, hK]
  have hHd (t : ℝ) : HasDerivAt G (deriv G t) t := (hGd t).hasDerivAt
  have hcross_a : a ∈ crossSet G := ⟨K, hK⟩
  have hcross_b : b ∈ crossSet G := ⟨K, hab.same.trans hK⟩
  have hdpos : 0 < deriv G a := by
    by_contra hle
    push Not at hle
    have hlt : deriv G a < 0 := lt_of_le_of_ne hle (htrG a hcross_a)
    have hn : HasDerivAt (fun u => -G u) (-deriv G a) a := (hHd a).neg
    obtain ⟨u, hu, hu'⟩ := ((eventually_lt_right_of_hasDerivAt_pos hn (by linarith)).and
      (Ioo_mem_nhdsGT hab.lt)).exists
    have := (hab.between u hu').1
    linarith
  have hdneg : deriv G b < 0 := by
    by_contra hle
    push Not at hle
    have hpos : 0 < deriv G b := lt_of_le_of_ne hle (Ne.symm (htrG b hcross_b))
    obtain ⟨u, hu, hu'⟩ := ((eventually_lt_left_of_hasDerivAt_pos (hHd b) hpos).and
      (Ioo_mem_nhdsLT hab.lt)).exists
    have := (hab.between u hu').1
    rw [hab.same] at hu
    linarith
  have hGl : ∀ᶠ u in 𝓝[<] a, G u < G a := eventually_lt_left_of_hasDerivAt_pos (hHd a) hdpos
  have hGr : ∀ᶠ u in 𝓝[>] b, G u < G b := by
    have hn : HasDerivAt (fun u => -G u) (-deriv G b) b := (hHd b).neg
    filter_upwards [eventually_lt_right_of_hasDerivAt_pos hn (by linarith)] with u hu
    linarith
  have hin : ∀ t ∈ Ioo a b, 0 < τ * ((γ t).1 - c) := fun t ht => by
    rw [hτc, ← hK]
    linarith [(hab.between t ht).1]
  set A := cutChart τ hτ2
  set γ' : ℝ → ℝ × ℝ := fun t => A (γ t) with hγ'def
  set c' := τ * c with hc'def
  have hγ'2 (t : ℝ) : (γ' t).2 - c' = G t - K := by
    rw [← hτc]
    simp only [hγ'def, hc'def, A, cutChart_apply]
    ring
  have hγ'1 (t : ℝ) : (γ' t).1 = (γ t).2 := rfl
  have hbig' : IsUpperBigon γ' c' a b := by
    refine ⟨hab.lt, (A.continuous.comp hγs.continuous).continuousOn, ?_, ?_, ?_, ?_⟩
    · have := hγ'2 a
      rw [hK, sub_self] at this
      linarith
    · have := hγ'2 b
      rw [hab.same, hK, sub_self] at this
      linarith
    · intro t ht
      have := hγ'2 t
      have := (hab.between t ht).1
      rw [hK] at this
      linarith
    · exact (A.injective.comp hγinj).injOn
  have hM' : ∀ t ∈ Icc a b, (γ' t).2 < c' + 1 := by
    intro t ht
    have e := hγ'2 t
    rcases eq_or_lt_of_le ht.1 with he | hlt
    · rw [← he]
      have e' := hγ'2 a
      rw [hK, sub_self] at e'
      linarith
    · rcases eq_or_lt_of_le ht.2 with he' | hlt'
      · rw [he']
        have e' := hγ'2 b
        rw [hab.same, hK, sub_self] at e'
        linarith
      · have := (hab.between t ⟨hlt, hlt'⟩).2
        rw [hK] at this
        linarith
  have hl' : ∀ᶠ u in 𝓝[<] a, (γ' u).2 < c' := by
    filter_upwards [hGl] with u hu
    have := hγ'2 u
    rw [hK] at hu
    linarith
  have hr' : ∀ᶠ u in 𝓝[>] b, (γ' u).2 < c' := by
    filter_upwards [hGr] with u hu
    have := hγ'2 u
    rw [hab.same, hK] at hu
    linarith
  set Γ' : ℤ → ℝ → ℝ × ℝ := fun n t => A (Φ (t, n)) with hΓ'def
  have hΓ'0 : Γ' 0 = γ' := funext fun t => by simp only [hΓ'def, hγ'def, Int.cast_zero, hγ]
  have hΓ'2 (n : ℤ) (t : ℝ) : (Γ' n t).2 - c' = G t - K := by
    rw [← hγ'2]
    simp only [hΓ'def, hγ'def, A, cutChart_apply, hΓ]
  have hΓ'1 (n : ℤ) (t : ℝ) : (Γ' n t).1 = (γ t).2 + n := by
    simp only [hΓ'def, A, cutChart_apply, hΓ]
  have hnormA (q : ℝ × ℝ) : |q.1| ≤ ‖A q‖ := by
    have := norm_snd_le (A q)
    rw [Real.norm_eq_abs] at this
    simp only [A, cutChart_apply, abs_mul, hτabs, one_mul] at this
    exact this
  have hfam' : ∀ (n : ℤ) t, Γ' n t ∈ bigonRegion γ' a b → n = 0 ∧ t ∈ Icc a b := by
    intro n t ht
    refine IsUpperBigon.family_mem_region' (Γ := Γ') hΓ'0 hbig' hM' hl' hr'
      (fun i => A.continuous.comp (hΦc.continuous.comp (continuous_id.prodMk continuous_const)))
      (fun i j t u he => ?_) (fun i t R => ?_) (fun i t ht δ hδ => ?_)
      (fun i a' b' hab' ha' hb' hbetw _ => ?_) ht
    · have he' := Φ.injective (A.injective he)
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
      refine ⟨⟨t + m, by linarith [abs_nonneg R, abs_nonneg X], ?_⟩,
        ⟨t + ((-m : ℤ) : ℝ), by push_cast; linarith [abs_nonneg R, abs_nonneg X], ?_⟩⟩
      · change R < ‖A (Φ (t + m, i))‖
        have h1 := hnormA (Φ (t + m, i))
        rw [hf] at h1 ⊢
        have h2 : |X + (m : ℝ)| ≥ X + m := le_abs_self _
        simp only at h1
        linarith [le_abs_self R, neg_abs_le X]
      · change R < ‖A (Φ (t + ((-m : ℤ) : ℝ), i))‖
        have h1 := hnormA (Φ (t + ((-m : ℤ) : ℝ), i))
        rw [hf] at h1 ⊢
        simp only at h1
        push_cast at h1 ⊢
        have h2 : |X + -(m : ℝ)| ≥ -(X + -(m : ℝ)) := neg_le_abs _
        linarith [le_abs_self R, le_abs_self X]
    · have e := hΓ'2 i t
      rw [ht, sub_self] at e
      have hct : t ∈ crossSet G := ⟨K, by linarith⟩
      obtain ⟨u, hu, hu'⟩ := exists_lt_of_hasDerivAt_ne (hHd t) (htrG t hct) hδ
      refine ⟨u, hu, ?_⟩
      have := hΓ'2 i u
      linarith
    · have ea := hΓ'2 i a'
      have eb := hΓ'2 i b'
      rw [ha', sub_self] at ea
      rw [hb', sub_self] at eb
      have hGa' : G a' = K := by linarith
      have hupa : IsUpperArc G a' b' := by
        refine ⟨hab', ⟨K, hGa'⟩, by linarith, fun u hu => ?_⟩
        have := hbetw u hu
        have e := hΓ'2 i u
        rw [hGa']
        constructor <;> linarith [this.1, this.2]
      have := hmin a' b' hupa
      rw [hγ'1, hγ'1, hΓ'1, hΓ'1, add_sub_add_right_eq_sub]
      exact this
  set D := bigonRegion γ a b with hDdef
  have hD'eq : bigonRegion γ' a b = A '' D := bigonRegion_cutChart hτ2 γ a b
  have hfam : ∀ (n : ℤ) t, Φ (t, n) ∈ D → n = 0 ∧ t ∈ Icc a b := fun n t ht =>
    hfam' n t (by rw [hD'eq]; exact mem_image_of_mem A ht)
  obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.lt.le)
    (A.continuous.comp hγs.continuous).snd.continuousOn
  set M := (γ' tm).2
  have hMle : ∀ u ∈ Icc a b, (γ' u).2 ≤ M := fun u hu => hmax hu
  have hMc : M < c' + 1 := hM' tm htm
  have hslab := hbig'.region_fst (lo := lo) (hi := lo + 1) (fun t _ => hlo t)
  have hDz : ∀ z ∈ D, (0 ≤ τ * (z.1 - c) ∧ τ * (z.1 - c) < 1) ∧ lo < z.2 ∧ z.2 < lo + 1 := by
    intro z hz
    have hAz : A z ∈ bigonRegion γ' a b := by rw [hD'eq]; exact mem_image_of_mem A hz
    have h1 := hbig'.region_snd_ge _ hAz
    have h2 := hbig'.region_snd_le hMle _ hAz
    have h3 := hslab _ hAz
    simp only [A, cutChart_apply] at h1 h2 h3
    refine ⟨⟨?_, ?_⟩, h3⟩
    · have : τ * (z.1 - c) = τ * z.1 - c' := by simp only [hc'def]; ring
      rw [this]; linarith
    · have : τ * (z.1 - c) = τ * z.1 - c' := by simp only [hc'def]; ring
      rw [this]; linarith
  have hsepD : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ D → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ D →
      m = 0 ∧ n = 0 := by
    intro m n z hz hz'
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDz z hz
    obtain ⟨⟨h1', h2'⟩, h3', h4'⟩ := hDz _ hz'
    simp only at h1' h2' h3' h4'
    refine ⟨int_eq_zero_of_abs_lt_one ?_, int_eq_zero_of_abs_lt_one ?_⟩
    · have e : τ * (z.1 + m - c) = τ * (z.1 - c) + τ * m := by ring
      rw [e] at h1' h2'
      have : |τ * (m : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
      rwa [abs_mul, hτabs, one_mul] at this
    · rw [abs_lt]; constructor <;> linarith
  have hDc : IsCompact D := by
    have := hbig'.isCompact_region
    rw [hD'eq] at this
    have hpre := A.isCompact_preimage.mpr this
    rwa [A.preimage_image] at hpre
  have hDx : ∀ z ∈ D, |z.1 - c| < 1 := by
    intro z hz
    obtain ⟨⟨h1, h2⟩, -⟩ := hDz z hz
    have : |τ * (z.1 - c)| < 1 := by rw [abs_lt]; constructor <;> linarith
    rwa [abs_mul, hτabs, one_mul] at this
  obtain ⟨δ₁, hδ₁, hδ₁P⟩ := exists_Ioo_of_eventually_nhdsLT hGl
  obtain ⟨δ₂, hδ₂, hδ₂P⟩ := exists_Ioo_of_eventually_nhdsGT hGr
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
  have hDP : Disjoint D P := by
    rw [Set.disjoint_left]
    rintro y hy ⟨p, ⟨⟨n, hn⟩, hpF⟩, rfl⟩
    have hp : p = (p.1, (n : ℝ)) := Prod.ext rfl hn
    rw [hp] at hy
    obtain ⟨rfl, ht⟩ := hfam n p.1 hy
    apply hpF
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [hn, Int.cast_zero]
    norm_num
  set W : Set (ℝ × ℝ) := {y | |y.1 - c| < 1} ∩ {y | lo < y.2 ∧ y.2 < lo + 1}
  have hWo : IsOpen W :=
    (isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  have hDW : D ⊆ W := fun z hz => ⟨hDx z hz, (hDz z hz).2⟩
  obtain ⟨N, hNo, hDN, hNW, hNP, hsepN⟩ := exists_push_nbhd hDc hPc hDP hsepD hWo hDW
  refine ⟨τ, c, a, b, ε, N, hτsq, hab.lt, hε, ⟨d * K, by simp only [hcdef, hτdef]; push_cast; ring⟩,
    hga, hgb, hin, ?_, hNo, hDN, fun y hy => (hNW hy).1, fun y hy => (hNW hy).2, hsepN, ?_⟩
  · intro t ht hside
    rw [hτc]
    rcases hside with h | h
    · have := hδ₁P t ⟨by linarith [ht.1], h⟩
      rw [hK] at this
      linarith
    · have := hδ₂P t ⟨h, by linarith [ht.2]⟩
      rw [hab.same, hK] at this
      linarith
  · intro t n ht
    by_contra hcon
    refine Set.disjoint_left.mp hNP ht ⟨(t, n), ⟨⟨n, rfl⟩, fun hm => hcon ?_⟩, rfl⟩
    have hn : n = 0 := by
      refine int_eq_zero_of_abs_lt_one ?_
      rw [abs_lt]
      constructor <;> linarith [hm.2.1, hm.2.2]
    exact ⟨hn, hm.1⟩

theorem exists_isotopic_annulus_push_add_two (φ : TDiff) (h : torusMatrix φ = 1) (s : Circle)
    (hs : ∀ z, heightOnCircle φ z ≠ s) (θ : Circle)
    (hθ : ∀ z, (φ (alphaCircle z)).1 = θ →
      mfderiv (𝓡 1) (𝓡 1) (fun z => (φ (alphaCircle z)).1) z ≠ 0)
    (harc : HasSameSideArcIn (fun z => (φ (alphaCircle z)).1) θ univ) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ (∀ z, heightOnCircle ψ z ≠ s) ∧
      (∀ z, (ψ (alphaCircle z)).1 = θ →
        mfderiv (𝓡 1) (𝓡 1) (fun z => (ψ (alphaCircle z)).1) z ≠ 0) ∧
      {z | (ψ (alphaCircle z)).1 = θ}.ncard + 2 = {z | (φ (alphaCircle z)).1 = θ}.ncard ∧
      ∃ Q : TDiff, IsotopicDiffeomorph torusRefl Q ∧ ψ = φ.trans Q ∧
        ∃ U : Set Torus, IsOpen U ∧ {p : Torus | p.2 = s} ⊆ U ∧ ∀ p ∈ U, Q p = p := by
  obtain ⟨Φ, hlift, hdeck⟩ := exists_lift_of_torusMatrix_eq_one φ h
  set γ : ℝ → ℝ × ℝ := fun t => Φ (t, 0) with hγdef
  have hΦc : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.mp Φ.contMDiff
  have hγs : ContDiff ℝ ∞ γ := hΦc.comp (contDiff_id.prodMk contDiff_const)
  have hfγ (t : ℝ) : φ (alphaCircle (cexp t)) = torusCover (γ t) := by
    rw [alphaCircle_cexp, hlift]
  set f : Circle → Torus := fun z => φ (alphaCircle z) with hfdef
  have hfc : Continuous f := φ.continuous.comp (continuous_id.prodMk continuous_const)
  have hxs : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z => (φ (alphaCircle z)).1) :=
    contMDiff_fst.comp (φ.contMDiff.comp contMDiff_alphaCircle)
  have hfx (t : ℝ) : (φ (alphaCircle (cexp t))).1 = cexp (γ t).1 := by
    rw [hfγ, torusCover_eq]
  have hfy (t : ℝ) : heightOnCircle φ (cexp t) = cexp (γ t).2 := by
    rw [heightOnCircle, hfγ, torusCover_eq]
  set σs := rep s with hσs
  have hne_int : ∀ t ∈ univ, ∀ n : ℤ, (fun t => (γ t).2 - σs) t ≠ n := by
    intro t _ n he
    apply hs (cexp t)
    rw [hfy, ← cexp_rep s, cexp_eq_cexp_iff]
    exact ⟨n, by simp only at he; linarith⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℤ, J = ⌊(γ 0).2 - σs⌋ := ⟨_, rfl⟩
  set lo := σs + J with hlodef
  have hlo : ∀ t, lo < (γ t).2 ∧ (γ t).2 < lo + 1 := fun t => by
    have := mem_Ioo_floor_of_ne_int (h := fun t => (γ t).2 - σs) isPreconnected_univ
      (hγs.continuous.snd.sub continuous_const).continuousOn hne_int (mem_univ 0) (mem_univ t)
    rw [← hJ] at this
    constructor <;> linarith [this.1, this.2]
  set θr := rep θ with hθr
  have htr : ∀ t (k : ℤ), (γ t).1 = θr + k → deriv (fun u => (γ u).1) t ≠ 0 := by
    intro t k hk
    refine deriv_lift_ne_zero hxs hγs.fst hfx (hθ _ ?_)
    rw [hfx, hk, cexp_add_int, cexp_rep]
  obtain ⟨g, σ, t₁, t₂, hgc, hgl, hσ, -, -, h12, hg1, hg2, hnoarc⟩ := harc
  have hgx (t : ℝ) : cexp (g t) = cexp ((fun u => (γ u).1) t) := (hgl t).symm.trans (hfx t)
  have hsub := sub_eq_of_cexp_eq hgc hγs.continuous.fst hgx t₁ t₂
  obtain ⟨k', hk'⟩ : ∃ k' : ℤ, σ = θr + k' := by
    have : cexp σ = cexp θr := by rw [hσ, cexp_rep]
    exact cexp_eq_cexp_iff.mp this
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℤ, g t₁ = (γ t₁).1 + n₁ := cexp_eq_cexp_iff.mp (hgx t₁)
  have h₁ : (γ t₁).1 = θr + ((k' - n₁ : ℤ) : ℝ) := by push_cast; linarith
  have h₂ : (γ t₂).1 = θr + ((k' - n₁ : ℤ) : ℝ) := by push_cast; linarith
  have hno : ∀ t ∈ Ioo t₁ t₂, ∀ j : ℤ, (γ t).1 ≠ θr + ((k' - n₁ : ℤ) : ℝ) + j := by
    intro t ht j he
    apply hnoarc t ht
    change (φ (alphaCircle (cexp t))).1 = θ
    rw [hfx, he, show θr + ((k' - n₁ : ℤ) : ℝ) + j = θr + ((k' - n₁ + j : ℤ) : ℝ) by
      push_cast; ring, cexp_add_int, cexp_rep]
  obtain ⟨τ, c, a, b, ε, N, hτ, hab, hε, ⟨k, hck⟩, ha, hb, hin, hout, hNo, hDN, hNc, hNlo,
    hsep, hempN⟩ := exists_annulus_bigon Φ hdeck γ (fun _ => rfl) hlo θr htr h12 h₁ h₂ hno
  have hcθ : cexp c = θ := by rw [hck, cexp_add_int, cexp_rep]
  have hdγ (t : ℝ) : HasDerivAt γ (fderiv ℝ Φ (t, 0) (1, 0)) t :=
    hasDerivAt_diffeomorph_horizontal Φ 0 t
  have hdγ1 (t : ℝ) : (deriv γ t).1 = deriv (fun u => (γ u).1) t := by
    rw [(hdγ t).deriv]
    exact ((hasDerivAt_fst_comp (hdγ t)).deriv).symm
  have himm (t : ℝ) : deriv γ t ≠ 0 := by
    rw [(hdγ t).deriv]
    intro h0
    have := fderiv_injective_of_diffeomorph Φ (t, 0) (h0.trans (map_zero _).symm)
    simp at this
  have hγinj : Function.Injective γ := fun t u he => congrArg Prod.fst (Φ.injective he)
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
  obtain ⟨Q, hQ, ⟨C, hCc, hCN, hQC, hQCC, hCcross⟩, hiff, h12', hf1, hf2⟩ :=
    exists_torus_bigon_push_vertical (f := f) hγs hfγ hτ hab hε ha hb hin hout
      (by rw [hdγ1]; exact htr a k (ha.trans hck))
      (by rw [hdγ1]; exact htr b k (hb.trans hck))
      (fun t _ => himm t) hγinj.injOn hNo hDN hNc hsep hemp
  rw [hcθ] at hiff hf1 hf2 hCcross
  have hCs : ∀ p ∈ C, p.2 ≠ s := by
    intro p hp hps
    obtain ⟨y, hy, rfl⟩ := hCN hp
    rw [torusCover_eq, ← cexp_rep s] at hps
    obtain ⟨n, hn⟩ := cexp_eq_cexp_iff.mp hps
    obtain ⟨h1, h2⟩ := hNlo y hy
    rw [hn] at h1 h2
    have h1' : J < n := by exact_mod_cast (show (J : ℝ) < n by linarith)
    have h2' : n < J + 1 := by exact_mod_cast (show (n : ℝ) < J + 1 by linarith)
    omega
  have hfin : {z | (φ (alphaCircle z)).1 = θ}.Finite := circle_finite_fiber_of_regular hxs hθ
  refine ⟨φ.trans Q, isotopicDiffeomorph_trans_of_refl φ hQ, fun z hz => ?_, fun z hz => ?_,
    ncard_add_two_of_forall_iff hfin h12' hf1 hf2 hiff, Q, hQ, rfl, Cᶜ,
    hCc.isClosed.isOpen_compl, fun p hp hpC => hCs p hpC hp, fun p hp => hQC p hp⟩
  · change (Q (f z)).2 = s at hz
    by_cases hzC : f z ∈ C
    · exact hCs _ (hQCC _ hzC) hz
    · rw [hQC _ hzC] at hz
      exact hs z hz
  · have hzC := hCcross z hz
    have hev : (fun z => ((φ.trans Q) (alphaCircle z)).1) =ᶠ[𝓝 z]
        (fun z => (φ (alphaCircle z)).1) :=
      (eventuallyEq_of_not_mem_support hCc hQC hfc hzC).fun_comp Prod.fst
    rw [hev.mfderiv_eq]
    exact hθ z ((hiff z).mp hz).1

theorem exists_isotopic_annulus_push (φ : TDiff) (h : torusMatrix φ = 1) (s : Circle)
    (hs : ∀ z, heightOnCircle φ z ≠ s) (θ : Circle)
    (hθ : ∀ z, (φ (alphaCircle z)).1 = θ →
      mfderiv (𝓡 1) (𝓡 1) (fun z => (φ (alphaCircle z)).1) z ≠ 0)
    (harc : HasSameSideArcIn (fun z => (φ (alphaCircle z)).1) θ univ) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ (∀ z, heightOnCircle ψ z ≠ s) ∧
      (∀ z, (ψ (alphaCircle z)).1 = θ →
        mfderiv (𝓡 1) (𝓡 1) (fun z => (ψ (alphaCircle z)).1) z ≠ 0) ∧
      {z | (ψ (alphaCircle z)).1 = θ}.ncard < {z | (φ (alphaCircle z)).1 = θ}.ncard := by
  obtain ⟨ψ, h1, h2, h3, h4, -⟩ := exists_isotopic_annulus_push_add_two φ h s hs θ hθ harc
  exact ⟨ψ, h1, h2, h3, by omega⟩

end GC.Seifert
