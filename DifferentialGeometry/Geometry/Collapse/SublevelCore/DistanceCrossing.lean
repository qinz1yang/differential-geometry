import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# LC34, first part: the distance crossing height `h_ρ`

Blueprint LC34 (master207A:21486), first paragraph of the proof. Along each coordinate curve
`u ↦ Φ (u - η y) y` of the LC33 product, the distance `d` from the base point increases with
slope at least `c > 0`; since `|η - d| < e` and `a + e ≤ ρ ≤ b - e`, it crosses the value `ρ`
exactly once, at a height `h_ρ(y) ∈ (a, b)` with `|h_ρ(y) - ρ| < e`. The height is constant on
flow lines and continuous on the band (lower-slope argument).

The statement is topological: `X` is any topological space, `η` and `d` are continuous, and `Φ`
is a jointly continuous flow with the band value property and the LC33 slope bound.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {X : Type*} [TopologicalSpace X]

/-- LC34, crossing height (kernel form). -/
theorem exists_distance_crossing_height {η d : X → ℝ} (hη : Continuous η) (hd : Continuous d)
    {Φ : ℝ → X → X} (hΦc : Continuous (fun q : ℝ × X => Φ q.1 q.2))
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x))
    {a b c e ρ : ℝ} (hval : ∀ y, η y ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η y) y) = s)
    (hc : 0 < c)
    (hslope : ∀ y, η y ∈ Icc a b → ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      c * (t - s) ≤ d (Φ (t - η y) y) - d (Φ (s - η y) y))
    (hclose : ∀ x, |η x - d x| < e) (hρa : a + e ≤ ρ) (hρb : ρ + e ≤ b) :
    ∃ hρ : X → ℝ, ContinuousOn hρ (η ⁻¹' Icc a b) ∧
      (∀ y, η y ∈ Icc a b → ∀ s, η y + s ∈ Icc a b → hρ (Φ s y) = hρ y) ∧
      ∀ y, η y ∈ Icc a b →
        hρ y ∈ Ioo a b ∧ |hρ y - ρ| < e ∧ d (Φ (hρ y - η y) y) = ρ ∧
        ∀ u ∈ Icc a b, (d (Φ (u - η y) y) ≤ ρ ↔ u ≤ hρ y) ∧
          (d (Φ (u - η y) y) < ρ ↔ u < hρ y) ∧ (d (Φ (u - η y) y) = ρ ↔ u = hρ y) := by
  classical
  let φ : X → ℝ → ℝ := fun y u => d (Φ (u - η y) y)
  have hφc : ∀ y, Continuous (φ y) := fun y =>
    hd.comp (hΦc.comp ((continuous_id.sub continuous_const).prodMk continuous_const))
  have hφa : ∀ y, η y ∈ Icc a b → φ y a < ρ := by
    intro y hy
    have hab : a ≤ b := hy.1.trans hy.2
    have h1 := hval y hy a ⟨le_rfl, hab⟩
    have h2 := abs_lt.mp (hclose (Φ (a - η y) y))
    rw [h1] at h2
    change d (Φ (a - η y) y) < ρ
    linarith [h2.1]
  have hφb : ∀ y, η y ∈ Icc a b → ρ < φ y b := by
    intro y hy
    have hab : a ≤ b := hy.1.trans hy.2
    have h1 := hval y hy b ⟨hab, le_rfl⟩
    have h2 := abs_lt.mp (hclose (Φ (b - η y) y))
    rw [h1] at h2
    change ρ < d (Φ (b - η y) y)
    linarith [h2.2]
  have hexists : ∀ y, η y ∈ Icc a b → ∃ u ∈ Icc a b, φ y u = ρ := by
    intro y hy
    have hab : a ≤ b := hy.1.trans hy.2
    exact intermediate_value_Icc hab (hφc y).continuousOn ⟨(hφa y hy).le, (hφb y hy).le⟩
  let hρ : X → ℝ := fun y =>
    if hy : η y ∈ Icc a b then Classical.choose (hexists y hy) else 0
  have hspec : ∀ y (hy : η y ∈ Icc a b), hρ y ∈ Icc a b ∧ φ y (hρ y) = ρ := by
    intro y hy
    have h := Classical.choose_spec (hexists y hy)
    simp only [hρ, dite_eq_left hy]
    exact h
  -- strict comparison along a coordinate curve
  have hlt : ∀ y, η y ∈ Icc a b → ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t → φ y s < φ y t := by
    intro y hy s hs t ht hst
    have := hslope y hy s t hs.1 hst.le ht.2
    change c * (t - s) ≤ φ y t - φ y s at this
    nlinarith
  have hiff : ∀ y, η y ∈ Icc a b → ∀ u ∈ Icc a b,
      (φ y u ≤ ρ ↔ u ≤ hρ y) ∧ (φ y u < ρ ↔ u < hρ y) ∧ (φ y u = ρ ↔ u = hρ y) := by
    intro y hy u hu
    obtain ⟨hmem, hcross⟩ := hspec y hy
    have hmono : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t ↔ φ y s ≤ φ y t := by
      intro s hs t ht
      constructor
      · intro hst
        rcases eq_or_lt_of_le hst with h | h
        · rw [h]
        · exact (hlt y hy s hs t ht h).le
      · intro hφ
        by_contra hts
        exact absurd hφ (not_le.mpr (hlt y hy t ht s hs (lt_of_not_ge hts)))
    have hmono' : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t ↔ φ y s < φ y t := by
      intro s hs t ht
      rw [← not_le, ← not_le, hmono t ht s hs]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hcross]; exact (hmono u hu _ hmem).symm
    · rw [← hcross]; exact (hmono' u hu _ hmem).symm
    · rw [← hcross]
      constructor
      · intro h
        exact le_antisymm ((hmono u hu _ hmem).mpr h.le) ((hmono _ hmem u hu).mpr h.ge)
      · intro h; rw [h]
  refine ⟨hρ, ?_, ?_, ?_⟩
  · -- continuity on the band (lower-slope argument)
    intro y₀ hy₀
    obtain ⟨hmem₀, hcross₀⟩ := hspec y₀ hy₀
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε' hε'
    set u₀ := hρ y₀ with hu₀
    have hcont : Continuous (fun y => φ y u₀) :=
      hd.comp (hΦc.comp ((continuous_const.sub hη).prodMk continuous_id))
    have hev : ∀ᶠ y in 𝓝 y₀, |φ y u₀ - ρ| < c * ε' := by
      have h2 : Tendsto (fun y => φ y u₀) (𝓝 y₀) (𝓝 ρ) := by
        have := hcont.continuousAt (x := y₀)
        rw [ContinuousAt, hcross₀] at this
        exact this
      have h3 := (Metric.tendsto_nhds.mp h2) (c * ε') (mul_pos hc hε')
      filter_upwards [h3] with y hy
      rwa [Real.dist_eq] at hy
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with y hy hyB
    obtain ⟨hmem, hcross⟩ := hspec y hyB
    rw [Real.dist_eq]
    have key : c * |hρ y - u₀| ≤ |φ y u₀ - ρ| := by
      rcases le_total u₀ (hρ y) with h | h
      · have h4 := hslope y hyB u₀ (hρ y) hmem₀.1 h hmem.2
        change c * (hρ y - u₀) ≤ φ y (hρ y) - φ y u₀ at h4
        rw [hcross] at h4
        rw [abs_of_nonneg (sub_nonneg.mpr h)]
        linarith [neg_abs_le (φ y u₀ - ρ)]
      · have h4 := hslope y hyB (hρ y) u₀ hmem.1 h hmem₀.2
        change c * (u₀ - hρ y) ≤ φ y u₀ - φ y (hρ y) at h4
        rw [hcross] at h4
        rw [abs_of_nonpos (sub_nonpos.mpr h)]
        linarith [le_abs_self (φ y u₀ - ρ)]
    by_contra hcon
    push Not at hcon
    have := mul_le_mul_of_nonneg_left hcon hc.le
    linarith
  · intro y hy s hs
    have hηs : η (Φ s y) = η y + s := by
      have h1 := hval y hy (η y + s) hs
      rwa [add_sub_cancel_left] at h1
    have hφeq : ∀ u, φ (Φ s y) u = φ y u := by
      intro u
      change d (Φ (u - η (Φ s y)) (Φ s y)) = d (Φ (u - η y) y)
      rw [hηs, ← hΦadd]
      congr 2
      ring
    have hyB' : η (Φ s y) ∈ Icc a b := by rw [hηs]; exact hs
    obtain ⟨hmem, hcross⟩ := hspec (Φ s y) hyB'
    rw [hφeq] at hcross
    exact (hiff y hy _ hmem).2.2.mp hcross
  · intro y hy
    obtain ⟨hmem, hcross⟩ := hspec y hy
    have hne_a : hρ y ≠ a := fun h => by
      have h1 := hφa y hy
      rw [← h] at h1
      exact absurd hcross (ne_of_lt h1)
    have hne_b : hρ y ≠ b := fun h => by
      have h1 := hφb y hy
      rw [← h] at h1
      exact absurd hcross (ne_of_gt h1)
    refine ⟨⟨lt_of_le_of_ne hmem.1 (Ne.symm hne_a), lt_of_le_of_ne hmem.2 hne_b⟩, ?_, hcross,
      fun u hu => hiff y hy u hu⟩
    have h1 := hval y hy (hρ y) hmem
    have h2 := hclose (Φ (hρ y - η y) y)
    rw [h1] at h2
    change |hρ y - φ y (hρ y)| < e at h2
    rwa [hcross] at h2

end DifferentialGeometry.Geometry.Collapse

namespace DifferentialGeometry.Geometry.Collapse

/-- The increasing piecewise affine map of LC34 fixing `a` and `b` and sending `ρ` to `k`. -/
def pwAffine (a b ρ k u : ℝ) : ℝ :=
  a + (k - a) / (ρ - a) * (min u ρ - a) + (b - k) / (b - ρ) * (max u ρ - ρ)

section PwAffine

variable {a b ρ k : ℝ}

theorem pwAffine_of_le {u : ℝ} (hu : u ≤ ρ) :
    pwAffine a b ρ k u = a + (k - a) / (ρ - a) * (u - a) := by
  simp only [pwAffine, min_eq_left hu, max_eq_right hu, sub_self, mul_zero, add_zero]

theorem pwAffine_of_ge (hρ : a < ρ) {u : ℝ} (hu : ρ ≤ u) :
    pwAffine a b ρ k u = k + (b - k) / (b - ρ) * (u - ρ) := by
  simp only [pwAffine, min_eq_right hu, max_eq_left hu]
  field_simp [(sub_pos.mpr hρ).ne']
  ring

theorem pwAffine_inv (hρa : a < ρ) (hρb : ρ < b) (hka : a < k) (hkb : k < b) (u : ℝ) :
    pwAffine a b k ρ (pwAffine a b ρ k u) = u := by
  rcases le_total u ρ with hu | hu
  · have hP : pwAffine a b ρ k u ≤ k := by
      rw [pwAffine_of_le hu]
      have h1 : (k - a) / (ρ - a) * (u - a) ≤ (k - a) / (ρ - a) * (ρ - a) := by
        rcases le_total a u with hau | hua
        · exact mul_le_mul_of_nonneg_left (by linarith)
            (div_nonneg (by linarith) (by linarith))
        · nlinarith [div_nonneg (sub_nonneg.mpr hka.le) (sub_nonneg.mpr hρa.le)]
      rw [div_mul_cancel₀ _ (sub_pos.mpr hρa).ne'] at h1
      linarith
    rw [pwAffine_of_le hP, pwAffine_of_le hu]
    field_simp [(sub_pos.mpr hρa).ne', (sub_pos.mpr hka).ne']
    ring
  · have hP : k ≤ pwAffine a b ρ k u := by
      rw [pwAffine_of_ge hρa hu]
      have : 0 ≤ (b - k) / (b - ρ) * (u - ρ) :=
        mul_nonneg (div_nonneg (by linarith) (by linarith)) (by linarith)
      linarith
    rw [pwAffine_of_ge hka hP, pwAffine_of_ge hρa hu]
    field_simp [(sub_pos.mpr hρb).ne', (sub_pos.mpr hkb).ne']
    ring

theorem strictMono_pwAffine (hρa : a < ρ) (hρb : ρ < b) (hka : a < k) (hkb : k < b) :
    StrictMono (pwAffine a b ρ k) := by
  intro u v huv
  have h1 : 0 < (k - a) / (ρ - a) := div_pos (by linarith) (by linarith)
  have h2 : 0 < (b - k) / (b - ρ) := div_pos (by linarith) (by linarith)
  simp only [pwAffine]
  rcases le_total u ρ with hu | hu <;> rcases le_total v ρ with hv | hv
  · rw [min_eq_left hu, min_eq_left hv, max_eq_right hu, max_eq_right hv]
    nlinarith
  · rw [min_eq_left hu, min_eq_right hv, max_eq_right hu, max_eq_left hv]
    rcases eq_or_lt_of_le hv with h | h
    · subst h; nlinarith
    · nlinarith
  · linarith
  · rw [min_eq_right hu, min_eq_right hv, max_eq_left hu, max_eq_left hv]
    nlinarith

theorem pwAffine_left (hρa : a < ρ) : pwAffine a b ρ k a = a := by
  rw [pwAffine_of_le hρa.le]; ring

theorem pwAffine_right (hρa : a < ρ) (hρb : ρ < b) : pwAffine a b ρ k b = b := by
  rw [pwAffine_of_ge hρa hρb.le]
  field_simp [(sub_pos.mpr hρb).ne']
  ring

theorem pwAffine_center (hρa : a < ρ) : pwAffine a b ρ k ρ = k := by
  rw [pwAffine_of_le le_rfl]
  field_simp [(sub_pos.mpr hρa).ne']
  ring

theorem pwAffine_mem_Icc (hρa : a < ρ) (hρb : ρ < b) (hka : a < k) (hkb : k < b) {u : ℝ}
    (hu : u ∈ Icc a b) : pwAffine a b ρ k u ∈ Icc a b := by
  have hm := (strictMono_pwAffine hρa hρb hka hkb).monotone
  constructor
  · have h1 := hm hu.1
    rwa [pwAffine_left hρa] at h1
  · have h1 := hm hu.2
    rwa [pwAffine_right hρa hρb] at h1

theorem abs_pwAffine_sub_le (hρa : a < ρ) (hρb : ρ < b) {u : ℝ} (hu : u ∈ Icc a b) :
    |pwAffine a b ρ k u - u| ≤ |k - ρ| := by
  rcases le_total u ρ with h | h
  · rw [pwAffine_of_le h]
    have hid : a + (k - a) / (ρ - a) * (u - a) - u = (k - ρ) * ((u - a) / (ρ - a)) := by
      field_simp [(sub_pos.mpr hρa).ne']
      ring
    rw [hid, abs_mul]
    have h1 : |(u - a) / (ρ - a)| ≤ 1 := by
      rw [abs_le]
      constructor
      · have := div_nonneg (sub_nonneg.mpr hu.1) (sub_pos.mpr hρa).le; linarith
      · rw [div_le_one (sub_pos.mpr hρa)]; linarith
    calc |k - ρ| * |(u - a) / (ρ - a)| ≤ |k - ρ| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |k - ρ| := mul_one _
  · rw [pwAffine_of_ge hρa h]
    have hid : k + (b - k) / (b - ρ) * (u - ρ) - u = (k - ρ) * ((b - u) / (b - ρ)) := by
      field_simp [(sub_pos.mpr hρb).ne']
      ring
    rw [hid, abs_mul]
    have h1 : |(b - u) / (b - ρ)| ≤ 1 := by
      rw [abs_le]
      constructor
      · have := div_nonneg (sub_nonneg.mpr hu.2) (sub_pos.mpr hρb).le; linarith
      · rw [div_le_one (sub_pos.mpr hρb)]; linarith
    calc |k - ρ| * |(b - u) / (b - ρ)| ≤ |k - ρ| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |k - ρ| := mul_one _

end PwAffine

end DifferentialGeometry.Geometry.Collapse

namespace DifferentialGeometry.Geometry.Collapse

variable {X : Type*} [TopologicalSpace X]

/-- LC34 (kernel form): a continuous isotopy of homeomorphisms, the identity where `η ∉ (a, b)`,
moving every point along its own flow line by less than `e` in time (inside the band when it
starts there), whose time-one map carries
the radial sublevel `{η ≤ ρ}` onto the distance ball `{d ≤ ρ}`, the level onto the distance
sphere and the strict sublevel onto the open ball. -/
theorem exists_distance_sublevel_isotopy {η d : X → ℝ} (hη : Continuous η) (hd : Continuous d)
    {Φ : ℝ → X → X} (hΦc : Continuous (fun q : ℝ × X => Φ q.1 q.2))
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x)) (hΦ0 : ∀ x, Φ 0 x = x)
    {a b c e ρ : ℝ} (hval : ∀ y, η y ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η y) y) = s)
    (hc : 0 < c)
    (hslope : ∀ y, η y ∈ Icc a b → ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      c * (t - s) ≤ d (Φ (t - η y) y) - d (Φ (s - η y) y))
    (hclose : ∀ x, |η x - d x| < e) (hρa : a + e ≤ ρ) (hρb : ρ + e ≤ b) :
    ∃ H : ℝ → X ≃ₜ X,
      Continuous (fun q : ℝ × X => H q.1 q.2) ∧
      Continuous (fun q : ℝ × X => (H q.1).symm q.2) ∧
      (∀ x, H 0 x = x) ∧ (∀ t x, η x ∉ Ioo a b → H t x = x) ∧
      (∀ t x, ∃ s, |s| < e ∧ H t x = Φ s x ∧ (η x ∈ Icc a b → η x + s ∈ Icc a b)) ∧
      H 1 '' {x | η x ≤ ρ} = {x | d x ≤ ρ} ∧ H 1 '' {x | η x = ρ} = {x | d x = ρ} ∧
      H 1 '' {x | η x < ρ} = {x | d x < ρ} := by
  classical
  obtain ⟨hρ, hρc, hρinv, hρspec⟩ :=
    exists_distance_crossing_height hη hd hΦc hΦadd hval hc hslope hclose hρa hρb
  -- elementary consequences
  have he : ∀ x : X, 0 < e := fun x => lt_of_le_of_lt (abs_nonneg _) (hclose x)
  have hab : ∀ x : X, a < ρ ∧ ρ < b := fun x => ⟨by linarith [he x], by linarith [he x]⟩
  let lam : ℝ → ℝ := fun t => max 0 (min t 1)
  have hlam : ∀ t, 0 ≤ lam t ∧ lam t ≤ 1 := fun t =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hlamc : Continuous lam := continuous_const.max (continuous_id.min continuous_const)
  let k : ℝ → X → ℝ := fun t y => (1 - lam t) * ρ + lam t * hρ y
  have hkI : ∀ t y, η y ∈ Icc a b → a < k t y ∧ k t y < b := by
    intro t y hy
    obtain ⟨h1, h2⟩ := (hρspec y hy).1
    obtain ⟨l0, l1⟩ := hlam t
    obtain ⟨ha, hb⟩ := hab y
    change a < (1 - lam t) * ρ + lam t * hρ y ∧ (1 - lam t) * ρ + lam t * hρ y < b
    set m₁ := min (ρ - a) (hρ y - a)
    set m₂ := min (b - ρ) (b - hρ y)
    have hm₁ : 0 < m₁ := lt_min (by linarith) (by linarith)
    have hm₂ : 0 < m₂ := lt_min (by linarith) (by linarith)
    have e1 : (1 - lam t) * m₁ ≤ (1 - lam t) * (ρ - a) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
    have e2 : lam t * m₁ ≤ lam t * (hρ y - a) := mul_le_mul_of_nonneg_left (min_le_right _ _) l0
    have e3 : (1 - lam t) * m₂ ≤ (1 - lam t) * (b - ρ) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
    have e4 : lam t * m₂ ≤ lam t * (b - hρ y) := mul_le_mul_of_nonneg_left (min_le_right _ _) l0
    constructor <;> nlinarith
  let S : Set (ℝ × X) := {q | η q.2 ∈ Icc a b}
  have hSc : IsClosed S := isClosed_Icc.preimage (hη.comp continuous_snd)
  have hlamS : ContinuousOn (fun q : ℝ × X => lam q.1) S := (hlamc.comp continuous_fst).continuousOn
  have hρS : ContinuousOn (fun q : ℝ × X => hρ q.2) S :=
    hρc.comp continuous_snd.continuousOn (fun q hq => hq)
  have hkc : ContinuousOn (fun q : ℝ × X => k q.1 q.2) S :=
    ((continuousOn_const.sub hlamS).mul continuousOn_const).add (hlamS.mul hρS)
  have hminOn : ∀ {f g : ℝ × X → ℝ}, ContinuousOn f S → ContinuousOn g S →
      ContinuousOn (fun q => min (f q) (g q)) S := fun hf hg =>
    continuous_min.comp_continuousOn (hf.prodMk hg)
  have hmaxOn : ∀ {f g : ℝ × X → ℝ}, ContinuousOn f S → ContinuousOn g S →
      ContinuousOn (fun q => max (f q) (g q)) S := fun hf hg =>
    continuous_max.comp_continuousOn (hf.prodMk hg)
  have hfront : ∀ q ∈ frontier S, η q.2 = a ∨ η q.2 = b := by
    intro q hq
    have hqS : η q.2 ∈ Icc a b := hSc.frontier_subset hq
    by_contra hne
    push Not at hne
    have hIoo : η q.2 ∈ Ioo a b := ⟨lt_of_le_of_ne hqS.1 (Ne.symm hne.1),
      lt_of_le_of_ne hqS.2 hne.2⟩
    have hopen : IsOpen {q : ℝ × X | η q.2 ∈ Ioo a b} := isOpen_Ioo.preimage (hη.comp continuous_snd)
    exact hq.2 (interior_maximal (s := S) (t := {q : ℝ × X | η q.2 ∈ Ioo a b})
      (fun r hr => Ioo_subset_Icc_self hr) hopen hIoo)
  -- the displacement times
  let τ : ℝ × X → ℝ := fun q =>
    if η q.2 ∈ Icc a b then pwAffine a b ρ (k q.1 q.2) (η q.2) - η q.2 else 0
  let τ' : ℝ × X → ℝ := fun q =>
    if η q.2 ∈ Icc a b then pwAffine a b (k q.1 q.2) ρ (η q.2) - η q.2 else 0
  have hτc : Continuous τ := by
    apply continuous_if
    · intro q hq
      rcases hfront q hq with h | h
      · rw [h, pwAffine_left (hab q.2).1, sub_self]
      · rw [h, pwAffine_right (hab q.2).1 (hab q.2).2, sub_self]
    · rw [hSc.closure_eq]
      have hu : ContinuousOn (fun q : ℝ × X => η q.2) S := (hη.comp continuous_snd).continuousOn
      have h1 : ContinuousOn (fun q : ℝ × X => (k q.1 q.2 - a) / (ρ - a)) S :=
        (hkc.sub continuousOn_const).div_const _
      have h2 : ContinuousOn (fun q : ℝ × X => min (η q.2) ρ - a) S :=
        (hminOn (f := fun q => η q.2) (g := fun _ => ρ) hu continuousOn_const).sub
          continuousOn_const
      have h3 : ContinuousOn (fun q : ℝ × X => (b - k q.1 q.2) / (b - ρ)) S :=
        (continuousOn_const.sub hkc).div_const _
      have h4 : ContinuousOn (fun q : ℝ × X => max (η q.2) ρ - ρ) S :=
        (hmaxOn (f := fun q => η q.2) (g := fun _ => ρ) hu continuousOn_const).sub
          continuousOn_const
      exact ((continuousOn_const.add (h1.mul h2)).add (h3.mul h4)).sub hu
    · exact continuousOn_const
  have hτ'c : Continuous τ' := by
    apply continuous_if
    · intro q hq
      have hqS : η q.2 ∈ Icc a b := hSc.frontier_subset hq
      have hk := hkI q.1 q.2 hqS
      rcases hfront q hq with h | h
      · rw [h, pwAffine_left hk.1, sub_self]
      · rw [h, pwAffine_right hk.1 hk.2, sub_self]
    · rw [hSc.closure_eq]
      have hu : ContinuousOn (fun q : ℝ × X => η q.2) S := (hη.comp continuous_snd).continuousOn
      have h1 : ContinuousOn (fun q : ℝ × X => (ρ - a) / (k q.1 q.2 - a)) S :=
        continuousOn_const.div (hkc.sub continuousOn_const)
          (fun q hq => (sub_pos.mpr (hkI q.1 q.2 hq).1).ne')
      have h2 : ContinuousOn (fun q : ℝ × X => min (η q.2) (k q.1 q.2) - a) S :=
        (hminOn (f := fun q => η q.2) (g := fun q => k q.1 q.2) hu hkc).sub continuousOn_const
      have h3 : ContinuousOn (fun q : ℝ × X => (b - ρ) / (b - k q.1 q.2)) S :=
        continuousOn_const.div (continuousOn_const.sub hkc)
          (fun q hq => (sub_pos.mpr (hkI q.1 q.2 hq).2).ne')
      have h4 : ContinuousOn (fun q : ℝ × X => max (η q.2) (k q.1 q.2) - k q.1 q.2) S :=
        (hmaxOn (f := fun q => η q.2) (g := fun q => k q.1 q.2) hu hkc).sub hkc
      exact ((continuousOn_const.add (h1.mul h2)).add (h3.mul h4)).sub hu
    · exact continuousOn_const
  let H0 : ℝ → X → X := fun t y => Φ (τ (t, y)) y
  let H1 : ℝ → X → X := fun t y => Φ (τ' (t, y)) y
  have hH0c : Continuous (fun q : ℝ × X => H0 q.1 q.2) :=
    hΦc.comp (hτc.prodMk continuous_snd)
  have hH1c : Continuous (fun q : ℝ × X => H1 q.1 q.2) :=
    hΦc.comp (hτ'c.prodMk continuous_snd)
  -- behaviour on the band
  have hshift : ∀ y, η y ∈ Icc a b → ∀ s, η y + s ∈ Icc a b → η (Φ s y) = η y + s := by
    intro y hy s hs
    have h1 := hval y hy (η y + s) hs
    rwa [add_sub_cancel_left] at h1
  have hout : ∀ t y, η y ∉ Icc a b → H0 t y = y ∧ H1 t y = y := by
    intro t y hy
    constructor
    · change Φ (if η y ∈ Icc a b then _ else 0) y = y
      simp only [hy, ite_false, hΦ0]
    · change Φ (if η y ∈ Icc a b then _ else 0) y = y
      simp only [hy, ite_false, hΦ0]
  have hin0 : ∀ t y, η y ∈ Icc a b →
      H0 t y = Φ (pwAffine a b ρ (k t y) (η y) - η y) y := by
    intro t y hy
    change Φ (if η y ∈ Icc a b then _ else 0) y = _
    simp only [hy, ite_true]
  have hin1 : ∀ t y, η y ∈ Icc a b →
      H1 t y = Φ (pwAffine a b (k t y) ρ (η y) - η y) y := by
    intro t y hy
    change Φ (if η y ∈ Icc a b then _ else 0) y = _
    simp only [hy, ite_true]
  have hmove : ∀ y, η y ∈ Icc a b → ∀ w ∈ Icc a b,
      η (Φ (w - η y) y) = w ∧ hρ (Φ (w - η y) y) = hρ y := by
    intro y hy w hw
    have hs : η y + (w - η y) ∈ Icc a b := by rw [add_sub_cancel]; exact hw
    refine ⟨?_, hρinv y hy _ hs⟩
    rw [hshift y hy _ hs, add_sub_cancel]
  have hcompose : ∀ y w w', Φ (w' - w) (Φ (w - η y) y) = Φ (w' - η y) y := by
    intro y w w'
    rw [← hΦadd]
    congr 1
    ring
  have hleft : ∀ t y, H1 t (H0 t y) = y := by
    intro t y
    by_cases hy : η y ∈ Icc a b
    · have hk := hkI t y hy
      set P := pwAffine a b ρ (k t y) (η y) with hP
      have hPI : P ∈ Icc a b := pwAffine_mem_Icc (hab y).1 (hab y).2 hk.1 hk.2 hy
      obtain ⟨hηP, hρP⟩ := hmove y hy P hPI
      rw [hin0 t y hy]
      have hyP : η (Φ (P - η y) y) ∈ Icc a b := by rw [hηP]; exact hPI
      rw [hin1 t _ hyP]
      have hkk : k t (Φ (P - η y) y) = k t y := by
        change (1 - lam t) * ρ + lam t * hρ _ = (1 - lam t) * ρ + lam t * hρ y
        rw [hρP]
      rw [hkk, hηP, hcompose, pwAffine_inv (hab y).1 (hab y).2 hk.1 hk.2, sub_self, hΦ0]
    · rw [(hout t y hy).1, (hout t y hy).2]
  have hright : ∀ t y, H0 t (H1 t y) = y := by
    intro t y
    by_cases hy : η y ∈ Icc a b
    · have hk := hkI t y hy
      set Q := pwAffine a b (k t y) ρ (η y) with hQ
      have hQI : Q ∈ Icc a b := pwAffine_mem_Icc hk.1 hk.2 (hab y).1 (hab y).2 hy
      obtain ⟨hηQ, hρQ⟩ := hmove y hy Q hQI
      rw [hin1 t y hy]
      have hyQ : η (Φ (Q - η y) y) ∈ Icc a b := by rw [hηQ]; exact hQI
      rw [hin0 t _ hyQ]
      have hkk : k t (Φ (Q - η y) y) = k t y := by
        change (1 - lam t) * ρ + lam t * hρ _ = (1 - lam t) * ρ + lam t * hρ y
        rw [hρQ]
      rw [hkk, hηQ, hcompose, pwAffine_inv hk.1 hk.2 (hab y).1 (hab y).2, sub_self, hΦ0]
    · rw [(hout t y hy).2, (hout t y hy).1]
  let H : ℝ → X ≃ₜ X := fun t =>
    { toFun := H0 t
      invFun := H1 t
      left_inv := hleft t
      right_inv := hright t
      continuous_toFun := hH0c.comp (continuous_const.prodMk continuous_id)
      continuous_invFun := hH1c.comp (continuous_const.prodMk continuous_id) }
  -- the time-one map
  have hk1 : ∀ y, k 1 y = hρ y := by
    intro y
    change (1 - max 0 (min 1 1)) * ρ + max 0 (min 1 1) * hρ y = hρ y
    norm_num
  have hkey : ∀ y, (η y ≤ ρ ↔ d (H0 1 y) ≤ ρ) ∧ (η y = ρ ↔ d (H0 1 y) = ρ) ∧
      (η y < ρ ↔ d (H0 1 y) < ρ) := by
    intro y
    obtain ⟨ha, hb⟩ := hab y
    by_cases hy : η y ∈ Icc a b
    · have hk := hkI 1 y hy
      rw [hk1] at hk
      have hm := strictMono_pwAffine ha hb hk.1 hk.2
      have hPI := pwAffine_mem_Icc ha hb hk.1 hk.2 hy
      obtain ⟨-, -, -, hiff⟩ := hρspec y hy
      obtain ⟨hle, hlt, heq⟩ := hiff _ hPI
      rw [hin0 1 y hy, hk1]
      have hc' := pwAffine_center (b := b) (k := hρ y) ha
      have k1 := hm.le_iff_le (a := η y) (b := ρ)
      have k2 := hm.injective.eq_iff (a := η y) (b := ρ)
      have k3 := hm.lt_iff_lt (a := η y) (b := ρ)
      rw [hc'] at k1 k2 k3
      refine ⟨?_, ?_, ?_⟩
      · rw [hle]; exact k1.symm
      · rw [heq]; exact k2.symm
      · rw [hlt]; exact k3.symm
    · rw [(hout 1 y hy).1]
      have hcl := abs_lt.mp (hclose y)
      rcases not_and_or.mp hy with h | h
      · have h' : η y < a := lt_of_not_ge h
        refine ⟨⟨fun _ => by linarith, fun _ => by linarith⟩, ⟨fun h2 => by linarith,
          fun h2 => by linarith⟩, ⟨fun _ => by linarith, fun _ => by linarith⟩⟩
      · have h' : b < η y := lt_of_not_ge h
        refine ⟨⟨fun h2 => by linarith, fun h2 => by linarith⟩, ⟨fun h2 => by linarith,
          fun h2 => by linarith⟩, ⟨fun h2 => by linarith, fun h2 => by linarith⟩⟩
  have himage : ∀ (A B : Set X), (∀ y, y ∈ A ↔ H0 1 y ∈ B) → H 1 '' A = B := by
    intro A B hAB
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hAB y).mp hy
    · intro hz
      refine ⟨H1 1 z, (hAB _).mpr ?_, hright 1 z⟩
      rw [hright]
      exact hz
  refine ⟨H, hH0c, hH1c, ?_, ?_, ?_, himage _ _ fun y => (hkey y).1,
    himage _ _ fun y => (hkey y).2.1, himage _ _ fun y => (hkey y).2.2⟩
  · intro x
    change H0 0 x = x
    by_cases hy : η x ∈ Icc a b
    · rw [hin0 0 x hy]
      have hk0 : k 0 x = ρ := by
        change (1 - max 0 (min 0 1)) * ρ + max 0 (min 0 1) * hρ x = ρ
        norm_num
      rw [hk0]
      have hid : pwAffine a b ρ ρ (η x) = η x := by
        obtain ⟨ha, hb⟩ := hab x
        have := pwAffine_inv ha hb ha hb (η x)
        rcases le_total (η x) ρ with h | h
        · rw [pwAffine_of_le h]
          field_simp [(sub_pos.mpr ha).ne']
          ring
        · rw [pwAffine_of_ge ha h]
          field_simp [(sub_pos.mpr hb).ne']
          ring
      rw [hid, sub_self, hΦ0]
    · exact (hout 0 x hy).1
  · intro t x hx
    change H0 t x = x
    by_cases hy : η x ∈ Icc a b
    · have hab' : η x = a ∨ η x = b := by
        by_contra hne
        push Not at hne
        exact hx ⟨lt_of_le_of_ne hy.1 (Ne.symm hne.1), lt_of_le_of_ne hy.2 hne.2⟩
      have hk := hkI t x hy
      rw [hin0 t x hy]
      rcases hab' with h | h
      · rw [h, pwAffine_left (hab x).1, sub_self, hΦ0]
      · rw [h, pwAffine_right (hab x).1 (hab x).2, sub_self, hΦ0]
    · exact (hout t x hy).1
  · intro t x
    by_cases hy : η x ∈ Icc a b
    · refine ⟨pwAffine a b ρ (k t x) (η x) - η x, ?_, hin0 t x hy, fun _ => ?_⟩
      swap
      · rw [add_sub_cancel]
        exact pwAffine_mem_Icc (hab x).1 (hab x).2 (hkI t x hy).1 (hkI t x hy).2 hy
      have h1 := abs_pwAffine_sub_le (k := k t x) (hab x).1 (hab x).2 hy
      have h2 : |k t x - ρ| ≤ |hρ x - ρ| := by
        have : k t x - ρ = lam t * (hρ x - ρ) := by
          change (1 - lam t) * ρ + lam t * hρ x - ρ = _
          ring
        rw [this, abs_mul, abs_of_nonneg (hlam t).1]
        exact mul_le_of_le_one_left (abs_nonneg _) (hlam t).2
      exact lt_of_le_of_lt (h1.trans h2) (hρspec x hy).2.1
    · refine ⟨0, by rw [abs_zero]; exact he x, ?_, fun h => absurd h hy⟩
      change H0 t x = Φ 0 x
      rw [(hout t x hy).1, hΦ0]

end DifferentialGeometry.Geometry.Collapse
