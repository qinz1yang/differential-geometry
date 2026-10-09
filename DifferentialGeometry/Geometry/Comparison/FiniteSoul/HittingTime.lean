import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import DifferentialGeometry.Analysis.Calculus.DistanceSmoothing.SeminormMollification

/-!
# S-HIT: hitting times of a continuous function along a flow with a positive rate

Package CM-S (finite soul), lane CMS-H. Design `docs/geometrization/chapter13/design-finite-soul-20261004.md`
§4.2 "S-HIT"; blueprint master207A LFR23 proof (A:26796–26806: "distance strictly increases along
the field, with lower rate 3/4 … The hitting time is unique and continuous … the entire band is its
product with an interval") and LFR46 proof (A:28948–28958: unique backward crossing of
`{d_S = ℓ}` from every point with `d_S ≥ ℓ`). This is the continuous-`η` companion of LC46
(`exists_field_band_product_of_contMDiffOn`, SublevelCore/FieldBand.lean), which needs `η` smooth.

Data: a jointly continuous flow `Φ` on a topological space `X` (`Φ 0 = id`,
`Φ (s + t) = Φ s ∘ Φ t`), a continuous `η : X → ℝ`, an OPEN set `U` containing the band
`η⁻¹[a, b]`, and the integrated rate `η (Φ t x) ≥ η x + κ t` along every orbit segment `[0, t]` that
stays in `U` (`κ > 0`). The Dini form is converted by `rate_of_eventually`.

Truth check (deviation from the design's wording "rate on `η⁻¹[a, b]`"): a rate condition on the
CLOSED band alone does not give backward hitting. If `η (Φ t x) = b + |t|` near a point `x` of the
top level, every orbit segment starting in the band leaves it at once, so the closed-band condition
holds vacuously there, yet the orbit of `x` never returns to level `a` backwards. An open `U ⊇ band`
is exactly what the consumers have (the field is outward on a neighbourhood of the band).

* `hittingTime Φ η x s`: the time `t` at which the orbit of `x` reaches level `s`, crossing only the
  levels between `η x` and `s` (band-free definition).
* `exists_hittingTime_band_product`: continuity of the hitting time on `η⁻¹[a, b] × [a, b]` and
  `{η = c} × [a, b] ≃ₜ {a ≤ η ≤ b}` with LC46's formulas.
* `exists_hittingTime_halfBand_product`: the half-infinite version
  `{η = c} × [a, ∞) ≃ₜ {η ≥ a}` (rates `κ_b` on neighbourhoods of each compact band `[a, b]`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {X : Type*}

/-- **The hitting time** of level `s` from `x` along `Φ`: a time `t` with `η (Φ t x) = s` such that
the orbit between times `0` and `t` only crosses levels between `η x` and `s`; `0` if there is
none. Under a positive rate on a neighbourhood of the band it is unique
(`hittingTime_eq_of_forall_mem`). -/
def hittingTime (Φ : ℝ → X → X) (η : X → ℝ) (x : X) (s : ℝ) : ℝ :=
  open Classical in
  if h : ∃ t : ℝ, η (Φ t x) = s ∧ ∀ u ∈ uIcc 0 t, η (Φ u x) ∈ uIcc (η x) s then h.choose else 0

/-- `Φ (-t) ∘ Φ t = id`. -/
theorem flow_neg_apply_flow {Φ : ℝ → X → X} (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)) (t : ℝ) (x : X) : Φ (-t) (Φ t x) = x := by
  rw [← hΦadd, neg_add_cancel, hΦ0]

/-- **The rate on any orbit interval** inside `U`. -/
theorem add_mul_le_of_forall_mem_Icc {Φ : ℝ → X → X}
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)) {η : X → ℝ} {U : Set X} {κ : ℝ}
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) (hU : ∀ u ∈ Icc t₁ t₂, Φ u x ∈ U) :
    η (Φ t₁ x) + κ * (t₂ - t₁) ≤ η (Φ t₂ x) := by
  have h := hrate (Φ t₁ x) (t₂ - t₁) (sub_nonneg.mpr h12) (fun s hs => by
    rw [← hΦadd]
    exact hU (s + t₁) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  rwa [← hΦadd, sub_add_cancel] at h

/-- Along an orbit interval inside `U`, `η` is monotone. -/
theorem le_and_le_of_forall_mem_Icc {Φ : ℝ → X → X}
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)) {η : X → ℝ} {U : Set X} {κ : ℝ}
    (hκ : 0 < κ)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} {t₁ t₂ : ℝ} (hU : ∀ u ∈ Icc t₁ t₂, Φ u x ∈ U) {u : ℝ} (hu : u ∈ Icc t₁ t₂) :
    η (Φ t₁ x) ≤ η (Φ u x) ∧ η (Φ u x) ≤ η (Φ t₂ x) := by
  have h1 := add_mul_le_of_forall_mem_Icc hΦadd hrate hu.1
    (fun v hv => hU v ⟨hv.1, hv.2.trans hu.2⟩)
  have h2 := add_mul_le_of_forall_mem_Icc hΦadd hrate hu.2
    (fun v hv => hU v ⟨hu.1.trans hv.1, hv.2⟩)
  constructor
  · nlinarith [sub_nonneg.mpr hu.1]
  · nlinarith [sub_nonneg.mpr hu.2]

/-- **Uniqueness of crossing times** on an orbit interval inside `U`. -/
theorem eq_of_forall_mem_uIcc {Φ : ℝ → X → X}
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)) {η : X → ℝ} {U : Set X} {κ : ℝ}
    (hκ : 0 < κ)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} {t t' : ℝ} (hU : ∀ u ∈ uIcc t t', Φ u x ∈ U) (heq : η (Φ t x) = η (Φ t' x)) :
    t = t' := by
  rcases le_total t t' with h | h
  · have hr := add_mul_le_of_forall_mem_Icc hΦadd hrate h
      (fun u hu => hU u (by rwa [uIcc_of_le h]))
    have : κ * (t' - t) ≤ 0 := by linarith
    have : t' - t ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      linarith [mul_pos hκ hc]
    linarith
  · have hr := add_mul_le_of_forall_mem_Icc hΦadd hrate h
      (fun u hu => hU u (by rwa [uIcc_of_ge h]))
    have : κ * (t - t') ≤ 0 := by linarith
    have : t - t' ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      linarith [mul_pos hκ hc]
    linarith

/-- An open set containing a compact interval contains a uniform thickening of it. -/
theorem exists_pos_Icc_sub_add_subset {W : Set ℝ} (hW : IsOpen W) {m M : ℝ}
    (h : Icc m M ⊆ W) (hmM : m ≤ M) : ∃ δ > 0, Icc (m - δ) (M + δ) ⊆ W := by
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.isOpen_iff.mp hW m (h ⟨le_rfl, hmM⟩)
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.isOpen_iff.mp hW M (h ⟨hmM, le_rfl⟩)
  refine ⟨min ε₁ ε₂ / 2, by positivity, fun u hu => ?_⟩
  have hm1 : min ε₁ ε₂ ≤ ε₁ := min_le_left _ _
  have hm2 : min ε₁ ε₂ ≤ ε₂ := min_le_right _ _
  rcases lt_or_ge u m with hum | hum
  · apply h₁
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
    linarith [hu.1]
  · rcases le_or_gt u M with huM | huM
    · exact h ⟨hum, huM⟩
    · apply h₂
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      linarith [hu.2]

variable [TopologicalSpace X]

section Band

variable {Φ : ℝ → X → X} {η : X → ℝ} {U : Set X} {a b κ : ℝ}

/-- **Forward crossing.** From a point of the band, every higher level `s ≤ b` is reached in
forward time, the orbit staying in the band meanwhile. -/
theorem exists_forward_crossing (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hη : Continuous η) (hU : IsOpen U) (hκ : 0 < κ) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} (hx : η x ∈ Icc a b) {s : ℝ} (hxs : η x ≤ s) (hsb : s ≤ b) :
    ∃ t, 0 ≤ t ∧ (∀ u ∈ Icc 0 t, η (Φ u x) ∈ Icc a b) ∧ η (Φ t x) = s := by
  have hΦx : Continuous (fun u : ℝ => Φ u x) := hΦ.comp (continuous_id.prodMk continuous_const)
  have hf : Continuous (fun u : ℝ => η (Φ u x)) := hη.comp hΦx
  set L : Set ℝ := {t | 0 ≤ t ∧ ∀ u ∈ Icc 0 t, η (Φ u x) ∈ Icc a b} with hL
  have h0L : (0 : ℝ) ∈ L := ⟨le_rfl, fun u hu => by
    obtain rfl : u = 0 := le_antisymm hu.2 hu.1
    rw [hΦ0]; exact hx⟩
  have hbdd : BddAbove L := by
    refine ⟨(b - a) / κ, fun t ht => ?_⟩
    have hr := add_mul_le_of_forall_mem_Icc hΦadd hrate ht.1 (fun u hu => hbandU (ht.2 u hu))
    rw [hΦ0, sub_zero] at hr
    have hb' := (ht.2 t ⟨ht.1, le_rfl⟩).2
    rw [le_div_iff₀ hκ]
    linarith [hx.1]
  set β := sSup L with hβ
  have hβ0 : 0 ≤ β := le_csSup hbdd h0L
  have hβL : ∀ u ∈ Icc 0 β, η (Φ u x) ∈ Icc a b := by
    have hC : IsClosed {u : ℝ | η (Φ u x) ∈ Icc a b} := isClosed_Icc.preimage hf
    have hIco : Ico 0 β ⊆ {u : ℝ | η (Φ u x) ∈ Icc a b} := by
      intro u hu
      obtain ⟨t, htL, hut⟩ := exists_lt_of_lt_csSup ⟨0, h0L⟩ hu.2
      exact htL.2 u ⟨hu.1, hut.le⟩
    rcases eq_or_lt_of_le hβ0 with hβ0' | hβ0'
    · intro u hu
      obtain rfl : u = 0 := le_antisymm (hu.2.trans hβ0'.symm.le) hu.1
      rw [hΦ0]; exact hx
    · intro u hu
      have hcl : Icc 0 β ⊆ closure (Ico 0 β) := by rw [closure_Ico hβ0'.ne]
      exact closure_minimal hIco hC (hcl hu)
  have hβs : s ≤ η (Φ β x) := by
    by_contra hlt
    rw [not_le] at hlt
    have hβU : Φ β x ∈ U := hbandU (hβL β ⟨hβ0, le_rfl⟩)
    have hev1 : ∀ᶠ u in 𝓝 β, Φ u x ∈ U := hΦx.continuousAt.preimage_mem_nhds (hU.mem_nhds hβU)
    have hev : ∀ᶠ u in 𝓝 β, Φ u x ∈ U ∧ η (Φ u x) < b :=
      hev1.and ((hf.continuousAt.tendsto).eventually (Iio_mem_nhds (hlt.trans_le hsb)))
    obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp hev
    have hmem : β + ε / 2 ∈ L := by
      refine ⟨by linarith, fun u hu => ?_⟩
      rcases le_or_gt u β with h | h
      · exact hβL u ⟨hu.1, h⟩
      · have hdist : ∀ v ∈ Icc β u, dist v β < ε := fun v hv => by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hv.1])]
          linarith [hv.2, hu.2]
        have hr := add_mul_le_of_forall_mem_Icc hΦadd hrate h.le
          (fun v hv => (hεP (hdist v hv)).1)
        have hβa := (hβL β ⟨hβ0, le_rfl⟩).1
        refine ⟨?_, (hεP (hdist u ⟨h.le, le_rfl⟩)).2.le⟩
        nlinarith [sub_nonneg.mpr h.le]
    have := le_csSup hbdd hmem
    linarith
  have hIVT := intermediate_value_Icc hβ0 hf.continuousOn
  obtain ⟨t, ht, hft⟩ := hIVT ⟨by rw [hΦ0]; exact hxs, hβs⟩
  exact ⟨t, ht.1, fun u hu => hβL u ⟨hu.1, hu.2.trans ht.2⟩, hft⟩

/-- **Crossings in both directions**, in the form used by `hittingTime`. -/
theorem exists_crossing (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hη : Continuous η) (hU : IsOpen U) (hκ : 0 < κ) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} (hx : η x ∈ Icc a b) {s : ℝ} (hs : s ∈ Icc a b) :
    ∃ t : ℝ, η (Φ t x) = s ∧ ∀ u ∈ uIcc 0 t, η (Φ u x) ∈ uIcc (η x) s := by
  rcases le_total (η x) s with hxs | hsx
  · obtain ⟨t, ht0, hband, hts⟩ :=
      exists_forward_crossing hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hxs hs.2
    refine ⟨t, hts, fun u hu => ?_⟩
    rw [uIcc_of_le ht0] at hu
    rw [uIcc_of_le hxs]
    have hm := le_and_le_of_forall_mem_Icc hΦadd hκ hrate (fun v hv => hbandU (hband v hv)) hu
    rw [hΦ0] at hm
    exact ⟨hm.1, hm.2.trans_eq hts⟩
  · -- the reversed flow `t ↦ Φ (-t)` with `-η` and the band `[-b, -a]`
    have hΨ : Continuous (fun p : ℝ × X => Φ (-p.1) p.2) :=
      hΦ.comp ((continuous_fst.neg).prodMk continuous_snd)
    have hΨ0 : ∀ y, Φ (-0) y = y := fun y => by rw [neg_zero, hΦ0]
    have hΨadd : ∀ s t y, Φ (-(s + t)) y = Φ (-s) (Φ (-t) y) := fun s t y => by
      rw [neg_add, hΦadd]
    have hband' : (fun y => -η y) ⁻¹' Icc (-b) (-a) ⊆ U := fun y hy =>
      hbandU ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hrate' : ∀ y t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ (-s) y ∈ U) →
        -η y + κ * t ≤ -η (Φ (-t) y) := by
      intro y t ht hU'
      have hr := add_mul_le_of_forall_mem_Icc hΦadd hrate (x := y) (t₁ := -t) (t₂ := 0)
        (by linarith) (fun u hu => by
          have := hU' (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
          rwa [neg_neg] at this)
      rw [hΦ0] at hr
      linarith
    obtain ⟨t, ht0, hband, hts⟩ :=
      exists_forward_crossing (Φ := fun t y => Φ (-t) y) (η := fun y => -η y) (a := -b) (b := -a)
        hΨ hΨ0 hΨadd hη.neg hU hκ hband' hrate' (x := x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
        (s := -s) (by linarith) (by linarith [hs.1])
    refine ⟨-t, by linarith [hts], fun u hu => ?_⟩
    rw [uIcc_of_ge (by linarith : -t ≤ 0)] at hu
    rw [uIcc_of_ge hsx]
    have hbandΦ : ∀ v ∈ Icc (-t) 0, Φ v x ∈ U := fun v hv => by
      have h := hband (-v) ⟨by linarith [hv.2], by linarith [hv.1]⟩
      simp only [neg_neg] at h
      exact hbandU ⟨by linarith [h.2], by linarith [h.1]⟩
    have hm := le_and_le_of_forall_mem_Icc hΦadd hκ hrate hbandΦ hu
    rw [hΦ0] at hm
    have hts' : η (Φ (-t) x) = s := by linarith [hts]
    exact ⟨hts' ▸ hm.1, hm.2⟩

/-- **Specification of the hitting time** on the band. -/
theorem hittingTime_spec (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hη : Continuous η) (hU : IsOpen U) (hκ : 0 < κ) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} (hx : η x ∈ Icc a b) {s : ℝ} (hs : s ∈ Icc a b) :
    η (Φ (hittingTime Φ η x s) x) = s ∧
      ∀ u ∈ uIcc 0 (hittingTime Φ η x s), η (Φ u x) ∈ uIcc (η x) s := by
  have h := exists_crossing hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hs
  unfold hittingTime
  split_ifs
  exact h.choose_spec

/-- **Uniqueness of the hitting time**: any crossing time whose orbit segment stays in `U` is the
hitting time. -/
theorem hittingTime_eq_of_forall_mem (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hη : Continuous η) (hU : IsOpen U) (hκ : 0 < κ) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} (hx : η x ∈ Icc a b) {s : ℝ} (hs : s ∈ Icc a b) {t : ℝ}
    (htU : ∀ u ∈ uIcc 0 t, Φ u x ∈ U) (hts : η (Φ t x) = s) :
    hittingTime Φ η x s = t := by
  obtain ⟨h1, h2⟩ := hittingTime_spec hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hs
  apply eq_of_forall_mem_uIcc hΦadd hκ hrate (x := x) (fun u hu => ?_) (h1.trans hts.symm)
  rcases uIcc_subset_uIcc_union_uIcc hu with hu' | hu'
  · rw [uIcc_comm] at hu'
    exact hbandU (uIcc_subset_Icc hx hs (h2 u hu'))
  · exact htU u hu'

/-- The hitting time from a point to its own level is `0`. -/
theorem hittingTime_self (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hη : Continuous η) (hU : IsOpen U) (hκ : 0 < κ) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} (hx : η x ∈ Icc a b) : hittingTime Φ η x (η x) = 0 :=
  hittingTime_eq_of_forall_mem hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hx
    (fun u hu => by
      rw [uIcc_self, mem_singleton_iff] at hu
      rw [hu, hΦ0]; exact hbandU hx)
    (by rw [hΦ0])

/-- **Hitting back**: from the hitting point, the hitting time back to the starting level is the
negative of the forward one. -/
theorem hittingTime_flow_hittingTime (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hη : Continuous η) (hU : IsOpen U) (hκ : 0 < κ) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} (hx : η x ∈ Icc a b) {s : ℝ} (hs : s ∈ Icc a b) :
    hittingTime Φ η (Φ (hittingTime Φ η x s) x) (η x) = -hittingTime Φ η x s := by
  set τ := hittingTime Φ η x s with hτ
  obtain ⟨h1, h2⟩ := hittingTime_spec hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hs
  rw [← hτ] at h1 h2
  refine hittingTime_eq_of_forall_mem hΦ hΦ0 hΦadd hη hU hκ hbandU hrate
    (by rw [h1]; exact hs) hx (fun u hu => ?_) ?_
  · rw [← hΦadd]
    have hu' : u + τ ∈ uIcc 0 τ := by
      rcases le_total τ 0 with h | h
      · rw [uIcc_of_ge h]
        rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ -τ)] at hu
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      · rw [uIcc_of_le h]
        rw [uIcc_of_ge (by linarith : -τ ≤ (0 : ℝ))] at hu
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    exact hbandU (uIcc_subset_Icc hx hs (h2 _ hu'))
  · rw [flow_neg_apply_flow hΦ0 hΦadd]

/-- **Time bound**: `κ |τ| ≤ |s - η x|`. -/
theorem mul_abs_hittingTime_le (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hη : Continuous η) (hU : IsOpen U) (hκ : 0 < κ) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} (hx : η x ∈ Icc a b) {s : ℝ} (hs : s ∈ Icc a b) :
    κ * |hittingTime Φ η x s| ≤ |s - η x| := by
  set τ := hittingTime Φ η x s with hτ
  obtain ⟨h1, h2⟩ := hittingTime_spec hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hs
  rw [← hτ] at h1 h2
  have hU' : ∀ u ∈ uIcc 0 τ, Φ u x ∈ U := fun u hu => hbandU (uIcc_subset_Icc hx hs (h2 u hu))
  rcases le_total 0 τ with h | h
  · have hr := add_mul_le_of_forall_mem_Icc hΦadd hrate h
      (fun u hu => hU' u (by rwa [uIcc_of_le h]))
    rw [hΦ0, h1, sub_zero] at hr
    rw [abs_of_nonneg h]
    exact (by linarith : κ * τ ≤ s - η x).trans (le_abs_self _)
  · have hr := add_mul_le_of_forall_mem_Icc hΦadd hrate h
      (fun u hu => hU' u (by rwa [uIcc_of_ge h]))
    rw [hΦ0, h1, zero_sub] at hr
    rw [abs_of_nonpos h, abs_sub_comm]
    exact (by linarith : κ * -τ ≤ η x - s).trans (le_abs_self _)

/-- **Continuity of the hitting time** on `η⁻¹[a, b] × [a, b]`. -/
theorem continuousOn_hittingTime (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hη : Continuous η) (hU : IsOpen U) (hκ : 0 < κ) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x)) :
    ContinuousOn (fun p : X × ℝ => hittingTime Φ η p.1 p.2) ((η ⁻¹' Icc a b) ×ˢ Icc a b) := by
  rintro ⟨x₀, s₀⟩ ⟨hx₀, hs₀⟩
  set S := (η ⁻¹' Icc a b) ×ˢ Icc a b with hS
  set t₀ := hittingTime Φ η x₀ s₀ with ht₀
  obtain ⟨h1, h2⟩ := hittingTime_spec hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx₀ hs₀
  rw [← ht₀] at h1 h2
  set m := min 0 t₀ with hm
  set M := max 0 t₀ with hM
  have hmM : m ≤ M := min_le_max
  have hIcc : Icc m M = uIcc 0 t₀ := rfl
  have hW : IsOpen {u : ℝ | Φ u x₀ ∈ U} :=
    hU.preimage (hΦ.comp (continuous_id.prodMk continuous_const))
  obtain ⟨δ, hδ, hδW⟩ := exists_pos_Icc_sub_add_subset hW
    (fun u hu => hbandU (uIcc_subset_Icc hx₀ hs₀ (h2 u (hIcc ▸ hu)))) hmM
  -- the core estimate for small `ε`
  have hcore : ∀ ε, 0 < ε → ε < δ → ∀ᶠ p in 𝓝[S] ((x₀, s₀) : X × ℝ),
      hittingTime Φ η p.1 p.2 ∈ Ioo (t₀ - ε) (t₀ + ε) := by
    intro ε hε hεδ
    set Hε := Icc (m - ε) (M + ε) with hHε
    have hHW : Hε ⊆ {u : ℝ | Φ u x₀ ∈ U} := fun u hu =>
      hδW ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have ht₀m : m ≤ t₀ := min_le_right _ _
    have ht₀M : t₀ ≤ M := le_max_right _ _
    have h0m : m ≤ 0 := min_le_left _ _
    have h0M : 0 ≤ M := le_max_left _ _
    -- tube lemma
    have hC1 : ∀ᶠ x in 𝓝 x₀, ∀ u ∈ Hε, Φ u x ∈ U := by
      refine isCompact_Icc.eventually_forall_of_forall_eventually fun u hu => ?_
      have hc : Continuous (fun z : X × ℝ => Φ z.2 z.1) :=
        hΦ.comp (continuous_snd.prodMk continuous_fst)
      exact hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (hHW hu))
    -- strict separation at `x₀`
    have hlo : η (Φ (t₀ - ε) x₀) + κ * ε ≤ s₀ := by
      have hr := add_mul_le_of_forall_mem_Icc hΦadd hrate (x := x₀) (t₁ := t₀ - ε) (t₂ := t₀)
        (by linarith) (fun u hu => hHW ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      rw [h1, sub_sub_cancel] at hr
      exact hr
    have hhi : s₀ + κ * ε ≤ η (Φ (t₀ + ε) x₀) := by
      have hr := add_mul_le_of_forall_mem_Icc hΦadd hrate (x := x₀) (t₁ := t₀) (t₂ := t₀ + ε)
        (by linarith) (fun u hu => hHW ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      rw [h1, add_sub_cancel_left] at hr
      exact hr
    have hκε : 0 < κ * ε := mul_pos hκ hε
    have hcont : ∀ c : ℝ, Continuous (fun p : X × ℝ => η (Φ c p.1)) := fun c =>
      hη.comp (hΦ.comp (continuous_const.prodMk continuous_fst))
    have hC2 : ∀ᶠ p in 𝓝 ((x₀, s₀) : X × ℝ), η (Φ (t₀ - ε) p.1) < p.2 :=
      (hcont (t₀ - ε)).continuousAt.eventually_lt continuous_snd.continuousAt
        (by change η (Φ (t₀ - ε) x₀) < s₀; linarith)
    have hC3 : ∀ᶠ p in 𝓝 ((x₀, s₀) : X × ℝ), p.2 < η (Φ (t₀ + ε) p.1) :=
      continuous_snd.continuousAt.eventually_lt (hcont (t₀ + ε)).continuousAt
        (by change s₀ < η (Φ (t₀ + ε) x₀); linarith)
    have hC1' : ∀ᶠ p in 𝓝 ((x₀, s₀) : X × ℝ), ∀ u ∈ Hε, Φ u p.1 ∈ U :=
      (continuous_fst.tendsto ((x₀, s₀) : X × ℝ)).eventually hC1
    filter_upwards [nhdsWithin_le_nhds hC1', nhdsWithin_le_nhds hC2, nhdsWithin_le_nhds hC3,
      self_mem_nhdsWithin] with p hp1 hp2 hp3 hpS
    obtain ⟨x, s⟩ := p
    obtain ⟨hx, hs⟩ := hpS
    change η (Φ (t₀ - ε) x) < s at hp2
    change s < η (Φ (t₀ + ε) x) at hp3
    have hgc : Continuous (fun u : ℝ => η (Φ u x)) :=
      hη.comp (hΦ.comp (continuous_id.prodMk continuous_const))
    obtain ⟨t, ht, hts⟩ := intermediate_value_Icc (by linarith : t₀ - ε ≤ t₀ + ε)
      hgc.continuousOn ⟨hp2.le, hp3.le⟩
    have ht1 : t₀ - ε < t := lt_of_le_of_ne ht.1 (fun h => by
      rw [← h] at hts; exact absurd hts hp2.ne)
    have ht2 : t < t₀ + ε := lt_of_le_of_ne ht.2 (fun h => by
      rw [h] at hts; exact absurd hts hp3.ne')
    have htU : ∀ u ∈ uIcc 0 t, Φ u x ∈ U := fun u hu =>
      hp1 u (uIcc_subset_Icc ⟨by linarith, by linarith⟩
        ⟨by linarith [ht.1], by linarith [ht.2]⟩ hu)
    change hittingTime Φ η x s ∈ Ioo (t₀ - ε) (t₀ + ε)
    rw [hittingTime_eq_of_forall_mem hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hs htU hts]
    exact ⟨ht1, ht2⟩
  rw [ContinuousWithinAt, tendsto_order]
  refine ⟨fun a' ha' => ?_, fun b' hb' => ?_⟩
  · have hε : 0 < min (δ / 2) (t₀ - a') := lt_min (by linarith) (by linarith)
    filter_upwards [hcore _ hε (lt_of_le_of_lt (min_le_left _ _) (by linarith))] with p hp
    have := min_le_right (δ / 2) (t₀ - a')
    linarith [hp.1]
  · have hε : 0 < min (δ / 2) (b' - t₀) := lt_min (by linarith) (by linarith)
    filter_upwards [hcore _ hε (lt_of_le_of_lt (min_le_left _ _) (by linarith))] with p hp
    have := min_le_right (δ / 2) (b' - t₀)
    linarith [hp.2]

end Band

/-- **The product from a hitting time** (generic over the set of levels `P`): if the hitting time
is continuous on `η⁻¹ P × P`, reaches every level of `P`, returns, and vanishes at the own level,
then `{η = c} × P ≃ₜ {η ∈ P}` with LC46's formulas. -/
theorem exists_homeomorph_of_hittingTime {Φ : ℝ → X → X}
    (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)) {η : X → ℝ}
    (hη : Continuous η) {P : Set ℝ} {c : ℝ} (hc : c ∈ P)
    (hcont : ContinuousOn (fun p : X × ℝ => hittingTime Φ η p.1 p.2) ((η ⁻¹' P) ×ˢ P))
    (hspec : ∀ x, η x ∈ P → ∀ s ∈ P, η (Φ (hittingTime Φ η x s) x) = s)
    (hback : ∀ x, η x ∈ P → ∀ s ∈ P,
      hittingTime Φ η (Φ (hittingTime Φ η x s) x) (η x) = -hittingTime Φ η x s)
    (hself : ∀ x, η x ∈ P → hittingTime Φ η x (η x) = 0) :
    ∃ e : ({x : X // η x = c} × P) ≃ₜ {x : X // η x ∈ P},
      (∀ p, (e p : X) = Φ (hittingTime Φ η p.1 p.2) p.1) ∧
      (∀ y, ((e.symm y).1 : X) = Φ (hittingTime Φ η y c) y) ∧
      (∀ y, ((e.symm y).2 : ℝ) = η y) ∧
      (∀ p, η (e p) = p.2) ∧
      ∀ x : {x : X // η x = c}, (e (x, ⟨c, hc⟩) : X) = x := by
  set τ := hittingTime Φ η with hτ
  have hmemc : ∀ x : {x : X // η x = c}, η x ∈ P := fun x => by rw [x.2]; exact hc
  have hfwd : ∀ p : {x : X // η x = c} × P, η (Φ (τ p.1 p.2) p.1) ∈ P := fun p => by
    rw [hspec p.1 (hmemc p.1) p.2 p.2.2]; exact p.2.2
  have hbwd : ∀ y : {x : X // η x ∈ P}, η (Φ (τ y c) y) = c := fun y => hspec y y.2 c hc
  have hτ1 : Continuous (fun p : {x : X // η x = c} × P => τ p.1 p.2) :=
    hcont.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun p => ⟨hmemc p.1, p.2.2⟩)
  have hτ2 : Continuous (fun y : {x : X // η x ∈ P} => τ y c) :=
    hcont.comp_continuous (continuous_subtype_val.prodMk continuous_const) (fun y => ⟨y.2, hc⟩)
  let e : ({x : X // η x = c} × P) ≃ₜ {x : X // η x ∈ P} :=
    { toFun := fun p => ⟨Φ (τ p.1 p.2) p.1, hfwd p⟩
      invFun := fun y => (⟨Φ (τ y c) y, hbwd y⟩, ⟨η y, y.2⟩)
      left_inv := by
        rintro ⟨x, s⟩
        have hxc : η (x : X) = c := x.2
        have hb := hback x (hmemc x) s s.2
        rw [hxc] at hb
        apply Prod.ext
        · apply Subtype.ext
          change Φ (τ (Φ (τ x s) x) c) (Φ (τ x s) x) = x
          rw [hb, flow_neg_apply_flow hΦ0 hΦadd]
        · apply Subtype.ext
          exact hspec x (hmemc x) s s.2
      right_inv := by
        intro y
        apply Subtype.ext
        change Φ (τ (Φ (τ y c) y) (η y)) (Φ (τ y c) y) = y
        rw [hback y y.2 c hc, flow_neg_apply_flow hΦ0 hΦadd]
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact hΦ.comp (hτ1.prodMk (continuous_subtype_val.comp continuous_fst))
      continuous_invFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          exact hΦ.comp (hτ2.prodMk continuous_subtype_val)
        · exact (hη.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨e, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun p => hspec p.1 (hmemc p.1) p.2 p.2.2, fun x => ?_⟩
  change Φ (τ x c) x = x
  have h := hself x (hmemc x)
  rw [x.2] at h
  rw [h, hΦ0]

/-- **S-HIT, bounded band.** A continuous `η` increasing at rate `κ > 0` along the orbits of a
continuous flow, on an open set containing the band `η⁻¹[a, b]`: the hitting time is continuous on
`η⁻¹[a, b] × [a, b]`, reaches every level in time `≤ |s - η x| / κ` with the orbit crossing only the
intermediate levels, and `{η = c} × [a, b] ≃ₜ {a ≤ η ≤ b}` by `(x, s) ↦ Φ_{τ(x, s)} x`. -/
theorem exists_hittingTime_band_product {Φ : ℝ → X → X}
    (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)) {η : X → ℝ}
    (hη : Continuous η) {U : Set X} (hU : IsOpen U) {a b c κ : ℝ} (hκ : 0 < κ)
    (hc : c ∈ Icc a b) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x)) :
    ContinuousOn (fun p : X × ℝ => hittingTime Φ η p.1 p.2) ((η ⁻¹' Icc a b) ×ˢ Icc a b) ∧
      (∀ x, η x ∈ Icc a b → ∀ s ∈ Icc a b,
        η (Φ (hittingTime Φ η x s) x) = s ∧
          (∀ u ∈ uIcc 0 (hittingTime Φ η x s), η (Φ u x) ∈ uIcc (η x) s) ∧
          κ * |hittingTime Φ η x s| ≤ |s - η x|) ∧
      ∃ e : ({x : X // η x = c} × Icc a b) ≃ₜ {x : X // η x ∈ Icc a b},
        (∀ p, (e p : X) = Φ (hittingTime Φ η p.1 p.2) p.1) ∧
        (∀ y, ((e.symm y).1 : X) = Φ (hittingTime Φ η y c) y) ∧
        (∀ y, ((e.symm y).2 : ℝ) = η y) ∧
        (∀ p, η (e p) = p.2) ∧
        ∀ x : {x : X // η x = c}, (e (x, ⟨c, hc⟩) : X) = x := by
  have hcont := continuousOn_hittingTime hΦ hΦ0 hΦadd hη hU hκ hbandU hrate
  refine ⟨hcont, fun x hx s hs =>
    ⟨(hittingTime_spec hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hs).1,
      (hittingTime_spec hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hs).2,
      mul_abs_hittingTime_le hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hs⟩, ?_⟩
  exact exists_homeomorph_of_hittingTime hΦ hΦ0 hΦadd hη hc hcont
    (fun x hx s hs => (hittingTime_spec hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hs).1)
    (fun x hx s hs => hittingTime_flow_hittingTime hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hs)
    (fun x hx => hittingTime_self hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx)

/-- **S-HIT, half-infinite band** (the S6 / LFR46 exterior product). If for every `b` the rate
holds with some `κ_b > 0` on an open set containing `η⁻¹[a, b]`, the hitting time is continuous on
`η⁻¹[a, ∞) × [a, ∞)` and `{η = c} × [a, ∞) ≃ₜ {η ≥ a}`. -/
theorem exists_hittingTime_halfBand_product {Φ : ℝ → X → X}
    (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)) {η : X → ℝ}
    (hη : Continuous η) {a c : ℝ} (hc : c ∈ Ici a)
    (hrate : ∀ b, ∃ U : Set X, IsOpen U ∧ η ⁻¹' Icc a b ⊆ U ∧ ∃ κ > 0,
      ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x)) :
    ContinuousOn (fun p : X × ℝ => hittingTime Φ η p.1 p.2) ((η ⁻¹' Ici a) ×ˢ Ici a) ∧
      (∀ x, η x ∈ Ici a → ∀ s ∈ Ici a,
        η (Φ (hittingTime Φ η x s) x) = s ∧
          ∀ u ∈ uIcc 0 (hittingTime Φ η x s), η (Φ u x) ∈ uIcc (η x) s) ∧
      ∃ e : ({x : X // η x = c} × Ici a) ≃ₜ {x : X // η x ∈ Ici a},
        (∀ p, (e p : X) = Φ (hittingTime Φ η p.1 p.2) p.1) ∧
        (∀ y, ((e.symm y).1 : X) = Φ (hittingTime Φ η y c) y) ∧
        (∀ y, ((e.symm y).2 : ℝ) = η y) ∧
        (∀ p, η (e p) = p.2) ∧
        ∀ x : {x : X // η x = c}, (e (x, ⟨c, hc⟩) : X) = x := by
  choose U hUo hUband κ hκ hrateU using hrate
  have hmem : ∀ {x : ℝ} {b : ℝ}, x ∈ Ici a → x ≤ b → x ∈ Icc a b := fun hx hxb => ⟨hx, hxb⟩
  have hspec : ∀ x, η x ∈ Ici a → ∀ s ∈ Ici a,
      η (Φ (hittingTime Φ η x s) x) = s ∧
        ∀ u ∈ uIcc 0 (hittingTime Φ η x s), η (Φ u x) ∈ uIcc (η x) s := fun x hx s hs =>
    hittingTime_spec hΦ hΦ0 hΦadd hη (hUo (max (η x) s)) (hκ _) (hUband _) (hrateU _)
      (hmem hx (le_max_left _ _)) (hmem hs (le_max_right _ _))
  have hcont : ContinuousOn (fun p : X × ℝ => hittingTime Φ η p.1 p.2) ((η ⁻¹' Ici a) ×ˢ Ici a) := by
    rintro ⟨x₀, s₀⟩ ⟨hx₀, hs₀⟩
    set b₀ := max (η x₀) s₀ + 1 with hb₀
    have hloc := continuousOn_hittingTime hΦ hΦ0 hΦadd hη (hUo b₀) (hκ b₀) (hUband b₀)
      (hrateU b₀) (x₀, s₀)
      ⟨hmem hx₀ (by linarith [le_max_left (η x₀) s₀]),
        hmem hs₀ (by linarith [le_max_right (η x₀) s₀])⟩
    refine hloc.mono_of_mem_nhdsWithin (mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_)
    refine ⟨{p : X × ℝ | η p.1 < b₀ ∧ p.2 < b₀}, ?_, fun p hp => ?_⟩
    · have ho : IsOpen {p : X × ℝ | η p.1 < b₀ ∧ p.2 < b₀} :=
        (isOpen_lt (hη.comp continuous_fst) continuous_const).inter
          (isOpen_lt continuous_snd continuous_const)
      exact ho.mem_nhds ⟨by change η x₀ < b₀; linarith [le_max_left (η x₀) s₀],
        by change s₀ < b₀; linarith [le_max_right (η x₀) s₀]⟩
    · exact ⟨hmem hp.2.1 hp.1.1.le, hmem hp.2.2 hp.1.2.le⟩
  refine ⟨hcont, hspec, ?_⟩
  exact exists_homeomorph_of_hittingTime hΦ hΦ0 hΦadd hη hc hcont
    (fun x hx s hs => (hspec x hx s hs).1)
    (fun x hx s hs => hittingTime_flow_hittingTime hΦ hΦ0 hΦadd hη (hUo (max (η x) s)) (hκ _)
      (hUband _) (hrateU _) (hmem hx (le_max_left _ _)) (hmem hs (le_max_right _ _)))
    (fun x hx => hittingTime_self hΦ hΦ0 hΦadd hη (hUo (η x)) (hκ _) (hUband _) (hrateU _)
      (hmem hx le_rfl))

/-- **Dini form of the rate** (the design's wording): a right lower Dini bound `κ` at every point
of the open set `U` gives the integrated rate along orbit segments inside `U`. -/
theorem rate_of_eventually {Φ : ℝ → X → X} (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)) {η : X → ℝ}
    (hη : Continuous η) {U : Set X} {κ : ℝ}
    (hdini : ∀ x ∈ U, ∀ κ' < κ, ∀ᶠ h in 𝓝[>] (0 : ℝ), η x + κ' * h ≤ η (Φ h x)) :
    ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x) := by
  intro x t ht hU
  have hf : Continuous (fun u : ℝ => -η (Φ u x)) :=
    (hη.comp (hΦ.comp (continuous_id.prodMk continuous_const))).neg
  have key := DifferentialGeometry.Analysis.Calculus.sub_le_mul_sub_of_eventually_increment_le
    (φ := fun u : ℝ => -η (Φ u x)) (B := -κ) ht hf.continuousOn (fun s hs c hc => ?_)
  · rw [hΦ0] at key
    linarith
  have hev := hdini (Φ s x) (hU s ⟨hs.1, hs.2.le⟩) (-c) (by linarith)
  have hmap : Tendsto (fun s' : ℝ => s' - s) (𝓝[>] s) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto (fun s' : ℝ => s' - s) (𝓝 s) (𝓝 0) := by
        have := (continuous_sub_right s).tendsto s
        rwa [sub_self] at this
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s' hs'
      exact mem_Ioi.mpr (sub_pos.mpr (mem_Ioi.mp hs'))
  filter_upwards [hmap.eventually hev] with s' hs'
  rw [← hΦadd, sub_add_cancel] at hs'
  linarith

/-- **Consumer of S-HIT**: the translation flow on `ℝ` with `η = id` identifies the unit band with
the product of the level `{0}` and `[0, 1]`, the second factor being the position. -/
theorem exists_translation_band_product :
    ∃ e : ({x : ℝ // id x = 0} × Icc (0 : ℝ) 1) ≃ₜ {x : ℝ // id x ∈ Icc (0 : ℝ) 1},
      ∀ p, (e p : ℝ) = p.2 := by
  obtain ⟨-, -, e, -, -, -, heη, -⟩ := exists_hittingTime_band_product (X := ℝ)
    (Φ := fun t x => t + x) (continuous_fst.add continuous_snd) (fun x => zero_add x)
    (fun s t x => add_assoc s t x) (η := id) continuous_id isOpen_univ (a := 0) (b := 1) (c := 0)
    (κ := 1) one_pos ⟨le_rfl, zero_le_one⟩ (subset_univ _)
    (fun x t _ _ => by simp only [id, one_mul]; linarith)
  exact ⟨e, heη⟩

end DifferentialGeometry.Geometry.FiniteSoul
