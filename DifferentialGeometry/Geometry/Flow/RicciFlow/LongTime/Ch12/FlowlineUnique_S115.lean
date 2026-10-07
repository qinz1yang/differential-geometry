import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TowerTransfer_S55

set_option autoImplicit false

/-! # CH12-S115 G1: uniqueness of flow-lines across different histories `(n, first, last)`

A *flow-line* is a family `w : ∀ r ∈ W, (postStage F.observation r).Carrier` which near a time `s` is the
survivor-map image `ψ_{act r} y` of ONE point `y` of `backwardSurvivorDomain first last` of the `n`-th history
(the shape of conjunct 16 of the S8 list, with `φ p = y` fixed, and of `PersistentModelPatch.agrees` at a
frozen source point).

* `backwardSurvivorMap_eq_range_S115` (one history): two survivor points whose images agree at ONE stage `c`
  have the same images at every stage of the common range `[max first, min last]` (backward trace uniqueness
  `point_unique` for `j ≤ c`, forward uniqueness `point_eq_of_point_first_eq` for `c ≤ j`).
* `flowline_window_S115` (tower coherence): two flow-lines lifted at `s` (possibly in DIFFERENT histories
  `n₁ ≠ n₂`, different `first / last`) have a common time window `(a, b) ∋ s` in which agreement at one time
  gives agreement at every time (both are transported to one history `N ≥ max n₀` by `lift_uniform_S55`).
* `flowline_unique_Icc_S115`: if lifted at every `s ∈ [r₀, t₀]` and equal at `t₀`, then equal on `[r₀, t₀]`
  (clopen set in the connected `Icc`). -/
noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.Ch12
universe u

theorem trace_point_eq_of_endpoint_eq_S115 {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {e₁ e₂ : (H.stage last).Carrier} (h : e₁ = e₂)
    (A : BackwardPointTrace H first last hle e₁) (B : BackwardPointTrace H first last hle e₂)
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) :
    A.point j hf hl = B.point j hf hl := by
  subst h
  exact BackwardPointTrace.point_unique A B j hf hl

theorem backwardSurvivorMap_eq_range_S115 (K : ObservedHistory.{u})
    {f₁ l₁ f₂ l₂ : Fin (K.eventCount + 1)} (o₁ : f₁ ≤ l₁) (o₂ : f₂ ≤ l₂)
    (y₁ : K.backwardSurvivorDomain f₁ l₁ o₁) (y₂ : K.backwardSurvivorDomain f₂ l₂ o₂)
    (c : Fin (K.eventCount + 1)) (hc₁ : f₁ ≤ c) (hc₁' : c ≤ l₁) (hc₂ : f₂ ≤ c) (hc₂' : c ≤ l₂)
    (hc : K.backwardSurvivorMap f₁ l₁ o₁ c hc₁ hc₁' y₁ = K.backwardSurvivorMap f₂ l₂ o₂ c hc₂ hc₂' y₂)
    (j : Fin (K.eventCount + 1)) (hj₁ : f₁ ≤ j) (hj₁' : j ≤ l₁) (hj₂ : f₂ ≤ j) (hj₂' : j ≤ l₂) :
    K.backwardSurvivorMap f₁ l₁ o₁ j hj₁ hj₁' y₁ = K.backwardSurvivorMap f₂ l₂ o₂ j hj₂ hj₂' y₂ := by
  let A₁ := Classical.choice y₁.property
  let A₂ := Classical.choice y₂.property
  rw [K.backwardSurvivorMap_eq_point f₁ l₁ o₁ j hj₁ hj₁' y₁ A₁,
    K.backwardSurvivorMap_eq_point f₂ l₂ o₂ j hj₂ hj₂' y₂ A₂]
  rw [K.backwardSurvivorMap_eq_point f₁ l₁ o₁ c hc₁ hc₁' y₁ A₁,
    K.backwardSurvivorMap_eq_point f₂ l₂ o₂ c hc₂ hc₂' y₂ A₂] at hc
  rcases le_total j c with hjc | hcj
  · let T₁ := (A₁.restrictLast hc₁ hc₁').restrictFirst hj₁ hjc
    let T₂ := (A₂.restrictLast hc₂ hc₂').restrictFirst hj₂ hjc
    exact trace_point_eq_of_endpoint_eq_S115 hc T₁ T₂ j le_rfl hjc
  · let T₁ := A₁.restrictFirst hc₁ hc₁'
    let T₂ := A₂.restrictFirst hc₂ hc₂'
    exact T₁.point_eq_of_point_first_eq T₂ hc j hcj hj₁' hj₂'

theorem flowline_window_S115 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (W : Set ℝ)
    (w₁ w₂ : ∀ r : ℝ, r ∈ W → (postStage F.observation r).Carrier) (s : ℝ) (hs0 : 0 < s)
    (h₁ : ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b) (hrW : (r : ℝ) ∈ W),
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
          (w₁ r hrW))
    (h₂ : ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b) (hrW : (r : ℝ) ∈ W),
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
          (w₂ r hrW)) :
    ∃ (a b : ℝ) (_ : a < s) (_ : s < b), ∀ (r₁ r₂ : ℝ) (h1 : r₁ ∈ W) (h2 : r₂ ∈ W),
      a < r₁ → r₁ < b → a < r₂ → r₂ < b → w₁ r₁ h1 = w₂ r₁ h1 → w₁ r₂ h2 = w₂ r₂ h2 := by
  have hup : ∀ (w : ∀ r : ℝ, r ∈ W → (postStage F.observation r).Carrier),
      (∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b) (hrW : (r : ℝ) ∈ W),
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
          (w r hrW)) →
      ∃ (a b : ℝ) (_ : a < s) (_ : s < b) (n₀ : ℕ), b ≤ n₀ ∧ ∀ N : ℕ, n₀ ≤ N →
      ∃ (first last : Fin ((F.tower.history N).eventCount + 1))
        (ordered : first ≤ last)
        (stages : ∀ r : Icc (0 : ℝ) (F.tower.history N).horizon, (r : ℝ) ∈ Ioo a b →
          first ≤ (F.tower.history N).toHistory.activeStage r ∧
            (F.tower.history N).toHistory.activeStage r ≤ last)
        (y : (F.tower.history N).toHistory.backwardSurvivorDomain first last ordered),
        ∀ (r : Icc (0 : ℝ) (F.tower.history N).horizon) (hr : (r : ℝ) ∈ Ioo a b)
          (hrW : (r : ℝ) ∈ W),
          HEq ((F.tower.history N).toHistory.backwardSurvivorMap first last ordered
            ((F.tower.history N).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
            (w r hrW) := by
    intro w hw
    obtain ⟨n, first, last, ordered, a, b, has, hsb, hb, stages, y, hy⟩ := hw
    obtain ⟨a', b', ha', hb', n₀, hn₀, hN⟩ := lift_uniform_S55 F
      ({0} : Set (EuclideanSpace ℝ (Fin 3))) W (fun r => (postStage F.observation r).Carrier)
      (fun r hrW _ => w r hrW) s
      ⟨n, first, last, ordered, a, b, has, hsb, hb, stages, fun _ => y,
        contMDiffOn_const, fun r hr hrW p _ => hy r hr hrW⟩
    refine ⟨a', b', ha', hb', n₀, hn₀, fun N hN' => ?_⟩
    obtain ⟨first', last', ordered', stages', φ', -, hφ'⟩ := hN N hN'
    exact ⟨first', last', ordered', stages', φ' 0, fun r hr hrW => hφ' r hr hrW 0 rfl⟩
  obtain ⟨a₁, b₁, ha₁, hb₁, n₁, hn₁, hN₁⟩ := hup w₁ h₁
  obtain ⟨a₂, b₂, ha₂, hb₂, n₂, hn₂, hN₂⟩ := hup w₂ h₂
  obtain ⟨f₁, l₁, o₁, st₁, y₁, hy₁⟩ := hN₁ (max n₁ n₂) (le_max_left _ _)
  obtain ⟨f₂, l₂, o₂, st₂, y₂, hy₂⟩ := hN₂ (max n₁ n₂) (le_max_right _ _)
  refine ⟨max (max a₁ a₂) 0, min b₁ b₂, max_lt (max_lt ha₁ ha₂) hs0, lt_min hb₁ hb₂, ?_⟩
  intro r₁ r₂ h1 h2 ha1 hb1 ha2 hb2 hw
  have hmem : ∀ r : ℝ, max (max a₁ a₂) 0 < r → r < min b₁ b₂ →
      r ∈ Icc (0 : ℝ) (F.tower.history (max n₁ n₂)).horizon := by
    intro r hra hrb
    refine ⟨(le_max_right _ _).trans hra.le, ?_⟩
    rw [F.tower.horizon_eq]
    have : r ≤ b₁ := (lt_min_iff.mp hrb).1.le
    exact this.trans (hn₁.trans (by exact_mod_cast le_max_left n₁ n₂))
  have hI1 : ∀ r : ℝ, max (max a₁ a₂) 0 < r → r < min b₁ b₂ → r ∈ Ioo a₁ b₁ := fun r hra hrb =>
    ⟨lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hra, (lt_min_iff.mp hrb).1⟩
  have hI2 : ∀ r : ℝ, max (max a₁ a₂) 0 < r → r < min b₁ b₂ → r ∈ Ioo a₂ b₂ := fun r hra hrb =>
    ⟨lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hra, (lt_min_iff.mp hrb).2⟩
  set R₁ : Icc (0 : ℝ) (F.tower.history (max n₁ n₂)).horizon := ⟨r₁, hmem r₁ ha1 hb1⟩ with hR₁
  set R₂ : Icc (0 : ℝ) (F.tower.history (max n₁ n₂)).horizon := ⟨r₂, hmem r₂ ha2 hb2⟩ with hR₂
  have e1 := hy₁ R₁ (hI1 r₁ ha1 hb1) h1
  have e2 := hy₂ R₁ (hI2 r₁ ha1 hb1) h1
  have hc : (F.tower.history (max n₁ n₂)).toHistory.backwardSurvivorMap f₁ l₁ o₁
      ((F.tower.history (max n₁ n₂)).toHistory.activeStage R₁) (st₁ R₁ (hI1 r₁ ha1 hb1)).1
      (st₁ R₁ (hI1 r₁ ha1 hb1)).2 y₁ =
      (F.tower.history (max n₁ n₂)).toHistory.backwardSurvivorMap f₂ l₂ o₂
      ((F.tower.history (max n₁ n₂)).toHistory.activeStage R₁) (st₂ R₁ (hI2 r₁ ha1 hb1)).1
      (st₂ R₁ (hI2 r₁ ha1 hb1)).2 y₂ := by
    apply eq_of_heq
    refine e1.trans (HEq.trans (heq_of_eq hw) e2.symm)
  have hj := backwardSurvivorMap_eq_range_S115 (F.tower.history (max n₁ n₂)).toHistory o₁ o₂ y₁ y₂
    _ (st₁ R₁ (hI1 r₁ ha1 hb1)).1 (st₁ R₁ (hI1 r₁ ha1 hb1)).2 (st₂ R₁ (hI2 r₁ ha1 hb1)).1
    (st₂ R₁ (hI2 r₁ ha1 hb1)).2 hc
    ((F.tower.history (max n₁ n₂)).toHistory.activeStage R₂) (st₁ R₂ (hI1 r₂ ha2 hb2)).1
    (st₁ R₂ (hI1 r₂ ha2 hb2)).2 (st₂ R₂ (hI2 r₂ ha2 hb2)).1 (st₂ R₂ (hI2 r₂ ha2 hb2)).2
  apply eq_of_heq
  exact (hy₁ R₂ (hI1 r₂ ha2 hb2) h2).symm.trans (HEq.trans (heq_of_eq hj) (hy₂ R₂ (hI2 r₂ ha2 hb2) h2))

theorem flowline_unique_Icc_S115 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (W : Set ℝ)
    (w₁ w₂ : ∀ r : ℝ, r ∈ W → (postStage F.observation r).Carrier) (r₀ t₀ : ℝ) (hr₀ : 0 < r₀)
    (hrt : r₀ ≤ t₀) (hW : Icc r₀ t₀ ⊆ W)
    (h₁ : ∀ s ∈ Icc r₀ t₀, ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b) (hrW : (r : ℝ) ∈ W),
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
          (w₁ r hrW))
    (h₂ : ∀ s ∈ Icc r₀ t₀, ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b) (hrW : (r : ℝ) ∈ W),
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
          (w₂ r hrW))
    (ht : w₁ t₀ (hW ⟨hrt, le_rfl⟩) = w₂ t₀ (hW ⟨hrt, le_rfl⟩)) :
    ∀ (r : ℝ) (hr : r ∈ Icc r₀ t₀), w₁ r (hW hr) = w₂ r (hW hr) := by
  have hwin : ∀ s : Icc r₀ t₀, ∃ (a b : ℝ) (_ : a < s.1) (_ : s.1 < b), ∀ (r₁ r₂ : ℝ) (h1 : r₁ ∈ W)
      (h2 : r₂ ∈ W), a < r₁ → r₁ < b → a < r₂ → r₂ < b → w₁ r₁ h1 = w₂ r₁ h1 →
      w₁ r₂ h2 = w₂ r₂ h2 := fun s =>
    flowline_window_S115 F W w₁ w₂ s.1 (hr₀.trans_le s.2.1) (h₁ s.1 s.2) (h₂ s.1 s.2)
  choose a b ha hb hwin using hwin
  let A : Set (Icc r₀ t₀) := {s | w₁ s.1 (hW s.2) = w₂ s.1 (hW s.2)}
  have hnhds : ∀ s : Icc r₀ t₀, {s' : Icc r₀ t₀ | a s < s'.1 ∧ s'.1 < b s} ∈ nhds s := fun s => by
    have : {s' : Icc r₀ t₀ | a s < s'.1 ∧ s'.1 < b s} = Subtype.val ⁻¹' Ioo (a s) (b s) := rfl
    rw [this]
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (ha s) (hb s))
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    filter_upwards [hnhds s] with s' hs'
    exact hwin s s.1 s'.1 (hW s.2) (hW s'.2) (ha s) (hb s) hs'.1 hs'.2 hs
  have hopen' : IsOpen Aᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    filter_upwards [hnhds s] with s' hs' hs'A
    exact hs (hwin s s'.1 s.1 (hW s'.2) (hW s.2) hs'.1 hs'.2 (ha s) (hb s) hs'A)
  have : PreconnectedSpace (Icc r₀ t₀) := Subtype.preconnectedSpace isPreconnected_Icc
  have hclopen : IsClopen A := ⟨isOpen_compl_iff.mp hopen', hopen⟩
  have hne : A.Nonempty := ⟨⟨t₀, hrt, le_rfl⟩, ht⟩
  intro r hr
  have := hclopen.eq_univ hne
  have hr' : (⟨r, hr⟩ : Icc r₀ t₀) ∈ A := by rw [this]; trivial
  exact hr'

end GC.LongTime.Ch12
