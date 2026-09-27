import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.Index

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u

namespace LWindowChain

private theorem exists_segment_partition {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) {F : Set ℝ}
    (hF : F.Finite) :
    ∃ (N : ℕ) (q : ℕ → ℝ), 0 < N ∧ q 0 = a ∧ q N = b ∧
      (∀ i < N, q i < q (i + 1) ∧ q (i + 1) - q i < δ) ∧ (∀ i, 0 < i → i < N → q i ∉ F) ∧
      (∀ i ≤ N, q i ∈ Icc a b) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (b - a) / δ)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  set L := (b - a) / N with hL
  have hLpos : 0 < L := div_pos (by linarith) hNpos
  have hNL : (N : ℝ) * L = b - a := by rw [hL]; field_simp
  have hLδ : L < δ / 2 := by
    rw [hL, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  have hpick : ∀ i : ℕ, ∃ x ∈ Ioo (a + i * L - L / 4) (a + i * L + L / 4), x ∉ F := fun i =>
    ((Set.Ioo_infinite (by linarith)).sdiff hF).nonempty
  let q : ℕ → ℝ := fun i => if i = 0 then a else if i < N then Classical.choose (hpick i) else b
  have hq0 : q 0 = a := by simp [q]
  have hqN : q N = b := by simp [q, hN0.ne']
  have hqi : ∀ i, 0 < i → i < N → q i ∈ Ioo (a + i * L - L / 4) (a + i * L + L / 4) ∧ q i ∉ F :=
    fun i hi hiN => by
      simp only [q, if_neg hi.ne', if_pos hiN]
      exact Classical.choose_spec (hpick i)
  have hlow : ∀ i ≤ N, a + i * L - L / 4 ≤ q i ∨ i = 0 := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact Or.inr rfl
    rcases lt_or_eq_of_le hi with hlt | rfl
    · exact Or.inl (hqi i hpos hlt).1.1.le
    · left
      rw [hqN, hNL]
      linarith
  have hup : ∀ i ≤ N, q i ≤ a + i * L + L / 4 := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hq0]; simp; linarith
    rcases lt_or_eq_of_le hi with hlt | rfl
    · exact (hqi i hpos hlt).1.2.le
    · rw [hqN, hNL]
      linarith
  have hlow' : ∀ i ≤ N, a + i * L - L / 4 ≤ q i ∧ (0 < i → a + i * L - L / 4 < q i ∨ i = N) := by
    intro i hi
    constructor
    · rcases hlow i hi with h | rfl
      · exact h
      · rw [hq0]; simp; linarith
    · intro hpos
      rcases lt_or_eq_of_le hi with hlt | rfl
      · exact Or.inl (hqi i hpos hlt).1.1
      · exact Or.inr rfl
  refine ⟨N, q, hN0, hq0, hqN, fun i hi => ?_, fun i hi hiN => (hqi i hi hiN).2, fun i hi => ?_⟩
  · have h1 := hup i hi.le
    have h2 := (hlow' (i + 1) hi).1
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h2
    constructor
    · rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rcases (hlow' 1 hi).2 one_pos with h | h
        · rw [hq0]; push_cast at h; linarith
        · have h' : q (0 + 1) = b := by rw [zero_add, h]; exact hqN
          rw [hq0, h']
          exact hab
      · rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with hlt | heq
        · have h3 := (hqi (i + 1) (Nat.succ_pos _) hlt).1.1
          rw [hcast] at h3
          have h4 := (hqi i hpos hi).1.2
          linarith
        · have h' : q (i + 1) = b := by rw [show i + 1 = N from heq]; exact hqN
          rw [h']
          have h4 := (hqi i hpos hi).1.2
          have : (i : ℝ) + 1 = N := by exact_mod_cast heq
          nlinarith
    · have h3 := hup (i + 1) hi
      rw [hcast] at h3
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hq0]; push_cast at h3; linarith
      · have h4 := (hqi i hpos hi).1.1
        linarith
  · constructor
    · rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hq0]
      · have := (hlow' i hi).1
        have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hpos
        nlinarith
    · have := hup i hi
      rcases lt_or_eq_of_le hi with hlt | rfl
      · have hi1 : (i : ℝ) + 1 ≤ N := by exact_mod_cast hlt
        nlinarith
      · rw [hqN]

private theorem exists_partition_of_cover {v w : ℝ} (hw : 0 < w) (hwv : w < v) {F : Set ℝ}
    (hF : F.Finite) (hwF : w ∉ F) (O : ℝ → Set ℝ) (hO : ∀ s ∈ Icc 0 v, IsOpen (O s) ∧ s ∈ O s) :
    ∃ (n : ℕ) (c : ℕ → ℝ), c 0 = 0 ∧ c n = v ∧ (∀ k < n, c k < c (k + 1)) ∧
      (∀ m, 0 < m → m < n → c m ∉ F) ∧ (∃ m, 0 < m ∧ m < n ∧ c m = w) ∧
      (∀ m ≤ n, c m ∈ Icc 0 v) ∧ (∀ k < n, ∃ s ∈ Icc 0 v, Icc (c k) (c (k + 1)) ⊆ O s) := by
  classical
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := (0 : ℝ)) (b := v))
    (c := fun i : Icc (0 : ℝ) v => O i) (fun i => (hO i i.2).1)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hO x hx).2⟩)
  obtain ⟨N₁, q₁, hN₁, hq₁0, hq₁N, hq₁s, hq₁F, hq₁I⟩ := exists_segment_partition hw hδ hF
  obtain ⟨N₂, q₂, hN₂, hq₂0, hq₂N, hq₂s, hq₂F, hq₂I⟩ := exists_segment_partition hwv hδ hF
  let c : ℕ → ℝ := fun m => if m ≤ N₁ then q₁ m else q₂ (m - N₁)
  have hc₁ : ∀ m ≤ N₁, c m = q₁ m := fun m hm => if_pos hm
  have hc₂ : ∀ m, N₁ ≤ m → c m = q₂ (m - N₁) := by
    intro m hm
    rcases eq_or_lt_of_le hm with rfl | hlt
    · rw [hc₁ _ le_rfl, hq₁N, Nat.sub_self, hq₂0]
    · exact if_neg (by omega)
  have hstep : ∀ k < N₁ + N₂, c k < c (k + 1) ∧ c (k + 1) - c k < δ := by
    intro k hk
    by_cases h : k < N₁
    · rw [hc₁ k h.le, hc₁ (k + 1) h]
      exact hq₁s k h
    · rw [hc₂ k (by omega), hc₂ (k + 1) (by omega), show k + 1 - N₁ = k - N₁ + 1 by omega]
      exact hq₂s _ (by omega)
  refine ⟨N₁ + N₂, c, ?_, ?_, fun k hk => (hstep k hk).1, ?_, ⟨N₁, hN₁, by omega, ?_⟩, ?_, ?_⟩
  · rw [hc₁ 0 (Nat.zero_le _), hq₁0]
  · rw [hc₂ _ (by omega), show N₁ + N₂ - N₁ = N₂ by omega, hq₂N]
  · intro m hm hmn
    by_cases h : m < N₁
    · rw [hc₁ m h.le]
      exact hq₁F m hm h
    by_cases h' : m = N₁
    · subst h'
      rw [hc₁ _ le_rfl, hq₁N]
      exact hwF
    · rw [hc₂ m (by omega)]
      exact hq₂F _ (by omega) (by omega)
  · rw [hc₁ _ le_rfl, hq₁N]
  · intro m hm
    by_cases h : m ≤ N₁
    · rw [hc₁ m h]
      exact Icc_subset_Icc le_rfl hwv.le (hq₁I m h)
    · rw [hc₂ m (by omega)]
      exact Icc_subset_Icc hw.le le_rfl (hq₂I _ (by omega))
  · intro k hk
    have hmem : c k ∈ Icc 0 v := by
      by_cases h : k ≤ N₁
      · rw [hc₁ k h]
        exact Icc_subset_Icc le_rfl hwv.le (hq₁I k h)
      · rw [hc₂ k (by omega)]
        exact Icc_subset_Icc hw.le le_rfl (hq₂I _ (by omega))
    obtain ⟨i, hi⟩ := hball (c k) hmem
    refine ⟨i, i.2, fun y hy => hi ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hy.1])]
    linarith [hy.2, (hstep k hk).2]

private theorem exists_contMDiff_eqOn {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    {γ : ℝ → X} {a b r : ℝ} (hab : a ≤ b) (hr : 0 < r)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ γ (Ioo (a - r) (b + r))) :
    ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ η ∧ EqOn η γ (Ioo (a - r / 2) (b + r / 2)) := by
  set m := (a + b) / 2 with hm
  let χ : ContDiffBump m := ⟨(b - a) / 2 + r / 2, (b - a) / 2 + r, by linarith, by linarith⟩
  let f : ℝ → ℝ := fun s => m + χ s * (s - m)
  have hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ f :=
    contMDiff_const.add (χ.contDiff.contMDiff.mul (contMDiff_id.sub contMDiff_const))
  have hfU (s : ℝ) : f s ∈ Ioo (a - r) (b + r) := by
    have hball : dist (f s) m < (b - a) / 2 + r := by
      by_cases hs : dist s m < (b - a) / 2 + r
      · change dist (m + χ s * (s - m)) m < _
        rw [Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_nonneg χ.nonneg]
        have hbound : χ s * |s - m| ≤ |s - m| :=
          (mul_le_mul_of_nonneg_right χ.le_one (abs_nonneg _)).trans_eq (one_mul _)
        exact hbound.trans_lt (by simpa only [Real.dist_eq] using hs)
      · have hχ : χ s = 0 := χ.zero_of_le_dist (not_lt.mp hs)
        simp only [f, hχ, zero_mul, add_zero, dist_self]
        linarith
    rw [Real.dist_eq, abs_lt] at hball
    constructor <;> linarith [hball.1, hball.2, hm]
  refine ⟨γ ∘ f, hγ.comp_contMDiff hf hfU, fun s hs => ?_⟩
  have hin : s ∈ Metric.closedBall m ((b - a) / 2 + r / 2) := by
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hs.1, hs.2, hm]
  change γ (m + χ s * (s - m)) = γ s
  rw [χ.one_of_mem_closedBall hin, one_mul, add_sub_cancel]

private theorem le_of_mem_stageDomain' {H : ObservedHistory.{u}} {j k : Fin (H.eventCount + 1)}
    {t t' : ℝ} (ht : t ∈ H.stageDomain j) (ht' : t' ∈ H.stageDomain k) (htt' : t ≤ t') :
    j ≤ k := by
  by_contra h
  have h1 := H.stageEndTime_le_time_of_lt (not_le.1 h)
  have h2 : t' < H.stageEndTime k := by
    cases k using Fin.lastCases with
    | last => exact absurd (not_le.1 h) (not_lt.2 (Fin.le_last j))
    | cast i =>
      simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht'
      rw [stageEndTime_castSucc]
      exact ht'.2
  linarith [H.time_le_of_mem_stageDomain ht]

private theorem mem_regularizedStage_Ioo' {H : ObservedHistory.{u}} {T a b r : ℝ} (ha : 0 ≤ a)
    (hr : r ∈ Ioo a b) {j : Fin (H.eventCount + 1)}
    (ht : T - r ^ 2 ∈ Ioo (H.time j) (H.stageEndTime j)) :
    r ∈ Ioo (H.regularizedStageStart T a j) (H.regularizedStageEnd T b j) := by
  have hr0 : 0 < r := ha.trans_lt hr.1
  have ha2 : a ^ 2 < r ^ 2 := pow_lt_pow_left₀ hr.1 ha two_ne_zero
  have hb2 : r ^ 2 < b ^ 2 := pow_lt_pow_left₀ hr.2 hr0.le two_ne_zero
  constructor
  · apply (Real.sqrt_lt' hr0).2
    have := lt_min (show T - r ^ 2 < T - a ^ 2 by linarith) ht.2
    linarith
  · apply (Real.lt_sqrt hr0.le).2
    have := max_lt (show T - b ^ 2 < T - r ^ 2 by linarith) ht.1
    linarith

end LWindowChain

variable {H : ObservedHistory.{u}}

private def PieceData {fst last : Fin (H.eventCount + 1)} (T v : ℝ)
    (α : (j : H.StageInterval fst last) → ℝ → (H.stage j.val).Carrier) (x y : ℝ) : Prop :=
  ∃ (lo hi : Fin (H.eventCount + 1)) (hlo : fst ≤ lo) (hhi : hi ≤ last) (W : H.LWindow lo hi T)
    (γ : ℝ → W.X), ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
    (∃ a b, a < x ∧ y < b ∧ IsLRegularizedGeodesicOn W.S T γ (Ioo a b)) ∧
    Icc x y ⊆ Icc W.a W.b ∧ (0 < x → W.a < x) ∧ (y < v → y < W.b) ∧
    (∀ j : H.StageInterval lo hi, EqOn (W.f j ∘ γ)
      (α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
      (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))) ∧
    (∀ j, T - y ^ 2 ∈ H.stageDomain j → lo ≤ j) ∧ (∀ j, T - x ^ 2 ∈ H.stageDomain j → j ≤ hi)

private theorem pieceData_of_window {first last fst : Fin (H.eventCount + 1)} (hfst : first ≤ fst)
    {T v : ℝ} {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    {lo hi : Fin (H.eventCount + 1)} (hlo : first ≤ lo) (hhi : hi ≤ last)
    (W : H.LWindow lo hi T) (γ : ℝ → W.X) {a₀ b₀ : ℝ}
    (hgeo : IsLRegularizedGeodesicOn W.S T γ (Ioo a₀ b₀))
    (heq : ∀ j : H.StageInterval lo hi, EqOn (W.f j ∘ γ)
      (α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
      (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)))
    {x y a' b' : ℝ} (hxy : x < y) (ha' : W.a ≤ a') (ha'x : a' ≤ x) (hx0 : 0 < x → a' < x)
    (hyb' : y < b') (hb' : b' ≤ W.b) (ha₀ : a₀ < a') (hb₀ : b' < b₀)
    {lo' hi' : Fin (H.eventCount + 1)} (hlo' : lo ≤ lo') (hhi' : hi' ≤ hi) (hle' : lo' ≤ hi')
    (hfst' : fst ≤ lo') (hup : T - a' ^ 2 ∈ H.stageDomain hi')
    (hdown : T - b' ^ 2 ∈ H.stageDomain lo') :
    PieceData T v (fun j : H.StageInterval fst last =>
      α ⟨j.val, hfst.trans j.property.1, j.property.2⟩) x y := by
  have hab' : a' < b' := ha'x.trans_lt (hxy.trans hyb')
  set r := min (a' - a₀) (b₀ - b') with hr
  have hr0 : 0 < r := lt_min (by linarith) (by linarith)
  have hsub : Ioo (a' - r) (b' + r) ⊆ Ioo a₀ b₀ := Ioo_subset_Ioo (by
    have := min_le_left (a' - a₀) (b₀ - b'); linarith) (by
    have := min_le_right (a' - a₀) (b₀ - b'); linarith)
  obtain ⟨η, hη, hηeq⟩ := LWindowChain.exists_contMDiff_eqOn hab'.le hr0
    ((hgeo.contMDiffOn W.solution isOpen_Ioo).mono hsub)
  let W' := W.restrict hlo' hhi' hle' ha' hab' hb' hup hdown
  have hsub' : Ioo (a' - r / 2) (b' + r / 2) ⊆ Ioo a₀ b₀ :=
    (Ioo_subset_Ioo (by linarith) (by linarith)).trans hsub
  refine ⟨lo', hi', hfst', hhi'.trans hhi, W', η, hη, ⟨a' - r / 2, b' + r / 2, by linarith,
    by linarith, ?_⟩, Icc_subset_Icc ha'x hyb'.le, fun hx => hx0 hx, fun _ => hyb', ?_, ?_, ?_⟩
  · have hg : IsLRegularizedGeodesicOn W.S T γ (Ioo (a' - r / 2) (b' + r / 2)) :=
      fun t ht => hgeo t (hsub' ht)
    exact hg.congr_of_eventuallyEq fun t ht =>
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun t' ht' => hηeq ht'
  · intro j t ht
    have htab : t ∈ Icc a' b' := W'.piece_subset j ht
    have hηt : η t = γ t := hηeq ⟨by linarith [htab.1], by linarith [htab.2]⟩
    have ht' : t ∈ Icc (H.regularizedStageStart T W.a j.val)
        (H.regularizedStageEnd T W.b j.val) :=
      ⟨(regularizedStageStart_le_of_le W.nonneg ha' j.val).trans ht.1,
        ht.2.trans (regularizedStageEnd_le_of_le ((W.nonneg.trans ha').trans hab'.le) hb' j.val)⟩
    change W.f ⟨j.val, hlo'.trans j.property.1, j.property.2.trans hhi'⟩ (η t) = _
    rw [hηt]
    exact heq ⟨j.val, hlo'.trans j.property.1, j.property.2.trans hhi'⟩ ht'
  · intro j hj
    have hy0 : 0 ≤ y := (W.nonneg.trans ha').trans (ha'x.trans hxy.le)
    exact LWindowChain.le_of_mem_stageDomain' hdown hj (by nlinarith)
  · intro j hj
    have hx0' : 0 ≤ a' := W.nonneg.trans ha'
    exact LWindowChain.le_of_mem_stageDomain' hj hup (by nlinarith)

private theorem exists_stage_of_le {fst last : Fin (H.eventCount + 1)} {T v b : ℝ}
    (hT : T ∈ H.stageDomain last) (hvf : H.time fst < T - v ^ 2) (hb : 0 ≤ b)
    (hbv : b ≤ v + min v ((T - v ^ 2 - H.time fst) / (4 * v))) (hv : 0 < v) :
    ∃ j, T - b ^ 2 ∈ H.stageDomain j ∧ fst ≤ j := by
  set ε := min v ((T - v ^ 2 - H.time fst) / (4 * v)) with hε
  have hε1 : ε ≤ v := min_le_left _ _
  have hε2 : ε ≤ (T - v ^ 2 - H.time fst) / (4 * v) := min_le_right _ _
  have hε2' : 4 * v * ε ≤ T - v ^ 2 - H.time fst := by
    rw [le_div_iff₀ (by positivity)] at hε2
    linarith
  have hεnn : 0 ≤ ε := le_min hv.le (div_nonneg (by linarith) (by positivity))
  have htime : H.time fst < T - b ^ 2 := by nlinarith
  have hTh : T ≤ H.horizon := (H.le_stageEndTime_of_mem_stageDomain hT).trans
    (H.stageEndTime_le_horizon last)
  have hmem : T - b ^ 2 ∈ Icc (0 : ℝ) H.horizon :=
    ⟨(H.time_nonneg fst).trans htime.le, by nlinarith [sq_nonneg b]⟩
  refine ⟨_, H.activeStage_mem ⟨_, hmem⟩, ?_⟩
  exact LWindowChain.le_of_mem_stageDomain' (H.time_mem_stageDomain fst)
    (H.activeStage_mem ⟨_, hmem⟩) htime.le

private theorem exists_cover {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    {T v₂ : ℝ} {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hgeo : H.IsHistoryLGeodesicOn hle T v₂ α) {p : (H.stage last).Carrier}
    {Z : TangentSpace ThreeModel p} (hZ : H.HasHistoryLInitialVector T α p Z)
    (hT : T ∈ H.stageDomain last) {v : ℝ} (hv : 0 < v) (hv₂ : v < v₂)
    {fst : Fin (H.eventCount + 1)} (hfst : first ≤ fst) (hvf : H.time fst < T - v ^ 2) :
    ∀ s ∈ Icc 0 v, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ ∀ x y, x < y → Icc x y ⊆ U →
      Icc x y ⊆ Icc 0 v → PieceData T v (fun j : H.StageInterval fst last =>
        α ⟨j.val, hfst.trans j.property.1, j.property.2⟩) x y := by
  set ε := min v ((T - v ^ 2 - H.time fst) / (4 * v)) with hε
  have hε0 : 0 < ε := lt_min hv (div_pos (by linarith) (by positivity))
  have hTh : T ≤ H.horizon := (H.le_stageEndTime_of_mem_stageDomain hT).trans
    (H.stageEndTime_le_horizon last)
  have hvT : 0 ≤ T - v ^ 2 := (H.time_nonneg fst).trans hvf.le
  intro s hs
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · subst hs0
    obtain ⟨lo₀, hlo₀, W₀, x₀, Zx, ha₀, -, -, hb₀, heq₀⟩ := hZ
    obtain ⟨α₂, J₂, hJo, hJc, h0J, hbJ, hcurve⟩ := hb₀
    have hgeo₀ : IsLRegularizedGeodesicOn W₀.S T (lRegularizedCurve W₀.S T x₀ Zx) J₂ :=
      hcurve.2.2.congr_of_eventuallyEq fun r hr => Filter.eventually_of_mem (hJo.mem_nhds hr)
        fun r' hr' => lRegularizedCurve_eqOn W₀.S W₀.solution T hJo hJc h0J hcurve hr'
    obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hJo 0 h0J
    have hb0 : 0 < W₀.b := ha₀ ▸ W₀.lt
    have hsubJ : Ioo (-r₁) W₀.b ⊆ J₂ := by
      intro t ht
      by_cases htr : t < r₁
      · apply hball
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
        exact ⟨ht.1, htr⟩
      · exact hJc.Icc_subset h0J hbJ ⟨by linarith, ht.2.le⟩
    refine ⟨Ioo (-r₁) W₀.b, isOpen_Ioo, ⟨by linarith, hb0⟩, fun x y hxy hU hI => ?_⟩
    have hx : 0 ≤ x := (hI (left_mem_Icc.2 hxy.le)).1
    have hyv : y ≤ v := (hI (right_mem_Icc.2 hxy.le)).2
    have hyb : y < W₀.b := (hU (right_mem_Icc.2 hxy.le)).2
    set b' := min ((y + W₀.b) / 2) (y + ε) with hb'
    have hb'y : y < b' := lt_min (by linarith) (by linarith)
    have hb'b : b' < W₀.b := (min_le_left _ _).trans_lt (by linarith)
    obtain ⟨lo', hlo'm, hfst'⟩ := exists_stage_of_le hT hvf (by linarith)
      ((min_le_right _ _).trans (by linarith)) hv
    have heq : ∀ j : H.StageInterval lo₀ last, EqOn (W₀.f j ∘ lRegularizedCurve W₀.S T x₀ Zx)
        (α ⟨j.val, hlo₀.trans j.property.1, j.property.2.trans le_rfl⟩)
        (Icc (H.regularizedStageStart T W₀.a j.val) (H.regularizedStageEnd T W₀.b j.val)) := by
      rw [ha₀]
      exact heq₀
    refine pieceData_of_window hfst hlo₀ le_rfl W₀ _ (fun t ht => hgeo₀ t (hsubJ ht)) heq hxy
      ha₀.le hx (fun h => h) hb'y hb'b.le (by linarith) hb'b
      (LWindowChain.le_of_mem_stageDomain' W₀.lower hlo'm (by nlinarith))
      le_rfl (LWindowChain.le_of_mem_stageDomain' hlo'm hT (by nlinarith)) hfst'
      (by simpa using hT) hlo'm
  · obtain ⟨lo, hi, hlo, hhi, W, hsW, -, γ, hγ, heqW⟩ := hgeo.2.2.1 s ⟨hs0, hs.2.trans_lt hv₂⟩
    refine ⟨Ioo W.a W.b, isOpen_Ioo, hsW, fun x y hxy hU hI => ?_⟩
    have hxv : x ≤ v := (hI (left_mem_Icc.2 hxy.le)).2
    have hyv : y ≤ v := (hI (right_mem_Icc.2 hxy.le)).2
    have hxa : W.a < x := (hU (left_mem_Icc.2 hxy.le)).1
    have hyb : y < W.b := (hU (right_mem_Icc.2 hxy.le)).2
    set a' := (W.a + x) / 2 with ha'
    set b' := min ((y + W.b) / 2) (y + ε) with hb'
    have hb'y : y < b' := lt_min (by linarith) (by linarith)
    have hb'b : b' < W.b := (min_le_left _ _).trans_lt (by linarith)
    have ha'0 : 0 ≤ a' := by linarith [W.nonneg]
    obtain ⟨lo', hlo'm, hfst'⟩ := exists_stage_of_le hT hvf (by linarith [W.nonneg])
      ((min_le_right _ _).trans (by linarith)) hv
    have hmem : T - a' ^ 2 ∈ Icc (0 : ℝ) H.horizon :=
      ⟨by nlinarith, by nlinarith [sq_nonneg a']⟩
    have hhi'm := H.activeStage_mem ⟨_, hmem⟩
    refine pieceData_of_window hfst hlo hhi W γ hγ heqW hxy (by linarith) (by linarith)
      (fun _ => by linarith) hb'y hb'b.le (by linarith) hb'b
      (LWindowChain.le_of_mem_stageDomain' W.lower hlo'm (by nlinarith [W.nonneg]))
      (LWindowChain.le_of_mem_stageDomain' hhi'm W.upper (by nlinarith [W.nonneg]))
      (LWindowChain.le_of_mem_stageDomain' hlo'm hhi'm (by nlinarith [W.nonneg]))
      hfst' hhi'm hlo'm

private theorem mem_Ioo_of_mem_stageDomain {j : Fin (H.eventCount + 1)} {t : ℝ}
    (ht : t ∈ H.stageDomain j) (hne : t ∉ range H.time) (hh : t < H.horizon) :
    t ∈ Ioo (H.time j) (H.stageEndTime j) := by
  refine ⟨lt_of_le_of_ne (H.time_le_of_mem_stageDomain ht) fun h => hne ⟨j, h⟩, ?_⟩
  cases j using Fin.lastCases with
  | last => rw [stageEndTime_last]; exact hh
  | cast i =>
    simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht
    rw [stageEndTime_castSucc]
    exact ht.2

theorem exists_lWindowChain {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    {T v₂ : ℝ} {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hgeo : H.IsHistoryLGeodesicOn hle T v₂ α) {p : (H.stage last).Carrier}
    {Z : TangentSpace ThreeModel p} (hZ : H.HasHistoryLInitialVector T α p Z)
    (hT : T ∈ H.stageDomain last) {v : ℝ} (hv : 0 < v) (hv₂ : v < v₂)
    {fst : Fin (H.eventCount + 1)} (hfst : first ≤ fst)
    (hvf : T - v ^ 2 ∈ Ioo (H.time fst) (H.stageEndTime fst)) {w : ℝ} (hw : 0 < w)
    (hwv : w < v) (hwF : T - w ^ 2 ∉ range H.time) :
    ∃ ch : H.LWindowChain T v (fun j : H.StageInterval fst last =>
      α ⟨j.val, hfst.trans j.property.1, j.property.2⟩), ∃ m, 0 < m ∧ m < ch.n ∧ ch.c m = w := by
  classical
  have hcov := exists_cover hle hgeo hZ hT hv hv₂ hfst hvf.1
  let O : ℝ → Set ℝ := fun s => if hs : s ∈ Icc 0 v then Classical.choose (hcov s hs) else univ
  have hO : ∀ s ∈ Icc 0 v, IsOpen (O s) ∧ s ∈ O s := fun s hs => by
    simp only [O, dif_pos hs]
    exact ⟨(Classical.choose_spec (hcov s hs)).1, (Classical.choose_spec (hcov s hs)).2.1⟩
  have hOP : ∀ s ∈ Icc 0 v, ∀ x y, x < y → Icc x y ⊆ O s → Icc x y ⊆ Icc 0 v →
      PieceData T v (fun j : H.StageInterval fst last =>
        α ⟨j.val, hfst.trans j.property.1, j.property.2⟩) x y := fun s hs => by
    simp only [O, dif_pos hs]
    exact (Classical.choose_spec (hcov s hs)).2.2
  have hwF' : w ∉ range (fun i => Real.sqrt (T - H.time i)) := by
    rintro ⟨i, hi⟩
    replace hi : Real.sqrt (T - H.time i) = w := hi
    apply hwF
    refine ⟨i, ?_⟩
    have hpos : 0 ≤ T - H.time i := by
      by_contra h
      rw [Real.sqrt_eq_zero'.2 (not_le.1 h).le] at hi
      linarith
    rw [← hi, Real.sq_sqrt hpos]
    ring
  obtain ⟨n, c, hc0, hcn, hlt, hcF, ⟨m, hm0, hmn, hcm⟩, hcI, hcO⟩ :=
    LWindowChain.exists_partition_of_cover hw hwv (Set.finite_range _) hwF' O hO
  have hpd : ∀ k, PieceData T v (fun j : H.StageInterval fst last =>
      α ⟨j.val, hfst.trans j.property.1, j.property.2⟩) (c (min k (n - 1)))
        (c (min k (n - 1) + 1)) := by
    intro k
    have hk : min k (n - 1) < n := (min_le_right _ _).trans_lt (by omega)
    obtain ⟨s, hs, hsub⟩ := hcO _ hk
    exact hOP s hs _ _ (hlt _ hk) hsub (Icc_subset_Icc (hcI _ hk.le).1 (hcI _ hk).2)
  choose lo hi hlo hhi W γ hγ hgeo' hpiece hxa hyb heq hstlo hsthi using hpd
  have hmin : ∀ k < n, min k (n - 1) = k := fun k hk => min_eq_left (by omega)
  have hTh : T ≤ H.horizon := (H.le_stageEndTime_of_mem_stageDomain hT).trans
    (H.stageEndTime_le_horizon last)
  have hvT : 0 ≤ T - v ^ 2 := (H.time_nonneg fst).trans hvf.1.le
  have hmemI : ∀ j ≤ n, T - c j ^ 2 ∈ Icc (0 : ℝ) H.horizon := fun j hj => by
    have h := hcI j hj
    constructor <;> nlinarith [h.1, h.2]
  let stg : ℕ → Fin (H.eventCount + 1) := fun j =>
    if j = 0 then last else if j = n then fst else
      if h : T - c j ^ 2 ∈ Icc (0 : ℝ) H.horizon then H.activeStage ⟨_, h⟩ else last
  have hstg : ∀ j (hj : 0 < j) (hjn : j < n), stg j = H.activeStage ⟨_, hmemI j hjn.le⟩ := by
    intro j hj hjn
    simp only [stg, if_neg hj.ne', if_neg hjn.ne, dif_pos (hmemI j hjn.le)]
  have hstgmem : ∀ j ≤ n, T - c j ^ 2 ∈ H.stageDomain (stg j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp only [stg, if_pos rfl, hc0]
      simpa using hT
    rcases eq_or_lt_of_le hj with rfl | hjn
    · simp only [stg, if_neg hpos.ne', hcn]
      exact H.mem_stageDomain_of_mem_Ioo hvf
    · rw [hstg j hpos hjn]
      exact H.activeStage_mem _
  refine ⟨
    { n := n, c := c, c_zero := hc0, c_n := hcn, lt := hlt, lo := lo, hi := hi
      first_le := hlo, le_last := hhi, W := W, γ := γ, geodesic := ?_, piece := ?_
      eqOn := ?_, contMDiff := hγ, stage := stg, stage_zero := (by simp [stg])
      stage_n := ?_, mem_stageDomain := hstgmem, lo_le_stage := ?_, stage_le_hi := ?_
      node := ?_ },
    m, hm0, hmn, hcm⟩
  · intro k hk
    have h := hgeo' k
    rw [hmin k hk] at h
    exact h
  · intro k hk
    have h := hpiece k
    rw [hmin k hk] at h
    exact h
  · intro k _ j
    exact heq k j
  · show stg n = fst
    simp [stg, show n ≠ 0 by omega]
  · intro k hk
    have h := hstlo k
    rw [hmin k hk] at h
    exact h _ (hstgmem (k + 1) hk)
  · intro k hk
    have h := hsthi k
    rw [hmin k hk] at h
    exact h _ (hstgmem k hk.le)
  · intro k hk
    have hk' : k < n := by omega
    have hmono : ∀ i j, i < j → j ≤ n → c i < c j := by
      intro i j hij hjn
      induction j with
      | zero => omega
      | succ j ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
        · exact (ih h (by omega)).trans (hlt j (by omega))
        · exact hlt i (by omega)
    have hpos : 0 < c (k + 1) := hc0 ▸ hmono 0 (k + 1) (by omega) hk.le
    have hcv : c (k + 1) < v := hcn ▸ hmono (k + 1) n hk le_rfl
    have hT' : T - c (k + 1) ^ 2 < H.horizon := by nlinarith
    have hne : T - c (k + 1) ^ 2 ∉ range H.time := by
      rintro ⟨i, hi⟩
      apply hcF (k + 1) (by omega) hk
      refine ⟨i, ?_⟩
      change Real.sqrt (T - H.time i) = c (k + 1)
      rw [hi, show T - (T - c (k + 1) ^ 2) = c (k + 1) ^ 2 by ring, Real.sqrt_sq hpos.le]
    have hIoo := mem_Ioo_of_mem_stageDomain (hstgmem (k + 1) hk.le) hne hT'
    have p₁ := hpiece k
    have p₂ := hpiece (k + 1)
    have y₁ := hyb k
    have x₂ := hxa (k + 1)
    rw [hmin k hk'] at p₁ y₁
    rw [hmin (k + 1) hk] at p₂ x₂
    refine ⟨LWindowChain.mem_regularizedStage_Ioo' (W k).nonneg ⟨?_, y₁ hcv⟩ hIoo,
      LWindowChain.mem_regularizedStage_Ioo' (W (k + 1)).nonneg ⟨x₂ hpos, ?_⟩ hIoo⟩
    · exact (p₁ (left_mem_Icc.2 (hlt k hk').le)).1.trans_lt (hlt k hk')
    · exact (hlt (k + 1) hk).trans_le (p₂ (right_mem_Icc.2 (hlt (k + 1) hk).le)).2

section Minimizer

variable {first last fst : Fin (H.eventCount + 1)} {hle : first ≤ last} {T B v₂ v : ℝ}
  {β : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}

private theorem truncate_facts (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hgeo : H.IsHistoryLGeodesicOn hle T v₂ β)
    (hac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (β j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₂ j.val))
    (hmin : H.regularizedExtendedAction first last T B 0 v₂ β =
      H.regularizedCost first last hle T B 0 v₂ (β ⟨last, hle, le_rfl⟩ 0)
        (β ⟨first, le_rfl, hle⟩ v₂))
    (hfin : H.regularizedExtendedAction first last T B 0 v₂ β ≠ ⊤) (hv : 0 < v) (hv₂ : v ≤ v₂)
    (hfst : first ≤ fst) (hfl : fst ≤ last) (hvk : T - v ^ 2 ∈ H.stageDomain fst) :
    (∀ j : H.StageInterval fst last, Manifold.absolutelyContinuousOnInterval ThreeModel
      (β ⟨j.val, hfst.trans j.property.1, j.property.2⟩)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ∧
    H.regularizedExtendedAction fst last T B 0 v
        (fun j => β ⟨j.val, hfst.trans j.property.1, j.property.2⟩) =
      H.regularizedCost fst last hfl T B 0 v (β ⟨last, hle, le_rfl⟩ 0)
        (β ⟨fst, hfst, hfl⟩ v) := by
  refine ⟨fun j => ?_, (regularizedExtendedAction_truncate_eq_regularizedCost hle hfst hfl hv.le
    hv₂ hvk hfloor β hac (fun i hf hl => ?_) hmin hfin).1⟩
  · have hne : (H.regularizedActionValues first last hle T B 0 v₂ (β ⟨last, hle, le_rfl⟩ 0)
        (β ⟨first, le_rfl, hle⟩ v₂)).Nonempty := by
      by_contra h
      exact hfin (hmin.trans (H.regularizedCost_eq_top_of_no_competitor first last hle T B 0 v₂
        _ _ (not_nonempty_iff_eq_empty.1 h)))
    obtain ⟨A, -, -, hupper, hlower, -⟩ := hne
    apply Manifold.absolutelyContinuousOnInterval_mono (hac _)
    have hb := H.regularizedStage_bounds le_rfl hv.le hupper hvk j
    have hb₂ := H.regularizedStage_bounds le_rfl (hv.le.trans hv₂) hupper hlower
      ⟨j.val, hfst.trans j.property.1, j.property.2⟩
    rw [uIcc_of_le hb.2.1, uIcc_of_le hb₂.2.1]
    exact Icc_subset_Icc le_rfl (regularizedStageEnd_le_of_le hv.le hv₂ j.val)
  · obtain ⟨z, -, h1, h2⟩ := hgeo.2.1 i hf hl
    exact ⟨z, h1, h2⟩

theorem LWindowChain.historyLIndex_nonneg_of_minimizer
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hgeo : H.IsHistoryLGeodesicOn hle T v₂ β)
    (hac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (β j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₂ j.val))
    (hmin : H.regularizedExtendedAction first last T B 0 v₂ β =
      H.regularizedCost first last hle T B 0 v₂ (β ⟨last, hle, le_rfl⟩ 0)
        (β ⟨first, le_rfl, hle⟩ v₂))
    (hfin : H.regularizedExtendedAction first last T B 0 v₂ β ≠ ⊤) (hv : 0 < v) (hv₂ : v ≤ v₂)
    (hfst : first ≤ fst) (hfl : fst ≤ last) (hvk : T - v ^ 2 ∈ H.stageDomain fst)
    (ch : H.LWindowChain T v (fun j : H.StageInterval fst last =>
      β ⟨j.val, hfst.trans j.property.1, j.property.2⟩)) (V : ch.Field)
    (hV : ∀ k < ch.n, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent 8 (fun t => (Bundle.TotalSpace.mk'
      ThreeSpace (E := (TangentSpace ThreeModel : (ch.W k).X → Type _)) (ch.γ k t) (V k t) :
        TangentBundle ThreeModel (ch.W k).X)))
    (hVg : ch.IsGlued V) (hV0 : V 0 0 = 0) (hVv : V (ch.n - 1) v = 0) :
    0 ≤ ch.historyLIndex V V := by
  obtain ⟨hac', hmin'⟩ := truncate_facts hfloor hgeo hac hmin hfin hv hv₂ hfst hfl hvk
  have hn : 0 < ch.n := Nat.pos_of_ne_zero fun h => by
    have := ch.c_n
    rw [h, ch.c_zero] at this
    linarith
  exact ch.historyLIndex_nonneg hn hfl hfloor hac' hmin' V hV hVg hV0 hVv

theorem LWindowChain.eqOn_zero_of_conjugate_of_minimizer
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hgeo : H.IsHistoryLGeodesicOn hle T v₂ β)
    (hac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (β j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₂ j.val))
    (hmin : H.regularizedExtendedAction first last T B 0 v₂ β =
      H.regularizedCost first last hle T B 0 v₂ (β ⟨last, hle, le_rfl⟩ 0)
        (β ⟨first, le_rfl, hle⟩ v₂))
    (hfin : H.regularizedExtendedAction first last T B 0 v₂ β ≠ ⊤) (hv : 0 < v) (hv₂ : v ≤ v₂)
    (hfst : first ≤ fst) (hfl : fst ≤ last) (hvk : T - v ^ 2 ∈ H.stageDomain fst)
    (ch : H.LWindowChain T v (fun j : H.StageInterval fst last =>
      β ⟨j.val, hfst.trans j.property.1, j.property.2⟩)) {k₀ : ℕ} (hk₀ : k₀ + 1 < ch.n)
    (J : ch.Field)
    (hJs : ∀ k ≤ k₀, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ (fun t => (Bundle.TotalSpace.mk'
      ThreeSpace (E := (TangentSpace ThreeModel : (ch.W k).X → Type _)) (ch.γ k t) (J k t) :
        TangentBundle ThreeModel (ch.W k).X)))
    (hJj : ∀ k ≤ k₀, ∃ a b, a < ch.c k ∧ ch.c (k + 1) < b ∧
      IsLRegularizedJacobi (ch.W k).S T (ch.γ k) (J k) (Ioo a b))
    (hJg : ∀ k (hk : k + 1 < ch.n), k + 1 ≤ k₀ →
      ch.GluedAt J hk ∧ ch.GluedAt (ch.covDerivField J) hk)
    (hJ0 : J 0 0 = 0) (hJ1 : J k₀ (ch.c (k₀ + 1)) = 0) :
    ∀ k ≤ k₀, ∀ s ∈ Icc (ch.c k) (ch.c (k + 1)), J k s = 0 := by
  obtain ⟨hac', hmin'⟩ := truncate_facts hfloor hgeo hac hmin hfin hv hv₂ hfst hfl hvk
  exact ch.eqOn_zero_of_conjugate hfl hfloor hac' hmin' hk₀ J hJs hJj hJg hJ0 hJ1

end Minimizer

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
