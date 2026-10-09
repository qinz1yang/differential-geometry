import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgerySepEventSG2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryStaticSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckChartBandNK

/-!
# R3（G3′，第 2 部分）：window 版——`U ⊆ ι_s '' interior KD`（S-A14-SURGERY-2）

event 层的分离（`SurgerySepEventSG2.lean`）搬到 window 上。window = `Fs = i.castSucc`、
`Ls = i.succ`（tight window：`s < τ₀ ⇒ activeStage s = Fs`；event 时刻 `τ₀ = time i.succ`）。

* `sliceHomeo_SG2`：`(stage i.castSucc).Carrier ≃ₜ (postStage T s).Carrier`
  （`activeStage s = i.castSucc`）；
* `windowEmbed_eq_SG2`：`ι_s = sliceHomeo ∘ Φ_{i.castSucc}`；
* `range_backwardSurvivorMap_SG2`：`range Φ_{i.castSucc} = {RegularCrossing 源点}`；
* **`exists_window_separation_SG2`**：`∃ KD ⊆ D` 紧（不依赖 `s`），`∀ s ∈ J`（`activeStage s = i.castSucc`），
  `∃ U V ⊆ M_s` 开不交，`M_s ∖ ⋃_b sliceHomeo '' Σ_b ⊆ U ∪ V`，`U ⊆ ι_s '' interior KD`，
  且 `range ι_s` 里不碰 `sliceHomeo '' N_b` 的点都在 `U` 里（`γ_s ⊆ U` 的判据）；
* `window_stages_eq_of_event_SG2`：tight window 在 event 时刻 `τ₀ = time i.succ` 处 `Fs = i.castSucc`、
  `Ls = i.succ`。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

section Window

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g) (N : ℕ)
  (i : Fin (T.history N).eventCount)

/-- window 的 slice 恒等：`activeStage s = i.castSucc` 时
`(stage i.castSucc).Carrier ≃ₜ (postStage s).Carrier`。 -/
def sliceHomeo_SG2 (s : ℝ) (hs0 : 0 ≤ s) (hsh : s ≤ (T.history N).horizon)
    (hact : (T.history N).activeStage ⟨s, hs0, hsh⟩ = i.castSucc) :
    ((T.history N).stage i.castSucc).Carrier ≃ₜ (postStage T s).Carrier :=
  carrierHomeo_CPD2 ((congrArg (T.history N).stage hact).symm.trans
    (postStage_eq_stage_active_CPD2 T N ⟨s, hs0, hsh⟩).symm)

variable (hFL : i.castSucc ≤ i.succ) (J : Set ℝ)
  (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
  (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
    i.castSucc ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧
      (T.history N).activeStage ⟨t, h0, h1⟩ ≤ i.succ)

/-- `ι_s = sliceHomeo ∘ Φ_{i.castSucc}`（`activeStage s = i.castSucc`）。 -/
theorem windowEmbed_eq_SG2 (s : ℝ) (hs : s ∈ J)
    (hact : (T.history N).activeStage ⟨s, (hJh s hs).1, (hJh s hs).2⟩ = i.castSucc)
    (w : (T.history N).backwardSurvivorDomain i.castSucc i.succ hFL) :
    windowEmbed_SG T N i.castSucc i.succ hFL J hJh hst s hs w =
      sliceHomeo_SG2 T N i s (hJh s hs).1 (hJh s hs).2 hact
        ((T.history N).backwardSurvivorMap i.castSucc i.succ hFL i.castSucc le_rfl hFL w) := by
  have key : ∀ (j : Fin ((T.history N).eventCount + 1)) (hj : j = i.castSucc)
      (h1 : i.castSucc ≤ j) (h2 : j ≤ i.succ) (e1 : postStage T s = (T.history N).stage j)
      (e2 : (T.history N).stage i.castSucc = postStage T s),
      carrierHomeo_CPD2 e1.symm
        ((T.history N).backwardSurvivorMap i.castSucc i.succ hFL j h1 h2 w) =
        carrierHomeo_CPD2 e2
          ((T.history N).backwardSurvivorMap i.castSucc i.succ hFL i.castSucc le_rfl hFL w) := by
    intro j hj
    subst hj
    intros
    rfl
  exact key _ hact _ _ (postStage_eq_stage_active_CPD2 T N ⟨s, (hJh s hs).1, (hJh s hs).2⟩)
    ((congrArg (T.history N).stage hact).symm.trans
      (postStage_eq_stage_active_CPD2 T N ⟨s, (hJh s hs).1, (hJh s hs).2⟩).symm)

/-- `range Φ_{i.castSucc}` = `RegularCrossing` 源点
（`D = backwardSurvivorDomain i.castSucc i.succ`）。 -/
theorem range_backwardSurvivorMap_SG2 :
    range ((T.history N).backwardSurvivorMap i.castSucc i.succ hFL i.castSucc le_rfl hFL) =
      {x | ∃ q, ((T.history N).event i).RegularCrossing x q} := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    have h := (T.history N).backwardSurvivorMap_crossing i.castSucc i.succ hFL i le_rfl le_rfl w
    exact ⟨_, h⟩
  · rintro ⟨q, hq⟩
    let A := BackwardPointTrace.singleton (T.history N) i.succ q
    have hcross : ((T.history N).event i).RegularCrossing x (A.point i.succ le_rfl le_rfl) := hq
    refine ⟨⟨q, ⟨A.prepend x hcross⟩⟩, ?_⟩
    rw [(T.history N).backwardSurvivorMap_eq_point i.castSucc i.succ hFL i.castSucc le_rfl hFL
      ⟨q, ⟨A.prepend x hcross⟩⟩ (A.prepend x hcross)]
    exact BackwardPointTrace.prepend_point_first A x hcross

variable {p : CutoffParameters}

/-- **R3（window 版）**：晚期 event `i` 的 record `R`（`∀ b, δ_s⁻¹ > 100`）。存在紧 `KD ⊆ D`（与 `s` 无关），
`∀ s ∈ J`（`activeStage s = i.castSucc`，即 tight window 的 `s < τ₀`）：开不交 `U V ⊆ M_s`，
`M_s ∖ ⋃_b e_s '' Σ_b ⊆ U ∪ V`，`U ⊆ ι_s '' interior KD`；`range ι_s` 里不碰 `e_s '' N_b` 的点都在 `U` 里。
这里 `e_s = sliceHomeo_SG2`，`Σ_b = {z_s = 50}`、`N_b = {0 ≤ z_s ≤ 50}`。 -/
theorem exists_window_separation_SG2 (R : GeometricCutoffRecord (T.history N) i p)
    (hcol : ∀ b : ((T.history N).event i).RetainedBoundaryIndex,
      100 < ((R.static b).delta)⁻¹) :
    ∃ KD : Set ((T.history N).backwardSurvivorDomain i.castSucc i.succ hFL), IsCompact KD ∧
      ∀ (s : ℝ) (hs : s ∈ J)
        (hact : (T.history N).activeStage ⟨s, (hJh s hs).1, (hJh s hs).2⟩ = i.castSucc),
        ∃ U V : Set (postStage T s).Carrier, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
          U ⊆ windowEmbed_SG T N i.castSucc i.succ hFL J hJh hst s hs '' interior KD ∧
          (∀ x, (∀ b, x ∉ sliceHomeo_SG2 T N i s (hJh s hs).1 (hJh s hs).2 hact ''
              neckSlab_SG2 R b {50}) → x ∈ U ∪ V) ∧
          ∀ x ∈ range (windowEmbed_SG T N i.castSucc i.succ hFL J hJh hst s hs),
            (∀ b, x ∉ sliceHomeo_SG2 T N i s (hJh s hs).1 (hJh s hs).2 hact ''
              neckSlab_SG2 R b (Icc 0 50)) → x ∈ U := by
  obtain ⟨K, U, V, hKc, hKreg, hUo, hVo, hUV, hUK, hsep, hcrit⟩ :=
    exists_event_separation_SG2 R hcol
  set Φ := (T.history N).backwardSurvivorMap i.castSucc i.succ hFL i.castSucc le_rfl hFL with hΦ
  have hemb : Topology.IsOpenEmbedding Φ :=
    isOpenEmbedding_survivorMap_CPD7 (T.history N) i.castSucc i.succ hFL i.castSucc le_rfl hFL
  have hrange : range Φ = {x | ∃ q, ((T.history N).event i).RegularCrossing x q} :=
    range_backwardSurvivorMap_SG2 T N i hFL
  have hKr : K ⊆ range Φ := fun x hx => by rw [hrange]; exact hKreg x hx
  refine ⟨Φ ⁻¹' K, hemb.isEmbedding.isInducing.isCompact_preimage' hKc hKr, ?_⟩
  intro s hs hact
  set e := sliceHomeo_SG2 T N i s (hJh s hs).1 (hJh s hs).2 hact with he
  have hι : ∀ w, windowEmbed_SG T N i.castSucc i.succ hFL J hJh hst s hs w = e (Φ w) :=
    fun w => windowEmbed_eq_SG2 T N i hFL J hJh hst s hs hact w
  have hUint : U ⊆ Φ '' interior (Φ ⁻¹' K) := by
    intro u hu
    have huK : u ∈ K := interior_subset (hUK hu)
    obtain ⟨w, rfl⟩ := hKr huK
    refine ⟨w, ?_, rfl⟩
    have h1 : Φ ⁻¹' interior K ⊆ interior (Φ ⁻¹' K) :=
      interior_maximal (preimage_mono interior_subset) (isOpen_interior.preimage hemb.continuous)
    exact h1 (hUK hu)
  refine ⟨e '' U, e '' V, e.isOpenMap _ hUo, e.isOpenMap _ hVo,
    (Set.disjoint_image_iff e.injective).2 hUV, ?_, ?_, ?_⟩
  · have : windowEmbed_SG T N i.castSucc i.succ hFL J hJh hst s hs '' interior (Φ ⁻¹' K) =
        e '' (Φ '' interior (Φ ⁻¹' K)) := by
      rw [image_image]
      exact image_congr fun w _ => hι w
    rw [this]
    exact image_mono hUint
  · intro x hx
    have h1 : e.symm x ∈ U ∪ V := hsep _ fun b hb => hx b ⟨_, hb, e.apply_symm_apply x⟩
    rcases h1 with h | h
    · exact Or.inl ⟨_, h, e.apply_symm_apply x⟩
    · exact Or.inr ⟨_, h, e.apply_symm_apply x⟩
  · rintro x ⟨w, rfl⟩ hx
    rw [hι]
    refine ⟨Φ w, hcrit _ ((Set.ext_iff.1 hrange _).1 (mem_range_self w)) fun b hb => ?_, rfl⟩
    rw [hι] at hx
    exact hx b ⟨_, hb, rfl⟩

end Window

section Stages

/-- tight window 在 event 时刻 `τ₀ = time i.succ`：`Fs = i.castSucc`、`Ls = i.succ`（`exists_tpw_SG` 的
`hleft`/`hright` 子句；`J` 开）。 -/
theorem window_stages_eq_of_event_SG2 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {Fs Ls : Fin (H.eventCount + 1)} {J : Set ℝ} (hJo : IsOpen J)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ H.horizon) (hτJ : H.time i.succ ∈ J)
    (hleft : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ H.horizon), t ∈ J → t < H.time i.succ →
      H.activeStage ⟨t, h0, h1⟩ = Fs)
    (hright : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ H.horizon), t ∈ J → H.time i.succ ≤ t →
      H.activeStage ⟨t, h0, h1⟩ = Ls) :
    Fs = i.castSucc ∧ Ls = i.succ := by
  refine ⟨?_, (hright _ (H.time_nonneg _) (H.time_le_horizon_at _) hτJ le_rfl).symm.trans
    (H.activeStage_at_time i.succ)⟩
  obtain ⟨l, u, ⟨hl, hu⟩, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJo.mem_nhds hτJ)
  have hlt : H.time i.castSucc < H.time i.succ := H.time_strictMono i.castSucc_lt_succ
  set t : ℝ := max (H.time i.castSucc) ((l + H.time i.succ) / 2) with ht
  have htτ : t < H.time i.succ := max_lt hlt (by linarith)
  have htJ : t ∈ J := hIoo ⟨by
    have := le_max_right (H.time i.castSucc) ((l + H.time i.succ) / 2)
    linarith, htτ.trans hu⟩
  obtain ⟨h0, h1⟩ := hJh t htJ
  rw [← hleft t h0 h1 htJ htτ]
  apply le_antisymm
  · apply Fin.le_castSucc_iff.2
    exact H.time_strictMono.lt_iff_lt.1
      (lt_of_le_of_lt (H.activeStage_time_le ⟨t, h0, h1⟩) htτ)
  · exact H.le_activeStage ⟨t, h0, h1⟩ _ (le_max_left _ _)

/-- `τ₀ ∈ T.eventTimes`、`τ₀ ≤ N` ⇒ `history N` 里有 event `i` 在 `τ₀`
（`eventTimes_mono`/`integer_restrict`）。 -/
theorem exists_event_index_SG2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) {τ₀ : ℝ} (hτ : τ₀ ∈ T.eventTimes) (N : ℕ) (hN : τ₀ ≤ N) :
    ∃ i : Fin (T.history N).eventCount, (T.history N).time i.succ = τ₀ := by
  obtain ⟨n, hn⟩ := mem_iUnion.1 hτ
  rcases le_total n N with h | h
  · obtain ⟨i, hi⟩ := T.eventTimes_mono n N h hn
    exact ⟨i, hi⟩
  · have R := T.integer_restrict N n h
    have hτ' : τ₀ ∈ (T.atIndex n N (Nat.cast_nonneg N) (by exact_mod_cast h)).eventTimes := by
      rw [T.atIndex_eventTimes]
      exact ⟨hn, T.eventTimes_pos hτ, hN⟩
    obtain ⟨i, hi⟩ := hτ'
    have he := R.time_eq i.succ
    change _ = (T.history N).time (Fin.cast R.count_eq i).succ at he
    exact ⟨Fin.cast R.count_eq i, he.symm.trans hi⟩

/-- tight window（`hleft`/`hright`）在 event 时刻 `τ₀ ∈ T.eventTimes`：存在 event `i`，
`time i.succ = τ₀`、`Fs = i.castSucc`、`Ls = i.succ`。 -/
theorem window_event_stages_SG2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) (N : ℕ) {τ₀ : ℝ} (hτ : τ₀ ∈ T.eventTimes)
    {Fs Ls : Fin ((T.history N).eventCount + 1)} {J : Set ℝ} (hJo : IsOpen J)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon) (hτJ : τ₀ ∈ J)
    (hleft : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J → t < τ₀ →
      (T.history N).activeStage ⟨t, h0, h1⟩ = Fs)
    (hright : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J → τ₀ ≤ t →
      (T.history N).activeStage ⟨t, h0, h1⟩ = Ls) :
    ∃ i : Fin (T.history N).eventCount, (T.history N).time i.succ = τ₀ ∧
      Fs = i.castSucc ∧ Ls = i.succ := by
  have hN : τ₀ ≤ N := by
    have := (hJh τ₀ hτJ).2
    rwa [T.horizon_eq] at this
  obtain ⟨i, hi⟩ := exists_event_index_SG2 T hτ N hN
  subst hi
  exact ⟨i, rfl, window_stages_eq_of_event_SG2 (T.history N) i hJo hJh hτJ hleft hright⟩

end Stages

section Middle

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- c5 的 `(N b, Z b)` 形：`N b := e '' range c`、`Z b y := chartHeight c (e.symm y) - 50`，
`{y ∈ N b | Z b y = 0}` 恰是 `e '' (c '' {z = 50})`。 -/
theorem mem_cutSphere_of_middle_SG2 (e : X ≃ₜ Y) {δ : ℝ} (c : neckBuffer δ → X)
    (hc : Function.Injective c) {y : Y} (hN : y ∈ e '' range c)
    (hZ : chartHeight_NK c (e.symm y) - 50 = 0) :
    y ∈ e '' (c '' {y' | y'.1.2 ∈ ({50} : Set ℝ)}) := by
  obtain ⟨_, ⟨y', rfl⟩, rfl⟩ := hN
  rw [e.symm_apply_apply, chartHeight_chart_NK hc] at hZ
  exact ⟨c y', ⟨y', by simpa [sub_eq_zero] using hZ, rfl⟩, rfl⟩

end Middle

end GC.LongTime.CuspP1
