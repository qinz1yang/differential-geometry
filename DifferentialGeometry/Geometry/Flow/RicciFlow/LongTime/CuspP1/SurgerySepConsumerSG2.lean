import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgerySepWindowSG2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.SurvivorConfinementIM6

/-!
# R3 的 consumer：分离 + 中间球面排除 ⇒ 盘落在 `ι_s '' interior KD`（S-A14-SURGERY-2）

`exists_window_separation_SG2` 的 `(KD, U, V)` 喂给 O-W-IMS06 的
`confined_in_survivor_of_neck_exclusion_IM6`
（`(N b, Z b) := (e '' range chart_b, chartHeight chart_b ∘ e.symm - 50)`，其中
`{y ∈ N b | Z b y = 0} = e '' Σ_b`）。`hγ`（`γ_s` 在 `range ι_s` 且不碰 `e '' N_b`）与 `hNK`（盘不碰
中间球面）是显式前提，分别由 ⑧ `transported_not_mem_band_IM6`（collar `R < 0` vs slab `R > 0`）与 S-W-NECK
G4/G5 供给。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

example {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g) (N : ℕ)
    (i : Fin (T.history N).eventCount) {p : CutoffParameters}
    (R : GeometricCutoffRecord (T.history N) i p)
    (hcol : ∀ b : ((T.history N).event i).RetainedBoundaryIndex, 100 < ((R.static b).delta)⁻¹)
    (hFL : i.castSucc ≤ i.succ) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
      i.castSucc ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧
        (T.history N).activeStage ⟨t, h0, h1⟩ ≤ i.succ) :
    ∃ KD : Set ((T.history N).backwardSurvivorDomain i.castSucc i.succ hFL), IsCompact KD ∧
      ∀ (s : ℝ) (hs : s ∈ J)
        (hact : (T.history N).activeStage ⟨s, (hJh s hs).1, (hJh s hs).2⟩ = i.castSucc)
        (v : C(closedDisk, (postStage T s).Carrier)) (γ : freeLoop (postStage T s).Carrier),
        DiskWeakJordanTrace γ v →
        (∀ θ, γ θ ∈ range (windowEmbed_SG T N i.castSucc i.succ hFL J hJh hst s hs) ∧
          ∀ b, γ θ ∉ sliceHomeo_SG2 T N i s (hJh s hs).1 (hJh s hs).2 hact ''
            neckSlab_SG2 R b (Icc 0 50)) →
        (∀ b ζ, ¬ (v ζ ∈ sliceHomeo_SG2 T N i s (hJh s hs).1 (hJh s hs).2 hact ''
            range (fun y => ((R.static b).neck.chart y).1) ∧
          chartHeight_NK (fun y => ((R.static b).neck.chart y).1)
            ((sliceHomeo_SG2 T N i s (hJh s hs).1 (hJh s hs).2 hact).symm (v ζ)) - 50 = 0)) →
        range v ⊆ windowEmbed_SG T N i.castSucc i.succ hFL J hJh hst s hs '' interior KD := by
  obtain ⟨KD, hKD, h⟩ := exists_window_separation_SG2 T N i hFL J hJh hst R hcol
  refine ⟨KD, hKD, fun s hs hact v γ htr hγ hNK => ?_⟩
  obtain ⟨U, V, hUo, hVo, hUV, hUK, hsep, hcrit⟩ := h s hs hact
  set e := sliceHomeo_SG2 T N i s (hJh s hs).1 (hJh s hs).2 hact with he
  have hinj : ∀ b : ((T.history N).event i).RetainedBoundaryIndex,
      Function.Injective (fun y => ((R.static b).neck.chart y).1) := fun b =>
    Subtype.val_injective.comp (neck_chart_isOpenEmbedding_SG (R.static b).neck).injective
  refine confined_in_survivor_of_neck_exclusion_IM6
    (ι := ((T.history N).event i).RetainedBoundaryIndex) v
    (fun b => e '' range (fun y => ((R.static b).neck.chart y).1))
    (fun b y => chartHeight_NK (fun y => ((R.static b).neck.chart y).1) (e.symm y) - 50)
    hUo hVo hUV (fun x hx => hsep x fun b hb => hx b ?_) hUK
    (fun θ => hcrit _ (hγ θ).1 (hγ θ).2) htr hNK
  obtain ⟨_, ⟨y', hy', rfl⟩, rfl⟩ := hb
  refine ⟨⟨_, ⟨y', rfl⟩, rfl⟩, ?_⟩
  rw [e.symm_apply_apply, chartHeight_chart_NK (hinj b)]
  have : y'.1.2 = 50 := hy'
  linarith

/-- consumer 2：对接 `exists_tpw_SG` 的 tight window 数据（`hleft`/`hright`/`hst`）与 analytic profile 的
`records`：event 时刻 `τ₀ ∈ F.observation.eventTimes` ⇒ 找到 event `i`（`Fs = i.castSucc`，
`Ls = i.succ`）并给出 `KD`、分离 `(U, V)`（`pr.records N i` 供切割系统）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (pr : AnalyticSurgeryProfile F δ) (N : ℕ) {τ₀ : ℝ} (hτ : τ₀ ∈ F.observation.eventTimes)
    {Fs Ls : Fin ((F.observation.history N).eventCount + 1)} (hFL : Fs ≤ Ls) {J : Set ℝ}
    (hJo : IsOpen J) (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
      Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
        (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    (hτJ : τ₀ ∈ J)
    (hleft : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J → t < τ₀ →
      (F.observation.history N).activeStage ⟨t, h0, h1⟩ = Fs)
    (hright : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J → τ₀ ≤ t →
      (F.observation.history N).activeStage ⟨t, h0, h1⟩ = Ls)
    (hcol : ∀ (i : Fin (F.tower.history N).eventCount)
      (b : ((F.tower.history N).toHistory.event i).RetainedBoundaryIndex),
      (F.tower.history N).toHistory.time i.succ = τ₀ →
        100 < (((pr.records N i).static b).delta)⁻¹) :
    ∃ i : Fin (F.observation.history N).eventCount, (F.observation.history N).time i.succ = τ₀ ∧
      Fs = i.castSucc ∧ Ls = i.succ ∧
        ∃ KD : Set ((F.observation.history N).backwardSurvivorDomain Fs Ls hFL), IsCompact KD ∧
          ∀ (s : ℝ) (hs : s ∈ J)
            (hact : (F.observation.history N).activeStage ⟨s, (hJh s hs).1, (hJh s hs).2⟩ =
              i.castSucc),
            ∃ U V : Set (postStage F.observation s).Carrier, IsOpen U ∧ IsOpen V ∧
              Disjoint U V ∧ U ⊆ windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s hs ''
                interior KD ∧
              ∀ x, (∀ b, x ∉ sliceHomeo_SG2 F.observation N i s (hJh s hs).1 (hJh s hs).2 hact ''
                neckSlab_SG2 (pr.records N i) b {50}) → x ∈ U ∪ V := by
  obtain ⟨i, hi, hF, hL⟩ := window_event_stages_SG2 F.observation N hτ hJo hJh hτJ hleft hright
  subst hF
  subst hL
  refine ⟨i, hi, rfl, rfl, ?_⟩
  obtain ⟨KD, hKD, h⟩ := exists_window_separation_SG2 F.observation N i hFL J hJh hst
    (pr.records N i) (fun b => hcol i b (hi.trans rfl))
  refine ⟨KD, hKD, fun s hs hact => ?_⟩
  obtain ⟨U, V, hUo, hVo, hUV, hUK, hsep, -⟩ := h s hs hact
  exact ⟨U, V, hUo, hVo, hUV, hUK, hsep⟩

end GC.LongTime.CuspP1
