import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HtLeftPacketTightIM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgerySepWindowSG2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryNeckSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.SurvivorConfinementIM6

/-!
# `hconfT` ⇐ 切割球面上的 IMS06′ + 边界环在存活侧（O-W-IMS06 G13，后缀 `_IM6`）

把 G12 的 `hconfT`（tight window 上的公共紧控制）用 S-A14-SURGERY-2 G3′ 的真定理展开：
`window_event_stages_SG2`（⇒ `Fs = i.castSucc`、`Ls = i.succ`）+ `exists_window_separation_SG2`
（`pr.records N i`，`hcol` 由 `exists_late_collar_SG pr hdec`）给与 `s` 无关的紧 `KD` 与每个 `s` 的 `U V`；
c5 的拓扑核心 `range_subset_of_separation_IM6`（G2）。剩余显式前提只有两条（均对晚期 `s`、每个 `_HC2` 盘）：
* `hcut`：IMS06′ 在切割球面上——盘不碰 `e_s '' Σ_b`（`Σ_b = neckSlab (pr.records N i) b {50}`，
  原 neck 坐标 `z = ±51`）；产出 = c3（G9）+ NECK G4 + band（中心 z_s = 50）+ G8 缩放；
* `hγ`：`γ_s` 在 `range ι_s` 里且不碰 `e_s '' N_b`（`N_b = neckSlab … (Icc 0 50)`）；产出 = G10（`hneg`
  + `N_b` 上 `R ≥ 0`）+ cusp collar ⊆ survivor domain。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G13 主定理**：`hcut` + `hγ`（+ `pr`、`hdec`）⇒ G12 的 `hconfT`。 -/
theorem hconfT_of_cut_sphere_IM6 {δ : ℝ → ℝ} (pr : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (M : PrescribedCuspMeridianTop_CPQ cores)
    (hcut : ∃ T₂ : ℝ, ∀ (N : ℕ) (i : Fin (F.observation.history N).eventCount) (s : ℝ)
      (h0 : 0 ≤ s) (h1 : s ≤ (F.observation.history N).horizon)
      (hact : (F.observation.history N).activeStage ⟨s, h0, h1⟩ = i.castSucc)
      (hs : M.exterior.start ≤ s), T₂ ≤ s →
            ∀ (U : TopologicalSpace.Opens (postStage F.observation s).Carrier)
              (G : SmoothRiemannianMetric (𝓡 3) U) (γU : freeLoop U) (q : C(closedDisk, U)),
              IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
              IsMorreyDisk G γU q →
              (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
                G.inner y = ((postMetric F.observation s).restrictOpen U).inner y) →
              DiskWeakJordanTrace (M.transported s hs)
                ((⟨Subtype.val, continuous_subtype_val⟩ :
                  C(U, (postStage F.observation s).Carrier)).comp q) →
              range ((⟨Subtype.val, continuous_subtype_val⟩ :
                C(U, (postStage F.observation s).Carrier)).comp q) ⊆ M.exterior.region s →
              (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
                ((⟨Subtype.val, continuous_subtype_val⟩ :
                  C(U, (postStage F.observation s).Carrier)).comp q) z ∈
                  interior (M.exterior.region s)) →
              (∀ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q →
                ∀ z ∈ Metric.ball (0 : ℂ) 1,
                  Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z)) →
              ∀ (b : ((F.observation.history N).event i).RetainedBoundaryIndex)
                (ζ : closedDisk),
                ((⟨Subtype.val, continuous_subtype_val⟩ :
                  C(U, (postStage F.observation s).Carrier)).comp q) ζ ∉
                  sliceHomeo_SG2 F.observation N i s h0 h1 hact ''
                    neckSlab_SG2 (pr.records N i) b {50})
    (hγ : ∃ T₃ : ℝ, ∀ (N : ℕ) (i : Fin (F.observation.history N).eventCount)
      (hFL : i.castSucc ≤ i.succ)
      (J : Set ℝ) (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
      (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
        i.castSucc ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
          (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ i.succ)
      (s : ℝ) (hsJ : s ∈ J)
      (hact : (F.observation.history N).activeStage ⟨s, (hJh s hsJ).1, (hJh s hsJ).2⟩ =
        i.castSucc)
      (hs : M.exterior.start ≤ s), T₃ ≤ s → ∀ θ : loopCircle,
        M.transported s hs θ ∈ range (windowEmbed_SG F.observation N i.castSucc i.succ hFL J hJh hst
          s hsJ) ∧
        ∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex,
          M.transported s hs θ ∉ sliceHomeo_SG2 F.observation N i s (hJh s hsJ).1 (hJh s hsJ).2
            hact '' neckSlab_SG2 (pr.records N i) b (Icc 0 50)) :
    ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (τ₀ : ℝ), M.exterior.start < τ₀ → T₁ ≤ τ₀ → τ₀ ∈ F.observation.eventTimes →
      ∀ (N : ℕ) (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls)
        (J : Set ℝ) (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
        (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
          Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
            (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls),
        IsOpen J → τ₀ ∈ J →
        (∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J → t < τ₀ →
          (F.observation.history N).activeStage ⟨t, h0, h1⟩ = Fs) →
        (∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J → τ₀ ≤ t →
          (F.observation.history N).activeStage ⟨t, h0, h1⟩ = Ls) →
        ∃ KD : Set ((F.observation.history N).backwardSurvivorDomain Fs Ls hFL), IsCompact KD ∧
          ∃ η₀ > (0 : ℝ), ∀ (s : ℝ) (hs : M.exterior.start ≤ s) (hsJ : s ∈ J),
            τ₀ - η₀ < s → s < τ₀ →
            ∀ (U : TopologicalSpace.Opens (postStage F.observation s).Carrier)
              (G : SmoothRiemannianMetric (𝓡 3) U) (γU : freeLoop U) (q : C(closedDisk, U)),
              IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
              IsMorreyDisk G γU q →
              (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
                G.inner y = ((postMetric F.observation s).restrictOpen U).inner y) →
              DiskWeakJordanTrace (M.transported s hs)
                ((⟨Subtype.val, continuous_subtype_val⟩ :
                  C(U, (postStage F.observation s).Carrier)).comp q) →
              range ((⟨Subtype.val, continuous_subtype_val⟩ :
                C(U, (postStage F.observation s).Carrier)).comp q) ⊆ M.exterior.region s →
              (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
                ((⟨Subtype.val, continuous_subtype_val⟩ :
                  C(U, (postStage F.observation s).Carrier)).comp q) z ∈
                  interior (M.exterior.region s)) →
              (∀ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q →
                ∀ z ∈ Metric.ball (0 : ℂ) 1,
                  Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z)) →
              range ((⟨Subtype.val, continuous_subtype_val⟩ :
                C(U, (postStage F.observation s).Carrier)).comp q) ⊆
                windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s hsJ '' interior KD := by
  obtain ⟨B, hB⟩ := exists_late_collar_SG pr hdec
  obtain ⟨T₂, hcut⟩ := hcut
  obtain ⟨T₃, hγ⟩ := hγ
  refine ⟨max M.exterior.start (max (B + 1) (max (T₂ + 1) (T₃ + 1))), le_max_left _ _,
    fun τ₀ _ hT hE N Fs Ls hFL J hJh hst hJo hτJ hleft hright => ?_⟩
  have hTB : B + 1 ≤ τ₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hT2 : T₂ + 1 ≤ τ₀ :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hT
  have hT3 : T₃ + 1 ≤ τ₀ :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hT
  obtain ⟨i, hi, hF, hL⟩ := window_event_stages_SG2 F.observation N hE hJo hJh hτJ hleft hright
  subst hF
  subst hL
  obtain ⟨KD, hKD, hsepW⟩ := exists_window_separation_SG2 F.observation N i hFL J hJh hst
    (pr.records N i) (fun b => hB N i b
      (lt_of_lt_of_le (by linarith : B < τ₀) (le_of_eq hi.symm)))
  refine ⟨KD, hKD, 1, one_pos, fun s hs hsJ hlo hhi => ?_⟩
  have hact := hleft s (hJh s hsJ).1 (hJh s hsJ).2 hsJ hhi
  obtain ⟨U', V', hUo, hVo, hUV, hUK, hsep, hcrit⟩ := hsepW s hsJ hact
  intro U G γU q hsm hMor hloc htr hW hint himm
  have hS := hcut N i s (hJh s hsJ).1 (hJh s hsJ).2 hact hs (by linarith) U G γU q hsm hMor hloc
    htr hW hint himm
  obtain ⟨ζ₀, hζ₀⟩ := exists_boundary_mem_of_weakTrace_IM6 htr (U := U') fun θ =>
    hcrit _ (hγ N i hFL J hJh hst s hsJ hact hs (by linarith) θ).1
      (hγ N i hFL J hJh hst s hsJ hact hs (by linarith) θ).2
  refine (range_subset_of_separation_IM6 _ hUo hVo hUV
    (S := {x | ∃ b, x ∈ sliceHomeo_SG2 F.observation N i s (hJh s hsJ).1 (hJh s hsJ).2 hact ''
      neckSlab_SG2 (pr.records N i) b {50}})
    (fun x hx => hsep x fun b hb => hx ⟨b, hb⟩) (fun ζ ⟨b, hb⟩ => hS b ζ hb) hζ₀).trans hUK

/-- consumer：G13 ⇒ G12 ⇒ G3：O-W-ASSEMBLY 的 `hleftE` ⇐ `hcut` + `hγ`（+ `pr`、`hdec`）。 -/
example {δ : ℝ → ℝ} (pr : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (M : PrescribedCuspMeridianTop_CPQ cores) :=
  fun hcut hγ => ht_left_at_event_IM6 M
    (hpkt_of_tight_window_IM6 M (hconfT_of_cut_sphere_IM6 pr hdec M hcut hγ))

end GC.LongTime.CuspP1
