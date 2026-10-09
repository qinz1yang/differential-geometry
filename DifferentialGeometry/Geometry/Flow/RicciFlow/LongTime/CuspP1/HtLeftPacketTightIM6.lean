import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HtLeftPacketIM6

/-!
# G11 的 tight-window 加强接口（O-W-IMS06 G12，后缀 `_IM6`）

G11 `hpkt_of_window_IM6` 的 `hconfW` 只对窗口给 `τ₀ ∈ J` 与左 tight 子句；S-A14-SURGERY-2 G3′ 的
`window_event_stages_SG2`（⇒ `∃ i, Fs = i.castSucc ∧ Ls = i.succ`，`exists_window_separation_SG2` 的输入）
还要 `IsOpen J` 与右 tight 子句。本文件 `hpkt_of_tight_window_IM6` 的 `hconfT` 多给这两条（前提更弱，
更容易产出），证明从 `exists_tpw_Top_WA` 一并取出。G11 保留。
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

/-- **left packet（tight window 版）**：`hconfT`（窗口另给 `IsOpen J` 与右 tight 子句）⇒ G3 的 `hpkt`。 -/
theorem hpkt_of_tight_window_IM6 (M : PrescribedCuspMeridianTop_CPQ cores)
    (hconfT : ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
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
                windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s hsJ '' interior KD) :
    ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ → t₀ ∈ F.observation.eventTimes →
      ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ (s : ℝ) (hs : M.exterior.start ≤ s), T₁ ≤ s →
        t₀ - η < s → s < t₀ →
        ∃ (K₀ : Set (postStage F.observation s).Carrier)
          (φ : (postStage F.observation s).Carrier → (postStage F.observation t₀).Carrier),
          IsOpen K₀ ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K₀ ∧
          MapsTo φ (K₀ ∩ M.exterior.region s) (M.exterior.region t₀) ∧
          (∀ θ, φ (M.transported s hs θ) = M.transported t₀ ht₀ θ) ∧
          (∀ p ∈ K₀, ∀ w : TangentSpace (𝓡 3) p,
            (postMetric F.observation t₀).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
              Real.exp ε * (postMetric F.observation s).inner p w w) ∧
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
              ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z)) →
            range ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) ⊆ K₀ := by
  obtain ⟨T₁, hT₁, hC⟩ := hconfT
  refine ⟨max T₁ (M.exterior.start + 1), hT₁.trans (le_max_left _ _),
    fun τ₀ hτ₀ hT hE ε hε => ?_⟩
  have hτ₀' : M.exterior.start < τ₀ :=
    lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hT)
  obtain ⟨N, Fs, Ls, hFL, J, hJh, hst, hτJ, a, b, hJab, hτab, hEab, Φ, C, ha, -, hJo, ⟨w₀⟩, -,
    -, -, -, -, hleft, hright, hKD⟩ := exists_tpw_Top_WA cores M hτ₀'
  obtain ⟨KD, hKDc, η₀, hη₀, hconf⟩ :=
    hC τ₀ hτ₀' ((le_max_left _ _).trans hT) hE N Fs Ls hFL J hJh hst hJo hτJ hleft hright
  obtain ⟨η, hη, hmet⟩ := hKD KD hKDc ε hε
  refine ⟨min (min η η₀) (τ₀ - a), lt_min (lt_min hη hη₀) (by linarith), fun s hs _ hlo hhi => ?_⟩
  have h1 : s - τ₀ > -η := by linarith [min_le_left (min η η₀) (τ₀ - a), min_le_left η η₀]
  have h2 : τ₀ - η₀ < s := by
    linarith [min_le_left (min η η₀) (τ₀ - a), min_le_right η η₀]
  have h3 : a < s := by linarith [min_le_right (min η η₀) (τ₀ - a)]
  have hsab : s ∈ Icc a b := ⟨h3.le, (hhi.trans_le hτab.2).le⟩
  have habs : |s - τ₀| < η := by
    rw [abs_lt]
    constructor <;> linarith
  obtain ⟨hopen, hsmooth, hmaps, htrans, hmetric⟩ := hmet s hsab hhi habs w₀
  refine ⟨_, _, hopen, hsmooth, hmaps, htrans, fun p hp w => hmetric p
    (image_mono interior_subset hp) w, ?_⟩
  intro U G γU q hsm hMor hloc htr hW hint himm
  exact hconf s hs (hJab hsab) h2 hhi U G γU q hsm hMor hloc htr hW hint himm

/-- consumer：tight 版输出喂 G3，得到 O-W-ASSEMBLY 的 `hleftE`。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) :=
  fun hconfT => ht_left_at_event_IM6 M (hpkt_of_tight_window_IM6 M hconfT)

end GC.LongTime.CuspP1
