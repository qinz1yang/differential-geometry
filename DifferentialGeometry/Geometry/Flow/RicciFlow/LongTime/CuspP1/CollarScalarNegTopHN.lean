import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CollarScalarNegHN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.TransportedBandSignIM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HgammaScalarIM6

/-!
# ⑧ 的 `hneg`：`∃ T₁` 版 + `PrescribedCuspMeridianTop_CPQ` consumer（O-W-HNEG G2，后缀 `_HN`）

G1 `scalar_neg_on_collar_of_accuracy_HN`（`acc s ≤ 1/2000` ⇒ collar 上 `R_post < 0`）+
`cores.accuracy_decay`（ε = 1/2000）⇒ `∃ T₁, ∀ s ≥ T₁`（对所有 `i`、`hs` 一致）。Top 版的形状与
IMS06 G14 `hgamma_of_scalar_IM6` 的 `hneg` 前提**逐字**一致，所以 ASSEMBLY 的 `hleftE` 链
（G14 ⇒ G13 ⇒ G12 ⇒ G3）里 `hneg` 被消去，只剩 `hcut` + `hrange` + `hRN`。
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

universe u

namespace GC.LongTime

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- **G2 `eventually_scalar_neg_on_collar_HN`**：`∃ T₁`，对所有 `s ≥ T₁`、所有 core `i`，
cusp collar `f_s '' ball` 上 `R_{g(s)} < 0`（G1 + `accuracy_decay`，ε₀ = 1/2000）。 -/
theorem PersistentHyperbolicCores.eventually_scalar_neg_on_collar_HN
    (cores : PersistentHyperbolicCores F K) :
    ∃ T₁ : ℝ, ∀ (i : Fin cores.count) (s : ℝ) (hs : cores.start ≤ s), T₁ ≤ s →
      ∀ p ∈ cores.map i s hs '' riemannianBallOf (cores.model i).metric
        (cores.model i).basepoint (cores.accuracy s)⁻¹,
        metricScalarAt (postMetric F.observation s) p < 0 := by
  obtain ⟨T, hT⟩ := cores.accuracy_decay (1 / 2000) (by norm_num)
  exact ⟨T, fun i s hs hTs => cores.scalar_neg_on_collar_of_accuracy_HN i hs (hT s hTs).le⟩

end GC.LongTime

namespace GC.LongTime.CuspP1

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G2 Top 版**：`M.model`、`M.exterior.after_cores.trans hs` 的 `hneg`，`∃ T₁` 形
（= IMS06 G14 `hgamma_of_scalar_IM6` 的 `hneg` 前提）。 -/
theorem PrescribedCuspMeridianTop_CPQ.eventually_scalar_neg_on_collar_HN
    (M : PrescribedCuspMeridianTop_CPQ cores) :
    ∃ T₁ : ℝ, ∀ (s : ℝ) (hs : M.exterior.start ≤ s), T₁ ≤ s →
      ∀ p ∈ cores.map M.model s (M.exterior.after_cores.trans hs) ''
        riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
          (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) p < 0 := by
  obtain ⟨T₁, hT⟩ := cores.eventually_scalar_neg_on_collar_HN
  exact ⟨T₁, fun s hs hTs => hT M.model s (M.exterior.after_cores.trans hs) hTs⟩

/-- consumer（G1 ⇒ IMS06 G7）：`acc s ≤ 1/2000` 时 `γ_s` 不进 band 闭包，只剩 band 上 `R ≥ 0`。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) {s : ℝ} (hs : M.exterior.start ≤ s)
    (hacc : cores.accuracy s ≤ 1 / 2000)
    {ι : Type*} (N : ι → Set (postStage F.observation s).Carrier)
    (Z : ι → (postStage F.observation s).Carrier → ℝ)
    (hR : ∀ b, ∀ p ∈ N b, |Z b p| < 20 → 0 ≤ metricScalarAt (postMetric F.observation s) p)
    (b : ι) (θ : loopCircle) :
    M.transported s hs θ ∉ closure {p | p ∈ N b ∧ |Z b p| < 20} :=
  transported_not_mem_band_nonneg_IM6 M hs
    (cores.scalar_neg_on_collar_of_accuracy_HN M.model (M.exterior.after_cores.trans hs) hacc)
    N Z hR b θ

/-- consumer（G2 ⇒ IMS06 G7 `transported_not_mem_band_nonneg_IM6`）：`s ≥ T₁` 时 `hneg` 自动成立。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) {ι : Type*} :
    ∃ T₁ : ℝ, ∀ (s : ℝ) (hs : M.exterior.start ≤ s), T₁ ≤ s →
      ∀ (N : ι → Set (postStage F.observation s).Carrier)
        (Z : ι → (postStage F.observation s).Carrier → ℝ),
        (∀ b, ∀ p ∈ N b, |Z b p| < 20 → 0 ≤ metricScalarAt (postMetric F.observation s) p) →
        ∀ (b : ι) (θ : loopCircle),
          M.transported s hs θ ∉ closure {p | p ∈ N b ∧ |Z b p| < 20} := by
  obtain ⟨T₁, hT⟩ := M.eventually_scalar_neg_on_collar_HN
  exact ⟨T₁, fun s hs hTs N Z hR b θ =>
    transported_not_mem_band_nonneg_IM6 M hs (hT s hs hTs) N Z hR b θ⟩

/-- consumer（G2 ⇒ IMS06 G10 `transported_not_mem_of_scalar_nonneg_IM6`）。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) {ι : Type*} :
    ∃ T₁ : ℝ, ∀ (s : ℝ) (hs : M.exterior.start ≤ s), T₁ ≤ s →
      ∀ (S : ι → Set (postStage F.observation s).Carrier),
        (∀ b, ∀ p ∈ S b, 0 ≤ metricScalarAt (postMetric F.observation s) p) →
        ∀ θ : loopCircle, ∀ b, M.transported s hs θ ∉ S b := by
  obtain ⟨T₁, hT⟩ := M.eventually_scalar_neg_on_collar_HN
  exact ⟨T₁, fun s hs hTs S hS θ =>
    transported_not_mem_of_scalar_nonneg_IM6 M hs (hT s hs hTs) S hS θ⟩

/-- consumer（G2 ⇒ IMS06 G14 ⇒ G13 ⇒ G12 ⇒ G3）：ASSEMBLY 的 `hleftE` ⇐ `hcut` + `hrange` + `hRN`
（`hneg` 已消去）。 -/
example {δ : ℝ → ℝ} (pr : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (M : PrescribedCuspMeridianTop_CPQ cores) :=
  fun hcut hrange hRN => ht_left_at_event_IM6 M (hpkt_of_tight_window_IM6 M
    (hconfT_of_cut_sphere_IM6 pr hdec M hcut
      (hgamma_of_scalar_IM6 pr M hrange M.eventually_scalar_neg_on_collar_HN hRN)))

end GC.LongTime.CuspP1
