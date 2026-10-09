import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HconfCutSphereIM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.TransportedNonnegIM6

/-!
# G13 的 `hγ` ⇐ ⑧（collar 负标量曲率）+ `N_b` 上 `R ≥ 0` + cusp collar ⊆ `range ι_s`（O-W-IMS06 G14）

`hγ` 的第二合取项（`γ_s θ ∉ e_s '' N_b`）由 G10 `transported_not_mem_of_scalar_nonneg_IM6` 给出；
剩下三条显式前提：`hrange`（cusp collar 在 survivor domain 的像里，window 的 static identification）、
`hneg`（collar 上 `R_post < 0`，`cores.metric_error`）、`hRN`（`e_s '' N_b` 上 `R_post ≥ 0`，neck closeness
覆盖整段 `{0 ≤ z_s ≤ 50}`）。consumer：`hleftE` ⇐ `hcut` + `hrange` + `hneg` + `hRN`。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G14 主定理**：`hrange` + `hneg` + `hRN` ⇒ G13 的 `hγ`。 -/
theorem hgamma_of_scalar_IM6 {δ : ℝ → ℝ} (pr : AnalyticSurgeryProfile F δ)
    (M : PrescribedCuspMeridianTop_CPQ cores)
    (hrange : ∃ T₃ : ℝ, ∀ (N : ℕ) (i : Fin (F.observation.history N).eventCount)
      (hFL : i.castSucc ≤ i.succ)
      (J : Set ℝ) (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
      (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
        i.castSucc ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
          (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ i.succ)
      (s : ℝ) (hsJ : s ∈ J), (F.observation.history N).activeStage
        ⟨s, (hJh s hsJ).1, (hJh s hsJ).2⟩ = i.castSucc →
      ∀ (hs : M.exterior.start ≤ s), T₃ ≤ s → ∀ θ : loopCircle,
        M.transported s hs θ ∈ range (windowEmbed_SG F.observation N i.castSucc i.succ hFL J hJh hst
          s hsJ))
    (hneg : ∃ T₄ : ℝ, ∀ (s : ℝ) (hs : M.exterior.start ≤ s), T₄ ≤ s →
      ∀ p ∈ cores.map M.model s (M.exterior.after_cores.trans hs) ''
        riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
          (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) p < 0)
    (hRN : ∃ T₅ : ℝ, ∀ (N : ℕ) (i : Fin (F.observation.history N).eventCount) (s : ℝ)
      (h0 : 0 ≤ s) (h1 : s ≤ (F.observation.history N).horizon)
      (hact : (F.observation.history N).activeStage ⟨s, h0, h1⟩ = i.castSucc), T₅ ≤ s →
      ∀ (b : ((F.observation.history N).event i).RetainedBoundaryIndex),
        ∀ p ∈ sliceHomeo_SG2 F.observation N i s h0 h1 hact ''
          neckSlab_SG2 (pr.records N i) b (Icc 0 50),
          0 ≤ metricScalarAt (postMetric F.observation s) p) :
    ∃ T₃ : ℝ, ∀ (N : ℕ) (i : Fin (F.observation.history N).eventCount)
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
            hact '' neckSlab_SG2 (pr.records N i) b (Icc 0 50) := by
  obtain ⟨T₃, hr⟩ := hrange
  obtain ⟨T₄, hn⟩ := hneg
  obtain ⟨T₅, hR⟩ := hRN
  refine ⟨max T₃ (max T₄ T₅), fun N i hFL J hJh hst s hsJ hact hs hT θ => ⟨?_, ?_⟩⟩
  · exact hr N i hFL J hJh hst s hsJ hact hs ((le_max_left _ _).trans hT) θ
  · exact transported_not_mem_of_scalar_nonneg_IM6 M hs
      (hn s hs (((le_max_left _ _).trans (le_max_right _ _)).trans hT))
      (fun b => sliceHomeo_SG2 F.observation N i s (hJh s hsJ).1 (hJh s hsJ).2 hact ''
        neckSlab_SG2 (pr.records N i) b (Icc 0 50))
      (hR N i s (hJh s hsJ).1 (hJh s hsJ).2 hact
        (((le_max_right _ _).trans (le_max_right _ _)).trans hT)) θ

/-- consumer：G14 ⇒ G13 ⇒ G12 ⇒ G3：O-W-ASSEMBLY 的 `hleftE` ⇐ `hcut` + `hrange` + `hneg` + `hRN`。 -/
example {δ : ℝ → ℝ} (pr : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (M : PrescribedCuspMeridianTop_CPQ cores) :=
  fun hcut hrange hneg hRN => ht_left_at_event_IM6 M (hpkt_of_tight_window_IM6 M
    (hconfT_of_cut_sphere_IM6 pr hdec M hcut (hgamma_of_scalar_IM6 pr M hrange hneg hRN)))

end GC.LongTime.CuspP1
