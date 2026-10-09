import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWAssemblyWA8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.WindowDataFluxST2

/-!
# Route W 端到端组装（O-W-ASSEMBLY-2 G8b，后缀 `_WA9`）

相对 G8（`RouteWAssemblyWA8.lean`）：`hwin` 由 S-A14-STATIC-2 G1 `window_data_flux_of_no_event_ST2`
（STATIC G6 window 数据 + `hvel`：`Φ` 在 `γ_{t₀}` 上的 `t₀`-速度 `√g(W,W)·√t₀ < acc t₀`）对 Top `M`
的字段实例化直接给出，barrier 分支（IMS09′）因此**无剩余义务**。

剩余显式义务只剩 `hconfW`（D-R3-6 公共紧控制，surgery 时刻左侧；本车道 G9 总装：R3 + c9 + ⑧ + ⑥）。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.MinimalSurface DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

/-- **Route W 主组装定理（G8b）**：A11 风格前提 + `H` + `hconfW`（唯一显式义务）。 -/
theorem hasAttainedExteriorAreaObstructionAfter_of_routeW_WA9
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (hconfW : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (τ₀ : ℝ), M.exterior.start < τ₀ → T₁ ≤ τ₀ → τ₀ ∈ F.observation.eventTimes →
      ∀ (N : ℕ) (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls)
        (J : Set ℝ) (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
        (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
          Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
            (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls),
        τ₀ ∈ J →
        (∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J → t < τ₀ →
          (F.observation.history N).activeStage ⟨t, h0, h1⟩ = Fs) →
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
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) :=
  hasAttainedExteriorAreaObstructionAfter_of_routeW_WA8 K hK δ H hdec L j hj C
    (fun M _ ht₀ hreg => window_data_flux_of_no_event_ST2 L.cores M.exterior M.model M.port
      M.loop M.transported M.prescribed ht₀ hreg) hconfW

/-- consumer：`.toObstruction`（`hasLateSequenceTests_of_thick_thin_and_obstruction` 的 producer 格）。 -/
theorem hasExteriorAreaObstructionAfter_of_routeW_WA9
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (hconfW : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (τ₀ : ℝ), M.exterior.start < τ₀ → T₁ ≤ τ₀ → τ₀ ∈ F.observation.eventTimes →
      ∀ (N : ℕ) (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls)
        (J : Set ℝ) (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
        (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
          Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
            (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls),
        τ₀ ∈ J →
        (∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J → t < τ₀ →
          (F.observation.history N).activeStage ⟨t, h0, h1⟩ = Fs) →
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
    hasExteriorAreaObstructionAfter F (L.decomposition j C) :=
  (hasAttainedExteriorAreaObstructionAfter_of_routeW_WA9 K hK δ H hdec L j hj C
    hconfW).toObstruction

end GC.LongTime.CuspP1
