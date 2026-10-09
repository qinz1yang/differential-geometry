import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWAssemblyWA6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.HbarWTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HtLeftPacketIM6

/-!
# Route W 端到端组装（O-W-ASSEMBLY-2 G8，后缀 `_WA8`）

相对 G6（`RouteWAssemblyWA6.lean`）的两次收缩：

* `hbarW` ⇐ **`hwin`**：O-W-CURV G4 `PrescribedCuspMeridianTop_CPQ.hbarW_of_window_flux_CV`
  （`∫k − f < π` 的 Top 合成，曲率常数 1，flux `|f| ≤ acc·√(1+acc)·L`）。`hwin` = S-A14-STATIC-2 G1
  `window_data_flux_of_no_event_ST` 对 Top `M` 的结论形（`window_data_of_no_event_ST` + `hvel`：
  `Φ` 在 `γ_{t₀}` 上的 `t`-速度 `√g(W,W)·√t₀ < acc t₀`）。
* `hpkt` ⇐ **`hconfW`**：O-W-IMS06 G11 `hpkt_of_window_IM6`（TPW 五字段由 `exists_tpw_Top_WA` 消去）。
  `hconfW` = D-R3-6 公共紧控制：对任意 tight window，`∃ KD` 紧（与 `s` 无关）`∃ η₀`，`s ↑ τ₀` 时每个
  `_HC2` 形 Morrey 盘的像 `⊆ ι_s '' interior KD`。

剩余显式义务：`hwin`（STATIC-2 G1）、`hconfW`（本车道下一组：R3 + c9 + ⑧ + ⑥ 的总装）。
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

/-- **Route W 主组装定理（G8）**：A11 风格前提 + `H` + `hwin`（window-flux）+ `hconfW`（公共紧控制）。 -/
theorem hasAttainedExteriorAreaObstructionAfter_of_routeW_WA8
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (hwin : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∀ {t₀ : ℝ}
      (ht₀ : M.exterior.start < t₀), t₀ ∉ F.observation.eventTimes →
      ∃ (I : Set ℝ) (D : RealTimeInterval)
        (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
        (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (postStage F.observation t₀).Carrier),
        IsOpen I ∧ t₀ ∈ I ∧ MetricFamilySmoothOn D G ∧ D.regular ∈ 𝓝 t₀ ∧
        G t₀ = postMetric F.observation t₀ ∧
        (∀ t ∈ I, ∀ (x : (postStage F.observation t₀).Carrier) (A B : TangentSpace ThreeModel x),
          HasDerivAt (fun r : ℝ => (G r).inner x A B)
            (-2 * ricciTensor (I := ThreeModel) (G t) x A B) t) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) ∧
        Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ ∧
        (∀ s : ℝ,
          Real.sqrt ((postMetric F.observation t₀).inner (loopLift (M.transported t₀ ht₀.le) s)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀.le) s))
                t₀ 1)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀.le) s))
                t₀ 1)) * Real.sqrt t₀ < L.cores.accuracy t₀) ∧
        ∀ t ∈ I, ∀ ht : M.exterior.start ≤ t,
          ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (postStage F.observation t).Carrier,
            G t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
            (∀ θ, ι (Φ t (M.transported t₀ ht₀.le θ)) = M.transported t ht θ) ∧
            (fun p => ι (Φ t p)) '' M.exterior.region t₀ = M.exterior.region t)
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
  hasAttainedExteriorAreaObstructionAfter_of_routeW_WA6 K hK δ H hdec L j hj C
    (fun M => M.hbarW_of_window_flux_CV (hwin M)) (fun M => hpkt_of_window_IM6 M (hconfW M))

/-- consumer：`.toObstruction`（`hasLateSequenceTests_of_thick_thin_and_obstruction` 的 producer 格）。 -/
theorem hasExteriorAreaObstructionAfter_of_routeW_WA8
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (hwin : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores, ∀ {t₀ : ℝ}
      (ht₀ : M.exterior.start < t₀), t₀ ∉ F.observation.eventTimes →
      ∃ (I : Set ℝ) (D : RealTimeInterval)
        (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
        (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (postStage F.observation t₀).Carrier),
        IsOpen I ∧ t₀ ∈ I ∧ MetricFamilySmoothOn D G ∧ D.regular ∈ 𝓝 t₀ ∧
        G t₀ = postMetric F.observation t₀ ∧
        (∀ t ∈ I, ∀ (x : (postStage F.observation t₀).Carrier) (A B : TangentSpace ThreeModel x),
          HasDerivAt (fun r : ℝ => (G r).inner x A B)
            (-2 * ricciTensor (I := ThreeModel) (G t) x A B) t) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) ∧
        Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ ∧
        (∀ s : ℝ,
          Real.sqrt ((postMetric F.observation t₀).inner (loopLift (M.transported t₀ ht₀.le) s)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀.le) s))
                t₀ 1)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀.le) s))
                t₀ 1)) * Real.sqrt t₀ < L.cores.accuracy t₀) ∧
        ∀ t ∈ I, ∀ ht : M.exterior.start ≤ t,
          ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (postStage F.observation t).Carrier,
            G t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
            (∀ θ, ι (Φ t (M.transported t₀ ht₀.le θ)) = M.transported t ht θ) ∧
            (fun p => ι (Φ t p)) '' M.exterior.region t₀ = M.exterior.region t)
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
  (hasAttainedExteriorAreaObstructionAfter_of_routeW_WA8 K hK δ H hdec L j hj C hwin
    hconfW).toObstruction

end GC.LongTime.CuspP1
