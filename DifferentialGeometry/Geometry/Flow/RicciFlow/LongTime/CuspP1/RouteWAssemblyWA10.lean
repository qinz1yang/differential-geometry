import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWAssemblyWA6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.HbarWFinal
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HtLeftPacketLeavesWA2

/-!
# Route W 端到端组装（O-W-ASSEMBLY-2 G9，后缀 `_WA10`）

相对 G6（`RouteWAssemblyWA6.lean`）：

* `hbarW` ⇐ O-W-CURV G5 `PrescribedCuspMeridianTop_CPQ.hbarW_CV`（无条件；= G8b 的 STAT-2 实例化）；
* `hpkt` ⇐ 本车道 G9 `hpkt_of_leaves_WA2`（window + TPW + R3 + c5 + ⑧ HNEG + c9a/c9b NECK-2 全部接好）。

唯一显式义务 **`h6E`**（⑥）：对每个 Top meridian `M`，晚期每个 `_HC2` 形 Morrey 盘、每个 `σ > 0` 的
IMS05′（S-W-NECK G4 形 `hIMS05`，`g_post(s)` 下）——O-W-IMS06 G16 交付（S-W-STAB-2 G1/G4 逐盘 +
IMS06 G9/G15）。
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

/-- **Route W 主组装定理（G9）**：A11 风格前提 + `H` + `h6E`（唯一显式义务，⑥）。 -/
theorem hasAttainedExteriorAreaObstructionAfter_of_routeW_WA10
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (h6E : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores,
      ∃ T₁ : ℝ, ∀ (s : ℝ) (hs : M.exterior.start ≤ s), T₁ ≤ s →
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
          ∀ σ : ℝ, 0 < σ → ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
            IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK (postMetric F.observation s)
              ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) z₀ z ≤ ENNReal.ofReal r} →
            (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK (postMetric F.observation s)
              ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) z₀ z = ENNReal.ofReal r) →
            (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK (postMetric F.observation s)
              ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) z₀ z ≤ ENNReal.ofReal r →
              ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt (postMetric F.observation s) (diskExtension
                ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) w)) →
            r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ))) :
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) :=
  hasAttainedExteriorAreaObstructionAfter_of_routeW_WA6 K hK δ H hdec L j hj C
    (fun M => M.hbarW_CV) (fun M => hpkt_of_leaves_WA2 H hdec M (h6E M))

/-- consumer：`.toObstruction`（`hasLateSequenceTests_of_thick_thin_and_obstruction` 的 producer 格）。 -/
theorem hasExteriorAreaObstructionAfter_of_routeW_WA10
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (h6E : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores,
      ∃ T₁ : ℝ, ∀ (s : ℝ) (hs : M.exterior.start ≤ s), T₁ ≤ s →
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
          ∀ σ : ℝ, 0 < σ → ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
            IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK (postMetric F.observation s)
              ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) z₀ z ≤ ENNReal.ofReal r} →
            (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK (postMetric F.observation s)
              ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) z₀ z = ENNReal.ofReal r) →
            (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK (postMetric F.observation s)
              ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) z₀ z ≤ ENNReal.ofReal r →
              ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt (postMetric F.observation s) (diskExtension
                ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(U, (postStage F.observation s).Carrier)).comp q) w)) →
            r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ))) :
    hasExteriorAreaObstructionAfter F (L.decomposition j C) :=
  (hasAttainedExteriorAreaObstructionAfter_of_routeW_WA10 K hK δ H hdec L j hj C
    h6E).toObstruction

end GC.LongTime.CuspP1
