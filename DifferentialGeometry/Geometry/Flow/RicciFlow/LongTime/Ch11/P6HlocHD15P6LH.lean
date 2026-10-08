import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HlocHProducerP6LH
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingDomC11CL2

/-!
# `hlocH` 在 D-15′ 赋值下的实例化（O-CH11-HLOCH G2，后缀 `_P6LH`）

R-C11-10 D-15′：坏点精度 `ηf := p6FineEta ε`（def 体 `≤ ηN/13000`、`≤ bJS ⌈ε⁻¹⌉₊`，CEIL3），坏点常数
`Cf := p6CoarseC ηf`（`C1₁ = C2₁ := Cf`，RERUN8B / HRESTP G4b 固定实例）。G1 `hlocH_of_transfers_P6LH` 的数值前提
在此由 CEIL3 §5 付：`thirteenK_mul_fineEta_le_C11CL3`（`13000 ηf ≤ ηN`）、`fineEta_le_bJS_C11CL3`；
Good 层常数前提收成具名数值前提 **`hdomL`**（`2 (max Cf 9 + √Cf) ≤ C1 ∧ 1200000 Cf ≤ C2`，同 HRESTP `hdomF` 的
地位），在 GAPTOP6 ceiling `C1P6 X1 Γ / C2P6 X2 Γ`（`ε := Γ.epsilon`）处由 CEIL3
`two_mul_fineCX_le_C1P6_C11CL3` / `mul1200k_fineC_le_C2P6_C11CL3` + `Cf ≤ p6FineC` 单调付清
（`hlocH_dom_ceiling_P6LH`）。
* **`hlocH_D15_P6LH`**：结论 = HRESTP G4b（`hrestP_of_jointPrefix_P6HP`）的 `hlocH` binder 逐字（`ηf Cf Cf`）。
* **`hlocH_ceiling_P6LH`**（consumer）：ceiling 常数处 0 前提的 hlocH。
槽文本由 build-logs/scratch/O-CH11-HLOCH/gen_d15.py 从 `P6HbdLateP6HB.lean:607–630` 逐字抽取。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6)

/-- **D-15′ 常数支配（hlocH 版）**：ceiling 常数处 `hdomL` 成立（`ε := Γ.epsilon`，`Cf ≤ p6FineC` 单调）。 -/
theorem hlocH_dom_ceiling_P6LH (Γ : GC.GeneralFlow.ClosedBirthConstants) :
    2 * (max (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) 9 +
        Real.sqrt (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon))) ≤
      GC.LongTime.Ch11.C1P6_C11GT6.{u} GC.LongTime.Ch11.p6X1std_C11GT6.{u} Γ ∧
    1200000 * p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
      GC.LongTime.Ch11.C2P6_C11GT6.{u} GC.LongTime.Ch11.p6X2std_C11GT6.{u} Γ := by
  have hc := GC.LongTime.Ch11.coarseFine_le_fineC_C11CL3.{u} Γ.epsilon
  have hm := max_le_max hc (le_refl (9 : ℝ))
  have hs := Real.sqrt_le_sqrt hc
  refine ⟨le_trans ?_ (GC.LongTime.Ch11.two_mul_fineCX_le_C1P6_C11CL3.{u} Γ),
    le_trans ?_ (GC.LongTime.Ch11.mul1200k_fineC_le_C2P6_C11CL3.{u} Γ)⟩
  · linarith
  · linarith

/-- **G2：D-15′ 实例化**：`η₁ := p6FineEta ε`、`C1₁ = C2₁ := p6CoarseC η₁`；结论 = HRESTP G4b 的 `hlocH`
binder 逐字（`let ηf / Cf`）。数值前提 `0 < ε < 1/11` + `hdomL`。 -/
theorem hlocH_D15_P6LH {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0} (hε0 : 0 < ε)
    (hε : ε < 1 / 11)
    (hdomL : 2 * (max (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)) 9 +
        Real.sqrt (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))) ≤ C1 ∧
      1200000 * p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε) ≤ C2) :
    let ηf : ℝ := p6FineEta_C11GT6 ε
    let Cf : ℝ := p6CoarseC_C11GT6.{u} ηf
    ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (Tn aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (pT : (H.stageAt Tn).Carrier)
        (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
          (H.activeStage_mono haT) pT)
        (σ : Icc (0 : ℝ) H.horizon) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
        (y : (H.stageAt σ).Carrier),
        H.time (Fin.last H.eventCount) < H.horizon → (σ : ℝ) = H.horizon → aSeed < σ →
        0 < metricScalarAt (H.stageMetric (H.activeStage σ) σ) y →
        ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ L : ℝ, 0 < L →
        LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) H.horizon => (t : ℝ))
          (fun t z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t)
            ηf Cf Cf z, W.capTubeHasNeckChart ηf)
          (fun t z => metricScalarAt (H.stageMetric (H.activeStage t) t) z)
          (fun t z => if h : aSeed ≤ t ∧ t ≤ Tn then
            riemannianEDistOf (H.stageMetric (H.activeStage t) t)
              (seedTrace.point (H.activeStage t) (H.activeStage_mono h.1)
                (H.activeStage_mono h.2)) z
            else 0)
          σ (metricScalarAt (H.stageMetric (H.activeStage σ) σ) y) L
          (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y) := by
  intro ηf Cf
  exact hlocH_of_transfers_P6LH F hε0 hε (GC.LongTime.Ch11.thirteenK_mul_fineEta_le_C11CL3 ε)
    (GC.LongTime.Ch11.fineEta_le_bJS_C11CL3 ε) hdomL.1 hdomL.2

/-- **consumer**：GAPTOP6 ceiling 常数处（`ε := Γ.epsilon`、`C1 := C1P6 X1 Γ`、`C2 := C2P6 X2 Γ`）的 hlocH，
0 前提（`hdomL` 由 `hlocH_dom_ceiling_P6LH` 付，`0 < ε < 1/11` 由 `epsilon_mem_C11GT6`）。 -/
theorem hlocH_ceiling_P6LH {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (Γ : GC.GeneralFlow.ClosedBirthConstants) {Ctime : ℝ≥0} :
    let ε : ℝ := Γ.epsilon
    let C1 : ℝ := GC.LongTime.Ch11.C1P6_C11GT6.{u} GC.LongTime.Ch11.p6X1std_C11GT6.{u} Γ
    let C2 : ℝ := GC.LongTime.Ch11.C2P6_C11GT6.{u} GC.LongTime.Ch11.p6X2std_C11GT6.{u} Γ
    let ηf : ℝ := p6FineEta_C11GT6 ε
    let Cf : ℝ := p6CoarseC_C11GT6.{u} ηf
    ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (Tn aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (pT : (H.stageAt Tn).Carrier)
        (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
          (H.activeStage_mono haT) pT)
        (σ : Icc (0 : ℝ) H.horizon) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
        (y : (H.stageAt σ).Carrier),
        H.time (Fin.last H.eventCount) < H.horizon → (σ : ℝ) = H.horizon → aSeed < σ →
        0 < metricScalarAt (H.stageMetric (H.activeStage σ) σ) y →
        ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ L : ℝ, 0 < L →
        LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) H.horizon => (t : ℝ))
          (fun t z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t)
            ηf Cf Cf z, W.capTubeHasNeckChart ηf)
          (fun t z => metricScalarAt (H.stageMetric (H.activeStage t) t) z)
          (fun t z => if h : aSeed ≤ t ∧ t ≤ Tn then
            riemannianEDistOf (H.stageMetric (H.activeStage t) t)
              (seedTrace.point (H.activeStage t) (H.activeStage_mono h.1)
                (H.activeStage_mono h.2)) z
            else 0)
          σ (metricScalarAt (H.stageMetric (H.activeStage σ) σ) y) L
          (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y) := by
  intro ε C1 C2 ηf Cf
  exact hlocH_D15_P6LH (Ctime := Ctime) F (GC.LongTime.Ch11.epsilon_mem_C11GT6 Γ).1
    (GC.LongTime.Ch11.epsilon_mem_C11GT6 Γ).2 (hlocH_dom_ceiling_P6LH.{u} Γ)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
