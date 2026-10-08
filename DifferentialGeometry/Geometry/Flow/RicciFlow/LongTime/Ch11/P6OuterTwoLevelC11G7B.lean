import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6OuterCoarseCXOU2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Gamma2ContractC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HrestJointPrefixAssembleP6HP2

/-!
# Good-time ceiling `C_t*(Γ)` 与两级 outer wrapper（O-CH11-GAPTOP7B G1，后缀 `_C11G7B`）

R-C11-11 D-5（Q4.3 新增遗漏）：HRESTP G4a / G4a′ 的三分量 `hdomF : C1₁ ≤ C1 ∧ C2₁ ≤ C2 ∧ Ctime₁ ≤ Ctime`
（`P6HrestJointPrefixAssembleP6HP.lean` L974–976，event 支 L1066–1069 用 `hdomF.2.2`）的第三分量在 CXOU2 旧固定式
`Ctime = max Γ.Ctime (Cco ε)ᵗᵒᴺᴺ`（`P6OuterCoarseCXOU2.lean` L57–60）下无来源。修法 = selection 前固定闭项
* **`p6Ctime_C11G7B Γ := max Γ.Ctime (C1P6 std Γ)ᵗᵒᴺᴺᴿᵉᵃˡ`**（`C1P6 std` = D-15″ 后的 `C1P6*`）：
  同时支配 `Γ.Ctime`（TDS）、`Cco(Γ.ε)ᵗᵒᴺᴺ`（coarse joint）、`c(Γ)ᵗᵒᴺᴺ ⊇ Cco(η₁)ᵗᵒᴺᴺ`（保留的 fine rerun time 常数）；
  Budget 仍用 `Γf.Ctime`（不混）。
* **三分量 `hdomF`**：`hdomF_twoLevel_C11G7B Γ`（坏点常数 `(c(Γ), c(Γ), Cco(η₁)ᵗᵒᴺᴺ)` ≤ outer
  `(C1P6 std Γ, C2P6 std Γ, C_t*(Γ))`）与 lower-bound 形 `hdomF_twoLevel_of_le_C11G7B`；
  `hdomL_bad_C11G7B`（htrans / hlocH 的数值前提在 `c(Γ)` 处）。
* **两级 outer wrapper `outerTwoLevel_C11G7B`**：CXOU2 G2′
  `canonicalLateCore_of_jointD_scrsPlus_coarse_CXOU2` 的两级孪生——tower `Tw` 在 `Γf`、新增
  `FineOf_C11G2 Γf Γ`，结论精度 / 常数仍在粗 `Γ`（`Γ.epsilon`、`C1P6 / C2P6 std Γ`）；
  **Ctime 由固定式改为 lower bounds** `Γ.Ctime ≤ Ctime`、`Cco(ε)ᵗᵒᴺᴺ ≤ Ctime`（固定 `Ctime := C_t*(Γ)` 时由
  `p6Ctime_bounds_C11G7B` 付）；外层 supply 用 `outerSupply_twoLevel_C11G2`。陈述由
  build-logs/scratch/O-CH11-GAPTOP7B/gen_g1.py 从 `P6OuterCoarseCXOU2.lean` L42–304 逐字抽取，只改 4 处。
* 输出仍是**空间** `CanonicalLateCore_P6X`（底层 coarse joint 只有空间核）。TimeCore 版（hP6b‴ 的 R-C11-14 输出）
  的 repair target = P6TIME G2 `canonicalLateTimeCore_of_jointD_P6CK` 交付后的 coarse 孪生接入（本车道不声称）。
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

namespace GC.LongTime.Ch11

open GC.GeneralFlow

universe u

/-! ## 1. Good-time ceiling `C_t*(Γ)` -/

/-- **`C_t*(Γ)`**（R-C11-11 D-5）：`max Γ.Ctime (C1P6 std Γ)ᵗᵒᴺᴺᴿᵉᵃˡ`，selection 前固定。 -/
def p6Ctime_C11G7B (Γ : ClosedBirthConstants) : ℝ≥0 :=
  max Γ.Ctime (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ).toNNReal

theorem Ctime_le_p6Ctime_C11G7B (Γ : ClosedBirthConstants) :
    Γ.Ctime ≤ p6Ctime_C11G7B.{u} Γ :=
  le_max_left _ _

theorem C1P6time_le_p6Ctime_C11G7B (Γ : ClosedBirthConstants) :
    (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ).toNNReal ≤ p6Ctime_C11G7B.{u} Γ :=
  le_max_right _ _

/-- 任意 `x ≤ C1P6 std Γ` 的 `xᵗᵒᴺᴺ` 被 `C_t*(Γ)` 支配。 -/
theorem toNNReal_le_p6Ctime_C11G7B (Γ : ClosedBirthConstants) {x : ℝ}
    (hx : x ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) : x.toNNReal ≤ p6Ctime_C11G7B.{u} Γ :=
  (Real.toNNReal_le_toNNReal hx).trans (C1P6time_le_p6Ctime_C11G7B Γ)

/-- coarse joint 的时间门槛：`Cco(Γ.ε)ᵗᵒᴺᴺ ≤ C_t*(Γ)`。 -/
theorem coarseTime_le_p6Ctime_C11G7B (Γ : ClosedBirthConstants) :
    (p6CoarseC_C11GT6.{u} Γ.epsilon).toNNReal ≤ p6Ctime_C11G7B.{u} Γ :=
  toNNReal_le_p6Ctime_C11G7B Γ (coarse_le_C1P6std_C11GT6 Γ)

/-- outer wrapper 在 `Ctime := C_t*(Γ)` 处的两条 lower bound。 -/
theorem p6Ctime_bounds_C11G7B (Γ : ClosedBirthConstants) :
    Γ.Ctime ≤ p6Ctime_C11G7B.{u} Γ ∧
      (p6CoarseC_C11GT6.{u} Γ.epsilon).toNNReal ≤ p6Ctime_C11G7B.{u} Γ :=
  ⟨Ctime_le_p6Ctime_C11G7B Γ, coarseTime_le_p6Ctime_C11G7B Γ⟩

/-! ## 2. 坏点常数 `c(Γ)` 的支配与三分量 `hdomF` -/

/-- `c(Γ) ≤ C1P6 std Γ`（D-15″：`2 · (max c 9 + √c) ≤ X1std Γ`）。 -/
theorem p6BadC_le_C1P6std_C11G7B (Γ : ClosedBirthConstants) :
    p6BadC_C11G2.{u} Γ ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ := by
  have h := (two_mul_bad_le_p6X1std_C11G7.{u} Γ).trans (X_le_C1P6_C11GT6 p6X1std_C11GT6.{u} Γ)
  have hs := Real.sqrt_nonneg (p6BadC_C11G2.{u} Γ)
  have hm : p6BadC_C11G2.{u} Γ ≤ max (p6BadC_C11G2.{u} Γ) 9 := le_max_left _ _
  have h9 : (9 : ℝ) ≤ max (p6BadC_C11G2.{u} Γ) 9 := le_max_right _ _
  linarith

/-- `1 ≤ c(Γ)`（`c(Γ) ≥ C1ceil Γ ≥ 1`）。 -/
theorem one_le_p6BadC_C11G7B (Γ : ClosedBirthConstants) : 1 ≤ p6BadC_C11G2.{u} Γ :=
  (one_le_C1ceil_C11SC.{u} Γ).trans (C1ceil_le_p6BadC_C11G2 Γ)

/-- `c(Γ) ≤ C2P6 std Γ`（D-15″：`1200000 · c ≤ X2std Γ`）。 -/
theorem p6BadC_le_C2P6std_C11G7B (Γ : ClosedBirthConstants) :
    p6BadC_C11G2.{u} Γ ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ := by
  have h := (mul1200k_bad_le_p6X2std_C11G7.{u} Γ).trans (X_le_C2P6_C11GT6 p6X2std_C11GT6.{u} Γ)
  have h1 := one_le_p6BadC_C11G7B.{u} Γ
  linarith

/-- `c(Γ)ᵗᵒᴺᴺ ≤ C_t*(Γ)`。 -/
theorem badTime_le_p6Ctime_C11G7B (Γ : ClosedBirthConstants) :
    (p6BadC_C11G2.{u} Γ).toNNReal ≤ p6Ctime_C11G7B.{u} Γ :=
  toNNReal_le_p6Ctime_C11G7B Γ (p6BadC_le_C1P6std_C11G7B Γ)

/-- 保留的 fine rerun time 常数 `Cco(η₁)ᵗᵒᴺᴺ ≤ C_t*(Γ)`（`Cco η₁ ≤ c(Γ) ≤ C1P6*`）——D-5 的缺项。 -/
theorem coarseFineTime_le_p6Ctime_C11G7B (Γ : ClosedBirthConstants) :
    (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ≤ p6Ctime_C11G7B.{u} Γ :=
  toNNReal_le_p6Ctime_C11G7B Γ ((coarseFine_le_p6BadC_C11G2 Γ).trans (p6BadC_le_C1P6std_C11G7B Γ))

/-- **三分量 `hdomF`（两级，C_t* 处）**：坏点常数 `(C1₁, C2₁, Ctime₁) := (c(Γ), c(Γ), Cco(η₁)ᵗᵒᴺᴺ)` ≤ outer
`(C1P6 std Γ, C2P6 std Γ, C_t*(Γ))`——HRESTP G4a / G4a′ 的 `hdomF` 实参。 -/
theorem hdomF_twoLevel_C11G7B (Γ : ClosedBirthConstants) :
    p6BadC_C11G2.{u} Γ ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      p6BadC_C11G2.{u} Γ ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ ∧
      (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ≤ p6Ctime_C11G7B.{u} Γ :=
  ⟨p6BadC_le_C1P6std_C11G7B Γ, p6BadC_le_C2P6std_C11G7B Γ, coarseFineTime_le_p6Ctime_C11G7B Γ⟩

/-- **三分量 `hdomF`（lower-bound 形）**：outer `Ctime ≥ C_t*(Γ)`，坏点 `Ctime₁ ∈ {Cco(η₁)ᵗᵒᴺᴺ, c(Γ)ᵗᵒᴺᴺ}` 的
上界 `c(Γ)ᵗᵒᴺᴺ`。 -/
theorem hdomF_twoLevel_of_le_C11G7B (Γ : ClosedBirthConstants) {Ctime Ctime₁ : ℝ≥0}
    (hCt : p6Ctime_C11G7B.{u} Γ ≤ Ctime) (hCt₁ : Ctime₁ ≤ (p6BadC_C11G2.{u} Γ).toNNReal) :
    p6BadC_C11G2.{u} Γ ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      p6BadC_C11G2.{u} Γ ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ ∧ Ctime₁ ≤ Ctime :=
  ⟨p6BadC_le_C1P6std_C11G7B Γ, p6BadC_le_C2P6std_C11G7B Γ,
    hCt₁.trans ((badTime_le_p6Ctime_C11G7B Γ).trans hCt)⟩

/-- **`hdomL` 在 `c(Γ)` 处**（htrans / hlocH 的 Good 层数值前提，`C1₁ = C2₁ := c(Γ)`）。 -/
theorem hdomL_bad_C11G7B (Γ : ClosedBirthConstants) :
    2 * (max (p6BadC_C11G2.{u} Γ) 9 + Real.sqrt (p6BadC_C11G2.{u} Γ)) ≤
        C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      1200000 * p6BadC_C11G2.{u} Γ ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  ⟨(two_mul_bad_le_p6X1std_C11G7.{u} Γ).trans (X_le_C1P6_C11GT6 p6X1std_C11GT6.{u} Γ),
    (mul1200k_bad_le_p6X2std_C11G7.{u} Γ).trans (X_le_C2P6_C11GT6 p6X2std_C11GT6.{u} Γ)⟩

end GC.LongTime.Ch11

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-! ## 3. 两级 outer wrapper -/

/-- **两级 outer wrapper**（CXOU2 G2′ 的两级孪生）：tower `Tw` 在 `Γf`、`FineOf_C11G2 Γf Γ`；结论精度 / 常数在粗
`Γ`；Ctime 只要 lower bounds `Γ.Ctime ≤ Ctime`、`Cco(ε)ᵗᵒᴺᴺ ≤ Ctime`（`C_t*(Γ)` 满足，见
`p6Ctime_bounds_C11G7B`）。binder `hgapJ hrestP` 与 CXOU2 G2′ 逐字。 -/
theorem outerTwoLevel_C11G7B :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ),
    (∀ (C : ℝ≥0) (n : ℕ), 0 < Cb C n ∧ Cb C n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
    (∀ (C : ℝ≥0) (n : ℕ), 0 < ζ C n ∧ ζ C n ≤ 1 / ((n : ℝ) + 1)) ∧
    (∀ (C : ℝ≥0) (n : ℕ), 0 < δ₀ C n ∧ δ₀ C n ≤ 1 / ((n : ℝ) + 1)) ∧
    (∀ (C : ℝ≥0) (n : ℕ), (n : ℝ) + 1 ≤ Rn C n) ∧ (∀ (C : ℝ≥0) (n : ℕ), n + 2 ≤ m₀ C n) ∧
    ∀ (ε : ℝ)
      {P : OrientedThreeStage.{u}} {g : P.Metric} {pB : CutoffParameters}
      {Γ Γf : GC.GeneralFlow.ClosedBirthConstants} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
      (Tw : GC.LongTime.Ch11.BlockTower_C11W pB Γf P g Cdist cMax Dstar εReserve),
      GC.LongTime.Ch11.SameConstructionRetentionSupplyPlus_C11GT6 Tw →
      GC.LongTime.Ch11.FineOf_C11G2.{u} Γf Γ → Γ.epsilon = ε →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ GC.LongTime.Ch11.epsW_CXOU2.{u} →
      ∀ {F : GC.Interface.RawSurgery P g} {q : CutoffParameters},
      F.tower = Tw.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (GC.LongTime.Ch11.chainDiagonal_C11A Tw.toChain).delta t ∧
        q.neckRadius t = (GC.LongTime.Ch11.chainDiagonal_C11A Tw.toChain).neckRadius t) →
      ∀ {C1 C2 : ℝ} {Ctime : ℝ≥0},
      C1 = GC.LongTime.Ch11.C1P6_C11GT6.{u} GC.LongTime.Ch11.p6X1std_C11GT6.{u} Γ →
      C2 = GC.LongTime.Ch11.C2P6_C11GT6.{u} GC.LongTime.Ch11.p6X2std_C11GT6.{u} Γ →
      Γ.Ctime ≤ Ctime → (GC.LongTime.Ch11.p6CoarseC_C11GT6.{u} ε).toNNReal ≤ Ctime →
      ∀ (Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ), Monotone T₀ → Monotone Qt →
      (hgapJ : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∃ (p pF : ℕ → CutoffParameters) (Qs : ℕ → ℝ)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n))
          (a₀ : ℝ),
          Nonempty (∀ n i, GeometricCutoffRecord (Ho n).toHistory i (pF n)) ∧
          0 < a₀ ∧
          (∀ n x, InFixedHamiltonIveyRegion ((Ho n).initialMetric 0) a₀ x ∧
            -3 / a₀ ≤ metricScalarAt ((Ho n).initialMetric 0) x) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ →
            (pF n).delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) ∧
          (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) ∧
          (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) ∧
          (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) ∧
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n i hi b, max (Qs n) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Qs n) (Fin.last (Ho n).eventCount)) ∧
          (∀ n, c n * Qs n < R n) ∧
          (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Ho n).toHistory.stageMetric
            ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (D / Real.sqrt (R n / c n)),
        ∀ (v : Icc (0 : ℝ) (Ho n).toHistory.horizon)
          (hvt : v ≤ (Ho n).unscaleTime_P6X (hc n) (σ n)),
          (((Ho n).unscaleTime_P6X (hc n) (σ n) : Icc (0 : ℝ) (Ho n).toHistory.horizon) : ℝ) -
            B / (R n / c n) ≤ v →
        ∀ tr : BackwardPointTrace (Ho n).toHistory ((Ho n).toHistory.activeStage v)
          ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
          ((Ho n).toHistory.activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
          (Ho n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((Ho n).toHistory.activeStage v) le_rfl
              ((Ho n).toHistory.activeStage_mono hvt))
            (ϱ / Real.sqrt (R n / c n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            ballVolume (scaleMetric (R n / c n) (div_pos (hRpos n) (hc n))
              ((Ho n).toHistory.stageMetric ((Ho n).toHistory.activeStage v) v))
              (tr.point ((Ho n).toHistory.activeStage v) le_rfl
                ((Ho n).toHistory.activeStage_mono hvt)) ϱ) ∧
          (∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
            (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) ∧
          (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
            (Ho n).time i.succ ∈ Icc (τ / 2) τ →
            ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
              (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stageAt (σ n)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
                ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) ∧
          (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) ∧
          (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
          v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
          (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              ((seedTrace n).point j'.castSucc h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
              (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
          ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
            (Kh n).time j'.castSucc < s →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n)) →
            ∀ z : ((Kh n).stage j'.castSucc).Carrier,
              riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                  ENNReal.ofReal
                    (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
                ((Kh n).event j').incoming.flow.scalar s z ≤
                  C * ((Kh n).event j').incoming.flow.scalar v w)) →
      (hrestP : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
        ((∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧ (σ k : ℝ) < (Kh k).horizon) ∨
          (∀ k, ¬ ∃ W : SpatialCanonicalWitness
            ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ε C1 C2 (y k), W.capTubeHasNeckChart ε)) → False) →
      GC.LongTime.Ch11.CanonicalLateCore_P6X F ε C1 C2 := by
  obtain ⟨c₀, hc₀, Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ₀, hRn, hm₀, -, hB⟩ :=
    canonicalLateCore_of_jointD_coarse_CXOU2.{u}
  refine ⟨c₀, hc₀, Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ₀, hRn, hm₀, ?_⟩
  intro ε P g pB Γ Γf Cdist cMax Dstar εReserve Tw hS hfine hΓ hs hW F q hF hq C1 C2 Ctime hC1e
    hC2e hCt hCco Ctime₀ T₀ Qt hT₀m hQm hgap hrest
  subst hΓ hC1e hC2e
  obtain ⟨-, hε1, hεW, hw, hn, hc⟩ := GC.LongTime.Ch11.joint_gates_of_closedBirth_CXOU2.{u} hs hW
  obtain ⟨-, hB'⟩ := hB Γ.epsilon Γ.epsilon_pos hε1 hεW hw hn hc
  obtain ⟨hanti, hcan, -, hder⟩ := GC.LongTime.Ch11.outerSupply_twoLevel_C11G2 hS hfine F q hF hq
    (GC.LongTime.Ch11.C1ceil_le_C1P6_C11GT6 GC.LongTime.Ch11.p6X1std_C11GT6.{u} Γ)
    (GC.LongTime.Ch11.C2ceil_le_C2P6_C11GT6 GC.LongTime.Ch11.p6X2std_C11GT6.{u} Γ) hCt
  exact hB' (GC.LongTime.Ch11.coarse_le_C1P6std_C11GT6.{u} Γ)
    (GC.LongTime.Ch11.coarse_le_C2P6std_C11GT6.{u} Γ) hCco hanti hcan hder Ctime₀ T₀ Qt hT₀m hQm
    hgap hrest

/-- consumer (i)：两级 Γ 选取（`hpbaseTwoLevel_C11G2`）给出 wrapper 的全部非结构前提——`FineOf Γf Γ`、两道
Γ-accuracy、两条 Ctime lower bound（取 `Ctime := C_t*(Γ)`）、坏点 `hcan₁` 精度门槛。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Γ Γf : GC.GeneralFlow.ClosedBirthConstants, GC.LongTime.Ch11.FineOf_C11G2.{u} Γf Γ ∧
      Γ.epsilon ≤ εStrong_C12X.{u} ∧ Γ.epsilon ≤ GC.LongTime.Ch11.epsW_CXOU2.{u} ∧
      Γ.Ctime ≤ GC.LongTime.Ch11.p6Ctime_C11G7B.{u} Γ ∧
      (GC.LongTime.Ch11.p6CoarseC_C11GT6.{u} Γ.epsilon).toNNReal ≤
        GC.LongTime.Ch11.p6Ctime_C11G7B.{u} Γ := by
  obtain ⟨-, Γ, Γf, hfine, hs, hW, -⟩ := GC.LongTime.Ch11.hpbaseTwoLevel_C11G2.{u} P g
  exact ⟨Γ, Γf, hfine, hs, hW, GC.LongTime.Ch11.p6Ctime_bounds_C11G7B.{u} Γ⟩

/-- consumer (ii)：wrapper 在 `Ctime := C_t*(Γ)` 处实例化（类型对齐；两条 lower bound 由
`p6Ctime_bounds_C11G7B` 付）。 -/
example : True := by
  obtain ⟨_c₀, -, _Cb, _Rn, _ζ, _δ₀, _m₀, -, -, -, -, -, hW⟩ := outerTwoLevel_C11G7B.{0}
  have _h := fun {P : OrientedThreeStage.{0}} {g : P.Metric} {pB : CutoffParameters}
      {Γ Γf : GC.GeneralFlow.ClosedBirthConstants} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
      (Tw : GC.LongTime.Ch11.BlockTower_C11W pB Γf P g Cdist cMax Dstar εReserve) hS hfine hs hW'
      {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} hF hq =>
    hW Γ.epsilon Tw hS hfine rfl hs hW' (F := F) (q := q) hF hq
      (Ctime := GC.LongTime.Ch11.p6Ctime_C11G7B.{0} Γ) rfl rfl
      (GC.LongTime.Ch11.p6Ctime_bounds_C11G7B.{0} Γ).1
      (GC.LongTime.Ch11.p6Ctime_bounds_C11G7B.{0} Γ).2
  trivial

/-- consumer (iii)：三分量 `hdomF` 喂 HRESTP G4a′（`hrestP_of_slots_P6HP2`）——outer
`(Γ.ε, C1P6 std Γ, C2P6 std Γ, C_t*(Γ))`、坏点 `(η₁, c(Γ), c(Γ), Cco(η₁)ᵗᵒᴺᴺ)`；`hdomF` 不再是 binder。 -/
example (Γ : GC.GeneralFlow.ClosedBirthConstants) {P : OrientedThreeStage.{0}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} : True := by
  have hsmall : Γ.epsilon < 1 / 11 := (GC.LongTime.Ch11.epsilon_mem_C11GT6 Γ).2
  have hηε : GC.LongTime.Ch11.p6FineEta_C11GT6 Γ.epsilon ≤ Γ.epsilon :=
    (GC.LongTime.Ch11.p6FineEta_le_C11GT6 Γ.epsilon).trans (half_le_self Γ.epsilon_pos.le)
  have _h := hrestP_of_slots_P6HP2 (F := F) (q := q)
    (C1f := 1) (C2f := 1) (m := 1) (kk := 0) (T₀ := fun _ => 0) (Qt := fun _ => 0)
    (C1 := GC.LongTime.Ch11.C1P6_C11GT6.{0} GC.LongTime.Ch11.p6X1std_C11GT6.{0} Γ)
    (C2 := GC.LongTime.Ch11.C2P6_C11GT6.{0} GC.LongTime.Ch11.p6X2std_C11GT6.{0} Γ)
    (Ctime := GC.LongTime.Ch11.p6Ctime_C11G7B.{0} Γ)
    (C1₁ := GC.LongTime.Ch11.p6BadC_C11G2.{0} Γ) (C2₁ := GC.LongTime.Ch11.p6BadC_C11G2.{0} Γ)
    (Ctime₁ := (GC.LongTime.Ch11.p6CoarseC_C11GT6.{0}
      (GC.LongTime.Ch11.p6FineEta_C11GT6 Γ.epsilon)).toNNReal)
    (hdomF := GC.LongTime.Ch11.hdomF_twoLevel_C11G7B.{0} Γ) (hηε := hηε) (hsmall := hsmall)
  trivial

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
