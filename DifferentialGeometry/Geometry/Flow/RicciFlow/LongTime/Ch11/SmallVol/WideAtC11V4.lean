import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.HICompareC11V3

set_option autoImplicit false

/-!
# S-CH11-SMALLVOL4 G1：`LocalKappaWideAt_C11Q`（逐点 `(A, L, κ)` 形）→ wide late / wide window（`_C11V4`）

SMALLVOL3 G1（`WideAlignC11V3`）的 wide envelope 步吃的是 `LocalKappaWideSupply_C11Q`（`∀ A L ∃ κ`
的供给形）。KAPPA 链（K0–K6）实际逐点产出 `LocalKappaWideAt_C11Q F δ α nr A L κ`（固定 `A, L, κ`）。
本文件给**逐点形**的 envelope 步：

* `wideLate_of_wideAt_C11V4`：`LocalKappaWideAt_C11Q F δ α nr (51200 e⁵⁷ A) (100 (A+1)) κ` + S7 ⇒
  SMALLVOL2 G2 `wideWindow_of_wideLate_C11V2` 的 wide late 展开前提（`∃ T > 0`，`T = A' = 51200 e⁵⁷ A`，
  accuracy 前提由 P6A `accuracy_on_late_half_P6A` 在 `T ≤ t` 时自动成立）。
* `wideWindow_of_wideAt_C11V4`：再接 `wideWindow_of_wideLate_C11V2`（seed shift，上沿 `(A+1) r`）。
* `localKappaWindow_zero_of_wideAt_C11V4`：逐点 K ⇒ `nr := 0` window（走晚期 `hcan`，即 SMALLVOL3 G2′ 的
  `localKappaWindow_zero_of_wide_window_late_C11V3`；`M`、`hcapS`、`hcan`、`hdeg` 仍是显式前提，
  其对齐见 `ProfileAlignC11V4`）。
* `wideLate_of_wideSupply_C11V4`（example）：SMALLVOL3 的供给形是本文件逐点形的 `∀ A L` 特化。
-/

noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **逐点 envelope 步**：`LocalKappaWideAt_C11Q`（accuracy 形）在 `A' = 51200 e⁵⁷ A`、`L = 100(A+1)`
处 + S7 ⇒ G2 的 wide late 展开前提（`T = A'`）。 -/
theorem wideLate_of_wideAt_C11V4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ} {A κ : ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (hA : 0 < A)
    (h : LocalKappaWideAt_C11Q F δ α nr (51200 * Real.exp 57 * A) (100 * (A + 1)) κ) :
    ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal ((51200 * Real.exp 57 * A)⁻¹ * r ^ 3) ≤
          ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (51200 * Real.exp 57 * A * r),
        ∀ ρ' : ℝ, nr t / 100 ≤ ρ' → ρ' ≤ 100 * (A + 1) * r →
          H.isParabolicallyRmControlledBall t x ρ' →
          ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x ρ' := by
  have hA' : 0 < 51200 * Real.exp 57 * A := by positivity
  refine ⟨51200 * Real.exp 57 * A, hA', ?_⟩
  intro n H t p r hT hr hsm hvol x hx ρ' hlow hup hball
  exact h n t p r hr (accuracy_on_late_half_P6A hacc hA' hT) hsm hvol x hx ρ' hlow hup hball

/-- **逐点 K ⇒ wide window**（seed shift 后上沿 `(A+1) r`，`T = 4A'/3`）。 -/
theorem wideWindow_of_wideAt_C11V4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ} {A κ : ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (hA : 0 < A)
    (h : LocalKappaWideAt_C11Q F δ α nr (51200 * Real.exp 57 * A) (100 * (A + 1)) κ) :
    ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t), (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, nr v / 100 ≤ ρ' → ρ' ≤ (A + 1) * r →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ' :=
  wideWindow_of_wideLate_C11V2 (F := F) (nr := nr) (κ := κ) hA (wideLate_of_wideAt_C11V4 hacc hA h)

/-- **逐点 K ⇒ `nr := 0` window**（晚期 `hcan`；`ε₀` 只依赖 `(D, ε, C1, C2, N)`）。前提：S7、
K 在 `(51200 e⁵⁷ A, 100(A+1), κ)` 处的逐点形、`nr ≤ M`、`hcapS`、晚期 `hcan`、`hdeg`。 -/
theorem localKappaWindow_zero_of_wideAt_C11V4 (D : ℝ)
    (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ} {A κ M : ℝ}, 0 < A → 0 < κ → (∀ s, nr s ≤ M) →
      LargerBallAccuracySupply_C11S δ α →
      LocalKappaWideAt_C11Q F δ α nr (51200 * Real.exp 57 * A) (100 * (A + 1)) κ →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
          ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
            (S : (H.event i).PresentedStaticCap fixed D m η b),
            η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow) →
      (∃ T₀ : ℝ, ∀ n, let H := (F.tower.history n).toHistory;
        ∀ v v' : Icc (0 : ℝ) H.horizon, T₀ ≤ (v' : ℝ) → v' ≤ v →
          ∀ (w : (H.stageAt v').Carrier) (s : ℝ),
          0 < s → s < nr v / 50 → (v : ℝ) - s ^ 2 ≤ v' →
          s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
            (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
          ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v') v') ε C1 C2 w,
            V.capTubeHasNeckChart ε) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'' := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_wide_window_late_C11V3.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α nr A κ M hA hκ hnrM hacc h hcapS hcan hdeg
  exact hE hA hκ hnrM (wideWindow_of_wideAt_C11V4 hacc hA h) hcapS hcan hdeg

/-- consumer：逐点形 ⇒ `nr := 0` window ⇒ `tracedKappa_of_window_P6B`（M8 bridge）。 -/
example (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ)
    (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ} {A κ M : ℝ}, 0 < A → 0 < κ → (∀ s, nr s ≤ M) →
      LargerBallAccuracySupply_C11S δ α →
      LocalKappaWideAt_C11Q F δ α nr (51200 * Real.exp 57 * A) (100 * (A + 1)) κ →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
          ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
            (S : (H.event i).PresentedStaticCap fixed D m η b),
            η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow) →
      (∃ T₀ : ℝ, ∀ n, let H := (F.tower.history n).toHistory;
        ∀ v v' : Icc (0 : ℝ) H.horizon, T₀ ≤ (v' : ℝ) → v' ≤ v →
          ∀ (w : (H.stageAt v').Carrier) (s : ℝ),
          0 < s → s < nr v / 50 → (v : ℝ) - s ^ 2 ≤ v' →
          s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
            (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
          ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v') v') ε C1 C2 w,
            V.capTubeHasNeckChart ε) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      True := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_wideAt_C11V4.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α nr A κ M hA hκ hnrM hacc h hcapS hcan hdeg
  obtain ⟨κ'', -, hW0⟩ := hE hA hκ hnrM hacc h hcapS hcan hdeg
  have := tracedKappa_of_window_P6B hW0
  trivial

/-- consumer（对齐 SMALLVOL3）：供给形 `LocalKappaWideSupply_C11Q` 是逐点形的 `∀ A L ∃ κ` 打包；
SMALLVOL3 的 `wideLate_of_wideSupply_C11V3` 即本文件逐点形在 `(A', L, κ)` 处的实例。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ} (hacc : LargerBallAccuracySupply_C11S δ α)
    (h : LocalKappaWideSupply_C11Q F δ α nr) {A : ℝ} (hA : 0 < A) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal ((51200 * Real.exp 57 * A)⁻¹ * r ^ 3) ≤
          ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (51200 * Real.exp 57 * A * r),
        ∀ ρ' : ℝ, nr t / 100 ≤ ρ' → ρ' ≤ 100 * (A + 1) * r →
          H.isParabolicallyRmControlledBall t x ρ' →
          ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x ρ' := by
  have hA' : 0 < 51200 * Real.exp 57 * A := by positivity
  obtain ⟨κ, hκ, hK⟩ := h _ (100 * (A + 1)) hA' (by positivity)
  exact ⟨κ, hκ, wideLate_of_wideAt_C11V4 hacc hA hK⟩

end GC.LongTime.Ch11
