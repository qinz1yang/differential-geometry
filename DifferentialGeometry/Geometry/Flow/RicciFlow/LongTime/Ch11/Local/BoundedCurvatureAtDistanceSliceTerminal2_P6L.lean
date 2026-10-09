import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceSliceTerminal_P6L

/-!
# `SliceTerminal:336` 序列形的局部化（`_P6L`，O-CH11-P6ANCH G1）：P6 基点 anchor `hanchor0`

原 `ST/BoundedCurvatureAtDistanceSliceTerminal.lean:336`
`RetainedCoreHistory.eventually_scalar_bound_at_distance_of_not_capWindowPoint_terminal`
是 `:249` 的 `filter_upwards` 序列包装。本文件照抄其证明，底层改调 P6A3 G4 的
`…_terminal_P6L`（`Local/BoundedCurvatureAtDistanceSliceTerminal_P6L.lean`）。改动：
* 区域序列 `U n`（last stage carrier）与 **任意尺度吸收** 前提
  `hU : ∀ Rad, ∀ᶠ n, B_{t n}(y n, Rad/√R_n) ⊆ U n`（`_P6L` 的 `Rad` 依赖 `A`，在 history 之前取，
  故序列层要求 `U n` eventually 吞下每个固定尺度球；selection 的 `U n = B(y n, L n/√Q n)`、`L n → ∞`
  正是此形）；
* `U` 相关前提（`hW` / `hslabs` footprint / `hder` / `hgrad` / `hnc` tested-ball）改成 **eventually**
  形（逐 n 透传进 `filter_upwards`；`∀ n` 形由 `Eventually.of_forall` 给）；
* 其余（records / canonical family / 参数极限 / pinching / `hR` / `hRt` / `hρ` / `D, θ` / `hnot`）逐字。
结论逐字（`∀ A > 0, ∃ Q ≥ 1, ∀ᶠ n, …`）。

consumer `hanchor0_of_closure_data_P6L`：从 `ObservedHistory.false_of_not_good_extendAt_P6D2`
（`Ch11/P6ClosureP6D2.lean`）的数据前提（`hpar` / `hqcan` / `hθcap` / `hpinch` / `hslab` / `hderG` /
`hqR` / `hnot` / `hRt`）+ SLT 的 `U` 侧前提，输出该定理 `hanchor0` 的**逐字**形（`Q ≥ 2`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **`_P6L`（SLT:336 序列形，局部化）**：原
`RetainedCoreHistory.eventually_scalar_bound_at_distance_of_not_capWindowPoint_terminal`。
区域 `U n` + `hU`（每个固定尺度球 eventually 含于 `U n`）；`hW` / `hslabs` / `hder` / `hgrad` / `hnc`
限于 `U n` 且只要 eventually。其余前提与结论逐字。 -/
theorem RetainedCoreHistory.eventually_scalar_bound_at_distance_of_not_capWindowPoint_terminal_P6L
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cq θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (H : ℕ → RetainedCoreHistory.{u})
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (p₀ : ℕ → CutoffParameters) (δbound ρbound : ℕ → ℝ) {p : ℕ → CutoffParameters}
    (records : ∀ n (i : Fin (H n).eventCount), GeometricCutoffRecord (H n).toHistory i (p n))
    (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δbound n) (ρbound n) (records n))
    (hradius : Tendsto (fun n => (p₀ n).modelRadius) atTop atTop)
    (horder : ∀ n, 2 ≤ (p₀ n).modelOrder)
    (haccuracy : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p₀ n).modelAccuracy ≤ ζ)
    (t : ℕ → ℝ) (ht : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n)
    (hts : ∀ n, t n < s n) (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (q ρ : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hqy : ∀ n, q n ≤ Cq * (G n).flow.scalar (t n) (y n))
    (hR : Tendsto (fun n => (G n).flow.scalar (t n) (y n)) atTop atTop)
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    (U : ∀ n, Set ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (hU : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ w ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))), w ∈ U n)
    (hW : ∀ᶠ n in atTop, ∀ x ∈ U n, q n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hslabs : ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U n, ∀ B : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
        (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hder : ∀ᶠ n in atTop, ∀ x ∈ U n,
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      q n < (G n).flow.scalar v x →
      |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
        Ctime * (G n).flow.scalar v x ^ 2)
    (hgrad : ∀ᶠ n in atTop, ∀ x ∈ U n,
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      q n < (G n).flow.scalar v x → ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential (G n).flow v x w| ≤
          Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
            Real.sqrt (((G n).flow.base.metric v).inner x w w))
    (hpinch : ∀ n, (H n).EventSlabsPinched phi)
    (hpinchG : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hnc : ∀ᶠ n in atTop, ∀ (T : ℝ) (hT : (H n).time (Fin.last (H n).eventCount) < T)
      (hTs : T < s n), T ≤ t n →
        let B := (H n).extendHorizon T (hend n ▸ hT.le) ((G n).closedPrefix T hT hTs) (hG n)
        let tm : Icc (0 : ℝ) B.horizon :=
          ⟨T, (H n).horizon_nonneg.trans (hend n ▸ hT.le), le_rfl⟩
        ∀ z ∈ U n, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρ n →
          B.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  yy b))
    (hρ : Tendsto (fun n => ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (D θ : ℕ → ℝ) (hD : Tendsto D atTop atTop) (hθ : ∀ n, θ₀ ≤ θ n)
    (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n)
      (D n) (θ n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n) := by
  intro A hA
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, hQ, _, _, _, hζ₀, hmain⟩ :=
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_P6L hεle κ
      C1 C2 hκ Ctime Cgrad hphi A hA Cq θ₀ hθ₀
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hradius.eventually_ge_atTop Rrad, haccuracy ζ₀ hζ₀, hR.eventually_ge_atTop Λ,
    hRt.eventually_ge_atTop Λ, hρ.eventually_ge_atTop Λ, hD.eventually_ge_atTop Dcap, hU Rad, hW,
    hslabs, hder, hgrad, hnc]
    with n hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hn9 hn10 hn11 hn12
  exact hmain (H n) (hend n) (G n) (hG n) (p₀ n) (δbound n) (ρbound n) (records n)
    (hrec n) hn1 (horder n) hn2 (ht n) (hts n) (y n) (q n) (ρ n) (hq n) (hqy n) hn3 hn4 (U n) hn7
    hn8 hn9 hn10 hn11 (hpinch n) (hpinchG n) hn12 hn5
    (fun hcw => hnot n (hcw.mono hn6 (hθ n)))

/-- consumer：原 `SLT:336`（carrier 全局前提）由 `_P6L` 序列形取 `U n = univ` 推出。 -/
example : type_of%
    @RetainedCoreHistory.eventually_scalar_bound_at_distance_of_not_capWindowPoint_terminal.{u}
    := by
  intro ε hεle κ C1 C2 hκ Ctime Cgrad phi hphi Cq θ₀ hθ₀ H hend s G hG p₀ δb ρb p records hrec
    hradius horder hacc t ht hts y q ρ hq hqy hR hRt hW hslabs hder hgrad hpinch hpinchG hnc hρ
    D θ hD hθ hnot
  exact RetainedCoreHistory.eventually_scalar_bound_at_distance_of_not_capWindowPoint_terminal_P6L
    hεle hκ hphi hθ₀ H hend s G hG p₀ δb ρb records hrec hradius horder hacc t ht hts y q ρ hq hqy
    hR hRt (fun _ => univ) (fun _ => Eventually.of_forall fun _ _ _ => trivial)
    (Eventually.of_forall fun n x _ => hW n x)
    (Eventually.of_forall fun n j _ _ _ _ B v hv hRv =>
      hslabs n j (Fin.castSucc_lt_last j) _ v hv hRv)
    (Eventually.of_forall fun n x _ v hv hRv => hder n x v hv hRv)
    (Eventually.of_forall fun n x _ v hv hRv w => hgrad n x v hv hRv w) hpinch hpinchG
    (Eventually.of_forall fun n T hT hTs hTt => by
      intro _ tm _ _ yy _ b _ hbρ hball
      exact hnc n T hT hTs hTt tm yy b le_rfl hbρ hball) hρ D θ hD hθ hnot

/-- **consumer（喂 `P6ClosureP6D2` 的 `hanchor0`）**：`ObservedHistory.false_of_not_good_extendAt_P6D2`
的数据前提（`hqcan` / `hpar` / `hθcap` / `hpinch` / `hslab` / `hat` / `hts` / `hderG` / `hqR` / `hnot` /
`hRt`）+ SLT 的 `U` 侧前提（阈值 `q = 2·qcan`、`Ctime' = 2·Ctime`、`Cq = 2`、`θ₀ = 1/2`）⇒ 该定理
`hanchor0` 的逐字形（`Q ≥ 2`）。全局 `hslab`（`EventSlabsDerivative Ctime qcan`）直接给 footprint
`hslabs`，`hderG` 直接给 `hder`；`U` 侧只剩 `hU` / `hW` / `hgrad` / `hnc` / `hρ`。 -/
theorem RetainedCoreHistory.hanchor0_of_closure_data_P6L
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t ρ : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n)
      (D n) (θcap n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    (U : ∀ n, Set ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (hU : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ w ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))), w ∈ U n)
    (hW : ∀ᶠ n in atTop, ∀ x ∈ U n, 2 * qcan n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hgrad : ∀ᶠ n in atTop, ∀ x ∈ U n,
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      2 * qcan n < (G n).flow.scalar v x → ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential (G n).flow v x w| ≤
          Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
            Real.sqrt (((G n).flow.base.metric v).inner x w w))
    (hnc : ∀ᶠ n in atTop, ∀ (T : ℝ) (hT : (H n).time (Fin.last (H n).eventCount) < T)
      (hTs : T < s n), T ≤ t n →
        let B := (H n).extendHorizon T (hend n ▸ hT.le) ((G n).closedPrefix T hT hTs) (hGi n)
        let tm : Icc (0 : ℝ) B.horizon :=
          ⟨T, (H n).horizon_nonneg.trans (hend n ▸ hT.le), le_rfl⟩
        ∀ z ∈ U n, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρ n →
          B.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  yy b))
    (hρ : Tendsto (fun n => ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n) := by
  have hq0 (n : ℕ) : 0 < qcan n := by
    have := hqcan n
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun n => (G n).flow.scalar (t n) (y n)) atTop atTop :=
    tendsto_atTop_mono (fun n => (hqcan n).trans (hqR n).le) hnat
  have hradius : Tendsto (fun n => (p₀ n).modelRadius) atTop atTop :=
    tendsto_atTop_mono (fun n => (hpar n).2.1.trans (hpar n).2.2.1) hnat
  have hDt : Tendsto D atTop atTop := tendsto_atTop_mono (fun n => (hpar n).2.1) hnat
  have hacc : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p₀ n).modelAccuracy ≤ ζ := by
    intro ζ hζ
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hζ)] with n hn
    exact (hpar n).1.trans hn
  have hθ (n : ℕ) : (1 : ℝ) / 2 ≤ θcap n := by
    refine le_trans ?_ (hθcap n)
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    linarith
  have hord (n : ℕ) : 2 ≤ (p₀ n).modelOrder := le_trans (by omega) (hpar n).2.2.2.1
  have hctime : ((2 * Ctime : ℝ≥0) : ℝ) = 2 * (Ctime : ℝ) := by push_cast; ring
  intro A hA
  obtain ⟨Q, hQ, hev⟩ :=
    RetainedCoreHistory.eventually_scalar_bound_at_distance_of_not_capWindowPoint_terminal_P6L
      (Ctime := 2 * Ctime) (Cq := 2) hεle hκ hphi (by norm_num : (0 : ℝ) < 1 / 2) H hend s G hGi
      p₀ δb ρb records hrec hradius hord hacc t hat hts y (fun n => 2 * qcan n) ρ
      (fun n => by have := hq0 n; positivity) (fun n => by have := hqR n; linarith) hR hRt U hU
      hW
      (Eventually.of_forall fun n j first hf z _ B v hv hRv => by
        have hlt : qcan n < ((H n).toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) := by
          have := hq0 n
          linarith
        have h := hslab n j (Fin.castSucc_lt_last j) _ v hv hlt
        rw [hctime]
        have h0 : 0 ≤ (Ctime : ℝ) * ((H n).toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) ^ 2 :=
          mul_nonneg Ctime.coe_nonneg (sq_nonneg _)
        linarith)
      (Eventually.of_forall fun n x _ v hv hRv => hderG n x v hv hRv) hgrad
      (fun n => (hpinch n).1) (fun n => (hpinch n).2) hnc hρ D θcap hDt hθ hnot A hA
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  filter_upwards [hev] with n hn z hz
  refine (hn z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact ((hq0 n).trans (hqR n)).le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
