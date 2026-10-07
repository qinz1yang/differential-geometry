import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceSliceTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceSliceTerminal_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceSliceLateRecords_P6N
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceSliceRebaseWindow_P6WB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceTracedPositiveWindow_P6WB

/-!
# P6WIN-B G4：`SliceTerminal:45/249`（E-local 终点）的时间窗形（`_P6WB`）

P6CON G2b 窗口 spine（A 段 → 02:43 RELEASE 给 B）：`SLT:249_P6L` 在窗口 `[t - Bw / R(t, y), t]` 内用
history 前提（接口约定 §4）。相对 `_P6L`：
* 常数 `∃ Q Λ Dcap Rrad ζ₀ Rad Bw`（`0 < Bw`，history 前取）。反证里取第 `n` 个反例的 `Bw n = n + 1 + θ`：
  窗口起点 `a n = t n - Bw n / R(t n, y n)`，`TP:55` 的 `hQa : Q n (t n - a n) → ∞` 由
  `Q n ≥ R(t n, y n)` 给 `Q n (t n - a n) ≥ Bw n ≥ n + 1`；SL 层 `a ≤ t - τ`（`τ` 为 `htrace` 的深度）由
  `4 M τ ≤ θ`、`6 R ≤ M`、`θ ≤ Bw n` 推出 `τ ≤ Bw n / R`。
* records 用 G2a 的 late 形：`T₀ ≤ t - Bw / R(t, y)`，`records : ∀ i, T₀ ≤ time i.succ → …`；
  `IsCanonicalCutoffRecordFamily` 展开为证明实际用到的四条（`hcan`、`Rrad ≤ p.modelRadius`、
  `2 ≤ p.modelOrder`、`p.modelAccuracy ≤ ζ₀`；其余合取项与 `p₀ δbound ρbound` 未被用，去掉）；
  `hnot` 为 `¬ CapWindowPoint` 的 late 展开形（同 G2a）。
* `hslabs` / `hder` / `hgrad`：`∀ v ∈ Ioo …,` 后 guard `t - Bw / R(t, y) ≤ v →`；`EventSlabsPinched`
  与 `hpinchG` 取 `… ∩ Ici (t - Bw / R(t, y))`；`hnc` 的 `T ≤ t` 后加 `t - Bw / R(t, y) ≤ T →`。
* 叶子：SL:73 late（`SliceLateRecords_P6N`）、rebase chain 窗口版（`SliceRebaseWindow_P6WB`）、
  `TP:55` 窗口版（`TracedPositiveWindow_P6WB`）。
私有成员关系引理（`_P6L` 副本）复制为 `_P6WB`。其余证明体照抄；结论逐字。
consumer：`SLT:249_P6L`（全 slab / 全 family 形）⇐ 窗口形（`T₀ = t - Bw / R`）。
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

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- 成员关系辅助：`d(y, w) ≤ a`、`d(w, v) < b`、`a + b ≤ r`、`B(y, r) ⊆ U` ⇒ `v ∈ U`。 -/
private theorem mem_of_edist_le_of_lt_P6WB {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : Set M) (y w v : M) {a b r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ r) (hU : ∀ x ∈ riemannianBallOf g y r, x ∈ U)
    (hw : riemannianEDistOf g y w ≤ ENNReal.ofReal a)
    (hv : riemannianEDistOf g w v < ENNReal.ofReal b) : v ∈ U := by
  apply hU
  change riemannianEDistOf g y v < ENNReal.ofReal r
  calc riemannianEDistOf g y v ≤ riemannianEDistOf g y w + riemannianEDistOf g w v :=
        riemannianEDistOf_triangle _ _ _ _
    _ < ENNReal.ofReal a + ENNReal.ofReal b :=
        ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hw) hw hv
    _ = ENNReal.ofReal (a + b) := (ENNReal.ofReal_add ha hb).symm
    _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hab

/-- 链距离：`p (k+1) ∈ B(p k, r₀)`（`k < N`）⇒ `d(p 0, p k) ≤ k·r₀`（`k ≤ N`）。 -/
private theorem edist_chain_le_P6WB {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) (p : ℕ → M) {r₀ : ℝ} (hr₀ : 0 ≤ r₀) {N : ℕ}
    (hchain : ∀ k < N, p (k + 1) ∈ riemannianBallOf g (p k) r₀) :
    ∀ k ≤ N, riemannianEDistOf g (p 0) (p k) ≤ ENNReal.ofReal (k * r₀) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [riemannianEDistOf_self]
    exact zero_le
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 : riemannianEDistOf g (p k) (p (k + 1)) < ENNReal.ofReal r₀ := hchain k (by omega)
    calc riemannianEDistOf g (p 0) (p (k + 1)) ≤
          riemannianEDistOf g (p 0) (p k) + riemannianEDistOf g (p k) (p (k + 1)) :=
          riemannianEDistOf_triangle _ _ _ _
      _ ≤ ENNReal.ofReal (k * r₀) + ENNReal.ofReal r₀ := add_le_add h1 h2.le
      _ = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * r₀) := by
          rw [← ENNReal.ofReal_add (by positivity) hr₀]
          push_cast
          ring_nf

/-- rebase 链生成形成员（SliceRebase_P6L 的 `hU`）：`B(y, Rad/√R) ⊆ U`、`A + 1 ≤ Rad`、`R ≤ m`、
`c ≤ 1/20` ⇒ `d(y, w) < A/√R` 时 `B(w, 4c/√(2m)) ⊆ U`。 -/
private theorem rebase_ball_subset_P6WB {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : Set M) (y : M) {A R m c Rad : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hRm : R ≤ m) (hc0 : 0 < c) (hc : c ≤ 1 / 20) (hRad : A + 1 ≤ Rad)
    (hUy : ∀ w ∈ riemannianBallOf g y (Rad / Real.sqrt R), w ∈ U) :
    ∀ w, riemannianEDistOf g y w < ENNReal.ofReal (A / Real.sqrt R) →
      riemannianBallOf g w (2 * (2 * (c / Real.sqrt (2 * m)))) ⊆ U := by
  intro w hw v hv
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hs : Real.sqrt R ≤ Real.sqrt (2 * m) := Real.sqrt_le_sqrt (by linarith)
  have hb : c / Real.sqrt (2 * m) ≤ c / Real.sqrt R := div_le_div_of_nonneg_left hc0.le hsR hs
  have hc' : c / Real.sqrt R ≤ (1 / 20) / Real.sqrt R := div_le_div_of_nonneg_right hc hsR.le
  refine mem_of_edist_le_of_lt_P6WB g U y w v (a := A / Real.sqrt R)
    (b := 2 * (2 * (c / Real.sqrt (2 * m)))) (div_nonneg hA.le (Real.sqrt_nonneg R))
    (by positivity) ?_ hUy hw.le hv
  have hsum : A / Real.sqrt R + (1 / 20 + 1 / 20 + 1 / 20 + 1 / 20) / Real.sqrt R ≤
      Rad / Real.sqrt R := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hsR.le
  have h4 : (1 / 20 + 1 / 20 + 1 / 20 + 1 / 20) / Real.sqrt R = 4 * ((1 / 20) / Real.sqrt R) := by
    ring
  linarith

/-- rebase 链球成员（SL:73_P6L 的 `hchainUc`）：链距离 `k·r₀ ≤ N·r₀ ≤ 2A/√R + 2r₀`、
`r₀ = c/(2√(2m)) ≤ (1/20)/√R`、`2A + 1 ≤ Rad` ⇒ `B(pc k, r₀) ⊆ B(y, Rad/√R) ⊆ U`。 -/
private theorem chain_ball_subset_P6WB {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : Set M) (y : M) (pc : ℕ → M)
    {A R m c Rad : ℝ} {Nc : ℕ} (hR : 0 < R) (hRm : R ≤ m) (hc0 : 0 < c) (hc : c ≤ 1 / 20)
    (hpc0 : pc 0 = y)
    (hchain : ∀ k < Nc, pc (k + 1) ∈ riemannianBallOf g (pc k) (c / (2 * Real.sqrt (2 * m))))
    (hNc : (Nc : ℝ) * (c / (2 * Real.sqrt (2 * m))) ≤
      2 * (A / Real.sqrt R) + 2 * (c / (2 * Real.sqrt (2 * m))))
    (hRad : 2 * A + 1 ≤ Rad)
    (hUy : ∀ w ∈ riemannianBallOf g y (Rad / Real.sqrt R), w ∈ U) :
    ∀ k < Nc, ∀ w ∈ riemannianBallOf g (pc k) (c / (2 * Real.sqrt (2 * m))), w ∈ U := by
  intro k hk w hw
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hs : Real.sqrt R ≤ Real.sqrt (2 * m) := Real.sqrt_le_sqrt (by linarith)
  have hm : 0 < Real.sqrt (2 * m) := hsR.trans_le hs
  have hr₀ : 0 < c / (2 * Real.sqrt (2 * m)) := by positivity
  have hd := edist_chain_le_P6WB g pc hr₀.le hchain k hk.le
  rw [hpc0] at hd
  have hkN : (k : ℝ) * (c / (2 * Real.sqrt (2 * m))) ≤
      (Nc : ℝ) * (c / (2 * Real.sqrt (2 * m))) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk.le) hr₀.le
  have hr₀le : c / (2 * Real.sqrt (2 * m)) ≤ (1 / 20) / Real.sqrt R := by
    have h2 : Real.sqrt R ≤ 2 * Real.sqrt (2 * m) := by linarith
    calc _ ≤ c / Real.sqrt R := div_le_div_of_nonneg_left hc0.le hsR h2
      _ ≤ _ := div_le_div_of_nonneg_right hc hsR.le
  refine mem_of_edist_le_of_lt_P6WB g U y (pc k) w (a := (k : ℝ) * (c / (2 * Real.sqrt (2 * m))))
    (b := c / (2 * Real.sqrt (2 * m))) (by positivity) hr₀.le ?_ hUy hd hw
  have hsum : 2 * (A / Real.sqrt R) + 3 * ((1 / 20) / Real.sqrt R) ≤ Rad / Real.sqrt R := by
    rw [show 2 * (A / Real.sqrt R) + 3 * ((1 / 20) / Real.sqrt R) =
      (2 * A + 3 / 20) / Real.sqrt R by ring]
    exact div_le_div_of_nonneg_right (by linarith) hsR.le
  linarith

/-- TP:97_P6L 的 `hU` 来源：`d_s(y, x) < A/√R`、`R ≤ Q`、`B_s(y, Rad/√R) ⊆ U`、`A + Rtp ≤ Rad`
⇒ `B_{Q·L}(x, Rtp) ⊆ U`（scaled 球换端点度量球，`riemannianBallOf_scaleMetric`）。 -/
private theorem scaled_ball_subset_of_base_ball_P6WB {P : OrientedThreeStage.{u}} {a s : ℝ}
    (A : P.ClosedSlab a s) {Q R Ar Rtp Rad : ℝ} (hQ : 0 < Q) (hR : 0 < R) (hRQ : R ≤ Q)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) (y : P.Carrier)
    (U : Set P.Carrier)
    (hxy : riemannianEDistOf (A.flow.base.metric s) y x.val < ENNReal.ofReal (Ar / Real.sqrt R))
    (hAr : 0 ≤ Ar) (hRtp : 0 ≤ Rtp) (hRad : Ar + Rtp ≤ Rad)
    (hUy : ∀ w ∈ riemannianBallOf (A.flow.base.metric s) y (Rad / Real.sqrt R), w ∈ U) :
    ∀ w ∈ riemannianBallOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x Rtp,
      w.val ∈ U := by
  intro w hw
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  rw [show Rtp = Real.sqrt Q * (Rtp / Real.sqrt Q) from (mul_div_cancel₀ _ hsQ.ne').symm,
    DifferentialGeometry.riemannianBallOf_scaleMetric] at hw
  have hw' : riemannianEDistOf (A.flow.base.metric s) x.val w.val <
      ENNReal.ofReal (Rtp / Real.sqrt Q) := by
    have h := hw
    change riemannianEDistOf (A.endpointTerminalLimitMetric P).metric x w < _ at h
    rwa [A.riemannianEDistOf_endpointTerminalLimitMetric] at h
  have hle : Rtp / Real.sqrt Q ≤ Rtp / Real.sqrt R :=
    div_le_div_of_nonneg_left hRtp hsR (Real.sqrt_le_sqrt hRQ)
  refine mem_of_edist_le_of_lt_P6WB _ U y x.val w.val (a := Ar / Real.sqrt R)
    (b := Rtp / Real.sqrt Q) (by positivity) (by positivity) ?_ hUy hxy.le hw'
  have hsum : Ar / Real.sqrt R + Rtp / Real.sqrt R ≤ Rad / Real.sqrt R := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right hRad hsR.le
  linarith

private theorem rebase_lam_bound_P6WB {A K Q R r₀ L : ℝ} (hA : 0 < A) (hK : 1 ≤ K) (hR : 0 < R)
    (hRQ : R ≤ Q) (hQK : Q ≤ K * R) (hL : 0 < L) (hr₀ : r₀ = L / (2 * Real.sqrt (2 * Q)))
    {N : ℕ} (hN : (N : ℝ) * r₀ ≤ 2 * (A / Real.sqrt R) + 2 * r₀) :
    (N : ℝ) * r₀ ≤ (2 * A * Real.sqrt K + L) / Real.sqrt Q := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have h1 : A / Real.sqrt R ≤ A * Real.sqrt K / Real.sqrt Q := by
    rw [div_le_div_iff₀ hsR hsQ]
    have : Real.sqrt Q ≤ Real.sqrt K * Real.sqrt R := by
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt hQK
    nlinarith
  have h2 : 2 * r₀ ≤ L / Real.sqrt Q := by
    rw [hr₀]
    have h2Q : Real.sqrt Q ≤ Real.sqrt (2 * Q) := Real.sqrt_le_sqrt (by linarith)
    rw [show 2 * (L / (2 * Real.sqrt (2 * Q))) = L / Real.sqrt (2 * Q) by field_simp]
    exact div_le_div_of_nonneg_left hL.le hsQ h2Q
  calc (N : ℝ) * r₀ ≤ 2 * (A / Real.sqrt R) + 2 * r₀ := hN
    _ ≤ 2 * (A * Real.sqrt K / Real.sqrt Q) + L / Real.sqrt Q := by linarith
    _ = (2 * A * Real.sqrt K + L) / Real.sqrt Q := by ring

private theorem false_of_terminal_counterexamples_window_P6WB {ε : ℝ}
    (heps : 13000 * (13000 * ε) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64))
    {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) {A Cq θ : ℝ} (hA : 0 < A) (hθ : 0 < θ)
    {K : ℝ} (hK : K = max Cq 1) (Dn : ℕ → ℝ) (hDn : Tendsto Dn atTop atTop)
    (Bw : ℕ → ℝ) (hBw1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ Bw n) (hBwθ : ∀ n, θ ≤ Bw n)
    (H : ℕ → RetainedCoreHistory.{u})
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    {p : ℕ → CutoffParameters} {T₀ : ℕ → ℝ}
    (records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hscale : ∀ n i hi b z, ((records n i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records n i hi).static b).witness.metric
        (((records n i hi).static b).witness.cap z))
    (hacc : ∀ n, (p n).modelAccuracy ≤ 1 / 2) (hradius : ∀ n, Dn n ≤ (p n).modelRadius)
    (t : ℕ → ℝ) (ht : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n)
    (hts : ∀ n, t n < s n) (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (q ρ : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hqy : ∀ n, q n ≤ Cq * (G n).flow.scalar (t n) (y n))
    (hΛ : ∀ n : ℕ, (n : ℝ) + K + 1 ≤ (G n).flow.scalar (t n) (y n))
    (hΛt : ∀ n : ℕ, (n : ℝ) + K + 1 ≤ (G n).flow.scalar (t n) (y n) * t n)
    (hT0 : ∀ n, T₀ n ≤ t n - Bw n / (G n).flow.scalar (t n) (y n))
    (U : ∀ n, Set ((H n).stage (Fin.last (H n).eventCount)).Carrier) {Rad : ℝ}
    (hRad : 3 * A + 2 * A * Real.sqrt K + 4 ≤ Rad)
    (hUy : ∀ n, ∀ w ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
      (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))), w ∈ U n)
    (hW : ∀ n, ∀ x ∈ U n, q n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hslabs : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U n, ∀ B : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      t n - Bw n / (G n).flow.scalar (t n) (y n) ≤ v →
      q n < ((H n).toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
        (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hder : ∀ n, ∀ x ∈ U n, ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - Bw n / (G n).flow.scalar (t n) (y n) ≤ v →
      q n < (G n).flow.scalar v x →
      |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
        Ctime * (G n).flow.scalar v x ^ 2)
    (hgrad : ∀ n, ∀ x ∈ U n, ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - Bw n / (G n).flow.scalar (t n) (y n) ≤ v →
      q n < (G n).flow.scalar v x → ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential (G n).flow v x w| ≤
          Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
            Real.sqrt (((G n).flow.base.metric v).inner x w w))
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, Perelman.PhiAlmostNonnegative
      ((H n).toHistory.event j).incoming.flow
      (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩
        Ici (t n - Bw n / (G n).flow.scalar (t n) (y n))) phi)
    (hpinchG : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩
        Ici (t n - Bw n / (G n).flow.scalar (t n) (y n))) phi)
    (hnc : ∀ n (T : ℝ) (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n),
      T ≤ t n → t n - Bw n / (G n).flow.scalar (t n) (y n) ≤ T →
      let B := (H n).extendHorizon T ((hend n) ▸ hT.le) ((G n).closedPrefix T hT hTs) (hG n)
      let tm : Icc (0 : ℝ) B.horizon :=
        ⟨T, (H n).horizon_nonneg.trans ((hend n) ▸ hT.le), le_rfl⟩
      ∀ z ∈ U n, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
      ∀ (b : ℝ), 0 < b → b ≤ ρ n →
        B.toHistory.isParabolicallyRmControlledBall tm yy b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) yy b))
    (hρ : ∀ n : ℕ, (n : ℝ) + K + 1 ≤ ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n)))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hT : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (B : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      B.point j.succ le_rfl hl = ((records n j hT).static b).window x ∧
        ‖x.val‖ < Dn n + 1 ∧
        t n - (H n).time j.succ ≤ θ * (((records n j hT).static b).neck.scale)⁻¹)
    (z : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (hz : ∀ n, z n ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
      (A / Real.sqrt ((G n).flow.scalar (t n) (y n))))
    (hbad : ∀ n : ℕ, ((n : ℝ) + K + 1) * (G n).flow.scalar (t n) (y n) <
      (G n).flow.scalar (t n) (z n)) : False := by
  have hK1 : 1 ≤ K := hK ▸ le_max_right _ _
  have hn0 (n : ℕ) : (0 : ℝ) ≤ n := n.cast_nonneg
  have hRpos (n : ℕ) : 0 < (G n).flow.scalar (t n) (y n) := by linarith [hΛ n, hn0 n]
  have hBwpos (n : ℕ) : 0 < Bw n := by linarith [hBw1 n, hn0 n]
  let a : ℕ → ℝ := fun n => t n - Bw n / (G n).flow.scalar (t n) (y n)
  have hat (n : ℕ) : a n < t n := sub_lt_self _ (div_pos (hBwpos n) (hRpos n))
  have hqK (n : ℕ) : q n ≤ K * (G n).flow.scalar (t n) (y n) :=
    (hqy n).trans (mul_le_mul_of_nonneg_right (hK ▸ le_max_left _ _) (hRpos n).le)
  let Asl : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).ClosedSlab
      ((H n).time (Fin.last (H n).eventCount)) (t n) := fun n =>
    (G n).closedPrefix (t n) (ht n) (hts n)
  have hzmax (n : ℕ) : max (q n) ((G n).flow.scalar (t n) (y n)) ≤
      (G n).flow.scalar (t n) (z n) := by
    refine max_le ?_ ?_
    · nlinarith [hbad n, hqK n, hRpos n, hn0 n]
    · nlinarith [hbad n, hRpos n, hn0 n]
  have hlpr := localPropagationRadius_pos Cgrad.coe_nonneg
  have hlpr' := localPropagationRadius_le Cgrad.coe_nonneg
  have hsR (n : ℕ) : 0 < Real.sqrt ((G n).flow.scalar (t n) (y n)) := Real.sqrt_pos.mpr (hRpos n)
  have hsRm (n : ℕ) : Real.sqrt ((G n).flow.scalar (t n) (y n)) ≤
      Real.sqrt (2 * max (q n) ((G n).flow.scalar (t n) (y n))) :=
    Real.sqrt_le_sqrt (by linarith [le_max_right (q n) ((G n).flow.scalar (t n) (y n)), hRpos n])
  have hsRm' (n : ℕ) : Real.sqrt ((G n).flow.scalar (t n) (y n)) ≤
      Real.sqrt (max (q n) ((G n).flow.scalar (t n) (y n))) :=
    Real.sqrt_le_sqrt (le_max_right _ _)
  have hRadA : A + 1 ≤ Rad := by
    have : 0 ≤ 2 * A * Real.sqrt K := by positivity
    linarith
  have hUreb (n : ℕ) := rebase_ball_subset_P6WB ((G n).flow.base.metric (t n)) (U n) (y n) hA
    (hRpos n) (le_max_right (q n) ((G n).flow.scalar (t n) (y n))) hlpr hlpr' hRadA (hUy n)
  choose xc Nc pc hxc hxy hpc0 hpcN hchainc hMc hNc using fun n =>
    (Asl n).exists_rebase_chain_window_P6WB Cgrad (hq n) (U n) (a n) (hat n)
      (fun y' hy' t' ht' hat' hq' v => hgrad n y' hy' t' ht' hat' hq' v)
      (y n) (z n) (hz n) (hzmax n) (hUreb n)
  have hQy (n : ℕ) : (G n).flow.scalar (t n) (y n) ≤ max (q n) ((G n).flow.scalar (t n) (y n)) :=
    le_max_right _ _
  have hQK (n : ℕ) : max (q n) ((G n).flow.scalar (t n) (y n)) ≤
      K * (G n).flow.scalar (t n) (y n) :=
    max_le (hqK n) (le_mul_of_one_le_left (hRpos n).le hK1)
  have hU (n : ℕ) (w : ((H n).stage (Fin.last (H n).eventCount)).Carrier) :
      w ∈ ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen := by
    change w ∈ ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularRegion
    rw [(Asl n).terminalRegularRegion_eq_univ _]
    trivial
  let x : ∀ n, ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen :=
    fun n => ⟨xc n, hU n (xc n)⟩
  have hxQ (n : ℕ) : (Asl n).flow.scalar (t n) (x n).val =
      max (q n) ((G n).flow.scalar (t n) (y n)) := hxc n
  have hQ1 (n : ℕ) : 1 ≤ (Asl n).flow.scalar (t n) (x n).val := by
    rw [hxQ n]
    linarith [hQy n, hΛ n, hn0 n]
  have hlp := localPropagationRadius_pos Cgrad.coe_nonneg
  have hr₀ (n : ℕ) : 0 < localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * max (q n) ((G n).flow.scalar (t n) (y n)))) := by
    have : 0 < max (q n) ((G n).flow.scalar (t n) (y n)) := (hq n).trans_le (le_max_left _ _)
    positivity
  have hlamc (n : ℕ) : ∑ k ∈ Finset.range (Nc n), (fun _ : ℕ => localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * max (q n) ((G n).flow.scalar (t n) (y n))))) k ≤
      (2 * A * Real.sqrt K + localPropagationRadius Cgrad) /
        Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hxQ n]
    exact rebase_lam_bound_P6WB hA hK1 (hRpos n) (hQy n) (hQK n) hlp rfl (hNc n)
  have hRad2 : 2 * A + 1 ≤ Rad := by
    have : 0 ≤ 2 * A * Real.sqrt K := by positivity
    linarith
  have hchainUc (n : ℕ) := chain_ball_subset_P6WB ((G n).flow.base.metric (t n)) (U n) (y n)
    (pc n) (hRpos n) (le_max_right (q n) ((G n).flow.scalar (t n) (y n))) hlpr hlpr' (hpc0 n)
    (hchainc n) (hNc n) hRad2 (hUy n)
  have htr (n : ℕ) :=
    RetainedCoreHistory.chain_traces_of_not_capWindowPoint_of_incomingSlab_late_P6N
    (H n) (hend n) (G n) (hG n) (ht n) (hts n) (records n) (hcan n) (hscale n) (hacc n) hphi
    (a n) (hT0 n) (hpinch n) (hpinchG n) (U n) (hslabs n) (hder n) le_rfl (hradius n) (y n)
    (hnot n) (pc n)
    (fun _ => localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * max (q n) ((G n).flow.scalar (t n) (y n))))) (hpc0 n)
    (fun _ _ => hr₀ n) (hchainc n) (hchainUc n) (hMc n) (hlamc n)
  have hRad3 : A + (2 * A * Real.sqrt K + 3) ≤ Rad := by linarith
  have hUTP (n : ℕ) := scaled_ball_subset_of_base_ball_P6WB (Asl n)
    (zero_lt_one.trans_le (hQ1 n)) (hRpos n)
    (by rw [hxQ n]; exact le_max_right _ _) (x n) (y n) (U n) (hxy n) hA.le
    (by positivity : (0 : ℝ) ≤ 2 * A * Real.sqrt K + 3) hRad3 (hUy n)
  have hlam : 0 ≤ 2 * A * Real.sqrt K + localPropagationRadius Cgrad := by positivity
  have hDn' : Tendsto Dn atTop atTop := hDn
  have hQlim : Tendsto (fun n => (Asl n).flow.scalar (t n) (x n).val) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    rw [hxQ n]
    linarith [hQy n, hΛ n, hK1]
  have htime : Tendsto (fun n => (Asl n).flow.scalar (t n) (x n).val * t n) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    have ht0 : 0 ≤ t n := ((H n).toHistory.time_nonneg _).trans (ht n).le
    rw [hxQ n]
    have := mul_le_mul_of_nonneg_right (hQy n) ht0
    linarith [hΛt n, hK1]
  have hσQ (n : ℕ) : 1 ≤ ρ n * Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) := by
    have h1 : 1 ≤ ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n)) :=
      le_trans (by linarith [hn0 n]) (hρ n)
    have hρpos : 0 ≤ ρ n := by
      by_contra hneg
      have := mul_nonpos_of_nonpos_of_nonneg (not_le.mp hneg).le
        (Real.sqrt_nonneg ((G n).flow.scalar (t n) (y n)))
      linarith
    rw [hxQ n]
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hQy n)) hρpos)
  have hQa : Tendsto (fun n => (Asl n).flow.scalar (t n) (x n).val * (t n - a n)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    have hsub : t n - a n = Bw n / (G n).flow.scalar (t n) (y n) := sub_sub_cancel _ _
    rw [hxQ n, hsub, mul_div_assoc', le_div_iff₀ (hRpos n)]
    calc ((n : ℝ) + 1) * (G n).flow.scalar (t n) (y n)
        ≤ Bw n * (G n).flow.scalar (t n) (y n) :=
          mul_le_mul_of_nonneg_right (hBw1 n) (hRpos n).le
      _ ≤ Bw n * max (q n) ((G n).flow.scalar (t n) (y n)) :=
          mul_le_mul_of_nonneg_left (hQy n) (hBwpos n).le
      _ = max (q n) ((G n).flow.scalar (t n) (y n)) * Bw n := mul_comm _ _
  obtain ⟨B, hB⟩ := RetainedCoreHistory.exists_normalized_scalar_bound_of_chain_traces_window_P6WB
    H t Asl (fun n => hG n) (fun n => (hend n) ▸ ht n) Ctime Cgrad q hq U a hat
    hslabs
    (fun n y' hy' t' ht' hat' hq' => hder n y' hy' t' ht' hat' hq')
    (fun n y' hy' t' ht' hat' hq' v => hgrad n y' hy' t' ht' hat' hq' v) x hQ1
    (fun n => by rw [hxQ n]; exact le_max_left _ _) hQa (2 * A * Real.sqrt K + 3) hUTP hQlim hphi
    (fun n => hpinch n)
    (fun n τ hτ w => hpinchG n τ ⟨⟨hτ.1.1, hτ.1.2.trans (hts n)⟩, hτ.2⟩ w) ρ hκ one_pos hσQ
    (fun n T hT hTt haT => by
      intro _ tm zz hzz yy hyy b hb hbρ hball
      exact hnc n T (by rw [hend n]; exact hT) (hTt.trans (hts n)) hTt.le haT zz hzz yy hyy b hb
        hbρ hball)
    heps (fun n => hW n) htime (Kc := 6) hlam hθ Dn hDn'
    (fun n N pp δ M τ h0 hδ hUm hch hb hKc h1 hτ0 hτt hC h4 hDD => by
      have hKc' : 6 * max (q n) ((G n).flow.scalar (t n) (y n)) ≤ M := by
        rw [hxQ n] at hKc
        exact hKc
      have hM6 : 6 * (G n).flow.scalar (t n) (y n) ≤ M :=
        le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)) hKc'
      have hτB : τ * (G n).flow.scalar (t n) (y n) ≤ Bw n := by
        have h24 : 24 * ((G n).flow.scalar (t n) (y n) * τ) ≤ 4 * M * τ := by
          nlinarith [mul_nonneg hτ0 (sub_nonneg.mpr hM6)]
        nlinarith [hBwθ n, mul_comm τ ((G n).flow.scalar (t n) (y n)), hθ]
      have haτ : a n ≤ t n - τ := by
        have : τ ≤ Bw n / (G n).flow.scalar (t n) (y n) := (le_div_iff₀ (hRpos n)).mpr hτB
        change t n - Bw n / (G n).flow.scalar (t n) (y n) ≤ t n - τ
        linarith
      exact htr n N pp δ M τ (h0.trans (hpcN n).symm) hδ hUm hch hb hKc' (by
          have := le_max_left (q n) ((G n).flow.scalar (t n) (y n))
          linarith) h1 hτ0 hτt haτ hC h4 hDD)
    (2 * A * Real.sqrt K + 1) (by positivity) (by linarith)
  obtain ⟨n, hn, hnB⟩ := (hB.and (eventually_gt_atTop ⌈B * K⌉₊)).exists
  let z' : ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen :=
    ⟨z n, hU n (z n)⟩
  have hsx : 0 < Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (hQ1 n))
  have hsy : 0 < Real.sqrt ((G n).flow.scalar (t n) (y n)) := Real.sqrt_pos.mpr (hRpos n)
  have hratio : Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) ≤
      Real.sqrt K * Real.sqrt ((G n).flow.scalar (t n) (y n)) := by
    rw [← Real.sqrt_mul (by linarith), hxQ n]
    exact Real.sqrt_le_sqrt (hQK n)
  have hxz : riemannianEDistOf ((G n).flow.base.metric (t n)) (xc n) (z n) <
      ENNReal.ofReal (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))) := by
    calc riemannianEDistOf ((G n).flow.base.metric (t n)) (xc n) (z n)
        ≤ riemannianEDistOf ((G n).flow.base.metric (t n)) (xc n) (y n) +
          riemannianEDistOf ((G n).flow.base.metric (t n)) (y n) (z n) :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (A / Real.sqrt ((G n).flow.scalar (t n) (y n))) +
          ENNReal.ofReal (A / Real.sqrt ((G n).flow.scalar (t n) (y n))) := by
          rw [riemannianEDistOf_comm]
          exact ENNReal.add_lt_add (hxy n) (hz n)
      _ = ENNReal.ofReal (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))) := by
          rw [← ENNReal.ofReal_add (div_nonneg hA.le (Real.sqrt_nonneg _))
            (div_nonneg hA.le (Real.sqrt_nonneg _))]
          ring_nf
  have hdist : riemannianEDistOf (scaleMetric ((Asl n).flow.scalar (t n) (x n).val)
      (zero_lt_one.trans_le (hQ1 n))
      ((Asl n).endpointTerminalLimitMetric _).metric) (x n) z' <
        ENNReal.ofReal (2 * A * Real.sqrt K + 1) := by
    rw [(Asl n).scaled_endpoint_edist_eq]
    calc ENNReal.ofReal (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val)) *
          riemannianEDistOf ((Asl n).flow.base.metric (t n)) (x n).val z'.val <
        ENNReal.ofReal (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val)) *
          ENNReal.ofReal (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))) :=
          ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hsx).ne' ENNReal.ofReal_ne_top hxz
      _ = ENNReal.ofReal (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) *
          (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n))))) :=
          (ENNReal.ofReal_mul hsx.le).symm
      _ ≤ ENNReal.ofReal (2 * A * Real.sqrt K) := by
          apply ENNReal.ofReal_le_ofReal
          rw [show Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) *
            (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))) =
            2 * A * (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) /
              Real.sqrt ((G n).flow.scalar (t n) (y n))) by ring]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ hsy]
          exact hratio
      _ < ENNReal.ofReal (2 * A * Real.sqrt K + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hle := hn z' hdist
  have hscal : metricScalarAt ((Asl n).endpointTerminalLimitMetric _).metric z' =
      (G n).flow.scalar (t n) (z n) := metricScalarAt_restrictOpen _ _ _
  rw [hscal, div_le_iff₀ (zero_lt_one.trans_le (hQ1 n)), hxQ n] at hle
  have hceil : B * K ≤ (n : ℝ) := (Nat.le_ceil (B * K)).trans (by exact_mod_cast hnB.le)
  have hbig := hbad n
  have hQKn := hQK n
  have hRyn := hRpos n
  have hn1 := hn0 n
  rcases le_or_gt 0 B with hB0 | hB0
  · have h1 : B * max (q n) ((G n).flow.scalar (t n) (y n)) ≤
        B * (K * (G n).flow.scalar (t n) (y n)) := mul_le_mul_of_nonneg_left hQKn hB0
    have h2 : B * K * (G n).flow.scalar (t n) (y n) ≤ n * (G n).flow.scalar (t n) (y n) :=
      mul_le_mul_of_nonneg_right hceil hRyn.le
    linarith [mul_nonneg (zero_le_one.trans hK1) hRyn.le]
  · have h1 : B * max (q n) ((G n).flow.scalar (t n) (y n)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hB0.le (by linarith [hQy n])
    linarith [mul_nonneg (zero_le_one.trans hK1) hRyn.le, mul_nonneg hn1 hRyn.le]

/-- **`_window_P6WB`（`SLT:249` E-local 终点的时间窗形）**：`_P6L` 之上：常数多取窗口深度 `Bw`（`0 < Bw`，
history 前取）；records 用 G2a 的 late 形（`T₀`，`records : ∀ i, T₀ ≤ time i.succ → …`，
`IsCanonicalCutoffRecordFamily` 展开为实际用到的四条：`hcan`、`Rrad ≤ p.modelRadius`、
`2 ≤ p.modelOrder`、`p.modelAccuracy ≤ ζ₀`）；`T₀ ≤ t - Bw / R(t, y)`；`hslabs` / `hder` / `hgrad` 的
`∀ v ∈ Ioo …,` 后 guard `t - Bw / R(t, y) ≤ v →`；pinching 取 `… ∩ Ici (t - Bw / R(t, y))`
（`hpinch` 逐 event）；`hnc` 的 `T ≤ t` 后加 `t - Bw / R(t, y) ≤ T →`；`hnot` 为 `¬ CapWindowPoint` 的
late 展开形。证明：反证取 `Bw n = n + 1 + θ`，窗口起点 `a n = t n - Bw n / R(t n, y n)`；
`TP:55` 的 `hQa` 由 `Q n ≥ R(t n, y n)` 给 `Q n (t n - a n) ≥ Bw n ≥ n + 1`；SL 层 `a ≤ t - τ`
由 `4 M τ ≤ θ`、`6 R ≤ M`、`θ ≤ Bw n` 给。 -/
theorem
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_window_P6WB
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq θ : ℝ) (hθ : 0 < θ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad Bw : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
    Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧
    ∀ (H : RetainedCoreHistory.{u})
      (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount))
      {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s)
        (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
      0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
      Λ ≤ G.flow.scalar t y * t →
      ∀ {p : CutoffParameters} (T₀ : ℝ), T₀ ≤ t - Bw / G.flow.scalar t y →
      ∀ (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        GeometricCutoffRecord H.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
      ∀ (U : Set (H.stage (Fin.last H.eventCount)).Carrier),
      (∀ w ∈ riemannianBallOf (G.flow.base.metric t) y (Rad / Real.sqrt (G.flow.scalar t y)),
        w ∈ U) →
      (∀ x ∈ U, q < G.flow.scalar t x →
        ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 x,
          W.capTubeHasNeckChart ε) →
      (∀ j : Fin H.eventCount,
        ∀ (first : Fin (H.eventCount + 1)) (hf : first ≤ j.castSucc),
        ∀ z ∈ U, ∀ B : BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
          (Fin.le_last first) z,
        ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ), t - Bw / G.flow.scalar t y ≤ v →
        q < (H.toHistory.event j).incoming.flow.scalar v
          (B.point j.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w
          (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) ^ 2) →
      (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
        q < G.flow.scalar v x →
        |derivWithin (fun w => G.flow.scalar w x) (Iic v) v| ≤ Ctime * G.flow.scalar v x ^ 2) →
      (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
        q < G.flow.scalar v x →
        ∀ w : TangentSpace ThreeModel x,
          |scalarDifferential G.flow v x w| ≤
            Cgrad * G.flow.scalar v x * Real.sqrt (G.flow.scalar v x) *
              Real.sqrt ((G.flow.base.metric v).inner x w w)) →
      (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (t - Bw / G.flow.scalar t y)) phi) →
      Perelman.PhiAlmostNonnegative G.flow
        (Ico (H.time (Fin.last H.eventCount)) s ∩ Ici (t - Bw / G.flow.scalar t y)) phi →
      (∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t →
        t - Bw / G.flow.scalar t y ≤ T →
        let B := H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG
        let tm : Icc (0 : ℝ) B.horizon := ⟨T, H.horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
        ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρ →
          B.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  yy b)) →
      Λ ≤ ρ * Real.sqrt (G.flow.scalar t y) →
      (¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ Fin.last H.eventCount)
        (B : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
        (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
          t - H.time j.succ ≤ θ * (((records j hT).static b).neck.scale)⁻¹) →
      ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
        G.flow.scalar t z ≤ Q * G.flow.scalar t y := by
  have heps : 13000 * (13000 * ε) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) := by
    unfold coneAccuracy at hεle
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 13000 * 13000)).mp hεle
    linarith
  have hTE := StandardCap.transitionEnd_pos
  have hn0 (n : ℕ) : (0 : ℝ) ≤ n := n.cast_nonneg
  have hDn (n : ℕ) : StandardCap.transitionEnd < StandardCap.transitionEnd + 1 + n := by
    linarith [hn0 n]
  have hK1 : (1 : ℝ) ≤ max Cq 1 := le_max_right _ _
  choose ε₀ hε₀ hsc using fun n : ℕ =>
    exists_presented_cap_scalar_lower_bound_of_canonical_window_core.{u}
      (StandardCap.transitionEnd + 1 + n) (hDn n)
  by_contra hcon
  push Not at hcon
  choose H hend s G hG t ht hts y q ρ hq hqy hΛ hΛt p T₀ hT0 records hcan hRrad hord hζ U hUy
    hW hslabs hder hgrad hpinch hpinchG hnc hρ hnot z hz hbad using fun n : ℕ =>
    hcon ((n : ℝ) + max Cq 1 + 1) ((n : ℝ) + max Cq 1 + 1) (StandardCap.transitionEnd + 1 + n)
      (StandardCap.transitionEnd + 1 + n) (min (1 / 2) (ε₀ n))
      (3 * A + 2 * A * Real.sqrt (max Cq 1) + 4) ((n : ℝ) + 1 + θ) (by linarith [hn0 n])
      (by linarith [hn0 n]) (hDn n) le_rfl (lt_min (by norm_num) (hε₀ n))
      (by linarith [hn0 n])
  have hradius (n : ℕ) : StandardCap.transitionEnd + 1 + n ≤ (p n).modelRadius := by
    exact hRrad n
  have hacc (n : ℕ) : (p n).modelAccuracy ≤ 1 / 2 := by
    exact (hζ n).trans (min_le_left _ _)
  have hscale (n : ℕ) (i : Fin (H n).eventCount) (hi : T₀ n ≤ (H n).time i.succ)
      (b : ((H n).toHistory.event i).RetainedBoundaryIndex) (w : ThreeBall) :
      ((records n i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records n i hi).static b).witness.metric
        (((records n i hi).static b).witness.cap w) :=
    hsc n ((H n).toHistory.event i) (hradius n) ((hζ n).trans (min_le_right _ _)) (hord n)
      ((records n i hi).static b) (hcan n i hi b) w
  refine false_of_terminal_counterexamples_window_P6WB heps hκ hphi hA hθ rfl
    (fun n => StandardCap.transitionEnd + 1 + n) ?_ (fun n => (n : ℝ) + 1 + θ)
    (fun n => by linarith) (fun n => by linarith [hn0 n]) H hend s G hG records hcan hscale hacc
    hradius t ht hts y q ρ hq hqy hΛ hΛt hT0 U le_rfl hUy hW hslabs hder hgrad hpinch hpinchG hnc
    hρ (fun n => by
      rintro ⟨j, hT, hl, B, b, x, h1, h2, h3⟩
      exact absurd h3 (not_le.mpr (hnot n j hT hl B b x h1 h2))) z hz hbad
  exact tendsto_atTop_add_const_left atTop _ tendsto_natCast_atTop_atTop

/-- consumer：`SLT:249_P6L`（全 slab / 全 family 形）⇐ 窗口形（`T₀ = t - Bw / R(t, y)`）。 -/
example : type_of%
    @RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_P6L.{u}
    := by
  intro ε hεle κ C1 C2 hκ Ctime Cgrad phi hphi A hA Cq θ hθ
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, hDR, hζ, hBw, hmain⟩ :=
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_window_P6WB
      hεle κ C1 C2 hκ Ctime Cgrad hphi A hA Cq θ hθ
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, hQ, hΛ, hD, hDR, hζ, ?_⟩
  intro H hend s G hG p₀ δb ρb p records hrec hRrad hord hζ' t ht hts y q ρ hq hqy hΛ1 hΛ2 U hUy
    hW hslabs hder hgrad hpinch hpinchG hnc hρ hnot
  exact hmain H hend G hG ht hts y q ρ hq hqy hΛ1 hΛ2 (t - Bw / G.flow.scalar t y) le_rfl
    (fun i _ => records i) (fun i _ b => hrec.2.2.2.2.2.1 i b) (hrec.2.1 ▸ hRrad)
    (hrec.2.2.1 ▸ hord) (hrec.2.2.2.1 ▸ hζ') U hUy hW
    (fun j first hf z hz B v hv _ hR => hslabs j first hf z hz B v hv hR)
    (fun x hx v hv _ hR => hder x hx v hv hR) (fun x hx v hv _ hR w => hgrad x hx v hv hR w)
    (fun j v hv w => hpinch j v hv.1 w) (fun v hv w => hpinchG v hv.1 w)
    (fun T hT hTs hTt _ => hnc T hT hTs hTt) hρ
    (fun ⟨j, _, hl, B, b, x, h1, h2, h3⟩ => hnot ⟨j, hl, B, b, x, h1, h2, h3⟩)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
