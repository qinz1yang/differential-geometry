import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingWindowAnchorBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedRegionAncientLimitDerivativeCutoff_P6L

/-!
# `CrossingWindowAnchorBound` 的 survivor-block 引理局部化副本（O-CH11-P6D2 G1，后缀 `_P6L`）

原文件：`ST/CrossingWindowAnchorBound.lean`（L7 任意深度的 window anchor，`:555` 的输入）。本文件
copy-localize 其中三个带**全局**前提的 survivor-block 引理，以及 `:130` 的底层
`exists_neckAlternatives_or_isCompact_of_survivor_maps`
（`ST/TracedRegionNeckAlternativesCompact:21`）：

* `exists_neckAlternatives_or_isCompact_of_survivor_maps_P6L`（底层 `:21`）：全局 `hwit`
  （`∀ v < t₀`, 非 event, `∀ p`）→ **survivor 点形**（只在 `f ⟨H.activeStage v, _, _⟩ z` 上），照
  P6D G1 `exists_neckAlternatives_of_survivor_maps_P6L`；原证明只在 `f j z` 一点求值，证明体照抄。
* `exists_eventually_neckAlternatives_or_isCompact_of_survivor_blocks_P6L`（`:130`）、
  `eventually_abs_derivWithin_scalar_le_of_survivor_blocks_P6L`（`:227`）、
  `survivor_blocks_scalar_le_at_distance_P6L`（`:264`）：全局 `hwit` / `hstage` / `hbound` 换成
  **trace-local 形**（与 P6D G2 `exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D`
  的 `hwit` / `hderiv` 逐字同形：`∀ D T`, eventually, `x ∈ B_{t n}(y n, D/√R n)`,
  `v ≥ t n − T/R n`, `v < t n`, 非 event, `∀ tr : BackwardPointTrace … x`，在 `tr.point` 上）。
  成员关系：survivor block 的 survivor maps 本身给出 backward trace
  （`exists_backwardPointTrace_of_survivor_maps_P6L`：`tr0.restrictFirst`，`tr.point = f j z` 是 `rfl`），
  `z ∈ W k n = B_ĝ(y n, k+3) = B(y n, (k+3)/√R n)`，`v ≥ a = t n − τ k/R n`。代价：block 前提从
  `(a, f, hf, hinj, hp)` 加强到 `:335` 的完整 survivor data（加 `RegularCrossing` 与末端恒等），外加
  `hWset`——`:555` 的 `hblock` 本来就提供这些。
* `t₀` 取 `t n`（P6 的"更早时刻好"只在 `v < t n` 上），`hE` 相应写 `t n + s/R n < t n`。
* `:264` 的 `hbound`（bounded curvature at bounded distance，`∀ z x : stage`）换成 trace 形：
  `∀ A Dd, ∃ C, ∀ σ' < 0, ∀ Dw`, eventually, 两条从 `B(y n, Dw/√R n)` 出发的 backward trace 的点；
  `C` 不依赖 `Dw`（与原 `C(A, Dd)` 同）。

`:335`（`eventually_scalar_backwardPointTrace_le_of_window_limit`）**不需要**局部化：它的前提只有
survivor data、收敛数据与极限上的 `hC₀`，没有任何 history 全局前提，G2 直接调用原定理。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.scaleMetric_restrictOpen
  ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
  ObservedHistory.riemannianBallOf_scaleMetric_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

universe u

/-- 照抄 `CrossingWindowAnchorBound` 的 private `closedBall_one_subset_of_ball_eq_window`。 -/
private theorem closedBall_one_subset_of_ball_eq_window_P6L {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) (b : M) (W : TopologicalSpace.Opens M) (k : ℕ)
    (hW : (W : Set M) = riemannianBallOf g b ((k + 3 : ℕ) : ℝ)) (z : M)
    (hz : z ∈ riemannianClosedBallOf g b ((k + 1 : ℕ) : ℝ)) :
    riemannianClosedBallOf g z 1 ⊆ W := by
  intro w hw
  rw [hW]
  have hz' : riemannianEDistOf g b z ≤ ENNReal.ofReal ((k + 1 : ℕ) : ℝ) := hz
  have hw' : riemannianEDistOf g z w ≤ ENNReal.ofReal 1 := hw
  change riemannianEDistOf g b w < ENNReal.ofReal ((k + 3 : ℕ) : ℝ)
  calc riemannianEDistOf g b w ≤ riemannianEDistOf g b z + riemannianEDistOf g z w :=
        riemannianEDistOf_triangle _ _ _ _
    _ ≤ ENNReal.ofReal ((k + 1 : ℕ) : ℝ) + ENNReal.ofReal 1 := add_le_add hz' hw'
    _ = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) + 1) :=
        (ENNReal.ofReal_add (by positivity) (by norm_num)).symm
    _ < ENNReal.ofReal ((k + 3 : ℕ) : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by push_cast; linarith)

/-- 照抄 `CrossingWindowAnchorBound` 的 private `lt_ofReal_div_of_ofReal_mul_lt`。 -/
private theorem lt_ofReal_div_of_ofReal_mul_lt_P6L {a b : ℝ} (ha : 0 < a) {d : ENNReal}
    (h : ENNReal.ofReal a * d < ENNReal.ofReal b) : d < ENNReal.ofReal (b / a) := by
  have hd : d ≠ ⊤ := by
    rintro rfl
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr ha).ne'] at h
    exact (not_top_lt h)
  rw [← ENNReal.ofReal_toReal hd, ← ENNReal.ofReal_mul ha.le] at h
  obtain ⟨h1, hb⟩ := (ENNReal.ofReal_lt_ofReal_iff').mp h
  rw [← ENNReal.ofReal_toReal hd]
  refine (ENNReal.ofReal_lt_ofReal_iff' ).mpr ⟨?_, div_pos hb ha⟩
  rw [lt_div_iff₀ ha]
  linarith

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace ObservedHistory

/-- **survivor maps ⇒ backward trace**：带 `RegularCrossing` 与末端恒等的 survivor maps 在每个
`z : W` 给出从 `z` 出发、到任意 `v ∈ [a, t]` 的 backward trace，其 `v` 处的点就是 `f j z`（`rfl`）。 -/
theorem exists_backwardPointTrace_of_survivor_maps_P6L (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) {W : TopologicalSpace.Opens (H.stageAt t).Carrier}
    (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W →
      (H.stage j.val).Carrier)
    (hcross : ∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
      (hl : i.succ ≤ H.activeStage t), ∀ x : W,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (hlast : ∀ x : W, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val)
    (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) (z : W) :
    ∃ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage t) (H.activeStage_mono hvt)
        z.val,
      tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvt) =
        f ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩ z := by
  let tr0 : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat)
      z.val :=
    { point := fun i hi hl => f ⟨i, hi, hl⟩ z
      endpoint_eq := hlast z
      crossing := fun i hi hl => hcross i hi hl z }
  exact ⟨tr0.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvt), rfl⟩

/-- `ST/TracedRegionNeckAlternativesCompact:21` 的局部化：`hwit` 只在 survivor 点上要求。 -/
theorem exists_neckAlternatives_or_isCompact_of_survivor_maps_P6L :
    ∃ D : ℝ, 0 < D ∧ ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
      {R θ t₀ qs qW L : ℝ} (hR : 0 < R) {eps C1 C2 : ℝ} (_ : qs ≤ R * qW) (_ : 0 < L)
      {W : TopologicalSpace.Opens (H.stageAt t).Carrier}
      {h : ℝ → SmoothRiemannianMetric ThreeModel W}
      (a : Icc (0 : ℝ) H.horizon) (_ : (a : ℝ) = t - θ / R)
      (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W →
        (H.stage j.val).Carrier)
      (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j)),
      (∀ j, Injective (f j)) →
      (∀ s ∈ Icc (-θ) 0, ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
        (t : ℝ) + s / R ∈ H.stageDomain j.val →
          h s = scaleMetric R hR
            (localPullMetric (H.stageMetric j.val ((t : ℝ) + s / R)) (f j) (hf j))) →
      (∀ v : Icc (0 : ℝ) H.horizon, (v : ℝ) < t₀ → H.time (H.activeStage v) < v →
        ∀ (hav : a ≤ v) (hvt : v ≤ t) (z : W),
          qs < metricScalarAt (H.stageMetric (H.activeStage v) v)
            (f ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩ z) →
          ∃ Wt : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) eps C1 C2
              (f ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩ z),
            Wt.capTubeHasNeckChart eps) →
      ∀ {s : ℝ}, s ∈ Icc (-θ) 0 → (t : ℝ) + s / R < t₀ →
      (∀ hv : (t : ℝ) + s / R ∈ Icc (0 : ℝ) H.horizon,
        H.time (H.activeStage ⟨_, hv⟩) < (t : ℝ) + s / R) →
      ∀ z : W, IsCompact (riemannianClosedBallOf (h 0) z 1) →
      (∀ y ∈ riemannianClosedBallOf (h 0) z 1, ∀ u : TangentSpace ThreeModel y,
        (h 0).inner y u u ≤ L ^ 2 * (h s).inner y u u) →
      qW < metricScalarAt (h s) z →
      L * (max (2 * |C1|) C2 + (D + 2 * eps⁻¹) * Real.sqrt (max (2 * |C1|) C2)) <
        Real.sqrt (metricScalarAt (h s) z) →
      Nonempty (SpatialNeck (h s) eps z) ∨
        (∃ w : W, Nonempty (SpatialNeck (h s) eps w) ∧
          metricScalarAt (h s) z ≤ max (2 * |C1|) C2 * metricScalarAt (h s) w ∧
          metricScalarAt (h s) w ≤ max (2 * |C1|) C2 * metricScalarAt (h s) z ∧
          riemannianEDistOf (h s) z w <
            ENNReal.ofReal (max (2 * |C1|) C2 / Real.sqrt (metricScalarAt (h s) z))) ∨
        IsCompact (connectedComponent z) := by
  obtain ⟨D, hD, hcore⟩ :=
    exists_neckAlternatives_or_isCompact_localPull_of_spatialCanonicalWitness.{u}
  refine ⟨D, hD, ?_⟩
  intro H t R θ t₀ qs qW L hR eps C1 C2 hqs hL W h a ha f hf hinj hp hwit s hs hst₀ hreg z
    hcpt hlower hz hsmall
  have hsR : s / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hR.le
  have hθR : -θ / R ≤ s / R := div_le_div_of_nonneg_right hs.1 hR.le
  have hlo : (a : ℝ) ≤ (t : ℝ) + s / R := by
    rw [ha, sub_eq_add_neg, ← neg_div]
    linarith
  let v : Icc (0 : ℝ) H.horizon :=
    ⟨(t : ℝ) + s / R, a.2.1.trans hlo, (by linarith : (t : ℝ) + s / R ≤ t).trans t.2.2⟩
  have hav : a ≤ v := hlo
  have hvt : v ≤ t := show (t : ℝ) + s / R ≤ t by linarith
  have hreg' := hreg v.2
  let j : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩
  have hs1 : h s = localPullMetric (scaleMetric R hR (H.stageMetric j.val v)) (f j) (hf j) := by
    rw [hp s hs j (H.activeStage_mem v), localPullMetric_scaleMetric]
  have hsc : metricScalarAt (h s) z =
      metricScalarAt (scaleMetric R hR (H.stageMetric j.val v)) (f j z) := by
    rw [hs1, metricScalarAt_localPull]
  have hqz : qs < metricScalarAt (H.stageMetric (H.activeStage v) v) (f j z) := by
    have h1 : R * qW < R * metricScalarAt (h s) z := mul_lt_mul_of_pos_left hz hR
    rw [hsc, metricScalarAt_scaleMetric, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] at h1
    exact hqs.trans_lt h1
  -- 局部化：witness 只在 survivor 点 `f j z` 取
  obtain ⟨Wt, hWt⟩ := hwit v hst₀ hreg' hav hvt z hqz
  have key := hcore (scaleMetric R hR (H.stageMetric j.val v)) (h 0) (hf j) (hinj j) z
    zero_lt_one hL hcpt (fun y hy u => by rw [← hs1]; exact hlower y hy u) (Wt.scaleMetric R hR)
    (hWt.scaleMetric (c := R) (hc := hR)) (by rw [one_mul, ← hsc]; exact hsmall)
  rw [← hs1] at key
  exact key

/-- `:130` 的局部化：`hwit` 换成 trace-local 形（P6D G2 的 `hwit` 逐字同形，`t₀ := t n`），
block 前提加 `RegularCrossing` / 末端恒等（`:335` 的完整 survivor data）。 -/
theorem exists_eventually_neckAlternatives_or_isCompact_of_survivor_blocks_P6L :
    ∃ D : ℝ, 0 < D ∧ ∀ {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
      {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n} {τ c : ℕ → ℝ}
      {W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens ((Hs n).stageAt (ts n)).Carrier}
      {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)},
      (∀ k, 0 < τ k) → (∀ k, c k ≤ τ k) →
      (∀ k : ℕ, ∀ᶠ n in atTop, (W k n : Set ((Hs n).stageAt (ts n)).Carrier) =
        riemannianBallOf (scaleMetric (R n) (hR n)
          ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))) (ys n) ((k + 3 : ℕ) : ℝ)) →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-τ k) 0,
        (ts n : ℝ) + s / R n ∈ (Hs n).stageDomain ((Hs n).activeStage (ts n)) →
        h k n s = scaleMetric (R n) (hR n)
          (((Hs n).stageMetric ((Hs n).activeStage (ts n)) ((ts n : ℝ) + s / R n)).restrictOpen
            (W k n))) →
      (∀ k : ℕ, ∀ᶠ n in atTop,
        ∃ (a : Icc (0 : ℝ) (Hs n).horizon) (hat : a ≤ ts n), (a : ℝ) = ts n - τ k / R n ∧
          ∃ f : (j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n))) →
              W k n → ((Hs n).stage j.val).Carrier,
            ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
              (∀ j, Function.Injective (f j)) ∧
              (∀ (i : Fin (Hs n).eventCount) (hi : (Hs n).activeStage a ≤ i.castSucc)
                  (hl : i.succ ≤ (Hs n).activeStage (ts n)), ∀ x : W k n,
                ((Hs n).event i).RegularCrossing
                  (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                  (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
              (∀ x : W k n,
                f ⟨(Hs n).activeStage (ts n), (Hs n).activeStage_mono hat, le_rfl⟩ x = x.val) ∧
              ∀ s ∈ Icc (-τ k) 0,
                ∀ j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n)),
                  (ts n : ℝ) + s / R n ∈ (Hs n).stageDomain j.val →
                    h k n s = scaleMetric (R n) (hR n)
                      (localPullMetric ((Hs n).stageMetric j.val ((ts n : ℝ) + s / R n)) (f j)
                        (hf j))) →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, ∀ (x : W k n)
        (u : TangentSpace ThreeModel x),
        (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u) →
      ∀ {qs : ℕ → ℝ} {E : ℕ → Set ℝ} {eps C1 C2 C qW : ℝ}, 0 < eps → 1 ≤ C →
      max (2 * |C1|) C2 ≤ C → (∀ n, qs n ≤ R n * qW) →
      (Real.exp 1 * (C + (D + 2 * eps⁻¹) * Real.sqrt C)) ^ 2 ≤ qW →
      (∀ Dw Tw : ℝ, 0 < Dw → 0 < Tw → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - Tw / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) eps C1 C2
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart eps) →
      (∀ n s, s ≤ 0 → s ∉ E n → (ts n : ℝ) + s / R n < ts n ∧
        ∀ i, (ts n : ℝ) + s / R n ≠ (Hs n).time i) →
      ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, s ∉ E n → ∀ z : W k n,
        (z : ((Hs n).stageAt (ts n)).Carrier) ∈ riemannianClosedBallOf (scaleMetric (R n) (hR n)
          ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))) (ys n) ((k + 1 : ℕ) : ℝ) →
        qW < metricScalarAt (h k n s) z →
        Nonempty (SpatialNeck (h k n s) eps z) ∨
          (∃ w : W k n, Nonempty (SpatialNeck (h k n s) eps w) ∧
            metricScalarAt (h k n s) z ≤ C * metricScalarAt (h k n s) w ∧
            metricScalarAt (h k n s) w ≤ C * metricScalarAt (h k n s) z ∧
            riemannianEDistOf (h k n s) z w <
              ENNReal.ofReal (C / Real.sqrt (metricScalarAt (h k n s) z))) ∨
          IsCompact (connectedComponent z) := by
  obtain ⟨D, hD, hB6⟩ := exists_neckAlternatives_or_isCompact_of_survivor_maps_P6L.{u}
  refine ⟨D, hD, ?_⟩
  intro Hs ts ys R hR τ c W h hτ hcτ hWset hcur hsurv hlow qs E eps C1 C2 C qW heps hC1 hC0
    hqs hqWsq hwit hE k
  have hC00 : 0 ≤ max (2 * |C1|) C2 := le_max_of_le_left (by positivity)
  have hDe : 0 ≤ D + 2 * eps⁻¹ := by have := inv_pos.mpr heps; linarith
  have hxnn : 0 ≤ Real.exp 1 * (C + (D + 2 * eps⁻¹) * Real.sqrt C) :=
    mul_nonneg (Real.exp_pos 1).le
      (add_nonneg (by linarith) (mul_nonneg hDe (Real.sqrt_nonneg _)))
  have hqW0 : 0 ≤ qW := (sq_nonneg _).trans hqWsq
  have he2 : Real.exp 1 ^ 2 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hk3 : (0 : ℝ) < ((k + 3 : ℕ) : ℝ) := by positivity
  filter_upwards [hWset k, hcur k, hsurv k, hlow k, hwit _ _ hk3 (hτ k)] with n hWn hcn hsn hlown
    hwn s hs hsE z hz hqz
  obtain ⟨a, hat, ha, fs, hfs, hinj, hcross, hlast, hp⟩ := hsn
  obtain ⟨hst₀, hne⟩ := hE n s hs.2 hsE
  have hsτ : s ∈ Icc (-τ k) 0 := ⟨by linarith [hs.1, hcτ k], hs.2⟩
  have hzpos : 0 < metricScalarAt (h k n s) z := hqW0.trans_lt hqz
  have hcpt : IsCompact (riemannianClosedBallOf (h k n 0) z 1) := by
    have hdom : ((ts n : ℝ) + 0 / R n) ∈ (Hs n).stageDomain ((Hs n).activeStage (ts n)) := by
      simpa using (Hs n).activeStage_mem (ts n)
    rw [hcn 0 ⟨neg_nonpos.mpr (hτ k).le, le_rfl⟩ hdom, zero_div, add_zero,
      ObservedHistory.scaleMetric_restrictOpen]
    exact ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen _ _ _ _
      (closedBall_one_subset_of_ball_eq_window_P6L _ _ _ k hWn _ hz)
  have hsmall : Real.exp 1 * (max (2 * |C1|) C2 + (D + 2 * eps⁻¹) *
      Real.sqrt (max (2 * |C1|) C2)) < Real.sqrt (metricScalarAt (h k n s) z) := by
    refine lt_of_le_of_lt ?_ ((Real.lt_sqrt hxnn).mpr (hqWsq.trans_lt hqz))
    gcongr
  -- 局部化：survivor 点形 witness 由 trace-local `hwit` 经 survivor maps 的 backward trace 给出
  have hwitS : ∀ v : Icc (0 : ℝ) (Hs n).horizon, (v : ℝ) < ts n →
      (Hs n).time ((Hs n).activeStage v) < v →
      ∀ (hav : a ≤ v) (hvt : v ≤ ts n) (z' : W k n),
        qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (fs ⟨(Hs n).activeStage v, (Hs n).activeStage_mono hav,
            (Hs n).activeStage_mono hvt⟩ z') →
        ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) eps C1 C2
            (fs ⟨(Hs n).activeStage v, (Hs n).activeStage_mono hav,
              (Hs n).activeStage_mono hvt⟩ z'),
          Wt.capTubeHasNeckChart eps := by
    intro v hvlt hreg hav hvt z' hq'
    obtain ⟨tr, htr⟩ := exists_backwardPointTrace_of_survivor_maps_P6L (Hs n) (ts n) a hat fs
      hcross hlast v hav hvt z'
    have hz'B : (z' : ((Hs n).stageAt (ts n)).Carrier) ∈
        riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
      rw [← ObservedHistory.riemannianBallOf_scaleMetric_eq _ (hR n), ← hWn]
      exact z'.property
    have hva : (ts n : ℝ) - τ k / R n ≤ v := by rw [← ha]; exact hav
    have hw := hwn z' hz'B v hvt hva hvlt hreg tr (by rw [htr]; exact hq')
    rw [htr] at hw
    exact hw
  have key := hB6 (Hs n) (ts n) (hR n) (θ := τ k) (t₀ := ts n) (eps := eps) (C1 := C1)
    (C2 := C2) (W := W k n) (h := h k n) (hqs n) (Real.exp_pos 1) a ha fs hfs hinj hp
    hwitS hsτ hst₀
    (fun hv => lt_of_le_of_ne (ObservedHistory.activeStage_time_le _ _)
      fun heq => hne _ heq.symm) z hcpt
    (fun y' _ u => by rw [he2]; exact hlown s hs y' u) hqz hsmall
  rcases key with h1 | ⟨w, hw, h2, h3, h4⟩ | h5
  · exact Or.inl h1
  · have hw0 : 0 < metricScalarAt (h k n s) w := by
      by_contra hneg
      have := mul_nonpos_of_nonneg_of_nonpos hC00 (not_lt.mp hneg)
      linarith
    refine Or.inr (Or.inl ⟨w, hw, h2.trans (mul_le_mul_of_nonneg_right hC0 hw0.le),
      h3.trans (mul_le_mul_of_nonneg_right hC0 hzpos.le), h4.trans_le ?_⟩)
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hC0 (Real.sqrt_nonneg _))
  · exact Or.inr (Or.inr h5)

variable {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
  {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n} {τ : ℕ → ℝ}
  {W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens ((Hs n).stageAt (ts n)).Carrier}
  {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)}

/-- `:227` 的局部化：`hstage` 换成 trace-local 形（P6D G2 的 `hderiv` 逐字同形，`t₀ := t n`）；
底层用 P6D G1 的 `abs_derivWithin_scalar_le_of_survivor_maps_of_lt_P6L`。 -/
theorem eventually_abs_derivWithin_scalar_le_of_survivor_blocks_P6L (hτ : ∀ k, 0 < τ k)
    (hWset : ∀ k : ℕ, ∀ᶠ n in atTop, (W k n : Set ((Hs n).stageAt (ts n)).Carrier) =
      riemannianBallOf (scaleMetric (R n) (hR n)
        ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))) (ys n) ((k + 3 : ℕ) : ℝ))
    (hsurv : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∃ (a : Icc (0 : ℝ) (Hs n).horizon) (hat : a ≤ ts n), (a : ℝ) = ts n - τ k / R n ∧
        ∃ f : (j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n))) →
            W k n → ((Hs n).stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin (Hs n).eventCount) (hi : (Hs n).activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ (Hs n).activeStage (ts n)), ∀ x : W k n,
              ((Hs n).event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : W k n,
              f ⟨(Hs n).activeStage (ts n), (Hs n).activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∀ s ∈ Icc (-τ k) 0,
              ∀ j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n)),
                (ts n : ℝ) + s / R n ∈ (Hs n).stageDomain j.val →
                  h k n s = scaleMetric (R n) (hR n)
                    (localPullMetric ((Hs n).stageMetric j.val ((ts n : ℝ) + s / R n)) (f j)
                      (hf j)))
    {E : ℕ → Set ℝ} {Ct qD : ℝ} (hCt : 0 ≤ Ct) {qst : ℕ → ℝ} (hqD : ∀ n, qst n ≤ R n * qD)
    (hstage : ∀ Dw Tw : ℝ, 0 < Dw → 0 < Tw → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - Tw / R n ≤ v →
      (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
        ((Hs n).activeStage_mono hvt) x,
        qst n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
        |derivWithin (fun v' => metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v')
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
          (Iic (v : ℝ)) v| ≤
          Ct * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ^ 2)
    (hE : ∀ n s, s ≤ 0 → s ∉ E n → ∀ i, (ts n : ℝ) + s / R n ≠ (Hs n).time i) :
    ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-τ k) 0, s ∉ E n →
      ∀ z : W k n, qD < metricScalarAt (h k n s) z →
        |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
          Ct * metricScalarAt (h k n s) z ^ 2 := by
  intro k
  have hk3 : (0 : ℝ) < ((k + 3 : ℕ) : ℝ) := by positivity
  filter_upwards [hWset k, hsurv k, hstage _ _ hk3 (hτ k)] with n hWn hn hsn s hs hsE z hz
  obtain ⟨a, hat, ha, fs, hfs, -, hcross, hlast, hp⟩ := hn
  have hne := hE n s hs.2.le hsE
  have hst : (ts n : ℝ) + s / R n < ts n := by
    have := div_neg_of_neg_of_pos hs.2 (hR n)
    linarith
  refine abs_derivWithin_scalar_le_of_survivor_maps_of_lt_P6L (Hs n) (ts n) (t₀ := ts n) (hR n)
    hCt (hqD n) a ha fs hfs hp ?_ ⟨hs.1, hs.2.le⟩ hst
    (fun hv => lt_of_le_of_ne (ObservedHistory.activeStage_time_le _ _)
      fun heq => hne _ heq.symm) z hz
  -- 局部化：survivor 点形导数界由 trace-local `hstage` 经 survivor maps 的 backward trace 给出
  intro v hvlt hreg hav hvt z' hq'
  obtain ⟨tr, htr⟩ := exists_backwardPointTrace_of_survivor_maps_P6L (Hs n) (ts n) a hat fs
    hcross hlast v hav hvt z'
  have hz'B : (z' : ((Hs n).stageAt (ts n)).Carrier) ∈
      riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
        (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
    rw [← ObservedHistory.riemannianBallOf_scaleMetric_eq _ (hR n), ← hWn]
    exact z'.property
  have hva : (ts n : ℝ) - τ k / R n ≤ v := by rw [← ha]; exact hav
  have hw := hsn z' hz'B v hvt hva hvlt hreg tr (by rw [htr]; exact hq')
  rw [htr] at hw
  exact hw

/-- `:264` 的局部化：`hbound`（bounded curvature at bounded distance，`∀ z x : stage`）换成
trace 形（两条从 `B(y n, Dw/√R n)` 出发的 backward trace 的点，`C` 不依赖 `Dw`）。 -/
theorem survivor_blocks_scalar_le_at_distance_P6L
    (hWset : ∀ k : ℕ, ∀ᶠ n in atTop, (W k n : Set ((Hs n).stageAt (ts n)).Carrier) =
      riemannianBallOf (scaleMetric (R n) (hR n)
        ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))) (ys n) ((k + 3 : ℕ) : ℝ))
    (hsurv : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∃ (a : Icc (0 : ℝ) (Hs n).horizon) (hat : a ≤ ts n), (a : ℝ) = ts n - τ k / R n ∧
        ∃ f : (j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n))) →
            W k n → ((Hs n).stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin (Hs n).eventCount) (hi : (Hs n).activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ (Hs n).activeStage (ts n)), ∀ x : W k n,
              ((Hs n).event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : W k n,
              f ⟨(Hs n).activeStage (ts n), (Hs n).activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∀ s ∈ Icc (-τ k) 0,
              ∀ j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n)),
                (ts n : ℝ) + s / R n ∈ (Hs n).stageDomain j.val →
                  h k n s = scaleMetric (R n) (hR n)
                    (localPullMetric ((Hs n).stageMetric j.val ((ts n : ℝ) + s / R n)) (f j)
                      (hf j)))
    {c : ℕ → ℝ} (hcτ : ∀ k, c k ≤ τ k)
    (hbound : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
      ∀ᶠ n in atTop,
      ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (Dw / Real.sqrt (R n)),
      ∀ x₂ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + σ' / R n →
      ∀ (tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x₂),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤
          A * R n →
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
            (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤
          C * R n) :
    ∀ A Dd : ℝ, ∃ C : ℝ, ∀ k : ℕ, ∀ s ∈ Icc (-c k) 0, s < 0 → ∀ᶠ n in atTop,
      ∀ z x : W k n, metricScalarAt (h k n s) z ≤ A →
        riemannianEDistOf (h k n s) z x < ENNReal.ofReal Dd →
        metricScalarAt (h k n s) x ≤ C := by
  intro A Dd
  obtain ⟨C₁, hC₁⟩ := hbound (max A 1) (max Dd 1) (by positivity) (by positivity)
  refine ⟨C₁, fun k s hs hs0 => ?_⟩
  have hk3 : (0 : ℝ) < ((k + 3 : ℕ) : ℝ) := by positivity
  filter_upwards [hWset k, hsurv k, hC₁ s hs0 _ hk3] with n hWn hn hCm z x hz hzx
  obtain ⟨a, hat, ha, fs, hfs, -, hcross, hlast, hp⟩ := hn
  have hR0 := hR n
  have hsτ : s ∈ Icc (-τ k) 0 := ⟨by linarith [hs.1, hcτ k], hs.2⟩
  have hsR : s / R n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hR0.le
  have hθR : -τ k / R n ≤ s / R n := div_le_div_of_nonneg_right hsτ.1 hR0.le
  have hlo : (a : ℝ) ≤ (ts n : ℝ) + s / R n := by
    rw [ha, sub_eq_add_neg, ← neg_div]
    linarith
  let v : Icc (0 : ℝ) (Hs n).horizon :=
    ⟨(ts n : ℝ) + s / R n, a.2.1.trans hlo,
      (by linarith : (ts n : ℝ) + s / R n ≤ ts n).trans (ts n).2.2⟩
  have hav : a ≤ v := hlo
  have hvt : v ≤ ts n := show (ts n : ℝ) + s / R n ≤ ts n by linarith
  let j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n)) :=
    ⟨(Hs n).activeStage v, (Hs n).activeStage_mono hav, (Hs n).activeStage_mono hvt⟩
  have hs1 := hp s hsτ j ((Hs n).activeStage_mem v)
  have hscz : ∀ w, metricScalarAt (h k n s) w =
      (R n)⁻¹ * metricScalarAt ((Hs n).stageMetric j.val v) (fs j w) := by
    intro w
    rw [hs1, metricScalarAt_scaleMetric, metricScalarAt_localPull]
  have hz' : metricScalarAt ((Hs n).stageMetric j.val v) (fs j z) ≤ max A 1 * R n := by
    rw [hscz z, inv_mul_le_iff₀ hR0] at hz
    nlinarith [le_max_left A 1]
  have hd : riemannianEDistOf ((Hs n).stageMetric j.val v) (fs j z) (fs j x) <
      ENNReal.ofReal (max Dd 1 / Real.sqrt (R n)) := by
    rw [hs1, edistOf_scale] at hzx
    have h1 := lt_ofReal_div_of_ofReal_mul_lt_P6L (Real.sqrt_pos.mpr hR0) hzx
    have h2 := edistOf_le_of_quad_of_localDiffeomorph
      (localPullMetric ((Hs n).stageMetric j.val v) (fs j) (hfs j))
      ((Hs n).stageMetric j.val v) (fs j) (hfs j) one_pos
      (fun x' u => by rw [localPullMetric_inner, one_mul]) z x
    rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at h2
    exact h2.trans_lt (h1.trans_le (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))))
  -- 局部化：`hbound` 只在 survivor maps 给出的两条 backward trace 的点上用
  obtain ⟨tr₁, htr₁⟩ := exists_backwardPointTrace_of_survivor_maps_P6L (Hs n) (ts n) a hat fs
    hcross hlast v hav hvt z
  obtain ⟨tr₂, htr₂⟩ := exists_backwardPointTrace_of_survivor_maps_P6L (Hs n) (ts n) a hat fs
    hcross hlast v hav hvt x
  have hzB : (z : ((Hs n).stageAt (ts n)).Carrier) ∈
      riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
        (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
    rw [← ObservedHistory.riemannianBallOf_scaleMetric_eq _ hR0, ← hWn]
    exact z.property
  have hxB : (x : ((Hs n).stageAt (ts n)).Carrier) ∈
      riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
        (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
    rw [← ObservedHistory.riemannianBallOf_scaleMetric_eq _ hR0, ← hWn]
    exact x.property
  have hx' := hCm z hzB x hxB v hvt rfl tr₁ tr₂ (by rw [htr₁]; exact hz')
    (by rw [htr₁, htr₂]; exact hd)
  rw [htr₂] at hx'
  rw [hscz x, inv_mul_le_iff₀ hR0]
  linarith

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
