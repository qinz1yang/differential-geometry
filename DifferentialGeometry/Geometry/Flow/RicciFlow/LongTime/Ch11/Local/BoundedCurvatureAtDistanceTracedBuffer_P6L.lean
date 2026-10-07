import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceTracedPositive

/-!
# L6-A spine：traced buffer `CB:55` / `TP:33` 的局部化（`_P6L`，TP:97_P6L 的 buffer 供给）

原 `ST/BoundedCurvatureAtDistanceChainBuffers.lean:55`
`RetainedCoreHistory.exists_trace_first_of_chain_trace_on_scaled_ball` 与
`ST/BoundedCurvatureAtDistanceTracedPositive.lean:33`
`RetainedCoreHistory.traced_buffer_of_chain_traces`。
`htrace`（链形，由 SL:73_P6L 供给）在局部化后带链球成员前提
`(∀ k ≤ N, ∀ z ∈ B_T(p k, δ k), z ∈ U) →`（插在 `0 < δ k` 后；与 O-CH11-P6A3 G2 SL:73_P6L 结论、
P6C2 `_P6Lm` 同位）。CB:55 只用单球链 `B_T(x, (R + ε/2)/√Q)`，成员由 `hU : B_{Q·L}(x, Rad) ⊆ U` 与
`R + ε ≤ Rad` 给（新桥 `ClosedSlab.ball_subset_of_scaled_dist_lt_P6L`）。TP:33_P6L 的 buffer 结论因此限于
`R + ε ≤ Rad`；TP:97_P6L 对 `R + ε` 超过失败半径的情形用 `hfailure` 反证（buffer 前提蕴含失败球上统一界）。
私有 `CB:45` 复制为 `_P6L`。证明体照抄；结论除半径限制外逐字。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- 成员关系桥（rev1a C2.1/C2.3，通用中心版）：`d_{Q·L}(x, c) < d`、`d + √Q·r ≤ Rad`，且
`B_{Q·L}(x, Rad)` 的点都在 `U` ⇒ 端点度量球 `B_s(c, r) ⊆ U`（`terminalRegularRegion = univ`）。
（同 P6C2 TSL:170_P6L 的私有桥，公开给 TP:33/97_P6L 用。） -/
theorem OrientedThreeStage.ClosedSlab.ball_subset_of_scaled_dist_lt_P6L {P : OrientedThreeStage.{u}}
    {a s : ℝ} (A : P.ClosedSlab a s) {Q : ℝ} (hQ : 0 < Q)
    (x c : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) (U : Set P.Carrier)
    {d Rad r : ℝ} (hd : 0 ≤ d) (hr0 : 0 ≤ r)
    (hc : riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x c <
      ENNReal.ofReal d)
    (hr : d + Real.sqrt Q * r ≤ Rad)
    (hU : ∀ y ∈ riemannianBallOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x
      Rad, y.val ∈ U) :
    riemannianBallOf (A.flow.base.metric s) c.val r ⊆ U := by
  intro w hw
  have hmem : w ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen := by
    change w ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
    rw [A.terminalRegularRegion_eq_univ _]
    trivial
  apply hU ⟨w, hmem⟩
  change riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x
    ⟨w, hmem⟩ < ENNReal.ofReal Rad
  have hw' : riemannianEDistOf (A.flow.base.metric s) c.val w < ENNReal.ofReal r := hw
  have hsq : ENNReal.ofReal (Real.sqrt Q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne'
  have hcw : riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) c
      ⟨w, hmem⟩ < ENNReal.ofReal (Real.sqrt Q * r) := by
    rw [DifferentialGeometry.edistOf_scale, A.riemannianEDistOf_endpointTerminalLimitMetric,
      ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
    have h := ENNReal.mul_lt_mul_left hsq ENNReal.ofReal_ne_top hw'
    rwa [mul_comm, mul_comm (ENNReal.ofReal r)] at h
  calc riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x ⟨w, hmem⟩
      ≤ riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x c +
          riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) c
            ⟨w, hmem⟩ := riemannianEDistOf_triangle _ _ _ _
    _ < ENNReal.ofReal d + ENNReal.ofReal (Real.sqrt Q * r) := ENNReal.add_lt_add hc hcw
    _ = ENNReal.ofReal (d + Real.sqrt Q * r) :=
        (ENNReal.ofReal_add hd (mul_nonneg (Real.sqrt_nonneg Q) hr0)).symm
    _ ≤ ENNReal.ofReal Rad := ENNReal.ofReal_le_ofReal hr

private theorem sqrt_mul_exp_mul_div_eq_P6L {M Q θ K a : ℝ} (hM : 0 ≤ M) (hQ : 0 < Q) :
    Real.sqrt (8 * (M * Q)) * Real.exp (9 * (K * (M * Q)) * (θ / Q)) * (a / Real.sqrt Q) =
      Real.sqrt (8 * M) * Real.exp (9 * (K * M) * θ) * a := by
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have h1 : Real.sqrt (8 * (M * Q)) = Real.sqrt (8 * M) * Real.sqrt Q := by
    rw [← mul_assoc, Real.sqrt_mul (by positivity)]
  have h2 : 9 * (K * (M * Q)) * (θ / Q) = 9 * (K * M) * θ := by field_simp
  rw [h1, h2]
  field_simp


/-- **`_P6L`**：原 `RetainedCoreHistory.exists_trace_first_of_chain_trace_on_scaled_ball`（`CB:55`）。
改动：`htrace` 在 `0 < δ k` 后加链球成员前提（区域 `U`，与 P6C2 `_P6Lm` 同位）；加先验半径 `Rad`、
`hRad : R + ε ≤ Rad` 与 `hU : B_{Q·L}(x, Rad) ⊆ U`（唯一的链 = 单球 `B_T(x, (R + ε/2)/√Q)`，
由 `ClosedSlab.ball_subset_of_scaled_dist_lt_P6L` 给成员）。证明体照抄；结论逐字。 -/
theorem RetainedCoreHistory.exists_trace_first_of_chain_trace_on_scaled_ball_P6L
    (H : RetainedCoreHistory.{u}) {T : ℝ}
    (A : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
    (hQ : 1 ≤ A.flow.scalar T x.val) {Kc lam θ D : ℝ} {Ctime : ℝ≥0} {Phi : ℝ → ℝ}
    (U : Set (H.stage (Fin.last H.eventCount)).Carrier)
    (htrace : ∀ (N : ℕ) (p : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δ : ℕ → ℝ)
      (M τ : ℝ), p 0 = x.val → (∀ k ≤ N, 0 < δ k) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p k) (δ k), z ∈ U) →
      (∀ k < N, p (k + 1) ∈ riemannianBallOf (A.flow.base.metric T) (p k) (δ k)) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p k) (δ k),
        A.flow.scalar T z ≤ M) →
      Kc * A.flow.scalar T x.val ≤ M → 1 ≤ M → 0 ≤ τ → τ ≤ T →
      (Ctime : ℝ) * M * τ ≤ 1 / 2 → 4 * M * τ ≤ θ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * M) * τ) *
          (lam / Real.sqrt (A.flow.scalar T x.val) + ∑ k ∈ Finset.range (N + 1), δ k) < D →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (p k) (δ k),
        ∃ first : Fin (H.eventCount + 1), H.time first ≤ T - τ ∧
          Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z))
    {R ε B θ₁ : ℝ} (hR : 0 < R) (hε : 0 < ε) {Rad : ℝ} (hRad : R + ε ≤ Rad)
    (hURad : ∀ y ∈ riemannianBallOf (scaleMetric (A.flow.scalar T x.val) (zero_lt_one.trans_le hQ)
      (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric) x Rad, y.val ∈ U)
    (hB : ∀ y ∈ riemannianClosedBallOf (scaleMetric (A.flow.scalar T x.val)
        (zero_lt_one.trans_le hQ)
        (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric) x (R + ε),
      metricScalarAt (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric y ≤
        B * A.flow.scalar T x.val)
    (hθ₁ : 0 < θ₁) (hθθ : 4 * max (max B Kc) 1 * θ₁ ≤ θ)
    (hCθ : (Ctime : ℝ) * max (max B Kc) 1 * θ₁ ≤ 1 / 2)
    (hT : θ₁ ≤ A.flow.scalar T x.val * T)
    (hD : 2 * StandardCap.transitionEnd + Real.sqrt (8 * max (max B Kc) 1) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * max (max B Kc) 1) * θ₁) *
        (lam + (R + ε / 2)) < D) :
    ∃ first : Fin (H.eventCount + 1), H.time first ≤ T - θ₁ / A.flow.scalar T x.val ∧
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (A.flow.scalar T x.val)
        (zero_lt_one.trans_le hQ)
        (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric) x R,
        Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
          (Fin.le_last first) y.val) := by
  set Q := A.flow.scalar T x.val with hQdef
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  set M' := max (max B Kc) 1 with hM'def
  have hM'1 : 1 ≤ M' := le_max_right _ _
  have hM'B : B ≤ M' := (le_max_left _ _).trans (le_max_left _ _)
  have hM'K : Kc ≤ M' := (le_max_right _ _).trans (le_max_left _ _)
  have hU : ∀ w : (H.stage (Fin.last H.eventCount)).Carrier,
      w ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen := by
    intro w
    change w ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
    rw [A.terminalRegularRegion_eq_univ (H.stage (Fin.last H.eventCount))]
    trivial
  have hτT : θ₁ / Q ≤ T := by rw [div_le_iff₀ hQpos]; linarith
  have hτ0 : 0 ≤ θ₁ / Q := by positivity
  have hball : ∀ z ∈ riemannianBallOf (A.flow.base.metric T) x.val ((R + ε / 2) / Real.sqrt Q),
      A.flow.scalar T z ≤ M' * Q := by
    intro z hz
    have hmem : (⟨z, hU z⟩ : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) ∈
        riemannianClosedBallOf (scaleMetric Q hQpos
          (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric) x (R + ε) := by
      rw [A.mem_scaled_endpoint_closedBall_iff Q hQpos]
      refine le_of_lt (lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal ?_))
      exact div_le_div_of_nonneg_right (by linarith) hsQ.le
    have h := hB _ hmem
    rw [show metricScalarAt (A.endpointTerminalLimitMetric
        (H.stage (Fin.last H.eventCount))).metric ⟨z, hU z⟩ = A.flow.scalar T z from
      metricScalarAt_restrictOpen _ _ _] at h
    nlinarith
  have hballU : riemannianBallOf (A.flow.base.metric T) x.val ((R + ε / 2) / Real.sqrt Q) ⊆ U :=
    A.ball_subset_of_scaled_dist_lt_P6L hQpos x x U (by linarith : (0 : ℝ) ≤ ε / 2)
      (by positivity)
      (by rw [riemannianEDistOf_self]; exact ENNReal.ofReal_pos.mpr (by linarith))
      (by rw [mul_div_cancel₀ _ hsQ.ne']; linarith) hURad
  have hbudget : 2 * StandardCap.transitionEnd + Real.sqrt (8 * (M' * Q)) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * (M' * Q)) * (θ₁ / Q)) *
        (lam / Real.sqrt Q + ∑ k ∈ Finset.range (0 + 1), (fun _ => (R + ε / 2) / Real.sqrt Q) k)
          < D := by
    rw [zero_add, Finset.sum_range_one, ← add_div, sqrt_mul_exp_mul_div_eq_P6L (by linarith) hQpos]
    exact hD
  have htr := htrace 0 (fun _ => x.val) (fun _ => (R + ε / 2) / Real.sqrt Q) (M' * Q) (θ₁ / Q)
    rfl (fun _ _ => by positivity) (fun _ _ z hz => hballU hz)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
    (fun _ _ z hz => hball z hz) (mul_le_mul_of_nonneg_right hM'K hQpos.le)
    (by nlinarith) hτ0 hτT
    (by
      have : (Ctime : ℝ) * (M' * Q) * (θ₁ / Q) = Ctime * M' * θ₁ := by field_simp
      rw [this]; exact hCθ)
    (by
      have : 4 * (M' * Q) * (θ₁ / Q) = 4 * M' * θ₁ := by field_simp
      rw [this]; exact hθθ)
    hbudget 0 le_rfl
  obtain ⟨first, hfirst, hS⟩ := ObservedHistory.exists_uniform_backwardPointTrace_of_forall
    H.toHistory {z | z ∈ riemannianClosedBallOf (A.flow.base.metric T) x.val (R / Real.sqrt Q)}
    (c := T - θ₁ / Q) (by linarith) (fun z hz => by
      refine htr z ?_
      change riemannianEDistOf _ _ _ < _
      refine lt_of_le_of_lt (show riemannianEDistOf _ _ _ ≤ _ from hz) ?_
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      exact div_lt_div_of_pos_right (by linarith) hsQ)
  refine ⟨first, hfirst, fun y hy => hS y.val ?_⟩
  exact (A.mem_scaled_endpoint_closedBall_iff Q hQpos x y R).mp hy

/-- **`_P6L`**：原 `RetainedCoreHistory.traced_buffer_of_chain_traces`（`TP:33`）。改动：区域
`U : ∀ i, Set (last stage).Carrier`、先验半径 `Rad` 与 `hU : ∀ i, B_{Q·L}(x i, Rad) ⊆ U i`（放 `hQ` 后）；
`htrace` 加链球成员前提；结论 buffer 限于 `R + ε ≤ Rad`（rev1 9.3/9.5：只在已控球内生产 trace）。
证明体照抄（调 `CB:55_P6L`）。 -/
theorem RetainedCoreHistory.traced_buffer_of_chain_traces_P6L
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (U : ∀ i, Set ((H i).stage (Fin.last (H i).eventCount)).Carrier) (Rad : ℝ)
    (hU : ∀ i, ∀ y ∈ riemannianBallOf
      (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
        ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
      (x i) Rad, y.val ∈ U i)
    {Kc lam θ : ℝ} {Ctime : ℝ≥0} {Phi : ℝ → ℝ} (hθ : 0 < θ) (D : ℕ → ℝ)
    (hD : Tendsto D atTop atTop)
    (htime : Tendsto (fun i => (A i).flow.scalar (time i) (x i).val * time i) atTop atTop)
    (htrace : ∀ i (N : ℕ) (p : ℕ → ((H i).stage (Fin.last (H i).eventCount)).Carrier)
      (δ : ℕ → ℝ) (M τ : ℝ), p 0 = (x i).val → (∀ k ≤ N, 0 < δ k) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k), z ∈ U i) →
      (∀ k < N, p (k + 1) ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k)) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k),
        (A i).flow.scalar (time i) z ≤ M) →
      Kc * (A i).flow.scalar (time i) (x i).val ≤ M → 1 ≤ M → 0 ≤ τ → τ ≤ time i →
      (Ctime : ℝ) * M * τ ≤ 1 / 2 → 4 * M * τ ≤ θ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * M) * τ) *
          (lam / Real.sqrt ((A i).flow.scalar (time i) (x i).val) +
            ∑ k ∈ Finset.range (N + 1), δ k) < D i →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k),
        ∃ first : Fin ((H i).eventCount + 1), (H i).time first ≤ time i - τ ∧
          Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
            (Fin.le_last first) z)) :
    ∀ R ε B : ℝ, 0 < R → 0 < ε → R + ε ≤ Rad → (∀ᶠ i in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
          (x i) (R + ε),
        metricScalarAt ((A i).endpointTerminalLimitMetric
          ((H i).stage (Fin.last (H i).eventCount))).metric y ≤
          B * (A i).flow.scalar (time i) (x i).val) →
      ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∀ᶠ i in atTop, ∃ first : Fin ((H i).eventCount + 1),
        (H i).time first ≤ time i - θ₁ / (A i).flow.scalar (time i) (x i).val ∧
        ∀ y ∈ riemannianClosedBallOf
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
            ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
          (x i) R,
          Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
            (Fin.le_last first) y.val) := by
  intro R ε B hR hε hRad hB
  have hM' : 1 ≤ max (max B Kc) 1 := le_max_right _ _
  set θ₁ := min (θ / (4 * max (max B Kc) 1)) (1 / (2 * ((Ctime : ℝ) + 1) * max (max B Kc) 1))
    with hθ₁def
  have hθ₁ : 0 < θ₁ := lt_min (by positivity) (by positivity)
  have hθθ : 4 * max (max B Kc) 1 * θ₁ ≤ θ := by
    have h := min_le_left (θ / (4 * max (max B Kc) 1))
      (1 / (2 * ((Ctime : ℝ) + 1) * max (max B Kc) 1))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hCθ : (Ctime : ℝ) * max (max B Kc) 1 * θ₁ ≤ 1 / 2 := by
    have h := min_le_right (θ / (4 * max (max B Kc) 1))
      (1 / (2 * ((Ctime : ℝ) + 1) * max (max B Kc) 1))
    rw [le_div_iff₀ (by positivity)] at h
    have hC := Ctime.coe_nonneg
    have h1 : 0 ≤ max (max B Kc) 1 * θ₁ := by positivity
    nlinarith
  refine ⟨θ₁, hθ₁, ?_⟩
  filter_upwards [hB, htime.eventually_ge_atTop θ₁,
    hD.eventually_gt_atTop (2 * StandardCap.transitionEnd + Real.sqrt (8 * max (max B Kc) 1) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * max (max B Kc) 1) * θ₁) *
        (lam + (R + ε / 2)))] with i hBi hTi hDi
  exact RetainedCoreHistory.exists_trace_first_of_chain_trace_on_scaled_ball_P6L (H i) (A i)
    (x i) (hQ i) (U i) (htrace i) hR hε hRad (hU i) hBi hθ₁ hθθ hCθ hTi hDi

/-- consumer：原 `TP:33`（无成员前提的 `htrace`、buffer 对所有 `R ε`）由 `_P6L` 版取 `U = univ`、
`Rad = R + ε` 推出。 -/
example : type_of% @RetainedCoreHistory.traced_buffer_of_chain_traces.{u} := by
  intro H time A x hQ Kc lam θ Ctime Phi hθ D hD htime htrace R ε B hR hε hB
  exact RetainedCoreHistory.traced_buffer_of_chain_traces_P6L H time A x hQ (fun _ => univ) (R + ε)
    (fun _ _ _ => trivial) hθ D hD htime
    (fun i N p δ M τ h0 hδ _ => htrace i N p δ M τ h0 hδ) R ε B hR hε le_rfl hB

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
