import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceTracedSecondLevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceChainBuffers3_P6L

/-!
# L6-B：`BoundedCurvatureAtDistanceTracedSecondLevel:67` 的局部化（`_P6L`）

局部化合同 §2 (W)(G) + rev1a C2.2：原
`RetainedCoreHistory.exists_trace_first_on_witness_ball_of_scaled_ray_chain`
（`ST/BoundedCurvatureAtDistanceTracedSecondLevel.lean:67`）只把 `hgradient`、`hW` 整体传给 CB:320
（链 `p k = (pt k).val`）。这里 `hgradient`、`hW` 限于 `U`，新增链点 / 终点成员前提
`hchainU : ∀ k < N, B_T((pt k).val, 4·r₀) ⊆ U`、`hendU : (pt N).val ∈ U`，转给 CB:320_P6L。
证明体照抄。
-/

set_option autoImplicit false


noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- **`_P6L`**：原 `RetainedCoreHistory.exists_trace_first_on_witness_ball_of_scaled_ray_chain`
（TSL:67）。改动：`hgradient`、`hW` 限于 `U`；加 `hchainU`、`hendU`（rev1a C2.2）。结论逐字。 -/
theorem RetainedCoreHistory.exists_trace_first_on_witness_ball_of_scaled_ray_chain_P6L
    (H : RetainedCoreHistory.{u}) {T : ℝ}
    (A : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
    (hQ : 1 ≤ A.flow.scalar T x.val) {Kc lam θ D : ℝ} {Ctime Cgrad : ℝ≥0} {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi) (hlam : 0 ≤ lam) (hθ : 0 < θ)
    (htrace : ∀ (N : ℕ) (p : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δ : ℕ → ℝ)
      (M τ : ℝ), p 0 = x.val → (∀ k ≤ N, 0 < δ k) →
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
    {q : ℝ} (hqQ : q ≤ A.flow.scalar T x.val) (U : Set (H.stage (Fin.last H.eventCount)).Carrier)
    (hgradient : ∀ y ∈ U, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) T, q < A.flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential (A.restrictIncoming le_rfl A.lt le_rfl).flow t y v| ≤
          Cgrad * A.flow.scalar t y * Real.sqrt (A.flow.scalar t y) *
            Real.sqrt ((A.flow.base.metric t).inner y v v))
    {eps C1 C2 : ℝ}
    (hW : ∀ y ∈ U, q < A.flow.scalar T y →
      ∃ W : SpatialCanonicalWitness (A.flow.base.metric T) eps C1 C2 y, W.capTubeHasNeckChart eps)
    {K L : ℝ} (hK : 1 ≤ K) (hL : 3 ≤ L) {N : ℕ}
    (pt : ℕ → (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) (hpt0 : pt 0 = x)
    (hptR : ∀ k < N, metricScalarAt (scaleMetric (A.flow.scalar T x.val) (zero_lt_one.trans_le hQ)
      (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric) (pt k) ≤
        K * L + 1)
    (hptd : ∀ k < N, riemannianEDistOf (scaleMetric (A.flow.scalar T x.val)
      (zero_lt_one.trans_le hQ)
      (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric) (pt k)
        (pt (k + 1)) <
      ENNReal.ofReal (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * ((K + 1) * L)))))
    (hyX : |metricScalarAt (scaleMetric (A.flow.scalar T x.val) (zero_lt_one.trans_le hQ)
      (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric) (pt N) - L| < 1)
    (hchainU : ∀ k < N, riemannianBallOf (A.flow.base.metric T) (pt k).val
      (2 * (2 * (localPropagationRadius Cgrad /
        Real.sqrt (2 * ((K + 1) * L * A.flow.scalar T x.val))))) ⊆ U)
    (hendU : (pt N).val ∈ U)
    (hT : secondLevelTraceDepth K C2 Kc θ Ctime ≤ A.flow.scalar T x.val * T)
    (hD : 2 * StandardCap.transitionEnd +
      Real.sqrt (8 * (secondLevelTraceConstant K C2 Kc * L)) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0)) *
        (3 / 2 * secondLevelTraceConstant K C2 Kc * secondLevelTraceDepth K C2 Kc θ Ctime)) *
      (lam + (N * (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * ((K + 1) * L)))) + 1)) <
        D) :
    ∃ first : Fin (H.eventCount + 1),
      H.time first ≤ T - secondLevelTraceDepth K C2 Kc θ Ctime / A.flow.scalar T (pt N).val ∧
      ∀ z ∈ riemannianBallOf (A.flow.base.metric T) (pt N).val
        (Real.sqrt (A.flow.scalar T (pt N).val))⁻¹,
        Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
          (Fin.le_last first) z) := by
  have hQpos : 0 < A.flow.scalar T x.val := zero_lt_one.trans_le hQ
  have hsQ : 0 < Real.sqrt (A.flow.scalar T x.val) := Real.sqrt_pos.mpr hQpos
  have hflow (k : ℕ) : A.flow.scalar T (pt k).val = A.flow.scalar T x.val *
      metricScalarAt (scaleMetric (A.flow.scalar T x.val) (zero_lt_one.trans_le hQ)
        (A.endpointTerminalLimitMetric (H.stage (Fin.last H.eventCount))).metric) (pt k) := by
    rw [A.scaled_endpoint_scalar_eq, ← mul_assoc, mul_inv_cancel₀ hQpos.ne', one_mul]
  refine RetainedCoreHistory.exists_trace_first_on_witness_ball_of_ray_chain_P6L H A x hQ hPhi
    hlam hθ htrace hqQ U hgradient hW hK hL (fun k => (pt k).val) (by rw [hpt0]) (fun k hk => ?_)
    hchainU hendU (fun k hk => ?_) ?_ ?_ hT hD
  · rw [hflow k]
    have h1 := mul_le_mul_of_nonneg_left (hptR k hk) hQpos.le
    have h2 : A.flow.scalar T x.val * (K * L + 1) ≤ (K + 1) * L * A.flow.scalar T x.val := by
      have : 0 ≤ A.flow.scalar T x.val * (L - 1) := mul_nonneg hQpos.le (by linarith)
      nlinarith
    exact h1.trans h2
  · have h := hptd k hk
    rw [A.scaled_endpoint_edist_eq] at h
    have hne : ENNReal.ofReal (Real.sqrt (A.flow.scalar T x.val)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hsQ).ne'
    rw [ENNReal.ofReal_div_of_pos hsQ, ENNReal.lt_div_iff_mul_lt (Or.inl hne)
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact h
  · rw [hflow N]
    have := (abs_lt.mp hyX).1
    nlinarith
  · rw [hflow N]
    have := (abs_lt.mp hyX).2
    nlinarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Set

/-- consumer：原 TSL:67（全局 `hgradient`、`hW`）由 `_P6L` 版（`U = univ`）推出。 -/
example :
    type_of% @RetainedCoreHistory.exists_trace_first_on_witness_ball_of_scaled_ray_chain.{0}
    := by
  intro H T A x hQ Kc lam θ D Ctime Cgrad Phi hPhi hlam hθ htrace q hqQ hgradient eps C1 C2 hW
    K L hK hL N pt hpt0 hptR hptd hyX hT hD
  exact H.exists_trace_first_on_witness_ball_of_scaled_ray_chain_P6L A x hQ hPhi hlam hθ htrace
    hqQ univ (fun y _ => hgradient y) (fun y _ => hW y) hK hL pt hpt0 hptR hptd hyX
    (fun _ _ => subset_univ _) (mem_univ _) hT hD

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
