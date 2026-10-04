import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.WholeBallRecentring
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Topology.SigmaCompactOpen

/-!
# Whole-ball Shi estimates on a traced region (chapters 9–10, adapter A11b)

Input: the M01 seed shape `isTracedRegion t p (2s) (τ s²) (C₀ s⁻²)`.  Output: the ambient bound on
`B(p, s)` for every derivative order, with the constant of A11a in dimension three.

Proof.  `exists_common_flow_with_compact_neighborhood_of_isTracedRegion` gives the common flow `S`
on `U = B(p, 2s)` with `S(t) = g(t).restrictOpen U` and the curvature bound.  For `q ∈ B(p, s)`
lifted to `q_U ∈ U`, the intrinsic closed ball `B̄_{S(t)}(q_U, s/2)` is compact:
* lifting: the ambient closed ball `B̄_{g(t)}(q, s/2)` lies in `U` and is compact (stages are
  compact), so its preimage in `U` is compact;
* closedness: the intrinsic ball is closed in `U` and lies in that preimage, because the ambient
  distance is at most the intrinsic one (`riemannianEDistOf_le_restrictOpen`).
This is the public copy of the private `isCompact_riemannianClosedBallOf_restrictOpen`
(`ST/TracedRegionAncientLimit.lean`).  Then the terminal Shi estimate at `q_U` with the shifted
left end `t - τ s²/2`, the constant bookkeeping of A11a, and `curvDerivNorm_restrictOpen`.

The zero-order bridge `curvDerivNormSq 0 g z = normSq0S g z 4 (metricRm04At g z)` is the public
copy of the private lemma in `ST/TracedRegionWindowLimit.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness

section Bridges

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]

/-- The zero-order curvature derivative norm is the tensor norm of `Rm` (dimension three;
public copy of the private bridge in `ST/TracedRegionWindowLimit.lean`). -/
theorem curvDerivNormSq_zero_eq_normSq0S_metricRm04At
    (g : SmoothRiemannianMetric ThreeModel M) (z : M) :
    curvDerivNormSq 0 g z = normSq0S g z 4 (metricRm04At g z) := by
  have h0 : curvCovDeriv (I := ThreeModel) (M := M) g 0 = metricRm04 g := rfl
  rw [curvDerivNormSq, h0, metricRm04_apply]

/-- Closed balls of a restricted metric are compact when the ambient closed ball of the same
radius lies in the open set and the ambient manifold is compact (lifting + closedness; public
copy of the private lemma in `ST/TracedRegionAncientLimit.lean`). -/
theorem isCompact_riemannianClosedBallOf_restrictOpen_of_subset [CompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : Opens M) (p : U) (r : ℝ)
    (hsub : riemannianClosedBallOf g (p : M) r ⊆ U) :
    IsCompact (riemannianClosedBallOf (g.restrictOpen U) p r) := by
  have hK : IsCompact (Subtype.val ⁻¹' riemannianClosedBallOf g (p : M) r : Set U) :=
    U.isOpenEmbedding'.isEmbedding.isInducing.isCompact_preimage'
      (Geometry.Metric.isClosed_riemannianClosedBallOf g _ r).isCompact
      (by rw [Subtype.range_coe]; exact hsub)
  refine hK.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ p r) ?_
  intro x hx
  exact (riemannianEDistOf_le_restrictOpen g U p x).trans hx

end Bridges

/-- A11b (I11 on a traced region, M): the WBD03 shape.  The input is exactly the M01 seed shape
`isTracedRegion t p (2s) (τ s²) (C₀ s⁻²)`; the output is the ambient whole-ball bound for every
order, with the A11a constant in dimension three. -/
theorem A11b_shi_whole_ball_of_isTracedRegion (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) {τ s C₀ : ℝ}
    (hτ : 0 < τ) (hs : 0 < s) (hC₀ : 0 < C₀)
    (htr : H.isTracedRegion t p (2 * s) (τ * s ^ 2) (C₀ / s ^ 2)) (m : ℕ) :
    ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p s,
      curvDerivNorm m (H.stageMetric (H.activeStage t) t) q ≤
        shiLocalUniformBound 3 m (C₀ * τ / 2)
            (Real.sqrt C₀ / (8 * Real.exp ((3 : ℝ) ^ 2 * (C₀ * τ / 2)))) *
          C₀ / Real.sqrt (τ / 2) ^ m / s ^ (m + 2) := by
  intro q hq
  obtain ⟨a, hat, ha, U, hU, -, -, -, -, -, S, hS, -, hRm, hcurrent, -⟩ :=
    H.exists_common_flow_with_compact_neighborhood_of_isTracedRegion t p htr
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hterminal : S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U :=
    hcurrent t ⟨hat, le_rfl⟩ (H.activeStage_mem t)
  have hmemU : ∀ y, riemannianEDistOf (H.stageMetric (H.activeStage t) t) p y <
      ENNReal.ofReal (2 * s) → y ∈ U := by
    intro y hy
    rw [← SetLike.mem_coe, hU]
    exact hy
  have hqU : q ∈ U := hmemU q (hq.trans_le (ENNReal.ofReal_le_ofReal (by linarith)))
  let qU : U := ⟨q, hqU⟩
  have hR : 0 < s / 2 := by positivity
  have hsub : riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) q (s / 2) ⊆ U := by
    intro y hy
    apply hmemU y
    calc riemannianEDistOf (H.stageMetric (H.activeStage t) t) p y
        ≤ riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q +
            riemannianEDistOf (H.stageMetric (H.activeStage t) t) q y :=
          riemannianEDistOf_triangle _ p q y
      _ ≤ ENNReal.ofReal s + ENNReal.ofReal (s / 2) := add_le_add hq.le hy
      _ = ENNReal.ofReal (s + s / 2) := (ENNReal.ofReal_add hs.le hR.le).symm
      _ < ENNReal.ofReal (2 * s) := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have hcpt : IsCompact (riemannianClosedBallOf (S.base.metric t) qU (s / 2)) := by
    rw [hterminal]
    exact isCompact_riemannianClosedBallOf_restrictOpen_of_subset _ U qU (s / 2) hsub
  have hs2 : 0 < τ * s ^ 2 := by positivity
  have hlt : t.val - τ * s ^ 2 / 2 < t.val := by linarith
  have hK : 0 < C₀ / s ^ 2 := by positivity
  have hcarrier : Icc (t.val - τ * s ^ 2 / 2) t.val ⊆
      (RealTimeInterval.closed a.val t.val hat).carrier := by
    intro u hu
    exact ⟨by rw [ha]; linarith [hu.1], hu.2⟩
  have hregular : Ico (t.val - τ * s ^ 2 / 2) t.val ⊆
      (RealTimeInterval.closed a.val t.val hat).regular := by
    intro u hu
    exact ⟨by rw [ha]; linarith [hu.1], hu.2⟩
  have hcurv : ∀ u ∈ Icc (t.val - τ * s ^ 2 / 2) t.val,
      ∀ y ∈ riemannianClosedBallOf (S.base.metric t) qU (s / 2),
        curvDerivNormSq 0 (S.base.metric u) y ≤ (C₀ / s ^ 2) ^ 2 := by
    intro u hu y _
    rw [curvDerivNormSq_zero_eq_normSq0S_metricRm04At]
    exact hRm u (hcarrier hu) y
  have h := shi_curvDerivNorm_terminal_of_terminal_ball S hS hlt hK hR hcarrier hregular qU hcpt
    hcurv m
  have hba : t.val - (t.val - τ * s ^ 2 / 2) = τ * s ^ 2 / 2 := by ring
  rw [hba, shiLocalUniformBound_recentred_eq _ m hτ hs, hterminal, curvDerivNorm_restrictOpen,
    finrank_euclideanSpace_fin] at h
  simpa only [Nat.cast_ofNat] using h

end FILL910
