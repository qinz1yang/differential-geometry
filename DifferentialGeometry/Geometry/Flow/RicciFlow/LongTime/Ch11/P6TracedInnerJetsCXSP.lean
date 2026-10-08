import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionShiWholeBall
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false

/-!
# CX-SPINE：原 history 的 traced outer ball 生产任意严格内闭球的 jets

固定 0 <= R < Rwide、theta、K0 后先选择全部阶数的 J；history 与 Q 随后。
令 delta=(Rwide-R)/4。对内闭球每个 z，真实三角包含将 z 中心的
2*delta/sqrt(Q) 开球放进原 traced region，原 starting clock 与全部 Rm 界原样保留。
再调用 A11b at z itself，取 s=delta/sqrt(Q)、tau=theta/delta^2、C0=K0*delta^2。
This recentering avoids shrinking the outer ball by one half and losing the inner ball.
不要求 Good、Dt、RegularSlice 或正 stage age；birth/horizon 保留。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 固定外层 traced ball 在任意严格内层闭球上生产 normalized jets。 -/
theorem exists_inner_jets_of_traced_region_CXSP
    (R Rwide θ K0 : ℝ) (hR : 0 ≤ R) (hRR : R < Rwide)
    (hθ : 0 < θ) (hK0 : 0 < K0) :
    ∃ J : ℕ → ℝ, (∀ m, 1 ≤ J m) ∧
      ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
        (p : (H.stageAt t).Carrier) (Q : ℝ) (hQ : 0 < Q),
        H.isTracedRegion t p (Rwide / Real.sqrt Q) (θ / Q) (K0 * Q) →
        ∀ m : ℕ, ∀ z ∈ riemannianClosedBallOf
          (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) p R,
          curvDerivNorm m
            (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) z ≤ J m := by
  let δ : ℝ := (Rwide - R) / 4
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  let τ : ℝ := θ / δ ^ 2
  let C0 : ℝ := K0 * δ ^ 2
  have hτ : 0 < τ := div_pos hθ (sq_pos_of_pos hδ)
  have hC0 : 0 < C0 := mul_pos hK0 (sq_pos_of_pos hδ)
  let D : ℕ → ℝ := fun m =>
    shiLocalUniformBound 3 m (C0 * τ / 2)
        (Real.sqrt C0 / (8 * Real.exp ((3 : ℝ) ^ 2 * (C0 * τ / 2)))) *
      C0 / Real.sqrt (τ / 2) ^ m
  let J : ℕ → ℝ := fun m => max 1 (D m / δ ^ (m + 2))
  refine ⟨J, fun m => le_max_left _ _, ?_⟩
  intro H t p Q hQ htraced m z hz
  let g := H.stageMetric (H.activeStage t) t
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hRwide : 0 < Rwide := hR.trans_lt hRR
  let s : ℝ := δ / Real.sqrt Q
  have hs : 0 < s := div_pos hδ hsqrt
  have hs2 : s ^ 2 = δ ^ 2 / Q := by
    dsimp only [s]
    rw [div_pow, Real.sq_sqrt hQ.le]
  have hdepth : τ * s ^ 2 = θ / Q := by
    dsimp only [τ]
    rw [hs2]
    field_simp [hδ.ne', hQ.ne']
  have hcurvature : C0 / s ^ 2 = K0 * Q := by
    dsimp only [C0]
    rw [hs2]
    field_simp [hδ.ne', hQ.ne']
  have hzphysical : z ∈ riemannianClosedBallOf g p (R / Real.sqrt Q) := by
    have hball := riemannianClosedBallOf_scaleMetric Q hQ g p (R / Real.sqrt Q)
    have hscaleR : Real.sqrt Q * (R / Real.sqrt Q) = R :=
      mul_div_cancel₀ R hsqrt.ne'
    rw [hscaleR] at hball
    rw [← hball]
    exact hz
  have hsum : R / Real.sqrt Q + 2 * s < Rwide / Real.sqrt Q := by
    calc
      _ = (R + 2 * δ) / Real.sqrt Q := by dsimp only [s]; ring
      _ < Rwide / Real.sqrt Q := div_lt_div_of_pos_right
        (by dsimp only [δ]; linarith) hsqrt
  have hsub : riemannianBallOf g z (2 * s) ⊆
      riemannianBallOf g p (Rwide / Real.sqrt Q) := by
    intro w hw
    calc
      riemannianEDistOf g p w ≤
          riemannianEDistOf g p z + riemannianEDistOf g z w :=
        riemannianEDistOf_triangle g p z w
      _ ≤ ENNReal.ofReal (R / Real.sqrt Q) + ENNReal.ofReal (2 * s) :=
        add_le_add hzphysical hw.le
      _ = ENNReal.ofReal (R / Real.sqrt Q + 2 * s) :=
        (ENNReal.ofReal_add (div_nonneg hR hsqrt.le) (by positivity)).symm
      _ < ENNReal.ofReal (Rwide / Real.sqrt Q) :=
        (ENNReal.ofReal_lt_ofReal_iff (div_pos hRwide hsqrt)).mpr hsum
  have htr : H.isTracedRegion t z (2 * s) (τ * s ^ 2) (C0 / s ^ 2) := by
    rw [hdepth, hcurvature]
    obtain ⟨_hradius, htime, a, hat, hclock, htraces⟩ := htraced
    exact ⟨by positivity, htime, a, hat, hclock, fun w hw => htraces w (hsub hw)⟩
  have hzself : z ∈ riemannianBallOf g z s := by
    change riemannianEDistOf g z z < ENNReal.ofReal s
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hs
  have hb := FILL910.A11b_shi_whole_ball_of_isTracedRegion
    H t z hτ hs hC0 htr m z hzself
  change curvDerivNorm m g z ≤ D m / s ^ (m + 2) at hb
  have hrescale : D m / s ^ (m + 2) =
      (D m / δ ^ (m + 2)) * Real.sqrt Q ^ (m + 2) := by
    dsimp only [s]
    rw [div_pow, div_div_eq_mul_div]
    ring
  rw [hrescale] at hb
  have hphysical : curvDerivNorm m g z ≤ J m * Real.sqrt Q ^ (m + 2) :=
    hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (pow_nonneg hsqrt.le _))
  change curvDerivNorm m (scaleMetric Q hQ g) z ≤ J m
  rw [curvDerivNorm_scaleMetric]
  apply (div_le_iff₀ (mul_pos hQ (pow_pos hsqrt m))).mpr
  calc
    curvDerivNorm m g z ≤ J m * Real.sqrt Q ^ (m + 2) := hphysical
    _ = J m * (Q * Real.sqrt Q ^ m) := by
      rw [pow_add, Real.sq_sqrt hQ.le]
      ring

end GC.LongTime.Ch11

end
