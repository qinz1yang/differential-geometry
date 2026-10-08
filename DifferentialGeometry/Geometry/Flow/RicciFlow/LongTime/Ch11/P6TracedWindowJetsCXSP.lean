import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedWindowPinchingCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionShiWholeBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall
import DifferentialGeometry.Geometry.Metric.RestrictionDistance

set_option autoImplicit false

/-!
# CX-SPINE：同一 normalized traced flow 的后半窗全阶 jets

J 只依赖 theta/K，先于 stage/history/query。
原 compact stage 支付 unit open ball 内的 intrinsic closed half-ball compactness，
再由公开 local Shi 生产 intrinsic 闭球 1/8、后半时间窗上的全部阶数界。
ambient 闭球 1/16 的点通过 restriction distance 实际落入该内球。
实际 consumer 只调用一次 G57，保留同 B 的 terminal identity、Rm 与统一 pinching。
不增加 compact-ball、metric comparison、jets、Good 或 Dt 输入。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- unit-ball flow 的零阶界实付后半窗全阶界；空间边界由原 stage 支付。 -/
theorem exists_stage_unit_window_jets_CXSP (θ K : ℝ) (hθ : 0 < θ) (hK : 0 < K) :
    ∃ J : ℕ → ℝ, (∀ m, 1 ≤ J m) ∧
      ∀ {P : OrientedThreeStage.{u}} (g : P.Metric) (p : P.Carrier)
        (U : TopologicalSpace.Opens P.Carrier),
        (U : Set P.Carrier) = riemannianBallOf g p 1 →
      ∀ B : SolutionOn (I := ThreeModel) (M := U)
          (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)),
        IsSolutionOn B → B.base.metric 0 = g.restrictOpen U →
        (∀ s ∈ Icc (-θ) 0, ∀ x : U, curvDerivNormSq 0 (B.base.metric s) x ≤ K ^ 2) →
      ∃ pU : U, pU.val = p ∧
        (∀ m : ℕ, ∀ s ∈ Icc (-(θ / 2)) 0,
          ∀ x ∈ riemannianClosedBallOf (B.base.metric 0) pU (1 / 8),
            curvDerivNorm m (B.base.metric s) x ≤ J m) ∧
        ∀ m : ℕ, ∀ s ∈ Icc (-(θ / 2)) 0, ∀ x : U,
          x.val ∈ riemannianClosedBallOf g p (1 / 16) →
            curvDerivNorm m (B.base.metric s) x ≤ J m := by
  let D : ℕ → ℝ := fun m =>
    shiLocalUniformBound 3 m (K * (θ / 4))
        (((1 / 2) / (4 * Real.exp ((3 : ℝ) ^ 2 * K * θ))) * Real.sqrt K /
          (4 * Real.exp ((3 : ℝ) ^ 2 * K * (θ / 4)))) *
      K / Real.sqrt (θ / 4) ^ m
  let J : ℕ → ℝ := fun m => max 1 (D m)
  refine ⟨J, fun m => le_max_left _ _, ?_⟩
  intro P g p U hU B hB hzero hRm
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hp : p ∈ U := by
    change p ∈ (U : Set P.Carrier)
    rw [hU]
    change riemannianEDistOf g p p < ENNReal.ofReal 1
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr zero_lt_one
  let pU : U := ⟨p, hp⟩
  have hhalf : riemannianClosedBallOf g p (1 / 2) ⊆ U := by
    intro x hx
    rw [hU]
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by norm_num))
  have hcompact : IsCompact (riemannianClosedBallOf (B.base.metric 0) pU (1 / 2)) := by
    rw [hzero]
    exact FILL910.isCompact_riemannianClosedBallOf_restrictOpen_of_subset
      g U pU (1 / 2) hhalf
  have hshi := shi_curvDerivNorm_on_terminal_ball B hB
    (a := -θ) (b := 0) (K := K) (R := 1 / 2)
    (neg_lt_zero.mpr hθ) hK (by norm_num) Subset.rfl Subset.rfl pU hcompact
    (fun s hs x _ => hRm s hs x)
  have hinner (m : ℕ) (s : ℝ) (hs : s ∈ Icc (-(θ / 2)) 0)
      (x : U) (hx : x ∈ riemannianClosedBallOf (B.base.metric 0) pU (1 / 8)) :
      curvDerivNorm m (B.base.metric s) x ≤ J m := by
    have hb : curvDerivNorm m (B.base.metric s) x ≤ D m := by
      have hh := hshi m s (by simpa only [add_zero, neg_div] using hs) x
        (by simpa only [show (1 / 2 : ℝ) / 4 = 1 / 8 by norm_num] using hx)
      simpa [D, ThreeSpace] using hh
    exact hb.trans (le_max_right _ _)
  refine ⟨pU, rfl, hinner, ?_⟩
  intro m s hs x hx
  have hball : riemannianBallOf g p (1 / 8) ⊆ U := by
    intro y hy
    rw [hU]
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (by norm_num : (1 / 8 : ℝ) ≤ 1))
  have hxlt : riemannianEDistOf g pU x < ENNReal.ofReal (1 / 8) :=
    hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 8)).mpr
      (by norm_num))
  have hxU := Geometry.Metric.riemannianEDistOf_restrictOpen_lt_of_riemannianBallOf_subset
    g U pU x hball hxlt
  apply hinner m s hs x
  rw [hzero]
  exact hxU.le

/-- G57 的同 B 同时保留 normalized terminal、Rm、pinching 及实际后半窗 jets。 -/
theorem exists_prepared_traced_window_pinching_and_jets_CXSP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (a₀ : ℝ) (Phi : ℝ → ℝ), 0 < a₀ ∧ AdmissiblePinchingFunction Phi ∧
      ∀ θ K : ℝ, ∀ hθ : 0 < θ, 0 < K →
      ∃ J : ℕ → ℝ, (∀ m, 1 ≤ J m) ∧
        ∀ {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
          (chain : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g),
          F.tower = chain.tower → ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
          (R : ℝ) (hR : 0 < R),
          H.isTracedRegion t p (Real.sqrt R)⁻¹ (θ / R) (K * R) →
        let gN := scaleMetric R hR (H.stageMetric (H.activeStage t) t)
        let aMin := a₀ + (t : ℝ) - θ / R
        let Lambda := aMin * R
        0 < aMin ∧ 0 < Lambda ∧
          ∃ U : TopologicalSpace.Opens (H.stageAt t).Carrier,
            (U : Set (H.stageAt t).Carrier) =
              riemannianBallOf (H.stageMetric (H.activeStage t) t) p (Real.sqrt R)⁻¹ ∧
            (U : Set (H.stageAt t).Carrier) = riemannianBallOf gN p 1 ∧
          ∃ B : SolutionOn (I := ThreeModel) (M := U)
              (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)),
            IsSolutionOn B ∧ B.base.metric 0 = gN.restrictOpen U ∧
            (∀ s ∈ Icc (-θ) 0, ∀ x : U,
              curvDerivNormSq 0 (B.base.metric s) x ≤ K ^ 2 ∧
              curvatureOperatorLowerBoundAt (B.base.metric s) x
                (metricAlgebraicCurvatureTensorAt (B.base.metric s) x)
                (rescalePinchingFunction Lambda Phi (metricScalarAt (B.base.metric s) x))) ∧
            ∃ pU : U, pU.val = p ∧
              (∀ m : ℕ, ∀ s ∈ Icc (-(θ / 2)) 0,
                ∀ x ∈ riemannianClosedBallOf (B.base.metric 0) pU (1 / 8),
                  curvDerivNorm m (B.base.metric s) x ≤ J m) ∧
              ∀ m : ℕ, ∀ s ∈ Icc (-(θ / 2)) 0, ∀ x : U,
                x.val ∈ riemannianClosedBallOf gN p (1 / 16) →
                  curvDerivNorm m (B.base.metric s) x ≤ J m := by
  obtain ⟨a₀, Phi, ha₀, hPhi, hpin⟩ := exists_prepared_traced_window_pinching_CXSP P g
  refine ⟨a₀, Phi, ha₀, hPhi, ?_⟩
  intro θ K hθ hK
  obtain ⟨J, hJ, hjets⟩ := exists_stage_unit_window_jets_CXSP θ K hθ hK
  refine ⟨J, hJ, ?_⟩
  intro pBase Γ chain F hTower n H t p R hR htraced gN aMin Lambda
  obtain ⟨hMin, hLambda, U, hU, B, hB, hzero, hcontrol⟩ :=
    hpin chain F hTower n t p R (Real.sqrt R)⁻¹ θ K hR hθ htraced
  have hball := riemannianBallOf_scaleMetric R hR
    (H.stageMetric (H.activeStage t) t) p (Real.sqrt R)⁻¹
  rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr hR).ne'] at hball
  have hUnorm : (U : Set (H.stageAt t).Carrier) = riemannianBallOf gN p 1 :=
    hU.trans hball.symm
  obtain ⟨pU, hpU, hinner, hambient⟩ := hjets gN p U hUnorm B hB hzero
    (fun s hs x => (hcontrol s hs x).1)
  exact ⟨hMin, hLambda, U, hU, hUnorm, B, hB, hzero, hcontrol,
    pU, hpU, hinner, hambient⟩

end GC.LongTime.Ch11

end
