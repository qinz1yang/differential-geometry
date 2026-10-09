import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TimeTracedRegionCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionShiWholeBall
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling

set_option autoImplicit false

/-!
# CX-SPINE：实际 secondary traced region 的 whole-ball Shi jets

先固定 θ/K0，再选择全部阶数的 J；history/query 随后。
实际调用 A11b common-flow/whole-ball Shi，取 s=1/(2√Rn)、τ=4θ、C0=K0/4。
保留原 history，允许 birth/horizon；不添加 Good、Dt 或 ratio 前提。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- 原 history 的 traced unit ball 给物理半球及其 normalized metric 的统一 jets。 -/
theorem exists_secondary_jets_of_traced_region_CXSP
    (θ K0 : ℝ) (hθ : 0 < θ) (hK0 : 0 < K0) :
    ∃ J : ℕ → ℝ, (∀ m, 1 ≤ J m) ∧
      ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
        (y : (H.stageAt t).Carrier) (Rn : ℝ) (hRn : 0 < Rn),
        H.isTracedRegion t y (Real.sqrt Rn)⁻¹ (θ / Rn) (K0 * Rn) →
        ∀ m : ℕ, ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y
          (1 / (2 * Real.sqrt Rn)),
          curvDerivNorm m (H.stageMetric (H.activeStage t) t) z ≤
              J m * Real.sqrt Rn ^ (m + 2) ∧
            curvDerivNorm m
              (scaleMetric Rn hRn (H.stageMetric (H.activeStage t) t)) z ≤ J m := by
  let D : ℕ → ℝ := fun m =>
    shiLocalUniformBound 3 m ((K0 / 4) * (4 * θ) / 2)
        (Real.sqrt (K0 / 4) /
          (8 * Real.exp ((3 : ℝ) ^ 2 * ((K0 / 4) * (4 * θ) / 2)))) *
      (K0 / 4) / Real.sqrt ((4 * θ) / 2) ^ m
  let J : ℕ → ℝ := fun m => max 1 (D m * 2 ^ (m + 2))
  refine ⟨J, fun m => le_max_left _ _, ?_⟩
  intro H t y Rn hRn htraced m z hz
  have hsqrt : 0 < Real.sqrt Rn := Real.sqrt_pos.mpr hRn
  let s := 1 / (2 * Real.sqrt Rn)
  have hs : 0 < s := by dsimp only [s]; positivity
  have hs2 : s ^ 2 = 1 / (4 * Rn) := by
    dsimp only [s]
    rw [div_pow, mul_pow, Real.sq_sqrt hRn.le]
    norm_num
  have hradius : 2 * s = (Real.sqrt Rn)⁻¹ := by
    dsimp only [s]
    field_simp [hsqrt.ne']
  have hdepth : (4 * θ) * s ^ 2 = θ / Rn := by
    rw [hs2]
    field_simp [hRn.ne']
  have hcurvature : (K0 / 4) / s ^ 2 = K0 * Rn := by
    rw [hs2]
    field_simp [hRn.ne']
  have htr : H.isTracedRegion t y (2 * s) ((4 * θ) * s ^ 2)
      ((K0 / 4) / s ^ 2) := by
    rwa [hradius, hdepth, hcurvature]
  have hb := FILL910.A11b_shi_whole_ball_of_isTracedRegion H t y
    (by positivity : 0 < 4 * θ) hs (by positivity : 0 < K0 / 4) htr m z hz
  change curvDerivNorm m (H.stageMetric (H.activeStage t) t) z ≤
    D m / s ^ (m + 2) at hb
  have hrescale : D m / s ^ (m + 2) =
      (D m * 2 ^ (m + 2)) * Real.sqrt Rn ^ (m + 2) := by
    dsimp only [s]
    rw [one_div, inv_pow, div_inv_eq_mul, mul_pow]
    ring
  rw [hrescale] at hb
  have hphysical : curvDerivNorm m (H.stageMetric (H.activeStage t) t) z ≤
      J m * Real.sqrt Rn ^ (m + 2) :=
    hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (pow_nonneg hsqrt.le _))
  refine ⟨hphysical, ?_⟩
  rw [curvDerivNorm_scaleMetric]
  apply (div_le_iff₀ (mul_pos hRn (pow_pos hsqrt m))).mpr
  calc
    curvDerivNorm m (H.stageMetric (H.activeStage t) t) z ≤
        J m * Real.sqrt Rn ^ (m + 2) := hphysical
    _ = J m * (Rn * Real.sqrt Rn ^ m) := by
      rw [pow_add, Real.sq_sqrt hRn.le]
      ring

/-- 从新 TimeCore 与实际 chain 直接生产 normalized secondary jets；J 先于 L。 -/
theorem exists_prepared_time_secondary_jets_CXSP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 L0 : ℝ, 4 ≤ H0 ∧ 3 ≤ L0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ θ K0 : ℝ, ∃ J : ℕ → ℝ, 0 < θ ∧ 0 < K0 ∧ (∀ m, 1 ≤ J m) ∧
        ∀ L : ℝ, L0 ≤ L → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ r →
        ∀ (y : (H.stageAt t).Carrier) (dCenter : ℝ), 0 ≤ dCenter →
          dCenter + 1 / Real.sqrt H0 ≤ d0 →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p y ≤
            ENNReal.ofReal (dCenter * r) →
        let Rn := metricScalarAt (H.stageMetric (H.activeStage t) t) y
        Q * (L - 1) < Rn → Rn < Q * (L + 1) →
        H.isTracedRegion t y (Real.sqrt Rn)⁻¹ (θ / Rn) (K0 * Rn) ∧
          ∀ (hRn : 0 < Rn) (m : ℕ),
          ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y
            (1 / (2 * Real.sqrt Rn)),
            curvDerivNorm m
              (scaleMetric Rn hRn (H.stageMetric (H.activeStage t) t)) z ≤ J m := by
  obtain ⟨ε₀, hε₀, htraced⟩ := exists_prepared_time_traced_region_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA
  obtain ⟨H0, L0, hH0, hL0, htracedA⟩ :=
    htraced S F q hTower hdiag hacc hrad hord hb Afac hA
  refine ⟨H0, L0, hH0, hL0, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨θ, K0, hθ, hK0, htracedL⟩ := htracedA d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨J, hJpos, hJ⟩ := exists_secondary_jets_of_traced_region_CXSP θ K0 hθ hK0
  refine ⟨θ, K0, J, hθ, hK0, hJpos, ?_⟩
  intro L hL
  obtain ⟨T₀, hT₀, htracedN⟩ := htracedL L hL
  refine ⟨T₀, hT₀, ?_⟩
  intro n H t p r Q ht htime hsmall hvol hguard y dCenter hdCenter hfit hcenter
    Rn hlower hupper
  have htr := htracedN n t p r ht htime hsmall hvol hguard
    y dCenter hdCenter hfit hcenter hlower hupper
  exact ⟨htr, fun hRn m z hz => (hJ H t y Rn hRn htr m z hz).2⟩

end GC.LongTime.Ch11

end
