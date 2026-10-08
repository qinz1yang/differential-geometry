import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedSeedFirstExitCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6MovingSpatialGradientCXSP

set_option autoImplicit false

/-!
# CX-SPINE G22：同一 moving spatial 供给消费任意 S 的 seed first-exit

未退出后缀给两条 trace 的当前距离，真实三角包含将局部梯度测试点放回同一ρ球。
standard C1P6/C2P6 原样保持；不从空间 witness 反推中心的完整时间 Good。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- 同一 moving spatial witness 支付 G21 的局部梯度，保留真实中心时间 Good。 -/
theorem exists_prepared_spatial_firstExit_CXSP (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
      ∀ L : ℝ, ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        let C1 := C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ
        let C2 := C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ
        ∀ {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t) {r M : ℝ},
        T₀ ≤ (t : ℝ) → (t : ℝ) / 2 ≤ a → 0 < r → q.neckRadius t ≤ r →
        M * r ^ 2 ≤ L →
        ∀ {p x : (H.stageAt t).Carrier}
          (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) p)
          (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x)
          {qcan Q K ℓ D ρ : ℝ},
        0 < M → qcan ≤ M →
        metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ M →
        metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ M →
        Γ.Ctime * M * ((t : ℝ) - a) ≤ 1 / 2 →
        0 < ℓ → 0 < Q → 1 ≤ Q * (a : ℝ) →
        (C2.toNNReal : ℝ) * ℓ * Real.sqrt (2 * M) ≤ 1 / 4 → K * ℓ ^ 2 ≤ 1 →
        2 * Real.sqrt 3 * (4 * M / Q + max (8 * M / Q) (2 * Real.exp 4)) * Q ≤ K →
        D + 2 * ℓ ≤ ρ →
        A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - a)) < (ENNReal.ofReal D) →
        ∀ (_hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a ≤ v) (_hvt : v ≤ t),
          (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < (ENNReal.ofReal D)) →
          ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → ∀ z : (H.stageAt w).Carrier,
            (z = A.point (H.activeStage w) (H.activeStage_mono haw)
                (H.activeStage_mono hwt) ∨
              z = B.point (H.activeStage w) (H.activeStage_mono haw)
                (H.activeStage_mono hwt)) →
            qcan ≤ metricScalarAt (H.stageMetric (H.activeStage w) w) z →
            H.HasSpatialCanonicalTimeControl Γ.epsilon C1 C2 Γ.Ctime w z)
        (_hspatial : ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
          a < w → w < t → H.time (H.activeStage w) < (w : ℝ) →
          ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
            (A.point (H.activeStage w) (H.activeStage_mono haw)
              (H.activeStage_mono hwt)) ρ,
          qcan ≤ metricScalarAt (H.stageMetric (H.activeStage w) w) z →
          Nonempty (SpatialCanonicalWitness (H.stageMetric (H.activeStage w) w)
            Γ.epsilon C1 C2 z)),
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          A.pairEDist_CXSP (hat := hat) B v hav hvt < (ENNReal.ofReal D) ∧
            A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
              A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v)) := by
  obtain ⟨ε₀, hε₀, hfirst⟩ := exists_prepared_seed_firstExit_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γ S F q hTower hdiag hacc hrad hord L
  obtain ⟨T₀, hT₀, hmain⟩ := hfirst S F q hTower hdiag hacc hrad hord L
  refine ⟨T₀, hT₀, ?_⟩
  intro n H C1 C2 a t hat r M ht hhalf hr hguard hML p x A B qcan Q K ℓ D ρ
    hM hqM hscalarA hscalarB htime hℓ hQ hlate hspace hKℓ hK hregion hmargin hgood hspatial
  refine hmain n hat ht hhalf hr hguard hML A B hM hqM hscalarA hscalarB htime hℓ
    hQ hlate hspace hKℓ hK hmargin hgood ?_
  intro v hav hvt hstay w haw hwt hvw hwtlt hage z hz hR ξ
  exact pair_ball_gradient_of_spatial_CXSP (H.stageMetric (H.activeStage w) w) _ _ hℓ
    (hstay w haw hwt hvw hwtlt) hregion
    (fun y hy hyR => hspatial w haw hwt (hav.trans_lt hvw) hwtlt hage y hy hyR) z hz hR ξ

end GC.LongTime.Ch11
