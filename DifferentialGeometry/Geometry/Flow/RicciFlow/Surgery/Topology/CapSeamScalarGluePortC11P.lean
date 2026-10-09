import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapBoundaryChord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckAnnulusControl
import DifferentialGeometry.Topology.MetricSpace.BallPasting

/-!
# S-CH11-FIX5 port of astra `CapSeamScalarGlue`（`PortC11P`）

来源：donor `CapSeamScalarGlue.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有 7 个 error（`NeckAnnulusControl` 落地后暴露），均为实例 / 型对齐问题；本 port 只做
elaboration 层面修补（no statement / definition / proof idea altered）：
* 在 namespace 开头加 `attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace`（同 `NeckAnnulusControl` / `CapWindowLocalInverse` donor 文件
  的第一行；W8 fat 宿主里这两个 Tensor0S 实例是全局的，会抢在 Riemannian bundle 实例前面）。
* 加 file-local `Nonempty (Sphere 2)` 实例（同 `CapAnnulusCoordinatesPortC11P`）。
* `truncatedAnnulusDistance_lipschitzOn`：开头 `have : LocallyCompactSpace M :=
  ChartedSpace.locallyCompactSpace ThreeSpace M`（给 `PseudoEMetricSpace.ofRiemannianMetric` 要的
  `RegularSpace M`）；`apply (show … by simpa only [truncatedAnnulusDistance, …] using h).trans`
  改为 `simp only [ENNReal.coe_one, one_mul] at h; exact h`（`edist` 与 `riemannianEDistOf`、以及
  `truncatedAnnulusDistance` 的 delta 只差默认透明度的 defeq，`simpa` 收尾只做 reducible 匹配）。
* `PresentedStaticCap` 一节开头加 `private local instance terminalSigmaCompact :
  SigmaCompactSpace E.incoming.terminalRegularOpen`（同树内 `BackwardNeckMetric` 的写法；
  `NormalizedNeck` 的 `annulusPoint_boundary` / `annulusPoint_retained` 需要它）。
-/

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold Function
open DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance : Nonempty (Sphere 2) :=
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

namespace NormalizedNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
  (N : NormalizedNeck g δ k)

def truncatedAnnulusDistance (p : M) (R : ℝ≥0) (x : ThreeSpace) : ℝ :=
  (min (riemannianEDistOf g (N.annulusPoint x) p) (R : ℝ≥0∞)).toReal

theorem truncatedAnnulusDistance_lipschitzOn (p : M) (R : ℝ≥0)
    {x₀ : ThreeSpace} (hx₀ : ‖x₀‖ = standardCapL) :
    LipschitzOnWith N.annulusDerivativeConstant (N.truncatedAnnulusDistance p R)
      (Metric.ball x₀ capSeamWidth) := by
  intro x hx y hy
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  let : RiemannianBundle (TangentSpace ThreeModel : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (TangentSpace ThreeModel : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric ThreeModel M
  have h := EMetric.lipschitzWith_truncated_edist_level p R (N.annulusPoint x) (N.annulusPoint y)
  apply (show edist (N.truncatedAnnulusDistance p R x)
    (N.truncatedAnnulusDistance p R y) ≤
      riemannianEDistOf g (N.annulusPoint x) (N.annulusPoint y) by
        simp only [ENNReal.coe_one, one_mul] at h
        exact h).trans
  exact N.annulusPoint_edist_le hx₀ hx hy

end NormalizedNeck

namespace MetricCutCapEvent.PresentedStaticCap

universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D η : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
  (S : E.PresentedStaticCap fixed D m η b)

private local instance terminalSigmaCompact : SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      E.incoming.terminalRegularOpen.isOpen)

def collarOldPoint (hOld : E.old = E.transition.trace.retainedCore)
    (x : neckRetainedCollar S.delta) : E.old :=
  ⟨(S.retainedPoint x).val, hOld.symm ▸ (S.retainedPoint x).property⟩

theorem oldTerminal_collarOldPoint (hOld : E.old = E.transition.trace.retainedCore)
    (x : neckRetainedCollar S.delta) (hx : x.val ∈ neckBuffer S.delta) :
    E.oldTerminal (S.collarOldPoint hOld x) = S.neck.chart ⟨x.val, hx⟩ := by
  apply Subtype.ext
  rw [E.oldTerminal_eq]
  exact S.retained_point_eq x hx

theorem oldOutput_collarOldPoint (hOld : E.old = E.transition.trace.retainedCore)
    (x : neckRetainedCollar S.delta) :
    E.oldOutput (S.collarOldPoint hOld x) = S.inclusion (S.witness.retained x) :=
  Sum.inl.inj ((E.oldOutput_eq (S.collarOldPoint hOld x)).symm.trans (S.retained_eq x))

/-- The actual post-window labels agree with the same retained old-output map. -/
theorem window_collarOldPoint (hOld : E.old = E.transition.trace.retainedCore)
    (hcoord : S.witness.HasRadialCoordinates) (x : neckRetainedCollar S.delta)
    (hx : (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ standardCapWindow D) :
    S.inclusion (S.witness.window
      ⟨(standardCapL + x.val.2) • (x.val.1 : ThreeSpace), hx⟩) =
        E.oldOutput (S.collarOldPoint hOld x) := by
  rw [hcoord.2 x hx, S.oldOutput_collarOldPoint hOld x]

/-- Glue the supplied boundary extension to the original terminal-distance data
on both sides of a fixed coordinate neighborhood of every seam point. -/
theorem exists_local_scalar_glue (p : E.incoming.terminalRegularOpen) (R : ℝ≥0) :
    ∃ (f φ : ThreeSpace → ℝ),
      LipschitzWith S.boundaryExtensionConstant f ∧
      (∀ x ∈ standardCapClosedCore, φ x = f x) ∧
      (∀ x, standardCapL ≤ ‖x‖ → φ x = S.neck.truncatedAnnulusDistance p R x) ∧
      ∀ x₀ : ThreeSpace, ‖x₀‖ = standardCapL →
        LipschitzOnWith (S.boundaryExtensionConstant + S.neck.annulusDerivativeConstant)
          φ (Metric.ball x₀ capSeamWidth) := by
  classical
  obtain ⟨f, hf, hboundary⟩ := S.exists_boundary_distance_extension p R
  let exterior := S.neck.truncatedAnnulusDistance p R
  have hseam : EqOn f exterior (Metric.sphere (0 : ThreeSpace) standardCapL) := by
    intro x hx
    have hnorm : ‖x‖ = standardCapL := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hx
    have hL : 0 < standardCapL := by
      rw [standardCapL_eq_transitionEnd]
      exact StandardCap.transitionEnd_pos
    let y : Sphere 2 := (capRadialCoordinates x).1
    have hcoord : capBoundaryCoordinate y = x := by
      change standardCapL • (DifferentialGeometry.Topology.Manifold.sphereDirection
        (Classical.choice (inferInstance : Nonempty (Sphere 2))) x : ThreeSpace) = x
      rw [← hnorm]
      exact DifferentialGeometry.Topology.Manifold.norm_smul_sphereDirection _
        (norm_pos_iff.mp (hnorm.symm ▸ hL))
    rw [← hcoord, hboundary]
    dsimp only [exterior, NormalizedNeck.truncatedAnnulusDistance, capBoundaryCoordinate]
    rw [S.neck.annulusPoint_boundary]
  let φ := (Metric.closedBall (0 : ThreeSpace) standardCapL).piecewise f exterior
  refine ⟨f, φ, hf, ?_, ?_, ?_⟩
  · intro x hx
    exact Set.piecewise_eq_of_mem _ _ _ hx
  · intro x hx
    by_cases hmem : x ∈ Metric.closedBall (0 : ThreeSpace) standardCapL
    · have heq : ‖x‖ = standardCapL := le_antisymm
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hmem) hx
      exact (Set.piecewise_eq_of_mem _ _ _ hmem).trans
        (hseam (by simpa only [Metric.mem_sphere, dist_zero_right] using heq))
    · exact Set.piecewise_eq_of_notMem _ _ _ hmem
  · intro x₀ hx₀
    apply DifferentialGeometry.Analysis.lipschitzOnWith_piecewise_closedBall_of_eqOn_sphere
      (convex_ball x₀ capSeamWidth)
    · exact hf.lipschitzOnWith
    · exact (S.neck.truncatedAnnulusDistance_lipschitzOn p R hx₀).mono inter_subset_left
    · exact hseam.mono inter_subset_right

/-- A coordinate-local receiver for the same actual cap and retained maps. The
coordinate companion is produced by the canonical finite constructor. This gives
no global output Lipschitz bound and no whole-event distance comparison. -/
theorem exists_actual_local_scalar_glue
    (hOld : E.old = E.transition.trace.retainedCore)
    (hcoord : S.witness.HasRadialCoordinates)
    (p : E.incoming.terminalRegularOpen) (R : ℝ≥0) :
    ∃ (f φ : ThreeSpace → ℝ),
      LipschitzWith S.boundaryExtensionConstant f ∧
      (∀ (x : ThreeSpace) (hx : x ∈ standardCapWindow D) (hc : x ∈ standardCapClosedCore),
        S.inclusion (S.witness.window ⟨x, hx⟩) =
          S.inclusion (S.witness.capChart ⟨x, hc⟩) ∧ φ x = f x) ∧
      (∀ (x : neckRetainedCollar S.delta)
        (hx : (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ standardCapWindow D),
        (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ capSeamOpen →
        S.inclusion (S.witness.window
          ⟨(standardCapL + x.val.2) • (x.val.1 : ThreeSpace), hx⟩) =
            E.oldOutput (S.collarOldPoint hOld x) ∧
        φ ((standardCapL + x.val.2) • (x.val.1 : ThreeSpace)) =
          (min (riemannianEDistOf E.terminal.metric
            (E.oldTerminal (S.collarOldPoint hOld x)) p) (R : ℝ≥0∞)).toReal) ∧
      ∀ x₀ : ThreeSpace, ‖x₀‖ = standardCapL →
        LipschitzOnWith (S.boundaryExtensionConstant + S.neck.annulusDerivativeConstant)
          φ (Metric.ball x₀ capSeamWidth) := by
  obtain ⟨f, φ, hf, hinside, houtside, hlocal⟩ := S.exists_local_scalar_glue p R
  refine ⟨f, φ, hf, ?_, ?_, hlocal⟩
  · intro x hx hc
    exact ⟨congrArg S.inclusion (hcoord.1 x hx hc), hinside x hc⟩
  · intro x hx hnear
    refine ⟨S.window_collarOldPoint hOld hcoord x hx, ?_⟩
    have hL : 0 < standardCapL := by
      rw [standardCapL_eq_transitionEnd]
      exact StandardCap.transitionEnd_pos
    have hr : 0 < standardCapL + x.val.2 := add_pos_of_pos_of_nonneg hL x.property.1
    have hnorm : ‖(standardCapL + x.val.2) • (x.val.1 : ThreeSpace)‖ =
        standardCapL + x.val.2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
    have hbuffer : x.val ∈ neckBuffer S.delta := by
      have hp := inv_pos.mpr S.neck.delta_pos
      constructor <;> linarith [x.property.1, x.property.2]
    rw [houtside _ (by rw [hnorm]; linarith [x.property.1])]
    dsimp only [NormalizedNeck.truncatedAnnulusDistance]
    rw [S.neck.annulusPoint_retained x hnear hbuffer,
      S.oldTerminal_collarOldPoint hOld x hbuffer]

end MetricCutCapEvent.PresentedStaticCap
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
