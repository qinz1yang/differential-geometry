import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs
import DifferentialGeometry.Topology.Manifold.Components
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false
noncomputable section

open Set Manifold Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

namespace BallChart

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  (c : BallChart n I M) (U : TopologicalSpace.Opens M) (hU : c.chart.target ⊆ U)

include c hU in
private theorem restrictTarget_nonempty : Nonempty U :=
  ⟨⟨c.chart 0, hU (c.chart.map_source
    (c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))))⟩⟩

private def restrictTargetChart :
    _root_.PartialDiffeomorph (𝓡 n) I (EuclideanSpace ℝ (Fin n)) U ∞ :=
  c.chart.trans (PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)).symm

private theorem restrictTargetChart_source : (c.restrictTargetChart U hU).source = c.chart.source := by
  change c.chart.source ∩ c.chart ⁻¹' (PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)).target = _
  have ht : (PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)).target = U :=
    U.openPartialHomeomorphSubtypeCoe_target _
  rw [ht]
  exact inter_eq_left.mpr fun x hx => hU (c.chart.map_source hx)

private theorem restrictTargetChart_target : (c.restrictTargetChart U hU).target =
    (Subtype.val : U → M) ⁻¹' c.chart.target := by
  change (PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)).source ∩
    (PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)) ⁻¹' c.chart.target = _
  have hs : (PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)).source = univ :=
    U.openPartialHomeomorphSubtypeCoe_source _
  rw [hs, univ_inter]
  rfl

def restrictTarget : BallChart n I U where
  chart := c.restrictTargetChart U hU
  closedBall_subset_source := by
    rw [c.restrictTargetChart_source U hU]
    exact c.closedBall_subset_source

@[simp] theorem restrictTarget_source : (c.restrictTarget U hU).chart.source = c.chart.source :=
  c.restrictTargetChart_source U hU

@[simp] theorem restrictTarget_target : (c.restrictTarget U hU).chart.target =
    (Subtype.val : U → M) ⁻¹' c.chart.target := c.restrictTargetChart_target U hU

theorem restrictTarget_apply {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ c.chart.source) :
    ((c.restrictTarget U hU).chart x).val = c.chart x := by
  let e := PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)
  have het : e.target = U := U.openPartialHomeomorphSubtypeCoe_target _
  have he : c.chart x ∈ e.target := by rw [het]; exact hU (c.chart.map_source hx)
  change (e.symm (c.chart x)).val = c.chart x
  exact e.right_inv' he


theorem restrictTarget_mfderiv {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ c.chart.source) :
    mfderiv (𝓡 n) I ((c.restrictTarget U hU).chart : EuclideanSpace ℝ (Fin n) → U) x =
      mfderiv (𝓡 n) I (c.chart : EuclideanSpace ℝ (Fin n) → M) x := by
  have heq : (fun y : EuclideanSpace ℝ (Fin n) => ((c.restrictTarget U hU).chart y).val)
      =ᶠ[𝓝 x] (c.chart : EuclideanSpace ℝ (Fin n) → M) := by
    filter_upwards [c.chart.open_source.mem_nhds hx] with y hy
    exact c.restrictTarget_apply U hU hy
  rw [← DifferentialGeometry.mfderiv_subtypeVal_comp]
  exact heq.mfderiv_eq

end BallChart

namespace OrientedBallChart

variable {M : ClosedOrientedManifold 3} (c : OrientedBallChart M)
  (K : ConnectedComponents M.Carrier) (hK : c.chart.target ⊆ M.componentSet K)

def component : OrientedBallChart (M.component K).toClosedOrientedManifold where
  toBallChart := c.toBallChart.restrictTarget (M.componentOpen K) hK
  preserves_orientation := by
    intro x hx
    have hx' : x ∈ c.chart.source :=
      (c.toBallChart.restrictTarget_source (M.componentOpen K) hK) ▸ hx
    have heq : (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
        (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
          (c.toBallChart.restrictTarget (M.componentOpen K) hK).chart hx) (by simp)).toLinearEquiv =
        (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
          (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ c.chart hx') (by simp)).toLinearEquiv := by
      ext v
      exact congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => L v)
        (c.toBallChart.restrictTarget_mfderiv (M.componentOpen K) hK hx')
    erw [heq]
    have ho := c.preserves_orientation x hx'
    change _ = M.componentTangentOrientation K ((c.toBallChart.restrictTarget (M.componentOpen K) hK).chart x)
    rw [M.componentTangentOrientation_apply,
      c.toBallChart.restrictTarget_apply (M.componentOpen K) hK hx']
    exact ho

@[simp] theorem component_source : (c.component K hK).chart.source = c.chart.source :=
  c.toBallChart.restrictTarget_source (M.componentOpen K) hK

@[simp] theorem component_target : (c.component K hK).chart.target =
    (Subtype.val : (M.component K).Carrier → M.Carrier) ⁻¹' c.chart.target :=
  c.toBallChart.restrictTarget_target (M.componentOpen K) hK

theorem component_apply {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ c.chart.source) :
    ((c.component K hK).chart x).val = c.chart x :=
  c.toBallChart.restrictTarget_apply (M.componentOpen K) hK hx

end OrientedBallChart

end DifferentialGeometry.Topology
