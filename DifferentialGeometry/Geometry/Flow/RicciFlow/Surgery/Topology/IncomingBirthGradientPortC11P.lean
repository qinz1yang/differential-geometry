import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabScalarDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabGradientBounds

/-!
# O-CH11-FIX3 port of astra `IncomingBirthGradient`（`PortC11P`）

来源：donor `DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/IncomingBirthGradient.lean`
（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。修补（elaboration only；no statement / definition /
proof idea altered）：
* 两处 `ContinuousWithinAt.mono (fun _ hu => hu.le)`（`Ioi a ⊆ Ici a`）改为
  `.mono Ioi_subset_Ici_self`（`hu.le : a ≤ x` 不再按 expected type `x ∈ Ici a` 统一）。

原路径 `IncomingBirthGradient` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

/-- An outgoing slab's original open gradient bound holds at its birth whenever
the original strict scalar threshold holds there. The coefficient is unchanged. -/
theorem abs_scalarDifferential_le_at_birth_of_gradientBoundBefore
    {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
    {Cgrad : ℝ≥0} {q : ℝ} (hq : 0 < q)
    (hgrad : G.GradientBoundBefore Cgrad q s)
    (y : P.Carrier) (hRy : q < G.flow.scalar a y) (v : TangentSpace ThreeModel y) :
    |Perelman.CanonicalNeighborhood.scalarDifferential G.flow a y v| ≤
      Cgrad * G.flow.scalar a y * Real.sqrt (G.flow.scalar a y) *
        Real.sqrt ((G.flow.base.metric a).inner y v v) := by
  obtain ⟨c, hac, hcs⟩ := exists_between G.lt
  let S := G.closedPrefix c hac hcs
  have hRcont : ContinuousOn (fun u : ℝ => G.flow.scalar u y) (Icc a c) :=
    S.equation.scalarCont.comp (f := fun u : ℝ => (u, y))
      (continuousOn_id.prodMk continuousOn_const) (fun u hu => ⟨hu, mem_univ y⟩)
  have hNcont : ContinuousOn (fun u : ℝ => (G.flow.base.metric u).inner y
      (gradientFun (G.flow.base.metric u) (G.flow.scalar u) y)
      (gradientFun (G.flow.base.metric u) (G.flow.scalar u) y)) (Icc a c) :=
    S.scalar_gradient_norm_sq_continuousOn.comp (f := fun u : ℝ => (u, y))
      (continuousOn_id.prodMk continuousOn_const) (fun u hu => ⟨hu, mem_univ y⟩)
  have hRci : ContinuousWithinAt (fun u : ℝ => G.flow.scalar u y) (Ici a) a :=
    (hRcont a ⟨le_rfl, hac.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨le_rfl, hac⟩)
  have hNci : ContinuousWithinAt (fun u : ℝ => (G.flow.base.metric u).inner y
      (gradientFun (G.flow.base.metric u) (G.flow.scalar u) y)
      (gradientFun (G.flow.base.metric u) (G.flow.scalar u) y)) (Ici a) a :=
    (hNcont a ⟨le_rfl, hac.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨le_rfl, hac⟩)
  have hRright : ContinuousWithinAt (fun u : ℝ => G.flow.scalar u y) (Ioi a) a :=
    hRci.mono Ioi_subset_Ici_self
  have hf : ContinuousWithinAt (fun u : ℝ => (G.flow.base.metric u).inner y
      (gradientFun (G.flow.base.metric u) (G.flow.scalar u) y)
      (gradientFun (G.flow.base.metric u) (G.flow.scalar u) y) -
      (Cgrad * G.flow.scalar u y * Real.sqrt (G.flow.scalar u y)) ^ 2) (Ioi a) a :=
    (hNci.mono Ioi_subset_Ici_self).sub
      (((continuousWithinAt_const.mul hRright).mul hRright.sqrt).pow 2)
  have hev : ∀ᶠ u in 𝓝[>] a, (G.flow.base.metric u).inner y
      (gradientFun (G.flow.base.metric u) (G.flow.scalar u) y)
      (gradientFun (G.flow.base.metric u) (G.flow.scalar u) y) -
      (Cgrad * G.flow.scalar u y * Real.sqrt (G.flow.scalar u y)) ^ 2 ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsGT G.lt, hRright.eventually (lt_mem_nhds hRy)]
      with u hu hqu
    have hRu : 0 < G.flow.scalar u y := hq.trans hqu
    exact sub_nonpos.mpr (G.inner_gradientFun_scalar_le_sq_of_abs_scalarDifferential_le y
      (by positivity) (hgrad y u hu hqu))
  have hle := le_of_tendsto hf.tendsto hev
  have hRa : 0 < G.flow.scalar a y := hq.trans hRy
  exact G.abs_scalarDifferential_le_of_inner_gradientFun_le_sq y (by positivity)
    (sub_nonpos.mp hle) v

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
