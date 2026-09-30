import DifferentialGeometry.Topology.Manifold.BallChartOpenImage
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.OrientedBallChart

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

universe u v

variable {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}

theorem exists_orientedBallChart_of_open_embedding
    (c : OrientedBallChart M) (U : TopologicalSpace.Opens M.Carrier)
    (f : U → N.Carrier) (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) (hinj : Injective f)
    (hfo : ∀ x, Orientation.map (Fin 3)
      (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (M.orientation.orientation x.val) = N.orientation.orientation (f x))
    (hU : ∀ x ∈ Metric.closedBall (0 : E3) 2, c.chart x ∈ U) :
    ∃ d : OrientedBallChart N, ∀ x (hx : x ∈ Metric.closedBall (0 : E3) 2),
      d.chart x = f ⟨c.chart x, hU x hx⟩ := by
  classical
  obtain ⟨d, hsub, hd, hb⟩ := c.toBallChart.exists_ballChart_of_open_embedding U f hf hinj hU
  refine ⟨⟨d, ?_⟩, hb⟩
  intro x hx
  have hxsrc := hsub hx
  obtain ⟨hxU, hxval⟩ := hd x hx
  have h0U : c.chart (0 : E3) ∈ U := hU 0 (Metric.mem_closedBall_self (by norm_num))
  let g : E3 → U := fun y =>
    if hy : c.chart y ∈ U then ⟨c.chart y, hy⟩ else ⟨c.chart 0, h0U⟩
  have hgx : g x = ⟨c.chart x, hxU⟩ := dite_eq_left hxU
  have hgc : (fun y => (g y).val) =ᶠ[𝓝 x] c.chart := by
    have hc := c.chart.contMDiffOn_toFun.continuousOn.continuousAt (c.chart.open_source.mem_nhds hxsrc)
    filter_upwards [hc.preimage_mem_nhds (U.isOpen.mem_nhds hxU)] with y hy
    rw [show g y = ⟨c.chart y, hy⟩ from dite_eq_left hy]
  have hcg := IsLocalDiffeomorphAt.of_eventuallyEq hgc (c.chart.isLocalDiffeomorphAt _ _ _ hxsrc)
  have hgloc : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ g x :=
    DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict (fun y => (g y).property) hcg
  have hdg : (d.chart : E3 → N.Carrier) =ᶠ[𝓝 x] f ∘ g := by
    filter_upwards [d.chart.open_source.mem_nhds hx] with y hy
    obtain ⟨hyU, hyval⟩ := hd y hy
    rw [hyval]
    change f ⟨c.chart y, hyU⟩ = f (g y)
    rw [show g y = ⟨c.chart y, hyU⟩ from dite_eq_left hyU]
  have hgder : mfderiv (𝓡 3) (𝓡 3) g x = mfderiv (𝓡 3) (𝓡 3) c.chart x := by
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp g x]
    exact hgc.mfderiv_eq
  have heq : ((d.chart.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hx).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv =
      ((c.chart.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hxsrc).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv.trans
        (hf.mfderivToContinuousLinearEquiv (by simp) (g x)).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 3) (𝓡 3) d.chart x v = mfderiv (𝓡 3) (𝓡 3) f (g x)
      (mfderiv (𝓡 3) (𝓡 3) c.chart x v)
    rw [hdg.mfderiv_eq]
    erw [mfderiv_comp_apply x (hf.mdifferentiable (by simp) _) (hgloc.mdifferentiableAt (by simp))]
    rw [hgder]
    rfl
  rw [heq]
  erw [← DifferentialGeometry.VectorBundle.map_orientation_trans_between]
  rw [c.preserves_orientation x hxsrc]
  have h := hfo (g x)
  rw [hgx] at h
  rw [hxval, hgx]
  exact h

end DifferentialGeometry.Topology.OrientedBallChart
