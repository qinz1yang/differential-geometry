import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamTransition
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SumLaws
open Set Metric Manifold Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology
open DifferentialGeometry.Topology.ConnectedSumQuotient
open DifferentialGeometry.Topology.OrientationAssembly

universe u

noncomputable section

namespace OrientationAssembly

variable {M : ClosedOrientedManifold.{u} 3}

def ballChartTangentEquiv (c : BallChart 3 (𝓡 3) M.Carrier) {x : csModel}
    (hx : x ∈ c.chart.source) :
    TangentSpace 𝓘(ℝ, csModel) x ≃L[ℝ] TangentSpace (𝓡 3) (c.chart x) :=
  IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
    (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ c.chart hx) (by simp)

end OrientationAssembly

variable {M M' : ClosedOrientedManifold.{u} 3} (c' : OrientedBallChart M')
    (Φ : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier)

theorem mem_source_pullback {x : csModel}
    (hx : x ∈ (BallChart.pullback c'.toBallChart Φ).chart.source) :
    x ∈ c'.toBallChart.chart.source := by
  have h := hx
  rw [BallChart.pullback, PartialDiffeomorph.trans_toPartialEquiv,
    OpenPartialHomeomorph.trans_source] at h
  exact h.1

namespace OrientationAssembly

theorem ballChartTangentEquiv_pullback {x : csModel}
    (hx : x ∈ (BallChart.pullback c'.toBallChart Φ).chart.source)
    (hx' : x ∈ c'.toBallChart.chart.source) :
    (ballChartTangentEquiv (BallChart.pullback c'.toBallChart Φ) hx).toLinearEquiv =
      (chartTangentEquiv c' hx').toLinearEquiv.trans
        (((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
          (c'.toBallChart.chart x)).toLinearEquiv) := by
  have hcomp := mfderiv_comp (x := x)
    (f := (fun y : csModel => c'.toBallChart.chart y))
    (g := (fun y : M'.Carrier => Φ.symm y))
    ((Φ.symm).mdifferentiable (by simp) (c'.toBallChart.chart x))
    (PartialDiffeomorph.mdifferentiableAt c'.toBallChart.chart (by simp) hx')
  apply LinearEquiv.ext
  intro v
  change (mfderiv (𝓡 3) (𝓡 3)
      (fun y : csModel => Φ.symm (c'.toBallChart.chart y)) x) v =
    (mfderiv (𝓡 3) (𝓡 3) (fun y : M'.Carrier => Φ.symm y) (c'.toBallChart.chart x))
      ((mfderiv (𝓡 3) (𝓡 3) (fun y : csModel => c'.toBallChart.chart y) x) v)
  erw [DFunLike.congr_fun hcomp v]
  rw [ContinuousLinearMap.comp_apply]

theorem ballChart_pullback_preserves_orientation
    (hΦ : Φ.preservesOrientation M.orientation M'.orientation) :
    ∀ x, ∀ hx : x ∈ (BallChart.pullback c'.toBallChart Φ).chart.source,
      Orientation.map (Fin 3)
        (ballChartTangentEquiv (BallChart.pullback c'.toBallChart Φ) hx).toLinearEquiv
        (_root_.OrientationAssembly.stdOrientation x) =
      M.orientation.orientation ((BallChart.pullback c'.toBallChart Φ).chart x) := by
  intro x hx
  have hx' := mem_source_pullback c' Φ hx
  have hchain := ballChartTangentEquiv_pullback c' Φ hx hx'
  have hsymm := Diffeomorph.preservesOrientation_symm hΦ
  have step1 : Orientation.map (Fin 3)
        (ballChartTangentEquiv (BallChart.pullback c'.toBallChart Φ) hx).toLinearEquiv
        (_root_.OrientationAssembly.stdOrientation x)
      = Orientation.map (Fin 3)
          ((chartTangentEquiv c' hx').toLinearEquiv.trans
            (((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
              (c'.toBallChart.chart x)).toLinearEquiv))
          (_root_.OrientationAssembly.stdOrientation x) := by
        rw [hchain]
        rfl
  have step2 : Orientation.map (Fin 3)
          ((chartTangentEquiv c' hx').toLinearEquiv.trans
            (((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
              (c'.toBallChart.chart x)).toLinearEquiv))
          (_root_.OrientationAssembly.stdOrientation x)
      = Orientation.map (Fin 3)
          ((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
            (c'.toBallChart.chart x)).toLinearEquiv
          (Orientation.map (Fin 3) (chartTangentEquiv c' hx').toLinearEquiv
            (_root_.OrientationAssembly.stdOrientation x)) := by
        rw [← _root_.OrientationAssembly.orientation_map_map_trans (R := ℝ)
          (chartTangentEquiv c' hx').toLinearEquiv
          ((Φ.symm).mfderivToContinuousLinearEquiv (by simp) (c'.toBallChart.chart x)).toLinearEquiv
          (_root_.OrientationAssembly.stdOrientation x)]
  have step3 : Orientation.map (Fin 3)
          ((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
            (c'.toBallChart.chart x)).toLinearEquiv
          (Orientation.map (Fin 3) (chartTangentEquiv c' hx').toLinearEquiv
            (_root_.OrientationAssembly.stdOrientation x))
      = Orientation.map (Fin 3)
          ((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
            (c'.toBallChart.chart x)).toLinearEquiv
          (M'.orientation.orientation (c'.toBallChart.chart x)) := by
        rw [← _root_.OrientationAssembly.orientation_eq_map_chartTangentEquiv c' hx']
  have step4 : Orientation.map (Fin 3)
          ((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
            (c'.toBallChart.chart x)).toLinearEquiv
          (M'.orientation.orientation (c'.toBallChart.chart x))
      = M.orientation.orientation (Φ.symm (c'.toBallChart.chart x)) :=
        hsymm (c'.toBallChart.chart x)
  have step5 : M.orientation.orientation (Φ.symm (c'.toBallChart.chart x))
      = M.orientation.orientation ((BallChart.pullback c'.toBallChart Φ).chart x) := by
        rw [BallChart.pullback_apply]
  exact step1.trans (step2.trans (step3.trans (step4.trans step5)))

end OrientationAssembly

theorem exists_orientedBallChart_pullback_of_preservesOrientation
    (hΦ : Φ.preservesOrientation M.orientation M'.orientation) :
    ∃ c : OrientedBallChart M,
      ∀ x ∈ Metric.closedBall (0 : csModel) 2,
        Φ (c.toBallChart.chart x) = c'.toBallChart.chart x :=
  ⟨{ toBallChart := BallChart.pullback c'.toBallChart Φ
     preserves_orientation :=
       OrientationAssembly.ballChart_pullback_preserves_orientation c' Φ hΦ },
    fun x _ => BallChart.map_pullback c'.toBallChart Φ x⟩

theorem orientedBallChartPullback : OrientedBallChartPullback.{u} :=
  fun Φ c' hΦ => exists_orientedBallChart_pullback_of_preservesOrientation c' Φ hΦ

end

end DifferentialGeometry.Topology
