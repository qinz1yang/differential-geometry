import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChartTransport
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedChartPullback
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport
import DifferentialGeometry.Topology.Manifold.SphereLinearIsometry

set_option autoImplicit false
noncomputable section
open Set Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u v

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

def connectedBallChartTransport : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3)
    (c c' : OrientedBallChart M.toClosedOrientedManifold),
    Manifold.BallChartTransport c.toBallChart c'.toBallChart

theorem orientedBallChartTransport_of_ballChartTransport
    {M : ConnectedClosedOrientedManifold.{u} 3}
    {M' : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (c' : OrientedBallChart M'.toClosedOrientedManifold)
    (h : Manifold.BallChartTransport c.toBallChart c'.toBallChart) :
    OrientedBallChartTransport c c' := by
  obtain ⟨Φ, hΦ⟩ := h
  have h0c : (0 : E3) ∈ c.toBallChart.chart.source :=
    c.toBallChart.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have h0c' : (0 : E3) ∈ c'.toBallChart.chart.source :=
    c'.toBallChart.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hEq : (fun x : E3 => Φ (c.toBallChart.chart x)) =ᶠ[𝓝 (0 : E3)]
      (fun x : E3 => c'.toBallChart.chart x) :=
    Filter.eventually_of_mem (Metric.closedBall_mem_nhds (0 : E3) (by norm_num)) hΦ
  have hchain : mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => Φ (c.toBallChart.chart x)) 0
      = mfderiv (𝓡 3) (𝓡 3) (⇑Φ) (c.toBallChart.chart 0)
        ∘L mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c.toBallChart.chart x) 0 :=
    mfderiv_comp (x := (0 : E3)) (f := fun x : E3 => c.toBallChart.chart x) (g := ⇑Φ)
      (Φ.mdifferentiable (by simp) _)
      (PartialDiffeomorph.mdifferentiableAt c.toBallChart.chart (by simp) h0c)
  have hkey : mfderiv (𝓡 3) (𝓡 3) (⇑Φ) (c.toBallChart.chart 0)
      ∘L mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c.toBallChart.chart x) 0
      = mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c'.toBallChart.chart x) 0 := by
    rw [← hchain, Filter.EventuallyEq.mfderiv_eq hEq]
    rfl
  have h3 : (OrientationAssembly.chartTangentEquiv c h0c).toLinearEquiv.trans
      ((Φ.mfderivToContinuousLinearEquiv (by simp) (c.toBallChart.chart 0)).toLinearEquiv)
      = (OrientationAssembly.chartTangentEquiv c' h0c').toLinearEquiv := by
    refine LinearEquiv.ext fun v => ?_
    simp only [LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
    exact DFunLike.congr_fun hkey v
  refine ⟨Φ, ?_, hΦ⟩
  refine Diffeomorph.preservesOrientation_of_eq_at Φ M.orientation M'.orientation
    (c.toBallChart.chart 0) ?_
  rw [hΦ 0 (Metric.mem_closedBall_self (by norm_num))]
  erw [OrientationAssembly.orientation_eq_map_chartTangentEquiv c h0c,
    OrientationAssembly.orientation_map_map_trans
      (OrientationAssembly.chartTangentEquiv c h0c).toLinearEquiv
      ((Φ.mfderivToContinuousLinearEquiv (by simp) (c.toBallChart.chart 0)).toLinearEquiv)
      (OrientationAssembly.stdOrientation 0),
    h3]
  exact (OrientationAssembly.orientation_eq_map_chartTangentEquiv c' h0c').symm

theorem selfTransport_of_connectedBallChartTransport (h : connectedBallChartTransport.{u}) :
    SelfTransport.{u} :=
  fun {M} c c' => orientedBallChartTransport_of_ballChartTransport c c' (h M c c')

def connectedSumUnorientedTransport : Prop :=
  ∀ (X X' Y Y' : ConnectedClosedOrientedManifold.{u} 3),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      X.toClosedOrientedManifold X'.toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      Y.toClosedOrientedManifold Y'.toClosedOrientedManifold) →
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (connectedSum X Y).Carrier
      (connectedSum X' Y').Carrier ∞)

def connectedSumOrientedTransport : Prop :=
  ∀ (X X' Y Y' : ConnectedClosedOrientedManifold.{u} 3),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      X.toClosedOrientedManifold X'.toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      Y.toClosedOrientedManifold Y'.toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Y).toClosedOrientedManifold
      (connectedSum X' Y').toClosedOrientedManifold)

def connectedSumOrientedChartTransport : Prop :=
  ∀ (X X' Y Y' : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart X.toClosedOrientedManifold)
    (c' : OrientedBallChart X'.toClosedOrientedManifold)
    (d : OrientedBallChart Y.toClosedOrientedManifold)
    (d' : OrientedBallChart Y'.toClosedOrientedManifold)
    (a : BoundaryAttachment)
    (Φ : X.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ X'.Carrier)
    (Ψ : Y.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Y'.Carrier),
    Φ.preservesOrientation X.orientation X'.orientation →
    Ψ.preservesOrientation Y.orientation Y'.orientation →
    (∀ x ∈ Metric.closedBall (0 : E3) 2,
      Φ (c.toBallChart.chart x) = c'.toBallChart.chart x) →
    (∀ x ∈ Metric.closedBall (0 : E3) 2,
      Ψ (d.toBallChart.chart x) = d'.toBallChart.chart x) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum X Y c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum X' Y' c' d' a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)

theorem connectedSum_unorientedTransport_of_selfTransport
    (h : SelfTransport.{u}) : connectedSumUnorientedTransport.{u} := by
  intro X X' Y Y' hX hY
  obtain ⟨Φ, hΦo⟩ := hX
  obtain ⟨Ψ, hΨo⟩ := hY
  obtain ⟨c, hc⟩ := orientedBallChartPullback Φ (orientedBallChart X') hΦo
  obtain ⟨d, hd⟩ := orientedBallChartPullback Ψ (orientedBallChart Y') hΨo
  obtain ⟨f⟩ := connectedSum_diffeomorph_of_ballChartTransport_left Y X X' c
    (orientedBallChart X') (h (orientedBallChart X) c).toBallChartTransport
    (Manifold.BallChartTransport.refl _) Φ hc
  obtain ⟨g⟩ := connectedSum_diffeomorph_of_ballChartTransport X' Y Y' d
    (orientedBallChart Y') (h (orientedBallChart Y) d).toBallChartTransport
    (Manifold.BallChartTransport.refl _) Ψ hd
  exact ⟨f.trans g⟩

theorem connectedSum_orientedTransport_of_selfTransport_and_orientedChartTransport
    (hself : SelfTransport.{u}) (h : connectedSumOrientedChartTransport.{u}) :
    connectedSumOrientedTransport.{u} := by
  intro X X' Y Y' hX hY
  obtain ⟨Φ, hΦo⟩ := hX
  obtain ⟨Ψ, hΨo⟩ := hY
  obtain ⟨c, hc⟩ := orientedBallChartPullback Φ (orientedBallChart X') hΦo
  obtain ⟨d, hd⟩ := orientedBallChartPullback Ψ (orientedBallChart Y') hΨo
  obtain ⟨Φc, hΦco, hΦc⟩ := hself (orientedBallChart X) c
  obtain ⟨Φd, hΦdo, hΦd⟩ := hself (orientedBallChart Y) d
  obtain ⟨f⟩ := h X X Y Y (orientedBallChart X) c (orientedBallChart Y) (orientedBallChart Y)
    boundaryAttachment Φc (Diffeomorph.refl (𝓡 3) Y.Carrier ∞) hΦco
    (Diffeomorph.preservesOrientation_refl Y.orientation) hΦc (fun _ _ => rfl)
  obtain ⟨f'⟩ := h X X Y Y c c (orientedBallChart Y) d boundaryAttachment
    (Diffeomorph.refl (𝓡 3) X.Carrier ∞) Φd
    (Diffeomorph.preservesOrientation_refl X.orientation) hΦdo (fun _ _ => rfl) hΦd
  obtain ⟨g⟩ := h X X' Y Y' c (orientedBallChart X') d (orientedBallChart Y')
    boundaryAttachment Φ Ψ hΦo hΨo hc hd
  exact ⟨f.trans (f'.trans g)⟩

end DifferentialGeometry.Topology
