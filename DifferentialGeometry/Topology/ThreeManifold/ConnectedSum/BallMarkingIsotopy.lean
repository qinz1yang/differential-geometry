import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarking
import DifferentialGeometry.Topology.Manifold.BallChartTransport

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

private abbrev E₃ := EuclideanSpace ℝ (Fin 3)

namespace BallMarking

variable {M : ClosedOrientedManifold.{u} 3} {I : Type u} [Fintype I] (B B' : BallMarking M I)

def Transport : Prop :=
  ∃ Φ : Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞,
    ∀ i, ∀ x ∈ Metric.closedBall (0 : E₃) 2, Φ ((B.ball i).chart x) = (B'.ball i).chart x

def Isotopic : Prop :=
  ∃ H : ℝ → Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞,
    ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M.Carrier => H q.1 q.2) ∧
    ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × M.Carrier => (H q.1).symm q.2) ∧
    H 0 = Diffeomorph.refl (𝓡 3) M.Carrier ∞ ∧
    ∀ i, ∀ x ∈ Metric.closedBall (0 : E₃) 2, H 1 ((B.ball i).chart x) = (B'.ball i).chart x

namespace Transport

theorem refl : B.Transport B :=
  ⟨Diffeomorph.refl (𝓡 3) M.Carrier ∞, fun _ _ _ => rfl⟩

end Transport

namespace Isotopic

theorem refl : B.Isotopic B :=
  ⟨fun _ => Diffeomorph.refl (𝓡 3) M.Carrier ∞, contMDiff_snd, contMDiff_snd, rfl,
    fun _ _ _ => rfl⟩

end Isotopic

theorem Isotopic.toTransport (h : B.Isotopic B') : B.Transport B' := by
  obtain ⟨H, -, -, -, hH⟩ := h
  exact ⟨H 1, hH⟩

theorem transport_to_ballChart (h : B.Transport B') (i : I) :
    Manifold.BallChartTransport (B.ball i).toBallChart (B'.ball i).toBallChart := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨Φ, hΦ i⟩

theorem transport_of_ballChartTransport [Subsingleton I] {i : I}
    (h : Manifold.BallChartTransport (B.ball i).toBallChart (B'.ball i).toBallChart) :
    B.Transport B' := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨Φ, fun j x hx => by rw [Subsingleton.elim j i]; exact hΦ x hx⟩

theorem transport_iff_ballChartTransport [Subsingleton I] (i : I) :
    B.Transport B' ↔
      Manifold.BallChartTransport (B.ball i).toBallChart (B'.ball i).toBallChart :=
  ⟨fun h => B.transport_to_ballChart B' h i, fun h => B.transport_of_ballChartTransport B' h⟩

theorem isotopic_to_ballChart (h : B.Isotopic B') (i : I) :
    Manifold.BallChartIsotopic (B.ball i).toBallChart (B'.ball i).toBallChart := by
  obtain ⟨H, hH, hHi, hH0, hH1⟩ := h
  exact ⟨H, hH, hHi, hH0, hH1 i⟩

theorem isotopic_of_ballChartIsotopic [Subsingleton I] {i : I}
    (h : Manifold.BallChartIsotopic (B.ball i).toBallChart (B'.ball i).toBallChart) :
    B.Isotopic B' := by
  obtain ⟨H, hH, hHi, hH0, hH1⟩ := h
  exact ⟨H, hH, hHi, hH0, fun j x hx => by rw [Subsingleton.elim j i]; exact hH1 x hx⟩

theorem isotopic_iff_ballChartIsotopic [Subsingleton I] (i : I) :
    B.Isotopic B' ↔
      Manifold.BallChartIsotopic (B.ball i).toBallChart (B'.ball i).toBallChart :=
  ⟨fun h => B.isotopic_to_ballChart B' h i, fun h => B.isotopic_of_ballChartIsotopic B' h⟩

end BallMarking

def G_ball : Prop :=
  ∀ (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier] (I : Type u) [Fintype I]
    (B B' : BallMarking M I), B.Isotopic B'

theorem G_ball_isotopic_refl (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier]
    (I : Type u) [Fintype I] (B : BallMarking M I) : B.Isotopic B :=
  BallMarking.Isotopic.refl B

theorem G_ball_iff_ballChartIsotopic_single (M : ClosedOrientedManifold.{u} 3)
    [ConnectedSpace M.Carrier] :
    (∀ B B' : BallMarking M PUnit, B.Isotopic B') ↔
      ∀ c c' : OrientedBallChart M,
        Manifold.BallChartIsotopic c.toBallChart c'.toBallChart := by
  constructor
  · intro h c c'
    have hc := h (BallMarking.singleton c) (BallMarking.singleton c')
    exact BallMarking.isotopic_to_ballChart _ _ hc PUnit.unit
  · intro h B B'
    exact BallMarking.isotopic_of_ballChartIsotopic B B'
      (h (B.ball PUnit.unit) (B'.ball PUnit.unit))

end DifferentialGeometry.Topology
