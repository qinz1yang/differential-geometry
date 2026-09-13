import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransitionIsotopy
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarkingSupport

set_option autoImplicit false
noncomputable section
open Set Metric Filter Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ClosedOrientedManifold.{u} 3} {I : Type u} [Fintype I]

theorem BallMarking.isotopic_of_relative_transition_tube (B B' : BallMarking M I)
    (hover : ∀ i, ∀ x ∈ Metric.closedBall (0 : E3) 2,
      (B.ball i).chart x ∈ (B'.ball i).chart.target)
    (V : I → Set E3) (hVopen : ∀ i, IsOpen (V i))
    (hVsub : ∀ i, V i ⊆ (B'.ball i).chart.source)
    (hVψ : ∀ i, ∀ x ∈ Metric.closedBall (0 : E3) 2,
      (B'.ball i).chart.symm ((B.ball i).chart x) ∈ V i)
    (hVball : ∀ i, Metric.closedBall (0 : E3) 2 ⊆ V i)
    (hseg : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • (B'.ball i).chart.symm ((B.ball i).chart 0) + t • (0 : E3) ∈ V i)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint ((B'.ball i).chart '' V i) ((B'.ball j).chart '' V j))
    (havoid : ∀ i j, i ≠ j → ∀ x ∈ Metric.closedBall (0 : E3) 2,
      (B.ball i).chart x ∉ (B'.ball j).chart '' V j) :
    B.Isotopic B' := by
  have hdata : ∀ i, ∃ (J : ℝ → Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞)
      (K : Set E3),
      ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M.Carrier => J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : ℝ × M.Carrier => (J q.1).symm q.2) ∧
      J 0 = Diffeomorph.refl (𝓡 3) M.Carrier ∞ ∧
      IsCompact K ∧ K ⊆ V i ∧
      (∀ t x, x ∉ (B'.ball i).chart '' K → J t x = x ∧ (J t).symm x = x) ∧
      ∀ x ∈ Metric.closedBall (0 : E3) 2, J 1 ((B.ball i).chart x) = (B'.ball i).chart x :=
    fun i => exists_supported_isotopy_of_transition_tube (B.ball i) (B'.ball i) (hover i)
      (hVopen i) (hVsub i) (hVψ i) (hVball i) (hseg i)
  choose J K hJc hJi hJ0 hKc hKV hJfix hJ1 using hdata
  refine B.isotopic_of_supportFamily B' J (fun i => (B'.ball i).chart '' V i)
    hJc hJi hJ0 hdisj ?_ ?_ ?_
  · intro i t x hx
    exact hJfix i t x fun h => hx (Set.image_mono (hKV i) h)
  · intro i j hij x hx
    exact havoid i j hij x hx
  · intro i x hx
    exact hJ1 i x hx

theorem BallMarking.singleton_isotopic_of_affine (c : OrientedBallChart M) (s : E3) (r : ℝ)
    (hr : 0 < r) (hs : ‖s‖ + 2 * r ≤ 2) :
    (BallMarking.singleton c).Isotopic (BallMarking.singleton (c.affine s r hr hs)) :=
  BallMarking.isotopic_of_ballChartIsotopic _ _
    (i := PUnit.unit) (ballChartIsotopic_affine c s r hr hs)

theorem BallMarking.isotopic_of_transition_tube [Subsingleton I] (B B' : BallMarking M I)
    (i : I)
    (hover : ∀ x ∈ Metric.closedBall (0 : E3) 2, (B.ball i).chart x ∈ (B'.ball i).chart.target)
    {V : Set E3} (hVopen : IsOpen V) (hVsub : V ⊆ (B'.ball i).chart.source)
    (hVψ : ∀ x ∈ Metric.closedBall (0 : E3) 2, (B'.ball i).chart.symm ((B.ball i).chart x) ∈ V)
    (hVball : Metric.closedBall (0 : E3) 2 ⊆ V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • (B'.ball i).chart.symm ((B.ball i).chart 0) + t • (0 : E3) ∈ V) :
    B.Isotopic B' :=
  BallMarking.isotopic_of_ballChartIsotopic B B' (i := i)
    (ballChartIsotopic_of_transition_tube (B.ball i) (B'.ball i) hover hVopen hVsub hVψ
      hVball hseg)

theorem G_ball_of_relative_transition_tube
    (h : ∀ (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier] (I : Type u)
      [Fintype I] (B B' : BallMarking M I),
      (∀ i, ∀ x ∈ Metric.closedBall (0 : E3) 2,
        (B.ball i).chart x ∈ (B'.ball i).chart.target) ∧
      ∃ V : I → Set E3,
        (∀ i, IsOpen (V i)) ∧
        (∀ i, V i ⊆ (B'.ball i).chart.source) ∧
        (∀ i, ∀ x ∈ Metric.closedBall (0 : E3) 2,
          (B'.ball i).chart.symm ((B.ball i).chart x) ∈ V i) ∧
        (∀ i, Metric.closedBall (0 : E3) 2 ⊆ V i) ∧
        (∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
          (1 - t) • (B'.ball i).chart.symm ((B.ball i).chart 0) + t • (0 : E3) ∈ V i) ∧
        (∀ i j, i ≠ j →
          Disjoint ((B'.ball i).chart '' V i) ((B'.ball j).chart '' V j)) ∧
        ∀ i j, i ≠ j → ∀ x ∈ Metric.closedBall (0 : E3) 2,
          (B.ball i).chart x ∉ (B'.ball j).chart '' V j) :
    G_ball.{u} := by
  intro M _ I _ B B'
  obtain ⟨hover, V, hVopen, hVsub, hVψ, hVball, hseg, hdisj, havoid⟩ := h M I B B'
  exact B.isotopic_of_relative_transition_tube B' hover V hVopen hVsub hVψ hVball hseg
    hdisj havoid

end DifferentialGeometry.Topology
