import DifferentialGeometry.Topology.Engulfing.Local.Obstacle.LocalObstacleAttachmentPreparation
import DifferentialGeometry.Topology.Engulfing.Newman.Inner.NewmanInnerIteration
import DifferentialGeometry.Topology.Engulfing.Newman.Membrane.NewmanRefinementTransport

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E M : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] {n p q : ℕ} {K L : SimplicialComplex ℝ E}
  {g : C(K.space, M)} {X U : Set M} {b : AdaptedPiecewiseLinearChart K L g X n p}
  {C : Set E} {V : Finset E} {ε η : ℝ}

theorem LocalObstacleAttachmentPreparation.exists_conclusion
    (P : LocalObstacleAttachmentPreparation K L g b C V U p q ε)
    (inner : NewmanInnerModel P.model.source (P.chartSetup.pullbackFixed P.model) P.covered
      (P.chartSetup.pullbackMap P.model) X P.chartSetup.approximation.totalRawMap P.active.space p)
    (hlower : relativeNewmanAt M n p q) (hqp : q ≤ p)
    (hX : IsClosed X) (hU : IsOpen U) (hp : p + 3 ≤ n)
    (hconn : NewmanConnectivity M U p) (hdata : hasAdaptedPiecewiseLinearCharts K L g X n p)
    (hfixed : InjOn g (Subtype.val ⁻¹' L.space)) (hη : 0 < η) :
    ∃ (g' : C(K.space, M)) (G : M ≃ₜ M),
      (∀ x : K.space, x.val ∈ L.space → g' x = g x) ∧
      (∀ x, dist (g' x) (g x) < ε + η) ∧
      X ∪ g' '' (Subtype.val ⁻¹' (C ∪
        (convexHull ℝ (V : Set E) ∩ (skeleton K q).space))) ⊆ G '' U ∧
      IsCompact (closure {x | G x ≠ x}) := by
  let S := P.chartSetup
  let m := P.model
  obtain ⟨f, G, -, hfix, hnear, hcover, hcompact⟩ :=
    inner.exists_engulfing hlower hqp m.finite_faces (S.pullbackFixed_faces m)
      P.covered_faces m.dimension P.covered_dimension hX hp
      (S.pullbackMap_hasAdaptedPiecewiseLinearCharts m hdata) (S.pullbackMap_injOn_fixed m hfixed)
      hU hconn P.covered_image (.of_faces_subset P.active_faces)
      P.active_dimension P.expansion hη
  have hspace : m.source.space = K.space := m.space.trans S.space
  have href : simplicialRefines m.source K := m.refines.trans S.refines
  have htarget : C ∪ (convexHull ℝ (V : Set E) ∩ (skeleton K q).space) ⊆
      P.covered.space ∪ (P.active.space ∩ (skeleton m.source q).space) := by
    rw [P.covered_space, P.active_space]
    exact union_subset_union_right C
      (inter_subset_inter_right _ (href.old_skeleton_subset hspace q))
  obtain ⟨g', hgfix, hgnear, hgcover, -⟩ := exists_map_on_equal_space_of_target_subset
    K L m.source (S.pullbackFixed m) hspace (S.pullbackFixed_space m) g f htarget
    (fun x hx => (hfix hx).trans (S.pullbackMap_fixed m x
      ((S.pullbackFixed_space m).subset hx)))
    (fun x => show dist (f x) (g (Homeomorph.setCongr hspace x)) < ε + η from by
      calc
        dist (f x) (g (Homeomorph.setCongr hspace x)) ≤
            dist (f x) (S.pullbackMap m x) +
              dist (S.pullbackMap m x) (g (Homeomorph.setCongr hspace x)) := dist_triangle _ _ _
        _ < η + ε := add_lt_add (hnear x) (S.pullbackMap_near m x)
        _ = ε + η := add_comm _ _)
    hcover
  exact ⟨g', G, hgfix, hgnear, hgcover, hcompact⟩

end DifferentialGeometry.Topology.Engulfing
