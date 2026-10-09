import DifferentialGeometry.Geometry.Thurston.StandardFactorGeometry
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscarded

namespace GC.Topology
open DifferentialGeometry.Topology
open scoped Manifold ContDiff
set_option autoImplicit false
noncomputable section
universe u

def nonemptyStandardFactors : List (ConnectedClosedOrientedManifold.{u} 3) →
    List (ConnectedClosedOrientedManifold.{u} 3)
  | [] => [standardThreeSphereLift]
  | F :: L => F :: L

def nonemptyStandardPresentation
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (P : PoincareStandardPresentation M) : PoincareStandardPresentation M := by
  rcases P with ⟨L, h, f⟩
  cases L with
  | nil =>
    exact ⟨[standardThreeSphereLift], by
      intro F hF
      simpa only [List.mem_singleton.mp hF] using isStandardFactor_standardThreeSphereLift,
      f⟩
  | cons F L => exact ⟨F :: L, h, f⟩

theorem nonemptyStandardPresentation_properties
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (P : PoincareStandardPresentation M) :
    (nonemptyStandardPresentation P).factors = nonemptyStandardFactors P.factors ∧
    (nonemptyStandardPresentation P).factors ≠ [] ∧
    HEq (nonemptyStandardPresentation P).diffeomorph P.diffeomorph := by
  rcases P with ⟨L,h,f⟩
  cases L <;> exact ⟨rfl, List.cons_ne_nil _ _, HEq.rfl⟩

end
end GC.Topology

namespace GC.Geometry
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
set_option autoImplicit false
noncomputable section
universe u

structure StandardGeometricPresentation (M : ClosedOrientedManifold.{u} 3) where
  presentation : OrientedPoincareStandardPresentation M
  factors_nonempty : presentation.factors ≠ []
  model : Fin presentation.factors.length → ElementaryModel
  metric : (i : Fin presentation.factors.length) →
    SmoothRiemannianMetric (𝓡 3) (presentation.factors.get i).Carrier
  geometry : ∀ i, ElementaryGeometry (metric i) (model i)

theorem standard_geometric_presentation
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (P : PoincareStandardPresentation M.Carrier) :
    ∃ G : StandardGeometricPresentation M.toClosedOrientedManifold,
      G.presentation.factors = GC.Topology.nonemptyStandardFactors P.factors ∨
      G.presentation.factors = (GC.Topology.nonemptyStandardFactors P.factors).map
        ConnectedClosedOrientedManifold.opposite := by
  classical
  obtain ⟨hlist,hnonempty,hmap⟩ := GC.Topology.nonemptyStandardPresentation_properties P
  obtain ⟨Q,hQ,hg⟩ := oriented_standard_presentation_geometry M
    (GC.Topology.nonemptyStandardPresentation P)
  have hne : Q.factors ≠ [] := by
    rcases hQ with h | h
    · simpa only [h] using hnonempty
    · intro hn
      apply hnonempty
      exact List.map_eq_nil_iff.mp (h.symm.trans hn)
  choose tag g hgeometry using hg
  refine ⟨⟨Q,hne,tag,g,hgeometry⟩, ?_⟩
  simpa only [hlist] using hQ

theorem StandardGeometricPresentation.factor_index_nonempty
    {M : ClosedOrientedManifold.{u} 3} (G : StandardGeometricPresentation M) :
    Nonempty (Fin G.presentation.factors.length) := by
  exact Fin.pos_iff_nonempty.mp (List.length_pos_iff.mpr G.factors_nonempty)

def StandardGeometricPresentation.pullback
    {M N : ClosedOrientedManifold.{u} 3}
    (G : StandardGeometricPresentation N)
    (f : ClosedOrientedManifold.OrientedDiffeomorph M N) :
    StandardGeometricPresentation M where
  presentation := ⟨G.presentation.factors,G.presentation.standard,
    f.trans G.presentation.diffeomorph⟩
  factors_nonempty := G.factors_nonempty
  model := G.model
  metric := G.metric
  geometry := G.geometry

theorem StandardGeometricPresentation.pullback_data
    {M N : ClosedOrientedManifold.{u} 3}
    (G : StandardGeometricPresentation N)
    (f : ClosedOrientedManifold.OrientedDiffeomorph M N) :
    (G.pullback f).presentation.factors = G.presentation.factors ∧
    (G.pullback f).presentation.diffeomorph = f.trans G.presentation.diffeomorph ∧
    (G.pullback f).model = G.model ∧
    (G.pullback f).metric = G.metric := ⟨rfl,rfl,rfl,rfl⟩

theorem sphere_unit_geometric_presentation :
    ∃ G : StandardGeometricPresentation standardThreeSphereLift.{u}.toClosedOrientedManifold,
      G.presentation.factors = [standardThreeSphereLift] ∨
      G.presentation.factors = [standardThreeSphereLift.opposite] := by
  let P : PoincareStandardPresentation standardThreeSphereLift.{u}.Carrier :=
    ⟨[],by simp,Diffeomorph.refl _ _ ∞⟩
  exact standard_geometric_presentation standardThreeSphereLift P

end
end GC.Geometry
