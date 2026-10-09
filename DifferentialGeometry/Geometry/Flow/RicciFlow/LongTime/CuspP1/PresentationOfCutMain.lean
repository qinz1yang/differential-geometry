import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PresentationOfCutPieces
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PortAdapterGlue

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.Topology GC.Seifert Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- The torus presentation (of the closed component) built from a decomposition, through the tree's
`presentationOfWidth`; `externalCount = 0` by construction. -/
def dp_CPG {M : ConnectedClosedOrientedManifold.{u} 3} (D : TorusDecomposition M) :
    TorusDecomposition.DecompositionPresentation D :=
  D.decompositionPresentationOfWidth
    (Classical.choose (Classical.choose_spec D.exists_width))
    (Classical.choose_spec (Classical.choose_spec D.exists_width)).1
    (Classical.choose_spec (Classical.choose_spec D.exists_width)).2

theorem exists_lift_CPG {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : C(Z, Y)) (he : _root_.Topology.IsEmbedding e) (f : C(X, Y)) (hf : ∀ x, f x ∈ Set.range e) :
    ∃ ψ : C(X, Z), ∀ x, e (ψ x) = f x := by
  choose ψ hψ using hf
  have hc : Continuous ψ := he.continuous_iff.mpr (by
    have : e ∘ ψ = f := funext hψ
    rw [this]; exact f.continuous)
  exact ⟨⟨ψ, hc⟩, hψ⟩

theorem side_data_CPG (L : LateCutFamily F K slices) (j : ℕ)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (s0 : (dp_CPG (L.decomposition j C)).presentation.Side) :
    ∃ (j' : Fin (L.decomposition j C).boundary.count) (ν : Torus ≃ₜ Torus), ∀ t,
      (dp_CPG (L.decomposition j C)).presentation.cutMap
        ((dp_CPG (L.decomposition j C)).presentation.sideCollar s0 (t, halfZero)) =
      (L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction j' (ν t) := by
  rcases s0 with k | k | k
  · exact ⟨(dp_CPG (L.decomposition j C)).seamIndex.symm k, Homeomorph.refl _, fun t =>
      (dp_CPG (L.decomposition j C)).cutMap_leftCollar_zero k t⟩
  · refine ⟨(dp_CPG (L.decomposition j C)).seamIndex.symm k,
      ((L.decomposition j C).boundary.matching ((dp_CPG (L.decomposition j C)).seamIndex.symm k)).symm.toHomeomorph, fun t => ?_⟩
    rw [show (dp_CPG (L.decomposition j C)).presentation.sideCollar (.inr (.inl k)) (t, halfZero) =
      (dp_CPG (L.decomposition j C)).presentation.pairing.rightCollar k (t, halfZero) from rfl,
      (dp_CPG (L.decomposition j C)).cutMap_rightCollar_zero k t,
      (L.decomposition j C).reconstructionAtlas.torusInPrime_eq_comp_matching]
    simp
  · exact (Fin.cast (dp_CPG (L.decomposition j C)).presentation.externalCount_eq_zero k).elim0

end GC.LongTime.CuspP1
