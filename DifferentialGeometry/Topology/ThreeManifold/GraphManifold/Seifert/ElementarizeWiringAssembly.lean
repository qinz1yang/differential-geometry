import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringRefinement

/-!
# `ElementarizeOnSubCollar` for orientable bases, and the Möbius branch

Lane P1W (P1 wiring), tiers T3 and T4.

T3. For a raw graph presentation all of whose pieces have orientable bases, the component
refinements of `exists_componentRefinement_of_orientable` for one common `δ` (the minimum over the
components, capped at `1`) form a `PieceRefinement` of `(G.toTorusPresentation.reparam id).shrink δ`
(`exists_pieceRefinement_of_orientable`). So `elementarizeOnSubCollar_of_pieceRefinement` gives
`ElementarizeOnSubCollar` when every base is orientable
(`elementarizeOnSubCollar_of_orientable`), and every such presentation alone has the clause of
`ElementarizeOnSubCollar` (`elementarizeOnSubCollar_rawGraph_of_orientable`, through the
straightening `ElementaryPresentation.exists_transport_subCollar`).

T4. The general statement is reduced to the pieces with a non-orientable base: if every component
with a non-orientable base has component refinements of `(G.toTorusPresentation.reparam id).shrink
δ` for all small `δ`, then `ElementarizeOnSubCollar` holds
(`elementarizeOnSubCollar_of_nonorientable`). The hypothesis is about those components only; the
orientable ones are discharged by T2.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.Wiring

variable {W : CompactCarrier.{u}}

theorem exists_pieceRefinement_of_components (G : RawGraphPresentation W)
    (h : ∀ i : Fin G.components.count, ∃ δ₀ > 0, ∀ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1), δ ≤ δ₀ →
      Nonempty (((G.toTorusPresentation.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink
        hδ hδ1).ComponentRefinement i)) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
      Nonempty (((G.toTorusPresentation.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink
        hδ hδ1).PieceRefinement) := by
  choose δ₀ hδ₀ hR using h
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_finite δ₀ hδ₀
  exact ⟨min m 1, lt_min hm one_pos, min_le_right _ _,
    ⟨TorusPresentation.PieceRefinement.ofComponents _ fun i =>
      (hR i (min m 1) (lt_min hm one_pos) (min_le_right _ _)
        ((min_le_left _ _).trans (hmle i))).some⟩⟩

theorem exists_pieceRefinement_of_orientable (G : RawGraphPresentation W)
    (o : ∀ i, ManifoldOrientation (SurfaceModel.model (G.fibration i).base.kind)
      (G.fibration i).base.Carrier 2) :
    ∃ (ψ : G.toTorusPresentation.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) (δ : ℝ)
      (hδ : 0 < δ) (hδ1 : δ ≤ 1),
      Nonempty ((G.toTorusPresentation.reparam ψ).shrink hδ hδ1).PieceRefinement := by
  obtain ⟨δ, hδ, hδ1, hR⟩ := exists_pieceRefinement_of_components G fun i =>
    exists_componentRefinement_of_orientable G i (o i)
  exact ⟨_, δ, hδ, hδ1, hR⟩

theorem elementarizeOnSubCollar_rawGraph_of_pieceRefinement (G : RawGraphPresentation W)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ((G.toTorusPresentation.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink
      hδ hδ1).PieceRefinement) :
    ∃ E : ElementaryPresentation W, ∃ h : E.toTorus.externalCount = G.externalCount,
      ∃ ψ : Fin G.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus), ∃ δ' > (0 : ℝ),
        ∀ i p, p ∈ halfCollarSource → p.2.val 0 < δ' →
          E.toTorus.external.collar (Fin.cast h.symm i) p = G.external.collar i (ψ i p.1, p.2) := by
  have hc : R.toProductRefinement.toElementaryPresentation.toTorus.externalCount =
      G.externalCount := R.toProductRefinement.toElementaryPresentation_externalCount
  have h₀ : ∀ i t, R.toProductRefinement.toElementaryPresentation.toTorus.external.collar
      (Fin.cast hc.symm i) (t, halfZero) =
        G.external.collar i (Diffeomorph.refl torusModel Torus ∞ t, halfZero) := fun i t =>
    (R.toProductRefinement.toElementaryPresentation_external_collar _
      (zero_mem_halfCollarSource t)).trans
      ((congrFun (BoundaryTori.shrink_torusMap
        (G.toTorusPresentation.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).external
          hδ hδ1 i) t).trans rfl)
  obtain ⟨δ', hδ', Φ, hΦ, hagree⟩ :=
    R.toProductRefinement.toElementaryPresentation.exists_transport_subCollar G.external hc _ h₀
  exact ⟨R.toProductRefinement.toElementaryPresentation.transport Φ hΦ, hc,
    fun _ => Diffeomorph.refl torusModel Torus ∞, δ', hδ', hagree⟩

theorem elementarizeOnSubCollar_rawGraph_of_orientable (G : RawGraphPresentation W)
    (o : ∀ i, ManifoldOrientation (SurfaceModel.model (G.fibration i).base.kind)
      (G.fibration i).base.Carrier 2) :
    ∃ E : ElementaryPresentation W, ∃ h : E.toTorus.externalCount = G.externalCount,
      ∃ ψ : Fin G.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus), ∃ δ > (0 : ℝ),
        ∀ i p, p ∈ halfCollarSource → p.2.val 0 < δ →
          E.toTorus.external.collar (Fin.cast h.symm i) p = G.external.collar i (ψ i p.1, p.2) := by
  obtain ⟨δ, hδ, hδ1, ⟨R⟩⟩ := exists_pieceRefinement_of_components G fun i =>
    exists_componentRefinement_of_orientable G i (o i)
  exact elementarizeOnSubCollar_rawGraph_of_pieceRefinement G hδ hδ1 R

theorem elementarizeOnSubCollar_of_orientable
    (ho : ∀ (W : CompactCarrier.{u}) (G : RawGraphPresentation W) (i : Fin G.components.count),
      Nonempty (ManifoldOrientation (SurfaceModel.model (G.fibration i).base.kind)
        (G.fibration i).base.Carrier 2)) :
    ElementarizeOnSubCollar.{u} :=
  elementarizeOnSubCollar_of_pieceRefinement fun _ G =>
    exists_pieceRefinement_of_orientable G fun i => (ho _ G i).some

theorem elementarizeOnSubCollar_of_nonorientable
    (hnon : ∀ (W : CompactCarrier.{u}) (G : RawGraphPresentation W) (i : Fin G.components.count),
      IsEmpty (ManifoldOrientation (SurfaceModel.model (G.fibration i).base.kind)
        (G.fibration i).base.Carrier 2) →
      ∃ δ₀ > 0, ∀ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1), δ ≤ δ₀ →
        Nonempty (((G.toTorusPresentation.reparam fun _ =>
          Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1).ComponentRefinement i)) :
    ElementarizeOnSubCollar.{u} := by
  refine elementarizeOnSubCollar_of_pieceRefinement fun W G => ?_
  obtain ⟨δ, hδ, hδ1, hR⟩ := exists_pieceRefinement_of_components G fun i => by
    rcases isEmpty_or_nonempty (ManifoldOrientation (SurfaceModel.model (G.fibration i).base.kind)
      (G.fibration i).base.Carrier 2) with h | h
    · exact hnon W G i h
    · exact exists_componentRefinement_of_orientable G i h.some
  exact ⟨_, δ, hδ, hδ1, hR⟩

end GC.Seifert.Wiring
