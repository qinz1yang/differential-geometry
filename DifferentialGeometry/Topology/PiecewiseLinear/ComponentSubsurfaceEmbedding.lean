/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TorusSubsurfaceEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphComponents
import DifferentialGeometry.Topology.PiecewiseLinear.CircleCappingComponentInvariants

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def HasEssentialBoundaryPLEmbeddings [DecidableEq E3]
    (K : Geometry.SimplicialComplex ℝ E3) (T : Set E3) : Prop :=
  ∀ (c : ConnectedComponents K.space) (H : Set E3), IsPLSphere 1 H →
    H ⊆ (boundaryComplex 2 (connectedComponentComplex K c)).space → ¬ boundsDiskIn H T →
      HasBoundaryFixedPLEmbedding 2 (connectedComponentComplex K c) T

theorem HasEssentialBoundaryPLEmbeddings.of_subset [DecidableEq E3]
    (K : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] {T : Set E3} (hKT : K.space ⊆ T) :
    HasEssentialBoundaryPLEmbeddings K T := by
  intro c _ _ _ _
  let _ : Finite (connectedComponentComplex K c).faces :=
    (connectedComponentComplex_faces_finite K c).to_subtype
  apply HasBoundaryFixedPLEmbedding.of_subset 2
  exact ((subset_iUnion (fun d => (connectedComponentComplex K d).space) c).trans
    (iUnion_connectedComponentComplex_space K).subset).trans hKT

theorem HasEssentialBoundaryPLEmbeddings.of_isPLHomeomorphOn [d : DecidableEq E3]
    (K Q : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] [Finite Q.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {T : Set E3}
    (h : HasEssentialBoundaryPLEmbeddings K T) {f : E3 → E3}
    (hf : IsPLHomeomorphOn f K.space Q.space) (hfix : EqOn f id (boundaryComplex 2 K).space) :
    HasEssentialBoundaryPLEmbeddings Q T := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  let _ (c : ConnectedComponents K.space) : Finite (connectedComponentComplex K c).faces :=
    (connectedComponentComplex_faces_finite K c).to_subtype
  let _ (c : ConnectedComponents Q.space) : Finite (connectedComponentComplex Q c).faces :=
    (connectedComponentComplex_faces_finite Q c).to_subtype
  obtain ⟨e, he⟩ := hf.exists_component_equiv K Q
  intro q H hH hHQ hess
  obtain ⟨c, rfl⟩ := e.surjective q
  have hfixed : EqOn f id (boundaryComplex 2 (connectedComponentComplex K c)).space := by
    rw [boundaryComplex_space_connectedComponentComplex]
    exact hfix.mono inter_subset_left
  have hbd : (boundaryComplex 2 (connectedComponentComplex Q (e c))).space =
      (boundaryComplex 2 (connectedComponentComplex K c)).space := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn (connectedComponentComplex K c)
      (connectedComponentComplex Q (e c)) (hK.connectedComponentComplex c) (he c)]
    simpa only [image_id] using hfixed.image_eq
  exact (h c H hH (hHQ.trans hbd.subset) hess).of_isPLHomeomorphOn (he c) hbd hfixed

theorem HasEssentialBoundaryPLEmbeddings.of_circle_capping [d : DecidableEq E3]
    (K Q : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] [Finite Q.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hQ : IsCombinatorialManifoldWithBoundary 2 Q) {T Θ : Set E3} (hΘ : IsPLTorus Θ)
    (h : HasEssentialBoundaryPLEmbeddings K Θ)
    (hcap : IsCircleCapping K.space Q.space T (boundaryComplex 2 K).space)
    (hnull : ∀ (c : ConnectedComponents K.space) (G : Set E3),
      G ∈ traceCircles (connectedComponentComplex K c).space T →
        boundsDiskIn G T → boundsDiskIn G Θ) : HasEssentialBoundaryPLEmbeddings Q Θ := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  let _ (c : ConnectedComponents K.space) : Finite (connectedComponentComplex K c).faces :=
    (connectedComponentComplex_faces_finite K c).to_subtype
  let _ (c : ConnectedComponents Q.space) : Finite (connectedComponentComplex Q c).faces :=
    (connectedComponentComplex_faces_finite Q c).to_subtype
  obtain ⟨c₀, e, hcap₀, hother, -, -⟩ := hcap.exists_component_capping K Q
  intro q H hH hHQ hess
  obtain ⟨c, rfl⟩ := e.surjective q
  by_cases hc : c = c₀
  · subst c
    have hcapC : IsCircleCapping (connectedComponentComplex K c₀).space
        (connectedComponentComplex Q (e c₀)).space T
        (boundaryComplex 2 (connectedComponentComplex K c₀)).space := by
      rw [boundaryComplex_space_connectedComponentComplex]
      exact hcap₀
    obtain ⟨Δ, r, f, -, -, -, -, -, -, -, hbd⟩ :=
      hcapC.exists_boundary_preserving_map (connectedComponentComplex K c₀)
        (connectedComponentComplex Q (e c₀)) (hK.connectedComponentComplex c₀)
    have hHK : H ⊆ (boundaryComplex 2 (connectedComponentComplex K c₀)).space :=
      fun x hx => (hbd.subset (hHQ hx)).1
    exact (h c₀ H hH hHK hess).of_circle_capping (connectedComponentComplex K c₀)
      (connectedComponentComplex Q (e c₀)) (hK.connectedComponentComplex c₀)
      (isConnected_connectedComponentComplex_space K c₀) (hQ.connectedComponentComplex (e c₀))
      (isConnected_connectedComponentComplex_space Q (e c₀)) hΘ hcapC (hnull c₀) hH hHQ hess
  · obtain ⟨f, hf, hfix⟩ := hother c hc
    have hfixed : EqOn f id (boundaryComplex 2 (connectedComponentComplex K c)).space := by
      rw [boundaryComplex_space_connectedComponentComplex]
      exact hfix
    have hbd : (boundaryComplex 2 (connectedComponentComplex Q (e c))).space =
        (boundaryComplex 2 (connectedComponentComplex K c)).space := by
      rw [boundaryComplex_space_of_isPLHomeomorphOn (connectedComponentComplex K c)
        (connectedComponentComplex Q (e c)) (hK.connectedComponentComplex c) hf]
      simpa only [image_id] using hfixed.image_eq
    exact (h c H hH (hHQ.trans hbd.subset) hess).of_isPLHomeomorphOn hf hbd hfixed

end DifferentialGeometry.Topology.PiecewiseLinear
