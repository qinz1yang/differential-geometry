import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimEdgeSlab
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimAxialCoordinateApplications
import DifferentialGeometry.Topology.Ehresmann.SideBoundaryIntervalPreserving

/-!
# FC39 GROUP G, RIMBOX route B: consumer of the edge slab (the gate G4 passed)

Lane FC39-G-RIMBOX. For every interval component of the edge export, the side-boundary transport
runs on its edge slab: with the two-sided axial coordinate (`exists_intervalBase_twoSidedCoordinate_GRIM`)
and the transport hypotheses (`edgeSlab_transportHypotheses_GRIM`), the theorem
`exists_sideBoundary_interval_trivialization_preserving` yields the flow `Fl` with `g (Fl t z) = t`
from the `g = 0` slice (also beyond the wall, `B z ≥ −r'`) for the TWO-SIDED time window
`(−ε/2, 1 + ε/2)` and `B` kept on `{|B| < r'}` (D62-3 (a)).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Ehresmann
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

/-- **The transport flow on the edge slab of an interval component.** -/
theorem EdgeComponentModels.exists_edgeSlabFlow_GRIM {P : EdgeBundle W}
    (M : EdgeComponentModels P) (i : Fin M.intervalCount) :
    ∃ (V : Set P.Base) (hV : IsOpen V) (φ : P.Base → ℝ) (ε : ℝ), 0 < ε ∧
      range (M.intervalBase i) ⊆ V ∧ (∀ t, φ (M.intervalBase i t) = t) ∧
      let _ := DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞
        (M := W.pieceInterior (edgeSlab_GRIM P V hV))
      ∃ (r' : ℝ) (U : TopologicalSpace.Opens (W.pieceInterior (edgeSlab_GRIM P V hV)))
        (Fl : ℝ → U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 3)), 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ U),
        0 < r' ∧
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
          (fun q : ℝ × U => Fl q.1 q.2) ∧
        Fl 0 = Diffeomorph.refl _ U ∞ ∧ (∀ s t, (Fl s).trans (Fl t) = Fl (s + t)) ∧
        (∀ z : U, φ (P.proj (edgeSlabIncl_GRIM P V hV z)) = 0 →
          -r' ≤ P.level - P.height (edgeSlabIncl_GRIM P V hV z) →
          ∀ t ∈ Ioo (-(ε / 2)) (1 + ε / 2),
            φ (P.proj (edgeSlabIncl_GRIM P V hV (Fl t z))) = t) ∧
        ∀ (z : U) (t : ℝ), |P.level - P.height (edgeSlabIncl_GRIM P V hV z)| < r' →
          P.level - P.height (edgeSlabIncl_GRIM P V hV (Fl t z)) =
            P.level - P.height (edgeSlabIncl_GRIM P V hV z) := by
  obtain ⟨V, φ, ε, hV, hε, hrange, hφ, hφβ, -, hφs, -, hK⟩ :=
    M.exists_intervalBase_twoSidedCoordinate_GRIM i
  refine ⟨V, hV, φ, ε, hε, hrange, hφβ, ?_⟩
  intro _
  have _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (W.pieceInterior (edgeSlab_GRIM P V hV)) :=
    DifferentialGeometry.Manifold.interiorIsManifold W.model ∞
  obtain ⟨hP, hB, hreg, hregb, hprop⟩ :=
    edgeSlab_transportHypotheses_GRIM P hV hφ hφs hK
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 1 + 1 + Module.finrank ℝ ℝ := by
    simp
  obtain ⟨Θ, -, -, -, -, ⟨r', hr', -, U, hU, Fl, hFl, hFl0, hFlgrp, -, hFlP, hFlB⟩, -⟩ :=
    exists_sideBoundary_interval_trivialization_preserving hdim hP hB (a := -ε) (b := 1 + ε)
      (fun y _ _ => hreg y) (fun y _ hy => hregb y hy) hprop
      (show -ε < -(ε / 2) by linarith) (show (0 : ℝ) ∈ Ioo (-(ε / 2)) (1 + ε / 2) by
        constructor <;> linarith) (show 1 + ε / 2 < 1 + ε by linarith)
  exact ⟨r', ⟨U, hU⟩, Fl, hr', hFl, hFl0, hFlgrp, hFlP, hFlB⟩

end GC.GraphManifold.Assembly.FC39P0
