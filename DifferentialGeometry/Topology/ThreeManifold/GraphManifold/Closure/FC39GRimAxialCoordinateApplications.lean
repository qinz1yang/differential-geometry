import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimAxialCoordinate
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Edges

/-!
# FC39 GROUP G, RIMBOX route B: consumer of the axial coordinate

Lane FC39-G-RIMBOX. Every interval component of the edge component export has an axial coordinate:
for `M : EdgeComponentModels P` and an interval index `i`, a smooth regular injective `φ` on an open
`V ⊇ range (intervalBase i)` of the edge base with `φ (intervalBase i t) = t`, margin `(-ε, 1 + ε)`
and compact preimages — the `P = φ ∘ proj` input of the flow handle.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

/-- **The two-sided axial coordinate of an interval component of the edge base** (D62-6 G4, first part). -/
theorem EdgeComponentModels.exists_intervalBase_twoSidedCoordinate_GRIM {P : EdgeBundle W}
    (M : EdgeComponentModels P) (i : Fin M.intervalCount) :
    ∃ (V : Set P.Base) (φ : P.Base → ℝ) (ε : ℝ), IsOpen V ∧ 0 < ε ∧
      range (M.intervalBase i) ⊆ V ∧ ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ V ∧
      (∀ t, φ (M.intervalBase i t) = t) ∧ InjOn φ V ∧
      (∀ c ∈ V, Surjective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c)) ∧
      φ '' V = Ioo (-ε) (1 + ε) ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-ε) (1 + ε) → IsCompact (V ∩ φ ⁻¹' K) :=
  GC.GraphManifold.Assembly.FC39P0.exists_axialCoordinate_GRIM (M.intervalBase i) (M.intervalBase_embedding i).contMDiff
    (M.intervalBase_embedding i).isEmbedding.injective
    (fun t => (M.intervalBase_embedding i).isImmersion.mfderiv_injective (by simp) t)

end GC.GraphManifold.Assembly.FC39P0
