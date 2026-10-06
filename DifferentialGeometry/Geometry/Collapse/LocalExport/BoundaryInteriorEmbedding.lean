import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorCompletion
import DifferentialGeometry.Topology.Manifold.ImmersionCriterionInteriorTarget

/-!
# G17: the inclusion of the interior `W°` is a smooth embedding into `W` (S-BAUG-D2)

`isSmoothEmbedding_val_interior_BAUGD`: the inclusion `W.pieceInterior ⊤ → W.Carrier` (interior
atlas, model `𝓡 3`, on the source; the carrier's own model `W.model` with corners on the target) is
a smooth embedding, and its values are interior points of `W.model`
(`isInteriorPoint_val_interior_BAUGD`).
These are the two inputs `hι`, `hιint` of `smoothProductChartAt_of_record_BAUGD` (and of the
circle version) for the actual boundary chain. Proof: the inclusion is a local diffeomorphism
(`isLocalDiffeomorph_pieceInterior_val`), so its differential is invertible, and the target values
are interior points (`isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

variable (W : CompactCarrier.{0})

/-- The values of the inclusion `W° → W` are interior points of the model with corners. -/
theorem isInteriorPoint_val_interior_BAUGD (x : W.pieceInterior ⊤) :
    W.model.IsInteriorPoint (x.val : W.Carrier) := by
  have hx : x.val ∈ W.model.interior W.Carrier := by
    rw [← coe_pieceInterior_top_BDRY1 W]
    exact x.property
  exact hx

/-- **The inclusion `W° → W` is a smooth embedding** (interior atlas on the source). -/
theorem isSmoothEmbedding_val_interior_BAUGD :
    IsSmoothEmbedding (𝓡 3) W.model ∞ (Subtype.val : W.pieceInterior ⊤ → W.Carrier) := by
  have hloc := isLocalDiffeomorph_pieceInterior_val W ⊤
  refine isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF
    (by simp) hloc.contMDiff Topology.IsEmbedding.subtypeVal (fun x => ?_)
    (fun x => isInteriorPoint_val_interior_BAUGD W x)
  have hinv := (hloc x).isInvertible_mfderiv (by simp)
  obtain ⟨e, he⟩ := hinv
  rw [← he]
  exact e.injective

end DifferentialGeometry.Geometry.Collapse
