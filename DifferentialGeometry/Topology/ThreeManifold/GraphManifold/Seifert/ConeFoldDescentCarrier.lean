import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentMap
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Interior
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Coordinates
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

/-!
# The interior of the filled carrier as a target of the descent

`descentCarrier c` is the filled carrier of `c` wrapped in a definition, so that the interior
instances of `CompactCarrier` are found syntactically. A point of the carrier is a point of
`filledSet ⊆ PlaneLift × S¹` (`carrierVal`); it lies in the interior `pieceInterior ⊤` exactly
when `filledFunction (conePoint x) < 0` (`mem_pieceInterior_iff`), and points of `PlaneLift × S¹`
with this property define interior points (`toDescentInterior`). The inclusion `descentIncl` of the
interior, read in the interior atlas (model `𝓡 3`), is a local diffeomorphism onto an open subset
of `PlaneLift × S¹` (`isLocalDiffeomorph_descentIncl`) and a topological embedding
(`isInducing_descentIncl`).
-/

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

def descentCarrier (c : ConeFilling) : CompactCarrier.{u} := c.filledCarrier

namespace ConeFilling

variable (c : ConeFilling)

def carrierVal (x : (descentCarrier.{u} c).Carrier) : PlaneLift.{u} × Circle :=
  Subtype.val (show c.filledSet.{u} from x)

theorem mem_pieceInterior_iff (x : (descentCarrier.{u} c).Carrier) :
    x ∈ (descentCarrier.{u} c).pieceInterior ⊤ ↔
      ConeFilling.filledFunction (c.conePoint (c.carrierVal x)) < 0 := by
  change (True ∧ (𝓡∂ 3).IsInteriorPoint (show c.filledSet.{u} from x)) ↔ _
  rw [true_and]
  exact c.filledSet_isInteriorPoint_iff _

def toDescentInterior {x : PlaneLift.{u} × Circle}
    (hx : ConeFilling.filledFunction (c.conePoint x) < 0) :
    (descentCarrier.{u} c).pieceInterior ⊤ :=
  ⟨show c.filledSet.{u} from ⟨x, hx.le⟩, (c.mem_pieceInterior_iff _).2 hx⟩

def descentIncl (y : (descentCarrier.{u} c).pieceInterior ⊤) : PlaneLift.{u} × Circle :=
  c.carrierVal y

theorem descentIncl_toDescentInterior {x : PlaneLift.{u} × Circle}
    (hx : ConeFilling.filledFunction (c.conePoint x) < 0) :
    c.descentIncl (c.toDescentInterior hx) = x :=
  rfl

theorem filledFunction_descentIncl (y : (descentCarrier.{u} c).pieceInterior ⊤) :
    ConeFilling.filledFunction (c.conePoint (c.descentIncl y)) < 0 :=
  (c.mem_pieceInterior_iff _).1 y.2

theorem descentIncl_injective : Function.Injective c.descentIncl.{u} := by
  intro y y' h
  exact Subtype.ext (Subtype.ext h)

theorem toDescentInterior_descentIncl (y : (descentCarrier.{u} c).pieceInterior ⊤) :
    c.toDescentInterior (c.filledFunction_descentIncl y) = y :=
  c.descentIncl_injective rfl

theorem isInducing_descentIncl : Topology.IsInducing c.descentIncl.{u} :=
  (Topology.IsInducing.subtypeVal (t := c.filledSet.{u})).comp
    (Topology.IsInducing.subtypeVal
      (t := ((descentCarrier.{u} c).pieceInterior ⊤ : Set (descentCarrier.{u} c).Carrier)))

theorem continuous_descentIncl : Continuous c.descentIncl.{u} :=
  c.isInducing_descentIncl.continuous

theorem mem_interior_filledSet {x : PlaneLift.{u} × Circle}
    (hx : ConeFilling.filledFunction (c.conePoint x) < 0) : x ∈ interior c.filledSet := by
  have ho : IsOpen {x : PlaneLift.{u} × Circle |
      ConeFilling.filledFunction (c.conePoint x) < 0} :=
    isOpen_lt c.contMDiff_filledFunction_conePoint.continuous continuous_const
  exact interior_maximal (t := {x : PlaneLift.{u} × Circle |
      ConeFilling.filledFunction (c.conePoint x) < 0})
    (fun x (hx : ConeFilling.filledFunction (c.conePoint x) < 0) => hx.le) ho hx

theorem isLocalDiffeomorph_descentIncl :
    letI := Manifold.interiorChartedSpace (descentCarrier.{u} c).model ∞
      (M := (descentCarrier.{u} c).pieceInterior ⊤)
    IsLocalDiffeomorph (𝓡 3) PlaneCircleModel ∞ c.descentIncl.{u} := by
  let _ := Manifold.interiorChartedSpace (descentCarrier.{u} c).model ∞
      (M := (descentCarrier.{u} c).pieceInterior ⊤)
  intro y
  have h1 := (Manifold.interiorAtlasDiffeomorph (descentCarrier.{u} c).model ∞
      (M := (descentCarrier.{u} c).pieceInterior ⊤)).symm.isLocalDiffeomorph y
  have h2 := isLocalDiffeomorph_subtype_val (I := (descentCarrier.{u} c).model)
    ((descentCarrier.{u} c).pieceInterior ⊤) y
  have h3 : IsLocalDiffeomorphAt (𝓡∂ 3) PlaneCircleModel ∞
      (Subtype.val : c.filledSet.{u} → PlaneLift.{u} × Circle) (y.1 : c.filledSet.{u}) :=
    c.filledAtlas.isLocalDiffeomorphAt_subtype_val
      (c.mem_interior_filledSet (c.filledFunction_descentIncl y))
  exact h1.comp _ _ (h2.comp _ _ h3)

end ConeFilling

end GC.Seifert
