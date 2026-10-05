import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugCut
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlaceBox
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Piece

/-!
# Chapter-14 assembly, relative COMPARE G4: the solid-cap plug interface

Lane ASM-L2e, group G4. `SolidCapPlug P`: a carrier `P` together with an actual sphere cut and
capping (`cut : SphereCutCapped P seam ports`) whose capped carrier splits into two pieces, each an
actual solid torus (`solid t : solidSet ≃ₘ piece t`), with a cap ball chart in each piece whose
closed unit ball is the cap and whose shell near radius one IS the cut-sphere half collar at height
`2 r - 2` (no attaching map), and whose solid-torus boundary collar is the retained port collar up
to one torus marking. The bounded fibre plug is an inhabitant (`AssemblySphereCutRelPlugFibre`).

* `SolidCapPlug.solidChart t`: the cap ball chart in solid-torus coordinates.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- A sphere-cut carrier whose two capped sides are solid tori with standard cap ball charts. -/
structure SolidCapPlug (P : CompactCarrier.{u}) where
  seam : SphereSeam P
  portCount : ℕ
  ports : BoundaryTori P portCount
  cut : SphereCutCapped P seam ports
  piece : Fin 2 → TopologicalSpace.Opens cut.Q.Carrier
  piece_disjoint : Disjoint (piece 0 : Set cut.Q.Carrier) (piece 1)
  piece_cover : (piece 0 : Set cut.Q.Carrier) ∪ piece 1 = univ
  solid : (t : Fin 2) → solidSet.{u} ≃ₘ⟮𝓡∂ 3, cut.Q.model⟯ ↥(piece t)
  capChart : Fin 2 → PartialDiffeomorph (𝓡 3) cut.Q.model E3 cut.Q.Carrier ∞
  capChart_source : ∀ t, closedBall (0 : E3) 2 ⊆ (capChart t).source
  capChart_piece : ∀ t, (capChart t).target ⊆ piece t
  capChart_interior : ∀ t, (capChart t).target ⊆ cut.Q.interior
  capChart_unit : ∀ t, capChart t '' closedBall 0 1 =
    range (cut.capping.cap (Fin.cast cut.h2.symm t))
  germ : ℝ
  germ_pos : 0 < germ
  germ_le : germ ≤ 1 / 4
  capChart_germ : ∀ t (z : sphere (0 : E3) 1) (r : ℝ) (hr : 1 ≤ r), r < 1 + germ →
    capChart t (r • (z : E3)) = cut.capping.core (cut.B.sphere (Fin.cast cut.h2.symm t)
      (ULift.up z, halfPoint (2 * r - 2) (by linarith)))
  port : Fin 2 → Fin cut.B.torusCount
  port_bijective : Bijective port
  marking : Fin 2 → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  depth : ℝ
  depth_pos : 0 < depth
  solid_collar : ∀ t (p : Torus) (s : ℝ) (hs : 0 ≤ s), s < depth →
    ((solid t) (solidCollar 1 (p, halfPoint s hs))).val =
      cut.capping.retained.collar (port t) (marking t p, halfPoint s hs)
  boundary_eq : P.model.boundary P.Carrier = ports.image

namespace SolidCapPlug

variable {P : CompactCarrier.{u}} (Y : SolidCapPlug P)

instance piece_nonempty (t : Fin 2) : Nonempty (Y.piece t) :=
  ⟨Y.solid t (Classical.arbitrary solidSet.{u})⟩

/-- The cap ball chart in solid-torus coordinates. -/
def solidChart (t : Fin 2) : PartialDiffeomorph (𝓡 3) (𝓡∂ 3) E3 solidSet.{u} ∞ :=
  (codRestrictOpens (Y.capChart t) (Y.piece t) inferInstance).trans
    (Y.solid t).symm.toPartialDiffeomorph

theorem solidChart_source (t : Fin 2) : (Y.solidChart t).source = (Y.capChart t).source := by
  change (codRestrictOpens (Y.capChart t) (Y.piece t) inferInstance).source ∩ _ = _
  rw [codRestrictOpens_source _ _ _ (Y.capChart_piece t)]
  exact inter_univ _

theorem solid_solidChart {t : Fin 2} {x : E3} (hx : x ∈ (Y.capChart t).source) :
    ((Y.solid t) (Y.solidChart t x)).val = Y.capChart t x := by
  change ((Y.solid t) ((Y.solid t).symm
    (codRestrictOpens (Y.capChart t) (Y.piece t) inferInstance x))).val = _
  rw [Diffeomorph.apply_symm_apply]
  exact codRestrictOpens_apply _ _ _ (Y.capChart_piece t ((Y.capChart t).map_source hx))

theorem solidChart_target_interior (t : Fin 2) :
    (Y.solidChart t).target ⊆ (𝓡∂ 3).interior solidSet.{u} := by
  intro y hy
  have hs : (Y.solidChart t).symm y ∈ (Y.capChart t).source := by
    rw [← Y.solidChart_source]
    exact (Y.solidChart t).map_target hy
  have he : Y.solidChart t ((Y.solidChart t).symm y) = y := (Y.solidChart t).right_inv hy
  have hint : Y.cut.Q.model.IsInteriorPoint (Y.capChart t ((Y.solidChart t).symm y)) :=
    Y.capChart_interior t ((Y.capChart t).map_source hs)
  rw [← Y.solid_solidChart hs] at hint
  have hint' : Y.cut.Q.model.IsInteriorPoint ((Y.solid t) (Y.solidChart t ((Y.solidChart t).symm y))) :=
    Y.cut.Q.model.isInteriorPoint_iff_isInteriorPoint_val.mpr hint
  rw [he] at hint'
  change (𝓡∂ 3).IsInteriorPoint y
  exact (((Y.solid t).isLocalDiffeomorph y).isInteriorPoint_iff (by simp)).mpr hint'

end SolidCapPlug

end GC.GraphManifold.Assembly
