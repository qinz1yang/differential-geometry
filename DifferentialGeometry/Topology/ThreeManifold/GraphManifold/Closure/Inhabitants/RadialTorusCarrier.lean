import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SolidTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

def carrier : CompactCarrier.{0} := solidTorusCarrier

def boundary : BoundaryTori carrier 1 :=
  solidTorusBoundary.shrink (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num)

def height (p : carrier.Carrier) : ℝ := cliffordHeight p.val

theorem height_continuous : Continuous height :=
  contMDiff_cliffordHeight.continuous.comp continuous_subtype_val

theorem boundary_torusMap : boundary.torusMap 0 = solidTorusBoundary.torusMap 0 :=
  BoundaryTori.shrink_torusMap _ _ _ _

theorem collar_height (q : Torus × EuclideanHalfSpace 1) (hq : q ∈ halfCollarSource) :
    height (boundary.collar 0 q) = -(q.2.val 0 / 8) := by
  change cliffordHeight (solidTorusCollarMap
    (q.1, halfSpaceScale (by norm_num : (0 : ℝ) < 1 / 8) q.2)).val = _
  rw [solidTorusCollarMap, cliffordHeight_cliffordSeamMap, halfSpaceScale_coord]
  have hs : 0 ≤ q.2.val 0 := q.2.property
  have ht : q.2.val 0 < 1 := hq
  rw [seamClamp_of_mem (by linarith) (by linarith)]
  ring

theorem collar_target_height {p : carrier.Carrier} (hp : p ∈ (boundary.collar 0).target) :
    -(1 / 8 : ℝ) < height p := by
  let q := (boundary.collar 0).symm p
  have hq : q ∈ halfCollarSource := by
    rw [← boundary.source_eq 0]
    exact (boundary.collar 0).map_target' hp
  have he : boundary.collar 0 q = p := (boundary.collar 0).right_inv' hp
  have ht : q.2.val 0 < 1 := hq
  have h := collar_height q hq
  rw [he] at h
  linarith

theorem collar_closure_height {p : carrier.Carrier}
    (hp : p ∈ closure (boundary.collar 0).target) : -(1 / 8 : ℝ) ≤ height p := by
  have hs : (boundary.collar 0).target ⊆ {p | -(1 / 8 : ℝ) ≤ height p} :=
    fun p hp => (collar_target_height hp).le
  exact closure_minimal hs (isClosed_le continuous_const height_continuous) hp

theorem collar_closure_off_internal :
    Disjoint (closure (boundary.collar 0).target) {p | height p = -(1 / 4 : ℝ)} := by
  refine Set.disjoint_left.2 ?_
  intro p hp hi
  have h := collar_closure_height hp
  change height p = -(1 / 4 : ℝ) at hi
  linarith

theorem carrier_connected : ConnectedSpace carrier.Carrier := by
  let connectedDisc_X135 : ConnectedSpace UnitDisc.{0} := unitDiscSurface.connected
  exact solidTorusDiscCircle.toHomeomorph.connectedSpace_iff.mpr inferInstance

theorem boundary_exhausted : carrier.model.boundary carrier.Carrier = boundary.image := by
  rw [show boundary.image = solidTorusBoundary.{0}.image from
    BoundaryTori.shrink_image _ _ _]
  ext p
  constructor
  · intro hp
    have hh : cliffordHeight p.val = 0 := solidTorus_isBoundaryPoint_iff p |>.mp hp
    have hn : sphereFirst p.val ≠ 0 := by
      intro he
      have h := norm_sphereFirst_sq_eq p.val
      rw [he, norm_zero, zero_pow (by decide)] at h
      linarith
    let t : Torus := (unitOf (sphereFirst p.val), unitOf (sphereSecond p.val))
    have hq : solidTorusCollarInv p = (t, halfZero) := by
      apply Prod.ext
      · rfl
      apply Subtype.ext
      ext i
      rw [Subsingleton.elim i 0]
      change -cliffordHeight p.val = 0
      rw [hh, neg_zero]
    refine mem_iUnion.mpr ⟨0, t, ?_⟩
    change solidTorusCollar (t, halfZero) = p
    have h := solidTorusCollar.{0}.right_inv' hn
    change solidTorusCollar (solidTorusCollarInv p) = p at h
    rw [hq] at h
    exact h
  · intro hp
    obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hp
    exact solidTorusBoundary.boundary_zero i t

def internalPoint : carrier.Carrier :=
  solidTorusCollar ((1, 1), halfPoint (1 / 4) (by norm_num))

theorem internalPoint_height : height internalPoint = -(1 / 4 : ℝ) := by
  change cliffordHeight (cliffordSeamMap ((1, 1), -(1 / 4 : ℝ))) = _
  rw [cliffordHeight_cliffordSeamMap, seamClamp_of_mem (by norm_num) (by norm_num)]

theorem internal_level_nonempty : {p : carrier.Carrier | height p = -(1 / 4 : ℝ)}.Nonempty :=
  ⟨internalPoint, internalPoint_height⟩

end GC.GraphManifold.Assembly.FC39P0.X135Radial
