import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationInterior
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Decomposition
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42Components

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)

theorem cutCarrier_nonempty_S12 : Nonempty (cutCarrier_C2a F).Carrier := by
  by_cases hc : F.count = 0
  · obtain ⟨y⟩ : Nonempty M.Carrier := inferInstance
    refine ⟨kpt_S12 F (y := y) ?_⟩
    intro hy
    obtain ⟨i, -⟩ := mem_iUnion.mp hy
    exact absurd i.2 (by omega)
  · exact ⟨sideTorus_C2a F ⟨0, Nat.pos_of_ne_zero hc⟩ hR_C2a 1⟩

theorem exists_owner_S12 (D : (cutCarrier_C2a F).Components) {S : Set (cutCarrier_C2a F).Carrier}
    (hS : IsPreconnected S) (hne : S.Nonempty) : ∃ j, S ⊆ (D.piece j : Set _) := by
  obtain ⟨p, hp⟩ := hne
  have hp' : p ∈ ⋃ j, (D.piece j : Set (cutCarrier_C2a F).Carrier) := by rw [D.covers]; trivial
  obtain ⟨j, hj⟩ := mem_iUnion.mp hp'
  exact ⟨j, hS.subset_isClopen ⟨D.closed j, (D.piece j).isOpen⟩ ⟨p, hp, hj⟩⟩

/-- **LP07 / C2b, the real cut as a torus presentation.** The cut carrier `K = M ∖ ⋃ σ_i(T²×(-1/2,1/2))`
with the torus pairing `left = σ_i(·, -ψ), right = σ_i(·, ψ)`, glued by the identity of the model
torus, reconstructs `M` through the stretch `R`; the seams are the given collars `σ_i`. -/
def cutPresentation_S12 (M : ConnectedClosedOrientedManifold.{u} 3)
    (F : CollaredTorusFamily_C2a M.Carrier) : GC.Seifert.TorusPresentation (NoCuts.carrier M) :=
  haveI : Nonempty (cutCarrier_C2a F).Carrier := cutCarrier_nonempty_S12 F
  let D : (cutCarrier_C2a F).Components :=
    (GC.GraphManifold.Assembly.nonempty_components_of_nonempty (cutCarrier_C2a F)).some
  have hleft : ∀ i : Fin F.count, ∃ j, (cutPairing_S12 F).gluing.left i ⊆ (D.piece j : Set _) :=
    fun i => exists_owner_S12 F D (isPreconnected_range (continuous_sideTorus_C2a F i hL_C2a))
      ⟨_, ⟨1, rfl⟩⟩
  have hright : ∀ i : Fin F.count, ∃ j, (cutPairing_S12 F).gluing.right i ⊆ (D.piece j : Set _) :=
    fun i => exists_owner_S12 F D (isPreconnected_range (continuous_sideTorus_C2a F i hR_C2a))
      ⟨_, ⟨1, rfl⟩⟩
  { cutCarrier := cutCarrier_C2a F
    components := D
    pairing := cutPairing_S12 F
    externalCount := 0
    external := GC.GraphManifold.BoundaryTori.empty _
    cutExternal := GC.GraphManifold.BoundaryTori.empty _
    external_exhausted := by
      rw [GC.GraphManifold.closedCarrier_boundary_eq_empty, GC.GraphManifold.BoundaryTori.empty_image]
    cut_boundary_exhausted := by
      rw [GC.GraphManifold.BoundaryTori.empty_image, Set.union_empty]
      exact (cutGluing_C2a F).boundary_exhausted
    external_disjoint := by
      rw [GC.GraphManifold.BoundaryTori.empty_image]; exact Set.disjoint_empty _
    reconstruction := cutRecon_S12 F
    quotient_smooth := contMDiff_rmapK_S12 F
    quotient_oriented := fun x =>
      ⟨(Manifold.differentialEquivOfBijective (cutCarrier_C2a F).model (𝓡 3) (rmapK_S12 F)
          (rmapK_mfderiv_bijective_S12 F) x).toLinearEquiv, fun v => rfl, rmapK_oriented_S12 F x⟩
    interiorImage := interiorImage_S12 F
    interiorDiffeomorph := interiorDiffeomorph_S12 F
    interior_map := fun x => rfl
    seam := F.collar
    seam_source := F.source_eq
    seam_zero := fun i t => (rmapK_sideTorus_left_S12 F i t).symm
    seam_positive := fun i t s hs h => by
      have hy : ((t, halfPoint s hs) : Torus × EuclideanHalfSpace 1) ∈ halfCollarSource := h
      have := rmapK_rightCollar_S12 F i hy
      exact this.symm
    seam_negative := fun i t s hs h => by
      have hy : ((t, halfPoint (-s) (neg_nonneg.mpr hs)) : Torus × EuclideanHalfSpace 1) ∈
          halfCollarSource := by change -s < 1; linarith
      have := rmapK_leftCollar_S12 F i hy
      have e : F.collar i (t, s) =
          F.collar i (t, -((halfPoint (-s) (neg_nonneg.mpr hs)).val 0)) := by
        congr 2; change s = -(-s); ring
      exact e.trans this.symm
    seam_interior := fun i y _ => BoundarylessManifold.isInteriorPoint
    seam_disjoint := F.disjoint
    marked_collar := fun i => i.elim0
    external_seam_disjoint := fun i => i.elim0
    leftPiece := fun i => (hleft i).choose
    rightPiece := fun i => (hright i).choose
    left_owned := fun i => (hleft i).choose_spec
    right_owned := fun i => (hright i).choose_spec
    externalPiece := fun i => i.elim0
    external_owned := fun i => i.elim0 }

theorem cutPresentation_count_S12 (M : ConnectedClosedOrientedManifold.{u} 3)
    (F : CollaredTorusFamily_C2a M.Carrier) : (cutPresentation_S12 M F).pairing.count = F.count := rfl

theorem cutPresentation_seam_S12 (M : ConnectedClosedOrientedManifold.{u} 3)
    (F : CollaredTorusFamily_C2a M.Carrier) (i : Fin F.count) :
    (cutPresentation_S12 M F).seam i = F.collar i := rfl

theorem cutPresentation_cutCarrier_S12 (M : ConnectedClosedOrientedManifold.{u} 3)
    (F : CollaredTorusFamily_C2a M.Carrier) : (cutPresentation_S12 M F).cutCarrier = cutCarrier_C2a F := rfl

/-- **C2b main theorem** (supersedes S3's frozen `cutAlongTori_C2a`): every finite family of disjoint
signed collars in a closed connected oriented 3-manifold `M` is the seam family of a
`TorusDecomposition` of `M` whose cut carrier is `M ∖ ⋃ σ_i(T²×(-1/2,1/2))`, with
`torusInPrime e i t = σ_i(t,0)` and `primeSeam e i = σ_i`. -/
theorem cutAlongTori_C2a_S12 (M : ConnectedClosedOrientedManifold.{u} 3)
    (F : CollaredTorusFamily_C2a M.Carrier) :
    ∃ (D : GC.Topology.TorusDecomposition M) (e : Fin F.count ≃ Fin D.boundary.count),
      D.carrier = cutCarrier_C2a F ∧
      (∀ i (t : Torus), D.reconstructionAtlas.torusInPrime D.reconstruction (e i) t =
        F.collar i (t, 0)) ∧
      (∀ i, ∀ p ∈ signedCollarSource,
        D.reconstructionAtlas.primeSeam D.reconstruction (e i) p = F.collar i p) :=
  ⟨(cutPresentation_S12 M F).toTorusDecomposition, Equiv.refl _, rfl,
    fun i t => (cutPresentation_S12 M F).toTorusDecomposition_torusInPrime i t,
    fun i p _ => (cutPresentation_S12 M F).toTorusDecomposition_primeSeam i p⟩

end GC.LongTime.Ch12
