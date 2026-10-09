import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalCoverEulerGlue
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalCoverEulerMatrix
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFiniteRelations

/-!
# The fibre of a closed three-cone block is nontrivial

Chapter 5 plan P5, the certificate `hnon`. For a closed block with three cones `(pᵢ, qᵢ)` the
pants values `a`, `b`, `(ba)⁻¹` of the three boundary circles go to the unimodular matrices `X`,
`Y`, `(YX)⁻¹` of `ClosedTerminalCoverEulerMatrix` (traces `2 cos (π qᵢ / pᵢ)`) and the fibre goes
to `-1`; the meridian relations `wᵢ ^ pᵢ h ^ qᵢ = 1` hold, so `exists_closedTriangle_portHom`
gives a homomorphism `π₁(Q) → GL₂(ℂ)`. The fibre class at a filled port point is the image of
the second torus loop, hence goes to a conjugate of `-1 ≠ 1`
(`fibreClass_ne_one_of_closed_three_cones`, at every point of the product piece).

The argument is nonabelian on purpose: for the cones `(2,1), (3,1), (7,-6)` (Euler number `1/42`)
the fibre dies in every abelian quotient (Codex X43b, `ClosedTerminalCoverH1Obstruction`). It uses
neither the sign of `orbChi` nor the Euler number, so the frozen `closedTriangle_fibre_nontrivial`
holds without a case split; its `euler ≠ 0` branch is
`closedTriangle_fibre_nontrivial_of_euler_ne_zero`.
-/

set_option autoImplicit false

noncomputable section
open Multiplicative
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Topology ContinuousMap unitInterval

universe u

namespace GC.Seifert

theorem closedTriangle_torusTurnLoop_fst :
    (GC.Topology.torusFundamentalGroup
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusTurnLoop torusBase)))).1 =
        1 := by
  have h := congrFun torusTurnLoop_coordinates 0
  rw [toAdd_torusCoordinates_zero] at h
  exact toAdd_eq_zero.mp h

theorem closedTriangle_torusTurnLoop_snd :
    (GC.Topology.torusFundamentalGroup
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusTurnLoop torusBase)))).2 =
        ofAdd 1 := by
  have h := congrFun torusTurnLoop_coordinates 1
  rw [toAdd_torusCoordinates_one] at h
  exact toAdd.injective (h.trans rfl)

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem fibreClass_portMap (B : SeifertBlock W d) (c : Fin d.k) :
    B.fibreClass (B.product.portMap c torusBase) =
      FundamentalGroup.map (B.productToCarrier.comp (B.product.portMap c)) torusBase
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusTurnLoop torusBase))) := by
  rw [fibreClass, ProductFibredPiece.turnLoop_portMap, GC.Topology.fundamentalGroup_map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem fibreClass_ne_one_of_closed_three_cones (B : SeifertBlock W d) (hclosed : d.ports = 0)
    (hcones : d.cones.length = 3) (p : B.presentation.components.piece (B.piece none)) :
    B.fibreClass p ≠ 1 := by
  have hsum := d.ports_add_length_add_length
  have hk3 := d.k_le_three
  have hk : d.k = 3 := by omega
  have hnormals : d.normals.length = 0 := by omega
  have h3 : d.fillingCount = 3 := by
    simp only [SeifertData.fillingCount]
    omega
  have : IsEmpty (Fin d.ports) := hclosed ▸ inferInstance
  let e : Fin 3 ≃ Fin d.fillingCount :=
    (((Equiv.emptySum (Fin d.ports) (Fin d.fillingCount)).symm.trans B.port).trans
      (finCongr hk)).symm
  have hp2 : ∀ m : Fin d.fillingCount, 2 ≤ (d.fillingSlope m).1 := by
    intro m
    induction m using Fin.addCases with
    | left c =>
      rw [SeifertData.fillingSlope, Fin.append_left]
      have := d.two_le_of_mem_cones d.cones[c] (List.getElem_mem _)
      dsimp only
      omega
    | right n => exact absurd n.isLt (by omega)
  obtain ⟨ι, hι1, hιrel⟩ := exists_closedTriangleMatrixHom (fun j => (d.fillingSlope (e j)).1)
    (fun j => (d.fillingSlope (e j)).2) (fun j => hp2 _) (fun j => d.isPrimitive_fillingSlope _)
  obtain ⟨b₀, κ, hκ⟩ := B.product.base.exists_pantsHom' hk (FreeGroup.of (0 : Fin 2))
    (FreeGroup.of (1 : Fin 2))
  let w : Fin d.fillingCount → FreeGroup (Fin 2) := fun m =>
    ![(FreeGroup.of 1 * FreeGroup.of 0)⁻¹, FreeGroup.of 0, FreeGroup.of 1]
      (Fin.cast hk (B.port (.inr m)))
  have hM : ∀ m, ι (w m ^ torusMapMatrix (B.presentation.matchingMap (B.seam m)) 0 0,
      ofAdd (torusMapMatrix (B.presentation.matchingMap (B.seam m)) 1 0)) = 1 := by
    intro m
    have hr := hιrel (e.symm m)
    simp only [Equiv.apply_symm_apply] at hr
    exact incl_relation_of_slope ι (w m) hr (B.torusMatrix_meridian m)
  obtain ⟨z, Φ, hΦ⟩ := B.exists_closedTriangle_portHom h3 ι κ w (fun m γ => hκ _ γ) hM
  let m₀ : Fin d.fillingCount := ⟨0, by omega⟩
  refine B.fibreClass_ne_one_transfer p (B.product.portMap (B.port (.inr m₀)) torusBase) ?_
  intro hfib
  have := B.connectedSpace
  have : LocallyPathConnectedSpace W.Carrier :=
    Manifold.locallyPathConnectedSpace_of_modelWithCorners (M := W.Carrier) W.model
  have : PathConnectedSpace W.Carrier := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  let δ := PathConnectedSpace.somePath z
    (B.productToCarrier (B.product.portMap (B.port (.inr m₀)) torusBase))
  obtain ⟨k, hk'⟩ := hΦ m₀ δ
  let g := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusTurnLoop torusBase))
  have hval : Φ (GC.Topology.markedMap
      (B.productToCarrier.comp (B.product.portMap (B.port (.inr m₀)))) torusBase δ g) = 1 := by
    change Φ (fundamentalGroupChangeBasepoint δ (FundamentalGroup.map
      (B.productToCarrier.comp (B.product.portMap (B.port (.inr m₀)))) torusBase g)) = 1
    rw [← B.fibreClass_portMap, hfib, map_one, map_one]
  rw [hk' g, closedTriangle_torusTurnLoop_fst, closedTriangle_torusTurnLoop_snd, toAdd_one,
    zpow_zero, hι1] at hval
  exact closedTriangle_neg_one_ne_one ((closedTriangle_neg_one_mem_center k).symm.trans hval)

end SeifertBlock

theorem closedTriangle_fibre_nontrivial (Q : ConnectedClosedOrientedManifold.{u} 3)
    (d : SeifertData) (B : SeifertBlock (NoCuts.carrier Q) d) (hclosed : d.ports = 0)
    (hcones : d.cones.length = 3) (_hchi : d.orbChi ≤ 0) :
    ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1 := by
  have : ConnectedSpace (B.presentation.components.piece (B.piece none)) :=
    B.presentation.components.connected _
  obtain ⟨p⟩ := (inferInstance : Nonempty (B.presentation.components.piece (B.piece none)))
  exact ⟨p, B.fibreClass_ne_one_of_closed_three_cones hclosed hcones p⟩

theorem closedTriangle_fibre_nontrivial_of_euler_ne_zero
    (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
    (B : SeifertBlock (NoCuts.carrier Q) d) (hclosed : d.ports = 0)
    (hcones : d.cones.length = 3) (hchi : d.orbChi ≤ 0) (_heuler : d.euler ≠ 0) :
    ∃ p : B.presentation.components.piece (B.piece none), B.fibreClass p ≠ 1 :=
  closedTriangle_fibre_nontrivial Q d B hclosed hcones hchi

end GC.Seifert
