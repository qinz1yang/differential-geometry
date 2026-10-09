import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutDrillPorts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreRetainedSeams
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreRetainedInterior
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawFibreComponents
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreRadialSquare
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreExcisionWithBoundary
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Chapter-14 assembly, L2-relative DRILL (c): the relative raw fibre excision

Lane ASM-L2c, row DRILL. The relative form of the closed drilling chain
(`Closure/RawFibreAssembly.lean:118` `fibreExcisionRawPresentation`, `Closure/RawFibrePuncture.lean:40`
`exists_connectedRawFibreExcision`), for a raw presentation `G` of an arbitrary compact carrier `W`
with `n = G.externalCount` ports. Drilling a regular fibre gives a raw presentation of the retained
carrier `L` with `n + 1` ports: the old ports of `W`, kept with their collars after ONE recorded
shrinking `p ↦ (p.1, δ • p.2)` (the same `δ` for every pairing collar and port, DRILL-a), and the
new radial torus last. Every old seam, matching, component index and port label is retained.

* `relativeRetainedQuotient_connected`: the retained quotient is connected when `W` is.
* `orientation_map_differentialEquivOfBijective_eq`: the positive-derivative form of an orientation
  clause (stated without any transparency option).
* `relativeFibreExcisionRawPresentation`: the relative raw presentation (`n + 1` ports).
* `exists_relativeRawFibreExcision`: the existence statement with all retained data.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Connected

private theorem relComponent_exists {C : CompactCarrier.{u}} (D : C.Components)
    (x : C.Carrier) : ∃ i, x ∈ D.piece i := by
  apply mem_iUnion.mp
  rw [D.covers]
  exact mem_univ x

private def relComponentIndex {C : CompactCarrier.{u}} (D : C.Components)
    (x : C.Carrier) : Fin D.count := Classical.choose (relComponent_exists D x)

private theorem relComponentIndex_mem {C : CompactCarrier.{u}} (D : C.Components)
    (x : C.Carrier) : x ∈ D.piece (relComponentIndex D x) :=
  Classical.choose_spec (relComponent_exists D x)

private theorem relComponentIndex_eq {C : CompactCarrier.{u}} (D : C.Components)
    {x : C.Carrier} {i : Fin D.count} (hx : x ∈ D.piece i) : relComponentIndex D x = i := by
  by_contra h
  exact (D.disjoint h).le_bot ⟨relComponentIndex_mem D x, hx⟩

private def relComponentPoint {C : CompactCarrier.{u}} (D : C.Components)
    (i : Fin D.count) : D.piece i := by
  let := D.connected i
  exact Classical.choice inferInstance

private theorem relComponentLabel_continuous {C : CompactCarrier.{u}} (D : C.Components)
    (a : Fin D.count → Bool) : Continuous (fun x => a (relComponentIndex D x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have heq : (fun y => a (relComponentIndex D y)) =ᶠ[𝓝 x]
      (fun _ : C.Carrier => a (relComponentIndex D x)) := by
    filter_upwards [(D.piece (relComponentIndex D x)).isOpen.mem_nhds
      (relComponentIndex_mem D x)] with y hy
    rw [relComponentIndex_eq D hy]
  exact continuousAt_const.congr heq.symm

private theorem relRetainedBlock_range {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
      (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (hI : φ.target ⊆ G.cutCarrier.interior) {K : CompactCarrier.{u}}
    (ι : K.Carrier → G.cutCarrier.Carrier) (hrange : range ι = G.FibreCutComplement φ)
    (j : Fin G.pairing.count) : G.pairing.gluing.block j ⊆ range ι := by
  intro x hx
  rw [hrange]
  rintro ⟨p, hp, rfl⟩
  have hs : p ∈ φ.source := h3 (by
    change ‖p.1.down‖ < 1 at hp
    change ‖p.1.down‖ ≤ 3
    linarith)
  have hi := hI (φ.map_source hs)
  have hb : G.cutCarrier.model.IsBoundaryPoint (φ p) := by
    change φ p ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier
    rw [G.cut_boundary_exhausted]
    exact Or.inl (mem_iUnion.mpr ⟨j, hx⟩)
  exact (G.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hi hb

/-- **The relative retained quotient is connected** when the carrier is (the relative form of
`fibreRetainedQuotient_connected`, `Closure/RawFibreConnected.lean:129`). -/
theorem relativeRetainedQuotient_connected {W : CompactCarrier.{u}} [ConnectedSpace W.Carrier]
    (G : RawGraphPresentation W)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
      (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (hI : φ.target ⊆ G.cutCarrier.interior) (K : CompactCarrier.{u})
    (ι : K.Carrier → G.cutCarrier.Carrier) (hι : _root_.Topology.IsEmbedding ι)
    (hrange : range ι = G.FibreCutComplement φ) (D : K.Components)
    (hc : D.count = G.components.count)
    (hm : ∀ j x, x ∈ D.piece (Fin.cast hc.symm j) ↔ ι x ∈ G.components.piece j) :
    ConnectedSpace (Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid) := by
  let q : K.Carrier → Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid :=
    Quotient.mk''
  have hconst : ∀ f : Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid → Bool,
      Continuous f → ∀ x y, f x = f y := by
    intro f hf
    let a : Fin G.components.count → Bool := fun j =>
      f (q (relComponentPoint D (Fin.cast hc.symm j)).val)
    let l : G.cutCarrier.Carrier → Bool := fun x => a (relComponentIndex G.components x)
    have hl : Continuous l := relComponentLabel_continuous G.components a
    have hret (x : K.Carrier) : l (ι x) = f (q x) := by
      let j := relComponentIndex G.components (ι x)
      have hx : x ∈ D.piece (Fin.cast hc.symm j) :=
        (hm j x).mpr (relComponentIndex_mem G.components (ι x))
      let := D.connected (Fin.cast hc.symm j)
      have hcont : Continuous (fun z : D.piece (Fin.cast hc.symm j) => f (q z.val)) :=
        hf.comp (continuous_quotient_mk'.comp continuous_subtype_val)
      exact (inferInstance : PreconnectedSpace (D.piece (Fin.cast hc.symm j))).constant
        hcont (x := relComponentPoint D (Fin.cast hc.symm j)) (y := ⟨x, hx⟩)
    have hrel : ∀ x y, G.pairing.gluing.rel x y → l x = l y := by
      intro x y hxy
      rcases hxy with rfl | ⟨j, hx, hy⟩
      · rfl
      · have hyr : y ∈ G.pairing.gluing.block j :=
          hy ▸ G.pairing.gluing.flip_mem_block hx
        obtain ⟨x', hx'⟩ := relRetainedBlock_range G φ h3 hI ι hrange j hx
        obtain ⟨y', hy'⟩ := relRetainedBlock_range G φ h3 hI ι hrange j hyr
        rw [← hx', ← hy', hret, hret]
        congr 1
        apply Quotient.sound
        apply (G.fibreRetainedGluing_rel_iff φ h3 hI K ι hι hrange x' y').mpr
        rw [hx', hy']
        exact Or.inr ⟨j, hx, hy⟩
    let old : G.pairing.QuotientSpace → Bool := Quotient.lift l hrel
    have hold : Continuous old := hl.quotient_lift hrel
    let : ConnectedSpace G.pairing.QuotientSpace :=
      G.reconstruction.symm.surjective.connectedSpace G.reconstruction.symm.continuous
    intro x y
    obtain ⟨x', rfl⟩ := Quotient.exists_rep x
    obtain ⟨y', rfl⟩ := Quotient.exists_rep y
    rw [← hret, ← hret]
    exact (inferInstance : PreconnectedSpace G.pairing.QuotientSpace).constant hold
      (x := G.pairing.quotientMap (ι x')) (y := G.pairing.quotientMap (ι y'))
  have hpre : PreconnectedSpace
      (Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid) :=
    preconnectedSpace_of_forall_constant hconst
  let j : Fin D.count := ⟨0, D.count_pos⟩
  have hne : Nonempty (Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid) :=
    ⟨Quotient.mk'' (relComponentPoint D j).val⟩
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

end Connected

/-- The positive-derivative form of an orientation clause. -/
theorem orientation_map_differentialEquivOfBijective_eq {C K : CompactCarrier.{u}}
    (f : K.Carrier → C.Carrier) (hbij : ∀ x, Bijective (mfderiv K.model C.model f x))
    (h : ∀ x, ∃ D : TangentSpace K.model x ≃L[ℝ] TangentSpace C.model (f x),
      D.toContinuousLinearMap = mfderiv K.model C.model f x ∧
      Orientation.map (Fin 3) D.toLinearEquiv (K.orientation.orientation x) =
        C.orientation.orientation (f x)) (x : K.Carrier) :
    Orientation.map (Fin 3)
      (Manifold.differentialEquivOfBijective K.model C.model f hbij x).toLinearEquiv
      (K.orientation.orientation x) = C.orientation.orientation (f x) := by
  obtain ⟨D, hD, ho⟩ := h x
  have he : (Manifold.differentialEquivOfBijective K.model C.model f hbij x).toLinearEquiv =
      D.toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    exact (DFunLike.congr_fun hD v).symm
  rw [he]
  exact ho

/-- A transported old port avoids the new radial collar. -/
theorem drilledPort_disjoint_radial {C K : CompactCarrier.{u}} {n : ℕ} (E : BoundaryTori C n)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model (PlaneLift.{u} × Circle) C.Carrier ∞)
    {ι : K.Carrier → C.Carrier} (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x) {δ : ℝ} (hδ : 0 < δ)
    (ha : ∀ j, (shrinkHalfCollar hδ (E.collar j)).target ⊆
      (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ)
    (Γ : PartialDiffeomorph halfCollarModel K.model (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hΓs : Γ.source = halfCollarSource)
    (hΓ : ∀ p, p ∈ halfCollarSource →
      ι (Γ p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) (j : Fin n) :
    Disjoint (drilledPort E O hδ j).target Γ.target := by
  rw [Set.disjoint_left]
  intro x hx hxΓ
  exact ha j (transportCollar_target ι O hO _ hx) (radialCollar_target_mem φ ι Γ hΓs hΓ hxΓ)

section Presentation

variable {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
variable (i : Fin G.components.count)
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
  (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
variable (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
variable (hI : φ.target ⊆ G.cutCarrier.interior)
variable (hUi : φ.target ⊆ G.components.piece i)
variable (K : CompactCarrier.{u}) (ι : K.Carrier → G.cutCarrier.Carrier)
variable (hι : IsSmoothEmbedding K.model G.cutCarrier.model ∞ ι)
variable (hrange : range ι = G.FibreCutComplement φ)
variable (hbij : ∀ x, Bijective (mfderiv K.model G.cutCarrier.model ι x))
variable (ho : ∀ x, Orientation.map (Fin 3)
  (Manifold.differentialEquivOfBijective K.model G.cutCarrier.model ι hbij x).toLinearEquiv
  (K.orientation.orientation x) = G.cutCarrier.orientation.orientation (ι x))
variable (ΓK : PartialDiffeomorph halfCollarModel K.model
  (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
variable (hΓKs : ΓK.source = halfCollarSource)
variable (hΓKb : ∀ t, K.model.IsBoundaryPoint (ΓK (t, halfZero)))
variable (hΓK : ∀ p, p ∈ halfCollarSource →
  ι (ΓK p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
variable (hbK : ι '' K.model.boundary K.Carrier =
  G.cutCarrier.model.boundary G.cutCarrier.Carrier ∪
    range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2)))
variable (O : PartialDiffeomorph G.cutCarrier.model K.model
  G.cutCarrier.Carrier K.Carrier ∞)
variable (hOs : O.source = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
variable (hOt : O.target = ι ⁻¹' (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
variable (hO : ∀ x, x ∈ O.source → ι (O x) = x)
variable (D : K.Components) (H : ∀ j, CircleFibration K (D.piece j))
variable (hc : D.count = G.components.count)
variable (hm : ∀ (j : Fin G.components.count) (x : K.Carrier),
  x ∈ D.piece (Fin.cast hc.symm j) ↔ ι x ∈ G.components.piece j)
variable {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
variable (hleft : ∀ j, (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆ O.source)
variable (hright : ∀ j, (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆ O.source)
variable (haL : ∀ j, (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆
  (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ)
variable (haR : ∀ j, (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆
  (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ)
variable (haC : ∀ j, (shrinkHalfCollar hδ (G.cutExternal.collar j)).target ⊆
  (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ)
variable (L : CompactCarrier.{u}) (η : L.Carrier → W.Carrier)
variable (hη : IsSmoothEmbedding L.model W.model ∞ η)
variable (hηbij : ∀ x, Bijective (mfderiv L.model W.model η x))
variable (hηo : ∀ x, Orientation.map (Fin 3)
  (Manifold.differentialEquivOfBijective L.model W.model η hηbij x).toLinearEquiv
  (L.orientation.orientation x) = W.orientation.orientation (η x))
variable (ΓL : PartialDiffeomorph halfCollarModel L.model
  (Torus × EuclideanHalfSpace 1) L.Carrier ∞)
variable (hΓLs : ΓL.source = halfCollarSource)
variable (hΓLb : ∀ t, L.model.IsBoundaryPoint (ΓL (t, halfZero)))
variable (hΓL : ∀ p, p ∈ halfCollarSource →
  η (ΓL p) = G.transportRegularFibreTube φ h3 hI
    (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
variable (hbL : η '' L.model.boundary L.Carrier =
  W.model.boundary W.Carrier ∪
    range (fun t : Torus => G.transportRegularFibreTube φ h3 hI
      (ULift.up (t.1 : ℂ), t.2)))
variable (O_L : PartialDiffeomorph W.model L.model W.Carrier L.Carrier ∞)
variable (hO_Ls : O_L.source = ((G.transportRegularFibreTube φ h3 hI) ''
  {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
variable (hO_L : ∀ x, x ∈ O_L.source → η (O_L x) = x)
variable (haW : ∀ j, (shrinkHalfCollar hδ (G.external.collar j)).target ⊆
  (G.transportRegularFibreTube φ h3 hI '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ)
variable (ρ : Quotient (G.fibreRetainedGluing φ h3 hI K ι hι.isEmbedding hrange).setoid
  ≃ₜ L.Carrier)
variable (hρ : ∀ x : K.Carrier,
  η (ρ (Quotient.mk'' x)) = G.reconstruction (G.pairing.quotientMap (ι x)))

/-- **Relative raw fibre excision** (`n + 1` ports): the relative form of
`fibreExcisionRawPresentation` (`Closure/RawFibreAssembly.lean:118`). The old ports of `W` are kept
after one shrinking (indices `Fin.castSucc j`), the new radial torus is the last port. -/
def relativeFibreExcisionRawPresentation : RawGraphPresentation L := by
  let P := G.fibreRetainedPairing φ h3 hI K ι hι.isEmbedding hrange hι.contMDiff hbij ho
    O hO hδ hδ1 hleft hright
  let V := G.fibreRetainedInteriorImage φ h3 hI K O L O_L
  let e := G.fibreRetainedInteriorDiffeomorph φ h3 hI K ι hι.isEmbedding hrange hbK
    O hOs hOt L O_L hO_Ls
  let ψ := G.transportRegularFibreTube φ h3 hI
  have hsK : ∀ j, (shrinkHalfCollar hδ (G.cutExternal.collar j)).target ⊆ O.source :=
    fun j => subset_source_of_avoid_radiusTwo φ O hOs (haC j)
  have hsL : ∀ j, (shrinkHalfCollar hδ (G.external.collar j)).target ⊆ O_L.source :=
    fun j => subset_source_of_avoid_radiusTwo ψ O_L hO_Ls (haW j)
  have hdK : ∀ j, Disjoint (drilledPort G.cutExternal O hδ j).target ΓK.target :=
    drilledPort_disjoint_radial G.cutExternal φ O hO hδ haC ΓK hΓKs hΓK
  have hdL : ∀ j, Disjoint (drilledPort G.external O_L hδ j).target ΓL.target :=
    drilledPort_disjoint_radial G.external ψ O_L hO_L hδ haW ΓL hΓLs hΓL
  let EK := drilledBoundaryTori G.cutExternal hι.isEmbedding.injective hbK O hO hδ hδ1 hsK
    ΓK hΓKs hΓKb hdK
  let EL := drilledBoundaryTori G.external hη.isEmbedding.injective hbL O_L hO_L hδ hδ1 hsL
    ΓL hΓLs hΓLb hdL
  have hEKl : EK.collar (Fin.last G.externalCount) = ΓK :=
    drilledBoundaryTori_last G.cutExternal hι.isEmbedding.injective hbK O hO hδ hδ1 hsK
      ΓK hΓKs hΓKb hdK
  have hELl : EL.collar (Fin.last G.externalCount) = ΓL :=
    drilledBoundaryTori_last G.external hη.isEmbedding.injective hbL O_L hO_L hδ hδ1 hsL
      ΓL hΓLs hΓLb hdL
  have hEKc (j : Fin G.externalCount) :
      EK.collar (Fin.castSucc j) = drilledPort G.cutExternal O hδ j :=
    drilledBoundaryTori_castSucc G.cutExternal hι.isEmbedding.injective hbK O hO hδ hδ1 hsK
      ΓK hΓKs hΓKb hdK j
  have hELc (j : Fin G.externalCount) :
      EL.collar (Fin.castSucc j) = drilledPort G.external O_L hδ j :=
    drilledBoundaryTori_castSucc G.external hη.isEmbedding.injective hbL O_L hO_L hδ hδ1 hsL
      ΓL hΓLs hΓLb hdL j
  refine
    { cutCarrier := K
      components := D
      fibration := H
      pairing := P
      externalCount := G.externalCount + 1
      external := EL
      cutExternal := EK
      external_exhausted := ?_
      cut_boundary_exhausted := ?_
      external_disjoint := ?_
      reconstruction := ρ
      quotient_smooth := ?_
      quotient_oriented := ?_
      interiorImage := V
      interiorDiffeomorph := e
      interior_map := ?_
      seam := G.fibreRetainedSeam L O_L hδ
      seam_source := ?_
      seam_zero := ?_
      seam_positive := ?_
      seam_negative := ?_
      seam_interior := G.fibreRetainedSeam_interior hδ L O_L
      seam_disjoint := G.fibreRetainedSeam_disjoint hδ L O_L
      marked_collar := ?_
      external_seam_disjoint := ?_
      leftPiece j := Fin.cast hc.symm (G.leftPiece j)
      rightPiece j := Fin.cast hc.symm (G.rightPiece j)
      left_owned := ?_
      right_owned := ?_
      externalPiece := Fin.lastCases (Fin.cast hc.symm i)
        (fun j => Fin.cast hc.symm (G.externalPiece j))
      external_owned := ?_ }
  · have h := drilledBoundaryTori_boundary G.external hη.isEmbedding.injective _ hbL O_L hO_L
      hδ hδ1 hsL ΓL hΓLs hΓLb hdL (radialCollar_zero ψ η ΓL hΓL)
      (fun _ : Fin 0 => (∅ : Set W.Carrier)) (fun _ : Fin 0 => (∅ : Set L.Carrier))
      (fun j => j.elim0) (by rw [G.external_exhausted, iUnion_of_empty, empty_union])
    rw [iUnion_of_empty, empty_union] at h
    exact h
  · exact drilledBoundaryTori_boundary G.cutExternal hι.isEmbedding.injective _ hbK O hO
      hδ hδ1 hsK ΓK hΓKs hΓKb hdK (radialCollar_zero φ ι ΓK hΓK)
      G.pairing.gluing.block (G.fibreRetainedGluing φ h3 hI K ι hι.isEmbedding hrange).block
      (fun _ _ => Iff.rfl) G.cut_boundary_exhausted
  · apply drilledBoundaryTori_disjoint_blocks G.cutExternal hι.isEmbedding.injective hbK O hO
      hδ hδ1 hsK ΓK hΓKs hΓKb hdK G.pairing.gluing.block
      (G.fibreRetainedGluing φ h3 hI K ι hι.isEmbedding hrange).block (fun _ _ h => h)
      G.external_disjoint
    intro t ht
    rw [radialCollar_zero φ ι ΓK hΓK t] at ht
    have hb : G.cutCarrier.model.IsBoundaryPoint (φ (ULift.up (t.1 : ℂ), t.2)) := by
      change φ (ULift.up (t.1 : ℂ), t.2) ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier
      rw [G.cut_boundary_exhausted]
      exact Or.inl ht
    have hs : (ULift.up (t.1 : ℂ), t.2) ∈ φ.source := h3 (by simp [Circle.norm_coe])
    exact (G.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp
      (hI (φ.map_source hs)) hb
  · exact G.fibreRetainedFold_contMDiff φ h3 hI hδ hδ1 K O hleft hright L
      ι hι.isEmbedding hrange hι.contMDiff hbij ho hO η hη ρ hρ
  · exact G.fibreRetainedFold_oriented φ h3 hI hδ hδ1 K O hleft hright L
      ι hι.isEmbedding hrange hι.contMDiff hbij ho hO η hη hηbij hηo ρ hρ
  · intro x
    exact G.fibreRetainedInteriorPD_apply φ h3 hI K ι hι.isEmbedding hrange O hO L η
      hη.isEmbedding O_L hO_L ρ hρ x.val (by
        rw [G.fibreRetainedInteriorPD_source φ h3 hI K ι hι.isEmbedding hrange hbK O
          hOs hOt L O_L hO_Ls]
        exact x.property)
  · exact G.fibreRetainedSeam_source φ h3 hI hδ hδ1 K O hOs hleft hright L O_L hO_Ls
  · exact G.fibreRetainedSeam_zero φ h3 hI hδ hδ1 K O hOs hleft hright L O_L hO_Ls
      ι hι.isEmbedding hrange hι.contMDiff hbij ho hO η hη hO_L ρ hρ
  · exact G.fibreRetainedSeam_positive φ h3 hI hδ hδ1 K O hOs hleft hright L O_L hO_Ls
      ι hι.isEmbedding hrange hι.contMDiff hbij ho hO η hη hO_L ρ hρ
  · exact G.fibreRetainedSeam_negative φ h3 hI hδ hδ1 K O hOs hleft hright L O_L hO_Ls
      ι hι.isEmbedding hrange hι.contMDiff hbij ho hO η hη hO_L ρ hρ
  · intro j p hp
    induction j using Fin.lastCases with
    | last =>
      rw [hEKl, hELl]
      exact G.fibreRetainedRadialSquare φ h3 hI K ι hι.isEmbedding hrange ΓK hΓK
        L η hη.isEmbedding.injective ΓL hΓL ρ hρ p hp
    | cast j =>
      rw [hEKc, hELc]
      apply hη.isEmbedding.injective
      rw [drilledPort_apply G.external O_L hO_L hδ hδ1 hsL j p hp]
      change η (ρ (Quotient.mk'' (drilledPort G.cutExternal O hδ j p))) = _
      rw [hρ, drilledPort_apply G.cutExternal O hO hδ hδ1 hsK j p hp, shrinkHalfCollar_apply,
        shrinkHalfCollar_apply]
      exact G.marked_collar j _ (halfSpaceScale_mem hδ hδ1 hp)
  · intro j k
    induction j using Fin.lastCases with
    | last =>
      rw [hELl]
      exact (G.fibreRetainedSeam_disjoint_radial φ h3 hI hδ hδ1 K O hOs hleft hright
        L O_L hO_Ls η hO_L haL haR ΓL hΓLs hΓL k).symm
    | cast j =>
      rw [hELc, Set.disjoint_left]
      intro x hx hxs
      have hxs' : x ∈ O_L.target ∧
          O_L.symm x ∈ (shrinkSignedCollar hδ (G.seam k)).target := hxs
      have hr : O_L (O_L.symm x) = x := O_L.right_inv hxs'.1
      have he : η x = O_L.symm x :=
        calc η x = η (O_L (O_L.symm x)) := by rw [hr]
          _ = O_L.symm x := hO_L _ (O_L.map_target hxs'.1)
      have h2 : η x ∈ (G.seam k).target := by
        rw [he]
        exact shrinkSignedCollar_target_subset hδ _ hxs'.2
      exact Set.disjoint_left.mp (G.external_seam_disjoint j k)
        (drilledPort_target G.external O_L hO_L hδ j hx) h2
  · intro j x hx
    apply (hm (G.leftPiece j) x).mpr
    exact G.left_owned j hx
  · intro j x hx
    apply (hm (G.rightPiece j) x).mpr
    exact G.right_owned j hx
  · intro j
    induction j using Fin.lastCases with
    | last =>
      rw [Fin.lastCases_last]
      rintro x ⟨t, rfl⟩
      change EK.collar (Fin.last _) (t, halfZero) ∈ _
      rw [hEKl]
      apply (hm i _).mpr
      rw [radialCollar_zero φ ι ΓK hΓK t]
      exact hUi (φ.map_source (h3 (by simp [Circle.norm_coe])))
    | cast j =>
      rw [Fin.lastCases_castSucc]
      rintro x ⟨t, rfl⟩
      change EK.collar (Fin.castSucc j) (t, halfZero) ∈ _
      rw [hEKc]
      apply (hm (G.externalPiece j) _).mpr
      rw [drilledPort_zero G.cutExternal O hO hδ hδ1 hsK j t]
      exact G.external_owned j ⟨t, rfl⟩

theorem relativeFibreExcisionRawPresentation_externalCount :
    (relativeFibreExcisionRawPresentation G i φ h3 hI hUi K ι hι hrange hbij ho ΓK hΓKs hΓKb hΓK
      hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η hη hηbij hηo ΓL hΓLs hΓLb hΓL
      hbL O_L hO_Ls hO_L haW ρ hρ).externalCount = G.externalCount + 1 := rfl

/-- The old ports of the relative excision are the old ports of `W` after one shrinking. -/
theorem relativeFibreExcisionRawPresentation_external_old (j : Fin G.externalCount)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    η ((relativeFibreExcisionRawPresentation G i φ h3 hI hUi K ι hι hrange hbij ho ΓK hΓKs hΓKb hΓK
      hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η hη hηbij hηo ΓL hΓLs hΓLb hΓL
      hbL O_L hO_Ls hO_L haW ρ hρ).external.collar (Fin.castSucc j) p) =
      shrinkHalfCollar hδ (G.external.collar j) p := by
  have hsL : ∀ j, (shrinkHalfCollar hδ (G.external.collar j)).target ⊆ O_L.source :=
    fun j => subset_source_of_avoid_radiusTwo _ O_L hO_Ls (haW j)
  rw [show (relativeFibreExcisionRawPresentation G i φ h3 hI hUi K ι hι hrange hbij ho ΓK hΓKs hΓKb hΓK
      hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η hη hηbij hηo ΓL hΓLs hΓLb hΓL
      hbL O_L hO_Ls hO_L haW ρ hρ).external.collar (Fin.castSucc j) = drilledPort G.external O_L hδ j from
    drilledBoundaryTori_castSucc G.external hη.isEmbedding.injective hbL O_L hO_L hδ hδ1 hsL
      ΓL hΓLs hΓLb
      (drilledPort_disjoint_radial G.external _ O_L hO_L hδ haW ΓL hΓLs hΓL) j]
  exact drilledPort_apply G.external O_L hO_L hδ hδ1 hsL j p hp

/-- The new port of the relative excision is the radial collar of the drilled tube. -/
theorem relativeFibreExcisionRawPresentation_external_new
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    η ((relativeFibreExcisionRawPresentation G i φ h3 hI hUi K ι hι hrange hbij ho ΓK hΓKs hΓKb hΓK
      hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η hη hηbij hηo ΓL hΓLs hΓLb hΓL
      hbL O_L hO_Ls hO_L haW ρ hρ).external.collar (Fin.last G.externalCount) p) =
      G.transportRegularFibreTube φ h3 hI
        (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2) := by
  have hsL : ∀ j, (shrinkHalfCollar hδ (G.external.collar j)).target ⊆ O_L.source :=
    fun j => subset_source_of_avoid_radiusTwo _ O_L hO_Ls (haW j)
  rw [show (relativeFibreExcisionRawPresentation G i φ h3 hI hUi K ι hι hrange hbij ho ΓK hΓKs hΓKb hΓK
      hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η hη hηbij hηo ΓL hΓLs hΓLb hΓL
      hbL O_L hO_Ls hO_L haW ρ hρ).external.collar (Fin.last G.externalCount) = ΓL from
    drilledBoundaryTori_last G.external hη.isEmbedding.injective hbL O_L hO_L hδ hδ1 hsL
      ΓL hΓLs hΓLb
      (drilledPort_disjoint_radial G.external _ O_L hO_L hδ haW ΓL hΓLs hΓL)]
  exact hΓL p hp

theorem relativeFibreExcisionRawPresentation_externalPiece_old (j : Fin G.externalCount) :
    (relativeFibreExcisionRawPresentation G i φ h3 hI hUi K ι hι hrange hbij ho ΓK hΓKs hΓKb hΓK
      hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η hη hηbij hηo ΓL hΓLs hΓLb hΓL
      hbL O_L hO_Ls hO_L haW ρ hρ).externalPiece (Fin.castSucc j) = Fin.cast hc.symm (G.externalPiece j) := by
  change Fin.lastCases (motive := fun _ => Fin D.count) (Fin.cast hc.symm i)
    (fun j => Fin.cast hc.symm (G.externalPiece j)) (Fin.castSucc j) = _
  exact Fin.lastCases_castSucc j

theorem relativeFibreExcisionRawPresentation_externalPiece_new :
    (relativeFibreExcisionRawPresentation G i φ h3 hI hUi K ι hι hrange hbij ho ΓK hΓKs hΓKb hΓK
      hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η hη hηbij hηo ΓL hΓLs hΓLb hΓL
      hbL O_L hO_Ls hO_L haW ρ hρ).externalPiece (Fin.last G.externalCount) = Fin.cast hc.symm i := by
  change Fin.lastCases (motive := fun _ => Fin D.count) (Fin.cast hc.symm i)
    (fun j => Fin.cast hc.symm (G.externalPiece j)) (Fin.last G.externalCount) = _
  exact Fin.lastCases_last

end Presentation

/-- **Relative raw fibre excision (DRILL).** Any raw presentation `G` of a compact carrier `W`
with `n = G.externalCount` ports, drilled along a regular fibre of the component `i`, gives a raw
presentation `R` of the retained carrier `L ↪ W` with `n + 1` ports: the old ports of `W` after one
recorded shrinking `δ` (indices `Fin.castSucc j`, same component labels), and the radial collar of
the drilled tube (index `Fin.last n`, component `i`). Every old seam, matching and component index
is retained; `L` is connected when `W` is. The relative form of
`RawGraphPresentation.exists_connectedRawFibreExcision` (`Closure/RawFibrePuncture.lean:40`). -/
theorem exists_relativeRawFibreExcision {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
    (i : Fin G.components.count) :
    ∃ (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
        (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
      (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
      (hI : φ.target ⊆ G.cutCarrier.interior)
      (L : CompactCarrier.{u}) (η : L.Carrier → W.Carrier) (R : RawGraphPresentation L),
      φ.target ⊆ G.components.piece i ∧
      L.kind = .withBoundary ∧
      (ConnectedSpace W.Carrier → ConnectedSpace L.Carrier) ∧
      IsSmoothEmbedding L.model W.model ∞ η ∧
      range η = ((G.transportRegularFibreTube φ h3 hI) ''
        {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ ∧
      (∀ x, Bijective (mfderiv L.model W.model η x)) ∧
      (∀ x, ∃ D : TangentSpace L.model x ≃L[ℝ] TangentSpace W.model (η x),
        D.toContinuousLinearMap = mfderiv L.model W.model η x ∧
        Orientation.map (Fin 3) D.toLinearEquiv (L.orientation.orientation x) =
          W.orientation.orientation (η x)) ∧
      ∃ (hc : R.components.count = G.components.count)
        (hp : R.pairing.count = G.pairing.count)
        (he : R.externalCount = G.externalCount + 1) (δ : ℝ) (hδ : 0 < δ),
        δ ≤ 1 ∧
        (∀ j, R.pairing.matching (Fin.cast hp.symm j) = G.pairing.matching j) ∧
        (∀ j, R.leftPiece (Fin.cast hp.symm j) = Fin.cast hc.symm (G.leftPiece j)) ∧
        (∀ j, R.rightPiece (Fin.cast hp.symm j) = Fin.cast hc.symm (G.rightPiece j)) ∧
        (∀ j, R.externalPiece (Fin.cast he.symm (Fin.castSucc j)) =
          Fin.cast hc.symm (G.externalPiece j)) ∧
        R.externalPiece (Fin.cast he.symm (Fin.last G.externalCount)) = Fin.cast hc.symm i ∧
        (∀ j p, p ∈ signedCollarSource →
          η (R.seam (Fin.cast hp.symm j) p) = G.seam j (p.1, δ * p.2)) ∧
        (∀ j p, p ∈ halfCollarSource →
          η (R.external.collar (Fin.cast he.symm (Fin.castSucc j)) p) =
            shrinkHalfCollar hδ (G.external.collar j) p) ∧
        ∀ p, p ∈ halfCollarSource →
          η (R.external.collar (Fin.cast he.symm (Fin.last G.externalCount)) p) =
            G.transportRegularFibreTube φ h3 hI
              (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2) := by
  obtain ⟨β, φ, hβ, hsource, htarget, htube⟩ :=
    (G.fibration i).exists_openSaturatedRegularFibreTube
  have h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source := by
    intro p hp
    rw [hsource]
    exact ⟨hβ hp, mem_univ p.2⟩
  have hI : φ.target ⊆ G.cutCarrier.interior := fun x hx => (htarget hx).2
  have hUi : φ.target ⊆ G.components.piece i := fun x hx => (htarget hx).1
  obtain ⟨K, ι, ΓK, O, hK⟩ :=
    CircleFibration.exists_fibreExcisionWithBoundary G.cutCarrier φ h3
  obtain ⟨hι, hrange, hbij, hpositive, hΓKs, hΓKb, hΓK, hbK, hKrest⟩ := hK.2
  have hOs := hKrest.2.1
  have hO := hKrest.2.2.1
  have hOt := hKrest.2.2.2
  have ho := orientation_map_differentialEquivOfBijective_eq ι hbij hpositive
  obtain ⟨D, ⟨H⟩, hc, hm⟩ := G.exists_rawFibreComponents i β hβ φ hsource htarget
    htube.2.2.2.2 K ι hι hrange O hOs hO
  obtain ⟨δ, hδ, hδ1, haL, haR, haC, haW⟩ := exists_fibreRelativeWidth G φ h3 hI
  have hleft (j : Fin G.pairing.count) :
      (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆ O.source :=
    subset_source_of_avoid_radiusTwo φ O hOs (haL j)
  have hright (j : Fin G.pairing.count) :
      (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆ O.source :=
    subset_source_of_avoid_radiusTwo φ O hOs (haR j)
  obtain ⟨L, η, ΓL, O_L, hLkind, hη, hLrange, hηbij, hηpositive, hΓLs, hΓLb, hΓL,
    hbL, hLrest⟩ := G.exists_rawFibreAmbient φ h3 hI
  have hO_Ls := hLrest.2.1
  have hO_L := hLrest.2.2.1
  obtain ⟨ρ, hρ⟩ := hLrest.2.2.2.2 K ι hι.isEmbedding hrange
  have hηo := orientation_map_differentialEquivOfBijective_eq η hηbij hηpositive
  have hconn : ConnectedSpace W.Carrier → ConnectedSpace L.Carrier := by
    intro hW
    let := relativeRetainedQuotient_connected G φ h3 hI K ι hι.isEmbedding hrange D hc hm
    exact ρ.surjective.connectedSpace ρ.continuous
  refine ⟨φ, h3, hI, L, η, relativeFibreExcisionRawPresentation G i φ h3 hI hUi K ι hι hrange
    hbij ho ΓK hΓKs hΓKb hΓK hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η
    hη hηbij hηo ΓL hΓLs hΓLb hΓL hbL O_L hO_Ls hO_L haW ρ hρ, hUi, hLkind, hconn, hη,
    hLrange, hηbij, hηpositive, hc, rfl, rfl, δ, hδ, hδ1, fun j => rfl, fun j => rfl,
    fun j => rfl, fun j => ?_, ?_, fun j p hp => ?_, fun j p hp => ?_, fun p hp => ?_⟩
  · exact relativeFibreExcisionRawPresentation_externalPiece_old G i φ h3 hI hUi K ι hι hrange
      hbij ho ΓK hΓKs hΓKb hΓK hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η
      hη hηbij hηo ΓL hΓLs hΓLb hΓL hbL O_L hO_Ls hO_L haW ρ hρ j
  · exact relativeFibreExcisionRawPresentation_externalPiece_new G i φ h3 hI hUi K ι hι hrange
      hbij ho ΓK hΓKs hΓKb hΓK hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η
      hη hηbij hηo ΓL hΓLs hΓLb hΓL hbL O_L hO_Ls hO_L haW ρ hρ
  · change η (G.fibreRetainedSeam L O_L hδ j p) = G.seam j (p.1, δ * p.2)
    exact G.fibreRetainedSeam_ambient φ h3 hI hδ hδ1 K O hOs hleft hright L O_L
      hO_Ls η hO_L j p hp
  · exact relativeFibreExcisionRawPresentation_external_old G i φ h3 hI hUi K ι hι hrange
      hbij ho ΓK hΓKs hΓKb hΓK hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η
      hη hηbij hηo ΓL hΓLs hΓLb hΓL hbL O_L hO_Ls hO_L haW ρ hρ j p hp
  · exact relativeFibreExcisionRawPresentation_external_new G i φ h3 hI hUi K ι hι hrange
      hbij ho ΓK hΓKs hΓKb hΓK hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η
      hη hηbij hηo ΓL hΓLs hΓLb hΓL hbL O_L hO_Ls hO_L haW ρ hρ p hp

end GC.GraphManifold.Assembly
