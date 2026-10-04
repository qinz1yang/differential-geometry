import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawFibreAssembly

/-!
An arbitrary original closed raw presentation supplies an actual same-tube punctured raw
presentation, with every old seam, matching and component index retained literally.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u
namespace GC.GraphManifold.RawGraphPresentation

set_option backward.isDefEq.respectTransparency false in
private theorem rawExcision_positive {C K : CompactCarrier.{u}} (f : K.Carrier → C.Carrier)
    (hbij : ∀ x, Bijective (mfderiv K.model C.model f x))
    (h : ∀ x, ∃ D : TangentSpace K.model x ≃L[ℝ] TangentSpace C.model (f x),
      D.toContinuousLinearMap = mfderiv K.model C.model f x ∧
      Orientation.map (Fin 3) D.toLinearEquiv (K.orientation.orientation x) =
        C.orientation.orientation (f x)) :
    ∀ x, Orientation.map (Fin 3)
      (Manifold.differentialEquivOfBijective K.model C.model f hbij x).toLinearEquiv
      (K.orientation.orientation x) = C.orientation.orientation (f x) := by
  intro x
  obtain ⟨D, hD, ho⟩ := h x
  have he : (Manifold.differentialEquivOfBijective K.model C.model f hbij x).toLinearEquiv =
      D.toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    exact (DFunLike.congr_fun hD v).symm
  rw [he]
  exact ho

theorem exists_rawFibreExcision
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (G : RawGraphPresentation (NoCuts.carrier M)) (i : Fin G.components.count) :
    ∃ (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
        (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
      (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
      (hI : φ.target ⊆ G.cutCarrier.interior)
      (L : CompactCarrier.{u}) (η : L.Carrier → M.Carrier) (R : RawGraphPresentation L),
      φ.target ⊆ G.components.piece i ∧
      L.kind = .withBoundary ∧
      IsSmoothEmbedding L.model (NoCuts.carrier M).model ∞ η ∧
      range η = ((G.transportRegularFibreTube φ h3 hI) ''
        {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ ∧
      (∀ x, Bijective (mfderiv L.model (NoCuts.carrier M).model η x)) ∧
      (∀ x, ∃ D : TangentSpace L.model x ≃L[ℝ]
          TangentSpace (NoCuts.carrier M).model (η x),
        D.toContinuousLinearMap = mfderiv L.model (NoCuts.carrier M).model η x ∧
        Orientation.map (Fin 3) D.toLinearEquiv (L.orientation.orientation x) =
          M.orientation.orientation (η x)) ∧
      ∃ (hc : R.components.count = G.components.count)
        (hp : R.pairing.count = G.pairing.count) (he : R.externalCount = 1) (δ : ℝ),
        0 < δ ∧ δ ≤ 1 ∧
        (∀ j, R.pairing.matching (Fin.cast hp.symm j) = G.pairing.matching j) ∧
        (∀ j, R.leftPiece (Fin.cast hp.symm j) = Fin.cast hc.symm (G.leftPiece j)) ∧
        (∀ j, R.rightPiece (Fin.cast hp.symm j) = Fin.cast hc.symm (G.rightPiece j)) ∧
        (∀ j p, p ∈ signedCollarSource →
          η (R.seam (Fin.cast hp.symm j) p) = G.seam j (p.1, δ * p.2)) ∧
        (∀ p, p ∈ halfCollarSource →
          η (R.external.collar (Fin.cast he.symm (0 : Fin 1)) p) =
            G.transportRegularFibreTube φ h3 hI
              (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
 := by
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
  have ho := rawExcision_positive ι hbij hpositive
  obtain ⟨D, ⟨H⟩, hc, hm⟩ := G.exists_rawFibreComponents i β hβ φ hsource htarget
    htube.2.2.2.2 K ι hι hrange O hOs hO
  obtain ⟨δ, hδ, hδ1, haL, haR⟩ := G.exists_fibreSeparatedWidth φ h3 hI
  have hunit : φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} ⊆
      φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} := by
    apply image_mono
    intro p hp
    change ‖p.1.down‖ ≤ 1 at hp
    change ‖p.1.down‖ ≤ 2
    linarith
  have hleft (j : Fin G.pairing.count) :
      (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆ O.source := by
    rw [hOs]
    intro x hx
    exact fun h => haL j hx (hunit h)
  have hright (j : Fin G.pairing.count) :
      (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆ O.source := by
    rw [hOs]
    intro x hx
    exact fun h => haR j hx (hunit h)
  obtain ⟨L, η, ΓL, O_L, hLkind, hη, hLrange, hηbij, hηpositive, hΓLs, hΓLb, hΓL,
    hbL, hLrest⟩ := G.exists_rawFibreAmbient φ h3 hI
  have hO_Ls := hLrest.2.1
  have hO_L := hLrest.2.2.1
  obtain ⟨ρ, hρ⟩ := hLrest.2.2.2.2 K ι hι.isEmbedding hrange
  have hηo := rawExcision_positive η hηbij hηpositive
  let R := G.fibreExcisionRawPresentation i φ h3 hI hUi K ι hι hrange hbij ho
    ΓK hΓKs hΓKb hΓK hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR
    L η hη hηbij hηo ΓL hΓLs hΓLb hΓL hbL O_L hO_Ls hO_L ρ hρ
  have hcR : R.components.count = G.components.count := hc
  have hpR : R.pairing.count = G.pairing.count := rfl
  have heR : R.externalCount = 1 := rfl
  refine ⟨φ, h3, hI, L, η, R, hUi, hLkind, hη, hLrange, hηbij, hηpositive,
    hcR, hpR, heR, δ, hδ, hδ1, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rfl
  · intro j
    rfl
  · intro j
    rfl
  · intro j p hp
    change η (G.fibreRetainedSeam L O_L hδ j p) = G.seam j (p.1, δ * p.2)
    exact G.fibreRetainedSeam_ambient φ h3 hI hδ hδ1 K O hOs hleft hright L O_L
      hO_Ls η hO_L j p hp
  · intro p hp
    change η (ΓL p) = _
    exact hΓL p hp

end GC.GraphManifold.RawGraphPresentation
