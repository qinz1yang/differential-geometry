import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutDrillRaw

/-!
# Chapter-14 assembly, relative COMPARE side adapters (a): the relative drill with its inverse

Lane ASM-L2f, group G1. The relative physical fibre excision of DRILL-c
(`exists_relativeRawPhysicalExcision`, `Closure/AssemblySphereCutDrillRawApplications.lean`)
re-derived from the same public constructions (`relativeFibreExcisionRawPresentation`,
`exists_rawFibreAmbient`), with the additional ambient data that the side adapters need: the
boundary of the drilled carrier read in `W` (the old boundary and the new radial torus), and the
partial inverse `O` of the embedding off the closed unit tube.

* `exists_relativeRawAmbientExcision`: the excision with all these data.
* `RelativeDrill.symm_apply_of_mem_target`: the inverse of the partial inverse is the embedding.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **Relative physical fibre excision with its ambient inverse.** A raw presentation of a
connected compact carrier `W` supplies an ambient regular-fibre tube `φ` of `W`, the connected
drilled carrier `L ↪ W` off the open unit tube, a raw presentation of `L` with `n + 1` ports (the
old ports after one shrinking `δ`, the radial collar last), the boundary of `L` read in `W`, and the
partial inverse `O` of the embedding on the complement of the closed unit tube. -/
theorem exists_relativeRawAmbientExcision (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (G : RawGraphPresentation W) :
    ∃ φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) W.model (PlaneLift.{u} × Circle) W.Carrier ∞,
      {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source ∧ φ.target ⊆ W.interior ∧
      ∃ (L : CompactCarrier.{u}) (η : L.Carrier → W.Carrier) (R : RawGraphPresentation L)
        (he : R.externalCount = G.externalCount + 1) (δ : ℝ) (hδ : 0 < δ)
        (O : PartialDiffeomorph W.model L.model W.Carrier L.Carrier ∞),
        δ ≤ 1 ∧ L.kind = .withBoundary ∧ ConnectedSpace L.Carrier ∧
        IsSmoothEmbedding L.model W.model ∞ η ∧
        range η = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ ∧
        (∀ x, Bijective (mfderiv L.model W.model η x)) ∧
        η '' L.model.boundary L.Carrier = W.model.boundary W.Carrier ∪
          range (fun τ : Torus => φ (ULift.up (τ.1 : ℂ), τ.2)) ∧
        O.source = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ ∧
        (∀ x, x ∈ O.source → η (O x) = x) ∧
        O.target = η ⁻¹' (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ ∧
        (∀ j p, p ∈ halfCollarSource →
          η (R.external.collar (Fin.cast he.symm (Fin.castSucc j)) p) =
            shrinkHalfCollar hδ (G.external.collar j) p) ∧
        ∀ p, p ∈ halfCollarSource →
          η (R.external.collar (Fin.cast he.symm (Fin.last G.externalCount)) p) =
            φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2) := by
  let i : Fin G.components.count := ⟨0, G.components.count_pos⟩
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
  have hO_Lt := hLrest.2.2.2.1
  obtain ⟨ρ, hρ⟩ := hLrest.2.2.2.2 K ι hι.isEmbedding hrange
  have hηo := orientation_map_differentialEquivOfBijective_eq η hηbij hηpositive
  have hconn : ConnectedSpace L.Carrier := by
    let := relativeRetainedQuotient_connected G φ h3 hI K ι hι.isEmbedding hrange D hc hm
    exact ρ.surjective.connectedSpace ρ.continuous
  let R := relativeFibreExcisionRawPresentation G i φ h3 hI hUi K ι hι hrange
    hbij ho ΓK hΓKs hΓKb hΓK hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η
    hη hηbij hηo ΓL hΓLs hΓLb hΓL hbL O_L hO_Ls hO_L haW ρ hρ
  refine ⟨G.transportRegularFibreTube φ h3 hI, G.transportRegularFibreTube_closedRadius φ h3 hI,
    G.transportRegularFibreTube_interior φ h3 hI, L, η, R, rfl, δ, hδ, O_L, hδ1, hLkind, hconn, hη,
    hLrange, hηbij, hbL, hO_Ls, hO_L, hO_Lt, fun j p hp => ?_, fun p hp => ?_⟩
  · exact relativeFibreExcisionRawPresentation_external_old G i φ h3 hI hUi K ι hι hrange
      hbij ho ΓK hΓKs hΓKb hΓK hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η
      hη hηbij hηo ΓL hΓLs hΓLb hΓL hbL O_L hO_Ls hO_L haW ρ hρ j p hp
  · exact relativeFibreExcisionRawPresentation_external_new G i φ h3 hI hUi K ι hι hrange
      hbij ho ΓK hΓKs hΓKb hΓK hbK O hOs hOt hO D H hc hm hδ hδ1 hleft hright haL haR haC L η
      hη hηbij hηo ΓL hΓLs hΓLb hΓL hbL O_L hO_Ls hO_L haW ρ hρ p hp

namespace RelativeDrill

/-- The inverse of a partial inverse of an embedding is the embedding on its target. -/
theorem symm_apply_of_mem_target {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {E F H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ F H'} [ChartedSpace H M] [ChartedSpace H' N]
    {η : N → M} (O : PartialDiffeomorph I J M N ∞) (hO : ∀ x, x ∈ O.source → η (O x) = x)
    {y : N} (hy : y ∈ O.target) : O.symm y = η y := by
  have h := hO (O.symm y) (O.map_target hy)
  have hr : O.toPartialEquiv (O.symm.toPartialEquiv y) = y := O.toPartialEquiv.right_inv hy
  rw [hr] at h
  exact h.symm

end RelativeDrill

end GC.GraphManifold.Assembly
