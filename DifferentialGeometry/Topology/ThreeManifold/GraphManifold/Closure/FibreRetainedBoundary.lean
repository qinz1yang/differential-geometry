import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePairingTopology
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawFibreTube

/-!
The same excision preserves all paired boundary blocks and creates precisely its radial torus.
For a closed ambient carrier no external tori survive, and the new torus belongs to the selected
original component through the literal excised-piece preimages.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RawGraphPresentation

variable {M : ConnectedClosedOrientedManifold.{u} 3}
variable (G : RawGraphPresentation (NoCuts.carrier M))

private theorem fibreClosedAmbient_boundary :
    (NoCuts.carrier M).model.boundary M.Carrier = ∅ := by
  exact ModelWithCorners.Boundaryless.boundary_eq_empty

theorem externalCount_eq_zero : G.externalCount = 0 := by
  by_contra h
  have hx : G.external.torusMap ⟨0, Nat.pos_of_ne_zero h⟩ 1 ∈ G.external.image :=
    mem_iUnion.mpr ⟨_, 1, rfl⟩
  rw [← G.external_exhausted, fibreClosedAmbient_boundary] at hx
  exact hx

private theorem fibreClosedCut_boundary :
    G.cutCarrier.model.boundary G.cutCarrier.Carrier = ⋃ j, G.pairing.gluing.block j := by
  have he : G.cutExternal.image = ∅ := by
    ext x
    simp only [BoundaryTori.image, mem_iUnion, mem_range, mem_empty_iff_false, iff_false]
    rintro ⟨j, t, ht⟩
    exact (Fin.cast G.externalCount_eq_zero j).elim0
  rw [G.cut_boundary_exhausted, he, union_empty]

private theorem fibreRadialCollar_zero {C K : CompactCarrier.{u}}
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model
      (PlaneLift.{u} × Circle) C.Carrier ∞)
    (ι : K.Carrier → C.Carrier)
    (Γ : PartialDiffeomorph halfCollarModel K.model
      (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hΓrad : ∀ p, p ∈ halfCollarSource →
      ι (Γ p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    (t : Torus) : ι (Γ (t, halfZero)) = φ (ULift.up (t.1 : ℂ), t.2) := by
  have he := hΓrad (t, halfZero) (zero_mem_halfCollarSource t)
  change ι (Γ (t, halfZero)) = φ (ULift.up ((1 + 0 / 2) • (t.1 : ℂ)), t.2) at he
  simpa using he

variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
  (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
variable (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
variable (hI : φ.target ⊆ G.cutCarrier.interior)
variable (K : CompactCarrier.{u}) (ι : K.Carrier → G.cutCarrier.Carrier)
variable (hι : _root_.Topology.IsEmbedding ι)
variable (hrange : range ι = G.FibreCutComplement φ)
variable (Γ : PartialDiffeomorph halfCollarModel K.model
  (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
variable (hΓrad : ∀ p, p ∈ halfCollarSource →
  ι (Γ p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))

include hΓrad in
theorem fibreRetainedBoundary_exhausted
    (hb : ι '' K.model.boundary K.Carrier =
      G.cutCarrier.model.boundary G.cutCarrier.Carrier ∪
        range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2))) :
    K.model.boundary K.Carrier =
      (⋃ j, (G.fibreRetainedGluing φ h3 hI K ι hι hrange).block j) ∪
        range (fun t : Torus => Γ (t, halfZero)) := by
  ext x
  constructor
  · intro hx
    have hi : ι x ∈ ι '' K.model.boundary K.Carrier := mem_image_of_mem ι hx
    rw [hb, G.fibreClosedCut_boundary] at hi
    rcases hi with hi | ⟨t, ht⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hi
      left
      apply mem_iUnion.mpr
      exact ⟨j, hj⟩
    · right
      exact ⟨t, hι.injective ((fibreRadialCollar_zero φ ι Γ hΓrad t).trans ht)⟩
  · intro hx
    have hi : ι x ∈ ι '' K.model.boundary K.Carrier := by
      rw [hb, G.fibreClosedCut_boundary]
      rcases hx with hx | ⟨t, rfl⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        exact Or.inl (mem_iUnion.mpr ⟨j, hj⟩)
      · exact Or.inr ⟨t, (fibreRadialCollar_zero φ ι Γ hΓrad t).symm⟩
    obtain ⟨y, hy, he⟩ := hi
    exact hι.injective he ▸ hy

include hΓrad in
theorem fibreRetainedBoundary_disjoint :
    Disjoint (⋃ j, (G.fibreRetainedGluing φ h3 hI K ι hι hrange).block j)
      (range (fun t : Torus => Γ (t, halfZero))) := by
  rw [disjoint_left]
  rintro x hx ⟨t, rfl⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  have hb : G.cutCarrier.model.IsBoundaryPoint (ι (Γ (t, halfZero))) := by
    change ι (Γ (t, halfZero)) ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier
    rw [G.fibreClosedCut_boundary]
    exact mem_iUnion.mpr ⟨j, hj⟩
  rw [fibreRadialCollar_zero φ ι Γ hΓrad t] at hb
  have hs : (ULift.up (t.1 : ℂ), t.2) ∈ φ.source := h3 (by simp [Circle.norm_coe])
  exact (G.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp
    (hI (φ.map_source hs)) hb

include h3 hΓrad in
theorem fibreRetainedBoundary_owned (i : Fin G.components.count)
    (hUi : φ.target ⊆ G.components.piece i) (D : K.Components)
    (hc : D.count = G.components.count)
    (hm : ∀ j x, x ∈ D.piece (Fin.cast hc.symm j) ↔ ι x ∈ G.components.piece j) :
    range (fun t : Torus => Γ (t, halfZero)) ⊆ D.piece (Fin.cast hc.symm i) := by
  rintro x ⟨t, rfl⟩
  apply (hm i _).mpr
  rw [fibreRadialCollar_zero φ ι Γ hΓrad t]
  exact hUi (φ.map_source (h3 (by simp [Circle.norm_coe])))

include h3 hΓrad in
theorem fibreRetainedCollar_owned (hΓs : Γ.source = halfCollarSource)
    (i : Fin G.components.count) (hUi : φ.target ⊆ G.components.piece i)
    (D : K.Components) (hc : D.count = G.components.count)
    (hm : ∀ j x, x ∈ D.piece (Fin.cast hc.symm j) ↔ ι x ∈ G.components.piece j) :
    Γ.target ⊆ D.piece (Fin.cast hc.symm i) := by
  intro x hx
  have hp : Γ.symm x ∈ halfCollarSource := hΓs ▸ Γ.map_target hx
  apply (hm i x).mpr
  have he := hΓrad (Γ.symm x) hp
  have he := (congrArg ι (Γ.right_inv hx)).symm.trans he
  rw [he]
  apply hUi
  apply φ.map_source
  apply h3
  have hn := (Γ.symm x).2.property
  change (Γ.symm x).2.val 0 < 1 at hp
  change ‖(1 + (Γ.symm x).2.val 0 / 2) • ((Γ.symm x).1.1 : ℂ)‖ ≤ 3
  rw [norm_smul, Real.norm_of_nonneg (by linarith), Circle.norm_coe, mul_one]
  linarith

theorem fibreAmbientRadialBoundary_exhausted (L : CompactCarrier.{u})
    (η : L.Carrier → M.Carrier) (hη : _root_.Topology.IsEmbedding η)
    (ΓL : PartialDiffeomorph halfCollarModel L.model
      (Torus × EuclideanHalfSpace 1) L.Carrier ∞)
    (hΓLrad : ∀ p, p ∈ halfCollarSource →
      η (ΓL p) = G.transportRegularFibreTube φ h3 hI
        (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    (hbL : η '' L.model.boundary L.Carrier =
      (NoCuts.carrier M).model.boundary M.Carrier ∪
        range (fun t : Torus => G.transportRegularFibreTube φ h3 hI
          (ULift.up (t.1 : ℂ), t.2))) :
    L.model.boundary L.Carrier = range (fun t : Torus => ΓL (t, halfZero)) := by
  have hz (t : Torus) : η (ΓL (t, halfZero)) =
      G.transportRegularFibreTube φ h3 hI (ULift.up (t.1 : ℂ), t.2) :=
    fibreRadialCollar_zero (G.transportRegularFibreTube φ h3 hI) η ΓL hΓLrad t
  rw [fibreClosedAmbient_boundary, empty_union] at hbL
  ext x
  constructor
  · intro hx
    have hi : η x ∈ η '' L.model.boundary L.Carrier := mem_image_of_mem η hx
    rw [hbL] at hi
    obtain ⟨t, ht⟩ := hi
    exact ⟨t, hη.injective ((hz t).trans ht)⟩
  · rintro ⟨t, rfl⟩
    have hi : η (ΓL (t, halfZero)) ∈ η '' L.model.boundary L.Carrier := by
      rw [hbL]
      exact ⟨t, (hz t).symm⟩
    obtain ⟨y, hy, he⟩ := hi
    simpa only [hη.injective he] using hy

end GC.GraphManifold.RawGraphPresentation
