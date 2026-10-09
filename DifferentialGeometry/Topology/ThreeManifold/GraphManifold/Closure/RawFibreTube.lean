import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RegularFibreOpenSaturatedTube
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
Actual regular-fibre charts in the cut carrier transport through its intrinsic interior
reconstruction to the same ambient carrier, retaining sources and literal quotient-image equations.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RawGraphPresentation

variable {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
  (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
variable (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
variable (hI : φ.target ⊆ G.cutCarrier.interior)

private def tubeInteriorPoint : G.cutCarrier.interior :=
  ⟨φ (ULift.up 0, 1), hI (φ.toPartialEquiv.map_source (h3 (by simp)))⟩

private def rawInteriorPartialDiffeomorph :
    PartialDiffeomorph G.cutCarrier.model W.model G.cutCarrier.Carrier W.Carrier ∞ :=
  let x := G.tubeInteriorPoint φ h3 hI
  let a := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    G.cutCarrier.model G.cutCarrier.interior ⟨x⟩
  let b := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    W.model G.interiorImage ⟨G.interiorDiffeomorph x⟩
  (a.symm.trans G.interiorDiffeomorph.toPartialDiffeomorph).trans b

private theorem rawInteriorPartialDiffeomorph_source :
    (G.rawInteriorPartialDiffeomorph φ h3 hI).source = G.cutCarrier.interior := by
  let x := G.tubeInteriorPoint φ h3 hI
  let a := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    G.cutCarrier.model G.cutCarrier.interior ⟨x⟩
  let b := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    W.model G.interiorImage ⟨G.interiorDiffeomorph x⟩
  ext y
  change ((y ∈ a.target ∧ a.symm y ∈ univ) ∧
    G.interiorDiffeomorph (a.symm y) ∈ b.source) ↔ y ∈ G.cutCarrier.interior
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target,
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_source]
  simp only [mem_univ, and_true]
  rfl

private theorem rawInteriorPartialDiffeomorph_apply (y : G.cutCarrier.Carrier)
    (hy : y ∈ G.cutCarrier.interior) :
    G.rawInteriorPartialDiffeomorph φ h3 hI y = G.reconstruction (G.pairing.quotientMap y) := by
  let x := G.tubeInteriorPoint φ h3 hI
  change (G.interiorDiffeomorph
    ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
      G.cutCarrier.model G.cutCarrier.interior ⟨x⟩).symm y)).val = _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply]
  exact G.interior_map ⟨y, hy⟩

private theorem rawInteriorPartialDiffeomorph_target :
    (G.rawInteriorPartialDiffeomorph φ h3 hI).target ⊆ G.interiorImage := by
  intro y hy
  let x := G.tubeInteriorPoint φ h3 hI
  have hb := hy.1
  change y ∈ (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    W.model G.interiorImage ⟨G.interiorDiffeomorph x⟩).target at hb
  rwa [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target] at hb

def transportRegularFibreTube :
    PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) W.model
      (PlaneLift.{u} × Circle) W.Carrier ∞ :=
  φ.trans (G.rawInteriorPartialDiffeomorph φ h3 hI)

theorem transportRegularFibreTube_source :
    (G.transportRegularFibreTube φ h3 hI).source = φ.source := by
  ext p
  change (p ∈ φ.source ∧ φ p ∈ (G.rawInteriorPartialDiffeomorph φ h3 hI).source) ↔
    p ∈ φ.source
  rw [G.rawInteriorPartialDiffeomorph_source]
  exact ⟨And.left, fun hp => ⟨hp, hI (φ.toPartialEquiv.map_source hp)⟩⟩

theorem transportRegularFibreTube_closedRadius :
    {p | ‖p.1.down‖ ≤ 3} ⊆ (G.transportRegularFibreTube φ h3 hI).source := by
  rw [G.transportRegularFibreTube_source]
  exact h3

theorem transportRegularFibreTube_apply (p : PlaneLift.{u} × Circle) (hp : p ∈ φ.source) :
    G.transportRegularFibreTube φ h3 hI p = G.reconstruction (G.pairing.quotientMap (φ p)) :=
  G.rawInteriorPartialDiffeomorph_apply φ h3 hI (φ p) (hI (φ.toPartialEquiv.map_source hp))

theorem transportRegularFibreTube_target :
    (G.transportRegularFibreTube φ h3 hI).target ⊆ G.interiorImage := by
  intro y hy
  exact G.rawInteriorPartialDiffeomorph_target φ h3 hI hy.1

theorem transportRegularFibreTube_interior :
    (G.transportRegularFibreTube φ h3 hI).target ⊆ W.interior := by
  intro y hy
  let ψ := G.transportRegularFibreTube φ h3 hI
  have hx := ψ.toPartialEquiv.map_target hy
  have hlocal := ψ.isLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) W.model ∞ hx
  have hi := (hlocal.isInteriorPoint_iff (by simp : (∞ : ℕ∞ω) ≠ 0)).mp
    BoundarylessManifold.isInteriorPoint
  rwa [ψ.toPartialEquiv.right_inv hy] at hi

theorem transportRegularFibreTube_image (S : Set (PlaneLift.{u} × Circle))
    (hS : S ⊆ φ.source) :
    (G.transportRegularFibreTube φ h3 hI) '' S =
      (G.reconstruction ∘ G.pairing.quotientMap) '' (φ '' S) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨φ p, ⟨p, hp, rfl⟩, (G.transportRegularFibreTube_apply φ h3 hI p (hS hp)).symm⟩
  · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, G.transportRegularFibreTube_apply φ h3 hI p (hS hp)⟩

theorem transportRegularFibreTube_closedDisc_image :
    (G.transportRegularFibreTube φ h3 hI) '' {p | ‖p.1.down‖ ≤ 1} =
      (G.reconstruction ∘ G.pairing.quotientMap) '' (φ '' {p | ‖p.1.down‖ ≤ 1}) :=
  G.transportRegularFibreTube_image φ h3 hI {p | ‖p.1.down‖ ≤ 1}
    (fun p hp => h3 (by
      change ‖p.1.down‖ ≤ 3
      exact le_trans hp (by norm_num)))

theorem transportRegularFibreTube_openDisc_image :
    (G.transportRegularFibreTube φ h3 hI) '' {p | ‖p.1.down‖ < 1} =
      (G.reconstruction ∘ G.pairing.quotientMap) '' (φ '' {p | ‖p.1.down‖ < 1}) :=
  G.transportRegularFibreTube_image φ h3 hI {p | ‖p.1.down‖ < 1}
    (fun p hp => h3 (by
      change ‖p.1.down‖ ≤ 3
      exact le_trans (le_of_lt hp) (by norm_num)))

theorem exists_rawSaturatedFibreTube (i : Fin G.components.count) :
    ∃ β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model (G.fibration i).base.kind)
        PlaneLift.{u} (G.fibration i).base.Carrier ∞,
    ∃ φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
        (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞,
    ∃ ψ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) W.model
        (PlaneLift.{u} × Circle) W.Carrier ∞,
      {z | ‖z.down‖ ≤ 3} ⊆ β.source ∧
      φ.source = β.source ×ˢ univ ∧
      φ.target ⊆ (G.components.piece i ⊓ G.cutCarrier.interior :
        TopologicalSpace.Opens G.cutCarrier.Carrier) ∧
      β.target ⊆ (SurfaceModel.model (G.fibration i).base.kind).interior
        (G.fibration i).base.Carrier ∧
      (∀ (z : PlaneLift.{u}) (t : Circle), z ∈ β.source →
        ∃ hu : φ (z, t) ∈ G.components.piece i,
          (G.fibration i).projection ⟨φ (z, t), hu⟩ = β z) ∧
      φ.target = Subtype.val '' {x : G.components.piece i |
        (G.fibration i).projection x ∈ β.target} ∧
      φ '' {p | ‖p.1.down‖ ≤ 1} = Subtype.val '' {x : G.components.piece i |
        (G.fibration i).projection x ∈ β '' {z | ‖z.down‖ ≤ 1}} ∧
      φ '' {p | ‖p.1.down‖ < 1} = Subtype.val '' {x : G.components.piece i |
        (G.fibration i).projection x ∈ β '' {z | ‖z.down‖ < 1}} ∧
      ψ.source = φ.source ∧
      {p | ‖p.1.down‖ ≤ 3} ⊆ ψ.source ∧
      ψ.target ⊆ (G.interiorImage ⊓ W.interior : TopologicalSpace.Opens W.Carrier) ∧
      (∀ p, p ∈ φ.source → ψ p = G.reconstruction (G.pairing.quotientMap (φ p))) ∧
      ψ '' {p | ‖p.1.down‖ ≤ 1} = (G.reconstruction ∘ G.pairing.quotientMap) ''
        (Subtype.val '' {x : G.components.piece i |
          (G.fibration i).projection x ∈ β '' {z | ‖z.down‖ ≤ 1}}) ∧
      ψ '' {p | ‖p.1.down‖ < 1} = (G.reconstruction ∘ G.pairing.quotientMap) ''
        (Subtype.val '' {x : G.components.piece i |
          (G.fibration i).projection x ∈ β '' {z | ‖z.down‖ < 1}}) := by
  obtain ⟨β, φ, hβ, hsource, htarget, hbase, hprojection, hsat, hclosed, hopen⟩ :=
    (G.fibration i).exists_openSaturatedRegularFibreTube
  have h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source := by
    intro p hp
    rw [hsource]
    exact ⟨hβ hp, mem_univ p.2⟩
  have hI : φ.target ⊆ G.cutCarrier.interior := fun x hx => (htarget hx).2
  let ψ := G.transportRegularFibreTube φ h3 hI
  refine ⟨β, φ, ψ, hβ, hsource, htarget, hbase, hprojection, hsat, hclosed, hopen,
    G.transportRegularFibreTube_source φ h3 hI,
    G.transportRegularFibreTube_closedRadius φ h3 hI, ?_,
    G.transportRegularFibreTube_apply φ h3 hI, ?_, ?_⟩
  · intro x hx
    exact ⟨G.transportRegularFibreTube_target φ h3 hI hx,
      G.transportRegularFibreTube_interior φ h3 hI hx⟩
  · change (G.transportRegularFibreTube φ h3 hI) '' {p | ‖p.1.down‖ ≤ 1} = _
    rw [G.transportRegularFibreTube_closedDisc_image, hclosed]
  · change (G.transportRegularFibreTube φ h3 hI) '' {p | ‖p.1.down‖ < 1} = _
    rw [G.transportRegularFibreTube_openDisc_image, hopen]

end GC.GraphManifold.RawGraphPresentation
