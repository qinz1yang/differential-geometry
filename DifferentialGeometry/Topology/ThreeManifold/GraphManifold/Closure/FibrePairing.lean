import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePairingTopology
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePairingOrientation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreCollarAvoidance

/-!
Retained half collars build the actual original torus pairing on the same excised cut carrier.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RawGraphPresentation

variable {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
  (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
variable (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
variable (hI : φ.target ⊆ G.cutCarrier.interior)
variable (K : CompactCarrier.{u}) (ι : K.Carrier → G.cutCarrier.Carrier)
variable (hι : _root_.Topology.IsEmbedding ι)
variable (hrange : range ι = G.FibreCutComplement φ)
variable (hsm : ContMDiff K.model G.cutCarrier.model ∞ ι)
variable (hbij : ∀ x, Bijective (mfderiv K.model G.cutCarrier.model ι x))
variable (ho : ∀ x, Orientation.map (Fin 3)
  (Manifold.differentialEquivOfBijective K.model G.cutCarrier.model ι hbij x).toLinearEquiv
  (K.orientation.orientation x) = G.cutCarrier.orientation.orientation (ι x))
variable (O : PartialDiffeomorph G.cutCarrier.model K.model
  G.cutCarrier.Carrier K.Carrier ∞)
variable (hO : ∀ x, x ∈ O.source → ι (O x) = x)
variable {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
variable (hleft : ∀ j, (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆ O.source)
variable (hright : ∀ j, (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆ O.source)

private theorem fibreRetainedCollar_source
    (c : PartialDiffeomorph halfCollarModel G.cutCarrier.model
      (Torus × EuclideanHalfSpace 1) G.cutCarrier.Carrier ∞)
    (hc : c.source = halfCollarSource) (ha : c.target ⊆ O.source) :
    (c.trans O).source = halfCollarSource := by
  ext p
  change (p ∈ c.source ∧ c p ∈ O.source) ↔ p ∈ halfCollarSource
  constructor
  · intro hp
    exact hc ▸ hp.1
  · intro hp
    have hs : p ∈ c.source := hc.symm ▸ hp
    exact ⟨hs, ha (c.map_source hs)⟩

include hO in
private theorem fibreRetainedCollar_apply
    (c : PartialDiffeomorph halfCollarModel G.cutCarrier.model
      (Torus × EuclideanHalfSpace 1) G.cutCarrier.Carrier ∞)
    (hc : c.source = halfCollarSource) (ha : c.target ⊆ O.source)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    ι ((c.trans O) p) = c p :=
  hO (c p) (ha (c.map_source (hc.symm ▸ hp)))

set_option backward.isDefEq.respectTransparency false in
include hsm hbij ho hO hδ1 hleft hright in
private theorem fibreRetainedCollars_reversing (j : Fin G.pairing.count) :
    ReversesBoundaryOrientation K
      ((shrinkHalfCollar hδ (G.pairing.leftCollar j)).trans O)
      (fun p => ((shrinkHalfCollar hδ (G.pairing.rightCollar j)).trans O)
        (G.pairing.matching j p.1, p.2)) := by
  let P := G.pairing.shrink hδ hδ1
  let l := (P.leftCollar j).trans O
  let r := (P.rightCollar j).trans O
  let m := G.pairing.matching j
  let f := m.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)
  let r' := f.toPartialDiffeomorph.trans r
  have hl : l.source = halfCollarSource :=
    G.fibreRetainedCollar_source K O (P.leftCollar j) (P.left_source j) (hleft j)
  have hr : r.source = halfCollarSource :=
    G.fibreRetainedCollar_source K O (P.rightCollar j) (P.right_source j) (hright j)
  have hr' : r'.source = halfCollarSource := by
    ext p
    change (p ∈ univ ∧ (m p.1, p.2) ∈ r.source) ↔ p ∈ halfCollarSource
    rw [hr]
    simp only [mem_univ, true_and]
    rfl
  have hlapply (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
      ι (l p) = P.leftCollar j p :=
    G.fibreRetainedCollar_apply K ι O hO _ (P.left_source j) (hleft j) p hp
  have hrapply (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
      ι (r' p) = P.rightCollar j (P.matching j p.1, p.2) := by
    exact G.fibreRetainedCollar_apply K ι O hO _ (P.right_source j) (hright j)
      (m p.1, p.2) hp
  have hcomp : ReversesBoundaryOrientation G.cutCarrier (ι ∘ l) (ι ∘ r') :=
    reversesBoundaryOrientation_congrOn (P.reversing j)
      (fun p hp => (hlapply p hp).symm) (fun p hp => (hrapply p hp).symm)
  exact reversesBoundaryOrientation_of_positiveInclusion ι hsm hbij ho l r' hl hr' hcomp

def fibreRetainedPairing : TorusPairing K where
  count := G.pairing.count
  gluing := G.fibreRetainedGluing φ h3 hI K ι hι hrange
  leftParam := G.fibreRetainedLeftParam φ h3 hI K ι hι hrange
  rightParam := G.fibreRetainedRightParam φ h3 hI K ι hι hrange
  matching := G.pairing.matching
  matching_eq := G.fibreRetainedGluing_matching φ h3 hI K ι hι hrange
  leftCollar j := (shrinkHalfCollar hδ (G.pairing.leftCollar j)).trans O
  rightCollar j := (shrinkHalfCollar hδ (G.pairing.rightCollar j)).trans O
  left_source j := G.fibreRetainedCollar_source K O _
    (shrinkHalfCollar_source hδ hδ1 (G.pairing.left_source j)) (hleft j)
  right_source j := G.fibreRetainedCollar_source K O _
    (shrinkHalfCollar_source hδ hδ1 (G.pairing.right_source j)) (hright j)
  left_zero j t := by
    apply hι.injective
    rw [G.fibreRetainedCollar_apply K ι O hO _
      (shrinkHalfCollar_source hδ hδ1 (G.pairing.left_source j))
        (hleft j) (t, halfZero) (zero_mem_halfCollarSource t)]
    rw [shrinkHalfCollar_apply, halfSpaceScale_halfZero, G.pairing.left_zero]
    exact (G.fibreRetainedLeftParam_apply φ h3 hI K ι hι hrange j t).symm
  right_zero j t := by
    apply hι.injective
    rw [G.fibreRetainedCollar_apply K ι O hO _
      (shrinkHalfCollar_source hδ hδ1 (G.pairing.right_source j))
        (hright j) (t, halfZero) (zero_mem_halfCollarSource t)]
    rw [shrinkHalfCollar_apply, halfSpaceScale_halfZero, G.pairing.right_zero]
    exact (G.fibreRetainedRightParam_apply φ h3 hI K ι hι hrange j t).symm
  reversing := G.fibreRetainedCollars_reversing K ι hsm hbij ho O hO hδ hδ1 hleft hright

theorem fibreRetainedPairing_count :
    (G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO hδ hδ1
      hleft hright).count = G.pairing.count := rfl

theorem fibreRetainedPairing_gluing :
    (G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO hδ hδ1
      hleft hright).gluing = G.fibreRetainedGluing φ h3 hI K ι hι hrange := rfl

theorem fibreRetainedPairing_matching :
    (G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO hδ hδ1
      hleft hright).matching = G.pairing.matching := rfl

theorem fibreRetainedPairing_leftCollar (j : Fin G.pairing.count)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    ι ((G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO hδ hδ1
      hleft hright).leftCollar j p) =
      G.pairing.leftCollar j (p.1, halfSpaceScale hδ p.2) :=
  G.fibreRetainedCollar_apply K ι O hO _
    (shrinkHalfCollar_source hδ hδ1 (G.pairing.left_source j)) (hleft j) p hp

theorem fibreRetainedPairing_rightCollar (j : Fin G.pairing.count)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    ι ((G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO hδ hδ1
      hleft hright).rightCollar j p) =
      G.pairing.rightCollar j (p.1, halfSpaceScale hδ p.2) :=
  G.fibreRetainedCollar_apply K ι O hO _
    (shrinkHalfCollar_source hδ hδ1 (G.pairing.right_source j)) (hright j) p hp


include h3 in
private theorem fibrePairingTube_compact :
    IsCompact (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1}) := by
  have hc : IsCompact {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} := by
    have he : {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} =
        (Homeomorph.ulift.symm : ℂ ≃ₜ PlaneLift.{u}) '' Metric.closedBall 0 1 := by
      ext z
      rcases z with ⟨z⟩
      simp [Metric.mem_closedBall, dist_zero_right, Homeomorph.ulift]
    rw [he]
    exact (isCompact_closedBall (0 : ℂ) 1).image Homeomorph.ulift.symm.continuous
  have hp : IsCompact {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} := by
    have he : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} =
        {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} ×ˢ univ := by ext p; simp
    rw [he]
    exact hc.prod isCompact_univ
  exact hp.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono
    (fun p hp => h3 (by change ‖p.1.down‖ ≤ 1 at hp; change ‖p.1.down‖ ≤ 3; linarith)))

include h3 hI in
theorem exists_fibrePairingWidth
    (hOs : O.source = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧
      (∀ j, (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆ O.source) ∧
      (∀ j, (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆ O.source) := by
  let c : Fin G.pairing.count × Bool →
      PartialDiffeomorph halfCollarModel G.cutCarrier.model
        (Torus × EuclideanHalfSpace 1) G.cutCarrier.Carrier ∞ :=
    fun a => if a.2 then G.pairing.leftCollar a.1 else G.pairing.rightCollar a.1
  have hc (a : Fin G.pairing.count × Bool) : (c a).source = halfCollarSource := by
    rcases a with ⟨j, b⟩
    cases b
    · exact G.pairing.right_source j
    · exact G.pairing.left_source j
  have hb (a : Fin G.pairing.count × Bool) (t : Torus) :
      G.cutCarrier.model.IsBoundaryPoint (c a (t, halfZero)) := by
    change c a (t, halfZero) ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier
    rw [G.cut_boundary_exhausted]
    refine Or.inl (mem_iUnion.mpr ⟨a.1, ?_⟩)
    rcases a with ⟨j, b⟩
    cases b
    · change G.pairing.rightCollar j (t, halfZero) ∈ G.pairing.gluing.block j
      rw [G.pairing.right_zero]
      exact Or.inr (G.pairing.rightParam j t).property
    · change G.pairing.leftCollar j (t, halfZero) ∈ G.pairing.gluing.block j
      rw [G.pairing.left_zero]
      exact Or.inl (G.pairing.leftParam j t).property
  have hKI : φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} ⊆ G.cutCarrier.interior := by
    rintro x ⟨p, hp, rfl⟩
    exact hI (φ.map_source (h3 (by
      change ‖p.1.down‖ ≤ 1 at hp
      change ‖p.1.down‖ ≤ 3
      linarith)))
  obtain ⟨δ, hδ, hδ1, ha⟩ := exists_shrinkHalfCollars_avoiding_compact c hc hb
    (G.fibrePairingTube_compact φ h3) hKI
  have htarget (a : Fin G.pairing.count × Bool) :
      (shrinkHalfCollar hδ (c a)).target ⊆ O.source := by
    intro x hx
    have hp : (shrinkHalfCollar hδ (c a)).symm x ∈ halfCollarSource := by
      have hs : (shrinkHalfCollar hδ (c a)).source = halfCollarSource :=
        shrinkHalfCollar_source hδ hδ1 (hc a)
      exact hs ▸ (shrinkHalfCollar hδ (c a)).map_target hx
    have h := ha a ((shrinkHalfCollar hδ (c a)).symm x) hp
    have hn : x ∉ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} :=
      (shrinkHalfCollar hδ (c a)).toPartialEquiv.right_inv hx ▸ h
    exact hOs.symm ▸ hn
  exact ⟨δ, hδ, hδ1, fun j => htarget (j, true), fun j => htarget (j, false)⟩

end GC.GraphManifold.RawGraphPresentation
