import DifferentialGeometry.Topology.Manifold.Components
import DifferentialGeometry.Topology.ThreeManifold.CapComponentBallChart
import DifferentialGeometry.Topology.ThreeManifold.PairedBallGluing
import DifferentialGeometry.Topology.ThreeManifold.UncappingProjection
import Mathlib.Topology.Homeomorph.Quotient

set_option autoImplicit false
noncomputable section
open Set Metric

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

private def capFlagMap (p : E.tubes.Index × Bool) (x : E3) :
    Σ K, (E.capped.component K).Carrier :=
  PairedBallGluing.flagMap E.capped.component E.cutCapVertex
    (fun e t => E.capComponentBallChart (e, t)) p x

private theorem capFlagMap_val (p : E.tubes.Index × Bool) (x : E3)
    (hx : x ∈ closedBall (0 : E3) 2) :
    E.capped.componentUnionHomeomorph (capFlagMap E p x) = (E.capping.capBallChart p).chart x :=
  E.capComponentBallChart_apply_closedBall p hx

theorem pairwise_disjoint_capComponentBallChart_image :
    Pairwise fun p q : E.tubes.Index × Bool =>
      Disjoint (PairedBallGluing.flagMap E.capped.component E.cutCapVertex
        (fun e t => E.capComponentBallChart (e, t)) p '' closedBall (0 : E3) 2)
      (PairedBallGluing.flagMap E.capped.component E.cutCapVertex
        (fun e t => E.capComponentBallChart (e, t)) q '' closedBall (0 : E3) 2) := by
  intro p q hpq
  rw [disjoint_left]
  rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
  have h := congrArg E.capped.componentUnionHomeomorph (hyx.trans hzx.symm)
  change E.capped.componentUnionHomeomorph (capFlagMap E p y) =
    E.capped.componentUnionHomeomorph (capFlagMap E q z) at h
  rw [capFlagMap_val E p y hy, capFlagMap_val E q z hz] at h
  exact disjoint_left.mp (E.capping.pairwise_disjoint_capBallChart_closedBall hpq)
    ⟨y, hy, h⟩ ⟨z, hz, rfl⟩

private theorem capFlagMap_holes (x : Σ K, (E.capped.component K).Carrier) :
    x ∈ ⋃ p, capFlagMap E p '' ball (0 : E3) 1 ↔
      E.capped.componentUnionHomeomorph x ∈
        ⋃ p, (E.capping.capBallChart p).chart '' ball (0 : E3) 1 := by
  have hball : ball (0 : E3) 1 ⊆ closedBall (0 : E3) 2 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  constructor
  · intro hx
    obtain ⟨p, y, hy, rfl⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨p, y, hy, (capFlagMap_val E p y (hball hy)).symm⟩
  · intro hx
    obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨p, y, hy, E.capped.componentUnionHomeomorph.injective
      ((capFlagMap_val E p y (hball hy)).trans hyx)⟩

def puncturedCapComponentHomeomorph :
    (Σ K, PairedBallGluing.PuncturedFactor E.capped.component E.cutCapVertex
      (fun e t => E.capComponentBallChart (e, t)) K) ≃ₜ
    {x : E.capped.Carrier // x ∉ ⋃ p, (E.capping.capBallChart p).chart '' ball (0 : E3) 1} := by
  let X := fun K => PairedBallGluing.PuncturedFactor E.capped.component E.cutCapVertex
    (fun e t => E.capComponentBallChart (e, t)) K
  let Y := {x : E.capped.Carrier // x ∉
    ⋃ p, (E.capping.capBallChart p).chart '' ball (0 : E3) 1}
  letI : ∀ K, TopologicalSpace (X K) := fun K => inferInstanceAs
    (TopologicalSpace (PairedBallGluing.PuncturedFactor E.capped.component E.cutCapVertex
      (fun e t => E.capComponentBallChart (e, t)) K))
  let f : (Σ K, X K) → Y := fun x =>
    ⟨x.snd.val.val, fun h => x.snd.property ((capFlagMap_holes E ⟨x.fst, x.snd.val⟩).mpr h)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply continuous_sigma
    intro K
    have hinner : Continuous (fun x : X K => x.val) := continuous_subtype_val
    have houter : Continuous (fun x : (E.capped.component K).Carrier => x.val) :=
      continuous_subtype_val
    exact houter.comp hinner
  have hi : Function.Injective f := by
    rintro ⟨K, x⟩ ⟨L,y⟩ h
    have hval : x.val.val = y.val.val := congrArg Subtype.val h
    have hK : K = L := x.val.property.symm.trans
      ((congrArg ConnectedComponents.mk hval).trans y.val.property)
    subst L
    have hxy : x = y := Subtype.ext (Subtype.ext hval)
    subst y
    rfl
  have hs : Function.Surjective f := by
    intro y
    let K := ConnectedComponents.mk y.val
    let x : (E.capped.component K).Carrier := ⟨y.val, rfl⟩
    have hx : (⟨K, x⟩ : Σ K, (E.capped.component K).Carrier) ∉
        ⋃ p, capFlagMap E p '' ball (0 : E3) 1 := fun h => y.property
          ((capFlagMap_holes E ⟨K, x⟩).mp h)
    exact ⟨⟨K, ⟨x, hx⟩⟩, rfl⟩
  letI : ∀ K, CompactSpace (X K) := fun K => by
    apply isCompact_iff_compactSpace.mp
    apply IsClosed.isCompact
    have hopen : IsOpen {x : (E.capped.component K).Carrier |
        (⟨K, x⟩ : Σ K, (E.capped.component K).Carrier) ∈
          ⋃ p, capFlagMap E p '' ball (0 : E3) 1} := by
      have heq : {x : (E.capped.component K).Carrier |
          (⟨K, x⟩ : Σ K, (E.capped.component K).Carrier) ∈
            ⋃ p, capFlagMap E p '' ball (0 : E3) 1} =
          (Subtype.val : (E.capped.component K).Carrier → E.capped.Carrier) ⁻¹'
            (⋃ p, (E.capping.capBallChart p).chart '' ball (0 : E3) 1) := by
        ext x
        exact capFlagMap_holes E ⟨K, x⟩
      rw [heq]
      exact (isOpen_iUnion fun p => (E.capping.capBallChart
          p).toBallChart.isOpen_chart_image_ball).preimage
        continuous_subtype_val
    exact hopen.isClosed_compl
  let := E.capped.finite_components
  let := Fintype.ofFinite (ConnectedComponents E.capped.Carrier)
  exact IsHomeomorph.homeomorph f (isHomeomorph_iff_continuous_bijective.mpr ⟨hf, hi, hs⟩)

@[simp] theorem puncturedCapComponentHomeomorph_val
    (x : Σ K, PairedBallGluing.PuncturedFactor E.capped.component E.cutCapVertex
      (fun e t => E.capComponentBallChart (e, t)) K) :
    (E.puncturedCapComponentHomeomorph x).val = x.snd.val.val := rfl


private abbrev S2 := sphere (0 : E3) 1

private abbrev hd := E.pairwise_disjoint_capComponentBallChart_image

private theorem puncturedCapComponentHomeomorph_boundary (a : E.tubes.Index) (t : Bool) (z : S2) :
    E.puncturedCapComponentHomeomorph
      ⟨E.cutCapVertex a t, PairedBallGluing.boundaryPoint E.capped.component E.cutCapVertex
        (fun a t => E.capComponentBallChart (a, t)) (hd E) a t z⟩ =
      E.capping.puncturedCapBoundary (a, t) z := by
  apply Subtype.ext
  exact (E.capComponentBallChart_apply_closedBall (a, t)
    (sphere_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) z.property)).trans
    (E.capping.puncturedCapBoundary_val (a, t) z).symm

private theorem puncturedCapping_symm_boundary (a : E.tubes.Index) (t : Bool) (z : S2) :
    E.capping.puncturedCappingHomeomorph.symm (E.capping.puncturedCapBoundary (a, t) z) =
      E.capping.innerCapBoundary a t (if t then z else -z) :=
  E.capping.puncturedCappingHomeomorph.symm_apply_apply _

private theorem boundaryAttachment_apply (z : S2) : boundaryAttachment.val z = -z := rfl

def pairedBallUncappingHomeomorph :
    Quot (fun x y => ∃ a, PairedBallGluing.seamRel E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) (hd E) a boundaryAttachment x y) ≃ₜ
      E.capping.UncappingQuotient := by
  let J := E.puncturedCapComponentHomeomorph.trans E.capping.puncturedCappingHomeomorph.symm
  have hB (a : E.tubes.Index) (t : Bool) (z : S2) :
      J ⟨E.cutCapVertex a t, PairedBallGluing.boundaryPoint E.capped.component E.cutCapVertex
        (fun a t => E.capComponentBallChart (a, t)) (hd E) a t z⟩ =
      E.capping.innerCapBoundary a t (if t then z else -z) := by
    change E.capping.puncturedCappingHomeomorph.symm (E.puncturedCapComponentHomeomorph _) = _
    rw [puncturedCapComponentHomeomorph_boundary, puncturedCapping_symm_boundary]
  apply Homeomorph.Quot.congr J
  intro x y
  constructor
  · rintro ⟨a, z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨a, -z, Or.inl ⟨hB a false z, by
        simpa only [ite_true, boundaryAttachment_apply] using
          hB a true (boundaryAttachment.val z)⟩⟩
    · exact ⟨a, -z, Or.inr ⟨hB a false z, by
        simpa only [ite_true, boundaryAttachment_apply] using
          hB a true (boundaryAttachment.val z)⟩⟩
  · rintro ⟨a, z, h | h⟩
    · refine ⟨a, -z, Or.inl ⟨J.injective ?_, J.injective ?_⟩⟩
      · exact h.1.trans (by simpa using (hB a false (-z)).symm)
      · exact h.2.trans (by simpa only [boundaryAttachment_apply, neg_neg, ite_true] using
          (hB a true (boundaryAttachment.val (-z))).symm)
    · refine ⟨a, -z, Or.inr ⟨J.injective ?_, J.injective ?_⟩⟩
      · exact h.1.trans (by simpa using (hB a false (-z)).symm)
      · exact h.2.trans (by simpa only [boundaryAttachment_apply, neg_neg, ite_true] using
          (hB a true (boundaryAttachment.val (-z))).symm)

@[simp] theorem pairedBallUncappingHomeomorph_mk
    (x : Σ K, PairedBallGluing.PuncturedFactor E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) K) :
    E.pairedBallUncappingHomeomorph (Quot.mk _ x) =
      E.capping.uncappingProjection (E.puncturedCapComponentHomeomorph x) := rfl

end DifferentialGeometry.Topology.SphericalCutCapTransition
