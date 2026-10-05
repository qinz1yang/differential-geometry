import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugCutFactorGeometry
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutCapMarking
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ConnectedSumFold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierSum

/-!
The same physical plug zero copies give the antipodal boundary relation of its punctured factors.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.Endpoint.CompactCarrier
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert.ElementaryPresentation
variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))
  (hc : E.toTorus.components.count = 2) (hn : E.toTorus.pairing.count = 1)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
  (havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)


local notation "Cᵢ" i => E.plugComponentCutCarrier h hlin d hs heq hc hn i
local notation "Bᵢ" i => E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "Kᵢ" i => E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "zᵢ" i => E.plugCutFactorZero h hlin d hs heq hc hn i
local notation "B₀" => E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ

theorem plugPuncturedFactor_sphere_zero (i : Fin 2) (z : ClosureSphere.{u}) :
    (Bᵢ i).sphere 0 (z, halfZero) = (zᵢ i) z := by
  apply Subtype.ext
  have hz := E.plugSideBoundary_sphere_zero h hlin d hs hI heq hc hn hρ hρ1 havρ i z
  change ((Bᵢ i).sphere 0 (z, halfZero)).val = _ at hz
  exact hz.trans (sphereCutFullCollar_zero (boundedPlugCutCollars d)
    (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
    0 (sphereCutBoundarySide i) z)

theorem plugPuncturedFactor_attaching_antipodal (z : ClosureSphere.{u}) :
    ((Kᵢ (1 : Fin 2)).attaching 0).symm ((Kᵢ (0 : Fin 2)).attaching 0 z) =
      ULift.up (boundaryAttachment.1 z.down) := by
  have ha := sphereCutCapMarking_antipodal (boundedPlugCutCollars d)
    (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
    (Function.const (Fin 1) hI) (E.toTorus.external.shrink hρ hρ1)
    (E.toTorus.external_exhausted.trans
      (E.toTorus.external.shrink_image hρ hρ1).symm)
    (fun i => Function.const (Fin 1) (havρ i))
  change ((B₀).sphereCapOrientationData.attaching (0 : Fin 2)).symm.trans
    ((B₀).sphereCapOrientationData.attaching (1 : Fin 2)) = sphereCapBoundaryReflection at ha
  let a0 := (Kᵢ (0 : Fin 2)).attaching 0
  let a1 := (Kᵢ (1 : Fin 2)).attaching 0
  change a0.symm.trans a1 = sphereCapBoundaryReflection at ha
  change a1.symm (a0 z) = ULift.up (boundaryAttachment.1 z.down)
  apply a1.injective
  change a1 (a1.symm (a0 z)) = a1 (ULift.up (boundaryAttachment.1 z.down))
  rw [Diffeomorph.apply_symm_apply]
  have hanti : ULift.up (boundaryAttachment.1 z.down) = sphereCapBoundaryReflection z := rfl
  rw [hanti]
  have hp := congrArg (fun a => a (a0 (sphereCapBoundaryReflection z))) ha
  change a1 (a0.symm (a0 (sphereCapBoundaryReflection z))) =
    sphereCapBoundaryReflection (a0 (sphereCapBoundaryReflection z)) at hp
  rw [Diffeomorph.symm_apply_apply] at hp
  rw [hp]
  rcases (B₀).sphereCapOrientationData.choices (0 : Fin 2) with h0 | h0
  · have he0 : a0 = Diffeomorph.refl (𝓡 2) ClosureSphere.{u} ∞ := h0.2
    rw [he0]
    apply ULift.ext
    apply Subtype.ext
    exact (neg_neg _).symm
  · have he0 : a0 = sphereCapBoundaryReflection := h0.2
    rw [he0]
    apply ULift.ext
    apply Subtype.ext
    change -z.down.val = - - -z.down.val
    rw [neg_neg]

section Punctures
variable (M N : ConnectedClosedOrientedManifold.{u} 3)
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d1 : OrientedBallChart N.toClosedOrientedManifold)
  (K0 K1 : CompactCarrier.{u}) (hK0 : K0.kind = .withBoundary)
  (hK1 : K1.kind = .withBoundary)
  (P0 : TorusPairing (withBoundarySum K0 (E.plugComponentCutCarrier h hlin d hs heq hc hn
    (0 : Fin 2)) hK0 rfl))
  (P1 : TorusPairing (withBoundarySum K1 (E.plugComponentCutCarrier h hlin d hs heq hc hn
    (1 : Fin 2)) hK1 rfl))
  (eL : P0.QuotientSpace ≃ₜ c.toBallChart.Punctured)
  (eR : P1.QuotientSpace ≃ₜ d1.toBallChart.Punctured)
  (heL : ∀ z : ClosureSphere.{u},
    eL (P0.quotientMap (Sum.inr ((E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ (0 :
      Fin 2)).sphere 0
      ((E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ (0 : Fin 2)).attaching 0 z,
      halfZero)))) = c.toBallChart.boundaryMap z.down)
  (heR : ∀ z : ClosureSphere.{u},
    eR (P1.quotientMap (Sum.inr ((E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ (1 :
      Fin 2)).sphere 0
      ((E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ (1 : Fin 2)).attaching 0 z,
      halfZero)))) = d1.toBallChart.boundaryMap z.down)

include heL in
private theorem puncturedLeft_coordinate (z : ClosureSphere.{u}) :
    eL (P0.quotientMap (Sum.inr ((zᵢ(0 : Fin 2)) z))) =
      c.toBallChart.boundaryMap (((Kᵢ (0 : Fin 2)).attaching 0).symm z).down := by
  have hz := heL (((Kᵢ (0 : Fin 2)).attaching 0).symm z)
  rw [Diffeomorph.apply_symm_apply,
    E.plugPuncturedFactor_sphere_zero h hlin d hs hI heq hc hn hρ hρ1 havρ] at hz
  exact hz

include heR in
private theorem puncturedRight_coordinate (z : ClosureSphere.{u}) :
    eR (P1.quotientMap (Sum.inr ((zᵢ(1 : Fin 2)) z))) =
      d1.toBallChart.boundaryMap (((Kᵢ (1 : Fin 2)).attaching 0).symm z).down := by
  have hz := heR (((Kᵢ (1 : Fin 2)).attaching 0).symm z)
  rw [Diffeomorph.apply_symm_apply,
    E.plugPuncturedFactor_sphere_zero h hlin d hs hI heq hc hn hρ hρ1 havρ] at hz
  exact hz

variable {Q : Type u} [TopologicalSpace Q]
  (L : C(P0.QuotientSpace, Q)) (R : C(P1.QuotientSpace, Q))

def plugPuncturedFactorLeft : C(c.toBallChart.Punctured, Q) :=
  L.comp ⟨eL.symm, eL.symm.continuous⟩

def plugPuncturedFactorRight : C(d1.toBallChart.Punctured, Q) :=
  R.comp ⟨eR.symm, eR.symm.continuous⟩

variable {E h hlin d hs hI heq hc hn hρ hρ1 havρ M N c d1 K0 K1 hK0 hK1 P0 P1 eL eR L R}

include heL heR in
theorem plugPuncturedFactor_boundary_cross
    (hcross : ∀ x y, L x = R y ↔ ∃ z : ClosureSphere.{u},
      x = P0.quotientMap (Sum.inr ((zᵢ(0 : Fin 2)) z)) ∧
      y = P1.quotientMap (Sum.inr ((zᵢ(1 : Fin 2)) z))) :
    ∀ {x y}, L (eL.symm x) = R (eR.symm y) ↔ ∃ z,
      c.toBallChart.boundaryMap z = x ∧
      d1.toBallChart.boundaryMap (boundaryAttachment.1 z) = y := by
  intro x y
  constructor
  · intro hxy
    rcases (hcross _ _).mp hxy with ⟨z, hl, hr⟩
    let a := ((Kᵢ (0 : Fin 2)).attaching 0).symm z
    refine ⟨a.down, ?_, ?_⟩
    · have hh := E.puncturedLeft_coordinate h hlin d hs hI heq hc hn hρ hρ1 havρ
        M c K0 hK0 P0 eL heL z
      exact hh.symm.trans ((congrArg eL hl).symm.trans (eL.apply_symm_apply x))
    · have hh := E.puncturedRight_coordinate h hlin d hs hI heq hc hn hρ hρ1 havρ
        N d1 K1 hK1 P1 eR heR z
      have ha := E.plugPuncturedFactor_attaching_antipodal
        h hlin d hs hI heq hc hn hρ hρ1 havρ a
      have hz : (Kᵢ (0 : Fin 2)).attaching 0 a = z := Diffeomorph.apply_symm_apply _ z
      rw [hz] at ha
      rw [ha] at hh
      exact hh.symm.trans ((congrArg eR hr).symm.trans (eR.apply_symm_apply y))
  · rintro ⟨z, rfl, rfl⟩
    let raw := (Kᵢ (0 : Fin 2)).attaching 0 (ULift.up z)
    apply (hcross _ _).mpr
    refine ⟨raw, ?_, ?_⟩
    · apply eL.injective
      rw [eL.apply_symm_apply]
      have hh := E.puncturedLeft_coordinate h hlin d hs hI heq hc hn hρ hρ1 havρ
        M c K0 hK0 P0 eL heL raw
      simpa only [raw, Diffeomorph.symm_apply_apply] using hh.symm
    · apply eR.injective
      rw [eR.apply_symm_apply]
      have hh := E.puncturedRight_coordinate h hlin d hs hI heq hc hn hρ hρ1 havρ
        N d1 K1 hK1 P1 eR heR raw
      rw [show ((Kᵢ (1 : Fin 2)).attaching 0).symm raw =
        ULift.up (boundaryAttachment.1 z) from E.plugPuncturedFactor_attaching_antipodal
          h hlin d hs hI heq hc hn hρ hρ1 havρ (ULift.up z)] at hh
      exact hh.symm

theorem plugPuncturedFactor_transport
    (hiL : Injective L) (hiR : Injective R) (hcover : range L ∪ range R = univ) :
    Continuous (fun x => L (eL.symm x)) ∧ Continuous (fun y => R (eR.symm y)) ∧
      Injective (fun x => L (eL.symm x)) ∧ Injective (fun y => R (eR.symm y)) ∧
      range (fun x => L (eL.symm x)) ∪ range (fun y => R (eR.symm y)) = univ := by
  refine ⟨L.continuous.comp eL.symm.continuous, R.continuous.comp eR.symm.continuous,
    hiL.comp eL.symm.injective, hiR.comp eR.symm.injective, ?_⟩
  have hleft : range (fun x => L (eL.symm x)) = range L := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨eL.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨eL x, congrArg L (eL.symm_apply_apply x)⟩
  have hright : range (fun y => R (eR.symm y)) = range R := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨eR.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨eR x, congrArg R (eR.symm_apply_apply x)⟩
  rw [hleft, hright]
  exact hcover

end Punctures

end GC.Seifert.ElementaryPresentation
