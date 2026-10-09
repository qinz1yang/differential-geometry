import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugMarkedFactorRestoration
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugCoreCollarTransport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MarkedCollarGermOrientation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RestoredPlugOrientedCharts

/-!
The canonical physical restoration supplies both reversals and the same oriented puncture.
No comparison homeomorphism or sphere compatibility is an input to this construction.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.Endpoint.CompactCarrier GC.GraphManifold.RelativeSphereCapping
open scoped Manifold ContDiff Topology

universe u
namespace GC.Seifert.ElementaryPresentation
open SplitTube

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
  (t : Bool)

variable (M : ConnectedClosedOrientedManifold.{u} 3)
  (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
    (PlaneLift.{u} × Circle) M.Carrier ∞)
  (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
  (K : CompactCarrier.{u}) (ι : K.Carrier → M.Carrier)
  (Γ : BoundaryTori K 1) (hK : K.kind = .withBoundary)
  (hι : IsSmoothEmbedding K.model (𝓡 3) ∞ ι)
  (hr : range ι = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ)
  (hΓ : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
    ι (Γ.collar 0 p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
  (hb : K.model.boundary K.Carrier = Γ.image)
  (hbij : ∀ x, Bijective (mfderiv K.model (𝓡 3) ι x))
  (hO : ∀ x, ∃ H : TangentSpace K.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι x),
    H.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι x ∧
    Orientation.map (Fin 3) H.toLinearEquiv (K.orientation.orientation x) =
      M.orientation.orientation (ι x))


local notation "Sₜ" => E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ
  (fibrePlugCutSideEquiv.symm t)
local notation "Kₜ" => E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ
  (fibrePlugCutSideEquiv.symm t)
local notation "Eₜ" => RelativeSphereCapping.retained
  (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ (fibrePlugCutSideEquiv.symm t))

local notation "Cₜ" => E.plugComponentCutCarrier h hlin d hs heq hc hn
  (fibrePlugCutSideEquiv.symm t)
local notation "Bₜ" => E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ
  (fibrePlugCutSideEquiv.symm t)

include h3 hι hr hΓ hb hbij hO in
theorem exists_canonicalRestoredPlugPuncture :
    let S := E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ
      (fibrePlugCutSideEquiv.symm t)
    let C := E.plugComponentCutCarrier h hlin d hs heq hc hn (fibrePlugCutSideEquiv.symm t)
    let B := E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ
      (fibrePlugCutSideEquiv.symm t)
    let Ki := E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ
      (fibrePlugCutSideEquiv.symm t)
    let : Nonempty K.Carrier := ⟨Γ.collar 0 (torusBase, halfZero)⟩
    let : Nonempty S.Carrier := E.plugCoreCapNonempty
      h hlin d hs hI heq hc hn hρ hρ1 havρ (fibrePlugCutSideEquiv.symm t)
    let : Nonempty C.Carrier := E.plugCoreCutNonempty
      h hlin d hs heq hc hn (fibrePlugCutSideEquiv.symm t)
    ∃ (εs : Bool) (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier) (ε : Bool),
    let ψ := E.boundedPlugMeridionalMarking h hlin εs
    let f := markedRestorationMatching ψ ε
    ∃ hr1 : ReversesBoundaryOrientation (withBoundarySum K S hK rfl)
      (boundaryPortLeftCollar K S hK rfl Γ)
      (fun p => boundaryPortRightCollar K S hK rfl Ki.retained 0 (f p.1, p.2)),
    ∃ hr0 : ReversesBoundaryOrientation (withBoundarySum K C hK rfl)
      (boundaryPortLeftCollar K C hK rfl Γ)
      (fun p => boundaryPortRightCollar K C hK rfl B.tori 0 (f p.1, p.2)),
    let P0 := boundaryCappingUncappedPairing K C hK rfl B rfl Γ f hr0
    let P1 := boundaryCappingCappedPairing K C S hK rfl B rfl Ki Γ f hr1
    ∃ (H : P1.QuotientSpace ≃ₜ M.Carrier)
      (c : OrientedBallChart M.toClosedOrientedManifold) (e : P0.QuotientSpace ≃ₜ c.Punctured),
      c.chart.source = Metric.ball 0 (5 / 2) ∧
      (∀ x, c.chart x = regularFibreRestorationFill M φ
        ((markedRestorationSolidMap S g ε).symm
          ((E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ
            (fibrePlugCutSideEquiv.symm t)).chart x))) ∧
      (∀ x : K.Carrier, H (P1.quotientMap (Sum.inl x)) = ι x) ∧
      (∀ y : S.Carrier, H (P1.quotientMap (Sum.inr y)) = regularFibreRestorationFill M φ
        ((markedRestorationSolidMap S g ε).symm y)) ∧
      (∀ x, (e x).val = H (boundaryCappingCore K C S hK rfl rfl B rfl Ki Γ f hr0 hr1 x)) ∧
      (∀ z : ClosureSphere.{u}, e (P0.quotientMap
        (Sum.inr (B.sphere 0 (Ki.attaching 0 z, halfZero)))) = c.boundaryMap z.down) ∧
      (∀ q : Torus, φ (ULift.up ((5 / 4 : ℝ) • (q.1 : ℂ)), q.2) ∈ c.toBallChart.interior) ∧
      ∀ θ : Circle, f (θ, 1) = (1, θ ^ (E.boundedSplitCharts h hlin).e₁)
 := by
  let : Nonempty K.Carrier := ⟨Γ.collar 0 (torusBase, halfZero)⟩
  let : Nonempty (Sₜ).Carrier := E.plugCoreCapNonempty
    h hlin d hs hI heq hc hn hρ hρ1 havρ (fibrePlugCutSideEquiv.symm t)
  let : Nonempty (Cₜ).Carrier := E.plugCoreCutNonempty
    h hlin d hs heq hc hn (fibrePlugCutSideEquiv.symm t)
  obtain ⟨εs, g, hg, σ, hσ, hσ1, hgc, hz, ε, hr1, H, hleft, hright, hm⟩ :=
    E.exists_plugMarkedFactorRestoration h hlin d hs hI heq hc hn hρ hρ1 havρ t
      M φ h3 K ι Γ hK hι hr hΓ hb hbij hO
  let ψ := E.boundedPlugMeridionalMarking h hlin εs
  let f := markedRestorationMatching ψ ε
  have hr0 := (plugCoreCollarTransport_reversal_iff (E := E) (h := h) (hlin := hlin)
    (d := d) (hs := hs) (hI := hI) (heq := heq) (hc := hc) (hn := hn) (hρ := hρ)
    (hρ1 := hρ1) (havρ := havρ) (i := fibrePlugCutSideEquiv.symm t) (C1 := K)
    (hC1 := hK) (l := Γ.collar 0) (f := f) (Γ.source_eq 0)).mpr hr1
  have hgu : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource → p.2.val 0 < σ →
      g (solidCollar 1 (p.1, halfSpaceScale (by norm_num : (0 : ℝ) < 1) p.2)) =
        (Eₜ).collar 0 (ψ p.1, p.2) := by
    intro p hp hpσ
    let q := (p.1, (halfSpaceScale hσ).symm p.2)
    have hqs : q ∈ halfCollarSource := by
      change ((halfSpaceScale hσ).symm p.2).val 0 < 1
      have hcq := halfSpaceScale_coord hσ ((halfSpaceScale hσ).symm p.2)
      rw [(halfSpaceScale hσ).apply_symm_apply] at hcq
      nlinarith
    have hq := hgc q hqs
    change g (solidCollar 1 (p.1, halfSpaceScale hσ ((halfSpaceScale hσ).symm p.2))) =
      (Eₜ).collar 0 (ψ p.1, halfSpaceScale hσ ((halfSpaceScale hσ).symm p.2)) at hq
    rw [(halfSpaceScale hσ).apply_symm_apply] at hq
    have hscale : halfSpaceScale (by norm_num : (0 : ℝ) < 1) p.2 = p.2 := by
      apply Subtype.ext
      ext k
      have hk : k = 0 := Subsingleton.elim k 0
      subst k
      simpa only [one_mul] using halfSpaceScale_coord (by norm_num : (0 : ℝ) < 1) p.2
    simpa only [hscale] using hq
  have hrmodel := markedCollarGermOrientation K (Sₜ) hK rfl Γ (Eₜ) g ψ
    1 (by norm_num) σ hσ hgu ε hr1
  obtain ⟨c, hcs, hcx, hcimage, hrad⟩ := E.exists_restoredPlugOrientedBallChart
    h hlin d hs hI heq hc hn hρ hρ1 havρ (fibrePlugCutSideEquiv.symm t) M φ h3
      K hK ι Γ hι.contMDiff hΓ hO g ψ ε hrmodel
  obtain ⟨c0, hc0s, hc0x, e0, he0, hbound⟩ := E.exists_restoredPlugPuncture
    h hlin d hs hI heq hc hn hρ hρ1 havρ (fibrePlugCutSideEquiv.symm t) K hK Γ f
      hr0 hr1 M φ h3 g ε H hright
  have hchart : (c0.chart : EuclideanSpace ℝ (Fin 3) → M.Carrier) = c.chart := by
    funext x
    exact (hc0x x).trans (hcx x).symm
  have hpunct : (c0.chart '' Metric.ball 0 1)ᶜ = (c.chart '' Metric.ball 0 1)ᶜ := by
    rw [hchart]
  let e := e0.trans (Homeomorph.setCongr hpunct)
  refine ⟨εs, g, ε, hr1, hr0, H, c, e, hcs, hcx, hleft, hright,
    fun x => he0 x, ?_, hrad, hm⟩
  intro z
  apply Subtype.ext
  change (e0 _).val = c.chart z.down.val
  have hh := congrArg Subtype.val (hbound z)
  change (e0 _).val = c0.chart z.down.val at hh
  exact hh.trans (congrFun hchart z.down.val)

end GC.Seifert.ElementaryPresentation
