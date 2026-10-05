import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RestoredPlugPunctures
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugMarkedRestoration

/-!
The same recognised solid and its physical meridional germ restore the actual retained-collar
quotient. Its whole comparison with the original manifold supplies the puncture factor square.
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
local notation "Ki" => E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ
  (fibrePlugCutSideEquiv.symm t)
local notation "Eₜ" => RelativeSphereCapping.retained
  (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ (fibrePlugCutSideEquiv.symm t))

include h3 hι hr hΓ hb hbij hO in
theorem exists_plugMarkedFactorRestoration :
    let S := E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ
      (fibrePlugCutSideEquiv.symm t)
    let Ei := (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ
      (fibrePlugCutSideEquiv.symm t)).retained
    let : Nonempty K.Carrier := ⟨Γ.collar 0 (torusBase, halfZero)⟩
    let : Nonempty S.Carrier := E.boundedPlugMarkedSide_nonempty
      h hlin d hs hI heq hc hn hρ hρ1 havρ t
    ∃ (εs : Bool) (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier),
      g.preservesOrientation (solidAtlas.orientation planeCircleOrientation) S.orientation ∧
      ∃ (σ : ℝ) (hσ : 0 < σ), σ ≤ 1 ∧
      let ψ := E.boundedPlugMeridionalMarking h hlin εs
      (∀ p ∈ halfCollarSource,
        g (solidCollar 1 (p.1, halfSpaceScale hσ p.2)) =
          Ei.collar 0 (ψ p.1, halfSpaceScale hσ p.2)) ∧
      (∀ t : Torus, g (solidCollar 1 (t, halfZero)) = Ei.torusMap 0 (ψ t)) ∧
      ∃ ε : Bool,
      let f := markedRestorationMatching ψ ε
      ∃ hrev : ReversesBoundaryOrientation (withBoundarySum K S hK rfl)
        (boundaryPortLeftCollar K S hK rfl Γ)
        (fun p => boundaryPortRightCollar K S hK rfl Ei 0 (f p.1, p.2)),
      let P := boundaryPortPairing K S hK rfl Γ Ei f hrev
      ∃ H : P.QuotientSpace ≃ₜ M.Carrier,
        (∀ x : K.Carrier, H (P.quotientMap (Sum.inl x)) = ι x) ∧
        (∀ y : S.Carrier, H (P.quotientMap (Sum.inr y)) =
          regularFibreRestorationFill M φ ((markedRestorationSolidMap S g ε).symm y)) ∧
        ∀ θ : Circle, f (θ, 1) = (1, θ ^ (E.boundedSplitCharts h hlin).e₁) := by
  let : Nonempty K.Carrier := ⟨Γ.collar 0 (torusBase, halfZero)⟩
  let : Nonempty (Sₜ).Carrier := E.boundedPlugMarkedSide_nonempty
    h hlin d hs hI heq hc hn hρ hρ1 havρ t
  obtain ⟨εs, g, hg, σ, hσ, hσ1, _, hgσ, _⟩ :=
    E.exists_boundedPlugMeridionalDiffeomorph h hlin d hs hI heq hc hn hρ hρ1 havρ t
  let ψ := E.boundedPlugMeridionalMarking h hlin εs
  have hgc : ∀ p ∈ halfCollarSource,
      g (solidCollar 1 (p.1, halfSpaceScale hσ p.2)) =
        (Eₜ).collar 0 (ψ p.1, halfSpaceScale hσ p.2) := by
    intro p hp
    apply Subtype.ext
    have hps : (ψ p.1, halfSpaceScale hσ p.2) ∈ halfCollarSource :=
      halfSpaceScale_mem hσ hσ1 hp
    have hh := E.plugSideCapping_retained_apply h hlin d hs hI heq hc hn hρ hρ1 havρ
      (fibrePlugCutSideEquiv.symm t) (ψ p.1, halfSpaceScale hσ p.2) hps
    rw [E.fibrePlugCutPortEquiv_side h hc hn t] at hh
    have hψ : ψ p.1 = germHol
        ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
        (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁
          (p.1.1, if εs then p.1.2⁻¹ else p.1.2) := by
      cases εs <;> rfl
    rw [hψ] at hh ⊢
    exact (hgσ p hp).trans hh.symm
  have hz : ∀ p : Torus, g (solidCollar 1 (p, halfZero)) = (Eₜ).torusMap 0 (ψ p) := by
    intro p
    have hh := hgc (p, halfZero) (zero_mem_halfCollarSource p)
    simpa only [halfSpaceScale_halfZero, BoundaryTori.torusMap] using hh
  obtain ⟨ε, hrev, Q, q, e, he, hq, hleft, hright, hm⟩ :=
    exists_markedRegularFibreRestoration K (Sₜ) hK rfl Γ (Eₜ) g ψ hz
      M φ h3 ι hι hr hΓ hb hbij hO
  refine ⟨εs, g, hg, σ, hσ, hσ1, hgc, hz, ε, hrev, q.trans e.toHomeomorph,
    hleft, hright, ?_⟩
  intro θ
  exact (hm θ).trans (E.boundedPlugMeridionalMarking_meridian h hlin εs θ)

end GC.Seifert.ElementaryPresentation
