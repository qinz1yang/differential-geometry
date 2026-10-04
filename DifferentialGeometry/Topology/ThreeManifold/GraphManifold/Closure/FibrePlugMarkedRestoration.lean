import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreMarkedRestoration
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugMeridian

/-!
The same recognised plug side supplies the actual marked solid and its retained collar for
regular-fibre restoration, without an input side model or an input reversing matching.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.Endpoint.CompactCarrier
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

abbrev boundedPlugMarkedSideCarrier : CompactCarrier.{u} :=
  GC.Topology.componentCarrier (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier
    (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ)
      (boundedPlugSideSolidIndex t)

instance boundedPlugMarkedSide_nonempty :
    Nonempty (E.boundedPlugMarkedSideCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ t).Carrier := by
  let D := E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ
  let := D.connected (boundedPlugSideSolidIndex t)
  exact inferInstanceAs (Nonempty (D.piece (boundedPlugSideSolidIndex t)))

def boundedPlugMeridionalMarking (ε : Bool) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  (if ε then boundaryPortSecondReflection else Diffeomorph.refl torusModel Torus ∞).trans
    (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
      (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁)

theorem boundedPlugMeridionalMarking_meridian (ε : Bool) (θ : Circle) :
    E.boundedPlugMeridionalMarking h hlin ε (θ, 1) =
      (1, θ ^ (E.boundedSplitCharts h hlin).e₁) := by
  let C := E.boundedSplitCharts h hlin
  cases ε
  · change germHol (C.e₀ * C.d) C.e₁ C.he₁ (θ, 1) = (1, θ ^ C.e₁)
    simp only [germHol_apply, inv_one, one_zpow, one_mul]
  · change germHol (C.e₀ * C.d) C.e₁ C.he₁ (θ, (1 : Circle)⁻¹) = (1, θ ^ C.e₁)
    rw [inv_one]
    simp only [germHol_apply, inv_one, one_zpow, one_mul]

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

set_option backward.isDefEq.respectTransparency false in
include h3 hι hr hΓ hb hbij hO in
theorem exists_boundedPlugMarkedRestoration
    (G : RawGraphPresentation (NoCuts.carrier M)) :
    let S := E.boundedPlugMarkedSideCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ t
    letI : Nonempty K.Carrier := ⟨Γ.collar 0 (torusBase, halfZero)⟩
    ∃ (εs : Bool) (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier),
      g.preservesOrientation (solidAtlas.orientation planeCircleOrientation) S.orientation ∧
      ∃ (σ : ℝ) (hσ : 0 < σ), σ ≤ 1 ∧
      let ψ := E.boundedPlugMeridionalMarking h hlin εs
      let Es := markedSolidBoundary S g ψ
      (∀ p ∈ halfCollarSource,
        (Es.collar 0 (ψ p.1, halfSpaceScale hσ p.2)).val =
          (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapRetained.collar
            (E.fibrePlugSideExternalEquiv h hc hn t) (ψ p.1, halfSpaceScale hσ p.2)) ∧
      ∃ ε : Bool,
      let f := markedRestorationMatching ψ ε
      ∃ hrev : ReversesBoundaryOrientation (withBoundarySum K S hK rfl)
        (boundaryPortLeftCollar K S hK rfl Γ)
        (fun p => boundaryPortRightCollar K S hK rfl Es 0 (f p.1, p.2)),
      let P := boundaryPortPairing K S hK rfl Γ Es f hrev
      ∃ (Q : ConnectedClosedOrientedManifold.{u} 3)
        (q : P.QuotientSpace ≃ₜ Q.Carrier)
        (e : Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier),
        e.preservesOrientation Q.orientation M.orientation ∧
        Nonempty (RawGraphPresentation (NoCuts.carrier Q)) ∧
        ContMDiff (withBoundarySum K S hK rfl).model (𝓡 3) ∞ (q ∘ P.quotientMap) ∧
        (∀ x : K.Carrier, e (q (P.quotientMap (Sum.inl x))) = ι x) ∧
        (∀ y : S.Carrier, e (q (P.quotientMap (Sum.inr y))) =
          regularFibreRestorationFill M φ ((markedRestorationSolidMap S g ε).symm y)) ∧
        ∀ θ : Circle, f (θ, 1) = (1, θ ^ (E.boundedSplitCharts h hlin).e₁) := by
  let S := E.boundedPlugMarkedSideCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ t
  let : Nonempty K.Carrier := ⟨Γ.collar 0 (torusBase, halfZero)⟩
  obtain ⟨εs, g, hg, σ, hσ, hσ1, hgc, hgs, hgm⟩ :=
    E.exists_boundedPlugMeridionalDiffeomorph h hlin d hs hI heq hc hn hρ hρ1 havρ t
  let ψ := E.boundedPlugMeridionalMarking h hlin εs
  let Es := markedSolidBoundary S g ψ
  have heqσ : ∀ p ∈ halfCollarSource,
      (Es.collar 0 (ψ p.1, halfSpaceScale hσ p.2)).val =
        (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapRetained.collar
          (E.fibrePlugSideExternalEquiv h hc hn t) (ψ p.1, halfSpaceScale hσ p.2) := by
    intro p hp
    rw [markedSolidBoundary_collar, ψ.symm_apply_apply]
    cases εs <;> exact hgs p hp
  obtain ⟨ε, hrev, Q, q, e, he, hG, hq, hl, hr, hm⟩ :=
    exists_modelMarkedRegularFibreRestoration K S hK rfl Γ g ψ M φ h3 ι hι hr hΓ hb hbij hO G
  refine ⟨εs, g, hg, σ, hσ, hσ1, heqσ, ε, hrev, Q, q, e, he, hG, hq, hl, hr, ?_⟩
  intro θ
  rw [hm θ]
  exact E.boundedPlugMeridionalMarking_meridian h hlin εs θ

end GC.Seifert.ElementaryPresentation
