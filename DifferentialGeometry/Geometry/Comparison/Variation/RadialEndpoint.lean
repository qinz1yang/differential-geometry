import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Comparison.Variation.EndpointParallel
import DifferentialGeometry.Geometry.Comparison.Variation.ExponentialEndpoint
import DifferentialGeometry.Geometry.Comparison.Variation.RadialIndex

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

structure RadialEndpointVariation
    (g : SmoothRiemannianMetric I M) (gamma beta : ℝ → M) (L : ℝ) where
  baseCurve : ℝ → M
  parallelField : ∀ t, TangentSpace I (baseCurve t)
  radialField : ∀ t, TangentSpace I (baseCurve t)
  variation : ℝ → ℝ → M
  smooth : IsSmoothVariation (I := I) variation
  central : ∀ t : ℝ, variation 0 t = baseCurve t
  agrees : ∀ t ∈ Set.Icc (0 : ℝ) L, baseCurve t = gamma t
  agreesGerm : ∀ t ∈ Set.Icc (0 : ℝ) L, baseCurve =ᶠ[𝓝 t] gamma
  parallelDifferentiable : ∀ t ∈ Set.Icc (0 : ℝ) L,
    DifferentiableAt ℝ (chartRepAt (I := I) baseCurve parallelField t) t
  parallelCovDeriv : ∀ t ∈ Set.Icc (0 : ℝ) L,
    covDerivAlong (I := I) g baseCurve parallelField t = 0
  parallelTerminalVelocity :
    (parallelField L : E) =
      mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)
  centralGeodesic : IsGeodesicOn (I := I) g
    (fun t : ℝ ↦ variation 0 t) (Set.Icc 0 L)
  centralUnitSpeed : ∀ t ∈ Set.Icc (0 : ℝ) L,
    g.inner (variation 0 t)
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ variation 0 u) t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ variation 0 u) t (1 : ℝ)) = 1
  fixedInitial : ∀ s : ℝ, variation s 0 = variation 0 0
  terminalGerm : (fun s : ℝ ↦ variation s L) =ᶠ[𝓝 (0 : ℝ)] beta
  terminalGeodesic : HasGeodesicEquationAt (I := I) g
    (fun s : ℝ ↦ variation s L) 0
  centralField : ∀ t : ℝ,
    centralVariationField (I := I) variation t = radialField t
  radialValue : ∀ t ∈ Set.Icc (0 : ℝ) L,
    radialField t = (t / L) • parallelField t
  radialCovDeriv : ∀ t ∈ Set.Icc (0 : ℝ) L,
    covDerivAlong (I := I) g baseCurve radialField t =
      (1 / L) • parallelField t
  parallelUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
    g.inner (baseCurve t) (parallelField t) (parallelField t) = 1

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_radialEndpointVariation
    (g : SmoothRiemannianMetric I M)
    (gamma beta : ℝ → M) (L : ℝ) (hL : 0 < L)
    (hgammaSmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hgammaGeo : IsGeodesicOn (I := I) g gamma (Set.Icc 0 L))
    (hgammaUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (gamma t)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)) = 1)
    (vL : TangentSpace I (gamma L))
    (hvLunit : g.inner (gamma L) vL vL = 1)
    (hbetaGeo : IsGeodesicAt (I := I) g beta 0)
    (hbeta0 : beta 0 = gamma L)
    (hbetaVel : (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ) : E) = vL) :
    Nonempty (RadialEndpointVariation (I := I) g gamma beta L) := by
  classical
  obtain ⟨Gamma, V, hVtotal, hGamma, hGammaGerm, hterminalV,
      hVdiff, hVpar, hVunit, W, hWtotal, hWradial, hWcov,
      K, hKcompact, hWmem⟩ :=
    exists_smooth_parallel_unit_field_with_terminal
      (I := I) g gamma hgammaSmooth L hL vL hvLunit
  obtain ⟨_eta, f, _hetaSmooth, _hetaId, _hetaBound, hf, hfcentral,
      hfField, hfFix, hfTerminal⟩ :=
    exists_clamped_geodesic_variation_on_compactCarrier
      (I := I) g Gamma (fun t : ℝ ↦ (W t : E)) L Set.univ K
      hWtotal hKcompact (fun t _ht ↦ hWmem t) (Set.mem_univ L)
  have hW0 : W 0 = 0 := by
    rw [hWradial 0 ⟨le_rfl, hL.le⟩]
    simp
  have hfixedGamma : ∀ s : ℝ, f s 0 = Gamma 0 := hfFix hW0
  have hfixed : ∀ s : ℝ, f s 0 = f 0 0 := by
    intro s
    rw [hfixedGamma s, hfcentral 0]
  have hVL : (V L : E) = vL := by
    exact congrArg (fun q : TangentBundle I M ↦ q.snd) hterminalV
  have hWL : (W L : E) = vL := by
    rw [hWradial L ⟨hL.le, le_rfl⟩]
    simpa [hL.ne'] using hVL
  have hbeta0Gamma : beta 0 = Gamma L :=
    hbeta0.trans (hGamma L ⟨hL.le, le_rfl⟩).symm
  have hbetaVelW :
      (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ) : E) = W L :=
    hbetaVel.trans hWL.symm
  obtain ⟨B, hBproj, hBint, hB0⟩ :=
    exists_centered_lift_of_isGeodesicAt (I := I) g beta (Gamma L) (W L)
      hbetaGeo hbeta0Gamma hbetaVelW
  have hterminalGerm : (fun s : ℝ ↦ f s L) =ᶠ[𝓝 (0 : ℝ)] beta :=
    hfTerminal beta B hBproj hBint hB0
  have hterminalGeo : HasGeodesicEquationAt (I := I) g
      (fun s : ℝ ↦ f s L) 0 := by
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
      hterminalGerm.self_of_nhds hterminalGerm
      hbetaGeo.hasGeodesicEquationAt
  have hGammaGeo : IsGeodesicOn (I := I) g Gamma (Set.Icc 0 L) := by
    intro t ht
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (hGamma t ht) (hGammaGerm t ht) (hgammaGeo t ht)
  have hcentralEq : (fun t : ℝ ↦ f 0 t) = Gamma := funext hfcentral
  have hfGeo : IsGeodesicOn (I := I) g
      (fun t : ℝ ↦ f 0 t) (Set.Icc 0 L) := by
    rw [hcentralEq]
    exact hGammaGeo
  have hGammaUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (Gamma t)
        (mfderiv 𝓘(ℝ, ℝ) I Gamma t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I Gamma t (1 : ℝ)) = 1 := by
    intro t ht
    rw [hGamma t ht, (hGammaGerm t ht).mfderiv_eq]
    exact hgammaUnit t ht
  have hfUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (f 0 t)
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ f 0 u) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ f 0 u) t (1 : ℝ)) = 1 := by
    intro t ht
    rw [hcentralEq, hfcentral t]
    exact hGammaUnit t ht
  have hcentralField : ∀ t : ℝ,
      centralVariationField (I := I) f t = W t := by
    intro t
    exact hfField t (Set.mem_univ t)
  exact ⟨{
    baseCurve := Gamma
    parallelField := V
    radialField := W
    variation := f
    smooth := hf
    central := hfcentral
    agrees := hGamma
    agreesGerm := hGammaGerm
    parallelDifferentiable := hVdiff
    parallelCovDeriv := hVpar
    parallelTerminalVelocity := hVL.trans hbetaVel.symm
    centralGeodesic := hfGeo
    centralUnitSpeed := hfUnit
    fixedInitial := hfixed
    terminalGerm := hterminalGerm
    terminalGeodesic := hterminalGeo
    centralField := hcentralField
    radialValue := hWradial
    radialCovDeriv := hWcov
    parallelUnit := hVunit
  }⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem RadialEndpointVariation.secondVariation_half_energy_le_inv
    {g : SmoothRiemannianMetric I M} {gamma beta : ℝ → M}
    {L : ℝ} (D : RadialEndpointVariation (I := I) g gamma beta L)
    (hL : 0 < L)
    (hcurv : ∀ t ∈ Set.Icc (0 : ℝ) L,
      0 ≤ g.inner (D.variation 0 t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita
              (I := I) g) (D.variation 0 t))
          (D.parallelField t)
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ ↦ D.variation 0 u) t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ ↦ D.variation 0 u) t (1 : ℝ)))
        (D.parallelField t)) :
    deriv
      (fun s : ℝ => deriv
        (fun r : ℝ => (1 / 2 : ℝ) *
          curveEnergy (I := I) g
            (fun t : ℝ => D.variation r t) 0 L) s) 0 ≤
      1 / L := by
  have hbaseEq : (fun t : ℝ ↦ D.variation 0 t) = D.baseCurve :=
    funext D.central
  apply secondVariation_half_curveEnergy_deriv_le_inv_of_radial_data
    (I := I) (M := M) g D.variation D.parallelField L D.smooth hL
      D.centralGeodesic D.fixedInitial D.terminalGeodesic
  · intro t ht
    exact (D.centralField t).trans (D.radialValue t ht)
  · intro t ht
    have hfieldEq :
        (fun u : ℝ ↦ centralVariationField (I := I) D.variation u) =
          (fun u : ℝ ↦ D.radialField u) :=
      funext D.centralField
    rw [hfieldEq, hbaseEq]
    exact D.radialCovDeriv t ht
  · intro t ht
    rw [D.central t]
    exact D.parallelUnit t ht
  · exact hcurv

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

namespace Poincare.Geometry.Riemannian.Variation

@[reducible] alias RadialEndpointVariation := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation
alias exists_radialEndpointVariation := DifferentialGeometry.Geometry.Riemannian.Variation.exists_radialEndpointVariation
end Poincare.Geometry.Riemannian.Variation

namespace Poincare.Geometry.Riemannian.Variation.RadialEndpointVariation

alias secondVariation_half_energy_le_inv := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.secondVariation_half_energy_le_inv
@[reducible] alias mk := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.mk
alias baseCurve := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.baseCurve
alias parallelField := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.parallelField
alias radialField := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.radialField
alias variation := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.variation
alias smooth := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.smooth
alias central := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.central
alias agrees := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.agrees
alias agreesGerm := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.agreesGerm
alias parallelDifferentiable := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.parallelDifferentiable
alias parallelCovDeriv := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.parallelCovDeriv
alias parallelTerminalVelocity := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.parallelTerminalVelocity
alias centralGeodesic := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.centralGeodesic
alias centralUnitSpeed := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.centralUnitSpeed
alias fixedInitial := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.fixedInitial
alias terminalGerm := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.terminalGerm
alias terminalGeodesic := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.terminalGeodesic
alias centralField := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.centralField
alias radialValue := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.radialValue
alias radialCovDeriv := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.radialCovDeriv
alias parallelUnit := DifferentialGeometry.Geometry.Riemannian.Variation.RadialEndpointVariation.parallelUnit

end Poincare.Geometry.Riemannian.Variation.RadialEndpointVariation
