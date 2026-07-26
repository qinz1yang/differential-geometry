import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.UhlenbeckBaseProducer

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Lowered-Riemann variation in second-Ricci-derivative form

This module normalizes the arbitrary-dimensional lowered-Riemann time
derivative from coordinate Christoffel variation terms to the canonical
`nablaGammaDtFromNabla2RicInFrame` expression.  It does not perform the later
Bianchi contraction or Ricci-commutator calculation.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle Set
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- The arbitrary-dimensional coordinate-frame variation of lowered Riemann
after replacing the covariant derivative of the Christoffel variation by its
explicit `∇²Ric` expression. -/
def rm04VarRHS
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M)
    (nabla2Ric :
      Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
        CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (t : Real) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) : Real :=
  ∑ p : CoordinateIdx (𝕜 := Real) E,
    ((nablaGammaDtFromNabla2RicInFrame
          (M := M) (coordInv (I := I) S x₀) nabla2Ric
          t x₀ (m 0) p (m 1) (m 2) -
        nablaGammaDtFromNabla2RicInFrame
          (M := M) (coordInv (I := I) S x₀) nabla2Ric
          t x₀ (m 1) p (m 0) (m 2)) *
        metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
          t x₀ (m 3) p +
      DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
          (I := I) (S.family.connection t) x₀ (m 0) (m 1) (m 2) p *
        ((-2 : Real) *
          ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
            t x₀ (m 3) p))

/-- Along a Ricci-flow solution, the time derivative of the canonical
coordinate component of lowered Riemann is `rm04VarRHS`, the explicit
arbitrary-dimensional `∇²Ric` variation formula. -/
theorem rm04Var_of_sol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (gInvDt :
      Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (nabla2Ric :
      Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
        CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (hmetricReg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S (coordInv (I := I) S x₀) gInvDt
        (coordinateFrameAt (I := I) x₀) (coordinateFrameSet (I := I) x₀))
    (hnablaReg :
      Nabla2RicciComponentsRegularInFrameOnLocal
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
        nabla2Ric)
    (hmix :
      ChristoffelVariationMixedDerivativeInFrameOnRegular
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (christoffelEvolutionRHSInFrame
          (M := M) (coordInv (I := I) S x₀)
          (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))))
    (hRm : ∀ s, s ∈ D.carrier →
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection
        (I := I) (S.family.connection s) (S.base.rm13 s))
    (hcurv : ∀ s, s ∈ D.carrier →
      DifferentialGeometry.Integral.Connection.ConnectionCurvatureCoordAt
        (I := I) (S.family.connection s) x₀)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real ↦ realizedRmBase (I := I) S x₀ s x₀ m)
      (rm04VarRHS (I := I) S x₀ nabla2Ric (t : Real) m)
      D.carrier (t : Real) := by
  classical
  let frame := coordinateFrameAt (I := I) x₀
  let u := coordinateFrameSet (I := I) x₀
  have hu : IsOpen u := coordinateFrameSet_open (I := I) x₀
  have hx₀ : x₀ ∈ u := coordinateFrameAt_mem (I := I) x₀
  have hRhs
      (s : Real) {x : M} (hx : x ∈ u)
      (i j k : CoordinateIdx (𝕜 := Real) E) :
      christoffelEvolutionRHSInFrame
          (M := M) (coordInv (I := I) S x₀)
          (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
          s x i j k =
        christoffelEvolutionRHSInFrame
          (M := M) (coordInv (I := I) S x₀)
          (fun t y d a b ↦
            ricciCovDerivCompInFrame
              (I := I) S (coordinateFrameAt (I := I) x₀) t y d a b)
          s x i j k := by
    unfold christoffelEvolutionRHSInFrame christoffelVariationLoweredRHSInFrame
    refine Finset.sum_congr rfl fun l _hl ↦ ?_
    rw [coordNablaRealOn (I := I) S x₀ s x hx i j l,
      coordNablaRealOn (I := I) S x₀ s x hx j i l,
      coordNablaRealOn (I := I) S x₀ s x hx l i j]
  have hmixLegacy :
      ChristoffelVariationMixedDerivativeInFrameOnRegular
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (christoffelEvolutionRHSInFrame
          (M := M) (coordInv (I := I) S x₀)
          (fun t x d a b ↦
            ricciCovDerivCompInFrame
              (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b)) := by
    intro i j k s hs x hx V
    have hEq :
        (fun y : M ↦
          christoffelEvolutionRHSInFrame
            (M := M) (coordInv (I := I) S x₀)
            (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
            s y i j k) =ᶠ[nhds x]
          (fun y : M ↦
            christoffelEvolutionRHSInFrame
              (M := M) (coordInv (I := I) S x₀)
              (fun t z d a b ↦
                ricciCovDerivCompInFrame
                  (I := I) S (coordinateFrameAt (I := I) x₀) t z d a b)
              s y i j k) :=
      by
        filter_upwards [hu.mem_nhds hx] with y hy
        exact hRhs s hy i j k
    exact (hmix i j k s hs x hx V).congr_deriv
      (extDerivFun_eventuallyEq_congr (I := I) V hEq)
  have hmetricFrame :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S (coordInv (I := I) S x₀) gInvDt frame u :=
    hmetricReg.toMetricFrameTimeRegularityInFrameOnLocal
  have hSmooth :
      ∀ a b : CoordinateIdx (𝕜 := Real) E, ∀ s, s ∈ D.regular →
        ∀ x : M, x ∈ u →
          ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
            (fun q : Real × M ↦
              (S.family.metric q.1).inner q.2 (frame a q.2) (frame b q.2)) (s, x) := by
    intro a b s hs x hx
    have hOn := (hmetricReg.frameMetricSpacetimeSmooth a b).mono
      (Set.prod_mono D.regular_subset (Set.Subset.rfl))
    exact (hOn.contMDiffAt ((D.regular_isOpen.prod hu).mem_nhds ⟨hs, hx⟩)).of_le
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have hFdiff :
      ∀ a b : CoordinateIdx (𝕜 := Real) E, ∀ s, s ∈ D.carrier →
        ∀ x : M, x ∈ u →
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M ↦
              (S.family.metric s).inner y (frame a y) (frame b y)) x := by
    intro a b s hs x hx
    have hslice :
        ContMDiffOn I (𝓘(Real, Real).prod I) ∞
          (fun y : M ↦ (s, y)) u :=
      (contMDiffOn_const (c := s)).prodMk contMDiffOn_id
    have hcomp := (hmetricReg.frameMetricSpacetimeSmooth a b).comp hslice
      (fun y hy ↦ ⟨hs, hy⟩)
    have hdiff :=
      (hcomp.contMDiffAt (hu.mem_nhds hx)).mdifferentiableAt (by simp)
    simpa [Function.comp_def, metricCompInFrame, frame] using hdiff
  have hFtdiff :
      ∀ a b : CoordinateIdx (𝕜 := Real) E, ∀ s, s ∈ D.regular →
        ∀ x : M, x ∈ u →
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M ↦
              ricciCompInFrame (I := I) S frame s y a b) x := by
    intro a b s _hs x hx
    simpa [frame, u] using coordRicciMdiff (I := I) S x₀ s x hx a b
  have hbase :=
    realizedRmBase_timeDeriv
      (I := I) S hS x₀ gInvDt hmetricFrame hSmooth hFdiff hFtdiff hmixLegacy
      hRm hcurv t m
  have hgamma
      (d k i j : CoordinateIdx (𝕜 := Real) E) :
      christoffelVariationCovDerivCoordAt
          (I := I) (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame
            (M := M) (coordInv (I := I) S x₀)
            (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀)))
          (t : Real) x₀ d k i j =
        nablaGammaDtFromNabla2RicInFrame
          (M := M) (coordInv (I := I) S x₀) nabla2Ric
          (t : Real) x₀ d k i j := by
    exact
      christoffelVariationCovDerivCoordAt_eq_nablaGammaDtFromNabla2RicInFrame
        (I := I) S (coordInv (I := I) S x₀)
        (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
        nabla2Ric x₀ gInvDt hmetricReg hnablaReg t d k i j
  have hgammaLegacy
      (d k i j : CoordinateIdx (𝕜 := Real) E) :
      christoffelVariationCovDerivCoordAt
          (I := I) (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame
            (M := M) (coordInv (I := I) S x₀)
            (fun τ y a b c ↦
              ricciCovDerivCompInFrame
                (I := I) S (coordinateFrameAt (I := I) x₀) τ y a b c))
          (t : Real) x₀ d k i j =
        nablaGammaDtFromNabla2RicInFrame
          (M := M) (coordInv (I := I) S x₀) nabla2Ric
          (t : Real) x₀ d k i j := by
    calc
      _ = christoffelVariationCovDerivCoordAt
          (I := I) (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame
            (M := M) (coordInv (I := I) S x₀)
            (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀)))
          (t : Real) x₀ d k i j := by
            unfold christoffelVariationCovDerivCoordAt
            have hEq :
                (fun y : M ↦
                  christoffelEvolutionRHSInFrame
                    (M := M) (coordInv (I := I) S x₀)
                    (fun τ z a b c ↦
                      ricciCovDerivCompInFrame
                        (I := I) S (coordinateFrameAt (I := I) x₀) τ z a b c)
                    (t : Real) y i j k) =ᶠ[nhds x₀]
                  (fun y : M ↦
                    christoffelEvolutionRHSInFrame
                      (M := M) (coordInv (I := I) S x₀)
                      (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
                      (t : Real) y i j k) :=
              by
                filter_upwards [hu.mem_nhds hx₀] with y hy
                exact (hRhs (t : Real) hy i j k).symm
            rw [extDerivFun_eventuallyEq_congr
              (I := I) (coordinateFrameAt (I := I) x₀ d x₀) hEq]
            simp_rw [← hRhs (t : Real) hx₀]
      _ = _ := hgamma d k i j
  refine hbase.congr_deriv ?_
  unfold rm04VarRHS
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [hgammaLegacy (m 0) p (m 1) (m 2), hgammaLegacy (m 1) p (m 0) (m 2)]

end DifferentialGeometry.PDE.RicciFlow
