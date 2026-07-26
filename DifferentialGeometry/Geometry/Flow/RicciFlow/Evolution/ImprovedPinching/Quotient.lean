import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.TfHeatCore

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Improved pinching Quotient

Split-out component of `DifferentialGeometry.PDE.RicciFlow.Evolution.ImprovedPinching`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped Manifold ContDiff BigOperators
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-! ## Lemma 10.5: scalar quotient evolution -/

/-- The scalar quotient field in Lemma 10.5, written as
`phi^alpha * psi^(-beta)`.  On the positive `psi` region this is the book's
`phi^alpha / psi^beta`, but the negative-power form is the stable calculus
normal form. -/
def quotField
    (phi psi : Real -> M -> Real) (alpha beta : Real) :
    Real -> M -> Real :=
  fun t x => phi t x ^ alpha * psi t x ^ (-beta)

/-- Canonical spatial Laplacian of the quotient field. -/
def quotLap
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi : Real -> M -> Real) (alpha beta : Real) :
    Real -> M -> Real :=
  fun t x =>
    DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
      (quotField (M := M) phi psi alpha beta t) x

/-- Right-hand side of Lemma 10.5 for
`(partial_t - Delta) (phi^alpha psi^(-beta))`.

The `phiHeat` and `psiHeat` inputs are the already-subtracted heat operator
values `(partial_t - Delta) phi` and `(partial_t - Delta) psi`. -/
def quotHeatRHS
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real) : Real -> M -> Real :=
  fun t x =>
    alpha * phi t x ^ (alpha - 1) * psi t x ^ (-beta) *
        phiHeat t x -
      beta * phi t x ^ alpha * psi t x ^ (-beta - 1) *
        psiHeat t x -
      alpha * (alpha - 1) * phi t x ^ (alpha - 2) *
        psi t x ^ (-beta) *
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (phi t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (phi t) x) -
      ((-beta) * ((-beta) - 1)) * phi t x ^ alpha *
        psi t x ^ (-beta - 2) *
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (psi t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (psi t) x) +
      2 * alpha * beta * phi t x ^ (alpha - 1) *
        psi t x ^ (-beta - 1) *
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (phi t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (psi t) x)

/-- Display-form right-hand side of Lemma 10.5, using `/ psi^...` notation.

The stable theorem uses negative powers.  This definition is only a
book-facing display layer on the positive `psi` region. -/
def quotHeatRHSDiv
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real) : Real -> M -> Real :=
  fun t x =>
    alpha * phi t x ^ (alpha - 1) / psi t x ^ beta *
        phiHeat t x -
      beta * phi t x ^ alpha / psi t x ^ (beta + 1) *
        psiHeat t x -
      alpha * (alpha - 1) * phi t x ^ (alpha - 2) /
        psi t x ^ beta *
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (phi t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (phi t) x) -
      beta * (beta + 1) * phi t x ^ alpha /
        psi t x ^ (beta + 2) *
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (psi t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (psi t) x) +
      2 * alpha * beta * phi t x ^ (alpha - 1) /
        psi t x ^ (beta + 1) *
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (phi t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (psi t) x)

/-- The display-form quotient RHS agrees with the stable negative-power RHS on
the positive-denominator region. -/
theorem quotHeatRHSDiv_eq
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real) {t : Real} {x : M}
    (hpsi : 0 < psi t x) :
    quotHeatRHSDiv (I := I) G phi psi phiHeat psiHeat alpha beta t x =
      quotHeatRHS (I := I) G phi psi phiHeat psiHeat alpha beta t x := by
  have h0 :
      psi t x ^ (-beta) = (psi t x ^ beta)⁻¹ := by
    simpa using Real.rpow_neg hpsi.le beta
  have h1 :
      psi t x ^ (-beta - 1) = (psi t x ^ (beta + 1))⁻¹ := by
    rw [show -beta - 1 = -(beta + 1) by ring]
    simpa using Real.rpow_neg hpsi.le (beta + 1)
  have h2 :
      psi t x ^ (-beta - 2) = (psi t x ^ (beta + 2))⁻¹ := by
    rw [show -beta - 2 = -(beta + 2) by ring]
    simpa using Real.rpow_neg hpsi.le (beta + 2)
  unfold quotHeatRHSDiv quotHeatRHS
  rw [h0, h1, h2]
  simp [div_eq_mul_inv]
  ring_nf

/-- Predicate form of Lemma 10.5 for a fixed realized metric family. -/
def QuotientEvolutionOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => quotField (M := M) phi psi alpha beta s x)
      (quotLap (I := I) G phi psi alpha beta (t : Real) x +
        quotHeatRHS (I := I) G phi psi phiHeat psiHeat alpha beta
          (t : Real) x)
      D.carrier
      (t : Real)

/-- Display-form predicate for Lemma 10.5, using `/ psi^...` notation in the
RHS.  The authoritative computational form is `QuotientEvolutionOn`. -/
def QuotEvolDivOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => quotField (M := M) phi psi alpha beta s x)
      (quotLap (I := I) G phi psi alpha beta (t : Real) x +
        quotHeatRHSDiv (I := I) G phi psi phiHeat psiHeat alpha beta
          (t : Real) x)
      D.carrier
      (t : Real)

/-- Lemma 10.5, pointwise quotient evolution identity.

The general real-exponent statement is intentionally stated on the positive
`phi`, positive `psi` region.  The extra gradient regularity hypotheses are
regularity inputs for the spatial product rule; they do not encode the
quotient identity itself. -/
theorem quotHeat_at
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (hphiDt :
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt :
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap :
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap :
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff :
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff :
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiPos : forall y : M, 0 < phi (t : Real) y)
    (hpsiPos : forall y : M, 0 < psi (t : Real) y)
    (hgradPhi :
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi :
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPhiPow :
      forall y : M, MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => phi (t : Real) w ^ alpha) z) y)
    (hgradPsiPow :
      forall y : M, MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    HasDerivWithinAt
      (fun s : Real => quotField (M := M) phi psi alpha beta s x)
      (quotLap (I := I) G phi psi alpha beta (t : Real) x +
        quotHeatRHS (I := I) G phi psi phiHeat psiHeat alpha beta
          (t : Real) x)
      D.carrier
      (t : Real) := by
  let tt : Real := (t : Real)
  let A : M -> Real := fun y => phi tt y ^ alpha
  let B : M -> Real := fun y => psi tt y ^ (-beta)
  have hA_diff : forall y : M, MDifferentiableAt I 𝓘(Real, Real) A y := by
    intro y
    exact DifferentialGeometry.Integral.Connection.mdifferentiableAt_rpow
      (I := I) alpha (hphiDiff y) (hphiPos y)
  have hB_diff : forall y : M, MDifferentiableAt I 𝓘(Real, Real) B y := by
    intro y
    exact DifferentialGeometry.Integral.Connection.mdifferentiableAt_rpow
      (I := I) (-beta) (hpsiDiff y) (hpsiPos y)
  have hA_lap :=
    DifferentialGeometry.Integral.Connection.laplacianAt_rpow (I := I) G tt
      (f := phi tt) (x := x) alpha hphiDiff hphiPos hgradPhi
  have hB_lap :=
    DifferentialGeometry.Integral.Connection.laplacianAt_rpow (I := I) G tt
      (f := psi tt) (x := x) (-beta) hpsiDiff hpsiPos hgradPsi
  have hAB_lap :=
    DifferentialGeometry.Integral.Connection.laplacianAt_mul_of_scalarRegular (I := I) G tt
      (f := A) (h := B) (x := x)
      hA_diff hB_diff hgradPhiPow hgradPsiPow
  have hgradA :=
    DifferentialGeometry.Integral.Connection.gradientAt_rpow (I := I) G tt
      (f := phi tt) (x := x) alpha (hphiDiff x) (hphiPos x)
  have hgradB :=
    DifferentialGeometry.Integral.Connection.gradientAt_rpow (I := I) G tt
      (f := psi tt) (x := x) (-beta) (hpsiDiff x) (hpsiPos x)
  have hphiPowDt :=
    hphiDt.rpow_const (p := alpha) (Or.inl (hphiPos x).ne')
  have hpsiPowDt :=
    hpsiDt.rpow_const (p := -beta) (Or.inl (hpsiPos x).ne')
  have hdt := hphiPowDt.mul hpsiPowDt
  convert hdt using 1
  · unfold quotLap quotHeatRHS quotField
    simp only [tt] at hA_lap hB_lap hAB_lap hgradA hgradB hphiLap hpsiLap
    rw [hAB_lap, hA_lap, hB_lap, hgradA, hgradB, hphiLap, hpsiLap]
    simp [A, B, tt, smul_eq_mul]
    ring_nf

/-- Lemma 10.5 as a reusable scalar quotient evolution producer. -/
theorem quotHeat
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPhiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => phi (t : Real) w ^ alpha) z) y)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    QuotientEvolutionOn (I := I) (D := D) G
      phi psi phiHeat psiHeat alpha beta := by
  intro t x
  exact quotHeat_at (I := I) G phi psi phiLap psiLap phiHeat psiHeat
    alpha beta t x
    (hphiDt t x) (hpsiDt t x) (hphiLap t x) (hpsiLap t x)
    (hphiDiff t) (hpsiDiff t) (hphiPos t) (hpsiPos t)
    (hgradPhi t x) (hgradPsi t x) (hgradPhiPow t) (hgradPsiPow t)

/-- Lemma 10.5 specialized to the Hamilton-ready numerator exponent
`alpha = 1`.  This keeps the same positivity assumptions as the general
producer; weakening the numerator positivity at zero is a separate local
frontier. -/
theorem quotHeat_one
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPhiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => phi (t : Real) w ^ (1 : Real)) z) y)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    QuotientEvolutionOn (I := I) (D := D) G
      phi psi phiHeat psiHeat (1 : Real) beta := by
  exact quotHeat (I := I) (D := D) G
    phi psi phiLap psiLap phiHeat psiHeat (1 : Real) beta
    hphiDt hpsiDt hphiLap hpsiLap hphiDiff hpsiDiff
    hphiPos hpsiPos hgradPhi hgradPsi hgradPhiPow hgradPsiPow

/-- Side form of Lemma 10.5 for the Hamilton-ready numerator exponent
`alpha = 1`.

Unlike `quotHeat_one`, this does not derive the result from the arbitrary
real-exponent theorem, so it only assumes `0 <= phi`.  The proof differentiates
`phi * psi^(-beta)` directly and uses the real-power chain rule only for the
positive denominator. -/
theorem quotHeat1_of_nonneg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (_hphiNonneg : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 <= phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    QuotientEvolutionOn (I := I) (D := D) G
      phi psi phiHeat psiHeat (1 : Real) beta := by
  intro t x
  let tt : Real := (t : Real)
  let B : M -> Real := fun y => psi tt y ^ (-beta)
  have hB_diff : forall y : M, MDifferentiableAt I 𝓘(Real, Real) B y := by
    intro y
    exact DifferentialGeometry.Integral.Connection.mdifferentiableAt_rpow
      (I := I) (-beta) (hpsiDiff t y) (hpsiPos t y)
  have hB_lap :=
    DifferentialGeometry.Integral.Connection.laplacianAt_rpow (I := I) G tt
      (f := psi tt) (x := x) (-beta) (hpsiDiff t) (hpsiPos t)
      (hgradPsi t x)
  have hphiB_lap :=
    DifferentialGeometry.Integral.Connection.laplacianAt_mul_of_scalarRegular (I := I) G tt
      (f := phi tt) (h := B) (x := x)
      (hphiDiff t) hB_diff (hgradPhi t) (hgradPsiPow t)
  have hgradB :=
    DifferentialGeometry.Integral.Connection.gradientAt_rpow (I := I) G tt
      (f := psi tt) (x := x) (-beta) (hpsiDiff t x) (hpsiPos t x)
  have hpsiPowDt :=
    (hpsiDt t x).rpow_const (p := -beta) (Or.inl (hpsiPos t x).ne')
  have hdt := (hphiDt t x).mul hpsiPowDt
  have hfield_lap :
      DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G tt
          (fun y : M => phi tt y ^ (1 : Real) * psi tt y ^ (-beta)) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G tt
          (fun y : M => phi tt y * B y) x := by
    congr 1
    funext y
    simp [B]
  convert hdt using 1
  · funext s
    simp [quotField]
  · unfold quotLap quotHeatRHS quotField
    simp only [tt] at hB_lap hphiB_lap hgradB hphiLap hpsiLap hfield_lap
    rw [hfield_lap, hphiB_lap, hB_lap, hgradB, hphiLap t x, hpsiLap t x]
    simp [B, tt, smul_eq_mul]
    ring_nf

/-! ### Book-facing Lemma 10.5 wrappers -/

/-- Book-facing positive-region form of Lemma 10.5.

This is a named wrapper around the stable negative-power theorem.  For
arbitrary real `alpha`, the numerator is required to be positive. -/
theorem quotHeat_book
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPhiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => phi (t : Real) w ^ alpha) z) y)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    QuotientEvolutionOn (I := I) (D := D) G
      phi psi phiHeat psiHeat alpha beta :=
  quotHeat (I := I) (D := D) G
    phi psi phiLap psiLap phiHeat psiHeat alpha beta
    hphiDt hpsiDt hphiLap hpsiLap hphiDiff hpsiDiff
    hphiPos hpsiPos hgradPhi hgradPsi hgradPhiPow hgradPsiPow

/-- Book-facing Hamilton-ready side form of Lemma 10.5.

This is the `alpha = 1` wrapper with only `0 <= phi`; the proof route does not
use a numerator real-power chain rule. -/
theorem quotHeat1_book
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiNonneg : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 <= phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    QuotientEvolutionOn (I := I) (D := D) G
      phi psi phiHeat psiHeat (1 : Real) beta :=
  quotHeat1_of_nonneg (I := I) (D := D) G
    phi psi phiLap psiLap phiHeat psiHeat beta
    hphiDt hpsiDt hphiLap hpsiLap hphiDiff hpsiDiff
    hphiNonneg hpsiPos hgradPhi hgradPsi hgradPsiPow

/-- Display-form corollary of the positive-region quotient evolution. -/
theorem quotHeatDiv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPhiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => phi (t : Real) w ^ alpha) z) y)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    QuotEvolDivOn (I := I) (D := D) G
      phi psi phiHeat psiHeat alpha beta := by
  have hstable :=
    quotHeat_book (I := I) (D := D) G
      phi psi phiLap psiLap phiHeat psiHeat alpha beta
      hphiDt hpsiDt hphiLap hpsiLap hphiDiff hpsiDiff
      hphiPos hpsiPos hgradPhi hgradPsi hgradPhiPow hgradPsiPow
  intro t x
  have h := hstable t x
  convert h using 1
  · rw [quotHeatRHSDiv_eq (I := I) G phi psi phiHeat psiHeat alpha beta
      (hpsiPos t x)]

end DifferentialGeometry.PDE.RicciFlow
