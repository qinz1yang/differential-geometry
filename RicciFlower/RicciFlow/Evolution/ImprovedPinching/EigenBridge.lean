import RicciFlower.RicciFlow.Evolution.ImprovedPinching.BookData
import RicciFlower.RicciFlow.Evolution.RicciPreservation

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Improved pinching eigenvalue bridges

This file contains pointwise bridges from Section 9 tensor inequalities to the
dimension-three eigenvalue algebra used in Hamilton Section 10.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open scoped Manifold ContDiff BigOperators
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

/-- Section 9 tensor inequalities give the unordered eigenvalue package used
by Lemma 10.8.  This is pointwise: no smooth eigenvalue field is selected. -/
theorem pinchEigen3Unordered_of_ricci_nonneg_and_shifted_pinch
    {g : SmoothRiemannianMetric I M}
    {x : M}
    {Ric : Realized.Tensor02At (I := I) (M := M) x}
    {scalar delta l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (hdiag : DimensionThree.RicciDiagAt
      (I := I) Ric scalar l1 l2 l3 basis)
    (hnonneg : DimensionThree.RicciNonnegAt (I := I) Ric)
    (hpinch : ∀ v : TangentSpace I x,
      0 <= Ric (Realized.vec2 (I := I) v v)
          - delta * scalar * g.inner x v v)
    (hdelta0 : 0 <= delta) :
    DimensionThree.PinchEigen3Unordered l1 l2 l3 delta := by
  classical
  have hscalar : scalar = DimensionThree.ricciEigenScalar3 l1 l2 l3 := hdiag.1
  have h00 :
      Ric (Realized.vec2 (I := I) (basis 0) (basis 0)) = l1 := by
    simpa [Realized.ricciCompAt_apply, DimensionThree.ricciDiag3] using
      hdiag.2 0 0
  have h11 :
      Ric (Realized.vec2 (I := I) (basis 1) (basis 1)) = l2 := by
    simpa [Realized.ricciCompAt_apply, DimensionThree.ricciDiag3] using
      hdiag.2 1 1
  have h22 :
      Ric (Realized.vec2 (I := I) (basis 2) (basis 2)) = l3 := by
    simpa [Realized.ricciCompAt_apply, DimensionThree.ricciDiag3] using
      hdiag.2 2 2
  have hg00 : g.inner x (basis 0) (basis 0) = 1 := by
    simpa [DimensionThree.delta3] using horth 0 0
  have hg11 : g.inner x (basis 1) (basis 1) = 1 := by
    simpa [DimensionThree.delta3] using horth 1 1
  have hg22 : g.inner x (basis 2) (basis 2) = 1 := by
    simpa [DimensionThree.delta3] using horth 2 2
  have hnonneg1 : 0 <= l1 := by
    simpa [h00] using hnonneg (basis 0)
  have hnonneg2 : 0 <= l2 := by
    simpa [h11] using hnonneg (basis 1)
  have hnonneg3 : 0 <= l3 := by
    simpa [h22] using hnonneg (basis 2)
  have hlower1 : delta * DimensionThree.ricciEigenScalar3 l1 l2 l3 <= l1 := by
    have hpin := hpinch (basis 0)
    rw [h00, hg00, hscalar] at hpin
    nlinarith
  have hlower2 : delta * DimensionThree.ricciEigenScalar3 l1 l2 l3 <= l2 := by
    have hpin := hpinch (basis 1)
    rw [h11, hg11, hscalar] at hpin
    nlinarith
  have hlower3 : delta * DimensionThree.ricciEigenScalar3 l1 l2 l3 <= l3 := by
    have hpin := hpinch (basis 2)
    rw [h22, hg22, hscalar] at hpin
    nlinarith
  exact
    { nonneg1 := hnonneg1
      nonneg2 := hnonneg2
      nonneg3 := hnonneg3
      delta_nonneg := hdelta0
      lower1 := hlower1
      lower2 := hlower2
      lower3 := hlower3 }

/-- Raw Section 9 nonnegativity predicates give the unordered eigenvalue
package after diagonalizing Ricci. -/
theorem pinchEigen3Unordered_of_pinchTensor_nonneg
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {delta t : Real} {x : M}
    {l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DimensionThree.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis)
    (hdiag : DimensionThree.RicciDiagAt
      (I := I) (S.ricciAt t x) (S.scalar t x) l1 l2 l3 basis)
    (hric :
      Realized.TwoTensorNonnegativeAt (I := I) (M := M)
        (Realized.twoTensorSecToFamily (I := I) (M := M) S.ricci t) x)
    (hpinch :
      Realized.TwoTensorNonnegativeAt (I := I) (M := M)
        (pinchTensor (I := I) (M := M)
          (fun t : Real => S.base.metric t)
          (Realized.twoTensorSecToFamily (I := I) (M := M) S.ricci)
          S.scalar delta t) x)
    (hdelta0 : 0 <= delta) :
    DimensionThree.PinchEigen3Unordered l1 l2 l3 delta := by
  refine pinchEigen3Unordered_of_ricci_nonneg_and_shifted_pinch
    (I := I) (M := M) horth hdiag ?_ ?_ hdelta0
  · intro v
    simpa [Realized.twoTensorSecToFamily, SolutionOn.ricciAt] using hric v
  · intro v
    simpa [pinchTensor, Realized.twoTensorSecToFamily, SolutionOn.ricciAt]
      using hpinch v

/-- Section 9 pointwise tensor inequalities imply the Lemma 10.8 reaction
bracket sign for the canonical Section 10 scalar fields. -/
theorem cubicQ_sub_nonneg_of_section9_point
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {delta epsilon t : Real} {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (_hscalarPos : 0 < S.scalar t x)
    (hdelta0 : 0 <= delta)
    (hepsilon : epsilon <= 2 * delta ^ 2)
    (hric :
      Realized.TwoTensorNonnegativeAt
        (I := I) (M := M)
        (Realized.twoTensorSecToFamily (I := I) (M := M) S.ricci t) x)
    (hpinch :
      Realized.TwoTensorNonnegativeAt
        (I := I) (M := M)
        (pinchTensor (I := I) (M := M)
          (fun t : Real => S.base.metric t)
          (Realized.twoTensorSecToFamily (I := I) (M := M) S.ricci)
          S.scalar delta t) x) :
    0 <=
      cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S) t x
        - epsilon * ricciNorm (I := I) S t x *
          tfRicNormSq S.scalar (ricciNorm (I := I) S) t x := by
  classical
  rcases DimensionThree.ricciEigen3 (I := I) (S.base.metric t)
      (S.ricciAt t x) hdim (ricciSym_can (I := I) S t x) with
    ⟨basis, l1, l2, l3, horth, hdiag0⟩
  have hScalarTrace :
      Realized.ScalarRealizesRicciTraceAt (I := I)
        (S.scalar t x) (S.ricciAt t x) DimensionThree.delta3 basis := by
    have htr := scalarTrace_delta (I := I) (S.base.metric t)
      (S.ricciAt t x) horth
    simpa [SolutionOn.scalar_eq_metricTrace] using htr
  have hscalar :
      S.scalar t x = DimensionThree.ricciEigenScalar3 l1 l2 l3 :=
    scalar_eq_diag (I := I) hScalarTrace hdiag0
  have hscalarMetric :
      Realized.metricTracePair0SAt (I := I)
          (S.base.metric t) (S.base.ricciAt t x) =
        DimensionThree.ricciEigenScalar3 l1 l2 l3 := by
    simpa [SolutionOn.scalar_eq_metricTrace, SolutionOn.ricciAt] using hscalar
  have hdiag :
      DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
        (S.scalar t x) l1 l2 l3 basis := by
    exact ⟨hscalar, hdiag0.2⟩
  have hctx :
      DimensionThree.PinchEigen3Unordered l1 l2 l3 delta :=
    pinchEigen3Unordered_of_pinchTensor_nonneg
      (I := I) (M := M) S horth hdiag hric hpinch hdelta0
  have hcube :
      ricciCube (I := I) S t x =
        DimensionThree.ricciEigenTraceCube3 l1 l2 l3 := by
    simpa [ricciCube] using
      (ricciCubeInv_diag (I := I) (S.base.metric t) horth hdiag0)
  have hinv :
      MetricInverseInBasis (I := I) (S.base.metric t) x basis
        DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I)
      (S.base.metric t) basis horth
  have hnorm :
      ricciNorm (I := I) S t x =
        DimensionThree.ricciEigenNormSq3 l1 l2 l3 := by
    have hinner :
        ricciNormAt (I := I) (S.ricciAt t x) basis =
          ricciNorm (I := I) S t x := by
      simpa [ricciNorm, SolutionOn.ricci, SolutionOn.ricciAt] using
        (ricciNorm_inner (I := I) (S.base.metric t)
          (S.ricciAt t x) basis hinv)
    have hdiagNorm :
        ricciNormAt (I := I) (S.ricciAt t x) basis =
          DimensionThree.ricciEigenNormSq3 l1 l2 l3 :=
      ricciNormAt_diag (I := I) hdiag0
    rw [← hinner]
    exact hdiagNorm
  have hq :=
    DimensionThree.PinchEigen3Unordered.q_sub_nonneg hctx hepsilon
  have hq_fields :
      0 <=
        cubicQAt
            (DimensionThree.ricciEigenScalar3 l1 l2 l3)
            (DimensionThree.ricciEigenNormSq3 l1 l2 l3)
            (DimensionThree.ricciEigenTraceCube3 l1 l2 l3) -
          epsilon * DimensionThree.ricciEigenNormSq3 l1 l2 l3 *
            tfRicNormSqAt
              (DimensionThree.ricciEigenScalar3 l1 l2 l3)
              (DimensionThree.ricciEigenNormSq3 l1 l2 l3) := by
    simpa [cubicQ_eigen, tfRic_eigen] using hq
  simpa [cubicQ, tfRicNormSq, tracefreeRicciNormSqOf,
    tracefreeRicciNormSqAtOf, SolutionOn.scalar_eq_metricTrace,
    hscalarMetric, hnorm, hcube] using hq_fields

end RicciFlow
end RicciFlower
