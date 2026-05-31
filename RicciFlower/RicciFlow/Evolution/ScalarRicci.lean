/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.RicciFlow.Evolution.Ricci
import RicciFlower.RicciFlow.Evolution.Scalar

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Scalar/Ricci Producer Bridges

This file contains producer bridges that need both the Ricci evolution component
API and the scalar-curvature heat-operator API.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx]

local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)

private theorem sum_swap_four
    {R : Type*} [AddCommMonoid R]
    (F : Idx -> Idx -> Idx -> Idx -> R) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) =
      ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, ∑ j : Idx, F i j k l := by
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) =
        ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx, F i j k l := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ k : Idx, ∑ i : Idx, ∑ j : Idx, ∑ l : Idx, F i j k l := by
          rw [Finset.sum_comm]
    _ = ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, ∑ j : Idx, F i j k l := by
          refine Finset.sum_congr rfl fun k _ => ?_
          calc
            (∑ i : Idx, ∑ j : Idx, ∑ l : Idx, F i j k l) =
                ∑ i : Idx, ∑ l : Idx, ∑ j : Idx, F i j k l := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ = ∑ l : Idx, ∑ i : Idx, ∑ j : Idx, F i j k l := by
                  rw [Finset.sum_comm]

/-- The two metric traces of the Ricci second covariant derivative agree after
swapping the two traced index pairs. -/
theorem scalarHessianFromNabla2Ric_trace_eq_roughLapRic_trace
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) :
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j) =
      scalarLaplacianTraceInFrame (M := M) gInv
        (roughLapRicInFrame (M := M) gInv nabla2Ric) t x := by
  classical
  unfold scalarHessianFromNabla2RicInFrame scalarLaplacianTraceInFrame
    roughLapRicInFrame
  calc
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        (∑ k : Idx, ∑ l : Idx, gInv t x k l * nabla2Ric t x i j k l)) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv t x i j * (gInv t x k l * nabla2Ric t x i j k l) := by
          simp [Finset.mul_sum]
    _ = ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, ∑ j : Idx,
          gInv t x i j * (gInv t x k l * nabla2Ric t x i j k l) :=
          sum_swap_four
            (Idx := Idx)
            (fun i j k l =>
              gInv t x i j * (gInv t x k l * nabla2Ric t x i j k l))
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv t x i j * (gInv t x k l * nabla2Ric t x k l i j) := by
          simp [mul_left_comm]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv t x i j *
            (∑ k : Idx, ∑ l : Idx,
              gInv t x k l * nabla2Ric t x k l i j) := by
          simp [Finset.mul_sum]

/-- Ricci-specific heat-operator producer for the canonical scalar Laplacian.

The scalar Hessian supplied by the Hessian-trace API is allowed to be the
`scalarHessianFromNabla2RicInFrame` trace of `nabla2Ric`.  The target rough
Ricci Laplacian uses `roughLapRicInFrame`; the equality between the two scalar
Laplacian traces is the finite-sum swap above. -/
@[deprecated "use a local or pointwise scalar trace statement instead" (since := "2026-05-22")]
theorem scalarLaplacianTraceInFrame_realizes_heatOperator_of_nabla2RicTrace
    {D : Realized.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (scalarHess : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (htrace : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      Realized.ScalarLaplacianRealizesTraceAtInBasis (I := I)
        (G.connection t) (G.metric t)
        (hframe.toBasisAt (hcover x))
        (gInv t x) (scalarTraceInFrame (I := I) S gInv frame t)
        (scalarHess t x))
    (hcomp : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      forall i j : Idx,
        scalarHess t x (Realized.vec2 (I := I) (frame i x) (frame j x)) =
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j) :
    ScalarLaplacianRealizesHeatOperatorOn (I := I) G T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv
        (roughLapRicInFrame (M := M) gInv nabla2Ric)) := by
  refine scalarLaplacianTraceInFrame_realizes_heatOperator_of_laplacianAt
    (I := I) S G T gInv frame
    (roughLapRicInFrame (M := M) gInv nabla2Ric) ?_
  intro t ht x
  let basis := hframe.toBasisAt (hcover x)
  have hmetric :
      Realized.metricTrace0S2InBasis (I := I) basis (gInv t x)
          (scalarHess t x) Fin.elim0 =
        ∑ i : Idx, ∑ j : Idx,
          gInv t x i j *
            scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j := by
    unfold Realized.metricTrace0S2InBasis
    refine Finset.sum_congr rfl fun i _hi => ?_
    refine Finset.sum_congr rfl fun j _hj => ?_
    congr 1
    have hinput :
        Realized.metricTraceInput (I := I) (basis i) (basis j) Fin.elim0 =
          Realized.vec2 (I := I) (frame i x) (frame j x) := by
      have hbi : basis i = frame i x := by
        simp [basis, IsLocalFrameOn.toBasisAt_coe]
      have hbj : basis j = frame j x := by
        simp [basis, IsLocalFrameOn.toBasisAt_coe]
      rw [hbi, hbj]
      funext q
      fin_cases q
      · simp [Realized.metricTraceInput, Realized.vec2, RicciFlower.Curvature.vec2]
      · rfl
    rw [hinput, hcomp t ht x i j]
  have htrace_tx := htrace t ht x
  unfold Realized.ScalarLaplacianRealizesTraceAtInBasis at htrace_tx
  calc
    scalarLaplacianTraceInFrame (M := M) gInv
        (roughLapRicInFrame (M := M) gInv nabla2Ric) t x =
        ∑ i : Idx, ∑ j : Idx,
          gInv t x i j *
            scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j :=
          (scalarHessianFromNabla2Ric_trace_eq_roughLapRic_trace
            (M := M) gInv nabla2Ric t x).symm
    _ = Realized.metricTrace0S2InBasis (I := I) basis (gInv t x)
          (scalarHess t x) Fin.elim0 := hmetric.symm
    _ = Realized.laplacianAt (I := I) G t
          (scalarTraceInFrame (I := I) S gInv frame t) x := by
        unfold Realized.laplacianAt
        exact htrace_tx.symm

end RicciFlow
end RicciFlower
