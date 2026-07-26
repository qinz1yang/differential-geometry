import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.SolutionTimeRestrict
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.ResidualCost
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.SolutionResidual
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.TowerProducer
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The arbitrary-dimensional curvature-derivative tower of a Ricci-flow solution

This file is the solution-facing owner of the arbitrary-dimensional curvature
tower.  It assembles the intrinsic squared norms `|nabla^k Rm|^2`, their
intrinsic scalar Laplacians, and the fixed costed residual field produced by the
all-order commutation recursion.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- An arbitrary-dimensional Ricci-flow solution directly produces the
intrinsic curvature-tower heat bound with the explicit constructor-tree
reaction cost. -/
theorem towerHeatSol_raw
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (k : Nat) :
    TowerHeatBoundOn (D := D)
      (nablaKRm04NormSqIntrinsic (I := I) S)
      (nablaKNormLap (I := I) S)
      (rmTowerCost (Module.finrank Real E) k) k := by
  classical
  let D' := D
  let S' := S
  change TowerHeatBoundOn (D := D')
    (nablaKRm04NormSqIntrinsic (I := I) S')
    (nablaKNormLap (I := I) S')
    (rmTowerCost (Module.finrank Real E) k) k
  have hS' : IsSolutionOn (I := I) S' := by
    simpa only [S'] using hS
  intro t x
  let Idx := Fin (Module.finrank Real E)
  obtain ⟨T, hTcost, hpoint⟩ := rmResidual_cost (I := I) S' hS' k t
  obtain ⟨basis, horth, hcompDt⟩ := hpoint x
  let gInv : Real → Idx → Idx → Real := fun r =>
    basisInvMetric (I := I) (S'.base.metric r) x basis
  have hinv : ∀ r : Real,
      MetricInverseInBasis_gen (I := I) (S'.base.metric r) x basis (gInv r) := by
    intro r
    simpa only [gInv] using
      basisInvMetric_real (I := I) (S'.base.metric r) x basis
  have hinvId : MetricInverseInBasis_gen (I := I) (S'.base.metric (t : Real)) x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal
      (I := I) (S'.base.metric (t : Real)) basis horth
  have hgInv : gInv (t : Real) = identityInvMetric (Idx := Idx) :=
    invBasis_unique (I := I) (S'.base.metric (t : Real)) x basis _ _
      (hinv (t : Real)) hinvId
  let ric : Idx → Idx → Real := fun i j =>
    S'.ricciAt (t : Real) x (vec2 (I := I) (basis i) (basis j))
  have hgInvDt : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gInv r i j)
        (2 * (∑ p : Idx, ∑ q : Idx,
          gInv (t : Real) i p * gInv (t : Real) j q * ric p q))
        D'.carrier (t : Real) := by
    intro i j
    let gdot : Idx → Idx → Real := fun p q => (-2 : Real) * ric p q
    have hraw : HasDerivAt (fun r : Real => gInv r i j)
        (-(∑ p : Idx, ∑ q : Idx,
          gInv (t : Real) i p * gdot p q * gInv (t : Real) q j)) (t : Real) := by
      simpa only [gInv] using
        basisInv_time (I := I) (fun r => S'.base.metric r) gdot basis
          (fun p q => by
            simpa only [gdot, ric] using
              metricDerivAt (I := I) S' hS' t x (basis p) (basis q)) i j
    have hterm :
        (∑ p : Idx, ∑ q : Idx,
          gInv (t : Real) i p * gdot p q * gInv (t : Real) q j) =
          ∑ p : Idx, ∑ q : Idx, (-2 : Real) *
            (gInv (t : Real) i p * gInv (t : Real) j q * ric p q) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [gInv]
      rw [basisInvMetric_symm (I := I) (S'.base.metric (t : Real)) x basis q j]
      dsimp only [gdot]
      ring
    have hfactor :
        (∑ p : Idx, ∑ q : Idx, (-2 : Real) *
          (gInv (t : Real) i p * gInv (t : Real) j q * ric p q)) =
          (-2 : Real) * (∑ p : Idx, ∑ q : Idx,
            gInv (t : Real) i p * gInv (t : Real) j q * ric p q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    apply (hraw.congr_deriv ?_).hasDerivWithinAt
    rw [hterm, hfactor]
    ring
  let Tdot : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x :=
    metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Idx))
        (nablaKRm04Field (I := I) S' (t : Real) (k + 2) x) + T x
  have hT : ∀ I0 : Fin (4 + k) → Idx,
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I)
          (nablaKRm04Field (I := I) S' r k x) (fun i => basis i) I0)
        (tensor0SComponent (I := I) Tdot (fun i => basis i) I0)
        D'.carrier (t : Real) := by
    intro I0
    simpa only [Tdot] using hcompDt I0
  have hst (j : Nat) : stNormSq (I := I) S' (t : Real) j x basis =
      nablaKRm04NormSqIntrinsic (I := I) S' j (t : Real) x := by
    simpa only [stNormSq, nablaKRm04NormSqIntrinsic] using
      (compNormSqMulti_orthoBasis_eq_normSq0S (I := I)
        (S'.base.metric (t : Real)) basis horth
        (nablaKRm04Field (I := I) S' (t : Real) j x))
  have hresid : ∀ m : Fin (4 + k) → Idx,
      |tensor0SComponent (I := I)
          (Tdot - metricTrace0S2TensorInBasis (I := I) basis (gInv (t : Real))
            (nablaKRm04Field (I := I) S' (t : Real) (k + 2) x))
          (fun i => basis i) m| ≤
        rmResidualCost (Module.finrank Real E) k *
          ∑ j ∈ Finset.range (k + 1),
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S' j (t : Real) x) *
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S' (k - j) (t : Real) x) := by
    intro m
    have hcancel :
        Tdot - metricTrace0S2TensorInBasis (I := I) basis (gInv (t : Real))
            (nablaKRm04Field (I := I) S' (t : Real) (k + 2) x) = T x := by
      rw [hgInv]
      dsimp only [Tdot]
      abel
    rw [hcancel]
    simpa only [hst, tensor0SComponent_apply] using
      hTcost.bound x basis (by
        simpa only [SolutionOn.family_metric] using horth) m
  have hlevel : compNormSqMulti (fun I0 : Fin (4 + k) → Idx =>
      tensor0SComponent (I := I) (nablaKRm04Field (I := I) S' (t : Real) k x)
        (fun i => basis i) I0) ≤
      nablaKRm04NormSqIntrinsic (I := I) S' k (t : Real) x := by
    exact le_of_eq (by
      simpa only [tensor0SComponent_apply, nablaKRm04NormSqIntrinsic] using
        (compNormSqMulti_orthoBasis_eq_normSq0S (I := I)
          (S'.base.metric (t : Real)) basis horth
          (nablaKRm04Field (I := I) S' (t : Real) k x)))
  have hRic : ∀ p q : Idx, |ric p q| ≤
      (Fintype.card Idx : Real) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S' 0 (t : Real) x) := by
    intro p q
    simpa only [ric, SolutionOn.ricciAt, SolutionFamily.ricciAt,
      nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
      SolutionFamily.rm04, metricRm04] using
        (metricRicciComp_le (I := I) (g := S'.base.metric (t : Real))
          basis horth p q)
  have hheat := nablaKNormHeatAt (I := I) S' k t x basis gInv ric Tdot
    (fun r => by simpa only [MetricInverseInBasis, MetricInverseInBasis_gen] using hinv r)
    hT hgInvDt
  have hreact0 := nablaKReactionAt_le (I := I) S' (t : Real) x basis
    (gInv (t : Real)) ric Tdot
    (nablaKRm04NormSqIntrinsic (I := I) S')
    horth hgInv hlevel hRic
    (rmResidualCost (Module.finrank Real E) k) hTcost.nonneg hresid
  have hreact : |nablaKReactionAt (I := I) S' k (t : Real) x basis
      (gInv (t : Real)) ric Tdot| ≤
      towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S')
        (rmTowerCost (Module.finrank Real E) k) k (t : Real) x := by
    simpa only [rmTowerCost, Idx, Fintype.card_fin] using hreact0
  refine ⟨nablaKNormLap (I := I) S' k (t : Real) x +
      (-2 * nablaKRm04NormSqIntrinsic (I := I) S' (k + 1) (t : Real) x +
        nablaKReactionAt (I := I) S' k (t : Real) x basis
          (gInv (t : Real)) ric Tdot), hheat, ?_⟩
  linarith [le_abs_self (nablaKReactionAt (I := I) S' k (t : Real) x basis
    (gInv (t : Real)) ric Tdot), hreact]

/-- On every strictly positive-time tail, the direct solution tower applies to
the restricted Ricci flow without an additional compactness or dimension
hypothesis. -/
theorem towerHeatSol_any
    {alpha t0 omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S)
    (halphat0 : alpha < t0) (ht0omega : t0 < omega)
    (k : Nat) :
    let D' := RealTimeInterval.closedOpen t0 omega ht0omega
    let S' := S.timeRestrict D'
    TowerHeatBoundOn (D := D')
      (nablaKRm04NormSqIntrinsic (I := I) S')
      (nablaKNormLap (I := I) S')
      (rmTowerCost (Module.finrank Real E) k) k := by
  classical
  let D' := RealTimeInterval.closedOpen t0 omega ht0omega
  let S' := S.timeRestrict D'
  have hS' : IsSolutionOn (I := I) S' := by
    simpa only [S', D'] using
      isSoln_tailRestrict (I := I) hS halphat0 ht0omega
  exact towerHeatSol_raw (I := I) S' hS' k

end DifferentialGeometry.PDE.RicciFlow
