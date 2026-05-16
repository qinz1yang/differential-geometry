import RicciFlower.Realized.RicciFlow
import RicciFlower.Realized.Bochner
import RicciFlower.Realized.CurvatureTensor

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# RicciFlower Ricci-Flow Folder Entry Point

This file is the forward-facing Ricci-flow API.  The older
`RicciFlower.Realized.RicciFlow` module remains as a compatibility layer; this
folder-level module packages a solution as a real-time metric family together
with bundled Ricci tensor sections, then records interval-local validity as a
separate layer.

The Section 6.2 evolution identities are introduced as explicit equation
predicates.  The current file records the interfaces and the algebraic
composition for Lemma 6.7; the geometric producers for Ricci/scalar evolution
are separate proof frontiers.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Ricci-flow solutions as metric families -/

/-- A time-dependent bundled Ricci tensor section. -/
abbrev RicciSectionFamily : Type _ :=
  Real -> Realized.Tensor02Section (I := I) (M := M)

namespace RicciSectionFamily

/-- View a bundled Ricci section family as the pointwise tensor field expected
by the compatibility `Realized.RicciFlow` API. -/
def toTensorField (Ric : RicciSectionFamily (I := I) (M := M)) :
    Realized.RicciTensorField (I := I) (M := M) Real :=
  fun t x X Y => Ric t x (Realized.vec2 X Y)

@[simp] theorem toTensorField_apply
    (Ric : RicciSectionFamily (I := I) (M := M))
    (t : Real) (x : M) (X Y : TangentSpace I x) :
    toTensorField (I := I) Ric t x X Y =
      Ric t x (Realized.vec2 X Y) := by
  rfl

end RicciSectionFamily

variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- A data-only real-time Ricci-flow family, independent of a chosen interval. -/
structure SolutionFamily where
  metric : Real -> SmoothRiemannianMetric I M
  connection : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)
  ricci : RicciSectionFamily (I := I) (M := M)

namespace SolutionFamily

/-- The metric and connection are compatible at every flow time of `D`. -/
def MetricCompatibleOn
    (G : SolutionFamily (I := I) (M := M))
    (D : Realized.RealTimeInterval) : Prop :=
  forall t : Realized.RealTimeInterval.FlowTime D,
    RicciFlower.Connection.IsMetricCompatible (I := I)
      (G.connection (t : Real)) (G.metric (t : Real))

end SolutionFamily

/-- A Ricci-flow candidate on a real interval.

The underlying metric, connection, and Ricci data are a real-time family; this
wrapper records that the metric and connection are compatible on the chosen
interval.  This keeps extension/maximality statements from needing to compare
families with different interval indices. -/
structure SolutionOn (D : Realized.RealTimeInterval) where
  base : SolutionFamily (I := I) (M := M)
  metricCompatible : base.MetricCompatibleOn D

namespace SolutionOn

/-- The interval-indexed realized metric family associated to a solution
candidate.  This preserves the previous `S.family` API. -/
def family {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Realized.RealizedMetricFamilyOn (I := I) (M := M) D where
  metric := S.base.metric
  connection := S.base.connection
  metricCompatible := S.metricCompatible

/-- The bundled Ricci tensor section family.  This preserves the previous
`S.ricci` API. -/
def ricci {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    RicciSectionFamily (I := I) (M := M) :=
  S.base.ricci

@[simp] theorem family_metric {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.family.metric = S.base.metric := by
  rfl

@[simp] theorem family_connection {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.family.connection = S.base.connection := by
  rfl

@[simp] theorem ricci_eq {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.ricci = S.base.ricci := by
  rfl

/-- Compatibility view as the older realized Ricci-flow candidate. -/
def toRealizedCandidate {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Realized.RealizedRicciFlowCandidateOn (I := I) (M := M) D where
  family := S.family
  ricci := RicciSectionFamily.toTensorField (I := I) S.ricci

@[simp] theorem toRealizedCandidate_family {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.toRealizedCandidate.family = S.family := by
  rfl

end SolutionOn

/-- The Ricci-flow metric equation for a folder-level solution:
`∂_t g = -2 Ric`, on the interval carrier and at regular times. -/
def MetricVariationEquationOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop :=
  Realized.MetricVariationEquationOn (I := I) S.family
    (RicciSectionFamily.toTensorField (I := I) S.ricci)

/-- Predicate package saying the folder-level candidate is a Ricci-flow
solution. -/
structure IsSolutionOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  smoothMetric : Realized.MetricFamilySmoothOn (I := I) (M := M) D S.family
  smoothConnection : RicciFlower.Connection.ConnectionFamilySmoothOn (I := I) (M := M) S.family
  leviCivita : RicciFlower.LeviCivita.IsLeviCivitaFamilyOn (I := I) S.family
  equation : MetricVariationEquationOn (I := I) S

/-- Convert the folder-level solution predicate to the older realized
compatibility predicate. -/
theorem isRealizedRicciFlowSolutionOn_of_isSolutionOn
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S) :
    Realized.IsRealizedRicciFlowSolutionOn (I := I) S.toRealizedCandidate := by
  exact
    { smoothMetric := hS.smoothMetric
      smoothConnection := hS.smoothConnection
      leviCivita := hS.leviCivita
      equation := hS.equation }

/-- Extract the interval metric evolution equation from a folder-level solution. -/
theorem metric_derivWithin_eq_neg_two_ricci
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (X Y : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => (S.family.metric s).inner x X Y)
      ((-2 : Real) * S.ricci (t : Real) x (Realized.vec2 X Y))
      D.carrier
      (t : Real) := by
  simpa [MetricVariationEquationOn, RicciSectionFamily.toTensorField] using
    hS.equation t x X Y

/-! ## Section 6.2: Ricci and scalar evolution interfaces -/

section Components

variable {Idx : Type*} [Fintype Idx]

private def raise2By
    (G A : Idx -> Idx -> Real) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx, G i a * G j b * A a b

private def oneUpBy
    (G A : Idx -> Idx -> Real) (i k : Idx) : Real :=
  ∑ a : Idx, G k a * A i a

private def quadraticBy
    (G A : Idx -> Idx -> Real) (i j : Idx) : Real :=
  ∑ k : Idx, oneUpBy G A i k * A k j

private theorem split_raise2By_tail
    (G B : Idx -> Idx -> Real) (c : Real) (i j : Idx)
    (P Q : Idx -> Idx -> Real) :
    c * (∑ a : Idx, ∑ b : Idx,
        (P a b + Q a b + G i a * G j b * B a b)) =
      c * (∑ a : Idx, ∑ b : Idx, (P a b + Q a b)) +
        c * raise2By G B i j := by
  classical
  unfold raise2By
  simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add,
    add_assoc, mul_left_comm, mul_comm]

private theorem sum_two_sub_cancel_scaled
    (L C Q R : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, (L i j - 2 * C i j - 2 * Q i j) * R i j) +
        4 * (∑ i : Idx, ∑ j : Idx, Q i j * R i j) +
        (∑ i : Idx, ∑ j : Idx, (L i j - 2 * C i j - 2 * Q i j) * R i j) =
      2 * (∑ i : Idx, ∑ j : Idx, L i j * R i j) +
        4 * (-(∑ i : Idx, ∑ j : Idx, C i j * R i j)) := by
  classical
  let LS : Real := ∑ i : Idx, ∑ j : Idx, L i j * R i j
  let CS : Real := ∑ i : Idx, ∑ j : Idx, C i j * R i j
  let QS : Real := ∑ i : Idx, ∑ j : Idx, Q i j * R i j
  have hpoint (i j : Idx) :
      (L i j - 2 * C i j - 2 * Q i j) * R i j =
        L i j * R i j - (C i j * R i j) * 2 - (Q i j * R i j) * 2 := by
    ring
  have hsum :
      (∑ i : Idx, ∑ j : Idx, (L i j - 2 * C i j - 2 * Q i j) * R i j) =
        LS - 2 * CS - 2 * QS := by
    calc
      (∑ i : Idx, ∑ j : Idx, (L i j - 2 * C i j - 2 * Q i j) * R i j)
          =
        ∑ i : Idx, ∑ j : Idx,
          (L i j * R i j - (C i j * R i j) * 2 - (Q i j * R i j) * 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          exact hpoint i j
      _ =
        (∑ i : Idx, ∑ j : Idx, L i j * R i j) -
          (∑ i : Idx, ∑ j : Idx, (C i j * R i j) * 2) -
            (∑ i : Idx, ∑ j : Idx, (Q i j * R i j) * 2) := by
          simp only [Finset.sum_sub_distrib]
      _ =
        LS - CS * 2 - QS * 2 := by
          simp only [LS, CS, QS, Finset.sum_mul]
      _ =
        LS - 2 * CS - 2 * QS := by
          ring
  rw [hsum]
  change (LS - 2 * CS - 2 * QS) + 4 * QS + (LS - 2 * CS - 2 * QS) =
    2 * LS + 4 * (-CS)
  ring

private theorem sum_mul_raise2By_comm
    (G A B : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i) :
    (∑ i : Idx, ∑ j : Idx, A i j * raise2By G B i j) =
      ∑ i : Idx, ∑ j : Idx, B i j * raise2By G A i j := by
  classical
  unfold raise2By
  calc
    (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx, G i a * G j b * B a b))
        =
      ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
        A i j * (G i a * G j b * B a b) := by
          simp [Finset.mul_sum]
    _ =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
        A i j * (G i a * G j b * B a b) := by
          calc
            (∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
              A i j * (G i a * G j b * B a b))
                =
              ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ b : Idx,
                A i j * (G i a * G j b * B a b) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ =
              ∑ a : Idx, ∑ i : Idx, ∑ j : Idx, ∑ b : Idx,
                A i j * (G i a * G j b * B a b) := by
                  rw [Finset.sum_comm]
            _ =
              ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
                A i j * (G i a * G j b * B a b) := by
                  refine Finset.sum_congr rfl fun a _ => ?_
                  calc
                    (∑ i : Idx, ∑ j : Idx, ∑ b : Idx,
                      A i j * (G i a * G j b * B a b))
                        =
                      ∑ i : Idx, ∑ b : Idx, ∑ j : Idx,
                        A i j * (G i a * G j b * B a b) := by
                          refine Finset.sum_congr rfl fun i _ => ?_
                          rw [Finset.sum_comm]
                    _ =
                      ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
                        A i j * (G i a * G j b * B a b) := by
                          rw [Finset.sum_comm]
    _ =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
        B a b * (G a i * G b j * A i j) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hG i a, hG j b]
          ring
    _ =
      ∑ a : Idx, ∑ b : Idx,
        B a b * (∑ i : Idx, ∑ j : Idx, G a i * G b j * A i j) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          simp [Finset.mul_sum, mul_left_comm, mul_comm]

private theorem sum_contraction_mul_eq_four_sum
    (R4 : Idx -> Idx -> Idx -> Idx -> Real)
    (A : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx,
      (∑ k : Idx, ∑ l : Idx, R4 i k j l * A k l) * A i j) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        R4 i k j l * A i j * A k l := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx,
      (∑ k : Idx, ∑ l : Idx, R4 i k j l * A k l) * A i j)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (R4 i k j l * A k l) * A i j := by
        simp [Finset.sum_mul]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        R4 i k j l * A i j * A k l := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

private theorem quadraticBy_eq_sum_right
    (G A : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i)
    (hA : forall i j, A i j = A j i)
    (i j : Idx) :
    quadraticBy G A i j =
      ∑ a : Idx, ∑ b : Idx, G a b * A i a * A j b := by
  classical
  unfold quadraticBy oneUpBy
  calc
    (∑ k : Idx, (∑ a : Idx, G k a * A i a) * A k j)
        =
      ∑ k : Idx, ∑ a : Idx, G k a * A i a * A k j := by
        simp [Finset.sum_mul, mul_assoc]
    _ =
      ∑ k : Idx, ∑ a : Idx, G k a * A i a * A j k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hA k j]
    _ =
      ∑ a : Idx, ∑ k : Idx, G k a * A i a * A j k := by
        rw [Finset.sum_comm]
    _ =
      ∑ a : Idx, ∑ b : Idx, G a b * A i a * A j b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hG b a]

private theorem quadraticBy_eq_sum_left
    (G A : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i)
    (hA : forall i j, A i j = A j i)
    (i j : Idx) :
    quadraticBy G A i j =
      ∑ a : Idx, ∑ b : Idx, G a b * A a i * A b j := by
  classical
  calc
    quadraticBy G A i j =
      ∑ a : Idx, ∑ b : Idx, G a b * A i a * A j b := by
        exact quadraticBy_eq_sum_right G A hG hA i j
    _ =
      ∑ a : Idx, ∑ b : Idx, G a b * A a i * A b j := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hA i a, hA j b]

private theorem metricDerivativeQuadraticTerms_eq_four
    (G A : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i)
    (hA : forall i j, A i j = A j i) :
    (∑ i : Idx, ∑ j : Idx,
      A i j *
        (∑ a : Idx, ∑ b : Idx,
          (2 * raise2By G A i a * G j b * A a b +
            G i a * (2 * raise2By G A j b) * A a b))) =
      4 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) := by
  classical
  have hright :
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          2 * raise2By G A i a * G j b * A a b)) =
        2 * (∑ i : Idx, ∑ a : Idx,
          quadraticBy G A i a * raise2By G A i a) := by
    calc
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          2 * raise2By G A i a * G j b * A a b))
          =
        ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
          A i j * (2 * raise2By G A i a * G j b * A a b) := by
            simp [Finset.mul_sum]
      _ =
        ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ b : Idx,
          A i j * (2 * raise2By G A i a * G j b * A a b) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
      _ =
        ∑ i : Idx, ∑ a : Idx,
          2 * raise2By G A i a *
            (∑ j : Idx, ∑ b : Idx, G j b * A i j * A a b) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ∑ i : Idx, ∑ a : Idx,
          2 * raise2By G A i a * quadraticBy G A i a := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← quadraticBy_eq_sum_right G A hG hA i a]
      _ =
        2 * (∑ i : Idx, ∑ a : Idx,
          quadraticBy G A i a * raise2By G A i a) := by
            simp [Finset.mul_sum, mul_left_comm, mul_comm]
  have hleft :
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          G i a * (2 * raise2By G A j b) * A a b)) =
        2 * (∑ j : Idx, ∑ b : Idx,
          quadraticBy G A j b * raise2By G A j b) := by
    calc
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          G i a * (2 * raise2By G A j b) * A a b))
          =
        ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
          A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
            simp [Finset.mul_sum]
      _ =
        ∑ j : Idx, ∑ b : Idx, ∑ i : Idx, ∑ a : Idx,
          A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
            calc
              (∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
                A i j * (G i a * (2 * raise2By G A j b) * A a b))
                  =
                ∑ j : Idx, ∑ i : Idx, ∑ a : Idx, ∑ b : Idx,
                  A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
                    rw [Finset.sum_comm]
              _ =
                ∑ j : Idx, ∑ i : Idx, ∑ b : Idx, ∑ a : Idx,
                  A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
                    refine Finset.sum_congr rfl fun j _ => ?_
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [Finset.sum_comm]
              _ =
                ∑ j : Idx, ∑ b : Idx, ∑ i : Idx, ∑ a : Idx,
                  A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
                    refine Finset.sum_congr rfl fun j _ => ?_
                    rw [Finset.sum_comm]
      _ =
        ∑ j : Idx, ∑ b : Idx,
          2 * raise2By G A j b *
            (∑ i : Idx, ∑ a : Idx, G i a * A i j * A a b) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun b _ => ?_
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ∑ j : Idx, ∑ b : Idx,
          2 * raise2By G A j b * quadraticBy G A j b := by
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [← quadraticBy_eq_sum_left G A hG hA j b]
      _ =
        2 * (∑ j : Idx, ∑ b : Idx,
          quadraticBy G A j b * raise2By G A j b) := by
            simp [Finset.mul_sum, mul_left_comm, mul_comm]
  calc
    (∑ i : Idx, ∑ j : Idx,
      A i j *
        (∑ a : Idx, ∑ b : Idx,
          (2 * raise2By G A i a * G j b * A a b +
            G i a * (2 * raise2By G A j b) * A a b)))
        =
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          2 * raise2By G A i a * G j b * A a b)) +
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          G i a * (2 * raise2By G A j b) * A a b)) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add,
            mul_left_comm, mul_comm]
    _ =
      2 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) +
      2 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) := by
          rw [hright, hleft]
    _ =
      4 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) := by
          ring

private theorem ricciNormDerivativeSimplifies_pure
    (G A L C : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i)
    (hA : forall i j, A i j = A j i) :
    (∑ i : Idx, ∑ j : Idx,
      ((L i j - 2 * C i j - 2 * quadraticBy G A i j) *
          raise2By G A i j +
        A i j *
          (∑ a : Idx, ∑ b : Idx,
            (2 * raise2By G A i a * G j b * A a b +
              G i a * (2 * raise2By G A j b) * A a b +
                G i a * G j b *
                  (L a b - 2 * C a b - 2 * quadraticBy G A a b))))) =
      2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
        4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := by
  classical
  let B : Idx -> Idx -> Real :=
    fun i j => L i j - 2 * C i j - 2 * quadraticBy G A i j
  have hpair :
      (∑ i : Idx, ∑ j : Idx, A i j * raise2By G B i j) =
        ∑ i : Idx, ∑ j : Idx, B i j * raise2By G A i j :=
    sum_mul_raise2By_comm G A B hG
  have hmetric := metricDerivativeQuadraticTerms_eq_four G A hG hA
  calc
    (∑ i : Idx, ∑ j : Idx,
      ((L i j - 2 * C i j - 2 * quadraticBy G A i j) *
          raise2By G A i j +
        A i j *
          (∑ a : Idx, ∑ b : Idx,
            (2 * raise2By G A i a * G j b * A a b +
              G i a * (2 * raise2By G A j b) * A a b +
                G i a * G j b *
                  (L a b - 2 * C a b - 2 * quadraticBy G A a b)))))
        =
      ∑ i : Idx, ∑ j : Idx,
        (B i j * raise2By G A i j +
          A i j *
            (∑ a : Idx, ∑ b : Idx,
              (2 * raise2By G A i a * G j b * A a b +
                G i a * (2 * raise2By G A j b) * A a b)) +
          A i j * raise2By G B i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          let P : Idx -> Idx -> Real :=
            fun a b => 2 * raise2By G A i a * G j b * A a b
          let Q : Idx -> Idx -> Real :=
            fun a b => G i a * (2 * raise2By G A j b) * A a b
          change
            B i j * raise2By G A i j +
                A i j * (∑ a : Idx, ∑ b : Idx,
                  (P a b + Q a b + G i a * G j b * B a b)) =
              B i j * raise2By G A i j +
                A i j * (∑ a : Idx, ∑ b : Idx, (P a b + Q a b)) +
                  A i j * raise2By G B i j
          rw [split_raise2By_tail]
          ring
    _ =
      (∑ i : Idx, ∑ j : Idx,
        B i j * raise2By G A i j) +
      (∑ i : Idx, ∑ j : Idx,
        A i j *
          (∑ a : Idx, ∑ b : Idx,
            (2 * raise2By G A i a * G j b * A a b +
              G i a * (2 * raise2By G A j b) * A a b))) +
      (∑ i : Idx, ∑ j : Idx,
        A i j * raise2By G B i j) := by
          simp [Finset.sum_add_distrib, add_assoc]
    _ =
      (∑ i : Idx, ∑ j : Idx,
        B i j * raise2By G A i j) +
      4 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) +
      (∑ i : Idx, ∑ j : Idx,
        B i j * raise2By G A i j) := by
          rw [hmetric, hpair]
    _ =
      2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
        4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := by
          simpa [B, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
            sum_two_sub_cancel_scaled
              (Idx := Idx)
              (L := L)
              (C := C)
              (Q := quadraticBy G A)
              (R := raise2By G A)

/-- Interpret the bundled Ricci section family as the pointwise two-tensor
field used by the coordinate Bochner layer. -/
def ricciTwoTensorField
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> Realized.TwoTensorField (I := I) (M := M) :=
  fun t x X Y => S.ricci t x (Realized.vec2 X Y)

@[simp] theorem ricciTwoTensorField_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (X Y : TangentSpace I x) :
    ricciTwoTensorField (I := I) S t x X Y =
      S.ricci t x (Realized.vec2 X Y) := by
  rfl

/-- Ricci component in a time-dependent frame. -/
def ricciCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  S.ricci t x (Realized.vec2 (frame i x) (frame j x))

@[simp] theorem ricciCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciCompInFrame (I := I) S frame t x i j =
      S.ricci t x (Realized.vec2 (frame i x) (frame j x)) := by
  rfl

/-- Ricci with both indices raised:
`Ric^{ij} = g^{ia} g^{jb} Ric_ab`. -/
def raisedRicciCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx,
    gInv t x i a * gInv t x j b *
      ricciCompInFrame (I := I) S frame t x a b

@[simp] theorem raisedRicciCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    raisedRicciCompInFrame (I := I) S gInv frame t x i j =
      ∑ a : Idx, ∑ b : Idx,
        gInv t x i a * gInv t x j b *
          ricciCompInFrame (I := I) S frame t x a b := by
  rfl

/-- Ricci with the second index raised:
`Ric_i^k = g^{ka} Ric_ia`. -/
def ricciOneUpCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i k : Idx) : Real :=
  ∑ a : Idx, gInv t x k a * ricciCompInFrame (I := I) S frame t x i a

@[simp] theorem ricciOneUpCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i k : Idx) :
    ricciOneUpCompInFrame (I := I) S gInv frame t x i k =
      ∑ a : Idx, gInv t x k a * ricciCompInFrame (I := I) S frame t x i a := by
  rfl

/-- The quadratic term `Ric_i^k Ric_kj` from Lemma 6.3. -/
def ricciQuadraticCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx,
    ricciOneUpCompInFrame (I := I) S gInv frame t x i k *
      ricciCompInFrame (I := I) S frame t x k j

@[simp] theorem ricciQuadraticCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciQuadraticCompInFrame (I := I) S gInv frame t x i j =
      ∑ k : Idx,
        ricciOneUpCompInFrame (I := I) S gInv frame t x i k *
          ricciCompInFrame (I := I) S frame t x k j := by
  rfl

/-- The curvature-Ricci contraction `R_ikjl Ric^{kl}` from Lemma 6.3. -/
def rmRicciContractionCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
      raisedRicciCompInFrame (I := I) S gInv frame t x k l

@[simp] theorem rmRicciContractionCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j =
      ∑ k : Idx, ∑ l : Idx,
        Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
          raisedRicciCompInFrame (I := I) S gInv frame t x k l := by
  rfl

/-- Component RHS for Lemma 6.3 in the project lowered-curvature convention:
`Delta Ric_ij - 2 * rmRicciContractionCompInFrame - 2 Ric_i^k Ric_kj`. -/
-- Convention note: in this file's `Rm04(W,X,Y,Z) = g(W,R(X,Y)Z)` slot order,
-- the implementation below has a minus sign on `rmRicciContractionCompInFrame`.
def ricciEvolutionRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  roughLapRic t x i j -
    2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j -
      2 * ricciQuadraticCompInFrame (I := I) S gInv frame t x i j

@[simp] theorem ricciEvolutionRHSInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) :
    ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j =
      roughLapRic t x i j -
        2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j -
          2 * ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  rfl

/-- Coordinate Ricci norm square for a folder-level Ricci-flow solution. -/
def ricciNormSqInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      ricciCompInFrame (I := I) S frame t x i j *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j

@[simp] theorem ricciNormSqInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        ricciCompInFrame (I := I) S frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j := by
  rfl

/-- Coordinate inner product `<roughDelta Ric, Ric>` for a folder-level
Ricci-flow solution. -/
def roughLapRicciInnerInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      roughLapRic t x i j *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j

@[simp] theorem roughLapRicciInnerInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        roughLapRic t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j := by
  rfl

/-- Coordinate squared norm of `nabla Ric`. -/
def nablaRicciNormSqInFrame
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx) :
    Real -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      gInv t x a b * gInv t x i k * gInv t x j l *
        nablaRic t x a i j * nablaRic t x b k l

@[simp] theorem nablaRicciNormSqInFrame_apply
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (t : Real) (x : M) :
    nablaRicciNormSqInFrame (M := M) nablaRic gInv t x =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x a b * gInv t x i k * gInv t x j l *
          nablaRic t x a i j * nablaRic t x b k l := by
  rfl

/-- The curvature-Ricci-Ricci term `R_ikjl Ric^ij Ric^kl`. -/
def curvRicciRicciInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x k l

@[simp] theorem curvRicciRicciInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j *
            raisedRicciCompInFrame (I := I) S gInv frame t x k l := by
  rfl

/-- Canonical curvature reaction in the Ricci-norm evolution formula.

With the project convention `Rm04(W,X,Y,Z) = g(W,R(X,Y)Z)`, the book term
`R_ikjl Ric^{ij} Ric^{kl}` is the negative of `curvRicciRicciInFrame`. -/
def ricciNormCurvatureReactionInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x => -curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x

@[simp] theorem ricciNormCurvatureReactionInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      -curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x := by
  rfl

/-- The inverse-metric part of the Ricci-flow metric evolution:
`partial_t g^{ij} = 2 Ric^{ij}`.  The future geometric proof differentiates
`g^{ik} g_kj = delta^i_j` and uses `partial_t g_ij = -2 Ric_ij`. -/
def inverseMetricEvolutionRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  2 * raisedRicciCompInFrame (I := I) S gInv frame t x i j

/-- Component equation `partial_t g^{ij} = 2 Ric^{ij}`. -/
def InverseMetricEvolutionEquationInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
        (t : Real) x i j)
      D.carrier
      (t : Real)

/-- Product-rule RHS for differentiating `Ric^{ij}`. -/
def raisedRicciDerivRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx,
    (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x i a *
        gInv t x j b * ricciCompInFrame (I := I) S frame t x a b +
      gInv t x i a *
        inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x j b *
          ricciCompInFrame (I := I) S frame t x a b +
        gInv t x i a * gInv t x j b *
          ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x a b)

/-- Product-rule RHS for differentiating `|Ric|^2 = Ric_ij Ric^ij`. -/
def ricciNormDerivRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j +
      ricciCompInFrame (I := I) S frame t x i j *
        raisedRicciDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j)

/-- The remaining finite-sum simplification in Lemma 6.7.

This is the explicit cancellation/reindexing frontier: after the product rule,
the inverse-metric variation terms cancel the `-2 Ric_i^k Ric_kj` part of
Lemma 6.3, leaving `2 <roughDelta Ric, Ric> + 4 R_ikjl Ric^ij Ric^kl`. -/
def RicciNormDerivativeSimplifiesInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      2 * roughLapInner (t : Real) x + 4 * reaction (t : Real) x

/-- Canonical finite-sum simplification for the time derivative of
`|Ric|^2`.

After differentiating the inverse metrics and substituting Lemma 6.3, the
inverse-metric derivative terms cancel the Ricci-quadratic terms, and the
curvature term is recorded with the project `Rm04(W,X,Y,Z)` sign convention. -/
theorem ricciNormDerivativeSimplifiesInFrame_canonical
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    RicciNormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame roughLapRic
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  classical
  intro t x
  let G : Idx -> Idx -> Real := fun i j => gInv (t : Real) x i j
  let A : Idx -> Idx -> Real :=
    fun i j => ricciCompInFrame (I := I) S frame (t : Real) x i j
  let L : Idx -> Idx -> Real := fun i j => roughLapRic (t : Real) x i j
  let C : Idx -> Idx -> Real :=
    fun i j =>
      rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame (t : Real) x i j
  have hG : forall i j, G i j = G j i := by
    intro i j
    exact hInvSym (t : Real) x i j
  have hA : forall i j, A i j = A j i := by
    intro i j
    exact hRicSym (t : Real) x i j
  have hpure := ricciNormDerivativeSimplifies_pure (Idx := Idx) G A L C hG hA
  have hderiv :
      ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := by
    change
      (∑ i : Idx, ∑ j : Idx,
        ((L i j - 2 * C i j - 2 * quadraticBy G A i j) *
            raise2By G A i j +
          A i j *
            (∑ a : Idx, ∑ b : Idx,
              (2 * raise2By G A i a * G j b * A a b +
                G i a * (2 * raise2By G A j b) * A a b +
                  G i a * G j b *
                    (L a b - 2 * C a b - 2 * quadraticBy G A a b))))) =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j))
    exact hpure
  have hrough :
      roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame (t : Real) x =
        ∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j := by
    simp [G, A, L, roughLapRicciInnerInFrame, raisedRicciCompInFrame, raise2By]
  let R4 : Idx -> Idx -> Idx -> Idx -> Real :=
    fun i k j l => Realized.rm04Comp (I := I) (Rm04 (t : Real)) frame x i k j l
  let AR : Idx -> Idx -> Real := fun i j => raise2By G A i j
  have hcurv :
      (∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j) =
        curvRicciRicciInFrame (I := I) S Rm04 gInv frame (t : Real) x := by
    change
      (∑ i : Idx, ∑ j : Idx,
        (∑ k : Idx, ∑ l : Idx, R4 i k j l * AR k l) * AR i j) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          R4 i k j l * AR i j * AR k l
    exact sum_contraction_mul_eq_four_sum (Idx := Idx) R4 AR
  have hreaction :
      ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame (t : Real) x =
        -(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j) := by
    rw [ricciNormCurvatureReactionInFrame_apply, ← hcurv]
  calc
    ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := hderiv
    _ =
        2 * roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame (t : Real) x +
          4 * ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame
            (t : Real) x := by
          rw [hrough, hreaction]

/-- Lemma 6.3 in component/equation form.  This is the geometric frontier
needed before the norm evolution proof can be made constructive. -/
def RicciEvolutionEquationInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real)

/-- Project the inverse-metric evolution equation at fixed components. -/
theorem inverseMetricEvolutionEquationInFrame_apply
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {gInv : Real -> Realized.InverseMetricComponents M Idx}
    {frame : Idx -> (x : M) -> TangentSpace I x}
    (h : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
        (t : Real) x i j)
      D.carrier
      (t : Real) :=
  h t x i j

/-- Constructor for the inverse-metric evolution equation from component
derivative equalities. -/
theorem inverseMetricEvolutionEquationInFrame_of_components
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (h : ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
      HasDerivWithinAt
        (fun s : Real => gInv s x i j)
        (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
          (t : Real) x i j)
        D.carrier
        (t : Real)) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame :=
  h

/-- Project Lemma 6.3's component equation at fixed components. -/
theorem ricciEvolutionEquationInFrame_apply
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M)}
    {gInv : Real -> Realized.InverseMetricComponents M Idx}
    {frame : Idx -> (x : M) -> TangentSpace I x}
    {roughLapRic : Real -> M -> Idx -> Idx -> Real}
    (h : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real) :=
  h t x i j

/-- Constructor for Lemma 6.3's component equation from component derivative
equalities. -/
theorem ricciEvolutionEquationInFrame_of_components
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h : ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x i j)
        D.carrier
        (t : Real)) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic :=
  h

/-- Product-rule derivative of the raised Ricci components. -/
theorem raisedRicciCompInFrame_hasDerivWithinAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => raisedRicciCompInFrame (I := I) S gInv frame s x i j)
      (raisedRicciDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real) := by
  simpa [raisedRicciCompInFrame, raisedRicciDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun a s =>
        ∑ b : Idx,
          gInv s x i a * gInv s x j b *
            ricciCompInFrame (I := I) S frame s x a b)
      (A' := fun a =>
        ∑ b : Idx,
          (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x i a *
              gInv (t : Real) x j b *
                ricciCompInFrame (I := I) S frame (t : Real) x a b +
            gInv (t : Real) x i a *
              inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x j b *
                ricciCompInFrame (I := I) S frame (t : Real) x a b +
              gInv (t : Real) x i a * gInv (t : Real) x j b *
                ricciEvolutionRHSInFrame
                  (I := I) S Rm04 gInv frame roughLapRic (t : Real) x a b))
      (s := D.carrier) (x := (t : Real))
      (fun a _ha =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun b s =>
                gInv s x i a * gInv s x j b *
                  ricciCompInFrame (I := I) S frame s x a b)
              (A' := fun b =>
                (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x i a *
                    gInv (t : Real) x j b *
                      ricciCompInFrame (I := I) S frame (t : Real) x a b +
                  gInv (t : Real) x i a *
                    inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x j b *
                      ricciCompInFrame (I := I) S frame (t : Real) x a b +
                    gInv (t : Real) x i a * gInv (t : Real) x j b *
                      ricciEvolutionRHSInFrame
                        (I := I) S Rm04 gInv frame roughLapRic (t : Real) x a b))
              (s := D.carrier) (x := (t : Real))
              (fun b _hb =>
                by
                  have hia := h_inv t x i a
                  have hjb := h_inv t x j b
                  have hrab := h_ricci t x a b
                  have hprod := (hia.mul hjb).mul hrab
                  simpa [Pi.mul_apply, mul_assoc, add_mul] using hprod))))

/-- Product-rule derivative of the coordinate Ricci norm square. -/
theorem ricciNormSqInFrame_hasDerivWithinAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) :
    HasDerivWithinAt
      (fun s : Real => ricciNormSqInFrame (I := I) S gInv frame s x)
      (ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x)
      D.carrier
      (t : Real) := by
  simpa [ricciNormSqInFrame, ricciNormDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun i s =>
        ∑ j : Idx,
          ricciCompInFrame (I := I) S frame s x i j *
            raisedRicciCompInFrame (I := I) S gInv frame s x i j)
      (A' := fun i =>
        ∑ j : Idx,
          (ricciEvolutionRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j *
              raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j +
            ricciCompInFrame (I := I) S frame (t : Real) x i j *
              raisedRicciDerivRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
      (s := D.carrier) (x := (t : Real))
      (fun i _hi =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun j s =>
                ricciCompInFrame (I := I) S frame s x i j *
                  raisedRicciCompInFrame (I := I) S gInv frame s x i j)
              (A' := fun j =>
                (ricciEvolutionRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j *
                    raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j +
                  ricciCompInFrame (I := I) S frame (t : Real) x i j *
                    raisedRicciDerivRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
              (s := D.carrier) (x := (t : Real))
              (fun j _hj =>
                by
                  have hRic := h_ricci t x i j
                  have hRaised :=
                    raisedRicciCompInFrame_hasDerivWithinAt
                      (I := I) S Rm04 gInv frame roughLapRic h_inv h_ricci t x i j
                  have hprod := hRic.mul hRaised
                  simpa [Pi.mul_apply] using hprod))))

end Components

/-- Scalar curvature evolution in Section 6.2:
`∂_t R = Δ R + 2 |Ric|²`. -/
def ScalarEvolutionEquationOn
    {D : Realized.RealTimeInterval}
    (scalar scalarLap ricciNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => scalar s x)
      (scalarLap (t : Real) x + 2 * ricciNormSq (t : Real) x)
      D.carrier
      (t : Real)

/-! ## Lemma 6.7: Ricci norm heat equation, component assembly -/

/-- Time derivative component identity for `|Ric|²`.

This is the point where differentiating inverse metrics and using Lemma 6.3 has
already cancelled the cubic `Ric_i^k Ric_kj` terms. -/
def RicciNormTimeDerivativeComponentsOn
    {D : Realized.RealTimeInterval}
    (ricciNormSq roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => ricciNormSq s x)
      (2 * roughLapInner (t : Real) x + 4 * reaction (t : Real) x)
      D.carrier
      (t : Real)

section RicciNormDerivative

variable {Idx : Type*} [Fintype Idx]

/-- The time-derivative identity for `|Ric|^2` once the component evolution
equations and the remaining finite-sum simplification are supplied. -/
theorem ricciNormTimeDerivativeComponentsOn_of_ricciEvolution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (h_simplify : RicciNormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame roughLapRic roughLapInner reaction) :
    RicciNormTimeDerivativeComponentsOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      roughLapInner reaction := by
  intro t x
  have hnorm :=
    ricciNormSqInFrame_hasDerivWithinAt
      (I := I) S Rm04 gInv frame roughLapRic h_inv h_ricci t x
  simpa [h_simplify t x] using hnorm

/-- Canonical time-derivative identity for `|Ric|^2` from Lemma 6.3 and the
inverse-metric evolution equation. -/
theorem ricciNormTimeDerivativeComponentsOn_of_ricciEvolution_canonical
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    RicciNormTimeDerivativeComponentsOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) :=
  ricciNormTimeDerivativeComponentsOn_of_ricciEvolution
    (I := I) S Rm04 gInv frame roughLapRic
    (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
    (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
    h_inv h_ricci
    (ricciNormDerivativeSimplifiesInFrame_canonical
      (I := I) S Rm04 gInv frame roughLapRic hInvSym hRicSym)

end RicciNormDerivative

/-- Laplacian component identity for `|Ric|²`:
`Δ |Ric|² = 2 <Δ Ric, Ric> + 2 |∇Ric|²`. -/
def RicciNormLaplacianComponentsOn
    (ricciNormLap roughLapInner nablaRicNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    ricciNormLap t x = 2 * roughLapInner t x + 2 * nablaRicNormSq t x

/-- Bridge from the realized Bochner coordinate predicate to the interval
Ricci-flow predicate. -/
theorem ricciNormLaplacianComponentsOn_of_bochner
    (ricciNormLap roughLapInner nablaRicNormSq : Real -> M -> Real)
    (h_lap : Realized.RicciNormLaplacianComponentsInFrame
      (M := M) (Time := Real) ricciNormLap roughLapInner nablaRicNormSq) :
    RicciNormLaplacianComponentsOn ricciNormLap roughLapInner nablaRicNormSq :=
  h_lap

/-- Canonical interval-level Ricci-norm Laplacian identity from the exact
coordinate Bochner expansion for `|Ric|^2`. -/
theorem ricciNormLaplacianComponentsOn_of_normSq_laplacian_expansion
    {D : Realized.RealTimeInterval}
    {Idx : Type*} [Fintype Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic) :
    RicciNormLaplacianComponentsOn
      ricciNormLap
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv) := by
  have hrealized :=
    Realized.ricciNormLaplacianComponentsInFrame_of_normSq_laplacian_expansion
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic h_lap
  intro t x
  simpa [Realized.roughLapRicciInnerInFrame, roughLapRicciInnerInFrame,
    Realized.raisedRicciComponentsInFrame, raisedRicciCompInFrame,
    ricciTwoTensorField, ricciCompInFrame, Realized.nablaRicciNormSqInFrame,
    nablaRicciNormSqInFrame] using hrealized t x

/-- Heat-equation form of Lemma 6.7:
`∂_t |Ric|² = Δ |Ric|² - 2 |∇Ric|² + 4 R_ikjl Ric^{ij} Ric^{kl}`. -/
def RicciNormHeatEquationOn
    {D : Realized.RealTimeInterval}
    (ricciNormSq ricciNormLap nablaRicNormSq reaction : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => ricciNormSq s x)
      (ricciNormLap (t : Real) x +
        (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x))
      D.carrier
      (t : Real)

/-- Algebraic assembly of Lemma 6.7 from the time-derivative and Laplacian
component identities. -/
theorem ricciNormHeatEquationOn_of_components
    {D : Realized.RealTimeInterval}
    (ricciNormSq ricciNormLap roughLapInner nablaRicNormSq reaction : Real -> M -> Real)
    (h_dt : RicciNormTimeDerivativeComponentsOn
      (D := D) ricciNormSq roughLapInner reaction)
    (h_lap : RicciNormLaplacianComponentsOn
      ricciNormLap roughLapInner nablaRicNormSq) :
    RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction := by
  intro t x
  have hvalue :
      ricciNormLap (t : Real) x +
          (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x) =
        2 * roughLapInner (t : Real) x + 4 * reaction (t : Real) x := by
    rw [h_lap (t : Real) x]
    ring
  rw [hvalue]
  exact h_dt t x

section RicciNormAssembly

variable {Idx : Type*} [Fintype Idx]

/-- Section 6.2 Ricci-norm heat identity for a folder-level solution, reduced
to inverse-metric evolution, Ricci evolution, symmetry, and the Bochner
Laplacian component frontier. -/
theorem ricciNormHeatEquationOn_of_solution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap nablaRicNormSq : Real -> M -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (h_lap : RicciNormLaplacianComponentsOn
      ricciNormLap
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      nablaRicNormSq) :
    RicciNormHeatEquationOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap nablaRicNormSq
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  exact
    ricciNormHeatEquationOn_of_components
      (D := D)
      (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      nablaRicNormSq
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
      (ricciNormTimeDerivativeComponentsOn_of_ricciEvolution_canonical
        (I := I) S Rm04 gInv frame roughLapRic
        h_inv h_ricci hInvSym hRicSym)
      h_lap

/-- Canonical Lemma 6.7 consumer using the exact Ricci-norm Bochner expansion
instead of an already-packaged Laplacian component identity. -/
theorem ricciNormHeatEquationOn_of_solution_canonical_laplacian
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic) :
    RicciNormHeatEquationOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  exact
    ricciNormHeatEquationOn_of_solution
      (I := I) S Rm04 gInv frame roughLapRic ricciNormLap
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      h_inv h_ricci hInvSym hRicSym
      (ricciNormLaplacianComponentsOn_of_normSq_laplacian_expansion
        (I := I) S gInv frame roughLapRic ricciNormLap nablaRic h_lap)

end RicciNormAssembly

end RicciFlow
end RicciFlower
