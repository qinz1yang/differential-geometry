import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ShiftedReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Lichnerowicz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.MetricVariationBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.TensorWeak
import DifferentialGeometry.Geometry.Curvature.Realized.CurvatureProducers
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Regularity
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TwoTensor
import DifferentialGeometry.Geometry.Connection.LeviCivita.KoszulFormula
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.TimeSlab

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Ricci positivity and pinching preservation

This file contains the Ricci-flow-specific consumer layer for LaTeX Lemma 9.1
and Lemma 9.2.  The results here are conditional on the current tensor weak
maximum principle regularity package.  They do not reopen the analytic proof of
Hamilton's tensor maximum principle.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Connection
open Bundle
open Tensor0SBundle
open scoped BigOperators Manifold ContDiff

/-! ## Conditional tensor-WMP consumers -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

private theorem real_smul0S_apply {s : ℕ} {x : M} (c : Real)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s → TangentSpace I x) :
    (c • A) v = c * A v := by
  rw [Tensor0SSpace.smul_apply, smul_eq_mul]

private theorem tensor02_zero_apply {x : M}
    (A : Tensor02At (I := I) (M := M) x) :
    A (0 : Fin 2 → TangentSpace I x) = 0 := by
  with_unfolding_all exact A.map_coord_zero (0 : Fin 2) rfl

/-- Component-realization predicate for the shifted first-null block reaction.

This is deliberately only an equality to the finite-dimensional block target.
It does not assert that a raw tensor input has already been put into block
form, nor that the supplied reaction is the canonical Ricci-flow reaction. -/
def ShiftBlockReactRealizes
    (G : Real -> SmoothRiemannianMetric I M)
    (N : TwoTensorReaction (I := I) (M := M))
    (delta t : Real)
    (A : RawTwoTensorField (I := I) (M := M)) {x : M}
    (v : TangentSpace I x) (a b c : Real) : Prop :=
  (N t (G t) A) x v v = shiftReactBlock3 delta a b c

/-- A symmetric-input null condition follows from a shifted first-null block
realization plus the strict block algebra.  The geometric producer still has to
show the reaction component equals `shiftReactBlock3`; this theorem only
packages the algebraic nonnegativity once that component realization is known. -/
theorem shiftNullSymm_of_block
    {G : Real -> SmoothRiemannianMetric I M}
    {N : TwoTensorReaction (I := I) (M := M)}
    {U : Set Real} {delta : Real}
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3)
    (hreal :
      ∀ t, t ∈ U -> ∀ A : RawTwoTensorField (I := I) (M := M), ∀ x,
        TwoTensorSymmetricAt (I := I) (M := M) A x ->
        TwoTensorBilinearAt (I := I) (M := M) A x ->
        TwoTensorNonnegativeAt (I := I) (M := M) A x ->
        ∀ v : TangentSpace I x,
          A x v v = 0 ->
          ∃ a b c : Real,
            ShiftBlockReactRealizes (I := I) (M := M) G N delta t A v a b c) :
    TensorNullEigenvectorConditionSymm (I := I) (M := M) G N U := by
  intro t ht A x hsym hbilin hA v hv
  rcases hreal t ht A x hsym hbilin hA v hv with ⟨a, b, c, hreact⟩
  rw [hreact]
  exact shiftReactBlock3_nonneg delta a b c hdelta0 hdelta13

/-- Scaled component-realization predicate for arbitrary null vectors.

If `v = r • e₀`, a bilinear reaction evaluates at `(v,v)` as `r^2` times the
unit block component.  This is the shape needed by the raw WMP null predicate,
which quantifies arbitrary null vectors. -/
def ShiftBlockReactRealizesScaled
    (G : Real -> SmoothRiemannianMetric I M)
    (N : TwoTensorReaction (I := I) (M := M))
    (delta t : Real)
    (A : RawTwoTensorField (I := I) (M := M)) {x : M}
    (v : TangentSpace I x) (r a b c : Real) : Prop :=
  (N t (G t) A) x v v = r ^ 2 * shiftReactBlock3 delta a b c

/-- A symmetric-input null condition follows from a scaled first-null block
realization plus the strict block algebra.  This is the consumer theorem for
the future canonical shifted reaction producer. -/
theorem shiftNullSymm_of_block_scaled
    {G : Real -> SmoothRiemannianMetric I M}
    {N : TwoTensorReaction (I := I) (M := M)}
    {U : Set Real} {delta : Real}
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3)
    (hreal :
      ∀ t, t ∈ U -> ∀ A : RawTwoTensorField (I := I) (M := M), ∀ x,
        TwoTensorSymmetricAt (I := I) (M := M) A x ->
        TwoTensorBilinearAt (I := I) (M := M) A x ->
        TwoTensorNonnegativeAt (I := I) (M := M) A x ->
        ∀ v : TangentSpace I x,
          A x v v = 0 ->
          ∃ r a b c : Real,
            ShiftBlockReactRealizesScaled
              (I := I) (M := M) G N delta t A v r a b c) :
    TensorNullEigenvectorConditionSymm (I := I) (M := M) G N U := by
  intro t ht A x hsym hbilin hA v hv
  rcases hreal t ht A x hsym hbilin hA v hv with ⟨r, a, b, c, hreact⟩
  rw [hreact]
  exact mul_nonneg (sq_nonneg r)
    (shiftReactBlock3_nonneg delta a b c hdelta0 hdelta13)

/-- The pinching tensor `Ric - delta R g`. -/
def pinchTensor
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) (delta : Real) :
    TwoTensorFamily (I := I) (M := M) :=
  fun t x v w => Ric t x v w - delta * scalar t x * (G t).inner x v w

/-- Initial strict positivity of the Ricci tensor as a quadratic form. -/
def RicciPosInit
    (Ric : TwoTensorFamily (I := I) (M := M)) : Prop :=
  ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M) (Ric 0) x

/-- The compactness/eigenvalue-minimum input of Corollary 9.3: an initial
pinching constant has been selected. -/
def PinchInit
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) : Prop :=
  ∃ delta : Real,
    0 < delta ∧ delta <= (1 : Real) / 3 ∧
      TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
        (pinchTensor (I := I) (M := M) G Ric scalar delta) 0

/-- Strict version of the initial pinching selector, used by the shifted
pinching null-condition route where `delta = 1/3` is intentionally excluded. -/
def PinchInitLt
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) : Prop :=
  ∃ delta : Real,
    0 < delta ∧ delta < (1 : Real) / 3 ∧
      TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
        (pinchTensor (I := I) (M := M) G Ric scalar delta) 0

/-- Forget the strict upper bound in the compatibility initial pinching
selector. -/
theorem pinchInit_of_lt
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hinit : PinchInitLt (I := I) (M := M) G Ric scalar) :
    PinchInit (I := I) (M := M) G Ric scalar := by
  rcases hinit with ⟨delta, hdelta0, hdelta13, hpinch⟩
  exact ⟨delta, hdelta0, le_of_lt hdelta13, hpinch⟩

/-- Uniform initial bounds which imply a selected pinching constant.  The
compactness/eigenvalue selector for Corollary 9.3 should produce this package
from strict initial Ricci positivity and scalar trace compatibility. -/
def InitBounds
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) : Prop :=
  ∃ c C : Real,
    0 < c ∧ 0 < C ∧
      (∀ x v, c * (G 0).inner x v v <= Ric 0 x v v) ∧
      (∀ x, scalar 0 x <= C)

/-- A base-function realization of the least initial Ricci lower bound.
The remaining geometric selector frontier is to construct such a continuous
positive function from strict initial Ricci positivity. -/
def RicMinData
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (ricMin : M -> Real) : Prop :=
  Continuous ricMin ∧
    (∀ x, 0 < ricMin x) ∧
    (∀ x v, ricMin x * (G 0).inner x v v <= Ric 0 x v v)

/-- Initial Ricci tensor data realized as the Ricci tensor of the initial
metric.  This is the canonical 9.3 entrypoint; `RicMinData` below is only the
compactness adapter once a lower-bound function has been produced. -/
structure MetricRicciData
    [SigmaCompactSpace M] [T2Space M]
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M)) where
  K : CurvatureSectionProducerData
    (I := I) (M := M)
    (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) (G 0)) (G 0)
  ricci_eq :
    ∀ x v w, Ric 0 x v w = K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w)

/-- Strict positivity of the canonical initial Ricci tensor. -/
def MetricRicciPos
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric) : Prop :=
  ∀ x v, v ≠ 0 -> 0 < D.K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)

/-- A base lower-bound function for the canonical initial Ricci tensor. -/
def MetricRicciMin
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (ricMin : M -> Real) : Prop :=
  Continuous ricMin ∧
    (∀ x, 0 < ricMin x) ∧
    (∀ x v,
      ricMin x * (G 0).inner x v v <=
        D.K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v))

/-- The unit tangent bundle of one metric as a subtype of the actual tangent
bundle.  This is the compactness-facing interface for the 9.3 selector. -/
abbrev UnitTangent (g : SmoothRiemannianMetric I M) : Type _ :=
  MetricUnitTangent (I := I) (M := M) g

namespace UnitTangent

/-- Base point of a unit tangent vector. -/
def base {g : SmoothRiemannianMetric I M}
    (p : UnitTangent (I := I) (M := M) g) : M :=
  p.1.1

/-- Fiber vector of a unit tangent vector. -/
def vec {g : SmoothRiemannianMetric I M}
    (p : UnitTangent (I := I) (M := M) g) :
    TangentSpace I (base (I := I) (M := M) p) :=
  p.1.2

@[simp]
theorem unit {g : SmoothRiemannianMetric I M}
    (p : UnitTangent (I := I) (M := M) g) :
    g.inner (base (I := I) (M := M) p)
      (vec (I := I) (M := M) p) (vec (I := I) (M := M) p) = 1 :=
  p.2

@[simp]
theorem base_mk {g : SmoothRiemannianMetric I M} {x : M}
    {v : TangentSpace I x} {hunit : g.inner x v v = 1} :
    base (I := I) (M := M)
      (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
        UnitTangent (I := I) (M := M) g) = x :=
  rfl

@[simp]
theorem vec_mk {g : SmoothRiemannianMetric I M} {x : M}
    {v : TangentSpace I x} {hunit : g.inner x v v = 1} :
    vec (I := I) (M := M)
      (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
        UnitTangent (I := I) (M := M) g) = v :=
  rfl

end UnitTangent

/-- Uniform initial Ricci lower bound on `g_0`-unit vectors. -/
def UnitRicciLower
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric) (c : Real) : Prop :=
  0 < c ∧
    ∀ x (v : TangentSpace I x), (G 0).inner x v v = 1 ->
      c <= D.K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)

/-- Ricci quadratic evaluation on the initial unit tangent bundle. -/
def unitRicEval
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (p : UnitTangent (I := I) (M := M) (G 0)) : Real :=
  D.K.ricci (UnitTangent.base (I := I) (M := M) p)
    (DifferentialGeometry.Integral.Connection.vec2 (I := I)
      (UnitTangent.vec (I := I) (M := M) p)
      (UnitTangent.vec (I := I) (M := M) p))

/-- A unit-vector Ricci lower bound gives a constant base lower-bound
function. -/
theorem metricMin_unit
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {c : Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hlower : UnitRicciLower (I := I) (M := M) D c) :
    MetricRicciMin (I := I) (M := M) D (fun _ : M => c) := by
  rcases hlower with ⟨hc, hlower⟩
  refine ⟨continuous_const, fun _ => hc, ?_⟩
  intro x v
  by_cases hv : v = 0
  · subst v
    have hzero :
        D.K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I)
          (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0 := by
      have hzero' :
          D.K.ricci x (fun _ : Fin 2 => (0 : TangentSpace I x)) = 0 := by
        simpa [quad02] using
          DifferentialGeometry.tensor02_smul2 (I := I) (M := M) (D.K.ricci x)
            0 (0 : TangentSpace I x)
      have hvec :
          DifferentialGeometry.Integral.Connection.vec2 (I := I) (0 : TangentSpace I x) (0 : TangentSpace I x) =
            (fun _ : Fin 2 => (0 : TangentSpace I x)) := by
        funext i
        simp [DifferentialGeometry.Integral.Connection.vec2]
      simpa [hvec] using hzero'
    simp [hzero]
  let r : Real := (G 0).inner x v v
  have hrpos : 0 < r := by
    exact (G 0).pos x v hv
  let s : Real := Real.sqrt r
  have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  let a : Real := s⁻¹
  let u : TangentSpace I x := a • v
  have hss : s * s = r := by
    simpa [sq] using (Real.sq_sqrt (le_of_lt hrpos))
  have haa : a * a * r = 1 := by
    have hmul : (s * s) * (s⁻¹ * s⁻¹) = 1 := by
      field_simp [hsne]
    calc
      a * a * r = (s⁻¹ * s⁻¹) * (s * s) := by
        rw [hss]
      _ = (s * s) * (s⁻¹ * s⁻¹) := by ring
      _ = 1 := hmul
  have hunit : (G 0).inner x u u = 1 := by
    calc
      (G 0).inner x u u = a * a * r := by
        simpa [u, r] using DifferentialGeometry.metric_smul2 (I := I) (M := M) (G 0) a v
      _ = 1 := haa
  have hRic_unit := hlower x u hunit
  have hRic_scale :
      D.K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I) u u) =
        a * a * D.K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) := by
    have hscale' :
        D.K.ricci x (fun _ : Fin 2 => a • v) =
          a * a * D.K.ricci x (fun _ : Fin 2 => v) := by
      simpa [quad02] using
        DifferentialGeometry.tensor02_smul2 (I := I) (M := M)
          (D.K.ricci x) a v
    have hvecu :
        DifferentialGeometry.Integral.Connection.vec2 (I := I) u u = (fun _ : Fin 2 => u) := by
      funext i
      simp [DifferentialGeometry.Integral.Connection.vec2]
    have hvecv :
        DifferentialGeometry.Integral.Connection.vec2 (I := I) v v = (fun _ : Fin 2 => v) := by
      funext i
      simp [DifferentialGeometry.Integral.Connection.vec2]
    simpa [hvecu, hvecv, u] using hscale'
  have hineq :
      c <= a * a * D.K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) := by
    simpa [hRic_scale] using hRic_unit
  have hs2_nonneg : 0 <= s * s := mul_nonneg (le_of_lt hspos) (le_of_lt hspos)
  have hmul := mul_le_mul_of_nonneg_left hineq hs2_nonneg
  have hcancel : (s * s) * (a * a *
        D.K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)) =
      D.K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) := by
    have hmul : (s * s) * (a * a) = 1 := by
      have hsa : s * a = 1 := by
        simp [a, hsne]
      calc
        (s * s) * (a * a) = (s * a) * (s * a) := by ring
        _ = 1 := by rw [hsa]; ring
    calc
      (s * s) * (a * a *
          D.K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)) =
          ((s * s) * (a * a)) *
            D.K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) := by ring
      _ = D.K.ricci x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) := by
        rw [hmul]
        ring
  have hleft : (s * s) * c = c * (G 0).inner x v v := by
    rw [hss]
    ring
  rwa [hcancel, hleft] at hmul

/-- Compactness of the initial unit tangent bundle gives a uniform positive
Ricci lower bound on unit vectors.  The remaining geometry outside this file is
to supply the compactness and continuity inputs for the canonical unit tangent
bundle. -/
theorem unitLower_raw
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hcompact : IsCompact (Set.univ : Set (UnitTangent (I := I) (M := M) (G 0))))
    (hcont : Continuous (unitRicEval (I := I) (M := M) D)) :
    ∃ c : Real, UnitRicciLower (I := I) (M := M) D c := by
  classical
  by_cases hne : (Set.univ : Set (UnitTangent (I := I) (M := M) (G 0))).Nonempty
  · obtain ⟨p0, _hp0, hmin⟩ :=
      hcompact.exists_isMinOn hne hcont.continuousOn
    let c : Real :=
      unitRicEval (I := I) (M := M) D p0
    have hc : 0 < c := by
      let x0 := UnitTangent.base (I := I) (M := M) p0
      let v0 := UnitTangent.vec (I := I) (M := M) p0
      have hunit0 : (G 0).inner x0 v0 v0 = 1 := by
        simp [x0, v0, UnitTangent.unit]
      have hv0 : v0 ≠ 0 := by
        intro hz
        have hbad : (0 : Real) = 1 := by
          simp [hz] at hunit0
        norm_num at hbad
      exact hpos x0 v0 hv0
    refine ⟨c, hc, ?_⟩
    intro x v hunit
    let p : UnitTangent (I := I) (M := M) (G 0) :=
      ⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩
    exact (isMinOn_iff.mp hmin) p (Set.mem_univ p)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x v hunit
    exfalso
    exact hne ⟨⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩, Set.mem_univ _⟩

/-- Compactness of the unit tangent bundle of a compact base.  This is the
remaining vector-bundle topology producer: prove it by local trivializations,
compact model spheres, and a finite subcover of the base. -/
theorem unitTan_compact
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    IsCompact (Set.univ : Set (UnitTangent (I := I) (M := M) g)) := by
  exact metricUnit_compact (I := I) (M := M) g

/-- Continuity of the Ricci quadratic form on the initial unit tangent bundle. -/
theorem unitRic_cont
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric) :
    Continuous (unitRicEval (I := I) (M := M) D) := by
  refine (metricUnit_quadCont (I := I) (M := M) (G 0) D.K.ricci).congr ?_
  intro p
  dsimp [unitRicEval, quad02, UnitTangent.base, UnitTangent.vec,
    MetricUnitTangent.base, MetricUnitTangent.vec]
  congr 1
  funext i
  fin_cases i <;> simp [DifferentialGeometry.Integral.Connection.vec2]

/-- Unit tangent compactness and unit Ricci positivity produce a uniform
positive Ricci lower bound on unit vectors. -/
theorem unitLower_pos
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D) :
    ∃ c : Real, UnitRicciLower (I := I) (M := M) D c := by
  exact unitLower_raw (I := I) (M := M) D hpos
    (unitTan_compact (I := I) (M := M) (G 0))
    (unitRic_cont (I := I) (M := M) D)

/-- Unit tangent compactness and unit Ricci positivity produce a constant
metric/Ricci lower-bound function. -/
theorem metricMin_pos
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D) :
    ∃ ricMin : M -> Real,
      MetricRicciMin (I := I) (M := M) D ricMin := by
  rcases unitLower_pos (I := I) (M := M) D hpos with ⟨c, hc⟩
  exact ⟨fun _ : M => c, metricMin_unit (I := I) (M := M) D hc⟩

/-- Canonical Ricci positivity implies the legacy pointwise positivity
predicate for the supplied Ricci family. -/
theorem ricciPos_metric
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D) :
    RicciPosInit (I := I) (M := M) Ric := by
  intro x v hv
  rw [D.ricci_eq x v v]
  exact hpos x v hv

/-- A canonical initial Ricci lower-bound function is the older `RicMinData`
adapter for the supplied Ricci family. -/
theorem ricMin_of_metric
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {ricMin : M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin) :
    RicMinData (I := I) (M := M) G Ric ricMin := by
  rcases hmin with ⟨hcont, hpos, hlower⟩
  refine ⟨hcont, hpos, ?_⟩
  intro x v
  rw [D.ricci_eq x v v]
  exact hlower x v

/-- Compactness-facing selector predicate: strict initial Ricci positivity
supplies the uniform bounds used to select the pinching constant. -/
def BoundsOfPosRic
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) : Prop :=
  RicciPosInit (I := I) (M := M) Ric ->
    InitBounds (I := I) (M := M) G Ric scalar

/-- A realized Ricci-minimum lower bound implies strict initial Ricci
positivity. -/
theorem ricPos_ricMin
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {ricMin : M -> Real}
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin) :
    RicciPosInit (I := I) (M := M) Ric := by
  rcases hmin with ⟨_hcont, hpos, hlower⟩
  intro x v hv
  have hgpos : 0 < (G 0).inner x v v := (G 0).pos x v hv
  exact lt_of_lt_of_le (mul_pos (hpos x) hgpos) (hlower x v)

/-- A continuous scalar curvature has a positive upper bound on compact
initial space. -/
theorem scalarUpper_cont
    [CompactSpace M] [Nonempty M]
    {scalar : Real -> M -> Real}
    (hcont : Continuous (fun x : M => scalar 0 x)) :
    ∃ C : Real, 0 < C ∧ ∀ x, scalar 0 x <= C := by
  have hcompact : IsCompact (Set.univ : Set M) := isCompact_univ
  have hnonempty : (Set.univ : Set M).Nonempty := Set.univ_nonempty
  obtain ⟨x0, _hx0, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty hcont.continuousOn
  refine ⟨max 1 (scalar 0 x0), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (scalar 0 x0))
  · intro x
    exact le_trans (hmax (by simp : x ∈ (Set.univ : Set M)))
      (le_max_right 1 (scalar 0 x0))

/-- A continuous positive realized Ricci-minimum function supplies the uniform
initial lower Ricci bound once the scalar upper bound is known. -/
theorem bounds_ricMin
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : ∃ C : Real, 0 < C ∧ ∀ x, scalar 0 x <= C) :
    InitBounds (I := I) (M := M) G Ric scalar := by
  rcases hmin with ⟨hcont, hpos, hRicLower⟩
  rcases hscalar with ⟨C, hC, hScalarUpper⟩
  have hcompact : IsCompact (Set.univ : Set M) := isCompact_univ
  have hnonempty : (Set.univ : Set M).Nonempty := Set.univ_nonempty
  obtain ⟨x0, _hx0, hminOn⟩ :=
    hcompact.exists_isMinOn hnonempty hcont.continuousOn
  let c : Real := ricMin x0
  have hc : 0 < c := by
    dsimp [c]
    exact hpos x0
  have hc_le : ∀ x : M, c <= ricMin x := by
    intro x
    exact hminOn (by simp : x ∈ (Set.univ : Set M))
  refine ⟨c, C, hc, hC, ?_, hScalarUpper⟩
  intro x v
  have hg_nonneg : 0 <= (G 0).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact le_of_lt ((G 0).pos x v hv)
  exact le_trans (mul_le_mul_of_nonneg_right (hc_le x) hg_nonneg)
    (hRicLower x v)

/-- The base-function selector also supplies the older compactness-facing
selector predicate. -/
theorem boundsPos_ricMin
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    BoundsOfPosRic (I := I) (M := M) G Ric scalar := by
  intro _hpos
  exact bounds_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (ricMin := ricMin) hmin
    (scalarUpper_cont (M := M) hscalar)

/-- Uniform initial lower Ricci and upper scalar bounds select a strict
initial pinching constant `0 < delta < 1/3`. -/
theorem pinchInitLt_bounds
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hbounds : InitBounds (I := I) (M := M) G Ric scalar) :
    PinchInitLt (I := I) (M := M) G Ric scalar := by
  rcases hbounds with ⟨c, C, hc, hC, hRicLower, hScalarUpper⟩
  let delta : Real := min ((1 : Real) / 6) (c / C)
  have hsix_pos : 0 < (1 : Real) / 6 := by norm_num
  have hdiv_pos : 0 < c / C := div_pos hc hC
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min hsix_pos hdiv_pos
  have hdelta_le_six : delta <= (1 : Real) / 6 := by
    dsimp [delta]
    exact min_le_left _ _
  have hdelta_lt_third : delta < (1 : Real) / 3 := by
    nlinarith
  have hdelta_nonneg : 0 <= delta := le_of_lt hdelta_pos
  have hdelta_le_div : delta <= c / C := by
    dsimp [delta]
    exact min_le_right _ _
  have hdeltaC_le_c : delta * C <= c := by
    have hmul := mul_le_mul_of_nonneg_right hdelta_le_div (le_of_lt hC)
    have hcancel : c / C * C = c := div_mul_cancel₀ c (ne_of_gt hC)
    nlinarith
  refine ⟨delta, hdelta_pos, hdelta_lt_third, ?_⟩
  intro x v
  have hg_nonneg : 0 <= (G 0).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact le_of_lt ((G 0).pos x v hv)
  have hscalar_le : delta * scalar 0 x <= delta * C :=
    mul_le_mul_of_nonneg_left (hScalarUpper x) hdelta_nonneg
  have hscaled_le :
      delta * scalar 0 x * (G 0).inner x v v <= c * (G 0).inner x v v := by
    calc
      delta * scalar 0 x * (G 0).inner x v v
          = (delta * scalar 0 x) * (G 0).inner x v v := by ring
      _ <= (delta * C) * (G 0).inner x v v :=
          mul_le_mul_of_nonneg_right hscalar_le hg_nonneg
      _ <= c * (G 0).inner x v v :=
          mul_le_mul_of_nonneg_right hdeltaC_le_c hg_nonneg
  have hpinch_le : delta * scalar 0 x * (G 0).inner x v v <= Ric 0 x v v :=
    le_trans hscaled_le (hRicLower x v)
  simpa [pinchTensor, sub_nonneg] using hpinch_le

/-- Uniform initial lower Ricci and upper scalar bounds select an initial
pinching constant. -/
theorem pinchInit_of_bounds
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hbounds : InitBounds (I := I) (M := M) G Ric scalar) :
    PinchInit (I := I) (M := M) G Ric scalar := by
  exact pinchInit_of_lt (I := I) (M := M)
    (pinchInitLt_bounds (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) hbounds)

/-- Strict initial Ricci positivity gives strict initial pinching once the
compactness selector has produced the uniform initial bounds. -/
theorem pinchInitLt_of_pos
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hpos : RicciPosInit (I := I) (M := M) Ric)
    (hbounds : BoundsOfPosRic (I := I) (M := M) G Ric scalar) :
    PinchInitLt (I := I) (M := M) G Ric scalar := by
  exact pinchInitLt_bounds (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (hbounds hpos)

/-- Strict initial Ricci positivity gives initial pinching once the compactness
selector has produced the uniform initial bounds. -/
theorem pinchInit_of_pos
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hpos : RicciPosInit (I := I) (M := M) Ric)
    (hbounds : BoundsOfPosRic (I := I) (M := M) G Ric scalar) :
    PinchInit (I := I) (M := M) G Ric scalar := by
  exact pinchInit_of_lt (I := I) (M := M)
    (pinchInitLt_of_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) hpos hbounds)

/-- A realized Ricci-minimum lower bound and scalar continuity select a strict
initial pinching constant. -/
theorem pinchInitLt_ricMin
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInitLt (I := I) (M := M) G Ric scalar :=
  pinchInitLt_bounds (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar)
    (bounds_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin
      (scalarUpper_cont (M := M) hscalar))

/-- A realized Ricci-minimum lower bound and scalar continuity select the
initial pinching constant. -/
theorem pinchInit_ricMin
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInit (I := I) (M := M) G Ric scalar :=
  pinchInit_of_lt (I := I) (M := M)
    (pinchInitLt_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin hscalar)

/-- Metric/Ricci-native initial pinching selector.  The remaining geometric
producer is now the canonical lower-bound function for the initial Ricci tensor,
not a lower-bound function for an arbitrary supplied tensor family. -/
theorem pinchInitLt_metric
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInitLt (I := I) (M := M) G Ric scalar :=
  pinchInitLt_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (ricMin := ricMin)
    (ricMin_of_metric (I := I) (M := M) D hmin) hscalar

/-- Metric/Ricci-native initial pinching selector.  The remaining geometric
producer is now the canonical lower-bound function for the initial Ricci tensor,
not a lower-bound function for an arbitrary supplied tensor family. -/
theorem pinchInit_metric
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInit (I := I) (M := M) G Ric scalar :=
  pinchInit_of_lt (I := I) (M := M)
    (pinchInitLt_metric (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) D hmin hscalar)

/-- Metric/Ricci-native initial pinching selector from the unit tangent compact
minimum route. -/
theorem pinchInitLt_pos
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInitLt (I := I) (M := M) G Ric scalar := by
  rcases metricMin_pos (I := I) (M := M) D hpos with ⟨ricMin, hmin⟩
  exact pinchInitLt_metric (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (ricMin := ricMin) D hmin hscalar

/-- Metric/Ricci-native initial pinching selector from the unit tangent compact
minimum route. -/
theorem pinchInit_pos
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInit (I := I) (M := M) G Ric scalar := by
  exact pinchInit_of_lt (I := I) (M := M)
    (pinchInitLt_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) D hpos hscalar)

/-- Canonical initial metric/Ricci data for a Ricci-flow solution candidate. -/
noncomputable def metricData_sol0
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    MetricRicciData (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) where
  K := metricCurvData (I := I) (M := M) (S.base.metric 0)
  ricci_eq := by
    intro x v w
    simp [twoTensorSecToFamily, SolutionOn.ricci, SolutionFamily.ricci,
      metricCurvData, DifferentialGeometry.Integral.Connection.metricCurvData]

/-- Initial positivity of the solution Ricci tensor transfers to the canonical
metric/Ricci data package at time zero. -/
theorem metricData_sol0_pos
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hpos : RicciPosInit (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci)) :
    MetricRicciPos (I := I) (M := M)
      (metricData_sol0 (I := I) (M := M) S) := by
  intro x v hv
  have h := hpos x v hv
  simpa [metricData_sol0] using h

/-- Time-zero scalar curvature is continuous for a solution package. -/
theorem scalar0_cont_sol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (h0 : (0 : Real) ∈ D.carrier) :
    Continuous (fun x : M => S.scalar 0 x) := by
  have hmap : Continuous (fun y : M => ((0 : Real), y)) :=
    continuous_const.prodMk continuous_id
  have hmem : ∀ y : M, ((0 : Real), y) ∈ D.carrier ×ˢ (Set.univ : Set M) := by
    intro y
    exact ⟨h0, trivial⟩
  have hcomp := hS.scalarCont.comp_continuous hmap hmem
  simpa [Function.comp_def] using hcomp

/-- Preserved pinching conclusion for a fixed `delta`. -/
def PinchPres
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) (T delta : Real) : Prop :=
  TwoTensorFamilyNonnegativeOn (I := I) (M := M)
    (pinchTensor (I := I) (M := M) G Ric scalar delta) (Set.Icc 0 T)

/-! ### Ricci-flow producers for theorem 7.5 input packages -/

/-- The all-time `C^1` regularity of the Levi-Civita connection in a
Ricci-flow solution candidate. -/
theorem ricciCov1
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (S.base.connection t)
      (1 : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection] using
    (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric t))

/-- The all-time smoothness of the Levi-Civita connection in a Ricci-flow
solution candidate. -/
theorem ricciCovInf
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (S.base.connection t)
      (∞ : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection, metricCov] using
    metricCov_smooth (I := I) (M := M) (S.base.metric t)

/-- Metric compatibility of the canonical Levi-Civita connection in a
Ricci-flow solution candidate. -/
theorem ricciMetricComp
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
      (I := I) (S.base.connection t) (S.base.metric t) := by
  simpa [SolutionFamily.connection] using
    (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) (S.base.metric t))

/-- Canonical first and second spatial Ricci derivatives for a solution
candidate at one time. -/
noncomputable def ricciDerivsWMP
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (S.base.connection t) (S.ricci t) :=
  CanonicalSpatialDerivs0S.of_smooth_connection
    (E := E) (H := H) (I := I) (M := M)
    (S.base.connection t) (ricciCovInf (I := I) S t) (S.ricci t)

/-- Canonical smooth section representing `∇ Ric` for theorem 7.5 inputs. -/
noncomputable def ricciNablaWMP
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TensorNabla1SecFamily (I := I) (M := M) :=
  fun t => (ricciDerivsWMP (I := I) S t).nablaA

/-- Canonical smooth section representing `∇² Ric` for theorem 7.5 inputs. -/
noncomputable def ricciNabla2WMP
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TensorNabla2SecFamily (I := I) (M := M) :=
  fun t => (ricciDerivsWMP (I := I) S t).nabla2A

/-- The canonical Ricci derivative sections realize the first and second total
covariant derivatives required by theorem 7.5. -/
theorem ricciSpatialWMP
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TensorSpatialDerivs (I := I) (M := M)
      (fun t : Real => S.base.connection t) S.ricci
      (ricciNablaWMP (I := I) S) (ricciNabla2WMP (I := I) S) := by
  constructor
  · intro t
    simpa [ricciNablaWMP, ricciDerivsWMP] using
      (ricciDerivsWMP (I := I) S t).first
  · intro t
    simpa [ricciNablaWMP, ricciNabla2WMP, ricciDerivsWMP] using
      (ricciDerivsWMP (I := I) S t).second

/-- The canonical smooth section for the shifted pinching tensor
`Ric - delta R g`. -/
noncomputable def pinchSec
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    TwoTensorSecFamily (I := I) (M := M) :=
  fun t =>
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2
    let hscalar :
        ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun x : M => delta * S.scalar t x) := by
      have hR :
          ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
            (fun x : M => S.scalar t x) := by
        simpa [SolutionOn.scalar, SolutionFamily.scalar] using
          metricScalar_smooth (I := I) (M := M) (S.base.metric t)
      simpa only [Pi.mul_apply] using (contMDiff_const.mul hR)
    let Ric : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2 := S.ricci t
    Ric + (-1 : Real) •
      tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        (fun x : M => delta * S.scalar t x) hscalar
        (metricTensorField (I := I) (S.base.metric t))

/-- The coefficient tensor controlling the metric-barrier reaction variation:
`3 Ric - R g`. -/
noncomputable def pinchLipSec
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TwoTensorSecFamily (I := I) (M := M) :=
  fun t =>
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2
    let hscalar :
        ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun x : M => S.scalar t x) := by
      simpa [SolutionOn.scalar, SolutionFamily.scalar] using
        metricScalar_smooth (I := I) (M := M) (S.base.metric t)
    (3 : Real) • S.ricci t + (-1 : Real) •
      tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        (fun x : M => S.scalar t x) hscalar
        (metricTensorField (I := I) (S.base.metric t))

@[simp]
theorem pinchLipSec_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v w : TangentSpace I x) :
    (pinchLipSec (I := I) S t x) (vec2 (I := I) v w) =
      3 * S.ricciAt t x (vec2 (I := I) v w) -
        S.scalar t x * (S.base.metric t).inner x v w := by
  simp only [pinchLipSec, tensor0SField_smulByFun_apply,
    ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul]
  rw [metricTensorField_apply]
  have h0 : vec2 (I := I) v w 0 = v := by
    unfold DifferentialGeometry.Integral.Connection.vec2
    simp
  have h1 : vec2 (I := I) v w 1 = w := by
    unfold DifferentialGeometry.Integral.Connection.vec2
    norm_num
  rw [h0, h1]
  simp [SolutionOn.ricciAt, SolutionFamily.ricciAt]
  ring

@[simp]
theorem pinchSec_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta) =
      pinchTensor (I := I) (M := M) (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar delta := by
  funext t x v w
  simp only [pinchSec, pinchTensor, twoTensorSecToFamily,
    ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply, tensor0SField_smulByFun_apply,
    Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
    smul_eq_mul]
  change
    ((S.ricci t) x) (vec2 (I := I) v w) +
        (-1 : Real) * (delta * S.scalar t x *
          (metricTensorField (I := I) (S.base.metric t) x)
            (vec2 (I := I) v w)) =
      ((S.ricci t) x) (vec2 (I := I) v w) -
        delta * S.scalar t x * (S.base.metric t).inner x v w
  rw [metricTensorField_apply]
  have h0 : vec2 (I := I) v w 0 = v := by
    unfold DifferentialGeometry.Integral.Connection.vec2
    simp
  have h1 : vec2 (I := I) v w 1 = w := by
    unfold DifferentialGeometry.Integral.Connection.vec2
    norm_num
  rw [h0, h1]
  ring

private theorem pinchSec_at_trace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (delta t : Real) (x : M) :
    (pinchSec (I := I) S delta) t x =
      S.ricci t x -
        (delta *
          metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x)) •
          metricTensorField (I := I) (S.base.metric t) x := by
  have hscalar :
      S.scalar t x =
        metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) := by
    simp [SolutionOn.scalar_eq_metricTrace, SolutionOn.ricci,
      SolutionFamily.ricci, SolutionOn.ricciAt, SolutionFamily.ricciAt]
  apply ContinuousMultilinearMap.ext
  intro slots
  simp only [pinchSec, tensor0SField_smulByFun_apply,
    ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply]
  rw [hscalar]
  simp [sub_eq_add_neg]

/-- Pointwise symmetry of the canonical metric Ricci tensor. -/
theorem ricciAt_symm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) (S.ricciAt t x) := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)
      Real (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv :
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real := fun k l =>
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := I) (S.base.metric t) x k l (extChartAt I x x)
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis gInv := by
    simpa [basis, gInv] using
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (S.base.metric t) x
  exact DifferentialGeometry.Integral.Connection.ricciSym_of_basis
    (I := I) basis (S.ricciAt t x)
    (fun i j => by
      simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, basis, gInv] using
        DifferentialGeometry.Integral.Connection.metricRicciSymm (I := I) (M := M) (S.base.metric t)
          basis gInv hinv i j)

/-- Symmetry of the canonical Ricci section family. -/
theorem ricciSec_symm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (U : Set Real) :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) U := by
  intro t _ht x v w
  simpa [twoTensorSecToFamily, SolutionOn.ricci, SolutionFamily.ricci,
    SolutionOn.ricciAt, SolutionFamily.ricciAt] using
    ricciAt_symm (I := I) S t x v w

/-- Symmetry of the shifted pinching section `Ric - delta R g`. -/
theorem pinchSec_symm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) (U : Set Real) :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta)) U := by
  intro t _ht x v w
  rw [pinchSec_eq (I := I) S delta]
  simp only [pinchTensor]
  have hRic := ricciAt_symm (I := I) S t x v w
  have hg := (S.base.metric t).symm x v w
  simpa [twoTensorSecToFamily, SolutionOn.ricci, SolutionFamily.ricci,
    SolutionOn.ricciAt, SolutionFamily.ricciAt, hg] using congrArg
      (fun z => z - delta * S.scalar t x * (S.base.metric t).inner x w v)
      hRic

/-- On the section-backed shifted pinching tensor, the legacy raw adapter for
the canonical shifted reaction evaluates as the invariant tensor-backed
reaction.  This keeps future parabolic proofs away from the adapter's totality
fallback branch. -/
theorem shiftNRaw_pinch
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real)
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    (shiftNRaw (I := I) (M := M) delta t g
        (twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) t)) x v w =
      shiftNAt (I := I) (M := M) delta t g x
        ((pinchSec (I := I) S delta) t x)
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w) := by
  let Araw : RawTwoTensorField (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M)
      (pinchSec (I := I) S delta) t
  have hbilin : TwoTensorBilinearAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      twoTensorSecToFamily_bilin (I := I) (M := M)
        (pinchSec (I := I) S delta) t x
  have hsym : TwoTensorSymmetricAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      (pinchSec_symm (I := I) S delta Set.univ) t (by simp) x
  rw [show
      twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) t = Araw by rfl]
  rw [shiftNRaw, Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (I := I) (M := M) (shiftNAt (I := I) (M := M) delta)
    t g Araw x hbilin]
  have hrealSec :
      Tensor02RealizesRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x
        ((pinchSec (I := I) S delta) t x) := by
    intro X Y
    rw [rawSym2_eq_of_symm (I := I) (M := M) hsym X Y]
    rfl
  have hrealBundled :
      Tensor02RealizesRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x
        (tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin)) :=
    tensor02OfRawAt_realizes (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      (rawSym2_bilin (I := I) (M := M) hbilin)
  have hT :
      tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin) =
        (pinchSec (I := I) S delta) t x :=
    tensor02_realizes_ext (I := I) (M := M) hrealBundled hrealSec
  rw [hT]

/-- On the section-backed metric barrier for the shifted pinching tensor, the
legacy raw adapter for `shiftNRaw` evaluates as the invariant tensor-backed
reaction on the bundled barrier tensor. -/
theorem shiftNRaw_barrier
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (G : Real -> SmoothRiemannianMetric I M)
    (delta epsilon d t0 t : Real) (x : M)
    (v w : TangentSpace I x) :
    (shiftNRaw (I := I) (M := M) delta t (G t)
        (tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S delta))
          epsilon d t0 t)) x v w =
      shiftNAt (I := I) (M := M) delta t (G t) x
        (((pinchSec (I := I) S delta) t x) +
          (epsilon * (d + t - t0)) •
            metricTensorField (I := I) (G t) x)
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w) := by
  let Araw : RawTwoTensorField (I := I) (M := M) :=
    tensorBarrierFamily (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M)
        (pinchSec (I := I) S delta))
      epsilon d t0 t
  have hbaseBilin :
      TwoTensorBilinearAt (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) t) x := by
    exact twoTensorSecToFamily_bilin (I := I) (M := M)
      (pinchSec (I := I) S delta) t x
  have hbilin : TwoTensorBilinearAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      barrierBilinearAt (I := I) (M := M)
        (G := G)
        (S := twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta))
        (epsilon := epsilon) (delta := d) (t0 := t0) (t := t)
        (x := x) hbaseBilin
  have hbaseSymm :
      TwoTensorSymmetricAt (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) t) x := by
    exact (pinchSec_symm (I := I) S delta Set.univ) t (by simp) x
  have hsym : TwoTensorSymmetricAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      barrierSymmAt (I := I) (M := M)
        (G := G)
        (S := twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta))
        (epsilon := epsilon) (delta := d) (t0 := t0) (t := t)
        (x := x) hbaseSymm
  rw [show
      tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S delta))
          epsilon d t0 t = Araw by rfl]
  rw [shiftNRaw, Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (I := I) (M := M) (shiftNAt (I := I) (M := M) delta)
    t (G t) Araw x hbilin]
  let Bsec : TwoTensorSecFamily (I := I) (M := M) :=
    tensorBarrierSecFamily (I := I) (M := M) G
      (pinchSec (I := I) S delta) epsilon d t0
  have hrealSec :
      Tensor02RealizesRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x (Bsec t x) := by
    intro X Y
    rw [rawSym2_eq_of_symm (I := I) (M := M) hsym X Y]
    change Bsec t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Y) = Araw x X Y
    rw [show Bsec t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Y) =
        twoTensorSecToFamily (I := I) (M := M) Bsec t x X Y by rfl]
    simpa [Araw, Bsec] using
      tensorBarrierSec_apply (I := I) (M := M) G
        (pinchSec (I := I) S delta) epsilon d t0 t x X Y
  have hrealBundled :
      Tensor02RealizesRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x
        (tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin)) :=
    tensor02OfRawAt_realizes (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      (rawSym2_bilin (I := I) (M := M) hbilin)
  have hT :
      tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin) =
        Bsec t x :=
    tensor02_realizes_ext (I := I) (M := M) hrealBundled hrealSec
  rw [hT]
  simp [Bsec, tensorBarrierSecFamily]

/-- Difference between the raw shifted reaction on the section-backed metric
barrier and on the shifted pinching section itself.  The metric-barrier
variation is linear and controlled by `3 Ric - R g`. -/
theorem shiftNRaw_barrier_diff
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {delta epsilon d t0 t : Real} {x : M}
    (hdelta : delta < (1 : Real) / 3)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (v : TangentSpace I x) :
    (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
        (tensorBarrierFamily (I := I) (M := M)
          (fun s : Real => S.base.metric s)
          (twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S delta))
          epsilon d t0 t)) x v v -
      (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) t)) x v v =
        ((epsilon * (d + t - t0)) / (1 - 3 * delta)) *
          (2 * delta - 1) *
          (pinchLipSec (I := I) S t x) (vec2 (I := I) v v) := by
  let c : Real := epsilon * (d + t - t0)
  rw [shiftNRaw_barrier (I := I) (M := M) S
      (fun s : Real => S.base.metric s) delta epsilon d t0 t x v v]
  rw [shiftNRaw_pinch (I := I) (M := M) S delta t
      (S.base.metric t) x v v]
  have hdiff :=
    shiftNAt_add_g_quad (I := I) (M := M)
      (delta := delta) (c := c) (t := t) (g := S.base.metric t)
      (x := x) hdelta hdim ((pinchSec (I := I) S delta) t x) v
  have hcoeff :
      ((3 : Real) •
          shiftRic3At (I := I) (M := M) delta (S.base.metric t)
            ((pinchSec (I := I) S delta) t x) -
          metricTracePair0SAt (I := I) (S.base.metric t)
              (shiftRic3At (I := I) (M := M) delta (S.base.metric t)
                ((pinchSec (I := I) S delta) t x)) •
            metricTensorField (I := I) (S.base.metric t) x)
        (vec2 (I := I) v v) =
        (pinchLipSec (I := I) S t x) (vec2 (I := I) v v) := by
    have tensor_zero
        (T : Tensor02At (I := I) (M := M) x) :
        T (vec2 (I := I) (0 : TangentSpace I x) 0) = 0 := by
      have h := tensor02_smul2 (I := I) (M := M) T
        (0 : Real) (0 : TangentSpace I x)
      simpa [quad02, vec2_self_eq_const] using h
    by_cases hv : v = 0
    · subst v
      simp [tensor_zero]
    · obtain ⟨nb⟩ :=
        exists_nullOrthonormalBasis3At (I := I) (M := M)
          (S.base.metric t) (x := x) (v := v) hdim hv
      have hpinch := pinchSec_at_trace (I := I) (M := M) S delta t x
      have hshift :=
        shiftRic3At_pinch (I := I) (M := M) nb.basis nb.orthonormal
          hdelta (S.ricci t x)
      rw [← hpinch] at hshift
      have htrace :
          metricTracePair0SAt (I := I) (S.base.metric t)
              (shiftRic3At (I := I) (M := M) delta (S.base.metric t)
                ((pinchSec (I := I) S delta) t x)) =
            S.scalar t x := by
        rw [hshift]
        simp [SolutionOn.scalar_eq_metricTrace, SolutionOn.ricci,
          SolutionFamily.ricci, SolutionOn.ricciAt, SolutionFamily.ricciAt]
      rw [hshift]
      rw [pinchLipSec_apply]
      simp only [Tensor0SSpace.sub_apply,
        Tensor0SSpace.smul_apply, smul_eq_mul]
      rw [metricTensorField_apply]
      have h0 : vec2 (I := I) v v 0 = v := by
        unfold DifferentialGeometry.Integral.Connection.vec2
        simp
      have h1 : vec2 (I := I) v v 1 = v := by
        unfold DifferentialGeometry.Integral.Connection.vec2
        norm_num
      rw [h0, h1]
      have hscalar :
          S.scalar t x =
            metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) := by
        simp [SolutionOn.scalar_eq_metricTrace, SolutionOn.ricci,
          SolutionFamily.ricci, SolutionOn.ricciAt, SolutionFamily.ricciAt]
      rw [hscalar]
      simp [SolutionOn.ricciAt, SolutionFamily.ricciAt]
  rw [hcoeff] at hdiff
  simpa [c] using hdiff

private theorem ricciEnd_repr_basis
    {g : SmoothRiemannianMetric I M} {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Ric : Tensor02At (I := I) (M := M) x)
    (i k : Idx) :
    basis.repr (DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric (basis i)) k =
      ∑ a : Idx, gInv k a * Ric (vec2 (I := I) (basis i) (basis a)) := by
  rw [basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv]
  simp [DifferentialGeometry.Integral.Connection.ricciEnd_inner]

private theorem ricciQuadAt_comp_basis
    {g : SmoothRiemannianMetric I M} {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Ric : Tensor02At (I := I) (M := M) x)
    (i j : Idx) :
    ricciQuadAt (I := I) (M := M) g Ric
        (vec2 (I := I) (basis i) (basis j)) =
      DifferentialGeometry.Integral.Connection.ricciQuadraticAt (I := I) basis gInv Ric i j := by
  rw [ricciQuadAt_apply]
  have hEnd :
      DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric (basis i) =
        ∑ k : Idx,
          basis.repr (DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric (basis i)) k •
            basis k := by
    exact (basis.sum_repr
      (DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric (basis i))).symm
  rw [hEnd]
  rw [show
      vec2 (I := I)
          (∑ k : Idx,
            basis.repr (DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric (basis i)) k •
              basis k)
          (basis j) =
        Fin.cons
          (∑ k : Idx,
            basis.repr (DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric (basis i)) k •
              basis k)
          (fun _ : Fin 1 => basis j) by
    funext q
    fin_cases q <;> rfl]
  rw [← DifferentialGeometry.Integral.Connection.metricTrace_tensor0S_curry_apply_cons
    (I := I) (M := M) (s := 1) Ric
      (∑ k : Idx,
        basis.repr (DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric (basis i)) k •
          basis k)
      (fun _ : Fin 1 => basis j)]
  change
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x Ric)
        (∑ k : Idx,
          basis.repr (DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric (basis i)) k •
            basis k))
        (fun _ : Fin 1 => basis j) =
      DifferentialGeometry.Integral.Connection.ricciQuadraticAt (I := I) basis gInv Ric i j
  rw [map_sum]
  simp [DifferentialGeometry.Integral.Connection.metricTrace_tensor0S_curry_apply_cons, finCons1_eq_vec2,
    ricciEnd_repr_basis (I := I) (M := M) basis gInv hinv Ric,
    DifferentialGeometry.Integral.Connection.ricciQuadraticAt, DifferentialGeometry.Integral.Connection.oneUp02CompAt, smul_eq_mul, mul_comm]

private theorem rm04ContrAt_comp_basis
    {g : SmoothRiemannianMetric I M} {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (Ric : Tensor02At (I := I) (M := M) x)
    (i j : Idx) :
    rm04RicciContrAt (I := I) (M := M) g Rm04 Ric
        (vec2 (I := I) (basis i) (basis j)) =
      DifferentialGeometry.Integral.Connection.rm04RicciContractionAt (I := I) basis Rm04 gInv Ric i j := by
  have hInv : ∀ a b : Idx, gInv a b = gInv b a :=
    Tensor0SBundle.invMetric_symm (I := I) (M := M) g x basis gInv hinv
  rw [rm04RicciContrAt_apply]
  rw [inner0S_two_eq_coord (I := I) g x basis gInv hinv]
  unfold DifferentialGeometry.Integral.Connection.rm04RicciContractionAt DifferentialGeometry.Integral.Connection.raised02CompAt
  change
    (∑ a : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
        (gInv a k * gInv b l *
          Ric (vec2 (I := I) (basis a) (basis b))) *
            rm04Mid02At (I := I) (M := M) Rm04 (basis i) (basis j)
              (vec2 (I := I) (basis k) (basis l))) =
      ∑ k : Idx, ∑ l : Idx,
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          (∑ a : Idx, ∑ b : Idx,
            gInv k a * gInv l b *
              Ric (vec2 (I := I) (basis a) (basis b)))
  have hmid : ∀ k l : Idx,
      rm04Mid02At (I := I) (M := M) Rm04 (basis i) (basis j)
          (vec2 (I := I) (basis k) (basis l)) =
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) := by
    intro k l
    exact rm04Mid02At_apply (I := I) (M := M) Rm04
      (basis i) (basis j) (basis k) (basis l)
  calc
    (∑ a : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
        (gInv a k * gInv b l *
          Ric (vec2 (I := I) (basis a) (basis b))) *
            rm04Mid02At (I := I) (M := M) Rm04 (basis i) (basis j)
              (vec2 (I := I) (basis k) (basis l))) =
      ∑ a : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
        (gInv a k * gInv b l *
          Ric (vec2 (I := I) (basis a) (basis b))) *
            Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hmid k l]
    _ =
      ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
        (gInv a k * gInv b l *
          Ric (vec2 (I := I) (basis a) (basis b))) *
            Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) := by
        calc
          (∑ a : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
              (gInv a k * gInv b l *
                Ric (vec2 (I := I) (basis a) (basis b))) *
                  Rm04 (vec4 (I := I) (basis i) (basis k) (basis j)
                    (basis l))) =
            ∑ a : Idx, ∑ k : Idx, ∑ b : Idx, ∑ l : Idx,
              (gInv a k * gInv b l *
                Ric (vec2 (I := I) (basis a) (basis b))) *
                  Rm04 (vec4 (I := I) (basis i) (basis k) (basis j)
                    (basis l)) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.sum_comm]
          _ = ∑ k : Idx, ∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
              (gInv a k * gInv b l *
                Ric (vec2 (I := I) (basis a) (basis b))) *
                  Rm04 (vec4 (I := I) (basis i) (basis k) (basis j)
                    (basis l)) := by
              rw [Finset.sum_comm]
          _ = ∑ k : Idx, ∑ a : Idx, ∑ l : Idx, ∑ b : Idx,
              (gInv a k * gInv b l *
                Ric (vec2 (I := I) (basis a) (basis b))) *
                  Rm04 (vec4 (I := I) (basis i) (basis k) (basis j)
                    (basis l)) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.sum_comm]
          _ = ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
              (gInv a k * gInv b l *
                Ric (vec2 (I := I) (basis a) (basis b))) *
                  Rm04 (vec4 (I := I) (basis i) (basis k) (basis j)
                    (basis l)) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.sum_comm]
    _ = ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          (gInv k a * gInv l b *
            Ric (vec2 (I := I) (basis a) (basis b))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hInv a k, hInv b l]
        ring
    _ = ∑ k : Idx, ∑ l : Idx,
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          (∑ a : Idx, ∑ b : Idx,
            gInv k a * gInv l b *
              Ric (vec2 (I := I) (basis a) (basis b))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

private theorem sum_coord_react_cancel
    {Idx : Type*} [Fintype Idx]
    (c L R Q : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx,
        c i j * ((-2 : Real) * R i j - 2 * Q i j)) =
      (∑ i : Idx, ∑ j : Idx,
        c i j * (L i j - 2 * R i j - 2 * Q i j)) -
        ∑ i : Idx, ∑ j : Idx, c i j * L i j := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring_nf
  simp_rw [Finset.sum_neg_distrib]
  abel

private theorem stdRmOfRic3_signed_contr
    (Ric : Fin 3 -> Fin 3 -> Real)
    (i j : Fin 3) :
    (∑ k : Fin 3, ∑ l : Fin 3,
        stdRmOfRic3 (fun a b : Fin 3 => -Ric a b) i k j l * Ric k l) =
      -∑ k : Fin 3, ∑ l : Fin 3,
        stdRmOfRic3 Ric i k j l * Ric k l := by
  fin_cases i <;> fin_cases j <;>
    simp [stdRmOfRic3, ricciScal3, DifferentialGeometry.Integral.Connection.delta3,
      Fin.sum_univ_three] <;>
    ring

private theorem actualRm04_comp_signed
    {g : SmoothRiemannianMetric I M} {x : M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) g x basis)
    (htrace :
      DifferentialGeometry.Integral.Connection.RiemannFromRicci3DTraceDataAt
        (I := I) g (-Ric) (-(metricTracePair0SAt (I := I) g Ric))
        Rm04 basis)
    (i k j l : Fin 3) :
    Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) =
      stdRmOfRic3
        (fun a b : Fin 3 =>
          -Ric (vec2 (I := I) (basis a) (basis b))) i k j l := by
  have hformula :=
    DifferentialGeometry.Integral.Connection.rm04Comp_displayedRiemannFromRicci3D_at
      (I := I) htrace i k l j
  have htraceRic :
      metricTracePair0SAt (I := I) g Ric =
        ricciScal3
          (fun a b : Fin 3 =>
            Ric (vec2 (I := I) (basis a) (basis b))) :=
    metricTrace_comp_orthonormal (I := I) (M := M) basis horth Ric
  rw [rm04CompAt_apply] at hformula
  rw [hformula, htraceRic]
  simp only [ricciCompAt_apply, Tensor0SSpace.neg_apply,
    stdRmOfRic3, ricciScal3, Finset.sum_neg_distrib]
  ring

private theorem actualRm04Contr_eq_canonical
    {g : SmoothRiemannianMetric I M} {x : M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) g x basis)
    (htrace :
      DifferentialGeometry.Integral.Connection.RiemannFromRicci3DTraceDataAt
        (I := I) g (-Ric) (-(metricTracePair0SAt (I := I) g Ric))
        Rm04 basis)
    (i j : Fin 3) :
    (∑ k : Fin 3, ∑ l : Fin 3,
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          Ric (vec2 (I := I) (basis k) (basis l))) =
      -∑ k : Fin 3, ∑ l : Fin 3,
        rm04OfRic3At (I := I) (M := M) g Ric
            (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          Ric (vec2 (I := I) (basis k) (basis l)) := by
  let RicC : Fin 3 -> Fin 3 -> Real :=
    fun a b => Ric (vec2 (I := I) (basis a) (basis b))
  calc
    (∑ k : Fin 3, ∑ l : Fin 3,
        Rm04 (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          Ric (vec2 (I := I) (basis k) (basis l))) =
      ∑ k : Fin 3, ∑ l : Fin 3,
        stdRmOfRic3 (fun a b : Fin 3 => -RicC a b) i k j l *
          RicC k l := by
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        exact congrArg (fun z : Real => z * RicC k l)
          (actualRm04_comp_signed (I := I) (M := M) horth htrace i k j l)
    _ =
      -∑ k : Fin 3, ∑ l : Fin 3,
        stdRmOfRic3 RicC i k j l * RicC k l := by
        exact stdRmOfRic3_signed_contr RicC i j
    _ =
      -∑ k : Fin 3, ∑ l : Fin 3,
        rm04OfRic3At (I := I) (M := M) g Ric
            (vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          Ric (vec2 (I := I) (basis k) (basis l)) := by
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        exact congrArg
          (fun z : Real => z * Ric (vec2 (I := I) (basis k) (basis l)))
          (rm04OfRic3At_comp_orthonormal
            (I := I) (M := M) basis horth Ric i k j l).symm

private theorem traceData_metricTrace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis) :
    DifferentialGeometry.Integral.Connection.RiemannFromRicci3DTraceDataAt
      (I := I) (S.base.metric t) (-(S.ricci t x))
      (-(metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x)))
      (S.base.rm04 t x) basis := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞) :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric t)
  have hRm13 :
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm13 t) := by
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
  have hRm04 :
      DifferentialGeometry.Integral.Connection.Rm04RealizesConnection (I := I) (S.base.metric t)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm04 t) := by
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
  have hRic13 :
      S.ricci t x =
        DifferentialGeometry.Integral.Connection.ricciFromRm13At (I := I) (M := M) (S.base.rm13 t x) := by
    simpa [SolutionOn.ricci, SolutionFamily.ricci, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).h_ricci13 x
  have hLowerAt :
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.base.metric t) x
        (S.base.rm13 t x) (S.base.rm04 t x) :=
    DifferentialGeometry.Integral.Connection.rm04LowersRm13At_of_realizes
      (I := I) (g := S.base.metric t)
      (cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
      hRm13 hRm04 x
  have hcurv :
      DifferentialGeometry.Integral.Connection.AlgebraicCurvatureSymmetries3
        (DifferentialGeometry.Integral.Connection.standardRmCompAt
          (I := I) basis (S.base.rm04 t x)) :=
    DifferentialGeometry.Integral.Connection.algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04) basis
  have hRicFirst :
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) (S.ricci t x)
        (S.base.rm04 t x) DifferentialGeometry.Integral.Connection.delta3 basis := by
    have hinv :
        MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
          DifferentialGeometry.Integral.Connection.delta3 :=
      DifferentialGeometry.Integral.Connection.orthonormal_invBasis3 (I := I) (S.base.metric t)
        basis horth
    have hInvSym :
        ∀ i j : Fin 3,
          DifferentialGeometry.Integral.Connection.delta3 i j = DifferentialGeometry.Integral.Connection.delta3 j i := by
      intro i j
      unfold DifferentialGeometry.Integral.Connection.delta3
      by_cases hij : i = j
      · subst j
        simp
      · have hji : j ≠ i := fun h => hij h.symm
        simp [hij, hji]
    exact DifferentialGeometry.Integral.Connection.ricciFirstTraceAt_of_rm13
      (I := I) (S.base.metric t) basis DifferentialGeometry.Integral.Connection.delta3 hinv
      (S.ricci t x) (S.base.rm13 t x) (S.base.rm04 t x)
      hRic13 hLowerAt hInvSym
  have hScalarTrace :
      DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceAt (I := I)
        (metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x))
        (S.ricci t x) DifferentialGeometry.Integral.Connection.delta3 basis := by
    have hinv :
        MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
          DifferentialGeometry.Integral.Connection.delta3 :=
      DifferentialGeometry.Integral.Connection.orthonormal_invBasis3 (I := I) (S.base.metric t)
        basis horth
    unfold DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceAt
    rw [metricTracePair0SAt_eq_sum_basis
      (I := I) (S.base.metric t) basis DifferentialGeometry.Integral.Connection.delta3 hinv
      (S.ricci t x)]
  exact DifferentialGeometry.Integral.Connection.traceDataOfFirst
    (I := I) (M := M) horth hcurv hRicFirst hScalarTrace

@[simp]
theorem pinchSec_quad
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real)
    (x : M) (v : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M)
        (pinchSec (I := I) S delta) t x v v =
      S.ricci t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) -
        delta * S.scalar t x * (S.family.metric t).inner x v v := by
  rw [pinchSec_eq (I := I) S delta]
  simp [pinchTensor]

/-- Time derivative of the quadratic shifted pinching section from pointwise
time derivatives of Ricci, scalar curvature, and the metric.  This is only the
product-rule part of the parabolic producer; the Ricci heat equation itself is
a separate geometric input. -/
theorem pinchSec_quad_deriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) {K : Set Real}
    {delta t ricDt scalarDt metricDt : Real}
    {x : M} {v : TangentSpace I x}
    (hRic :
      HasDerivWithinAt
        (fun s : Real => S.ricci s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v))
        ricDt K t)
    (hScalar :
      HasDerivWithinAt (fun s : Real => S.scalar s x) scalarDt K t)
    (hMetric :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x v v) metricDt K t) :
    HasDerivWithinAt
      (fun s : Real =>
        twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) s x v v)
      (ricDt -
        delta * (scalarDt * (S.family.metric t).inner x v v +
          S.scalar t x * metricDt))
      K t := by
  have hprod :
      HasDerivWithinAt
        (fun s : Real => S.scalar s x * (S.family.metric s).inner x v v)
        (scalarDt * (S.family.metric t).inner x v v +
          S.scalar t x * metricDt) K t :=
    hScalar.mul hMetric
  have hscaled :
      HasDerivWithinAt
        (fun s : Real =>
          delta * (S.scalar s x * (S.family.metric s).inner x v v))
        (delta * (scalarDt * (S.family.metric t).inner x v v +
          S.scalar t x * metricDt)) K t :=
    hprod.const_mul delta
  have hsub :
      HasDerivWithinAt
        (fun s : Real =>
          S.ricci s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) -
            delta * (S.scalar s x * (S.family.metric s).inner x v v))
        (ricDt -
          delta * (scalarDt * (S.family.metric t).inner x v v +
            S.scalar t x * metricDt)) K t :=
    hRic.sub hscaled
  refine hsub.congr_of_eventuallyEq ?_ ?_
  · filter_upwards with s
    simpa [twoTensorSecToFamily, SolutionOn.ricci, SolutionOn.scalar,
      SolutionOn.family, mul_assoc] using
      (pinchSec_quad (I := I) (M := M) S delta s x v)
  · simpa [twoTensorSecToFamily, SolutionOn.ricci, SolutionOn.scalar,
      SolutionOn.family, mul_assoc] using
      (pinchSec_quad (I := I) (M := M) S delta t x v)

/-- Coordinate-frame lift of Lemma 6.3 from fixed Ricci components to the
quadratic evaluation on an arbitrary fixed tangent vector.  The target is still
the coordinate RHS; the remaining direct-parabolic bridge identifies this
finite sum with the invariant rough-trace plus `ricciReaction3At`. -/
theorem ricciQuadDeriv_coord
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (v : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => S.ricci s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v))
      (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord i v *
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord j v *
              ricciEvolutionRHSInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
                (t : Real) x i j)
      D.carrier (t : Real) := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let rhs : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      ricciEvolutionRHSInFrame
        (I := I) S S.base.rm04 (coordInv (I := I) S x)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
        (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
        (t : Real) x i j
  have hsum_eval : ∀ s : Real,
      S.ricci s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) =
        ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            b.coord i v * b.coord j v *
              ricciCompInFrame (I := I) S frame s x i j := by
    intro s
    have h :=
      DifferentialGeometry.Tensor.Coordinates.tensor0S_two_eval_coordFrame_sum (I := I)
        (M := M) (x₀ := x) (Ax := S.ricci s x) v v
    rw [vec2_self_eq_const (I := I) (M := M) v]
    simpa [b, frame, DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2, ricciCompInFrame,
      SolutionOn.ricci, SolutionOn.ricciAt] using h
  have hsum_deriv :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
              b.coord i v * b.coord j v *
                ricciCompInFrame (I := I) S frame s x i j)
        (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            b.coord i v * b.coord j v * rhs i j)
        D.carrier (t : Real) := by
    simpa [rhs, b, frame, mul_assoc] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ :
          Finset (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)))
        (A := fun i s =>
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            b.coord i v * b.coord j v *
              ricciCompInFrame (I := I) S frame s x i j)
        (A' := fun i =>
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            b.coord i v * b.coord j v * rhs i j)
        (s := D.carrier) (x := (t : Real))
        (fun i _hi => by
          simpa [rhs, b, frame, mul_assoc] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ :
                Finset (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)))
              (A := fun j s =>
                b.coord i v * b.coord j v *
                  ricciCompInFrame (I := I) S frame s x i j)
              (A' := fun j => b.coord i v * b.coord j v * rhs i j)
              (s := D.carrier) (x := (t : Real))
              (fun j _hj => by
                simpa [rhs, b, frame, mul_assoc] using
                  ((hS.ricciEvol x t i j).const_mul
                    (b.coord i v * b.coord j v))))))
  refine hsum_deriv.congr_of_eventuallyEq ?_ ?_
  · filter_upwards with s
    exact hsum_eval s
  · exact hsum_eval (t : Real)

/-- Coordinate-RHS time derivative of the shifted pinching quadratic
evaluation.  This combines Lemma 6.3, scalar evolution, and
`partial_t g = -2 Ric`; the remaining direct-parabolic frontier is identifying
this coordinate expression with the invariant WMP heat-plus-reaction operator. -/
theorem pinchQuadDeriv_coord
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {delta : Real}
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (v : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real =>
        twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) s x v v)
      ((∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord i v *
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord j v *
                ricciEvolutionRHSInFrame
                  (I := I) S S.base.rm04 (coordInv (I := I) S x)
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
                  (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
                  (t : Real) x i j) -
        delta *
          ((DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) (t : Real)
                (S.scalar (t : Real)) x +
              2 * normSq0S (I := I) (S.family.metric (t : Real)) x 2
                (S.ricci (t : Real) x)) *
              (S.family.metric (t : Real)).inner x v v +
            S.scalar (t : Real) x *
              ((-2 : Real) * S.ricciAt (t : Real) x
                (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v))))
      D.carrier (t : Real) := by
  have hRic := ricciQuadDeriv_coord (I := I) (M := M) S hS t x v
  have hScalar :
      HasDerivWithinAt (fun s : Real => S.scalar s x)
        (DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) (t : Real)
            (S.scalar (t : Real)) x +
          2 * normSq0S (I := I) (S.family.metric (t : Real)) x 2
            (S.ricci (t : Real) x))
        D.carrier (t : Real) := by
    exact hS.scalarEvolution (flowG (I := I) S)
      (by intro τ; rfl) (by intro τ; rfl) t x
  have hMetric :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x v v)
        ((-2 : Real) * S.ricciAt (t : Real) x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v))
        D.carrier (t : Real) := by
    exact metric_derivWithin_eq_neg_two_ricci (I := I) S hS.isSolution t x v v
  exact pinchSec_quad_deriv (I := I) (M := M) S
    (delta := delta) hRic hScalar hMetric

/-- Ricci-flow-facing zero derivative package for the metric tensor at a fixed
time.  This is the metric-compatibility input needed to reduce the rough
Laplacian of an `R g` factor to the scalar Laplacian of `R` times `g`. -/
noncomputable def pinchMetricDerivs
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (S.base.connection t)
      (metricTensorField (I := I) (S.base.metric t)) := by
  simpa [SolutionFamily.connection] using
    metricDerivsZero (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) (S.base.metric t))
      (S.base.metric t)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) (S.base.metric t))

@[simp]
theorem pinchMetric_nabla
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (x : M) (slots : Fin 3 -> TangentSpace I x) :
    (pinchMetricDerivs (I := I) S t).nablaA x slots = 0 := by
  simp [pinchMetricDerivs]

@[simp]
theorem pinchMetric_nabla2
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (x : M) (slots : Fin 4 -> TangentSpace I x) :
    (pinchMetricDerivs (I := I) S t).nabla2A x slots = 0 := by
  simp [pinchMetricDerivs]

/-- Rough-Laplacian product rule for a scalar times the Ricci-flow metric
tensor, after metric compatibility kills the metric derivative terms. -/
theorem pinchRough_smulMetric
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis gInv)
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nabla2fG :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (tail : Fin 2 -> TangentSpace I x)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin 2 -> TangentSpace I x,
        nabla2fG (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) *
              metricTensorField (I := I) (S.base.metric t) x tail +
            df (fun _ : Fin 1 => X) *
              (pinchMetricDerivs (I := I) S t).nablaA x (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) *
              (pinchMetricDerivs (I := I) S t).nablaA x (Fin.cons X tail) +
            f * (pinchMetricDerivs (I := I) S t).nabla2A x
              (metricTraceInput (I := I) X Y tail)) :
    roughLap0STensor (I := I) (S.base.metric t) nabla2fG tail =
      metricTraceFirstTwo0SAt (I := I) (S.base.metric t) hessF Fin.elim0 *
        metricTensorField (I := I) (S.base.metric t) x tail := by
  exact roughLap_smul_par (I := I) (S.base.metric t) basis gInv hinv
    f df hessF (metricTensorField (I := I) (S.base.metric t) x)
    ((pinchMetricDerivs (I := I) S t).nablaA x)
    ((pinchMetricDerivs (I := I) S t).nabla2A x)
    nabla2fG tail
    (by intro X tail; simp)
    (by intro X Y tail; simp)
    hleib

/-- Concrete rough-Laplacian trace of a scalar Hessian tensor multiplied by
the Ricci-flow metric tensor.  This is the checked metric-factor cancellation
used for the explicit shifted second-derivative model. -/
theorem pinchRough_hessMetric
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis gInv)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (tail : Fin 2 -> TangentSpace I x) :
    roughLap0STensor (I := I) (S.base.metric t)
        ((Bundle.continuousMultilinearMap.product_fun
          (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I)
          (s := 2) (q := 2) (x := x) hessF
          (metricTensorField (I := I) (S.base.metric t) x)) :
            Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
        tail =
      metricTraceFirstTwo0SAt (I := I) (S.base.metric t) hessF Fin.elim0 *
        metricTensorField (I := I) (S.base.metric t) x tail := by
  refine pinchRough_smulMetric (I := I) S t basis gInv hinv
    (0 : Real)
    (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    hessF
    ((Bundle.continuousMultilinearMap.product_fun
      (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I)
      (s := 2) (q := 2) (x := x) hessF
      (metricTensorField (I := I) (S.base.metric t) x)) :
        Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    tail ?_
  intro X Y tail
  rw [Bundle.continuousMultilinearMap.product_fun_apply]
  have hleft :
      metricTraceInput (I := I) X Y tail ∘ Fin.castAdd 2 =
        metricTraceInput (I := I) X Y Fin.elim0 := by
    funext a
    fin_cases a <;> rfl
  have hright :
      metricTraceInput (I := I) X Y tail ∘ Fin.natAdd 2 = tail := by
    funext a
    fin_cases a <;> rfl
  rw [hleft, hright]
  rw [metricTensorField_apply]
  simp

/-- Fixed-time smoothness of scalar curvature for the solution metric. -/
theorem scalarSmoothSec
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x : M => S.scalar t x) := by
  simpa [SolutionOn.scalar, SolutionFamily.scalar] using
    metricScalar_smooth (I := I) (M := M) (S.base.metric t)

/-- Canonical spatial differential of scalar curvature at a fixed time. -/
noncomputable def scalarDuSec
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    OneFormSection (I := I) (M := M) :=
  duSec (I := I) (fun x : M => S.scalar t x)
    (scalarSmoothSec (I := I) S t)

/-- Canonical scalar Hessian section at a fixed time. -/
noncomputable def scalarHessSec
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TwoTensorSection (I := I) (M := M) :=
  hessianSec (I := I) (S.base.connection t) (ricciCovInf (I := I) S t)
    (fun x : M => S.scalar t x) (scalarSmoothSec (I := I) S t)

/-- Explicit section model for `dR tensor g` at a fixed time. -/
noncomputable def scalarMetric1Sec
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
    (scalarDuSec (I := I) S t)
    (metricTensorField (I := I) (S.base.metric t))

/-- Explicit section model for `Hess R tensor g` at a fixed time. -/
noncomputable def scalarMetric2Sec
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
    (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2)
    (scalarHessSec (I := I) S t)
    (metricTensorField (I := I) (S.base.metric t))

@[simp]
theorem scalarMetric1Sec_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    scalarMetric1Sec (I := I) S t x =
      (Bundle.continuousMultilinearMap.product_fun
        (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I)
        (s := 1) (q := 2) (x := x) (scalarDuSec (I := I) S t x)
        (metricTensorField (I := I) (S.base.metric t) x) :
          Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) := by
  rfl

@[simp]
theorem scalarMetric2Sec_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    scalarMetric2Sec (I := I) S t x =
      (Bundle.continuousMultilinearMap.product_fun
        (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I)
        (s := 2) (q := 2) (x := x) (scalarHessSec (I := I) S t x)
        (metricTensorField (I := I) (S.base.metric t) x) :
          Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x) := by
  rfl

/-- The trace of the canonical fixed-time scalar Hessian is the intrinsic
scalar Laplacian used by the Ricci-flow scalar evolution equation. -/
theorem scalarHessTrace_eq_lap
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
        (scalarHessSec (I := I) S t x) Fin.elim0 =
      DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
        (S.scalar t) x := by
  have hlap :
      ScalarLaplacianRealizesTraceAt (I := I)
        (S.base.connection t) (S.base.metric t)
        (fun y : M => S.scalar t y)
        (scalarHessSec (I := I) S t x) := by
    simpa [scalarHessSec] using
      (scalarLap_smooth (I := I) (M := M)
        (cov := S.base.connection t) (ricciCovInf (I := I) S t)
        (g := S.base.metric t) (ricciMetricComp (I := I) S t)
        (f := fun y : M => S.scalar t y) (scalarSmoothSec (I := I) S t)
        (x := x))
  have htrace :=
    ScalarLaplacianRealizesTraceAt.eq_trace (I := I)
      (S.base.connection t) (S.base.metric t)
      (fun y : M => S.scalar t y) (scalarHessSec (I := I) S t x) hlap
  rw [traceFirstTwo_elim0]
  simpa [DifferentialGeometry.Integral.Connection.laplacianAt, flowG, SolutionOn.scalar, SolutionFamily.scalar,
    metricScalarAt, DifferentialGeometry.Integral.Connection.metricScalarAt, SolutionFamily.ricciAt,
    metricRicciAt] using htrace.symm

/-- The rough trace of the canonical Ricci second derivative expands to the
coordinate rough-Ricci RHS on arbitrary quadratic evaluations. -/
theorem ricciRoughTrace_coord
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (x : M) (v : TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
        (ricciNabla2WMP (I := I) S t x)
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) =
      ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord i v *
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord j v *
              coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
                t x i j := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x :=
    roughLap0STensor (I := I) (S.base.metric t)
      (ricciNabla2WMP (I := I) S t x)
  have hnabla : ∀ y a i j,
      ricciNablaWMP (I := I) S t y
          (DifferentialGeometry.Integral.Connection.vec3 (I := I)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a y)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i y)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j y)) =
        nablaRicComp (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t y a i j := by
    intro y a i j
    simp [ricciNablaWMP, ricciDerivsWMP, nablaRicComp,
      CanonicalSpatialDerivs0S.of_smooth_connection]
  have hnab2 :=
    coordNab2_can (I := I) S t x
      (ricciNablaWMP (I := I) S t)
      (ricciNabla2WMP (I := I) S t)
      (by
        simpa [SolutionOn.family, ricciNablaWMP, ricciNabla2WMP] using
          (ricciSpatialWMP (I := I) S).second t)
      hnabla
  have hcomp :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        roughA
            (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
          coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
            t x i j := by
    intro i j
    simpa [roughA, frame, SolutionOn.family] using
      coordRough_can (I := I) S t x
        (ricciNabla2WMP (I := I) S t) hnab2 i j
  have hcomp_if :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        roughA
            (fun q : Fin 2 => if q = 0 then frame i x else frame j x) =
          coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
            t x i j := by
    intro i j
    simpa [DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2] using hcomp i j
  have hsum :=
    DifferentialGeometry.Tensor.Coordinates.tensor0S_two_eval_coordFrame_sum (I := I)
      (M := M) (x₀ := x) (Ax := roughA) v v
  rw [← roughLap0STensor_apply (I := I) (S.base.metric t)
      (ricciNabla2WMP (I := I) S t x) (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)]
  rw [vec2_self_eq_const (I := I) (M := M) v]
  change roughA (fun _ : Fin 2 => v) =
    ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        b.coord i v * b.coord j v *
          coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x i j
  simpa [b, frame, hcomp_if] using hsum

/-- The intrinsic rough Ricci tensor evaluated on a fixed pair is the
coordinate expansion of the canonical coordinate rough-Laplacian components. -/
theorem ricciRoughPair
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (x : M) (v w : TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
        (ricciNabla2WMP (I := I) S t x)
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w) =
      ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord i v *
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord j w *
              coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
                t x i j := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x :=
    roughLap0STensor (I := I) (S.base.metric t)
      (ricciNabla2WMP (I := I) S t x)
  have hnabla : ∀ y a i j,
      ricciNablaWMP (I := I) S t y
          (DifferentialGeometry.Integral.Connection.vec3 (I := I)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a y)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i y)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j y)) =
        nablaRicComp (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t y a i j := by
    intro y a i j
    simp [ricciNablaWMP, ricciDerivsWMP, nablaRicComp,
      CanonicalSpatialDerivs0S.of_smooth_connection]
  have hnab2 :=
    coordNab2_can (I := I) S t x
      (ricciNablaWMP (I := I) S t)
      (ricciNabla2WMP (I := I) S t)
      (by
        simpa [SolutionOn.family, ricciNablaWMP, ricciNabla2WMP] using
          (ricciSpatialWMP (I := I) S).second t)
      hnabla
  have hcomp :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        roughA
            (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
          coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
            t x i j := by
    intro i j
    simpa [roughA, frame, SolutionOn.family] using
      coordRough_can (I := I) S t x
        (ricciNabla2WMP (I := I) S t) hnab2 i j
  have hcomp_if :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        roughA
            (fun q : Fin 2 => if q = 0 then frame i x else frame j x) =
          coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
            t x i j := by
    intro i j
    simpa [DifferentialGeometry.Integral.Connection.vec2] using hcomp i j
  have hsum :=
    DifferentialGeometry.Tensor.Coordinates.tensor0S_two_eval_coordFrame_sum (I := I)
      (M := M) (x₀ := x) (Ax := roughA) v w
  rw [← roughLap0STensor_apply (I := I) (S.base.metric t)
      (ricciNabla2WMP (I := I) S t x)
      (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w)]
  change roughA (fun q : Fin 2 => if q = 0 then v else w) = _
  simpa [b, frame, hcomp_if] using hsum

/-- The metric trace of the pointwise product `Hess(R) ⊗ g` is
`(tr Hess(R)) g` when the metric factor is parallel. -/
theorem scalarMetric_trace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis gInv)
    (v : TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
        (scalarMetric2Sec (I := I) S t x)
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) =
      metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (scalarHessSec (I := I) S t x) Fin.elim0 *
        (S.base.metric t).inner x v v := by
  have h := pinchRough_hessMetric (I := I) S t basis gInv hinv
    (scalarHessSec (I := I) S t x) (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)
  rw [scalarMetric2Sec_apply]
  simpa [roughLap0STensor_apply, metricTensorField_apply,
    DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2] using h

private theorem trace_sub_smul
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    {s : ℕ}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (c : Real) (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g (A - c • B) tail =
      metricTraceFirstTwo0SAt (I := I) g A tail -
        c * metricTraceFirstTwo0SAt (I := I) g B tail := by
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv
      (A - c • B) tail,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv A tail,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv B tail]
  simp only [metricTrace0S2InBasis, Tensor0SSpace.sub_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul]
  simp_rw [mul_sub]
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Pointwise model for the second derivative of the shifted tensor after the
missing canonical product-rule identification has been supplied:
`∇²Ric - δ (∇²R ⊗ g)`. -/
def pinchNab2Model
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  ricciNabla2WMP (I := I) S t x -
    delta • scalarMetric2Sec (I := I) S t x

/-- The explicit model has the expected rough-trace expansion for
`Ric - δ R g`.  This is the algebraic trace part of the direct parabolic
producer for the explicit shifted second-derivative model. -/
theorem pinchNab2Model_trace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis gInv)
    (v : TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
        (pinchNab2Model (I := I) S delta t x) (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) =
      metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
          (ricciNabla2WMP (I := I) S t x) (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) -
        delta *
          (metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
              (scalarHessSec (I := I) S t x) Fin.elim0 *
            (S.base.metric t).inner x v v) := by
  rw [pinchNab2Model]
  rw [trace_sub_smul (I := I) (M := M) (S.base.metric t) basis gInv hinv
    (ricciNabla2WMP (I := I) S t x)
    (scalarMetric2Sec (I := I) S t x)
    delta (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)]
  rw [scalarMetric_trace (I := I) S t basis gInv hinv v]

/-- The canonical scalar Hessian section realizes the total covariant
derivative of the canonical scalar differential. -/
theorem scalarHessSec_realizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (S.base.connection t) (scalarDuSec (I := I) S t)
      (scalarHessSec (I := I) S t) := by
  simpa [scalarDuSec, scalarHessSec] using
    (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (S.base.connection t) (scalarDuSec (I := I) S t)
      (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        1 (S.base.connection t) (ricciCovInf (I := I) S t)
        (scalarDuSec (I := I) S t)))

/-- First scalar-times-parallel-metric product rule for the fixed-time scalar
curvature: `∇(R g) = dR tensor g`. -/
theorem scalarMetric1Sec_realizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.base.connection t)
      (tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        (fun x : M => S.scalar t x) (scalarSmoothSec (I := I) S t)
        (metricTensorField (I := I) (S.base.metric t)))
      (scalarMetric1Sec (I := I) S t) := by
  intro X x slots
  classical
  let V : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose
  have hV : ∀ a : Fin 2, V a x = slots a := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose_spec
  let metricSec : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    metricTensorField (I := I) (S.base.metric t)
  let f : M -> Real := fun y : M => S.scalar t y
  let mfun : M -> Real := fun y : M => metricSec y (fun a : Fin 2 => V a y)
  have hf : MDifferentiableAt I 𝓘(Real, Real) f x :=
    (scalarSmoothSec (I := I) S t).contMDiffAt.mdifferentiableAt (by simp)
  have hm : MDifferentiableAt I 𝓘(Real, Real) mfun x := by
    exact (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      metricSec V x).mdifferentiableAt (by simp)
  have hprod :
      extDerivFun (I := I) (fun y : M => f y * mfun y) x (X x) =
        f x * extDerivFun (I := I) mfun x (X x) +
          extDerivFun (I := I) f x (X x) * mfun x := by
    exact extDerivFun_mul (I := I) (f := f) (h := mfun) (X x) hf hm
  have hmetricReal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.base.connection t) metricSec
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) 3) := by
    simpa [metricSec, SolutionFamily.connection] using
      zero_realizes_metric (I := I) (S.base.connection t) (S.base.metric t)
        (ricciMetricComp (I := I) S t)
  have hmetricEval :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I) hmetricReal X V x
  have hnabla :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (S.base.connection t) X V
      (tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        f (scalarSmoothSec (I := I) S t) metricSec) x
  have hdu :
      scalarDuSec (I := I) S t x (fun _ : Fin 1 => X x) =
        extDerivFun (I := I) f x (X x) := by
    simp [scalarDuSec, f, differential1FormFun_apply_eq_extDerivFun]
  have hslots :
      (fun a : Fin 2 => V a x) = slots := by
    funext a
    exact hV a
  have hmetric_zero :
      extDerivFun (I := I) mfun x (X x) -
          ∑ a : Fin 2,
            metricSec x
              (Function.update (fun b : Fin 2 => V b x) a
                (((S.base.connection t) (fun p : M => V a p) x) (X x))) =
        0 := by
    simpa [metricSec, mfun] using hmetricEval.symm
  calc
    scalarMetric1Sec (I := I) S t x (Fin.cons (X x) slots)
        =
          extDerivFun (I := I) f x (X x) * metricSec x slots := by
          rw [scalarMetric1Sec_apply,
            Bundle.continuousMultilinearMap.product_fun_apply]
          have hleft :
              Fin.cons (X x) slots ∘ Fin.castAdd 2 =
                fun _ : Fin 1 => X x := by
            funext a
            fin_cases a
            rfl
          have hright :
              Fin.cons (X x) slots ∘ Fin.natAdd 1 = slots := by
            funext a
            fin_cases a <;> rfl
          rw [hleft, hright, hdu]
      _ =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 (S.base.connection t) X
            (tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
              f (scalarSmoothSec (I := I) S t) metricSec) x slots := by
          rw [← hslots]
          rw [hnabla]
          simp only [tensor0SField_smulByFun_apply,
            Tensor0SSpace.smul_apply, smul_eq_mul]
          rw [hprod]
          have hsum :
              (∑ a : Fin 2,
                f x *
                  metricSec x
                    (Function.update (fun b : Fin 2 => V b x) a
                      (((S.base.connection t) (fun p : M => V a p) x) (X x)))) =
                f x *
                  ∑ a : Fin 2,
                    metricSec x
                      (Function.update (fun b : Fin 2 => V b x) a
                        (((S.base.connection t) (fun p : M => V a p) x)
                          (X x))) := by
            rw [Finset.mul_sum]
          rw [hsum]
          have hm0 := hmetric_zero
          have hmfunx : mfun x = metricSec x (fun a : Fin 2 => V a x) := rfl
          have hdm :
              (extDerivFun (I := I) mfun x) (X x) =
                ∑ a : Fin 2,
                  metricSec x
                    (Function.update (fun b : Fin 2 => V b x) a
                      (((S.base.connection t) (fun p : M => V a p) x)
                        (X x))) := by
            linarith [hm0]
          rw [hmfunx, hdm]
          ring

/-- Second scalar-times-parallel-metric product rule for the fixed-time scalar
curvature: `∇(dR tensor g) = Hess R tensor g`. -/
theorem scalarMetric2Sec_realizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 (S.base.connection t) (scalarMetric1Sec (I := I) S t)
      (scalarMetric2Sec (I := I) S t) := by
  intro X x slots
  classical
  let V : Fin 3 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose
  have hV : ∀ a : Fin 3, V a x = slots a := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose_spec
  let alphaSec : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 :=
    scalarDuSec (I := I) S t
  let hessSec : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    scalarHessSec (I := I) S t
  let metricSec : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    metricTensorField (I := I) (S.base.metric t)
  let V0 : Fin 1 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun _ => V 0
  let W : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun a => V (Fin.natAdd 1 a)
  let afun : M -> Real := fun y : M => alphaSec y (fun _ : Fin 1 => V 0 y)
  let mfun : M -> Real := fun y : M => metricSec y (fun a : Fin 2 => W a y)
  have ha : MDifferentiableAt I 𝓘(Real, Real) afun x := by
    exact (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      alphaSec V0 x).mdifferentiableAt (by simp)
  have hm : MDifferentiableAt I 𝓘(Real, Real) mfun x := by
    exact (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      metricSec W x).mdifferentiableAt (by simp)
  have hprod :
      extDerivFun (I := I) (fun y : M => afun y * mfun y) x (X x) =
        afun x * extDerivFun (I := I) mfun x (X x) +
          extDerivFun (I := I) afun x (X x) * mfun x := by
    exact extDerivFun_mul (I := I) (f := afun) (h := mfun) (X x) ha hm
  have hmetricReal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.base.connection t) metricSec
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) 3) := by
    simpa [metricSec, SolutionFamily.connection] using
      zero_realizes_metric (I := I) (S.base.connection t) (S.base.metric t)
        (ricciMetricComp (I := I) S t)
  have hmetricEval :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I) hmetricReal X W x
  have halphaReal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 (S.base.connection t) alphaSec hessSec := by
    simpa [alphaSec, hessSec] using scalarHessSec_realizes (I := I) S t
  have halphaEval :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I) halphaReal X V0 x
  have hnabla :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (S.base.connection t) X V
      (scalarMetric1Sec (I := I) S t) x
  have hslots :
      (fun a : Fin 3 => V a x) = slots := by
    funext a
    exact hV a
  have hmetric_zero :
      extDerivFun (I := I) mfun x (X x) -
          ∑ a : Fin 2,
            metricSec x
              (Function.update (fun b : Fin 2 => W b x) a
                (((S.base.connection t) (fun p : M => W a p) x) (X x))) =
        0 := by
    simpa [metricSec, mfun, W] using hmetricEval.symm
  have halpha_eq :
      hessSec x (Fin.cons (X x) (fun _ : Fin 1 => V 0 x)) =
        extDerivFun (I := I) afun x (X x) -
          alphaSec x
            (Function.update (fun _ : Fin 1 => V 0 x) 0
              (((S.base.connection t) (fun p : M => V 0 p) x) (X x))) := by
    simpa [alphaSec, hessSec, afun, V0] using halphaEval
  calc
    scalarMetric2Sec (I := I) S t x (Fin.cons (X x) slots)
        =
          hessSec x (Fin.cons (X x) (fun _ : Fin 1 => slots 0)) *
            metricSec x (fun a : Fin 2 => slots (Fin.natAdd 1 a)) := by
          rw [scalarMetric2Sec_apply,
            Bundle.continuousMultilinearMap.product_fun_apply]
          have hleft :
              Fin.cons (X x) slots ∘ Fin.castAdd 2 =
                Fin.cons (X x) (fun _ : Fin 1 => slots 0) := by
            funext a
            fin_cases a <;> rfl
          have hright :
              Fin.cons (X x) slots ∘ Fin.natAdd 2 =
                fun a : Fin 2 => slots (Fin.natAdd 1 a) := by
            funext a
            fin_cases a <;> rfl
          rw [hleft, hright]
      _ =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            3 (S.base.connection t) X (scalarMetric1Sec (I := I) S t) x slots := by
          rw [← hslots]
          rw [hnabla]
          have hfun_eval :
              (fun p : M =>
                scalarMetric1Sec (I := I) S t p (fun a : Fin 3 => V a p)) =
                fun p : M => afun p * mfun p := by
            funext p
            rw [scalarMetric1Sec_apply,
              Bundle.continuousMultilinearMap.product_fun_apply]
            have hleft :
                (fun a : Fin 3 => V a p) ∘ Fin.castAdd 2 =
                  fun _ : Fin 1 => V 0 p := by
              funext a
              fin_cases a
              rfl
            have hright :
                (fun a : Fin 3 => V a p) ∘ Fin.natAdd 1 =
                  fun a : Fin 2 => W a p := by
              funext a
              fin_cases a <;> rfl
            rw [hleft, hright]
          rw [hfun_eval, hprod]
          have hsum3 :
              (∑ a : Fin 3,
                scalarMetric1Sec (I := I) S t x
                  (Function.update (fun b : Fin 3 => V b x) a
                    (((S.base.connection t) (fun p : M => V a p) x)
                      (X x)))) =
                alphaSec x
                    (Function.update (fun _ : Fin 1 => V 0 x) 0
                      (((S.base.connection t) (fun p : M => V 0 p) x)
                        (X x))) *
                  mfun x +
                afun x *
                  ∑ a : Fin 2,
                    metricSec x
                      (Function.update (fun b : Fin 2 => W b x) a
                        (((S.base.connection t) (fun p : M => W a p) x)
                          (X x))) := by
            rw [Fin.sum_univ_three]
            repeat rw [scalarMetric1Sec_apply]
            repeat rw [Bundle.continuousMultilinearMap.product_fun_apply]
            have h0left :
                (Function.update (fun b : Fin 3 => V b x) 0
                    (((S.base.connection t) (fun p : M => V 0 p) x)
                      (X x)) ∘ Fin.castAdd 2) =
                  Function.update (fun _ : Fin 1 => V 0 x) 0
                    (((S.base.connection t) (fun p : M => V 0 p) x)
                      (X x)) := by
              funext a
              fin_cases a
              rfl
            have h1left :
                (Function.update (fun b : Fin 3 => V b x) 1
                    (((S.base.connection t) (fun p : M => V 1 p) x)
                      (X x)) ∘ Fin.castAdd 2) =
                  fun _ : Fin 1 => V 0 x := by
              funext a
              fin_cases a
              rfl
            have h2left :
                (Function.update (fun b : Fin 3 => V b x) 2
                    (((S.base.connection t) (fun p : M => V 2 p) x)
                      (X x)) ∘ Fin.castAdd 2) =
                  fun _ : Fin 1 => V 0 x := by
              funext a
              fin_cases a
              rfl
            rw [h0left, h1left, h2left]
            repeat rw [metricTensorField_apply]
            simp [afun, mfun, alphaSec, metricSec, W, Function.update]
            ring_nf
          rw [hsum3]
          have hmetricInput :
              (fun a : Fin 2 => W a x) =
                fun a : Fin 2 => V (Fin.natAdd 1 a) x := rfl
          have hafunx :
              afun x = alphaSec x (fun _ : Fin 1 => V 0 x) := rfl
          have hmfunx :
              mfun x = metricSec x (fun a : Fin 2 => W a x) := rfl
          have hdm :
              (extDerivFun (I := I) mfun x) (X x) =
                ∑ a : Fin 2,
                  metricSec x
                    (Function.update (fun b : Fin 2 => W b x) a
                      (((S.base.connection t) (fun p : M => W a p) x)
                        (X x))) := by
            linarith [hmetric_zero]
          have hda :
              (extDerivFun (I := I) afun x) (X x) =
                hessSec x (Fin.cons (X x) (fun _ : Fin 1 => V 0 x)) +
                  alphaSec x
                    (Function.update (fun _ : Fin 1 => V 0 x) 0
                      (((S.base.connection t) (fun p : M => V 0 p) x)
                        (X x))) := by
            linarith [halpha_eq]
          rw [hdm, hda, hafunx, hmfunx]
          ring_nf
          simp [W]

/-- Explicit smooth section model for `nabla Ric - delta (dR tensor g)`. -/
noncomputable def pinchNablaModel
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    TensorNabla1SecFamily (I := I) (M := M) :=
  fun t => ricciNablaWMP (I := I) S t -
    delta • scalarMetric1Sec (I := I) S t

/-- Explicit smooth section model for `nabla^2 Ric - delta (Hess R tensor g)`. -/
noncomputable def pinchNab2ModelSec
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    TensorNabla2SecFamily (I := I) (M := M) :=
  fun t => ricciNabla2WMP (I := I) S t -
    delta • scalarMetric2Sec (I := I) S t

@[simp]
theorem pinchNablaModel_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real) (x : M) :
    pinchNablaModel (I := I) S delta t x =
      ricciNablaWMP (I := I) S t x -
        delta • scalarMetric1Sec (I := I) S t x := by
  simp [pinchNablaModel]

@[simp]
theorem pinchNab2ModelSec_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real) (x : M) :
    pinchNab2ModelSec (I := I) S delta t x =
      pinchNab2Model (I := I) S delta t x := by
  simp [pinchNab2ModelSec, pinchNab2Model]

/-- Zero-drift WMP heat operator for the explicit shifted second derivative,
expanded to the coordinate rough-Ricci trace and scalar Laplacian terms. -/
theorem pinchHeat_coord
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta t : Real)
    (x : M) (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadMetricAt (I := I) (S.base.metric t)
        (fun _y : M => 0)
        (pinchNab2ModelSec (I := I) S delta t x)
        (pinchNablaModel (I := I) S delta t x) v =
      (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord i v *
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord j v *
              coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x)
                t x i j) -
        delta *
          (DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
              (S.scalar t) x *
            (S.base.metric t).inner x v v) := by
  rw [tensorHeatWithDrift2QuadMetricAt_zero_drift]
  rw [pinchNab2ModelSec_apply (I := I) S delta t x]
  rw [pinchNab2Model_trace (I := I) S delta t
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
    (fun a b : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
      coordInv (I := I) S x t x a b)
    (coordInvReal (I := I) S x t) v]
  rw [ricciRoughTrace_coord (I := I) S t x v]
  rw [scalarHessTrace_eq_lap (I := I) S t x]

/-- Coordinate finite-sum RHS for the Ricci quadratic evaluation derivative
from Lemma 6.3. -/
def ricciCoordQuadRHS
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : TangentSpace I x) : Real :=
  ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
    ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord i v *
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord j v *
          ricciEvolutionRHSInFrame
            (I := I) S S.base.rm04 (coordInv (I := I) S x)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x)
            (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
            t x i j

/-- Coordinate finite-sum rough Ricci trace on a quadratic evaluation. -/
def ricciCoordRough
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : TangentSpace I x) : Real :=
  ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
    ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord i v *
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord j v *
          coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x i j

/-- Coordinate reaction part of Lemma 6.3 on a quadratic evaluation, i.e. the
full Ricci RHS minus its rough-Laplacian component. -/
def ricciCoordReact
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : TangentSpace I x) : Real :=
  ricciCoordQuadRHS (I := I) S t x v -
    ricciCoordRough (I := I) S t x v

/-- Coordinate Ricci-evolution reaction evaluated on a fixed pair, obtained by
subtracting the coordinate rough-Laplacian expansion from `ricciPairRHS`. -/
noncomputable def ricciPairReact
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v w : TangentSpace I x) : Real :=
  ricciPairRHS (I := I) S t x v w -
    ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord i v *
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord j w *
            coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x i j

/-- Coordinate RHS for the time derivative of the shifted pinching quadratic
evaluation. -/
def pinchCoordTime
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (delta t : Real) (x : M) (v : TangentSpace I x) : Real :=
  ricciCoordQuadRHS (I := I) S t x v -
    delta *
      ((DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
            (S.scalar t) x +
          2 * normSq0S (I := I) (S.family.metric t) x 2
            (S.ricci t x)) *
          (S.family.metric t).inner x v v +
        S.scalar t x *
          ((-2 : Real) * S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)))

/-- The reaction value needed to identify the coordinate shifted derivative
with the invariant shifted WMP reaction.  Producing this equality for
`shiftNRaw` is the remaining geometric reaction bridge, not a parabolic
regularity assumption. -/
def pinchCoordReact
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (delta t : Real) (x : M) (v : TangentSpace I x) : Real :=
  ricciCoordReact (I := I) S t x v -
    delta *
      (2 * normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) *
          (S.family.metric t).inner x v v +
        S.scalar t x *
          ((-2 : Real) * S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)))

/-- Intrinsic reaction tensor in the Ricci evolution equation. -/
noncomputable def ricciActualReactAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) : Tensor02At (I := I) (M := M) x :=
  (-2 : Real) •
      rm04RicciContrAt (I := I) (M := M) (S.base.metric t)
        (S.base.rm04 t x) (S.ricci t x) -
    2 • ricciQuadAt (I := I) (M := M) (S.base.metric t) (S.ricci t x)

private theorem actualReact_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : Fin 2 → TangentSpace I x) :
    ricciActualReactAt (I := I) S t x v =
      (-2 : Real) *
          rm04RicciContrAt (I := I) (M := M) (S.base.metric t)
            (S.base.rm04 t x) (S.ricci t x) v -
        2 * ricciQuadAt (I := I) (M := M) (S.base.metric t) (S.ricci t x) v := by
  unfold ricciActualReactAt
  simp only [Tensor0SSpace.sub_apply, real_smul0S_apply,
    Tensor0SSpace.nsmul_apply, nsmul_eq_mul, Nat.cast_ofNat]

/-- Components of the intrinsic Ricci reaction in any tangent basis. -/
theorem actualReact_comp
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis gInv)
    (i j : Idx) :
    ricciActualReactAt (I := I) S t x
        (vec2 (I := I) (basis i) (basis j)) =
      (-2 : Real) *
          DifferentialGeometry.Integral.Connection.rm04RicciContractionAt
            (I := I) basis (S.base.rm04 t x) gInv (S.ricci t x) i j -
        2 * DifferentialGeometry.Integral.Connection.ricciQuadraticAt
          (I := I) basis gInv (S.ricci t x) i j := by
  rw [actualReact_apply (I := I) (M := M) S t x
    (vec2 (I := I) (basis i) (basis j))]
  rw [rm04ContrAt_comp_basis (I := I) (M := M) basis gInv hinv,
    ricciQuadAt_comp_basis (I := I) (M := M) basis gInv hinv]

private theorem reaction3_apply
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x)
    (v : Fin 2 → TangentSpace I x) :
    ricciReaction3At (I := I) (M := M) g Ric v =
      2 * rm04RicciContrAt (I := I) (M := M) g
          (rm04OfRic3At (I := I) (M := M) g Ric) Ric v -
        2 * ricciQuadAt (I := I) (M := M) g Ric v := by
  unfold ricciReaction3At
  simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.nsmul_apply,
    nsmul_eq_mul, Nat.cast_ofNat]

private theorem ricciActualReactAt_eq_reaction_basis
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis) :
    ricciActualReactAt (I := I) S t x =
      ricciReaction3At (I := I) (M := M) (S.base.metric t) (S.ricci t x) := by
  have htrace := traceData_metricTrace (I := I) (M := M) S horth
  have hsym : DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) (S.ricci t x) := by
    simpa [SolutionOn.ricci, SolutionFamily.ricci, SolutionOn.ricciAt,
      SolutionFamily.ricciAt] using ricciAt_symm (I := I) S t x
  apply ext0S_basis (I := I) basis
  intro slots
  let i : Fin 3 := slots 0
  let j : Fin 3 := slots 1
  have hslots :
      (fun q : Fin 2 => basis (slots q)) =
        vec2 (I := I) (basis i) (basis j) := by
    funext q
    fin_cases q <;> rfl
  change
    ricciActualReactAt (I := I) S t x (fun q : Fin 2 => basis (slots q)) =
      ricciReaction3At (I := I) (M := M) (S.base.metric t) (S.ricci t x)
        (fun q : Fin 2 => basis (slots q))
  rw [hslots]
  have hactual :=
    rm04Contr_comp_orthonormal (I := I) (M := M) basis horth
      (S.base.rm04 t x) (S.ricci t x) i j
  have hcanon :=
    rm04Contr_comp_orthonormal (I := I) (M := M) basis horth
      (rm04OfRic3At (I := I) (M := M) (S.base.metric t) (S.ricci t x))
      (S.ricci t x) i j
  have hcontr :=
    actualRm04Contr_eq_canonical (I := I) (M := M) horth htrace i j
  calc
    ricciActualReactAt (I := I) S t x
        (vec2 (I := I) (basis i) (basis j)) =
      (-2 : Real) *
          rm04RicciContrAt (I := I) (M := M) (S.base.metric t)
            (S.base.rm04 t x) (S.ricci t x)
            (vec2 (I := I) (basis i) (basis j)) -
        2 * ricciQuadAt (I := I) (M := M) (S.base.metric t)
            (S.ricci t x) (vec2 (I := I) (basis i) (basis j)) := by
        exact actualReact_apply (I := I) (M := M) S t x
          (vec2 (I := I) (basis i) (basis j))
    _ =
      2 *
          rm04RicciContrAt (I := I) (M := M) (S.base.metric t)
            (rm04OfRic3At (I := I) (M := M) (S.base.metric t)
              (S.ricci t x)) (S.ricci t x)
            (vec2 (I := I) (basis i) (basis j)) -
        2 * ricciQuadAt (I := I) (M := M) (S.base.metric t)
            (S.ricci t x) (vec2 (I := I) (basis i) (basis j)) := by
        rw [hactual, hcanon, hcontr]
        ring
    _ =
      ricciReaction3At (I := I) (M := M) (S.base.metric t) (S.ricci t x)
        (vec2 (I := I) (basis i) (basis j)) := by
        exact (reaction3_apply (I := I) (M := M) (S.base.metric t)
          (S.ricci t x) (vec2 (I := I) (basis i) (basis j))).symm

private theorem ricciCoordReact_eq_actual
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : TangentSpace I x) :
    ricciCoordReact (I := I) S t x v =
      ricciActualReactAt (I := I) S t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let gInvAt : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j => coordInv (I := I) S x t x i j
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric t) x b gInvAt := by
    simpa [b, gInvAt] using coordInvReal (I := I) S x t
  have hbasis :
      ∀ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        b i = frame i x := by
    intro i
    simp [b, frame, DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
  have hcomp :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ricciActualReactAt (I := I) S t x
            (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
          (-2 : Real) *
              rmRicciContractionCompInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                frame t x i j -
            2 * ricciQuadraticCompInFrame
                (I := I) S (coordInv (I := I) S x) frame t x i j := by
    intro i j
    have hrm :=
      rm04ContrAt_comp_basis (I := I) (M := M) b gInvAt hinv
        (S.base.rm04 t x) (S.ricci t x) i j
    have hquad :=
      ricciQuadAt_comp_basis (I := I) (M := M) b gInvAt hinv
        (S.ricci t x) i j
    calc
      ricciActualReactAt (I := I) S t x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
        (-2 : Real) *
            rm04RicciContrAt (I := I) (M := M) (S.base.metric t)
              (S.base.rm04 t x) (S.ricci t x)
              (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) -
          2 * ricciQuadAt (I := I) (M := M) (S.base.metric t)
              (S.ricci t x)
              (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) := by
          exact actualReact_apply (I := I) (M := M) S t x
            (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x))
      _ =
        (-2 : Real) *
            DifferentialGeometry.Integral.Connection.rm04RicciContractionAt (I := I) b (S.base.rm04 t x)
              gInvAt (S.ricci t x) i j -
          2 * DifferentialGeometry.Integral.Connection.ricciQuadraticAt (I := I) b gInvAt
              (S.ricci t x) i j := by
          rw [← hbasis i, ← hbasis j]
          rw [hrm, hquad]
      _ =
          (-2 : Real) *
              rmRicciContractionCompInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                frame t x i j -
            2 * ricciQuadraticCompInFrame
                (I := I) S (coordInv (I := I) S x) frame t x i j := by
          simp [rmRicciContractionCompInFrame, raisedRicciCompInFrame,
            ricciQuadraticCompInFrame, ricciOneUpCompInFrame, ricciCompInFrame,
            DifferentialGeometry.Integral.Connection.rm04Comp, DifferentialGeometry.Integral.Connection.rm04Comp,
            DifferentialGeometry.Integral.Connection.rm04RicciContractionAt, DifferentialGeometry.Integral.Connection.raised02CompAt,
            DifferentialGeometry.Integral.Connection.ricciQuadraticAt, DifferentialGeometry.Integral.Connection.oneUp02CompAt,
            SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionOn.ricci,
            SolutionFamily.ricci, b, frame, gInvAt, hbasis]
  have hcomp_if :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ricciActualReactAt (I := I) S t x
            (fun q : Fin 2 =>
              if q = 0 then frame i x else frame j x) =
          (-2 : Real) *
              rmRicciContractionCompInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                frame t x i j -
            2 * ricciQuadraticCompInFrame
                (I := I) S (coordInv (I := I) S x) frame t x i j := by
    intro i j
    simpa [DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2] using hcomp i j
  have hsum :=
    DifferentialGeometry.Tensor.Coordinates.tensor0S_two_eval_coordFrame_sum (I := I)
      (M := M) (x₀ := x) (Ax := ricciActualReactAt (I := I) S t x) v v
  symm
  change ricciActualReactAt (I := I) S t x
      (fun q : Fin 2 => if q = 0 then v else v) =
    ricciCoordReact (I := I) S t x v
  rw [hsum]
  simp only [ricciCoordReact, ricciCoordQuadRHS, ricciCoordRough,
    ricciEvolutionRHSInFrame, hcomp_if, frame]
  let c : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord i v *
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord j v
  let L : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j => coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x i j
  let R : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      rmRicciContractionCompInFrame
        (I := I) S S.base.rm04 (coordInv (I := I) S x)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t x i j
  let Q : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      ricciQuadraticCompInFrame
        (I := I) S (coordInv (I := I) S x)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t x i j
  change
    (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        c i j * ((-2 : Real) * R i j - 2 * Q i j)) =
      (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          c i j * (L i j - 2 * R i j - 2 * Q i j)) -
        ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            c i j * L i j
  exact sum_coord_react_cancel c L R Q

/-- The coordinate reaction on a fixed pair is the evaluation of the intrinsic
Ricci reaction tensor on that pair. -/
theorem pairReact_eq_actual
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v w : TangentSpace I x) :
    ricciPairReact (I := I) S t x v w =
      ricciActualReactAt (I := I) S t x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w) := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
  let gInvAt : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j => coordInv (I := I) S x t x i j
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric t) x b gInvAt := by
    simpa [b, gInvAt] using coordInvReal (I := I) S x t
  have hbasis :
      ∀ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        b i = frame i x := by
    intro i
    simp [b, frame, DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
  have hcomp :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ricciActualReactAt (I := I) S t x
            (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
          (-2 : Real) *
              rmRicciContractionCompInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                frame t x i j -
            2 * ricciQuadraticCompInFrame
                (I := I) S (coordInv (I := I) S x) frame t x i j := by
    intro i j
    calc
      ricciActualReactAt (I := I) S t x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
        ricciActualReactAt (I := I) S t x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) (b i) (b j)) := by
            rw [hbasis i, hbasis j]
      _ =
        (-2 : Real) *
            DifferentialGeometry.Integral.Connection.rm04RicciContractionAt
              (I := I) b (S.base.rm04 t x) gInvAt (S.ricci t x) i j -
          2 * DifferentialGeometry.Integral.Connection.ricciQuadraticAt
            (I := I) b gInvAt (S.ricci t x) i j :=
        actualReact_comp (I := I) (M := M) S t x b gInvAt hinv i j
      _ =
          (-2 : Real) *
              rmRicciContractionCompInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                frame t x i j -
            2 * ricciQuadraticCompInFrame
                (I := I) S (coordInv (I := I) S x) frame t x i j := by
          simp [rmRicciContractionCompInFrame, raisedRicciCompInFrame,
            ricciQuadraticCompInFrame, ricciOneUpCompInFrame, ricciCompInFrame,
            DifferentialGeometry.Integral.Connection.rm04Comp,
            DifferentialGeometry.Integral.Connection.rm04RicciContractionAt,
            DifferentialGeometry.Integral.Connection.raised02CompAt,
            DifferentialGeometry.Integral.Connection.ricciQuadraticAt,
            DifferentialGeometry.Integral.Connection.oneUp02CompAt,
            SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionOn.ricci,
            SolutionFamily.ricci, b, frame, gInvAt, hbasis]
  have hcomp_if :
      ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ricciActualReactAt (I := I) S t x
            (fun q : Fin 2 => if q = 0 then frame i x else frame j x) =
          (-2 : Real) *
              rmRicciContractionCompInFrame
                (I := I) S S.base.rm04 (coordInv (I := I) S x)
                frame t x i j -
            2 * ricciQuadraticCompInFrame
                (I := I) S (coordInv (I := I) S x) frame t x i j := by
    intro i j
    simpa [DifferentialGeometry.Integral.Connection.vec2] using hcomp i j
  have hsum :=
    DifferentialGeometry.Tensor.Coordinates.tensor0S_two_eval_coordFrame_sum (I := I)
      (M := M) (x₀ := x) (Ax := ricciActualReactAt (I := I) S t x) v w
  symm
  change ricciActualReactAt (I := I) S t x
      (fun q : Fin 2 => if q = 0 then v else w) =
    ricciPairReact (I := I) S t x v w
  rw [hsum]
  simp only [ricciPairReact, ricciPairRHS, ricciEvolutionRHSInFrame,
    hcomp_if, frame]
  let c : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord i v *
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x).coord j w
  let L : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j => coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x i j
  let R : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      rmRicciContractionCompInFrame
        (I := I) S S.base.rm04 (coordInv (I := I) S x)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t x i j
  let Q : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      ricciQuadraticCompInFrame
        (I := I) S (coordInv (I := I) S x)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t x i j
  change
    (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        c i j * ((-2 : Real) * R i j - 2 * Q i j)) =
      (∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          c i j * (L i j - 2 * R i j - 2 * Q i j)) -
        ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            c i j * L i j
  exact sum_coord_react_cancel c L R Q

/-- Intrinsic Ricci evolution on any fixed pair of tangent vectors, produced
directly from `IsSolutionOn`. -/
theorem ricciPairDeriv
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => S.ricci s x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w))
      (metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : Real))
          (ricciNabla2WMP (I := I) S (t : Real) x)
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w) +
        ricciActualReactAt (I := I) S (t : Real) x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w))
      D.carrier (t : Real) := by
  have hcoord := ricciPairCoord (I := I) S hS x t v w
  have hrough := ricciRoughPair (I := I) S (t : Real) x v w
  have hreact := pairReact_eq_actual (I := I) S (t : Real) x v w
  have hvalue :
      ricciPairRHS (I := I) S (t : Real) x v w =
        metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : Real))
            (ricciNabla2WMP (I := I) S (t : Real) x)
            (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w) +
          ricciActualReactAt (I := I) S (t : Real) x
            (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w) := by
    unfold ricciPairReact at hreact
    rw [hrough]
    linarith
  exact hcoord.congr_deriv hvalue

theorem shiftNRaw_pinchCoordReact
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {delta t : Real} {x : M}
    (hdelta13 : delta < (1 : Real) / 3)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (v : TangentSpace I x) :
    (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M)
        (pinchSec (I := I) S delta) t)) x v v =
      pinchCoordReact (I := I) S delta t x v := by
  classical
  by_cases hv : v = 0
  · subst v
    have hvec0 :
        vec2 (I := I) (0 : TangentSpace I x) 0 =
          (0 : Fin 2 → TangentSpace I x) := by
      funext q
      fin_cases q <;> rfl
    have hric :
        ricciCoordReact (I := I) S t x 0 = 0 := by
      rw [ricciCoordReact_eq_actual (I := I) S t x 0]
      rw [actualReact_apply (I := I) (M := M) S t x
        (vec2 (I := I) (0 : TangentSpace I x) 0)]
      rw [hvec0, tensor02_zero_apply, tensor02_zero_apply]
      ring
    rw [shiftNRaw_pinch (I := I) (M := M) S delta t (S.base.metric t) x 0 0]
    have hN :
        shiftNAt (I := I) (M := M) delta t (S.base.metric t) x
            ((pinchSec (I := I) S delta) t x)
            (vec2 (I := I) (0 : TangentSpace I x) 0) = 0 := by
      rw [hvec0]
      exact tensor02_zero_apply _
    rw [hN]
    unfold pinchCoordReact
    rw [hric]
    have hRicZero :
        S.ricciAt t x (vec2 (I := I) (0 : TangentSpace I x) 0) = 0 := by
      rw [hvec0]
      exact tensor02_zero_apply _
    rw [hRicZero]
    simp
  · obtain ⟨nb⟩ :=
      exists_nullOrthonormalBasis3At (I := I) (M := M)
        (S.base.metric t) hdim hv
    have hpinch := pinchSec_at_trace (I := I) (M := M) S delta t x
    have hshift :=
      shiftNAt_pinch (I := I) (M := M) nb.basis nb.orthonormal
        hdelta13 (S.ricci t x) (t := t)
    have hactual :=
      ricciActualReactAt_eq_reaction_basis (I := I) (M := M) S t x
        nb.basis nb.orthonormal
    have hcoord := ricciCoordReact_eq_actual (I := I) S t x v
    rw [shiftNRaw_pinch (I := I) (M := M) S delta t (S.base.metric t) x v v]
    rw [hpinch, hshift, ← hactual]
    simp only [Tensor0SSpace.sub_apply, real_smul0S_apply]
    rw [← hcoord]
    simp [pinchCoordReact, metricTensorField_apply,
      SolutionOn.scalar_eq_metricTrace, vec2, DifferentialGeometry.Integral.Connection.vec2]
    ring

/-- Direct parabolic producer once the remaining canonical reaction-coordinate
bridge is supplied.  The proof itself assembles the shifted time derivative,
the explicit zero-drift heat operator, and the scalar-metric cancellation. -/
theorem pinchParabolic_of_react
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hreact :
      ∀ t, t ∈ Set.Ioc 0 T -> ∀ x, ∀ v : TangentSpace I x,
        (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
          (twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S delta) t)) x v v =
          pinchCoordReact (I := I) S delta t x v) :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      (fun _t x => (0 : TangentSpace I x))
      (shiftNRaw (I := I) (M := M) delta)
      (fun t x => pinchNab2ModelSec (I := I) S delta t x)
      (fun t x => pinchNablaModel (I := I) S delta t x) T := by
  refine ⟨?_⟩
  refine ⟨fun t x v => pinchCoordTime (I := I) S delta t x v, ?_, ?_⟩
  · intro t ht x v
    have htreg : t ∈ D.regular := hTreg ht
    have hderiv :=
      pinchQuadDeriv_coord (I := I) (M := M) S hS
        (delta := delta) ⟨t, htreg⟩ x v
    simpa [pinchCoordTime, ricciCoordQuadRHS] using hderiv.mono hTsub
  · intro t ht x v
    have hheat := pinchHeat_coord (I := I) S delta t x v
    have hN := hreact t ht x v
    apply le_of_eq
    calc
      tensorHeatWithDrift2QuadMetricAt (I := I) (S.base.metric t)
            (fun x => (0 : TangentSpace I x))
            (pinchNab2ModelSec (I := I) S delta t x)
            (pinchNablaModel (I := I) S delta t x) v +
          (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
            (twoTensorSecToFamily (I := I) (M := M)
              (pinchSec (I := I) S delta) t)) x v v
          =
        (ricciCoordRough (I := I) S t x v -
            delta *
              (DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
                  (S.scalar t) x *
                (S.base.metric t).inner x v v)) +
          pinchCoordReact (I := I) S delta t x v := by
            rw [hheat, hN]
            rfl
      _ = pinchCoordTime (I := I) S delta t x v := by
            simp [pinchCoordTime, pinchCoordReact, ricciCoordReact,
              ricciCoordQuadRHS, ricciCoordRough, SolutionOn.family]
            ring

/-- Direct parabolic producer for the canonical shifted pinching section.

This discharges the former reaction-coordinate bridge internally, using the
canonical tensor-backed `shiftNRaw` reaction and the metric-derived 3D
Riemann-from-Ricci convention bridge above. -/
theorem pinchParabolic
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      (fun _t x => (0 : TangentSpace I x))
      (shiftNRaw (I := I) (M := M) delta)
      (fun t x => pinchNab2ModelSec (I := I) S delta t x)
      (fun t x => pinchNablaModel (I := I) S delta t x) T :=
  pinchParabolic_of_react (I := I) (M := M) S hS hTsub hTreg
    (fun t _ht x v =>
      shiftNRaw_pinchCoordReact (I := I) (M := M) S
        hdelta13 (hdim x) v)

/-- The explicit shifted derivative sections realize the first and second
spatial covariant derivatives of `Ric - delta R g`. -/
theorem pinchSpatialModel
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    TensorSpatialDerivs (I := I) (M := M)
      (fun t : Real => S.base.connection t) (pinchSec (I := I) S delta)
      (pinchNablaModel (I := I) S delta)
      (pinchNab2ModelSec (I := I) S delta) := by
  constructor
  · intro t
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3
    have hRic := (ricciSpatialWMP (I := I) S).first t
    have hRg := scalarMetric1Sec_realizes (I := I) S t
    have hscaled :
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 (S.base.connection t)
          (delta • tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
            (fun x : M => S.scalar t x)
            (by
              simpa [SolutionOn.scalar, SolutionFamily.scalar] using
                metricScalar_smooth (I := I) (M := M) (S.base.metric t))
            (metricTensorField (I := I) (S.base.metric t)))
          (delta • scalarMetric1Sec (I := I) S t) :=
      TotalNabla0SRealizes.smul (I := I) (M := M) delta hRg
    have hscaled' :
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 (S.base.connection t)
          (tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
            (fun x : M => delta * S.scalar t x)
            (by
              have hR :
                  ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
                    (fun x : M => S.scalar t x) := by
                simpa [SolutionOn.scalar, SolutionFamily.scalar] using
                  metricScalar_smooth (I := I) (M := M) (S.base.metric t)
              simpa only [Pi.mul_apply] using (contMDiff_const.mul hR))
            (metricTensorField (I := I) (S.base.metric t)))
          (delta • scalarMetric1Sec (I := I) S t) := by
      convert hscaled using 1
      apply ContMDiffSection.ext
      intro x
      simp [tensor0SField_smulByFun_apply, smul_smul]
    have hneg := TotalNabla0SRealizes.smul (I := I) (M := M)
      (-1 : Real) hscaled'
    have hadd := TotalNabla0SRealizes.add (I := I) (M := M) hRic hneg
    simpa [pinchSec, pinchNablaModel, sub_eq_add_neg, smul_smul,
      tensor0SField_smulByFun_apply, mul_assoc, mul_left_comm, mul_comm]
      using hadd
  · intro t
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4
    have hRic := (ricciSpatialWMP (I := I) S).second t
    have hRg := scalarMetric2Sec_realizes (I := I) S t
    have hscaled := TotalNabla0SRealizes.smul (I := I) (M := M)
      delta hRg
    have hneg := TotalNabla0SRealizes.smul (I := I) (M := M)
      (-1 : Real) hscaled
    have hadd := TotalNabla0SRealizes.add (I := I) (M := M) hRic hneg
    simpa [pinchNablaModel, pinchNab2ModelSec, sub_eq_add_neg, smul_smul]
      using hadd

/-- The shifted pinching section is jointly continuous over the solution
interval when the Ricci-flow solution package supplies scalar, Ricci, and
metric total-space continuity. -/
theorem pinchSecFamilyContinuousOnSet
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (delta : Real) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => (pinchSec (I := I) S delta) t x) := by
  have hcoef :
      Continuous (fun q : {t : Real // t ∈ D.carrier} × M =>
        delta * S.scalar q.1.1 q.2) := by
    have hscalarSub :
        Continuous (fun q : {t : Real // t ∈ D.carrier} × M =>
          S.scalar q.1.1 q.2) := by
      exact ScalarSTContOn.continuous_subtype (I := I) (M := M) (S := S)
        ({ scalar_continuousOn := hS.scalarCont } :
          ScalarSTContOn (I := I) (M := M) S)
    exact continuous_const.mul hscalarSub
  have hmetric :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x => metricTensorField (I := I) (S.base.metric t) x) := by
    simpa [SolutionOn.family] using hS.smoothMetric.metricTensor_cont
  have hscaled :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          (delta * S.scalar t x) •
            metricTensorField (I := I) (S.base.metric t) x) :=
    Tensor0SFamilyContinuousOnSet.smul (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (f := fun t x => delta * S.scalar t x)
      (A := fun t x => metricTensorField (I := I) (S.base.metric t) x)
      hcoef hmetric
  have hneg :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          (-1 : Real) •
            ((delta * S.scalar t x) •
              metricTensorField (I := I) (S.base.metric t) x)) :=
    Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (A := fun t x =>
        (delta * S.scalar t x) •
          metricTensorField (I := I) (S.base.metric t) x)
      (-1 : Real) hscaled
  have hsum :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          S.ricci t x +
            (-1 : Real) •
              ((delta * S.scalar t x) •
                metricTensorField (I := I) (S.base.metric t) x)) :=
    Tensor0SFamilyContinuousOnSet.add (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (A := fun t x => S.ricci t x)
      (B := fun t x =>
        (-1 : Real) •
          ((delta * S.scalar t x) •
            metricTensorField (I := I) (S.base.metric t) x))
      hS.ricciCont hneg
  simpa [pinchSec, tensor0SField_smulByFun_apply] using hsum

/-- Joint continuity of the reaction Lipschitz coefficient tensor
`3 Ric - R g`. -/
theorem pinchLipFamilyContinuousOnSet
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => (pinchLipSec (I := I) S) t x) := by
  have hscalarSub :
      Continuous (fun q : {t : Real // t ∈ D.carrier} × M =>
        S.scalar q.1.1 q.2) := by
    exact ScalarSTContOn.continuous_subtype (I := I) (M := M) (S := S)
      ({ scalar_continuousOn := hS.scalarCont } :
        ScalarSTContOn (I := I) (M := M) S)
  have hmetric :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x => metricTensorField (I := I) (S.base.metric t) x) := by
    simpa [SolutionOn.family] using hS.smoothMetric.metricTensor_cont
  have hscaled :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          S.scalar t x • metricTensorField (I := I) (S.base.metric t) x) :=
    Tensor0SFamilyContinuousOnSet.smul (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (f := fun t x => S.scalar t x)
      (A := fun t x => metricTensorField (I := I) (S.base.metric t) x)
      hscalarSub hmetric
  have hneg :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          (-1 : Real) •
            (S.scalar t x • metricTensorField (I := I) (S.base.metric t) x)) :=
    Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (A := fun t x =>
        S.scalar t x • metricTensorField (I := I) (S.base.metric t) x)
      (-1 : Real) hscaled
  have hric3 :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x => (3 : Real) • S.ricci t x) :=
    Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (A := fun t x => S.ricci t x) (3 : Real) hS.ricciCont
  have hsum :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          (3 : Real) • S.ricci t x +
            (-1 : Real) •
              (S.scalar t x •
                metricTensorField (I := I) (S.base.metric t) x)) :=
    Tensor0SFamilyContinuousOnSet.add (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (A := fun t x => (3 : Real) • S.ricci t x)
      (B := fun t x =>
        (-1 : Real) •
          (S.scalar t x • metricTensorField (I := I) (S.base.metric t) x))
      hric3 hneg
  simpa [pinchLipSec, tensor0SField_smulByFun_apply] using hsum

/-- Tangent-bundle continuity for the reaction Lipschitz coefficient tensor. -/
theorem pinchLip_tangentBundle_cont
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval} {K : Set Real}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hK : K ⊆ D.carrier) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
        ((pinchLipSec (I := I) S) q.1.1 q.2.proj)) := by
  exact Tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M)
    (Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
      (pinchLipFamilyContinuousOnSet (I := I) S hS) hK)

/-- Compact unit-tangent bound for the reaction Lipschitz coefficient
`3 Ric - R g` on a closed time slab. -/
theorem pinchLip_bound_Icc
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 t1 : Real}
    (hK : Set.Icc t0 t1 ⊆ D.carrier) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t, t ∈ Set.Icc t0 t1 ->
        ∀ x (v : TangentSpace I x),
          |(pinchLipSec (I := I) S t x) (vec2 (I := I) v v)| ≤
            C * (S.base.metric t).inner x v v := by
  let G : Real -> SmoothRiemannianMetric I M := fun t => S.base.metric t
  let A : (t : Real) -> (x : M) -> Tensor0SSpace 2 I x :=
    fun t x => (pinchLipSec (I := I) S) t x
  have hGcont :
      Continuous
        (metricTimeBundleQuad (I := I) (M := M) G (Set.Icc t0 t1)) := by
    simpa [G, SolutionOn.family] using
      metricTimeBundleQuad_cont_of_metricFamilySmoothOn (I := I) (M := M)
        S.family hS.smoothMetric hK
  have hcompact :
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 t1))) :=
    metricUnitTimeSlab_icc_compact_of_bundle (I := I) (M := M)
      G t0 t1 (S.base.metric t0) hGcont
  have hcont :
      Continuous
        (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 t1) =>
          |quad02 (I := I) (M := M)
            (A (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
              (MetricUnitTangentTimeSlab.base (I := I) (M := M) p))
            (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)|) := by
    exact timeSlabAbsQuadCont (I := I) (M := M) G A
      (Set.Icc t0 t1)
      (pinchLip_tangentBundle_cont (I := I) S hS hK)
  obtain ⟨C, hC, hbound⟩ :=
    compactUnitTimeSlab_absBound (I := I) (M := M) G A
      (Set.Icc t0 t1) hcompact hcont
  refine ⟨C, hC, ?_⟩
  intro t ht x v
  simpa [G, A, quad02, vec2_self_eq_const] using hbound t ht x v

/-- Tangent-bundle form of shifted pinching section continuity on any time set
inside the solution interval. -/
theorem pinchSec_tangentBundle_cont
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval} {K : Set Real}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (delta : Real)
    (hK : K ⊆ D.carrier) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
        ((pinchSec (I := I) S delta) q.1.1 q.2.proj)) := by
  exact Tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M)
    (Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
      (pinchSecFamilyContinuousOnSet (I := I) S hS delta) hK)

/-- Quadratic-evaluation continuity for the shifted pinching section on any
time set inside the solution interval. -/
theorem pinchSec_tensorQuadCont
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval} {K : Set Real}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (delta : Real)
    (hK : K ⊆ D.carrier) :
    Continuous
      (tensorSecBundleQuad (I := I) (M := M)
        (pinchSec (I := I) S delta) K) :=
  tensorQuadCont (I := I) (M := M) (pinchSec (I := I) S delta) K
    (pinchSec_tangentBundle_cont (I := I) S hS delta hK)

/-- Fixed-vector evaluation continuity for a time-dependent `(0,2)` tensor
family from joint tensor-bundle continuity. -/
theorem tensorEval_contOn
    {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K A)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun t : Real => A t x (vec2 (I := I) v w)) K := by
  rw [continuousOn_iff_continuous_restrict]
  let P := {t : Real // t ∈ K}
  let b : P -> M := fun _ => x
  let T : (p : P) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (b p) :=
    fun p => A p.1 x
  let V : Fin 2 -> ∀ p : P, TangentSpace I (b p) :=
    fun i _ => vec2 (I := I) v w i
  have hb : Continuous b := by
    exact continuous_const
  have hT : Continuous (fun p : P =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) (b p) (T p)) := by
    have hincl : Continuous (fun p : P => (p, x)) :=
      continuous_id.prodMk continuous_const
    simpa [P, b, T] using hA.comp hincl
  have hV : ∀ i : Fin 2, Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
        (b p) (V i p)) := by
    intro i
    change Continuous (fun _ : P =>
      (TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
        x (vec2 (I := I) v w i) : TangentBundle I M))
    exact continuous_const
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := P) (n := 2)
    b hb T hT V hV
  simpa [P, b, T, V, Tensor0SSpace.toModel,
    tensor0SSpace_continuousLinearEquiv_apply] using hEval

/-- Fixed-vector continuity for the shifted pinching section on `[0,T]`. -/
theorem pinchEval_contOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn
      (fun t : Real =>
        twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta) t x v w)
      (Set.Icc 0 T) := by
  have hcont :=
    tensorEval_contOn (I := I) (M := M)
      (Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
        (pinchSecFamilyContinuousOnSet (I := I) S hS delta) hTsub)
      x v w
  simpa [twoTensorSecToFamily] using hcont

/-- The metric-gain field for the shifted pinching barrier is produced from
the Ricci-flow metric equation `∂ₜ g = -2 Ric`. -/
theorem pinchMetricGain
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    ∀ t0 : Real,
      t0 ∈ Set.Icc 0 T ->
      t0 < T ->
      ∃ delta0 : Real,
        0 < delta0 ∧ t0 + delta0 ≤ T ∧
          ∀ delta : Real,
            0 < delta ->
            delta ≤ delta0 ->
            ∀ epsilon : Real,
              SmallBarrierEps epsilon ->
              ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    HasDerivWithinAt
                      (fun s : Real => (S.base.metric s).inner x v v)
                      (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    (epsilon / 2) * (S.base.metric t).inner x v v ≤
                      epsilon * ((S.base.metric t).inner x v v +
                        (delta + t - t0) * metricDeriv t x v)) := by
  let A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    fun t x => (-2 : Real) • S.ricci t x
  have hgain := metricGainControl_of_metricVariationOn (I := I) (M := M)
    (D := D) (G := S.family)
    (Ric := RicciAtFamily.toTensorField (I := I) S.ricciAt)
    (A := A) (T := T)
    (by
      simpa [MetricVariationEquationOn] using hS.equation)
    (by
      intro t0 ht0 ht0T
      let deltaRaw : Real := (T - t0) / 2
      have hdeltaRaw : 0 < deltaRaw := by
        dsimp [deltaRaw]
        linarith
      have hdeltaRawT : t0 + deltaRaw ≤ T := by
        dsimp [deltaRaw]
        linarith
      have hcarrier : Set.Icc t0 (t0 + deltaRaw) ⊆ D.carrier := by
        intro s hs
        exact hTsub ⟨le_trans ht0.1 hs.1, le_trans hs.2 hdeltaRawT⟩
      have hregular : ∀ t, t ∈ Set.Ioc t0 (t0 + deltaRaw) -> t ∈ D.regular := by
        intro t ht
        exact hTreg ⟨lt_of_le_of_lt ht0.1 ht.1, le_trans ht.2 hdeltaRawT⟩
      have hAeval :
          ∀ t, t ∈ Set.Ioc t0 (t0 + deltaRaw) ->
            ∀ x, ∀ v : TangentSpace I x,
              quad02 (I := I) (M := M) (A t x) v =
                (-2 : Real) *
                  RicciAtFamily.toTensorField (I := I) S.ricciAt t x v v := by
        intro t ht x v
        simp [A, quad02, vec2_self_eq_const, RicciAtFamily.toTensorField,
          SolutionOn.ricci, SolutionFamily.ricci, SolutionOn.ricciAt,
          SolutionFamily.ricciAt]
      have hGcont :
          Continuous
            (metricTimeBundleQuad (I := I) (M := M)
              (fun t => S.family.metric t)
              (Set.Icc t0 (t0 + deltaRaw))) := by
        exact metricTimeBundleQuad_cont_of_metricFamilySmoothOn
          (I := I) (M := M) S.family hS.smoothMetric hcarrier
      have hAcont :
          Continuous (fun q :
              {t : Real // t ∈ Set.Icc t0 (t0 + deltaRaw)} ×
                  TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (A q.1.1 q.2.proj)) := by
        have hAset :
            Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
              (Set.Icc t0 (t0 + deltaRaw)) A :=
          Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
            (s := 2) (K := Set.Icc t0 (t0 + deltaRaw))
            (A := fun t x => S.ricci t x) (-2 : Real)
            (Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
              hS.ricciCont hcarrier)
        exact Tensor0SFamilyContinuousOnSet.tangentBundle
          (I := I) (M := M) hAset
      exact ⟨deltaRaw, hdeltaRaw, hdeltaRawT, hcarrier, hregular,
        hAeval, hGcont, hAcont⟩)
  simpa [SolutionOn.family] using hgain

/-- Small-barrier reaction Lipschitz estimate for the canonical shifted
reaction on the shifted pinching section. -/
theorem pinchSmallLip
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T delta : Real}
    (hdelta : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier) :
    ∀ delta0 t0 : Real, 0 < delta0 ->
      Set.Icc t0 (t0 + delta0) ⊆ Set.Icc 0 T ->
      ∃ K : Real, 0 ≤ K ∧
        ∀ epsilon d : Real,
          SmallBarrierEps epsilon -> 0 < d -> d ≤ delta0 ->
          ∀ t, t ∈ Set.Icc t0 (t0 + d) -> ∀ x, ∀ v : TangentSpace I x,
            |(shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
                (twoTensorSecToFamily (I := I) (M := M)
                  (pinchSec (I := I) S delta) t)) x v v -
              (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
                (tensorBarrierFamily (I := I) (M := M)
                  (fun s : Real => S.base.metric s)
                  (twoTensorSecToFamily (I := I) (M := M)
                    (pinchSec (I := I) S delta))
                  epsilon d t0 t)) x v v| ≤
                K *
                  |epsilon * (d + t - t0) * (S.base.metric t).inner x v v| := by
  intro delta0 t0 hdelta0 hsub0
  have hKcarrier : Set.Icc t0 (t0 + delta0) ⊆ D.carrier := by
    intro s hs
    exact hTsub (hsub0 hs)
  obtain ⟨C, hC, hbound⟩ :=
    pinchLip_bound_Icc (I := I) S hS
      (t0 := t0) (t1 := t0 + delta0) hKcarrier
  let alpha : Real := (2 * delta - 1) / (1 - 3 * delta)
  refine ⟨|alpha| * C, mul_nonneg (abs_nonneg alpha) hC, ?_⟩
  intro epsilon d hepsilon hd hdle t ht x v
  let c : Real := epsilon * (d + t - t0)
  let base : Real :=
    (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M)
        (pinchSec (I := I) S delta) t)) x v v
  let barr : Real :=
    (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
      (tensorBarrierFamily (I := I) (M := M)
        (fun s : Real => S.base.metric s)
        (twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S delta))
        epsilon d t0 t)) x v v
  let lip : Real := (pinchLipSec (I := I) S t x) (vec2 (I := I) v v)
  let gvv : Real := (S.base.metric t).inner x v v
  have ht_delta0 : t ∈ Set.Icc t0 (t0 + delta0) :=
    ⟨ht.1, by linarith [ht.2, hdle]⟩
  have hdiff :
      barr - base =
        (c / (1 - 3 * delta)) * (2 * delta - 1) * lip := by
    simpa [base, barr, lip, c] using
      shiftNRaw_barrier_diff (I := I) (M := M) S
        (delta := delta) (epsilon := epsilon) (d := d)
        (t0 := t0) (t := t) (x := x) hdelta (hdim x) v
  have hbase :
      base - barr =
        -((c / (1 - 3 * delta)) * (2 * delta - 1) * lip) := by
    rw [← hdiff]
    ring
  have hden : 1 - 3 * delta ≠ 0 := by nlinarith
  have hcoef :
      (c / (1 - 3 * delta)) * (2 * delta - 1) = alpha * c := by
    dsimp [alpha]
    field_simp [hden]
  have hmetric_nonneg : 0 ≤ gvv := by
    by_cases hv : v = 0
    · subst v
      simp [gvv]
    · exact le_of_lt ((S.base.metric t).pos x v hv)
  have hLip := hbound t ht_delta0 x v
  have hleft :
      |base - barr| = |alpha| * |c| * |lip| := by
    rw [hbase, hcoef]
    simp [abs_mul, mul_assoc, mul_comm]
  calc
    |base - barr| = |alpha| * |c| * |lip| := hleft
    _ ≤ |alpha| * |c| * (C * gvv) := by
      exact mul_le_mul_of_nonneg_left hLip
        (mul_nonneg (abs_nonneg alpha) (abs_nonneg c))
    _ = (|alpha| * C) * |c * gvv| := by
      simp [c, gvv, abs_mul, abs_of_nonneg hmetric_nonneg]
      ring
    _ = (|alpha| * C) *
          |epsilon * (d + t - t0) * (S.base.metric t).inner x v v| := by
      simp [c, gvv, mul_assoc]

/-- Full barrier regularity for the canonical shifted reaction on the shifted
pinching section. -/
theorem pinchBarrierReg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T delta : Real}
    (hdelta : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      (fun _t x => (0 : TangentSpace I x))
      (shiftNRaw (I := I) (M := M) delta) T where
  tensor_eval_continuous := by
    intro x v w
    exact pinchEval_contOn (I := I) (M := M) S hS hTsub x v w
  metric_eval_continuous := by
    intro x v w
    simpa [SolutionOn.family] using
      ((hS.smoothMetric.coeff_cont x v w).mono hTsub)
  barrier_eval_continuous := by
    intro epsilon d t0 hsub x v w
    have hScont :
        ContinuousOn
          (fun t : Real =>
            twoTensorSecToFamily (I := I) (M := M)
              (pinchSec (I := I) S delta) t x v w)
          (Set.Icc t0 (t0 + d)) :=
      (pinchEval_contOn (I := I) (M := M) S hS hTsub x v w).mono hsub
    have hGcont :
        ContinuousOn
          (fun t : Real => (S.base.metric t).inner x v w)
          (Set.Icc t0 (t0 + d)) := by
      exact
        (by
          simpa [SolutionOn.family] using
            ((hS.smoothMetric.coeff_cont x v w).mono hTsub) :
          ContinuousOn
            (fun t : Real => (S.base.metric t).inner x v w)
            (Set.Icc 0 T)).mono hsub
    have hcoef :
        ContinuousOn (fun t : Real => epsilon * (d + t - t0))
          (Set.Icc t0 (t0 + d)) := by
      have hlin : Continuous (fun t : Real => d + t - t0) :=
        (continuous_const.add continuous_id).sub continuous_const
      exact (continuous_const.mul hlin).continuousOn
    simpa [tensorBarrierFamily] using hScont.add (hcoef.mul hGcont)
  metricGainControl :=
    pinchMetricGain (I := I) (M := M) S hS hTsub hTreg
  smallBarrierLip :=
    pinchSmallLip (I := I) (M := M) S hS hdelta hdim hTsub

/-- Core theorem-7.5 section regularity for the shifted pinching section from
smooth Ricci-flow data, once the analytic barrier regularity field is supplied.

This proves the compactness, metric/tensor total-space continuity, fixed-vector
barrier continuity, and symmetry parts of the core package.  It intentionally
does not prove `TensorBarrierRegularityOn.smallBarrierLip`; that remains the
separate analytic reaction-control frontier. -/
theorem pinchSecCore
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X N T) :
    TensorWMPSectionCore (I := I) (M := M)
      (fun t : Real => S.base.metric t) (pinchSec (I := I) S delta) X N T := by
  exact TensorWMPSectionCore.ofSmoothMetric (I := I) (M := M)
    (G := S.family) (S := pinchSec (I := I) S delta)
    (X := X) (N := N) (T := T)
    hTsub hS.smoothMetric
    (pinchSec_symm (I := I) S delta (Set.Icc 0 T))
    (by simpa [SolutionOn.family] using hbar)
    (fun d t0 _hd hsub =>
      pinchSec_tangentBundle_cont (I := I) S hS delta
        (fun t ht => hTsub (hsub ht)))
    (fun epsilon d t0 _hepsilon _hd hsub x v =>
      hbar.barrier_eval_continuous epsilon d t0 hsub x v v)

/-- Section 9 Ricci-flow data needed to feed theorem 7.5 for the canonical
Ricci tensor.  The connection, metric compatibility, and spatial derivative
realization are produced canonically from the solution candidate; the remaining
fields are the genuine WMP application inputs. -/
structure RicciWMPData
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (T : Real) : Type _ where
  X : TimeDependentVectorField (I := I) (M := M)
  N : TwoTensorReaction (I := I) (M := M)
  reg :
    TensorWMPSectionCore (I := I) (M := M)
      (fun t : Real => S.base.metric t) S.ricci X N T
  parabolic :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) X N
      (fun t x => ricciNabla2WMP (I := I) S t x)
      (fun t x => ricciNablaWMP (I := I) S t x) T
  null :
    TensorNullEigenvectorCondition (I := I) (M := M)
      (fun t : Real => S.base.metric t) N (Set.Icc 0 T)
  initial :
    TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) 0

namespace RicciWMPData

/-- Build the theorem-7.5 input package for the canonical Ricci section of a
Ricci-flow solution candidate. -/
def toInput
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} {T : Real}
    (data : RicciWMPData (I := I) (M := M) S T) (hT : 0 <= T) :
    TensorWMPInput (I := I) (M := M)
      (fun t : Real => S.base.metric t) S.ricci data.X data.N
      (fun t : Real => S.base.connection t)
      (ricciNablaWMP (I := I) S) (ricciNabla2WMP (I := I) S) T where
  hT := hT
  reg := data.reg
  parabolic := data.parabolic
  null := data.null
  initial := data.initial
  hcov1 := fun t => ricciCov1 (I := I) S t
  hcovInf := fun t => ricciCovInf (I := I) S t
  hmc := fun t => ricciMetricComp (I := I) S t
  spatial := ricciSpatialWMP (I := I) S

end RicciWMPData

/-- Tensor-WMP data for the shifted tensor `Ric - delta R g`. -/
structure PinchWMPData
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) (T delta : Real) : Type _ where
  S : TwoTensorSecFamily (I := I) (M := M)
  X : TimeDependentVectorField (I := I) (M := M)
  N : TwoTensorReaction (I := I) (M := M)
  cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)
  nablaS : TensorNabla1SecFamily (I := I) (M := M)
  nabla2S : TensorNabla2SecFamily (I := I) (M := M)
  section_eq :
    twoTensorSecToFamily (I := I) (M := M) S =
      pinchTensor (I := I) (M := M) G Ric scalar delta
  reg :
    TensorWMPSectionCore (I := I) (M := M) G S X N T
  parabolic :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x) T
  null :
    TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T)
  hcov1 :
    forall t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (1 : WithTop ℕ∞)
  hcovInf :
    forall t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (∞ : WithTop ℕ∞)
  hmc :
    forall t : Real,
      DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) (cov t) (G t)
  spatial : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S

namespace PinchWMPData

/-- Build the theorem-7.5 input package from the Section 9 pinching data. -/
def toInput
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T delta : Real}
    (data : PinchWMPData (I := I) (M := M) G Ric scalar T delta)
    (hT : 0 <= T)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) G Ric scalar delta) 0) :
    TensorWMPInput (I := I) (M := M)
      G data.S data.X data.N data.cov data.nablaS data.nabla2S T where
  hT := hT
  reg := data.reg
  parabolic := data.parabolic
  null := data.null
  initial := by
    simpa [data.section_eq] using hinit
  hcov1 := data.hcov1
  hcovInf := data.hcovInf
  hmc := data.hmc
  spatial := data.spatial

end PinchWMPData

/-- Ricci-flow pinching WMP data for the explicit shifted derivative models.
The section and core regularity are produced from the solution candidate; the
remaining fields are the genuine application frontiers: spatial realization of
the explicit models, the direct parabolic inequality, barrier regularity, and
the reaction-wide null-eigenvector condition. -/
structure PinchFlowWMPData
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (T delta : Real) : Type _ where
  X : TimeDependentVectorField (I := I) (M := M)
  N : TwoTensorReaction (I := I) (M := M)
  reg :
    TensorWMPSectionCore (I := I) (M := M)
      (fun t : Real => S.base.metric t) (pinchSec (I := I) S delta) X N T
  spatial :
    TensorSpatialDerivs (I := I) (M := M)
      (fun t : Real => S.base.connection t) (pinchSec (I := I) S delta)
      (pinchNablaModel (I := I) S delta) (pinchNab2ModelSec (I := I) S delta)
  parabolic :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X N
      (fun t x => pinchNab2ModelSec (I := I) S delta t x)
      (fun t x => pinchNablaModel (I := I) S delta t x) T
  null :
    TensorNullEigenvectorCondition (I := I) (M := M)
      (fun t : Real => S.base.metric t) N (Set.Icc 0 T)

namespace PinchFlowWMPData

/-- Build the canonical shifted-pinching WMP data package once the genuine
application inputs have been supplied.  The core section regularity is produced
from smooth solution data by `pinchSecCore`; callers no longer need to assemble
the compactness and continuity fields manually. -/
def ofBarrier
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X N T)
    (hparabolic :
      TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
        X N
        (fun t x => pinchNab2ModelSec (I := I) S delta t x)
        (fun t x => pinchNablaModel (I := I) S delta t x) T)
    (hnull :
      TensorNullEigenvectorCondition (I := I) (M := M)
        (fun t : Real => S.base.metric t) N (Set.Icc 0 T)) :
    PinchFlowWMPData (I := I) (M := M) S T delta where
  X := X
  N := N
  reg := pinchSecCore (I := I) S hS hTsub hbar
  spatial := pinchSpatialModel (I := I) S delta
  parabolic := hparabolic
  null := hnull

/-- Build the canonical shifted-pinching WMP data using the natural symmetric
null-condition interface.  The legacy raw null condition is recovered by
symmetrizing the reaction input, so future reaction producers can work only on
symmetric first-null tensors. -/
def ofSymmNull
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X N T)
    (hparabolic :
      TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
        X N
        (fun t x => pinchNab2ModelSec (I := I) S delta t x)
        (fun t x => pinchNablaModel (I := I) S delta t x) T)
    (hdep :
      TensorReactionSymmInputOn (I := I) (M := M)
        (fun t : Real => S.base.metric t) N (Set.Icc 0 T))
    (hnull :
      TensorNullEigenvectorConditionSymm (I := I) (M := M)
        (fun t : Real => S.base.metric t) N (Set.Icc 0 T)) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofBarrier (I := I) (M := M) hS hTsub X N hbar hparabolic
    (null_of_symm (I := I) (M := M) hdep hnull)

/-- Build the canonical shifted-pinching WMP data with the tensor-backed
shifted reaction `shiftNRaw`.  This closes the reaction-wide null condition
from the dimension-three shifted reaction algebra; the parabolic inequality and
small-barrier reaction regularity remain explicit application inputs. -/
def ofShiftN
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T delta : Real}
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (X : TimeDependentVectorField (I := I) (M := M))
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X (shiftNRaw (I := I) (M := M) delta) T)
    (hparabolic :
      TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
        X (shiftNRaw (I := I) (M := M) delta)
        (fun t x => pinchNab2ModelSec (I := I) S delta t x)
        (fun t x => pinchNablaModel (I := I) S delta t x) T) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofSymmNull (I := I) (M := M) hS hTsub X
    (shiftNRaw (I := I) (M := M) delta) hbar hparabolic
    (shiftNRaw_symmInputOn (I := I) (M := M)
      (fun t : Real => S.base.metric t) (Set.Icc 0 T) delta)
    (shiftNRaw_null_symm (I := I) (M := M)
      (G := fun t : Real => S.base.metric t) (U := Set.Icc 0 T)
      hdelta0 hdelta13 hdim)

/-- Build the canonical shifted-pinching WMP data with the tensor-backed
shifted reaction `shiftNRaw` for every `delta < 1/3`.

The `delta = 0` case is the Ricci-preservation reaction. -/
def ofShiftNLt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T delta : Real}
    (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (X : TimeDependentVectorField (I := I) (M := M))
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X (shiftNRaw (I := I) (M := M) delta) T)
    (hparabolic :
      TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
        X (shiftNRaw (I := I) (M := M) delta)
        (fun t x => pinchNab2ModelSec (I := I) S delta t x)
        (fun t x => pinchNablaModel (I := I) S delta t x) T) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofSymmNull (I := I) (M := M) hS hTsub X
    (shiftNRaw (I := I) (M := M) delta) hbar hparabolic
    (shiftNRaw_symmInputOn (I := I) (M := M)
      (fun t : Real => S.base.metric t) (Set.Icc 0 T) delta)
    (shiftNRaw_null_symm_of_lt (I := I) (M := M)
      (G := fun t : Real => S.base.metric t) (U := Set.Icc 0 T)
      hdelta13 hdim)

/-- Canonical shifted-pinching WMP data with the direct parabolic input
assembled from smooth Ricci-flow evolution, once the remaining
reaction-coordinate bridge and barrier regularity are supplied. -/
def ofShiftNReact
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      (fun _t x => (0 : TangentSpace I x))
      (shiftNRaw (I := I) (M := M) delta) T)
    (hreact :
      ∀ t, t ∈ Set.Ioc 0 T -> ∀ x, ∀ v : TangentSpace I x,
        (shiftNRaw (I := I) (M := M) delta t (S.base.metric t)
          (twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S delta) t)) x v v =
          pinchCoordReact (I := I) S delta t x v) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofShiftN (I := I) (M := M) hS.isSolution hdelta0 hdelta13 hdim hTsub
    (fun _t x => (0 : TangentSpace I x)) hbar
    (pinchParabolic_of_react (I := I) (M := M) S hS
      hTsub hTreg hreact)

/-- Canonical shifted-pinching WMP data with the direct parabolic input
produced from smooth Ricci-flow evolution and the canonical shifted reaction.

The only remaining non-produced WMP input here is
`TensorBarrierRegularityOn`, specifically its small-barrier reaction control. -/
def ofShiftNDirect
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      (fun _t x => (0 : TangentSpace I x))
      (shiftNRaw (I := I) (M := M) delta) T) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofShiftN (I := I) (M := M) hS.isSolution hdelta0 hdelta13 hdim hTsub
    (fun _t x => (0 : TangentSpace I x)) hbar
    (pinchParabolic (I := I) (M := M) S hS hdelta13 hdim hTsub hTreg)

/-- Canonical shifted-pinching WMP data with null condition, direct parabolic
input, and barrier regularity all produced from smooth Ricci-flow data. -/
def ofShiftNClosed
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofShiftNDirect (I := I) (M := M) hS hdelta0 hdelta13 hdim hTsub hTreg
    (pinchBarrierReg (I := I) (M := M) S hS.isSolution
      hdelta13 hdim hTsub hTreg)

/-- Fill the old Section 9 pinching package from the canonical solution-level
pinching section and derivative producers. -/
def toPinchWMPData
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} {T delta : Real}
    (data : PinchFlowWMPData (I := I) (M := M) S T delta) :
    PinchWMPData (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci)
      S.scalar T delta where
  S := pinchSec (I := I) S delta
  X := data.X
  N := data.N
  cov := fun t : Real => S.base.connection t
  nablaS := pinchNablaModel (I := I) S delta
  nabla2S := pinchNab2ModelSec (I := I) S delta
  section_eq := pinchSec_eq (I := I) S delta
  reg := data.reg
  parabolic := data.parabolic
  null := data.null
  hcov1 := fun t => ricciCov1 (I := I) S t
  hcovInf := fun t => ricciCovInf (I := I) S t
  hmc := fun t => ricciMetricComp (I := I) S t
  spatial := data.spatial

end PinchFlowWMPData

/-- Lemma 9.1 as a raw compatibility consumer of Hamilton's tensor WMP. -/
theorem ricci_nonneg_wmp_raw
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Ric : TensorNabla2Family (I := I) (M := M)}
    {nablaRic : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (hT : 0 <= T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G Ric X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G Ric X N nabla2Ric nablaRic T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) Ric 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) Ric (Set.Icc 0 T) := by
  exact hamilton_tensor_wmp (I := I) (M := M) (G := G) (S := Ric)
    (X := X) (N := N) (nabla2S := nabla2Ric) (nablaS := nablaRic)
    hT hreg hparabolic hnull hinit

/-- Lemma 9.1 as a section-backed consumer of theorem 7.5. -/
theorem ricci_nonneg_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {RicSec : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {nablaRic : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2Ric : TensorNabla2SecFamily (I := I) (M := M)}
    {T : Real}
    (hRic :
      twoTensorSecToFamily (I := I) (M := M) RicSec = Ric)
    (data : TensorWMPInput (I := I) (M := M)
      G RicSec X N cov nablaRic nabla2Ric T) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) Ric (Set.Icc 0 T) := by
  have hsec :
      TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) RicSec) (Set.Icc 0 T) :=
    tensor_wmp (I := I) (M := M) data
  simpa [hRic] using hsec

/-- Lemma 9.1 for the canonical Ricci section of a Ricci-flow solution
candidate, with theorem-7.5 connection and spatial-derivative inputs produced
from the solution candidate. -/
theorem ricci_nonneg_sol
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    {T : Real}
    (hT : 0 <= T)
    (data : RicciWMPData (I := I) (M := M) S T) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) (Set.Icc 0 T) := by
  exact tensor_wmp (I := I) (M := M) (RicciWMPData.toInput
    (I := I) (M := M) data hT)

/-- Lemma 9.2 as a raw compatibility consumer of Hamilton's tensor WMP. -/
theorem ricci_pinch_wmp_raw
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {delta : Real}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (hT : 0 <= T)
    (_hdelta0 : 0 <= delta) (_hdelta13 : delta <= (1 : Real) / 3)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G
      (pinchTensor (I := I) (M := M) G Ric scalar delta) X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G
      (pinchTensor (I := I) (M := M) G Ric scalar delta) X N
      nabla2S nablaS T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) G Ric scalar delta) 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (pinchTensor (I := I) (M := M) G Ric scalar delta) (Set.Icc 0 T) := by
  exact hamilton_tensor_wmp (I := I) (M := M) (G := G)
    (S := pinchTensor (I := I) (M := M) G Ric scalar delta)
    (X := X) (N := N) (nabla2S := nabla2S) (nablaS := nablaS)
    hT hreg hparabolic hnull hinit

/-- Lemma 9.2 as a section-backed consumer of theorem 7.5. -/
theorem ricci_pinch_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {delta : Real}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {T : Real}
    (_hdelta0 : 0 <= delta) (_hdelta13 : delta <= (1 : Real) / 3)
    (hS :
      twoTensorSecToFamily (I := I) (M := M) S =
        pinchTensor (I := I) (M := M) G Ric scalar delta)
    (data : TensorWMPInput (I := I) (M := M)
      G S X N cov nablaS nabla2S T) :
    PinchPres (I := I) (M := M) G Ric scalar T delta := by
  have hsec :
      TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T) :=
    tensor_wmp (I := I) (M := M) data
  simpa [PinchPres, hS] using hsec

namespace PinchWMPData

/-- Preserve a supplied Section 9 pinching package through theorem 7.5. -/
theorem preserve
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T delta : Real}
    (data : PinchWMPData (I := I) (M := M) G Ric scalar T delta)
    (hT : 0 <= T)
    (hdelta0 : 0 <= delta) (hdelta13 : delta <= (1 : Real) / 3)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) G Ric scalar delta) 0) :
    PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact ricci_pinch_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (delta := delta) (S := data.S) (X := data.X)
    (N := data.N) (cov := data.cov) (nablaS := data.nablaS)
    (nabla2S := data.nabla2S) (T := T)
    hdelta0 hdelta13 data.section_eq (data.toInput hT hinit)

end PinchWMPData

namespace PinchFlowWMPData

/-- Preserve the canonical shifted pinching section through theorem 7.5 once
the remaining WMP application data have been proved for that canonical
section. -/
theorem preserve
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    {T delta : Real}
    (data : PinchFlowWMPData (I := I) (M := M) S T delta)
    (hT : 0 <= T)
    (hdelta0 : 0 <= delta) (hdelta13 : delta <= (1 : Real) / 3)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar delta) 0) :
    PinchPres (I := I) (M := M) (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T delta := by
  exact (data.toPinchWMPData (I := I) (M := M)).preserve
    (I := I) (M := M) hT hdelta0 hdelta13 hinit

end PinchFlowWMPData

/-- Preserve the canonical shifted pinching section for a fixed strict
`delta`, with all Section 9 WMP data produced from smooth Ricci-flow data. -/
theorem pinch_sol_closed
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hT : 0 ≤ T) (hdelta0 : 0 < delta)
    (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar delta) 0) :
    PinchPres (I := I) (M := M) (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T delta := by
  exact (PinchFlowWMPData.ofShiftNClosed (I := I) (M := M) hS
    hdelta0 hdelta13 hdim hTsub hTreg).preserve
      (I := I) (M := M) hT (le_of_lt hdelta0)
      (le_of_lt hdelta13) hinit

/-- Preserve the canonical shifted pinching section for `0 <= delta < 1/3`.

The endpoint `delta = 0` is the Ricci-preservation case. -/
theorem pinch_sol_closed_nonneg
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T delta : Real}
    (hT : 0 ≤ T) (hdelta0 : 0 ≤ delta)
    (hdelta13 : delta < (1 : Real) / 3)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar delta) 0) :
    PinchPres (I := I) (M := M) (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T delta := by
  exact (PinchFlowWMPData.ofShiftNLt (I := I) (M := M) hS.isSolution
    hdelta13 hdim hTsub (fun _t x => (0 : TangentSpace I x))
    (pinchBarrierReg (I := I) (M := M) S hS.isSolution
      hdelta13 hdim hTsub hTreg)
    (pinchParabolic (I := I) (M := M) S hS hdelta13 hdim hTsub hTreg)).preserve
      (I := I) (M := M) hT hdelta0 (le_of_lt hdelta13) hinit

/-- Lemma 9.1 for a smooth solution, produced as the `delta = 0` endpoint of
the closed shifted-pinching WMP package. -/
theorem ricci_nonneg_sol_closed
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hT : 0 ≤ T)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) (Set.Icc 0 T) := by
  have hinit0 : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar 0) 0 := by
    intro x v
    simpa [pinchTensor] using hinit x v
  have hpinch : PinchPres (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T 0 :=
    pinch_sol_closed_nonneg (I := I) (M := M) hS hT (le_refl 0)
      (by norm_num) hdim hTsub hTreg hinit0
  intro t ht x v
  exact (by
    simpa [PinchPres, pinchTensor] using hpinch t ht x v)

/-- Corollary 9.3 setup from an already selected initial pinching constant. -/
theorem pinch_init_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hinit : PinchInit (I := I) (M := M) G Ric scalar)
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  rcases hinit with ⟨delta, hdelta0, hdelta13, hpinch0⟩
  let data := hdata delta hdelta0 hdelta13
  refine ⟨delta, hdelta0, hdelta13, ?_⟩
  exact data.preserve (I := I) (M := M) hT
    (le_of_lt hdelta0) hdelta13 hpinch0

/-- Corollary 9.3 setup from a strict selected initial pinching constant. -/
theorem pinch_init_wmp_lt
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hinit : PinchInitLt (I := I) (M := M) G Ric scalar)
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  rcases hinit with ⟨delta, hdelta0, hdelta13, hpinch0⟩
  let data := hdata delta hdelta0 hdelta13
  refine ⟨delta, hdelta0, hdelta13, ?_⟩
  exact data.preserve (I := I) (M := M) hT
    (le_of_lt hdelta0) (le_of_lt hdelta13) hpinch0

/-- Corollary 9.3 for a smooth Ricci-flow solution, using the closed
canonical Section 9 WMP data producer. -/
theorem pinch_init_sol_lt
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hT : 0 ≤ T)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hinit : PinchInitLt (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) (fun t : Real => S.base.metric t)
          (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T delta := by
  refine pinch_init_wmp_lt (I := I) (M := M)
    (G := fun t : Real => S.base.metric t)
    (Ric := twoTensorSecToFamily (I := I) (M := M) S.ricci)
    (scalar := S.scalar) (T := T) hT hinit ?_
  intro delta hdelta0 hdelta13
  exact (PinchFlowWMPData.ofShiftNClosed (I := I) (M := M) hS
    hdelta0 hdelta13 hdim hTsub hTreg).toPinchWMPData (I := I) (M := M)

/-- Corollary 9.3 conditional form: strict initial Ricci positivity supplies a
pinching constant, and Lemma 9.2 preserves it. -/
theorem strict_pinch_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hpos : RicciPosInit (I := I) (M := M) Ric)
    (hselect : BoundsOfPosRic (I := I) (M := M) G Ric scalar)
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInit_of_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) hpos hselect)
    hdata

/-- Strict-`delta` Corollary 9.3 conditional form: strict initial Ricci
positivity supplies `0 < delta < 1/3`, and Lemma 9.2 preserves it. -/
theorem strict_pinch_wmp_lt
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hpos : RicciPosInit (I := I) (M := M) Ric)
    (hselect : BoundsOfPosRic (I := I) (M := M) G Ric scalar)
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp_lt (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInitLt_of_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) hpos hselect)
    hdata

/-- Corollary 9.3 conditional form using a realized continuous base
Ricci-minimum function instead of a raw compactness selector. -/
theorem strict_pinch_min
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInit_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin hscalar)
    hdata

/-- Strict-`delta` version using a realized continuous base Ricci-minimum
function instead of a raw compactness selector. -/
theorem strict_pinch_min_lt
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp_lt (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInitLt_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin hscalar)
    hdata

/-- Corollary 9.3 conditional form with the initial Ricci tensor realized from
the initial metric. -/
theorem strict_pinch_metric
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInit_metric (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) D hmin hscalar)
    hdata

/-- Strict-`delta` version with the initial Ricci tensor realized from the
initial metric. -/
theorem strict_pinch_metric_lt
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp_lt (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInitLt_metric (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) D hmin hscalar)
    hdata

/-- Corollary 9.3 conditional form using the unit tangent compact-minimum
selector. -/
theorem strict_pinch_pos
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInit_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) D hpos hscalar)
    hdata

/-- Strict-`delta` version using the unit tangent compact-minimum selector. -/
theorem strict_pinch_pos_lt
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp_lt (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInitLt_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) D hpos hscalar)
    hdata

/-- Smooth-solution Corollary 9.3: positive initial Ricci for the canonical
solution Ricci tensor gives a preserved strict shifted pinching constant. -/
theorem strict_pinch_sol_lt
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    [Nonempty M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hT : 0 ≤ T)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hpos : RicciPosInit (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci)) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) (fun t : Real => S.base.metric t)
          (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T delta := by
  exact pinch_init_sol_lt (I := I) (M := M) hS hT hdim hTsub hTreg
    (pinchInitLt_pos (I := I) (M := M)
      (G := fun t : Real => S.base.metric t)
      (Ric := twoTensorSecToFamily (I := I) (M := M) S.ricci)
      (scalar := S.scalar)
      (metricData_sol0 (I := I) (M := M) S)
      (metricData_sol0_pos (I := I) (M := M) S hpos)
      (scalar0_cont_sol (I := I) (M := M) S hS.isSolution
        (hTsub (show (0 : Real) ∈ Set.Icc 0 T from ⟨le_rfl, hT⟩))))

end DifferentialGeometry.PDE.RicciFlow
