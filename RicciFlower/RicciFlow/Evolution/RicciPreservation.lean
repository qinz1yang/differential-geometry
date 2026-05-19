import RicciFlower.DimensionThree.RicciControlsRm
import RicciFlower.MaximumPrinciple.TensorWeak
import RicciFlower.Realized.CurvatureProducers
import RicciFlower.LeviCivita.Koszul
import RicciFlower.Tensor.RSTensor.QuadraticBounds

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Ricci positivity and pinching preservation

This file contains the Ricci-flow-specific consumer layer for LaTeX Lemma 9.1
and Lemma 9.2.  The results here are conditional on the current tensor weak
maximum principle regularity package.  They do not reopen the analytic proof of
Hamilton's tensor maximum principle.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Realized
open Tensor0SBundle
open scoped BigOperators Manifold ContDiff

/-! ## Pure three-dimensional reaction algebra -/

/-- Matrix square of Ricci components in an orthonormal `Fin 3` basis. -/
def ricciSq3 (Ric : Fin 3 -> Fin 3 -> Real) (i j : Fin 3) : Real :=
  ∑ k : Fin 3, Ric i k * Ric k j

/-- Ricci component trace in an orthonormal `Fin 3` basis. -/
def ricciScal3 (Ric : Fin 3 -> Fin 3 -> Real) : Real :=
  ∑ i : Fin 3, Ric i i

/-- Ricci component norm square in an orthonormal `Fin 3` basis. -/
def ricciNorm3 (Ric : Fin 3 -> Fin 3 -> Real) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3, Ric i j * Ric i j

/-- The Ricci reaction tensor components
`2 R_ikjl Ric_kl - 2 Ric_i^k Ric_kj` in an orthonormal `Fin 3` basis. -/
def ricciReact
    (Rm : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (Ric : Fin 3 -> Fin 3 -> Real) (i j : Fin 3) : Real :=
  2 * (∑ k : Fin 3, ∑ l : Fin 3, Rm i k j l * Ric k l) -
    2 * ricciSq3 Ric i j

/-- The shifted pinching reaction for `S = Ric - delta R g`, in an
orthonormal `Fin 3` basis. -/
def pinchReact
    (delta : Real)
    (Rm : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (Ric : Fin 3 -> Fin 3 -> Real) (i j : Fin 3) : Real :=
  ricciReact Rm Ric i j -
    2 * delta * (ricciNorm3 Ric * RicciFlower.DimensionThree.delta3 i j -
      ricciScal3 Ric * Ric i j)

/-- Lemma 9.1 reaction algebra at a Ricci-null eigenvector. -/
theorem ricciReactNull
    (l1 l2 l3 : Real) (hnull : l1 = 0) :
    ricciReact (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0 =
      (l2 - l3) ^ 2 := by
  subst l1
  unfold ricciReact ricciSq3 RicciFlower.DimensionThree.stdRmDiag3
    RicciFlower.DimensionThree.ricciDiag3 RicciFlower.DimensionThree.ricciEigenScalar3
    RicciFlower.DimensionThree.delta3
  simp [Fin.sum_univ_three]
  ring

/-- Nonnegativity form of `ricciReactNull`. -/
theorem ricciReact_ge
    (l1 l2 l3 : Real) (hnull : l1 = 0) :
    0 <= ricciReact (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0 := by
  rw [ricciReactNull l1 l2 l3 hnull]
  positivity

/-- Lemma 9.2 shifted reaction algebra at a pinching-null eigenvector. -/
theorem pinchReactNull
    (delta l1 l2 l3 : Real)
    (hnull : l1 = delta * RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3) :
    pinchReact delta (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0 =
      delta ^ 2 * (1 - 3 * delta) *
          RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3 ^ 2 +
        (1 - delta) * (l2 - l3) ^ 2 := by
  let lhs :=
    pinchReact delta (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0
  let rhs :=
    delta ^ 2 * (1 - 3 * delta) *
        RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3 ^ 2 +
      (1 - delta) * (l2 - l3) ^ 2
  change lhs = rhs
  have hrel : delta * (l1 + l2 + l3) - l1 = 0 := by
    unfold RicciFlower.DimensionThree.ricciEigenScalar3 at hnull
    nlinarith
  have hfactor :
      lhs - rhs =
        (delta * (l1 + l2 + l3) - l1) *
          (3 * delta ^ 2 * l1 + 3 * delta ^ 2 * l2 + 3 * delta ^ 2 * l3 +
            2 * delta * l1 - delta * l2 - delta * l3 + 2 * l1 - l2 - l3) := by
    dsimp [lhs, rhs]
    unfold pinchReact ricciReact ricciSq3 ricciNorm3 ricciScal3
      RicciFlower.DimensionThree.stdRmDiag3 RicciFlower.DimensionThree.ricciDiag3
      RicciFlower.DimensionThree.ricciEigenScalar3 RicciFlower.DimensionThree.delta3
    simp [Fin.sum_univ_three]
    ring
  have hzero : lhs - rhs = 0 := by
    rw [hfactor, hrel]
    ring
  nlinarith

/-- Nonnegativity form of `pinchReactNull` for `0 <= delta <= 1/3`. -/
theorem pinchReact_ge
    (delta l1 l2 l3 : Real)
    (hdelta0 : 0 <= delta) (hdelta13 : delta <= (1 : Real) / 3)
    (hnull : l1 = delta * RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3) :
    0 <= pinchReact delta (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0 := by
  rw [pinchReactNull delta l1 l2 l3 hnull]
  have h1 : 0 <= delta ^ 2 * (1 - 3 * delta) *
      RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3 ^ 2 := by
    have hdelta_sq : 0 <= delta ^ 2 := sq_nonneg delta
    have hcoeff : 0 <= 1 - 3 * delta := by nlinarith
    have hscalar_sq : 0 <= RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3 ^ 2 :=
      sq_nonneg _
    positivity
  have h2 : 0 <= (1 - delta) * (l2 - l3) ^ 2 := by
    have hcoeff : 0 <= 1 - delta := by nlinarith
    have hsquare : 0 <= (l2 - l3) ^ 2 := sq_nonneg _
    positivity
  exact add_nonneg h1 h2

/-! ## Conditional tensor-WMP consumers -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

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
    (LeviCivita.leviCivitaConnectionOfMetric (I := I) (G 0)) (G 0)
  ricci_eq :
    ∀ x v w, Ric 0 x v w = K.ricci x (Curvature.vec2 (I := I) v w)

/-- Strict positivity of the canonical initial Ricci tensor. -/
def MetricRicciPos
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric) : Prop :=
  ∀ x v, v ≠ 0 -> 0 < D.K.ricci x (Curvature.vec2 (I := I) v v)

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
        D.K.ricci x (Curvature.vec2 (I := I) v v))

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
      c <= D.K.ricci x (Curvature.vec2 (I := I) v v)

/-- Ricci quadratic evaluation on the initial unit tangent bundle. -/
def unitRicEval
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (p : UnitTangent (I := I) (M := M) (G 0)) : Real :=
  D.K.ricci (UnitTangent.base (I := I) (M := M) p)
    (Curvature.vec2 (I := I)
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
        D.K.ricci x (Curvature.vec2 (I := I)
          (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0 := by
      have hzero' :
          D.K.ricci x (fun _ : Fin 2 => (0 : TangentSpace I x)) = 0 := by
        simpa [quad02] using
          RicciFlower.tensor02_smul2 (I := I) (M := M) (D.K.ricci x)
            0 (0 : TangentSpace I x)
      have hvec :
          Curvature.vec2 (I := I) (0 : TangentSpace I x) (0 : TangentSpace I x) =
            (fun _ : Fin 2 => (0 : TangentSpace I x)) := by
        funext i
        simp [Curvature.vec2]
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
        simpa [u, r] using RicciFlower.metric_smul2 (I := I) (M := M) (G 0) a v
      _ = 1 := haa
  have hRic_unit := hlower x u hunit
  have hRic_scale :
      D.K.ricci x (Curvature.vec2 (I := I) u u) =
        a * a * D.K.ricci x (Curvature.vec2 (I := I) v v) := by
    have hscale' :
        D.K.ricci x (fun _ : Fin 2 => a • v) =
          a * a * D.K.ricci x (fun _ : Fin 2 => v) := by
      simpa [quad02] using
        RicciFlower.tensor02_smul2 (I := I) (M := M)
          (D.K.ricci x) a v
    have hvecu :
        Curvature.vec2 (I := I) u u = (fun _ : Fin 2 => u) := by
      funext i
      simp [Curvature.vec2]
    have hvecv :
        Curvature.vec2 (I := I) v v = (fun _ : Fin 2 => v) := by
      funext i
      simp [Curvature.vec2]
    simpa [hvecu, hvecv, u] using hscale'
  have hineq :
      c <= a * a * D.K.ricci x (Curvature.vec2 (I := I) v v) := by
    simpa [hRic_scale] using hRic_unit
  have hs2_nonneg : 0 <= s * s := mul_nonneg (le_of_lt hspos) (le_of_lt hspos)
  have hmul := mul_le_mul_of_nonneg_left hineq hs2_nonneg
  have hcancel : (s * s) * (a * a *
        D.K.ricci x (Curvature.vec2 (I := I) v v)) =
      D.K.ricci x (Curvature.vec2 (I := I) v v) := by
    have hmul : (s * s) * (a * a) = 1 := by
      have hsa : s * a = 1 := by
        simp [a, hsne]
      calc
        (s * s) * (a * a) = (s * a) * (s * a) := by ring
        _ = 1 := by rw [hsa]; ring
    calc
      (s * s) * (a * a *
          D.K.ricci x (Curvature.vec2 (I := I) v v)) =
          ((s * s) * (a * a)) *
            D.K.ricci x (Curvature.vec2 (I := I) v v) := by ring
      _ = D.K.ricci x (Curvature.vec2 (I := I) v v) := by
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
        simpa [x0, v0] using UnitTangent.unit (I := I) (M := M) p0
      have hv0 : v0 ≠ 0 := by
        intro hz
        have hbad : (0 : Real) = 1 := by
          simpa [hz] using hunit0
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
  fin_cases i <;> simp [Curvature.vec2]

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

/-- Uniform initial lower Ricci and upper scalar bounds select an initial
pinching constant. -/
theorem pinchInit_of_bounds
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hbounds : InitBounds (I := I) (M := M) G Ric scalar) :
    PinchInit (I := I) (M := M) G Ric scalar := by
  rcases hbounds with ⟨c, C, hc, hC, hRicLower, hScalarUpper⟩
  let delta : Real := min ((1 : Real) / 3) (c / C)
  have hthird_pos : 0 < (1 : Real) / 3 := by norm_num
  have hdiv_pos : 0 < c / C := div_pos hc hC
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min hthird_pos hdiv_pos
  have hdelta_le_third : delta <= (1 : Real) / 3 := by
    dsimp [delta]
    exact min_le_left _ _
  have hdelta_nonneg : 0 <= delta := le_of_lt hdelta_pos
  have hdelta_le_div : delta <= c / C := by
    dsimp [delta]
    exact min_le_right _ _
  have hdeltaC_le_c : delta * C <= c := by
    have hmul := mul_le_mul_of_nonneg_right hdelta_le_div (le_of_lt hC)
    have hcancel : c / C * C = c := div_mul_cancel₀ c (ne_of_gt hC)
    nlinarith
  refine ⟨delta, hdelta_pos, hdelta_le_third, ?_⟩
  intro x v
  have hg_nonneg : 0 <= (G 0).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact le_of_lt ((G 0).pos x v hv)
  have hscalar_le : delta * scalar 0 x <= delta * C :=
    mul_le_mul_of_nonneg_left (hScalarUpper x) hdelta_nonneg
  have hscaled_le : delta * scalar 0 x * (G 0).inner x v v <= c * (G 0).inner x v v := by
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

/-- Strict initial Ricci positivity gives initial pinching once the compactness
selector has produced the uniform initial bounds. -/
theorem pinchInit_of_pos
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hpos : RicciPosInit (I := I) (M := M) Ric)
    (hbounds : BoundsOfPosRic (I := I) (M := M) G Ric scalar) :
    PinchInit (I := I) (M := M) G Ric scalar := by
  exact pinchInit_of_bounds (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (hbounds hpos)

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
  pinchInit_of_bounds (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar)
    (bounds_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin
      (scalarUpper_cont (M := M) hscalar))

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
  pinchInit_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (ricMin := ricMin)
    (ricMin_of_metric (I := I) (M := M) D hmin) hscalar

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
  rcases metricMin_pos (I := I) (M := M) D hpos with ⟨ricMin, hmin⟩
  exact pinchInit_metric (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (ricMin := ricMin) D hmin hscalar

/-- Preserved pinching conclusion for a fixed `delta`. -/
def PinchPres
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) (T delta : Real) : Prop :=
  TwoTensorFamilyNonnegativeOn (I := I) (M := M)
    (pinchTensor (I := I) (M := M) G Ric scalar delta) (Set.Icc 0 T)

/-- Tensor-WMP data for the shifted tensor `Ric - delta R g`. -/
structure PinchWMPData
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) (T delta : Real) : Type _ where
  X : TimeDependentVectorField (I := I) (M := M)
  N : TwoTensorReaction (I := I) (M := M)
  nabla2S : TensorNabla2Family (I := I) (M := M)
  nablaS : TensorNabla1Family (I := I) (M := M)
  reg :
    TensorWMPRegularityOn (I := I) (M := M) G
      (pinchTensor (I := I) (M := M) G Ric scalar delta) X N T
  parabolic :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M) G
      (pinchTensor (I := I) (M := M) G Ric scalar delta) X N
      nabla2S nablaS T
  null :
    TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T)

/-- Lemma 9.1 as a conditional consumer of Hamilton's tensor WMP. -/
theorem ricci_nonneg_wmp
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

/-- Lemma 9.2 as a conditional consumer of Hamilton's tensor WMP. -/
theorem ricci_pinch_wmp
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

/-- Corollary 9.3 setup from an already selected initial pinching constant. -/
theorem pinch_init_wmp
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
  exact ricci_pinch_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (delta := delta) (X := data.X) (N := data.N)
    (nabla2S := data.nabla2S) (nablaS := data.nablaS) (T := T)
    hT (le_of_lt hdelta0) hdelta13 data.reg data.parabolic data.null hpinch0

/-- Corollary 9.3 conditional form: strict initial Ricci positivity supplies a
pinching constant, and Lemma 9.2 preserves it. -/
theorem strict_pinch_wmp
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

/-- Corollary 9.3 conditional form using a realized continuous base
Ricci-minimum function instead of a raw compactness selector. -/
theorem strict_pinch_min
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

/-- Corollary 9.3 conditional form with the initial Ricci tensor realized from
the initial metric. -/
theorem strict_pinch_metric
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

/-- Corollary 9.3 conditional form using the unit tangent compact-minimum
selector. -/
theorem strict_pinch_pos
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

end RicciFlow
end RicciFlower
