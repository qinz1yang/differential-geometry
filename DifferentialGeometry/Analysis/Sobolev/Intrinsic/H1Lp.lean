import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lp
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# `Lp`-witnessed intrinsic `H¹` space on a closed Riemannian manifold

This file defines an `Lp`-witnessed variant of the intrinsic `H¹` predicate on a
closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`. The key
deviation from the function-based predicate of `IntrinsicLp.lean` is that the
weak Riemannian gradient witness here is required to live in the
*Banach-space quotient* `MeasureTheory.Lp E 2 μ_g`, rather than being an
arbitrary measurable map `M → E`.

This sidesteps part of the closure-under-addition obstruction that arises
when one only has `AEStronglyMeasurable` witnesses, because the `Lp` carrier
is an honest Banach space (in particular it is closed under addition and
scalar multiplication), and the integration-by-parts identity is invariant
under a.e.-modification of either the function or the witness.

In addition, the predicate carries a *joint measurability clause*
`PairAEMeasurable g G` against arbitrary almost-everywhere strongly
measurable tangent test fields. This strengthening makes closure under
addition unconditional, while remaining provable for the gradients of smooth
functions (where the Riemannian gradient is a smooth tangent section). The
latter case is delivered when needed by chart-localized arguments at the
point of use; the predicate definition leaves the clause as an existence
witness inside each `MemH1Lp` element.

## Main definitions

* `PairAEMeasurable g G` : the pairing `x ↦ g.inner x (G x) (V x)` is AESM
  for every AESM `V`. Closed under addition, scalar, negation, and a.e.
  modification of `G`.
* `MemH1Lp g u` : the `Lp ℝ 2 μ_g` class `u` is in the `Lp`-witnessed `H¹`
  space, i.e., there is a witness `G : Lp E 2 μ_g` whose representative
  satisfies the standard integration-by-parts identity against every smooth
  compactly-supported tangent test field, the metric `g`-norm of `G` is
  in `L^2`, and `G` satisfies the joint AESM pairing clause.

## Main results

* `MemH1Lp.zero`, `MemH1Lp.const_smul`, `MemH1Lp.neg`, `MemH1Lp.add`,
  `MemH1Lp.sub` : closure under the `ℝ`-vector-space operations on the `Lp`
  quotient. Closure under addition is unconditional.

The predicate uses the Riemannian volume measure and works in the natural
"closed manifold" hypotheses `[CompactSpace M] [I.Boundaryless]
[T2Space M] [SigmaCompactSpace M]`, in line with the project's hypothesis
discipline. The model space `E` is required to be a real inner-product
space.

## Implementation notes

The `Lp` quotient is constructed at the abstract level of "almost-everywhere
classes" of measurable functions. Since the IBP identity is bilinear in
`(u, G)` and is invariant under a.e.-modification, well-definedness of the
predicate on classes (rather than representatives) follows automatically,
provided one phrases the integrand correctly via `Lp.coeFn`. We do this here
by reducing to the `HasWeakRiemannianGradLp` predicate of `IntrinsicLp.lean`
applied to the canonical representatives.

The metric `g`-norm `√(g(G,G))` is included as a separate `MemLp 2`
hypothesis on the witness. On a closed (compact) manifold the Euclidean norm
on `E` and the metric `g`-norm are equivalent, so the two formulations
coincide in spirit; the explicit hypothesis gives a clean reduction to the
existing `HasWeakRiemannianGradLp.add` infrastructure when paired with
appropriate measurability witnesses for the cross pairings.

The joint-AESM clause `PairAEMeasurable` is preserved under bilinear
operations on `G`: addition, scalar multiplication, negation, and a.e.
modification. Verification of the clause for a specific witness — for
example the gradient of a smooth function — is delivered through
chart-localized arguments at the point of construction.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace IntrinsicH1Lp
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma g_inner_zero_left
    (g : SmoothRiemannianMetric I M) (x : M) (y : TangentSpace I x) :
    g.inner x (0 : TangentSpace I x) y = 0 := by
  rw [map_zero, ContinuousLinearMap.zero_apply]

private lemma g_inner_add_left
    (g : SmoothRiemannianMetric I M) (x : M) (v w y : TangentSpace I x) :
    g.inner x (v + w) y = g.inner x v y + g.inner x w y := by
  rw [map_add (g.inner x), ContinuousLinearMap.add_apply]

private lemma g_inner_add_right
    (g : SmoothRiemannianMetric I M) (x : M) (v w y : TangentSpace I x) :
    g.inner x v (w + y) = g.inner x v w + g.inner x v y := by
  rw [map_add (g.inner x v)]

private lemma g_inner_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (v y : TangentSpace I x) :
    g.inner x (c • v) y = c * g.inner x v y := by
  rw [map_smul (g.inner x), ContinuousLinearMap.smul_apply, smul_eq_mul]

private lemma g_inner_neg_left
    (g : SmoothRiemannianMetric I M) (x : M) (v y : TangentSpace I x) :
    g.inner x (-v) y = - g.inner x v y := by
  rw [map_neg, ContinuousLinearMap.neg_apply]

/-- Scalar homogeneity for the metric `g`-norm. -/
private lemma g_norm_const_smul
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (v : TangentSpace I x) :
    Real.sqrt (g.inner x (c • v) (c • v)) =
      |c| * Real.sqrt (g.inner x v v) := by
  rw [g_inner_smul_left g x c v (c • v),
    map_smul (g.inner x v), smul_eq_mul]
  rw [show c * (c * g.inner x v v) = c ^ 2 * g.inner x v v from by ring]
  rw [Real.sqrt_mul (sq_nonneg c)]
  rw [Real.sqrt_sq_eq_abs]

/-- Negation preserves the metric `g`-norm. -/
private lemma g_norm_neg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    Real.sqrt (g.inner x (-v) (-v)) = Real.sqrt (g.inner x v v) := by
  rw [g_inner_neg_left g x v (-v), map_neg]
  simp

/-- Triangle inequality for the metric `g`-norm. Reproves the result of
`IntrinsicLp.lean` (where it is `private`) for use in this file. -/
private lemma g_norm_triangle
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    Real.sqrt (g.inner x (v + w) (v + w)) ≤
      Real.sqrt (g.inner x v v) + Real.sqrt (g.inner x w w) := by
  set a := g.inner x v v
  set b := g.inner x w w
  set c := g.inner x v w
  have ha_nn : 0 ≤ a := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · simp [a, hv0]
    · exact (g.pos x v hv0).le
  have hb_nn : 0 ≤ b := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · simp [b, hw0]
    · exact (g.pos x w hw0).le
  have hCS_sq : c ^ 2 ≤ a * b := by
    have hquad : ∀ t : ℝ, 0 ≤ t * t * a + 2 * t * c + b := by
      intro t
      have hpos : 0 ≤ g.inner x (t • v + w) (t • v + w) := by
        rcases eq_or_ne (t • v + w) 0 with hz | hnz
        · rw [hz, g_inner_zero_left]
        · exact (g.pos x _ hnz).le
      have h_expand : g.inner x (t • v + w) (t • v + w) =
          t * t * a + 2 * t * c + b := by
        rw [g_inner_add_left g x (t • v) w (t • v + w),
            map_add (g.inner x (t • v)) (t • v) w,
            map_add (g.inner x w) (t • v) w,
            g_inner_smul_left g x t v (t • v),
            g_inner_smul_left g x t v w,
            map_smul (g.inner x v) t v,
            map_smul (g.inner x w) t v]
        simp only [smul_eq_mul]
        have hsymm : g.inner x w v = g.inner x v w := g.symm x w v
        rw [hsymm]; ring
      rw [h_expand] at hpos
      exact hpos
    rcases lt_or_eq_of_le ha_nn with ha_pos | ha_zero
    · have hroot := hquad (-c / a)
      have hsimp : -c / a * (-c / a) * a + 2 * (-c / a) * c + b =
          b - c^2 / a := by field_simp; ring
      rw [hsimp] at hroot
      have hcsa : c ^ 2 / a ≤ b := by linarith
      have h1 : c ^ 2 = a * (c ^ 2 / a) := by field_simp
      rw [h1]
      exact mul_le_mul_of_nonneg_left hcsa ha_nn
    · have ha_eq : a = 0 := ha_zero.symm
      have hv_zero : v = 0 := by
        by_contra hne
        have hpos : 0 < g.inner x v v := g.pos x v hne
        rw [show g.inner x v v = a from rfl, ha_eq] at hpos
        exact lt_irrefl 0 hpos
      have hc_eq : c = 0 := by
        change g.inner x v w = 0
        rw [hv_zero]
        exact g_inner_zero_left g x w
      rw [hc_eq, ha_eq]; simp
  have hC : |c| ≤ Real.sqrt (a * b) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hCS_sq
  have hsqrt_mul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b :=
    Real.sqrt_mul ha_nn b
  rw [hsqrt_mul] at hC
  have hc_le : c ≤ Real.sqrt a * Real.sqrt b := (le_abs_self c).trans hC
  have h_expand : g.inner x (v + w) (v + w) =
      a + 2 * c + b := by
    rw [g_inner_add_left g x v w (v + w),
      map_add (g.inner x v) v w, map_add (g.inner x w) v w]
    have hsymm : g.inner x w v = g.inner x v w := g.symm x w v
    rw [hsymm]; ring
  rw [h_expand]
  have h_le_sq : a + 2 * c + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have h_sq_expand : (Real.sqrt a + Real.sqrt b) ^ 2 =
        a + 2 * (Real.sqrt a * Real.sqrt b) + b := by
      have ha_sq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha_nn
      have hb_sq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb_nn
      nlinarith [ha_sq, hb_sq]
    rw [h_sq_expand]
    linarith
  have h_nn : 0 ≤ Real.sqrt a + Real.sqrt b :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_sqrt_le := Real.sqrt_le_sqrt h_le_sq
  rw [show Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) = Real.sqrt a + Real.sqrt b
      from Real.sqrt_sq h_nn] at h_sqrt_le
  exact h_sqrt_le

/-- Congruence of `HasWeakRiemannianGradLp` along a.e. modifications of
both `u` and `G`. -/
theorem hasWeakRiemannianGradLp_congr_ae
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {u u' : M → ℝ} {G G' : M → E}
    (hu : u =ᵐ[riemannianVolumeMeasure I M g] u')
    (hG : G =ᵐ[riemannianVolumeMeasure I M g] G')
    (h : HasWeakRiemannianGradLp (I := I) (M := M) g u G) :
    HasWeakRiemannianGradLp (I := I) (M := M) g u' G' := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  refine ⟨?_, ?_⟩
  · intro Y
    have hcong : (fun x : M => g.inner x (G' x) (Y x))
        =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => g.inner x (G x) (Y x)) := by
      filter_upwards [hG] with x hx
      rw [hx]
    exact (h.1 Y).congr hcong.symm
  · intro X hX
    have hLHS : (fun x : M => g.inner x (G' x) (X x))
        =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => g.inner x (G x) (X x)) := by
      filter_upwards [hG] with x hx
      rw [hx]
    have hRHS : (fun x : M => u' x * divergence_g (I := I) g X x)
        =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => u x * divergence_g (I := I) g X x) := by
      filter_upwards [hu] with x hx
      rw [hx]
    rw [integral_congr_ae hLHS, integral_congr_ae hRHS]
    exact h.2 X hX

/-- The metric `g`-norm `MemLp` hypothesis is invariant under a.e. modification
of the witness. -/
theorem memLp_g_norm_congr_ae
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {G G' : M → E} {p : ℝ≥0∞}
    (hG : G =ᵐ[riemannianVolumeMeasure I M g] G')
    (h : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
      (riemannianVolumeMeasure I M g)) :
    MemLp (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) p
      (riemannianVolumeMeasure I M g) := by
  refine (memLp_congr_ae ?_).mp h
  filter_upwards [hG] with x hx
  rw [hx]

/-- The joint AESM pairing clause: `G` pairs AESM-ly against any AESM `V`. -/
def PairAEMeasurable
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (G : M → E) : Prop :=
  ∀ V : M → E, AEStronglyMeasurable V (riemannianVolumeMeasure I M g) →
    AEStronglyMeasurable (fun x : M => g.inner x (G x) (V x))
      (riemannianVolumeMeasure I M g)

namespace PairAEMeasurable

variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

/-- The zero witness pairs AESM-ly against everything. -/
theorem zero (g : SmoothRiemannianMetric I M) :
    PairAEMeasurable (I := I) (M := M) g (fun _ : M => (0 : E)) := by
  intro V _
  have hcongr : (fun x : M =>
      g.inner x ((fun _ : M => (0 : E)) x) (V x)) =
      (fun _ : M => (0 : ℝ)) := by
    funext x
    change g.inner x (0 : TangentSpace I x) (V x) = 0
    exact g_inner_zero_left g x (V x)
  rw [hcongr]
  exact aestronglyMeasurable_const

/-- Sum of two PairAEMeasurable witnesses. -/
theorem add {g : SmoothRiemannianMetric I M} {G G' : M → E}
    (hG : PairAEMeasurable (I := I) (M := M) g G)
    (hG' : PairAEMeasurable (I := I) (M := M) g G') :
    PairAEMeasurable (I := I) (M := M) g (fun x => G x + G' x) := by
  intro V hV
  have hcongr : (fun x : M =>
      g.inner x ((fun y : M => G y + G' y) x) (V x)) =
      (fun x : M => g.inner x (G x) (V x) + g.inner x (G' x) (V x)) := by
    funext x
    exact g_inner_add_left g x (G x) (G' x) (V x)
  rw [hcongr]
  exact (hG V hV).add (hG' V hV)

/-- Constant scalar multiple of a PairAEMeasurable witness. -/
theorem const_smul {g : SmoothRiemannianMetric I M} {G : M → E} (c : ℝ)
    (hG : PairAEMeasurable (I := I) (M := M) g G) :
    PairAEMeasurable (I := I) (M := M) g (fun x => c • G x) := by
  intro V hV
  have hcongr : (fun x : M =>
      g.inner x ((fun y : M => c • G y) x) (V x)) =
      (fun x : M => c * g.inner x (G x) (V x)) := by
    funext x
    exact g_inner_smul_left g x c (G x) (V x)
  rw [hcongr]
  exact (hG V hV).const_mul c

/-- Negation of a PairAEMeasurable witness. -/
theorem neg {g : SmoothRiemannianMetric I M} {G : M → E}
    (hG : PairAEMeasurable (I := I) (M := M) g G) :
    PairAEMeasurable (I := I) (M := M) g (fun x => -G x) := by
  have h := const_smul (I := I) (M := M) (-1 : ℝ) hG
  have heq : (fun x : M => (-1 : ℝ) • G x) = (fun x : M => -G x) := by
    funext x; rw [neg_one_smul]
  rw [heq] at h
  exact h

/-- The PairAEMeasurable property is invariant under a.e. modification of `G`. -/
theorem congr_ae {g : SmoothRiemannianMetric I M} {G G' : M → E}
    (hG : G =ᵐ[riemannianVolumeMeasure I M g] G')
    (h : PairAEMeasurable (I := I) (M := M) g G) :
    PairAEMeasurable (I := I) (M := M) g G' := by
  intro V hV
  have hcong : (fun x : M => g.inner x (G' x) (V x))
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => g.inner x (G x) (V x)) := by
    filter_upwards [hG] with x hx
    rw [hx]
  exact (h V hV).congr hcong.symm

end PairAEMeasurable

/-- `MemH1Lp g u` asserts that `u : Lp ℝ 2 μ_g` lies in the `Lp`-witnessed
intrinsic `H¹` space. Concretely, there exists a witness
`G : Lp E 2 μ_g` such that, working with the canonical representatives
`(u : M → ℝ)` and `(G : M → E)`:

* the pair satisfies the integration-by-parts identity against every
  smooth compactly-supported tangent test field;
* the metric `g`-norm `x ↦ √(g(G x, G x))` is in `L²`;
* the witness `G` pairs `AEStronglyMeasurable`-ly against any AESM test
  tangent field `V` — i.e., `x ↦ g.inner x (G x) (V x)` is AESM whenever
  `V` is.

The third clause is preserved under bilinear operations and a.e.
modification, making the predicate unconditionally closed under addition
and scalar multiplication. Verification of the clause for a specific
concrete witness — for example the gradient of a smooth function — is
performed at the point of construction via chart-localized arguments. -/
def MemH1Lp [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (u : Lp ℝ 2 (riemannianVolumeMeasure I M g)) :
    Prop :=
  ∃ G : Lp E 2 (riemannianVolumeMeasure I M g),
    HasWeakRiemannianGradLp (I := I) (M := M) g
      (fun x : M => (u : M → ℝ) x) (fun x : M => (G : M → E) x) ∧
    MemLp (fun x : M => Real.sqrt (g.inner x ((G : M → E) x) ((G : M → E) x))) 2
      (riemannianVolumeMeasure I M g) ∧
    PairAEMeasurable (I := I) (M := M) g (fun x : M => (G : M → E) x)

namespace MemH1Lp

variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

/-- The zero class lies in `MemH1Lp` with the zero witness. -/
theorem zero (g : SmoothRiemannianMetric I M) :
    MemH1Lp (I := I) (M := M) g (0 : Lp ℝ 2 (riemannianVolumeMeasure I M g)) := by
  refine ⟨(0 : Lp E 2 (riemannianVolumeMeasure I M g)), ?_, ?_, ?_⟩
  · have h0u : (fun x : M => ((0 : Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : ℝ)) := by
      have h := Lp.coeFn_zero (E := ℝ) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))
      filter_upwards [h] with x hx
      exact hx
    have h0G : (fun x : M => ((0 : Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : E)) := by
      have h := Lp.coeFn_zero (E := E) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))
      filter_upwards [h] with x hx
      exact hx
    exact hasWeakRiemannianGradLp_congr_ae (I := I) (M := M) (g := g)
      h0u.symm h0G.symm (HasWeakRiemannianGradLp.zero (I := I) (M := M) g)
  · have h0G : (fun x : M => ((0 : Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : E)) := by
      have h := Lp.coeFn_zero (E := E) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))
      filter_upwards [h] with x hx
      exact hx
    refine memLp_g_norm_congr_ae (I := I) (M := M) (g := g) (p := 2) h0G.symm ?_
    have hcongr : (fun x : M => Real.sqrt
          (g.inner x ((fun _ : M => (0 : E)) x) ((fun _ : M => (0 : E)) x))) =
        (fun _ : M => (0 : ℝ)) := by
      funext x
      change Real.sqrt (g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0
      rw [g_inner_zero_left g x (0 : TangentSpace I x)]
      exact Real.sqrt_zero
    rw [hcongr]
    exact MemLp.zero
  · have h0G : (fun x : M => ((0 : Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : E)) := by
      have h := Lp.coeFn_zero (E := E) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))
      filter_upwards [h] with x hx
      exact hx
    exact PairAEMeasurable.congr_ae (I := I) (M := M) (g := g) h0G.symm
      (PairAEMeasurable.zero (I := I) (M := M) g)

/-- Scalar multiplication closure of `MemH1Lp`. -/
theorem const_smul (g : SmoothRiemannianMetric I M) (c : ℝ)
    {u : Lp ℝ 2 (riemannianVolumeMeasure I M g)}
    (hu : MemH1Lp (I := I) (M := M) g u) :
    MemH1Lp (I := I) (M := M) g (c • u) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  obtain ⟨G, hG_weak, hG_p, hG_pair⟩ := hu
  refine ⟨c • G, ?_, ?_, ?_⟩
  · have h_smul_G : (fun x : M => ((c • G : Lp E 2 (riemannianVolumeMeasure I M g)) :
          M → E) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => c • (G : M → E) x) := by
      filter_upwards [Lp.coeFn_smul c G] with x hx
      exact hx
    have h_smul_u : (fun x : M => ((c • u : Lp ℝ 2 (riemannianVolumeMeasure I M g)) :
          M → ℝ) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => c * (u : M → ℝ) x) := by
      filter_upwards [Lp.coeFn_smul c u] with x hx
      simpa using hx
    have h_smul : HasWeakRiemannianGradLp (I := I) (M := M) g
        (fun x : M => c * (u : M → ℝ) x) (fun x : M => c • (G : M → E) x) :=
      HasWeakRiemannianGradLp.const_smul (I := I) (M := M) (p := 2) (by norm_num) c
        hG_weak (Lp.memLp u)
    exact hasWeakRiemannianGradLp_congr_ae (I := I) (M := M) (g := g)
      h_smul_u.symm h_smul_G.symm h_smul
  · have h_smul_G : (fun x : M => ((c • G : Lp E 2 (riemannianVolumeMeasure I M g)) :
          M → E) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => c • (G : M → E) x) := by
      filter_upwards [Lp.coeFn_smul c G] with x hx
      exact hx
    refine memLp_g_norm_congr_ae (I := I) (M := M) (g := g) (p := 2) h_smul_G.symm ?_
    have hcongr : (fun x : M => Real.sqrt
        (g.inner x ((fun y : M => c • (G : M → E) y) x)
          ((fun y : M => c • (G : M → E) y) x))) =
        (fun x : M => |c| * Real.sqrt (g.inner x ((G : M → E) x) ((G : M → E) x))) := by
      funext x
      exact g_norm_const_smul g x c ((G : M → E) x)
    rw [hcongr]
    exact hG_p.const_mul (|c|)
  · have h_smul_G : (fun x : M => ((c • G : Lp E 2 (riemannianVolumeMeasure I M g)) :
          M → E) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => c • (G : M → E) x) := by
      filter_upwards [Lp.coeFn_smul c G] with x hx
      exact hx
    exact PairAEMeasurable.congr_ae (I := I) (M := M) (g := g) h_smul_G.symm
      (PairAEMeasurable.const_smul (I := I) (M := M) c hG_pair)

/-- Negation closure of `MemH1Lp`. -/
theorem neg (g : SmoothRiemannianMetric I M)
    {u : Lp ℝ 2 (riemannianVolumeMeasure I M g)}
    (hu : MemH1Lp (I := I) (M := M) g u) :
    MemH1Lp (I := I) (M := M) g (-u) := by
  have h := const_smul (I := I) (M := M) g (-1 : ℝ) hu
  have h_eq : ((-1 : ℝ) • u : Lp ℝ 2 (riemannianVolumeMeasure I M g)) = -u := by
    rw [neg_one_smul]
  rw [h_eq] at h
  exact h

end MemH1Lp

namespace MemH1Lp

variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

/-- Addition closure of `MemH1Lp`. Unconditional thanks to the joint-AESM
clause baked into the predicate. -/
theorem add (g : SmoothRiemannianMetric I M)
    {u v : Lp ℝ 2 (riemannianVolumeMeasure I M g)}
    (hu : MemH1Lp (I := I) (M := M) g u)
    (hv : MemH1Lp (I := I) (M := M) g v) :
    MemH1Lp (I := I) (M := M) g (u + v) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  obtain ⟨G, hG_weak, hG_p, hG_pair⟩ := hu
  obtain ⟨G', hG'_weak, hG'_p, hG'_pair⟩ := hv
  refine ⟨G + G', ?_, ?_, ?_⟩
  · have h_sum_G : (fun x : M => ((G + G' : Lp E 2 (riemannianVolumeMeasure I M g)) :
          M → E) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => (G : M → E) x + (G' : M → E) x) := by
      filter_upwards [Lp.coeFn_add G G'] with x hx
      exact hx
    have h_sum_u : (fun x : M => ((u + v : Lp ℝ 2 (riemannianVolumeMeasure I M g)) :
          M → ℝ) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => (u : M → ℝ) x + (v : M → ℝ) x) := by
      filter_upwards [Lp.coeFn_add u v] with x hx
      exact hx
    have h_add : HasWeakRiemannianGradLp (I := I) (M := M) g
        (fun x : M => (u : M → ℝ) x + (v : M → ℝ) x)
        (fun x : M => (G : M → E) x + (G' : M → E) x) :=
      HasWeakRiemannianGradLp.add (I := I) (M := M) (p := 2) (by norm_num)
        hG_weak hG'_weak (Lp.memLp u) (Lp.memLp v) hG_p hG'_p
    exact hasWeakRiemannianGradLp_congr_ae (I := I) (M := M) (g := g)
      h_sum_u.symm h_sum_G.symm h_add
  · have h_sum_G : (fun x : M => ((G + G' : Lp E 2 (riemannianVolumeMeasure I M g)) :
          M → E) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => (G : M → E) x + (G' : M → E) x) := by
      filter_upwards [Lp.coeFn_add G G'] with x hx
      exact hx
    refine memLp_g_norm_congr_ae (I := I) (M := M) (g := g) (p := 2) h_sum_G.symm ?_
    have hAESM : AEStronglyMeasurable
        (fun x : M => Real.sqrt
          (g.inner x ((fun y : M => (G : M → E) y + (G' : M → E) y) x)
            ((fun y : M => (G : M → E) y + (G' : M → E) y) x)))
        (riemannianVolumeMeasure I M g) := by
      have hGG : AEStronglyMeasurable
          (fun x : M => g.inner x ((G : M → E) x) ((G : M → E) x))
          (riemannianVolumeMeasure I M g) :=
        hG_pair (fun x : M => (G : M → E) x) (Lp.aestronglyMeasurable G)
      have hGG' : AEStronglyMeasurable
          (fun x : M => g.inner x ((G : M → E) x) ((G' : M → E) x))
          (riemannianVolumeMeasure I M g) :=
        hG_pair (fun x : M => (G' : M → E) x) (Lp.aestronglyMeasurable G')
      have hG'G' : AEStronglyMeasurable
          (fun x : M => g.inner x ((G' : M → E) x) ((G' : M → E) x))
          (riemannianVolumeMeasure I M g) :=
        hG'_pair (fun x : M => (G' : M → E) x) (Lp.aestronglyMeasurable G')
      have hsum_aem : AEStronglyMeasurable
          (fun x : M => g.inner x ((G : M → E) x + (G' : M → E) x)
            ((G : M → E) x + (G' : M → E) x))
          (riemannianVolumeMeasure I M g) := by
        have hpt : ∀ x : M,
            g.inner x ((G : M → E) x + (G' : M → E) x)
              ((G : M → E) x + (G' : M → E) x) =
            g.inner x ((G : M → E) x) ((G : M → E) x) +
              (g.inner x ((G : M → E) x) ((G' : M → E) x) +
              (g.inner x ((G' : M → E) x) ((G : M → E) x) +
              g.inner x ((G' : M → E) x) ((G' : M → E) x))) := by
          intro x
          calc g.inner x ((G : M → E) x + (G' : M → E) x)
                ((G : M → E) x + (G' : M → E) x)
              = g.inner x ((G : M → E) x) ((G : M → E) x + (G' : M → E) x) +
                g.inner x ((G' : M → E) x) ((G : M → E) x + (G' : M → E) x) :=
                g_inner_add_left g x ((G : M → E) x) ((G' : M → E) x)
                  ((G : M → E) x + (G' : M → E) x)
            _ = (g.inner x ((G : M → E) x) ((G : M → E) x) +
                  g.inner x ((G : M → E) x) ((G' : M → E) x)) +
                (g.inner x ((G' : M → E) x) ((G : M → E) x) +
                  g.inner x ((G' : M → E) x) ((G' : M → E) x)) := by
                congr 1
                · exact g_inner_add_right g x ((G : M → E) x)
                    ((G : M → E) x) ((G' : M → E) x)
                · exact g_inner_add_right g x ((G' : M → E) x)
                    ((G : M → E) x) ((G' : M → E) x)
            _ = g.inner x ((G : M → E) x) ((G : M → E) x) +
                  (g.inner x ((G : M → E) x) ((G' : M → E) x) +
                  (g.inner x ((G' : M → E) x) ((G : M → E) x) +
                  g.inner x ((G' : M → E) x) ((G' : M → E) x))) := by ring
        have hcong : (fun x : M => g.inner x ((G : M → E) x + (G' : M → E) x)
              ((G : M → E) x + (G' : M → E) x)) =
            (fun x : M => g.inner x ((G : M → E) x) ((G : M → E) x) +
              (g.inner x ((G : M → E) x) ((G' : M → E) x) +
              (g.inner x ((G' : M → E) x) ((G : M → E) x) +
              g.inner x ((G' : M → E) x) ((G' : M → E) x)))) := by
          funext x; exact hpt x
        rw [hcong]
        have hG'G : AEStronglyMeasurable
            (fun x : M => g.inner x ((G' : M → E) x) ((G : M → E) x))
            (riemannianVolumeMeasure I M g) := by
          have hcong2 : (fun x : M => g.inner x ((G' : M → E) x) ((G : M → E) x)) =
              (fun x : M => g.inner x ((G : M → E) x) ((G' : M → E) x)) := by
            funext x
            exact g.symm x ((G' : M → E) x) ((G : M → E) x)
          rw [hcong2]
          exact hGG'
        exact hGG.add (hGG'.add (hG'G.add hG'G'))
      exact Real.continuous_sqrt.comp_aestronglyMeasurable hsum_aem
    refine MemLp.of_le (g := fun x : M =>
        Real.sqrt (g.inner x ((G : M → E) x) ((G : M → E) x)) +
          Real.sqrt (g.inner x ((G' : M → E) x) ((G' : M → E) x)))
      (hG_p.add hG'_p) hAESM ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    have htri := g_norm_triangle (I := I) (M := M) g x
      ((G : M → E) x) ((G' : M → E) x)
    have hLHS_nn : 0 ≤ Real.sqrt
        (g.inner x ((fun y : M => (G : M → E) y + (G' : M → E) y) x)
          ((fun y : M => (G : M → E) y + (G' : M → E) y) x)) :=
      Real.sqrt_nonneg _
    have hRHS_nn : 0 ≤ Real.sqrt (g.inner x ((G : M → E) x) ((G : M → E) x)) +
        Real.sqrt (g.inner x ((G' : M → E) x) ((G' : M → E) x)) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs (Real.sqrt _),
      Real.norm_eq_abs (Real.sqrt _ + Real.sqrt _),
      abs_of_nonneg hLHS_nn, abs_of_nonneg hRHS_nn]
    exact htri
  · have h_sum_G : (fun x : M => ((G + G' : Lp E 2 (riemannianVolumeMeasure I M g)) :
          M → E) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => (G : M → E) x + (G' : M → E) x) := by
      filter_upwards [Lp.coeFn_add G G'] with x hx
      exact hx
    have hsum_pair : PairAEMeasurable (I := I) (M := M) g
        (fun x : M => (G : M → E) x + (G' : M → E) x) :=
      PairAEMeasurable.add (I := I) (M := M) (g := g) hG_pair hG'_pair
    exact PairAEMeasurable.congr_ae (I := I) (M := M) (g := g) h_sum_G.symm hsum_pair

/-- Subtraction closure of `MemH1Lp`. -/
theorem sub (g : SmoothRiemannianMetric I M)
    {u v : Lp ℝ 2 (riemannianVolumeMeasure I M g)}
    (hu : MemH1Lp (I := I) (M := M) g u)
    (hv : MemH1Lp (I := I) (M := M) g v) :
    MemH1Lp (I := I) (M := M) g (u - v) := by
  have h := add (I := I) (M := M) g hu (neg (I := I) (M := M) g hv)
  rw [show (u + -v : Lp ℝ 2 (riemannianVolumeMeasure I M g)) = u - v from by
    rw [sub_eq_add_neg]] at h
  exact h

end MemH1Lp

end IntrinsicH1Lp
end Sobolev
end Analysis
end DifferentialGeometry

end
