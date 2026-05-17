import DifferentialGeometry.Geometry.Riemannian.Geodesic.Velocity
import DifferentialGeometry.Geometry.Riemannian.Geodesic.ConstantSpeed
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Intrinsic
import DifferentialGeometry.Metric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousOn

set_option linter.unusedSectionVars false

/-!
# Length functional for curves on a Riemannian manifold

For a smooth Riemannian manifold `(M, g)` and a curve `γ : ℝ → M`, this file
defines the *speed*

```
speed g γ t = √(g(γ̇(t), γ̇(t)))
```

and the *length functional*

```
length g γ a b = ∫_a^b speed g γ t dt.
```

The principal API consists of the speed being nonneg, the length on `a ≤ b`
being nonneg, the degenerate-interval and constant-curve identities, and the
splitting identity `length γ a c = length γ a b + length γ b c` for `a ≤ b ≤ c`
when `γ` is `C¹`.

A predicate `IsPiecewiseC1On γ s` is also defined: existence of a finite
sorted partition of `s` such that on every adjacent sub-interval `γ` is `C¹`.
This is the natural regularity hypothesis under which the length functional
extends from the smooth class to piecewise-smooth curves.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Length

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-! ## Speed function -/

/-- The speed of a curve `γ` at time `t` with respect to a smooth Riemannian
metric `g`: the `g`-norm of the intrinsic velocity. -/
def speed (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) : ℝ :=
  Real.sqrt (g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t))

@[simp] lemma speed_def (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    speed (I := I) g γ t =
      Real.sqrt (g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t)) :=
  rfl

/-- The squared speed equals the metric pairing of the velocity with itself.
This is the relationship to `speedSq` used by the constant-speed development. -/
lemma speed_sq_eq (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    (speed (I := I) g γ t) ^ 2 =
      g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t) := by
  classical
  have hnn : 0 ≤ g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t) := by
    by_cases hv : velocity (I := I) γ t = 0
    · rw [hv]
      have hmap : g.inner (γ t) (0 : TangentSpace I (γ t)) =
          (0 : TangentSpace I (γ t) →L[ℝ] ℝ) := map_zero _
      rw [hmap]; rfl
    · exact le_of_lt (g.pos (γ t) _ hv)
  unfold speed
  rw [sq]
  exact Real.mul_self_sqrt hnn

/-! ### Headline 2: speed nonneg -/

/-- The speed of a curve is nonnegative. -/
theorem speed_nonneg (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    0 ≤ speed (I := I) g γ t := by
  unfold speed
  exact Real.sqrt_nonneg _

/-! ### Headline 3: speed at constant curve -/

/-- The speed of a constant curve at any time is zero. -/
theorem speed_const (g : SmoothRiemannianMetric I M) (p : M) (t : ℝ) :
    speed (I := I) g (fun _ : ℝ => p) t = 0 := by
  classical
  unfold speed
  have hvel : velocity (I := I) (fun _ : ℝ => p) t = 0 :=
    Geodesic.velocity_const (I := I) p t
  -- Express the inner product of zero with itself as zero.
  have hzero : g.inner ((fun _ : ℝ => p) t)
        (velocity (I := I) (fun _ : ℝ => p) t)
        (velocity (I := I) (fun _ : ℝ => p) t) = 0 := by
    rw [hvel]
    have hmap : g.inner ((fun _ : ℝ => p) t) (0 : TangentSpace I p) =
        (0 : TangentSpace I p →L[ℝ] ℝ) := map_zero _
    rw [hmap]; rfl
  rw [hzero, Real.sqrt_zero]

/-! ## Continuity of speed for `C¹` curves

For `γ : ℝ → M` that is `C¹`, the intrinsic-velocity lift
`t ↦ ⟨γ t, velocity γ t⟩` is continuous (in fact `C⁰`) as a map into the
tangent bundle, and consequently `t ↦ g.inner (γ t) (velocity γ t)
(velocity γ t)` is continuous on `ℝ`. The `g`-speed `Real.sqrt` of this
inner product is therefore also continuous.

The continuity statement is used to obtain `IntervalIntegrable` for the
splitting identity `length_concat`. -/

namespace Internal

/-- For a `C¹` curve `γ`, the velocity lift `t ↦ ⟨γ t, velocity γ t⟩` is
`C⁰` as a map `ℝ → TangentBundle I M`. -/
private lemma velocityLift_contMDiff_zero_of_contMDiff_one
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent 0
      (fun t : ℝ => (⟨γ t, velocity (I := I) γ t⟩ : TangentBundle I M)) := by
  classical
  -- Express as tangentMap composed with the canonical unit-tangent section.
  rw [velocityLift_eq_tangentMap_comp (I := I) γ]
  -- `tangentMap γ` is `C⁰` because `γ` is `C¹`.
  have htm : ContMDiff 𝓘(ℝ, ℝ).tangent I.tangent 0 (tangentMap 𝓘(ℝ, ℝ) I γ) := by
    have hle : (0 : WithTop ℕ∞) + 1 ≤ 1 := by
      exact_mod_cast (by decide : (0 : ℕ∞) + 1 ≤ 1)
    exact hγ.contMDiff_tangentMap hle
  -- The canonical section is `C^∞`, downgrade to `C⁰`.
  have hsec : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent 0 realUnitTangentSection :=
    realUnitTangentSection_contMDiff.of_le
      (by exact_mod_cast (le_top : (0 : ℕ∞) ≤ ⊤))
  exact htm.comp hsec

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Continuity (`C⁰`) of `t ↦ g.inner (γ t) (V t) (W t)` for two continuous
sections `V, W` of the tangent bundle along `γ`. -/
private lemma contMDiff_g_inner_aux_zero
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M}
    {v w : ∀ t : ℝ, TangentSpace I (γ t)}
    (hv : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) 0
      (fun t : ℝ => (⟨γ t, v t⟩ : TangentBundle I M)))
    (hw : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) 0
      (fun t : ℝ => (⟨γ t, w t⟩ : TangentBundle I M))) :
    Continuous (fun t : ℝ => g.inner (γ t) (v t) (w t)) := by
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := ContMDiff.inner_bundle (n := (0 : WithTop ℕ∞))
    (F := E) (B := M) (E := (TangentSpace I : M → Type _))
    (b := fun t => γ t) (v := v) (w := w) hv hw
  have h_cont : Continuous (fun t : ℝ => Inner.inner ℝ (v t) (w t)) := h.continuous
  refine h_cont.congr ?_
  intro t
  rfl

/-- Continuity of the squared speed of a `C¹` curve. -/
private lemma speed_sq_continuous
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    Continuous (fun t : ℝ =>
      g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t)) := by
  have hVel := velocityLift_contMDiff_zero_of_contMDiff_one (I := I) hγ
  exact contMDiff_g_inner_aux_zero (I := I) g hVel hVel

end Internal

/-- The speed of a `C¹` curve is continuous in `t`. -/
theorem speed_continuous
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    Continuous (speed (I := I) g γ) := by
  have hsq := Internal.speed_sq_continuous (I := I) g hγ
  -- `speed = Real.sqrt ∘ (squared speed)`.
  exact Real.continuous_sqrt.comp hsq

/-- Interval-integrability of the speed of a `C¹` curve. -/
theorem speed_intervalIntegrable
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    IntervalIntegrable (speed (I := I) g γ) MeasureTheory.volume a b :=
  (speed_continuous (I := I) g hγ).intervalIntegrable a b

/-! ## Length functional -/

/-- ### Headline 4: length functional

The Riemannian length of a curve segment `γ |_{[a,b]}`: the integral of the
speed over the parametrising interval. -/
def length (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, speed (I := I) g γ t

@[simp] lemma length_def (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    length (I := I) g γ a b = ∫ t in a..b, speed (I := I) g γ t := rfl

/-! ### Headline 5: length is nonneg on `a ≤ b` -/

/-- For `a ≤ b`, the length of `γ` over `[a, b]` is nonnegative. The proof
uses pointwise nonnegativity of the speed and `intervalIntegral.integral_nonneg`,
so no regularity hypothesis on `γ` is needed at the pointwise integral level.
The `ContMDiff` hypothesis on `γ` is retained for uniformity with `length_concat`
and to keep the API headline matching the standard formulation. -/
theorem length_nonneg [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} (_hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ length (I := I) g γ a b := by
  unfold length
  refine intervalIntegral.integral_nonneg hab ?_
  intro u _
  exact speed_nonneg (I := I) g γ u

/-! ### Headline 6: length on degenerate interval -/

/-- The length of a curve over the degenerate interval `[a, a]` is zero. -/
theorem length_self (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a : ℝ) :
    length (I := I) g γ a a = 0 := by
  unfold length
  exact intervalIntegral.integral_same

/-! ### Headline 7: orientation-reversed length

Per the standard convention of `intervalIntegral`, the integral over `[a, b]`
agrees with the negation of the integral over `[b, a]`. Since the speed is
nonnegative, both `length g γ a b` and `length g γ b a` are typically not
both nonneg unless they are both zero; the identity below captures the
orientation-flip behaviour. -/

/-- Swapping the bounds of `length` flips the sign, by the convention of
`intervalIntegral`. -/
theorem length_swap (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    length (I := I) g γ a b = - length (I := I) g γ b a := by
  unfold length
  -- `integral_symm a b : ∫ x in b..a, f x = - ∫ x in a..b, f x`
  have h := intervalIntegral.integral_symm (μ := MeasureTheory.volume)
    (f := speed (I := I) g γ) a b
  -- `h : ∫ x in b..a, speed g γ x = - ∫ x in a..b, speed g γ x`
  linarith

/-! ### Headline 8: length splits over a midpoint -/

/-- The length splits over a midpoint: for `a ≤ b ≤ c` and a `C¹` curve `γ`,
`length γ a c = length γ a b + length γ b c`. -/
theorem length_concat [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b c : ℝ) (_hab : a ≤ b) (_hbc : b ≤ c) :
    length (I := I) g γ a c =
      length (I := I) g γ a b + length (I := I) g γ b c := by
  unfold length
  have hab_int : IntervalIntegrable (speed (I := I) g γ) MeasureTheory.volume a b :=
    speed_intervalIntegrable (I := I) g hγ a b
  have hbc_int : IntervalIntegrable (speed (I := I) g γ) MeasureTheory.volume b c :=
    speed_intervalIntegrable (I := I) g hγ b c
  exact (intervalIntegral.integral_add_adjacent_intervals hab_int hbc_int).symm

/-! ### Headline 9: constant curve has zero length -/

/-- The length of a constant curve is zero on every interval. -/
theorem length_const (g : SmoothRiemannianMetric I M) (p : M) (a b : ℝ) :
    length (I := I) g (fun _ : ℝ => p) a b = 0 := by
  unfold length
  have hint : ∫ t in a..b, speed (I := I) g (fun _ : ℝ => p) t = ∫ _ in a..b, (0 : ℝ) := by
    refine intervalIntegral.integral_congr ?_
    intro u _
    exact speed_const (I := I) g p u
  rw [hint]
  simp [intervalIntegral.integral_zero]

/-! ## Piecewise-`C¹` predicate

The predicate `IsPiecewiseC1On γ s` asserts the existence of a finite sorted
list of breakpoints in `s` such that on every adjacent sub-interval
`Icc tᵢ tᵢ₊₁`, the curve `γ` is `C¹` (manifold `ContMDiffOn`).

This is the natural regularity hypothesis under which the length functional
extends from `C¹` curves to piecewise-`C¹` curves: by additivity of the
interval integral over a finite partition, the length is the sum of the
lengths of the smooth pieces. -/

/-- The list of adjacent pairs `(xᵢ, xᵢ₊₁)` of a list. -/
private def adjacentPairs : List ℝ → List (ℝ × ℝ)
  | [] => []
  | [_] => []
  | x :: y :: rest => (x, y) :: adjacentPairs (y :: rest)

/-- A curve `γ` is *piecewise `C¹` on* `s` if there exists a finite sorted
list of breakpoints in `s` so that on every adjacent sub-interval determined
by consecutive breakpoints, `γ` is `C¹` (in the manifold sense). -/
def IsPiecewiseC1On (γ : ℝ → M) (s : Set ℝ) : Prop :=
  ∃ partition : List ℝ,
    partition.Pairwise (· ≤ ·) ∧
    (∀ pt ∈ partition, pt ∈ s) ∧
    (∀ adj ∈ adjacentPairs partition,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (s ∩ Set.Icc adj.1 adj.2))

/-! ### Stability of piecewise-`C¹` -/

/-- A `C¹` curve on `Icc a b` is piecewise-`C¹` on `Icc a b`. -/
theorem IsPiecewiseC1On.of_contMDiffOn
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b)) :
    IsPiecewiseC1On (I := I) γ (Set.Icc a b) := by
  classical
  refine ⟨[a, b], ?_, ?_, ?_⟩
  · -- The two-element list `[a, b]` is pairwise (· ≤ ·) by `hab`.
    refine List.Pairwise.cons ?_ (List.pairwise_singleton (· ≤ ·) b)
    intro c hc
    rcases List.mem_singleton.mp hc with rfl
    exact hab
  · intro pt hpt
    rcases List.mem_cons.mp hpt with rfl | hpt'
    · exact Set.left_mem_Icc.mpr hab
    rcases List.mem_singleton.mp hpt' with rfl
    exact Set.right_mem_Icc.mpr hab
  · intro adj hadj
    -- `adjacentPairs [a, b] = [(a, b)]`.
    have hpairs : adjacentPairs [a, b] = [(a, b)] := rfl
    rw [hpairs] at hadj
    rcases List.mem_singleton.mp hadj with rfl
    -- `adj.1 = a`, `adj.2 = b`, so the intersection is `Icc a b ∩ Icc a b = Icc a b`.
    have hsub : Set.Icc a b ∩ Set.Icc a b = Set.Icc a b := by
      ext x; simp [Set.mem_Icc]
    rw [hsub]
    exact hγ

/-- The constant curve is piecewise-`C¹` on any set. -/
theorem IsPiecewiseC1On.const (p : M) (s : Set ℝ) :
    IsPiecewiseC1On (I := I) (fun _ : ℝ => p) s := by
  classical
  refine ⟨[], ?_, ?_, ?_⟩
  · exact List.Pairwise.nil
  · intro pt hpt
    cases hpt
  · intro adj hadj
    -- `adjacentPairs [] = []`.
    have hpairs : adjacentPairs ([] : List ℝ) = [] := rfl
    rw [hpairs] at hadj
    cases hadj

/-! ### Length is well-defined for piecewise-`C¹` curves on `[a, b]`

The integrability of `speed g γ` on each smooth piece, combined with
`intervalIntegral.integral_add_adjacent_intervals`, yields integrability of
the speed over the whole interval `[a, b]`. We do not formalise this fully
here; the definition `length` already integrates over `[a, b]` directly via
the Lebesgue integral, and `intervalIntegral.integral_nonneg` /
`intervalIntegral.integral_same` apply unconditionally. -/

end Length
end Riemannian
end Geometry
end DifferentialGeometry

end
