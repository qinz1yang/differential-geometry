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
def adjacentPairs : List ℝ → List (ℝ × ℝ)
  | [] => []
  | [_] => []
  | x :: y :: rest => (x, y) :: adjacentPairs (y :: rest)

@[simp] lemma adjacentPairs_nil : adjacentPairs [] = [] := rfl
@[simp] lemma adjacentPairs_singleton (x : ℝ) : adjacentPairs [x] = [] := rfl
@[simp] lemma adjacentPairs_cons_cons (x y : ℝ) (rest : List ℝ) :
    adjacentPairs (x :: y :: rest) = (x, y) :: adjacentPairs (y :: rest) := rfl

/-- Adjacent pairs commute with mapping a function over the list. -/
lemma adjacentPairs_map (f : ℝ → ℝ) (L : List ℝ) :
    adjacentPairs (L.map f) = (adjacentPairs L).map (Prod.map f f) := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y rest =>
      -- `(x :: y :: rest).map f = f x :: f y :: rest.map f`.
      change adjacentPairs (f x :: f y :: rest.map f) =
          (adjacentPairs (x :: y :: rest)).map (Prod.map f f)
      rw [adjacentPairs_cons_cons, adjacentPairs_cons_cons, List.map_cons]
      -- Now reduce `adjacentPairs (f y :: rest.map f)` via IH applied to `y :: rest`.
      have h : adjacentPairs ((y :: rest).map f) =
          (adjacentPairs (y :: rest)).map (Prod.map f f) := ih
      change (f x, f y) :: adjacentPairs (f y :: rest.map f) =
          (Prod.map f f (x, y)) :: ((adjacentPairs (y :: rest)).map (Prod.map f f))
      have h2 : (y :: rest).map f = f y :: rest.map f := by simp
      rw [h2] at h
      rw [h]
      rfl

/-- Auxiliary: if `L` is non-empty, then
`adjacentPairs (L ++ [y, x]) = adjacentPairs (L ++ [y]) ++ [(y, x)]`. -/
lemma adjacentPairs_append_two_cons_nonempty (L : List ℝ) (y x : ℝ) (hL : L ≠ []) :
    adjacentPairs (L ++ [y, x]) = adjacentPairs (L ++ [y]) ++ [(y, x)] := by
  induction L with
  | nil => exact (hL rfl).elim
  | cons a L' ih =>
    cases L' with
    | nil =>
      -- `L = [a]`, so the lhs is `adjacentPairs [a, y, x] = (a, y) :: adjacentPairs [y, x] = [(a, y), (y, x)]`,
      -- and the rhs is `adjacentPairs [a, y] ++ [(y, x)] = [(a, y)] ++ [(y, x)] = [(a, y), (y, x)]`.
      simp [adjacentPairs_cons_cons]
    | cons b L'' =>
      -- `L = a :: b :: L''`, then `adjacentPairs (a :: b :: L'' ++ [y, x]) = (a, b) :: adjacentPairs (b :: L'' ++ [y, x])`.
      have h1 : a :: b :: L'' ++ [y, x] = a :: (b :: L'' ++ [y, x]) := by simp
      have h2 : a :: b :: L'' ++ [y] = a :: (b :: L'' ++ [y]) := by simp
      have hL'_ne : b :: L'' ≠ [] := by simp
      simp only [h1, h2]
      have hib := ih hL'_ne
      -- Now we need `adjacentPairs (a :: (b :: L'' ++ [y, x])) =
      --   adjacentPairs (a :: (b :: L'' ++ [y])) ++ [(y, x)]`.
      -- Both sides start with `(a, b)`.
      have hl : adjacentPairs (a :: (b :: L'' ++ [y, x])) =
          (a, b) :: adjacentPairs (b :: L'' ++ [y, x]) := by
        simp [adjacentPairs_cons_cons]
      have hr : adjacentPairs (a :: (b :: L'' ++ [y])) =
          (a, b) :: adjacentPairs (b :: L'' ++ [y]) := by
        simp [adjacentPairs_cons_cons]
      rw [hl, hr, hib]
      simp

/-- Adjacent pairs of a reversed list: reverse the list of pairs and swap each
pair. -/
lemma adjacentPairs_reverse (L : List ℝ) :
    adjacentPairs L.reverse = ((adjacentPairs L).map Prod.swap).reverse := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y rest =>
      -- `(x :: y :: rest).reverse = rest.reverse ++ [y, x]`.
      have h_rev : (x :: y :: rest).reverse = rest.reverse ++ [y, x] := by
        simp [List.reverse_cons]
      rw [h_rev]
      -- Adjacent pairs of `rest.reverse ++ [y, x]`. We do a manual case split on `rest`.
      cases h_rest_cases : rest with
      | nil =>
        -- `rest.reverse = []`, so the list is `[y, x]`.
        simp [adjacentPairs_cons_cons]
      | cons z rest' =>
        -- After `cases h_rest_cases : rest with ... | cons z rest' =>`,
        -- `rest` in the goal has been substituted to `z :: rest'`.
        -- The IH `ih` still mentions `rest`, but we can use `h_rest_cases` to rewrite.
        have h_rev_ne : (z :: rest').reverse ≠ [] := by simp
        rw [adjacentPairs_append_two_cons_nonempty (L := (z :: rest').reverse)
          (y := y) (x := x) h_rev_ne]
        -- Use IH at `y :: rest = y :: z :: rest'`.
        have h_ih_at_y_rest : adjacentPairs (y :: rest).reverse =
            ((adjacentPairs (y :: rest)).map Prod.swap).reverse := ih
        rw [h_rest_cases] at h_ih_at_y_rest
        -- Now `h_ih_at_y_rest : adjacentPairs (y :: z :: rest').reverse = ...`.
        have h_y_rest_rev : (y :: z :: rest').reverse = (z :: rest').reverse ++ [y] := by
          simp [List.reverse_cons]
        rw [h_y_rest_rev] at h_ih_at_y_rest
        rw [h_ih_at_y_rest]
        simp [adjacentPairs_cons_cons, Prod.swap]

/-- A curve `γ` is *piecewise `C¹` on* `s` if it is continuous on `s` and
there exists a finite sorted list of breakpoints in `s` whose adjacent
sub-intervals cover `s`, and on each of which `γ` is `C¹` (in the manifold
sense).

The continuity-on-`s` conjunct rules out discontinuous-curve abuse, and the
covering conjunct rules out the empty-partition abuse: together they make
the predicate vacuity-free on intervals `s = Icc a b`. -/
def IsPiecewiseC1On (γ : ℝ → M) (s : Set ℝ) : Prop :=
  ContinuousOn γ s ∧
  ∃ partition : List ℝ,
    partition.Pairwise (· ≤ ·) ∧
    (∀ pt ∈ partition, pt ∈ s) ∧
    (s ⊆ ⋃ adj ∈ adjacentPairs partition, Set.Icc adj.1 adj.2) ∧
    (∀ adj ∈ adjacentPairs partition,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (s ∩ Set.Icc adj.1 adj.2))

/-! ### Stability of piecewise-`C¹` -/

/-- A `C¹` curve on `Icc a b` is piecewise-`C¹` on `Icc a b`. -/
theorem IsPiecewiseC1On.of_contMDiffOn
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b)) :
    IsPiecewiseC1On (I := I) γ (Set.Icc a b) := by
  classical
  refine ⟨hγ.continuousOn, [a, b], ?_, ?_, ?_, ?_⟩
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
  · -- Coverage: `Icc a b ⊆ ⋃ p ∈ [(a,b)], Icc p.1 p.2 = Icc a b`.
    intro x hx
    simp only [Set.mem_iUnion]
    refine ⟨(a, b), ?_, hx⟩
    exact List.mem_singleton.mpr rfl
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

/-- The constant curve is piecewise-`C¹` on `Icc a b` whenever `a ≤ b`. -/
theorem IsPiecewiseC1On.const_Icc (p : M) {a b : ℝ} (hab : a ≤ b) :
    IsPiecewiseC1On (I := I) (fun _ : ℝ => p) (Set.Icc a b) := by
  classical
  refine ⟨continuousOn_const, [a, b], ?_, ?_, ?_, ?_⟩
  · refine List.Pairwise.cons ?_ (List.pairwise_singleton (· ≤ ·) b)
    intro c hc
    rcases List.mem_singleton.mp hc with rfl
    exact hab
  · intro pt hpt
    rcases List.mem_cons.mp hpt with rfl | hpt'
    · exact Set.left_mem_Icc.mpr hab
    rcases List.mem_singleton.mp hpt' with rfl
    exact Set.right_mem_Icc.mpr hab
  · intro x hx
    simp only [Set.mem_iUnion]
    refine ⟨(a, b), ?_, hx⟩
    exact List.mem_singleton.mpr rfl
  · intro adj hadj
    have hpairs : adjacentPairs [a, b] = [(a, b)] := rfl
    rw [hpairs] at hadj
    rcases List.mem_singleton.mp hadj with rfl
    exact contMDiffOn_const

/-! ### Length is well-defined for piecewise-`C¹` curves on `[a, b]`

The integrability of `speed g γ` on each smooth piece, combined with
`intervalIntegral.integral_add_adjacent_intervals`, yields integrability of
the speed over the whole interval `[a, b]`. We do not formalise this fully
here; the definition `length` already integrates over `[a, b]` directly via
the Lebesgue integral, and `intervalIntegral.integral_nonneg` /
`intervalIntegral.integral_same` apply unconditionally. -/

/-! ### Reversal of a piecewise-`C¹` curve on `Icc 0 1` -/

/-- The reversal of a piecewise-`C¹` curve `γ` on `Icc 0 1`: the curve
`t ↦ γ (1 - t)` is also piecewise-`C¹` on `Icc 0 1`. -/
theorem IsPiecewiseC1On.reverse_unitInterval
    {γ : ℝ → M} (hγ : IsPiecewiseC1On (I := I) γ (Set.Icc (0:ℝ) 1)) :
    IsPiecewiseC1On (I := I) (fun t : ℝ => γ (1 - t)) (Set.Icc (0:ℝ) 1) := by
  classical
  obtain ⟨hγ_cont, L, hL_sorted, hL_mem, hL_cov, hL_pieces⟩ := hγ
  -- Continuity of `t ↦ γ (1 - t)` on `Icc 0 1`: pre-compose with the continuous
  -- map `t ↦ 1 - t` whose image of `Icc 0 1` lies in `Icc 0 1`.
  have h_one_sub_cont : Continuous (fun t : ℝ => 1 - t) := by continuity
  have h_image_subset_unit : Set.MapsTo (fun t : ℝ => 1 - t)
      (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := by
    intro t ht
    rcases ht with ⟨h0, h1⟩
    refine ⟨?_, ?_⟩ <;> linarith
  have hγ_rev_cont : ContinuousOn (fun t : ℝ => γ (1 - t)) (Set.Icc (0:ℝ) 1) := by
    refine hγ_cont.comp (h_one_sub_cont.continuousOn) ?_
    exact h_image_subset_unit
  refine ⟨hγ_rev_cont, L.reverse.map (fun x => 1 - x), ?_, ?_, ?_, ?_⟩
  · -- Sorted property: `L` is sorted increasing, `L.reverse` is decreasing,
    -- mapping `1 - ·` flips the order back to increasing.
    rw [List.pairwise_map]
    have h_rev_pw : L.reverse.Pairwise (fun a b => b ≤ a) := hL_sorted.reverse
    exact h_rev_pw.imp (by intros a b h; linarith)
  · -- Membership in `Icc 0 1`: if `pt = 1 - q` with `q ∈ L ⊆ Icc 0 1`, then `pt ∈ Icc 0 1`.
    intro pt hpt
    rw [List.mem_map] at hpt
    obtain ⟨q, hq_mem, rfl⟩ := hpt
    rw [List.mem_reverse] at hq_mem
    have hq_in := hL_mem q hq_mem
    rw [Set.mem_Icc] at hq_in ⊢
    refine ⟨?_, ?_⟩ <;> linarith [hq_in.1, hq_in.2]
  · -- Coverage: for each `s ∈ Icc 0 1`, `1 - s ∈ Icc 0 1` is covered by some
    -- adjacent pair `(a, b)` of `L`, hence `s ∈ Icc (1 - b) (1 - a)` lies in
    -- the reversed-mapped pair `(1 - b, 1 - a)` which arises in
    -- `adjacentPairs (L.reverse.map (1 - ·))`.
    intro s hs
    rcases hs with ⟨hs0, hs1⟩
    have h_1s : (1 - s) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have h_cov_1s := hL_cov h_1s
    simp only [Set.mem_iUnion] at h_cov_1s
    obtain ⟨pair_set, h_pair_in_adj, h_in_pair⟩ := h_cov_1s
    -- Now construct the corresponding pair `(1 - pair_set.2, 1 - pair_set.1)`
    -- in `adjacentPairs (L.reverse.map (1 - ·))`.
    simp only [Set.mem_iUnion]
    refine ⟨(1 - pair_set.2, 1 - pair_set.1), ?_, ?_⟩
    · -- Membership: apply `adjacentPairs_map` and `adjacentPairs_reverse`.
      rw [adjacentPairs_map, adjacentPairs_reverse]
      rw [List.mem_map]
      refine ⟨pair_set.swap, ?_, ?_⟩
      · rw [List.mem_reverse, List.mem_map]
        refine ⟨pair_set, h_pair_in_adj, ?_⟩
        rfl
      · simp [Prod.swap, Prod.map]
    · -- Coverage point.
      rcases h_in_pair with ⟨h_lo, h_hi⟩
      refine ⟨?_, ?_⟩ <;> simp <;> linarith
  · -- Pieces: every adjacent pair `(a', b')` of the reverse-mapped partition
    -- corresponds to a reversed adjacent pair `(b, a)` of `L`.
    intro adj hadj
    -- `adjacentPairs (L.reverse.map (1 - ·)) =
    --   (adjacentPairs L.reverse).map (Prod.map (1-·) (1-·))
    --  = ((adjacentPairs L).map Prod.swap).reverse.map (Prod.map (1-·) (1-·))`.
    rw [adjacentPairs_map, adjacentPairs_reverse] at hadj
    rw [List.mem_map] at hadj
    obtain ⟨swapped, h_swap_mem, h_swap_eq⟩ := hadj
    -- `swapped` is in `((adjacentPairs L).map Prod.swap).reverse = (adjacentPairs L).map Prod.swap`
    -- (as a set, `reverse` and `id` have same membership).
    rw [List.mem_reverse, List.mem_map] at h_swap_mem
    obtain ⟨orig, h_orig_mem, h_orig_eq⟩ := h_swap_mem
    -- `orig = (a, b)` in `adjacentPairs L`, `swapped = (b, a)`, so
    -- `adj = Prod.map (1-·) (1-·) (b, a) = (1 - b, 1 - a)`.
    -- Use `hL_pieces` to know `γ` is `C¹` on `Icc 0 1 ∩ Icc a b`.
    have h_piece := hL_pieces orig h_orig_mem
    -- Express `Icc 0 1 ∩ Icc adj.1 adj.2` as `(1 - ·) ⁻¹' (Icc 0 1 ∩ Icc orig.1 orig.2)`.
    -- That is, `s ∈ Icc 0 1 ∩ Icc adj.1 adj.2 ↔ (1 - s) ∈ Icc 0 1 ∩ Icc orig.1 orig.2`.
    have h_adj_proj : adj = (1 - orig.2, 1 - orig.1) := by
      rw [← h_swap_eq, ← h_orig_eq]
      simp [Prod.map, Prod.swap]
    rw [h_adj_proj]
    -- Now we need: `ContMDiffOn 𝓘(ℝ,ℝ) I 1 (fun t => γ (1-t)) (Icc 0 1 ∩ Icc (1-orig.2) (1-orig.1))`.
    -- Use composition: `(fun t => γ (1-t)) = γ ∘ (1-·)`.
    have h_one_sub_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun s : ℝ => 1 - s) := by
      refine (?_ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ _).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
      exact (contMDiff_const).sub contMDiff_id
    have h_one_sub_on : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun s : ℝ => 1 - s)
        (Set.Icc (0:ℝ) 1 ∩ Set.Icc (1 - orig.2) (1 - orig.1)) :=
      h_one_sub_smooth.contMDiffOn
    -- Show that the image of `Icc 0 1 ∩ Icc (1-orig.2) (1-orig.1)` under `(1-·)` lies in
    -- `Icc 0 1 ∩ Icc orig.1 orig.2`.
    have h_image_subset :
        (Set.Icc (0:ℝ) 1 ∩ Set.Icc (1 - orig.2) (1 - orig.1)) ⊆
          (fun s : ℝ => 1 - s) ⁻¹' (Set.Icc (0:ℝ) 1 ∩ Set.Icc orig.1 orig.2) := by
      rintro x ⟨hx01, hx_int⟩
      rw [Set.mem_Icc] at hx01 hx_int
      rw [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hx01.1, hx01.2, hx_int.1, hx_int.2]
    -- Now `(γ ∘ (1-·))` is `C^1` on the set.
    have h_comp : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ (fun s : ℝ => 1 - s))
        (Set.Icc (0:ℝ) 1 ∩ Set.Icc (1 - orig.2) (1 - orig.1)) :=
      h_piece.comp h_one_sub_on h_image_subset
    exact h_comp

/-! ### Concatenation of two piecewise-`C¹` curves at `t = 1/2`

For `γ₁, γ₂ : ℝ → M`, the *concatenated curve at the half-way mark* is
`fun t => if t ≤ 1/2 then γ₁ (2 * t) else γ₂ (2 * t - 1)`. This is
piecewise-`C¹` on `Icc 0 1` provided each of `γ₁` and `γ₂` is, with the
midpoint matching `γ₁ 1 = γ₂ 0`. -/

/-- Concatenation of two curves on the unit interval at the midpoint. -/
def concatHalf (γ₁ γ₂ : ℝ → M) (t : ℝ) : M :=
  if t ≤ (1/2 : ℝ) then γ₁ (2 * t) else γ₂ (2 * t - 1)

@[simp] lemma concatHalf_zero (γ₁ γ₂ : ℝ → M) :
    concatHalf (M := M) γ₁ γ₂ 0 = γ₁ 0 := by
  unfold concatHalf; simp

@[simp] lemma concatHalf_one (γ₁ γ₂ : ℝ → M) :
    concatHalf (M := M) γ₁ γ₂ 1 = γ₂ 1 := by
  unfold concatHalf; simp; norm_num

/-! ### Affine reparametrization helpers

Let `φ_a(t) = c * t + d`. We record the manifold-derivative of `φ_a` (it is
multiplication by `c` as a CLM `ℝ →L[ℝ] ℝ`) and the resulting chain rule for
`velocity (γ ∘ φ_a)` and `speed (γ ∘ φ_a)`. -/

namespace Internal

/-- The manifold derivative of `t ↦ c * t + d` is multiplication by `c`
(seen as a CLM `ℝ →L[ℝ] ℝ`). -/
private lemma mfderiv_affine (c d t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => c * s + d) t =
      c • (ContinuousLinearMap.id ℝ ℝ) := by
  have hd : HasDerivAt (fun s : ℝ => c * s + d) c t := by
    simpa using ((hasDerivAt_id t).const_mul c).add_const d
  have h_fd : HasFDerivAt (fun s : ℝ => c * s + d)
      (ContinuousLinearMap.toSpanSingleton ℝ c) t :=
    hd.hasFDerivAt
  have hfd : fderiv ℝ (fun s : ℝ => c * s + d) t =
      ContinuousLinearMap.toSpanSingleton ℝ c := h_fd.fderiv
  rw [mfderiv_eq_fderiv, hfd]
  ext
  simp [ContinuousLinearMap.toSpanSingleton_apply]

/-- The intrinsic velocity of the affine reparametrization `t ↦ γ (c * t + d)`
at `t`, when `γ` is mdifferentiable at `c * t + d`. -/
private lemma velocity_affine_reparam
    {γ : ℝ → M} {c d t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (c * t + d)) :
    Geodesic.velocity (I := I) (fun s : ℝ => γ (c * s + d)) t =
      c • (Geodesic.velocity (I := I) γ (c * t + d) :
        TangentSpace I (γ (c * t + d))) := by
  classical
  set φ : ℝ → ℝ := fun s : ℝ => c * s + d
  have hφ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ⊤ φ := by
    exact ((contMDiff_const).mul contMDiff_id).add contMDiff_const
  have hφ_md : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t :=
    hφ_smooth.mdifferentiable (by simp [ne_eq]) t
  have h_comp_eq : γ ∘ φ = fun s : ℝ => γ (c * s + d) := by funext s; rfl
  have h_chain : mfderiv 𝓘(ℝ, ℝ) I (γ ∘ φ) t =
      (mfderiv 𝓘(ℝ, ℝ) I γ (φ t)).comp (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t) :=
    mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I) (x := t)
      (by simpa [φ] using hγ) hφ_md
  have h_φd := mfderiv_affine c d t
  unfold Geodesic.velocity
  rw [← h_comp_eq, h_chain, h_φd]
  change (mfderiv 𝓘(ℝ, ℝ) I γ (c * t + d))
      ((c • (ContinuousLinearMap.id ℝ ℝ)) (1 : ℝ)) =
    c • (mfderiv 𝓘(ℝ, ℝ) I γ (c * t + d)) (1 : ℝ)
  -- The CLM applied to `c • 1 = c`.
  have h_clm_smul :
      ((c • (ContinuousLinearMap.id ℝ ℝ)) : ℝ →L[ℝ] ℝ) (1 : ℝ) = c := by
    simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul]
  rw [h_clm_smul]
  -- Now: `mfderiv γ (c*t+d) c = c • mfderiv γ (c*t+d) 1`.
  -- Use ContinuousLinearMap.map_smul: `L (c • v) = c • L v`. We need to rewrite
  -- `c` as `c • 1` on the LHS only.
  have h_target : (mfderiv 𝓘(ℝ, ℝ) I γ (c * t + d)) c =
      c • (mfderiv 𝓘(ℝ, ℝ) I γ (c * t + d)) (1 : ℝ) := by
    have h_eq : (c : ℝ) = c • (1 : ℝ) := by rw [smul_eq_mul, mul_one]
    calc (mfderiv 𝓘(ℝ, ℝ) I γ (c * t + d)) c
        = (mfderiv 𝓘(ℝ, ℝ) I γ (c * t + d)) (c • (1 : ℝ)) := by
          rw [← h_eq]
      _ = c • (mfderiv 𝓘(ℝ, ℝ) I γ (c * t + d)) (1 : ℝ) :=
          ContinuousLinearMap.map_smul _ c (1 : ℝ)
  exact h_target

end Internal

/-- Squared speed transforms via `c²` under the affine reparametrization
`t ↦ γ (c * t + d)`, when `γ` is mdifferentiable at `c * t + d`. -/
private lemma speedSq_affine_reparam
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {c d t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (c * t + d)) :
    g.inner ((fun s : ℝ => γ (c * s + d)) t)
        (Geodesic.velocity (I := I) (fun s : ℝ => γ (c * s + d)) t)
        (Geodesic.velocity (I := I) (fun s : ℝ => γ (c * s + d)) t) =
      (c * c) *
        g.inner (γ (c * t + d))
          (Geodesic.velocity (I := I) γ (c * t + d))
          (Geodesic.velocity (I := I) γ (c * t + d)) := by
  classical
  have h_pt : (fun s : ℝ => γ (c * s + d)) t = γ (c * t + d) := rfl
  have h_vel := Internal.velocity_affine_reparam (I := I) hγ
  rw [h_pt, h_vel]
  -- Now: `g.inner _ (c • v) (c • v) = c * c * g.inner _ v v`.
  have h_sm₁ : g.inner (γ (c * t + d))
        (c • (Geodesic.velocity (I := I) γ (c * t + d) :
          TangentSpace I (γ (c * t + d)))) =
      c • g.inner (γ (c * t + d))
        (Geodesic.velocity (I := I) γ (c * t + d)) := by
    exact (g.inner (γ (c * t + d))).map_smul c _
  rw [h_sm₁]
  -- Now: `(c • g.inner _ v) (c • v) = c * ((g.inner _ v)(c • v))`.
  -- For a CLM `L : V →L[ℝ] ℝ`, `(c • L) v = c * L v`, and `L (c • v) = c • L v`.
  change (c • g.inner (γ (c * t + d))
        (Geodesic.velocity (I := I) γ (c * t + d)))
        (c • (Geodesic.velocity (I := I) γ (c * t + d) :
          TangentSpace I (γ (c * t + d)))) =
    c * c * (g.inner (γ (c * t + d))
        (Geodesic.velocity (I := I) γ (c * t + d)))
        (Geodesic.velocity (I := I) γ (c * t + d))
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.map_smul]
  simp only [smul_eq_mul]
  ring

/-- Speed transforms via `|c|` under the affine reparametrization
`t ↦ γ (c * t + d)`. -/
private lemma speed_affine_reparam
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {c d t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (c * t + d)) :
    speed (I := I) g (fun s : ℝ => γ (c * s + d)) t =
      |c| * speed (I := I) g γ (c * t + d) := by
  classical
  unfold speed
  have h_sq := speedSq_affine_reparam (I := I) g hγ
  -- `√(c² * x) = |c| * √x` for `x ≥ 0`.
  have h_pt : (fun s : ℝ => γ (c * s + d)) t = γ (c * t + d) := rfl
  rw [h_pt]
  rw [h_sq]
  rw [show (c * c : ℝ) = c^2 by ring, ← sq_abs c,
    Real.sqrt_mul (sq_nonneg _)]
  rw [Real.sqrt_sq (abs_nonneg c)]

/-- Affine reparametrization `t ↦ c * t + d` is a diffeomorphism when `c ≠ 0`,
in particular the chain-rule criterion shows mdifferentiability of `γ ∘ (c·+d)`
at `t` is equivalent to mdifferentiability of `γ` at `c * t + d`. -/
private lemma mdifferentiableAt_reparam_iff
    {γ : ℝ → M} {c d t : ℝ} (hc : c ≠ 0) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ (c * s + d)) t ↔
      MDifferentiableAt 𝓘(ℝ, ℝ) I γ (c * t + d) := by
  classical
  set φ : ℝ → ℝ := fun s : ℝ => c * s + d with hφ_def
  have hφ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ⊤ φ :=
    ((contMDiff_const).mul contMDiff_id).add contMDiff_const
  have hφ_md : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t :=
    hφ_smooth.mdifferentiable (by simp [ne_eq]) t
  -- The inverse `ψ s = (s - d)/c`. With `hc : c ≠ 0`, `ψ` is smooth.
  set ψ : ℝ → ℝ := fun s : ℝ => (s - d)/c with hψ_def
  have hψ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ⊤ ψ := by
    have hsmooth_sub : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ⊤ (fun s : ℝ => s - d) :=
      contMDiff_id.sub contMDiff_const
    have h_div : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ⊤ (fun s : ℝ => s / c) := by
      have h_mul_const : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ⊤ (fun s : ℝ => s * c⁻¹) :=
        contMDiff_id.mul contMDiff_const
      simpa [div_eq_mul_inv] using h_mul_const
    exact h_div.comp hsmooth_sub
  have hψ_md : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ψ (c * t + d) :=
    hψ_smooth.mdifferentiable (by simp [ne_eq]) (c * t + d)
  have h_ψ_apply : ψ (c * t + d) = t := by
    simp [ψ]
    field_simp
  refine ⟨fun h_left => ?_, fun h_right => ?_⟩
  · -- From mdifferentiability of `fun s => γ(c*s+d)` at `t`,
    -- compose with `ψ` to get mdifferentiability of `γ` at `c*t+d = φ t`.
    have h_comp_eq : (fun s : ℝ => γ (c * s + d)) ∘ ψ = γ := by
      funext s
      change γ (c * ((s - d)/c) + d) = γ s
      have : c * ((s - d)/c) + d = s := by field_simp; ring
      rw [this]
    have h_comp_md := MDifferentiableAt.comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I)
      (g := fun s : ℝ => γ (c * s + d)) (f := ψ) (x := c * t + d)
      (by rw [h_ψ_apply]; exact h_left) hψ_md
    rw [h_comp_eq] at h_comp_md
    exact h_comp_md
  · -- From mdifferentiability of γ at `c*t+d`, compose with φ.
    have h_comp_eq : γ ∘ φ = fun s : ℝ => γ (c * s + d) := by funext; rfl
    have h_comp_md := MDifferentiableAt.comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I)
      (g := γ) (f := φ) (x := t) (by simpa [φ] using h_right) hφ_md
    rw [h_comp_eq] at h_comp_md
    exact h_comp_md

/-- Unconditional speed identity for the affine reparametrization
`t ↦ γ (c * t + d)`, valid for ALL `t` (using the convention that
`velocity` is zero at non-mdifferentiable points). -/
lemma speed_reparam_unconditional
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (c d t : ℝ) :
    speed (I := I) g (fun s : ℝ => γ (c * s + d)) t =
      |c| * speed (I := I) g γ (c * t + d) := by
  classical
  by_cases hc : c = 0
  · -- `c = 0` case: `fun s => γ(0*s + d) = fun s => γ d` is constant, speed = 0.
    -- `|0| * _ = 0`.
    subst hc
    simp only [zero_mul, zero_add, abs_zero, zero_mul]
    -- Now LHS = speed g (fun s => γ d) t.
    -- This is a constant curve in `M`, so velocity = 0, speed = 0.
    exact speed_const (I := I) g (γ d) t
  · by_cases h : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (c * t + d)
    · exact speed_affine_reparam (I := I) g h
    · -- Not mdifferentiable: both sides equal 0.
      have h_not_left : ¬ MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ (c * s + d)) t := by
        rw [mdifferentiableAt_reparam_iff (I := I) hc]
        exact h
      have h_vel_γ : Geodesic.velocity (I := I) γ (c * t + d) = 0 :=
        Geodesic.velocity_eq_zero_of_not_mdifferentiable (I := I) h
      have h_vel : Geodesic.velocity (I := I) (fun s : ℝ => γ (c * s + d)) t = 0 :=
        Geodesic.velocity_eq_zero_of_not_mdifferentiable (I := I) h_not_left
      unfold speed
      rw [h_vel, h_vel_γ]
      -- Goal: `Real.sqrt (g.inner ((fun s => γ(c*s+d)) t) 0 0) = |c| * Real.sqrt (g.inner (γ(c*t+d)) 0 0)`.
      have h_pt : (fun s : ℝ => γ (c * s + d)) t = γ (c * t + d) := rfl
      rw [h_pt]
      have h0' : g.inner (γ (c * t + d)) (0 : TangentSpace I _) =
          (0 : TangentSpace I _ →L[ℝ] ℝ) := map_zero _
      rw [h0']
      change Real.sqrt 0 = |c| * Real.sqrt 0
      rw [Real.sqrt_zero]; ring

/-! ### Length under affine reparametrization

For a positive scaling `a > 0` and arbitrary shift `b`, the affine
reparametrization `t ↦ γ (a * t + b)` preserves the length: integrating the
speed over the new domain `[c, d]` agrees with integrating the speed of the
original `γ` over the rescaled domain `[a*c + b, a*d + b]`. Specialisations
to pure translation, pure reflection, and unit-interval reversal follow. -/

/-- Length under an affine reparametrization `t ↦ γ (a * t + b)` with positive
scaling `a`. The integration domain rescales accordingly. -/
theorem length_affine_reparam [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    {a : ℝ} (ha : 0 < a) (b c d : ℝ) :
    length (I := I) g (fun t => γ (a * t + b)) c d =
      length (I := I) g γ (a * c + b) (a * d + b) := by
  classical
  unfold length
  -- Step 1: rewrite the LHS integrand using `speed_reparam_unconditional`.
  have h_int_eq :
      (∫ t in c..d, speed (I := I) g (fun s => γ (a * s + b)) t) =
        ∫ t in c..d, a * speed (I := I) g γ (a * t + b) := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    have h := speed_reparam_unconditional (I := I) g γ a b t
    rw [h, abs_of_pos ha]
  rw [h_int_eq]
  -- Step 2: pull out the constant `a`.
  rw [intervalIntegral.integral_const_mul a (fun t => speed (I := I) g γ (a * t + b))]
  -- Step 3: change of variable, using `intervalIntegral.integral_comp_mul_add`.
  have ha_ne : a ≠ 0 := ne_of_gt ha
  rw [intervalIntegral.integral_comp_mul_add (f := speed (I := I) g γ) ha_ne b]
  -- Goal: a * (a⁻¹ • ∫ x in a*c+b..a*d+b, speed g γ x) = ∫ x in a*c+b..a*d+b, ...
  rw [smul_eq_mul]
  rw [← mul_assoc]
  rw [mul_inv_cancel₀ ha_ne]
  ring

/-- Length under a pure time translation `t ↦ γ (t + b)`. The integration
domain shifts by `b`. -/
theorem length_comp_add [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (b c d : ℝ) :
    length (I := I) g (fun t => γ (t + b)) c d =
      length (I := I) g γ (c + b) (d + b) := by
  classical
  unfold length
  -- Speed of the shifted curve at `t` equals speed of `γ` at `t + b`.
  have h_speed_pt : ∀ t : ℝ,
      speed (I := I) g (fun s => γ (s + b)) t = speed (I := I) g γ (t + b) := by
    intro t
    have h := speed_reparam_unconditional (I := I) g γ 1 b t
    -- `h : speed (fun s => γ(1*s + b)) t = |1| * speed γ (1*t + b)`.
    simp only [one_mul, abs_one, one_mul] at h
    exact h
  -- Rewrite the integrand.
  have h_int_eq :
      (∫ t in c..d, speed (I := I) g (fun s => γ (s + b)) t) =
        ∫ t in c..d, speed (I := I) g γ (t + b) := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    exact h_speed_pt t
  rw [h_int_eq]
  -- Apply `intervalIntegral.integral_comp_add_right` to shift the interval.
  exact intervalIntegral.integral_comp_add_right (f := speed (I := I) g γ) b

/-- Length under time reflection `t ↦ γ (-t)`. The integration domain flips
sign and reverses orientation. -/
theorem length_reverse [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    length (I := I) g (fun t => γ (-t)) (-b) (-a) =
      length (I := I) g γ a b := by
  classical
  unfold length
  -- Speed of `fun t => γ(-t)` at `t` equals `|-1| * speed γ (-t) = speed γ (-t)`.
  have h_speed_pt : ∀ t : ℝ,
      speed (I := I) g (fun s => γ (-s)) t = speed (I := I) g γ (-t) := by
    intro t
    have h := speed_reparam_unconditional (I := I) g γ (-1) 0 t
    -- `h : speed (fun s => γ((-1)*s + 0)) t = |-1| * speed γ ((-1)*t + 0)`.
    have h_neg_one : |(-1 : ℝ)| = 1 := by
      rw [abs_neg, abs_one]
    rw [h_neg_one] at h
    simp only [neg_one_mul, add_zero, one_mul] at h
    exact h
  -- Rewrite the integrand.
  have h_int_eq :
      (∫ t in (-b)..(-a), speed (I := I) g (fun s => γ (-s)) t) =
        ∫ t in (-b)..(-a), speed (I := I) g γ (-t) := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    exact h_speed_pt t
  rw [h_int_eq]
  -- `intervalIntegral.integral_comp_neg : ∫ x in a..b, f (-x) = ∫ x in -b..-a, f x`.
  have h_neg := intervalIntegral.integral_comp_neg
    (f := speed (I := I) g γ) (a := -b) (b := -a)
  -- `h_neg : ∫ x in -b..-a, f (-x) = ∫ x in -(-a)..-(-b), f x = ∫ x in a..b, f x`.
  rw [h_neg]
  simp only [neg_neg]

/-- Length under unit-interval reversal `t ↦ γ (1 - t)`, integrated over
`[0, 1]`. The reversed curve has the same length. -/
theorem length_unit_reverse [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    length (I := I) g (fun t => γ (1 - t)) 0 1 =
      length (I := I) g γ 0 1 := by
  classical
  unfold length
  -- Speed of `fun t => γ(1 - t)` at `t` equals `speed γ (1 - t)`.
  have h_speed_pt : ∀ t : ℝ,
      speed (I := I) g (fun s => γ (1 - s)) t = speed (I := I) g γ (1 - t) := by
    intro t
    -- `1 - s = (-1) * s + 1`, so apply `speed_reparam_unconditional` with `c = -1, d = 1`.
    have h := speed_reparam_unconditional (I := I) g γ (-1) 1 t
    have h_neg_one : |(-1 : ℝ)| = 1 := by
      rw [abs_neg, abs_one]
    rw [h_neg_one] at h
    -- Massage `(-1) * s + 1 = 1 - s` and `(-1) * t + 1 = 1 - t`.
    have h_fun : (fun s : ℝ => γ ((-1) * s + 1)) = (fun s : ℝ => γ (1 - s)) := by
      funext s; congr 1; ring
    have h_pt : ((-1 : ℝ) * t + 1) = 1 - t := by ring
    rw [h_fun, h_pt] at h
    rw [one_mul] at h
    exact h
  -- Rewrite the integrand.
  have h_int_eq :
      (∫ t in (0:ℝ)..1, speed (I := I) g (fun s => γ (1 - s)) t) =
        ∫ t in (0:ℝ)..1, speed (I := I) g γ (1 - t) := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    exact h_speed_pt t
  rw [h_int_eq]
  -- `intervalIntegral.integral_comp_sub_left : ∫ x in a..b, f (d - x) = ∫ x in d - b..d - a, f x`.
  have h_sub := intervalIntegral.integral_comp_sub_left
    (f := speed (I := I) g γ) (a := (0 : ℝ)) (b := 1) 1
  -- `h_sub : ∫ x in 0..1, f (1 - x) = ∫ x in 1 - 1..1 - 0, f x`.
  rw [h_sub]
  -- `1 - 1 = 0` and `1 - 0 = 1`.
  simp

/-! ### `concatHalf` agrees piecewise with each half on its half

Identifying `concatHalf γ₁ γ₂` as `fun s => γ₁ (2 * s)` on the open interval
`Iio (1/2)` (where the `if`-condition holds and the value is `γ₁ (2 * s)`),
and as `fun s => γ₂ (2 * s - 1)` on `Ioi (1/2)`, lets us reduce the
speed and velocity of `concatHalf` to those of the affinely reparametrized
halves on the appropriate open intervals (hence almost everywhere on the
closed halves `Icc 0 (1/2)` and `Icc (1/2) 1`). -/

/-- `concatHalf γ₁ γ₂` agrees with `fun s => γ₁ (2 * s)` strictly to the left
of `1/2`. -/
lemma concatHalf_eq_left {γ₁ γ₂ : ℝ → M} {t : ℝ} (ht : t < (1/2 : ℝ)) :
    concatHalf (M := M) γ₁ γ₂ t = γ₁ (2 * t) := by
  unfold concatHalf
  rw [if_pos (le_of_lt ht)]

/-- `concatHalf γ₁ γ₂` agrees with `fun s => γ₂ (2 * s - 1)` strictly to the
right of `1/2`. -/
lemma concatHalf_eq_right {γ₁ γ₂ : ℝ → M} {t : ℝ} (ht : (1/2 : ℝ) < t) :
    concatHalf (M := M) γ₁ γ₂ t = γ₂ (2 * t - 1) := by
  unfold concatHalf
  rw [if_neg (not_le.mpr ht)]

/-- `concatHalf γ₁ γ₂` agrees with `fun s => γ₁ (2 * s)` on `Icc 0 (1/2)`. -/
lemma concatHalf_eq_left_on_Icc {γ₁ γ₂ : ℝ → M} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (1/2)) :
    concatHalf (M := M) γ₁ γ₂ t = γ₁ (2 * t) := by
  unfold concatHalf
  rw [if_pos ht.2]

/-- `concatHalf γ₁ γ₂` agrees with `fun s => γ₂ (2 * s - 1)` on `Icc (1/2) 1`
provided the matching condition `γ₁ 1 = γ₂ 0` at the midpoint. -/
lemma concatHalf_eq_right_on_Icc {γ₁ γ₂ : ℝ → M}
    (h_match : γ₁ 1 = γ₂ 0) {t : ℝ}
    (ht : t ∈ Set.Icc ((1/2 : ℝ)) 1) :
    concatHalf (M := M) γ₁ γ₂ t = γ₂ (2 * t - 1) := by
  rcases eq_or_lt_of_le ht.1 with h12 | h12
  · -- `t = 1/2`.
    rw [← h12]
    unfold concatHalf
    rw [if_pos (le_refl _)]
    -- LHS = γ₁ (2 * (1/2)) = γ₁ 1, RHS = γ₂ (2 * (1/2) - 1) = γ₂ 0.
    have hL : γ₁ ((2 : ℝ) * (1/2)) = γ₁ 1 := by norm_num
    have hR : γ₂ ((2 : ℝ) * (1/2) - 1) = γ₂ 0 := by norm_num
    rw [hL, hR]
    exact h_match
  · -- `t > 1/2`.
    exact concatHalf_eq_right h12

/-! ### Continuity of `concatHalf` from continuity of each half

When `γ₁` is continuous on `Icc 0 1` and `γ₂` is continuous on `Icc 0 1` and
the matching condition `γ₁ 1 = γ₂ 0` holds, then `concatHalf γ₁ γ₂` is
continuous on `Icc 0 1`. -/

/-- Continuity of `concatHalf γ₁ γ₂` on `Icc 0 1`, given continuity of the two
halves on `Icc 0 1` and the midpoint-matching condition. -/
lemma concatHalf_continuousOn {γ₁ γ₂ : ℝ → M}
    (hγ₁ : ContinuousOn γ₁ (Set.Icc (0:ℝ) 1))
    (hγ₂ : ContinuousOn γ₂ (Set.Icc (0:ℝ) 1))
    (h_match : γ₁ 1 = γ₂ 0) :
    ContinuousOn (concatHalf (M := M) γ₁ γ₂) (Set.Icc (0:ℝ) 1) := by
  classical
  -- Continuity on each closed half.
  have h_aff_left : Continuous (fun s : ℝ => (2 : ℝ) * s) := by continuity
  have h_aff_right : Continuous (fun s : ℝ => (2 : ℝ) * s - 1) := by continuity
  have h_image_left : Set.MapsTo (fun s : ℝ => (2 : ℝ) * s)
      (Set.Icc (0:ℝ) (1/2)) (Set.Icc (0:ℝ) 1) := by
    intro s hs
    rcases hs with ⟨h0, h1⟩
    refine ⟨?_, ?_⟩ <;> linarith
  have h_image_right : Set.MapsTo (fun s : ℝ => (2 : ℝ) * s - 1)
      (Set.Icc ((1/2):ℝ) 1) (Set.Icc (0:ℝ) 1) := by
    intro s hs
    rcases hs with ⟨h0, h1⟩
    refine ⟨?_, ?_⟩ <;> linarith
  have h_left_cont : ContinuousOn (fun s : ℝ => γ₁ (2 * s)) (Set.Icc (0:ℝ) (1/2)) :=
    hγ₁.comp h_aff_left.continuousOn h_image_left
  have h_right_cont : ContinuousOn (fun s : ℝ => γ₂ (2 * s - 1))
      (Set.Icc ((1/2):ℝ) 1) :=
    hγ₂.comp h_aff_right.continuousOn h_image_right
  -- `concatHalf γ₁ γ₂` agrees with the left function on `Icc 0 (1/2)` and the
  -- right function on `Icc (1/2) 1`.
  have h_concat_left :
      ContinuousOn (concatHalf (M := M) γ₁ γ₂) (Set.Icc (0:ℝ) (1/2)) := by
    refine h_left_cont.congr ?_
    intro s hs
    exact concatHalf_eq_left_on_Icc (γ₂ := γ₂) hs
  have h_concat_right :
      ContinuousOn (concatHalf (M := M) γ₁ γ₂) (Set.Icc ((1/2):ℝ) 1) := by
    refine h_right_cont.congr ?_
    intro s hs
    exact concatHalf_eq_right_on_Icc (γ₁ := γ₁) h_match hs
  -- Combine on `Icc 0 1 = Icc 0 (1/2) ∪ Icc (1/2) 1`.
  have h_union : Set.Icc (0:ℝ) 1 = Set.Icc (0:ℝ) (1/2) ∪ Set.Icc ((1/2):ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨h0, h1⟩
      by_cases h : x ≤ 1/2
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨le_of_not_ge h, h1⟩
    · rintro (⟨h0, h⟩ | ⟨h, h1⟩)
      · exact ⟨h0, by linarith⟩
      · exact ⟨by linarith, h1⟩
  rw [h_union]
  -- Continuity on a union of two closed sets follows from continuity on each,
  -- using that both are closed in the union.
  refine ContinuousOn.union_of_isClosed ?_ ?_ ?_ ?_
  · exact h_concat_left
  · exact h_concat_right
  · exact isClosed_Icc
  · exact isClosed_Icc

/-! ### Piecewise-`C¹` of `concatHalf` -/

/-- The first reparametrization `fun t => γ (2 * t)` is `C¹` on
`Icc 0 (1/2) ∩ Icc (a/2) (b/2)` whenever `γ` is `C¹` on `Icc 0 1 ∩ Icc a b`,
where `0 ≤ a ≤ b ≤ 1`. -/
private lemma firstHalf_contMDiffOn_aux
    {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc (0:ℝ) 1 ∩ Set.Icc a b)) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun s : ℝ => γ (2 * s))
      (Set.Icc (0:ℝ) (1/2) ∩ Set.Icc (a/2) (b/2)) := by
  classical
  have h_aff_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun s : ℝ => (2 : ℝ) * s) := by
    refine (?_ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ _).of_le
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    exact contMDiff_const.mul contMDiff_id
  have h_image : (Set.Icc (0:ℝ) (1/2) ∩ Set.Icc (a/2) (b/2)) ⊆
      (fun s : ℝ => (2 : ℝ) * s) ⁻¹' (Set.Icc (0:ℝ) 1 ∩ Set.Icc a b) := by
    rintro x ⟨hx01, hxab⟩
    rcases hx01 with ⟨hx0, hx1⟩
    rcases hxab with ⟨hxa, hxb⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  exact hγ.comp h_aff_smooth.contMDiffOn h_image

/-- The second reparametrization `fun t => γ (2 * t - 1)` is `C¹` on
`Icc (1/2) 1 ∩ Icc ((a+1)/2) ((b+1)/2)` whenever `γ` is `C¹` on
`Icc 0 1 ∩ Icc a b`, where `0 ≤ a ≤ b ≤ 1`. -/
private lemma secondHalf_contMDiffOn_aux
    {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc (0:ℝ) 1 ∩ Set.Icc a b)) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun s : ℝ => γ (2 * s - 1))
      (Set.Icc ((1/2):ℝ) 1 ∩ Set.Icc ((a + 1)/2) ((b + 1)/2)) := by
  classical
  have h_aff_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun s : ℝ => (2 : ℝ) * s - 1) := by
    refine (?_ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ _).of_le
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    exact (contMDiff_const.mul contMDiff_id).sub contMDiff_const
  have h_image : (Set.Icc ((1/2):ℝ) 1 ∩ Set.Icc ((a + 1)/2) ((b + 1)/2)) ⊆
      (fun s : ℝ => (2 : ℝ) * s - 1) ⁻¹' (Set.Icc (0:ℝ) 1 ∩ Set.Icc a b) := by
    rintro x ⟨hx01, hxab⟩
    rcases hx01 with ⟨hx0, hx1⟩
    rcases hxab with ⟨hxa, hxb⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  exact hγ.comp h_aff_smooth.contMDiffOn h_image

/-! ### Structural facts about `adjacentPairs` and partition endpoints -/

/-- An element appearing in `adjacentPairs L` is the first or second component
of one of the adjacent pairs; both components lie in `L`. -/
private lemma fst_mem_of_mem_adjacentPairs : ∀ {L : List ℝ} {adj : ℝ × ℝ},
    adj ∈ adjacentPairs L → adj.1 ∈ L := by
  intro L
  induction L with
  | nil => intro adj hadj; simp at hadj
  | cons x L' ih =>
    cases L' with
    | nil => intro adj hadj; simp at hadj
    | cons y rest =>
      intro adj hadj
      rw [adjacentPairs_cons_cons, List.mem_cons] at hadj
      rcases hadj with hadj | hadj
      · subst hadj; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hadj)

private lemma snd_mem_of_mem_adjacentPairs : ∀ {L : List ℝ} {adj : ℝ × ℝ},
    adj ∈ adjacentPairs L → adj.2 ∈ L := by
  intro L
  induction L with
  | nil => intro adj hadj; simp at hadj
  | cons x L' ih =>
    cases L' with
    | nil => intro adj hadj; simp at hadj
    | cons y rest =>
      intro adj hadj
      rw [adjacentPairs_cons_cons, List.mem_cons] at hadj
      rcases hadj with hadj | hadj
      · subst hadj
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hadj)

/-- Decomposition of `adjacentPairs` over a list-append, when both lists are
non-empty. -/
private lemma adjacentPairs_append_nonempty {A B : List ℝ}
    (hA : A ≠ []) (hB : B ≠ []) :
    adjacentPairs (A ++ B) =
      adjacentPairs A ++ (A.getLast hA, B.head hB) :: adjacentPairs B := by
  induction A with
  | nil => exact (hA rfl).elim
  | cons x A' ih =>
    cases A' with
    | nil =>
      -- A = [x], so A ++ B = x :: B. We split on B.
      cases B with
      | nil => exact (hB rfl).elim
      | cons y B' =>
        -- A ++ B = x :: y :: B'. adjacentPairs starts with (x, y), then recurses on y :: B'.
        rw [List.singleton_append, adjacentPairs_cons_cons]
        rfl
    | cons z A'' =>
      -- A = x :: z :: A''. So A ++ B = x :: (z :: A'' ++ B).
      have hA'_ne : (z :: A'') ≠ [] := by simp
      -- Build the IH application separately.
      have h_ih : adjacentPairs ((z :: A'') ++ B) =
          adjacentPairs (z :: A'') ++
            ((z :: A'').getLast hA'_ne, B.head hB) :: adjacentPairs B :=
        ih hA'_ne
      change adjacentPairs (x :: (z :: A'' ++ B)) =
        adjacentPairs (x :: z :: A'') ++
          (List.getLast (x :: z :: A'') hA, List.head B hB) ::
          adjacentPairs B
      have heq1 : (z :: A'' ++ B) = z :: (A'' ++ B) := by simp
      rw [heq1, adjacentPairs_cons_cons, adjacentPairs_cons_cons]
      -- `(x :: z :: A'').getLast hA = (z :: A'').getLast hA'_ne`.
      have h_getLast : (x :: z :: A'').getLast hA = (z :: A'').getLast hA'_ne := by
        rw [List.getLast_cons hA'_ne]
      rw [h_getLast]
      -- Need: (x, z) :: adjacentPairs (z :: (A'' ++ B)) = (x, z) :: adjacentPairs (z :: A'') ++ (...) :: adjacentPairs B
      -- Now: ((x,z) :: adjacentPairs (z :: A'')) ++ (...) :: ... = (x,z) :: (adjacentPairs (z :: A'') ++ (...) :: ...).
      -- z :: (A'' ++ B) = (z :: A'') ++ B definitionally.
      change (x, z) :: adjacentPairs ((z :: A'') ++ B) =
        ((x, z) :: adjacentPairs (z :: A'')) ++
          ((z :: A'').getLast hA'_ne, B.head hB) :: adjacentPairs B
      rw [h_ih]
      rfl

/-- The last element of any partition witness for
`IsPiecewiseC1On γ (Icc 0 1)` is `1`. -/
private lemma getLast_eq_one_of_isPiecewiseC1On_unit
    {γ : ℝ → M} (hγ : IsPiecewiseC1On (I := I) γ (Set.Icc (0:ℝ) 1)) :
    ∃ L : List ℝ, ∃ hne : L ≠ [],
      L.Pairwise (· ≤ ·) ∧ (∀ pt ∈ L, pt ∈ Set.Icc (0:ℝ) 1) ∧
      (Set.Icc (0:ℝ) 1 ⊆ ⋃ adj ∈ adjacentPairs L, Set.Icc adj.1 adj.2) ∧
      (∀ adj ∈ adjacentPairs L,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc (0:ℝ) 1 ∩ Set.Icc adj.1 adj.2)) ∧
      L.getLast hne = 1 ∧ L.head hne = 0 := by
  classical
  obtain ⟨_, L, hL_sorted, hL_mem, hL_cov, hL_pieces⟩ := hγ
  -- The list `L` must be non-empty (since coverage at `0` requires an adj pair).
  have hL_ne : L ≠ [] := by
    rintro rfl
    have h0_in : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
    have h_uni := hL_cov h0_in
    simp only [adjacentPairs_nil, Set.mem_iUnion, List.not_mem_nil] at h_uni
    obtain ⟨_, ⟨_, _⟩, _⟩ := h_uni
  -- Get coverage at `1`.
  have h1_in : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have h_cov_1 := hL_cov h1_in
  simp only [Set.mem_iUnion] at h_cov_1
  obtain ⟨pair, h_pair_in, h_1_in_pair⟩ := h_cov_1
  rcases h_1_in_pair with ⟨h_pair1_le_1, h_1_le_pair2⟩
  -- `pair.2 ∈ L`, so `pair.2 ≤ 1` by hL_mem. Combined with `1 ≤ pair.2`: `pair.2 = 1`.
  have h_pair2_in_L := snd_mem_of_mem_adjacentPairs h_pair_in
  have h_pair2_in_Icc := hL_mem pair.2 h_pair2_in_L
  rcases h_pair2_in_Icc with ⟨_, h_pair2_le_1⟩
  have h_pair2_eq_1 : pair.2 = 1 := le_antisymm h_pair2_le_1 h_1_le_pair2
  -- By the pairwise-(· ≤ ·) property, `pair.2 ≤ getLast L hL_ne`.
  -- More precisely: every element of L is ≤ getLast L hL_ne (when L is sorted).
  have h_last_le_1 : L.getLast hL_ne ≤ 1 := by
    exact (hL_mem (L.getLast hL_ne) (List.getLast_mem hL_ne)).2
  have h_pair2_le_last : pair.2 ≤ L.getLast hL_ne := by
    have h := hL_sorted.rel_getLast h_pair2_in_L
    -- `h : pair.2 ≤ L.getLast _` with the proof obligation `ne_nil_of_mem h_pair2_in_L`.
    -- Convert to use `hL_ne`.
    convert h using 1
  have h_last_eq_1 : L.getLast hL_ne = 1 := by
    rw [h_pair2_eq_1] at h_pair2_le_last
    exact le_antisymm h_last_le_1 h_pair2_le_last
  -- Similarly, head L hne = 0.
  have h_cov_0 := hL_cov ⟨le_refl 0, zero_le_one⟩
  simp only [Set.mem_iUnion] at h_cov_0
  obtain ⟨pair0, h_pair0_in, h_0_in_pair0⟩ := h_cov_0
  rcases h_0_in_pair0 with ⟨h_pair01_le_0, h_0_le_pair02⟩
  have h_pair01_in_L := fst_mem_of_mem_adjacentPairs h_pair0_in
  have h_pair01_in_Icc := hL_mem pair0.1 h_pair01_in_L
  rcases h_pair01_in_Icc with ⟨h_pair01_ge_0, _⟩
  have h_pair01_eq_0 : pair0.1 = 0 := le_antisymm h_pair01_le_0 h_pair01_ge_0
  have h_head_ge_0 : 0 ≤ L.head hL_ne :=
    (hL_mem (L.head hL_ne) (List.head_mem hL_ne)).1
  have h_head_le_pair01 : L.head hL_ne ≤ pair0.1 := by
    have h := hL_sorted.rel_head h_pair01_in_L
    convert h using 1
  have h_head_eq_0 : L.head hL_ne = 0 := by
    rw [h_pair01_eq_0] at h_head_le_pair01
    exact le_antisymm h_head_le_pair01 h_head_ge_0
  refine ⟨L, hL_ne, hL_sorted, hL_mem, hL_cov, hL_pieces, h_last_eq_1, h_head_eq_0⟩

/-- Piecewise-`C¹` concatenation: given piecewise-`C¹` curves `γ₁, γ₂` on
`Icc 0 1` with matching midpoint `γ₁ 1 = γ₂ 0`, their concatenation
`concatHalf γ₁ γ₂` is piecewise-`C¹` on `Icc 0 1`. -/
theorem isPiecewiseC1On_concatHalf
    {γ₁ γ₂ : ℝ → M}
    (hγ₁ : IsPiecewiseC1On (I := I) γ₁ (Set.Icc (0:ℝ) 1))
    (hγ₂ : IsPiecewiseC1On (I := I) γ₂ (Set.Icc (0:ℝ) 1))
    (h_match : γ₁ 1 = γ₂ 0) :
    IsPiecewiseC1On (I := I) (concatHalf (M := M) γ₁ γ₂)
      (Set.Icc (0:ℝ) 1) := by
  classical
  have hγ₁_cont : ContinuousOn γ₁ (Set.Icc (0:ℝ) 1) := hγ₁.1
  have hγ₂_cont : ContinuousOn γ₂ (Set.Icc (0:ℝ) 1) := hγ₂.1
  obtain ⟨L₁, hL₁_ne, hL₁_sorted, hL₁_mem, hL₁_cov, hL₁_pieces, hL₁_last, hL₁_head⟩ :=
    getLast_eq_one_of_isPiecewiseC1On_unit (I := I) hγ₁
  obtain ⟨L₂, hL₂_ne, hL₂_sorted, hL₂_mem, hL₂_cov, hL₂_pieces, hL₂_last, hL₂_head⟩ :=
    getLast_eq_one_of_isPiecewiseC1On_unit (I := I) hγ₂
  -- Use the partition `L₁.map (·/2) ++ L₂.map ((·+1)/2)`. Since `last L₁ = 1` and
  -- `head L₂ = 0`, the cross adjacent pair is `(1/2, 1/2)`, degenerate.
  set f₁ : ℝ → ℝ := fun x => x / 2 with hf₁_def
  set f₂ : ℝ → ℝ := fun x => (x + 1) / 2 with hf₂_def
  set L : List ℝ := (L₁.map f₁) ++ (L₂.map f₂) with hL_def
  -- Useful facts:
  have hL₁_map_ne : L₁.map f₁ ≠ [] := fun h => hL₁_ne (List.map_eq_nil_iff.mp h)
  have hL₂_map_ne : L₂.map f₂ ≠ [] := fun h => hL₂_ne (List.map_eq_nil_iff.mp h)
  have hL₁_map_last : (L₁.map f₁).getLast hL₁_map_ne = 1/2 := by
    rw [List.getLast_map, hL₁_last]
  have hL₂_map_head : (L₂.map f₂).head hL₂_map_ne = 1/2 := by
    rw [List.head_map, hL₂_head]
    change ((0 : ℝ) + 1) / 2 = 1/2
    norm_num
  refine ⟨concatHalf_continuousOn hγ₁_cont hγ₂_cont h_match, L, ?_, ?_, ?_, ?_⟩
  · -- Sorted.
    refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact hL₁_sorted.imp (fun {a b} h => by simp [f₁]; linarith)
    · rw [List.pairwise_map]
      exact hL₂_sorted.imp (fun {a b} h => by simp [f₂]; linarith)
    · intro a ha b hb
      rw [List.mem_map] at ha hb
      obtain ⟨a', ha'_mem, rfl⟩ := ha
      obtain ⟨b', hb'_mem, rfl⟩ := hb
      have ha'_in := hL₁_mem a' ha'_mem
      have hb'_in := hL₂_mem b' hb'_mem
      simp only [f₁, f₂]
      linarith [ha'_in.2, hb'_in.1]
  · -- Membership in `Icc 0 1`.
    intro pt hpt
    rw [List.mem_append] at hpt
    rcases hpt with hpt₁ | hpt₂
    · rw [List.mem_map] at hpt₁
      obtain ⟨q, hq_mem, rfl⟩ := hpt₁
      have hq_in := hL₁_mem q hq_mem
      simp only [f₁]
      refine ⟨?_, ?_⟩ <;> linarith [hq_in.1, hq_in.2]
    · rw [List.mem_map] at hpt₂
      obtain ⟨q, hq_mem, rfl⟩ := hpt₂
      have hq_in := hL₂_mem q hq_mem
      simp only [f₂]
      refine ⟨?_, ?_⟩ <;> linarith [hq_in.1, hq_in.2]
  · -- Coverage.
    intro s hs
    rcases hs with ⟨hs0, hs1⟩
    by_cases h_half : s ≤ 1/2
    · -- Use `L₁` part.
      have h_2s_in : (2 * s) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
      have h_cov := hL₁_cov h_2s_in
      simp only [Set.mem_iUnion] at h_cov
      obtain ⟨pair, h_pair_in_adj, h_in_pair⟩ := h_cov
      simp only [Set.mem_iUnion]
      refine ⟨(pair.1 / 2, pair.2 / 2), ?_, ?_⟩
      · -- Adjacent pair lies in the L₁-block of L.
        rw [hL_def, adjacentPairs_append_nonempty hL₁_map_ne hL₂_map_ne]
        rw [List.mem_append]
        left
        rw [adjacentPairs_map, List.mem_map]
        exact ⟨pair, h_pair_in_adj, by simp [f₁, Prod.map]⟩
      · rcases h_in_pair with ⟨h_lo, h_hi⟩
        refine ⟨?_, ?_⟩ <;> linarith
    · push Not at h_half
      -- Use `L₂` part.
      have h_2s1_in : (2 * s - 1) ∈ Set.Icc (0:ℝ) 1 :=
        ⟨by linarith, by linarith⟩
      have h_cov := hL₂_cov h_2s1_in
      simp only [Set.mem_iUnion] at h_cov
      obtain ⟨pair, h_pair_in_adj, h_in_pair⟩ := h_cov
      simp only [Set.mem_iUnion]
      refine ⟨((pair.1 + 1) / 2, (pair.2 + 1) / 2), ?_, ?_⟩
      · rw [hL_def, adjacentPairs_append_nonempty hL₁_map_ne hL₂_map_ne]
        rw [List.mem_append, List.mem_cons]
        right; right
        rw [adjacentPairs_map, List.mem_map]
        exact ⟨pair, h_pair_in_adj, by simp [f₂, Prod.map]⟩
      · rcases h_in_pair with ⟨h_lo, h_hi⟩
        refine ⟨?_, ?_⟩ <;> linarith
  · -- Pieces.
    intro adj hadj
    rw [hL_def, adjacentPairs_append_nonempty hL₁_map_ne hL₂_map_ne] at hadj
    rw [List.mem_append, List.mem_cons] at hadj
    rcases hadj with h_left | h_cross | h_right
    · -- Left block.
      rw [adjacentPairs_map, List.mem_map] at h_left
      obtain ⟨orig, h_orig_mem, h_orig_eq⟩ := h_left
      have h_piece := hL₁_pieces orig h_orig_mem
      have h_first :=
        firstHalf_contMDiffOn_aux (I := I) (γ := γ₁)
          (a := orig.1) (b := orig.2) h_piece
      have h_adj_eq : adj = (orig.1/2, orig.2/2) := by
        rw [← h_orig_eq]; simp [f₁, Prod.map]
      rw [h_adj_eq]
      have h_orig2_in := hL₁_mem orig.2 (snd_mem_of_mem_adjacentPairs h_orig_mem)
      have h_orig2_le := h_orig2_in.2
      have h_subset_half :
          Set.Icc (0:ℝ) 1 ∩ Set.Icc (orig.1/2) (orig.2/2) ⊆
            Set.Icc (0:ℝ) (1/2) ∩ Set.Icc (orig.1/2) (orig.2/2) := by
        rintro x ⟨hx01, hxab⟩
        rcases hx01 with ⟨hx0, _⟩
        rcases hxab with ⟨hxa, hxb⟩
        refine ⟨⟨hx0, ?_⟩, hxa, hxb⟩
        linarith
      have h_first_restricted :
          ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun s : ℝ => γ₁ (2 * s))
            (Set.Icc (0:ℝ) 1 ∩ Set.Icc (orig.1/2) (orig.2/2)) :=
        h_first.mono h_subset_half
      refine h_first_restricted.congr ?_
      intro x hx
      have hx_copy := hx
      rcases hx with ⟨hx01, hxab⟩
      have hxb := hxab.2
      have h_x_half : x ≤ 1/2 := by linarith
      have h_x_in : x ∈ Set.Icc (0:ℝ) (1/2) := ⟨hx01.1, h_x_half⟩
      exact concatHalf_eq_left_on_Icc (γ₂ := γ₂) h_x_in
    · -- Cross piece: `adj = (1/2, 1/2)` after the substitutions.
      have hadj_eq : adj = ((L₁.map f₁).getLast hL₁_map_ne,
          (L₂.map f₂).head hL₂_map_ne) := h_cross
      rw [hL₁_map_last, hL₂_map_head] at hadj_eq
      rw [hadj_eq]
      -- Goal: ContMDiffOn ... (concatHalf γ₁ γ₂) (Icc 0 1 ∩ Icc (1/2) (1/2)).
      have h_set_eq : Set.Icc (0:ℝ) 1 ∩ Set.Icc ((1/2):ℝ) (1/2) = {(1/2 : ℝ)} := by
        ext x
        constructor
        · rintro ⟨_, hx2⟩
          rw [Set.mem_Icc] at hx2
          exact Set.mem_singleton_iff.mpr (le_antisymm hx2.2 hx2.1)
        · rintro hx
          rcases Set.mem_singleton_iff.mp hx with rfl
          refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> norm_num
      rw [h_set_eq]
      -- `ContMDiffOn` on a singleton: at the single point, the function agrees
      -- with the constant function `fun _ => concatHalf γ₁ γ₂ (1/2)`, which
      -- is smooth.
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      have h_const_eq : ∀ z ∈ ({(1/2 : ℝ)} : Set ℝ),
          concatHalf γ₁ γ₂ z =
            (fun _ : ℝ => concatHalf γ₁ γ₂ ((1/2 : ℝ))) z := by
        intro z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        rfl
      have h_ev_eq : concatHalf γ₁ γ₂ =ᶠ[𝓝[{(1/2 : ℝ)}] (1/2)]
          (fun _ : ℝ => concatHalf γ₁ γ₂ ((1/2 : ℝ))) :=
        Filter.eventually_of_mem self_mem_nhdsWithin h_const_eq
      exact (contMDiffWithinAt_const
        (c := concatHalf γ₁ γ₂ ((1/2 : ℝ)))).congr_of_eventuallyEq
          h_ev_eq rfl
    · -- Right block.
      rw [adjacentPairs_map, List.mem_map] at h_right
      obtain ⟨orig, h_orig_mem, h_orig_eq⟩ := h_right
      have h_piece := hL₂_pieces orig h_orig_mem
      have h_second :=
        secondHalf_contMDiffOn_aux (I := I) (γ := γ₂)
          (a := orig.1) (b := orig.2) h_piece
      have h_adj_eq : adj = ((orig.1 + 1)/2, (orig.2 + 1)/2) := by
        rw [← h_orig_eq]; simp [f₂, Prod.map]
      rw [h_adj_eq]
      have h_orig1_in := hL₂_mem orig.1 (fst_mem_of_mem_adjacentPairs h_orig_mem)
      have h_orig1_ge := h_orig1_in.1
      have h_subset_half :
          Set.Icc (0:ℝ) 1 ∩ Set.Icc ((orig.1 + 1)/2) ((orig.2 + 1)/2) ⊆
            Set.Icc ((1/2):ℝ) 1 ∩ Set.Icc ((orig.1 + 1)/2) ((orig.2 + 1)/2) := by
        rintro x ⟨hx01, hxab⟩
        rcases hx01 with ⟨_, hx1⟩
        rcases hxab with ⟨hxa, hxb⟩
        refine ⟨⟨?_, hx1⟩, hxa, hxb⟩
        linarith
      have h_second_restricted :
          ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun s : ℝ => γ₂ (2 * s - 1))
            (Set.Icc (0:ℝ) 1 ∩ Set.Icc ((orig.1 + 1)/2) ((orig.2 + 1)/2)) :=
        h_second.mono h_subset_half
      refine h_second_restricted.congr ?_
      intro x hx
      rcases hx with ⟨hx01, hxab⟩
      have hxa := hxab.1
      have h_x_half : (1/2 : ℝ) ≤ x := by linarith
      have h_x_in : x ∈ Set.Icc ((1/2):ℝ) 1 := ⟨h_x_half, hx01.2⟩
      exact concatHalf_eq_right_on_Icc (γ₁ := γ₁) h_match h_x_in

/-! ### Length additivity for `concatHalf` -/

/-- For `t < 1/2`, the velocity of `concatHalf γ₁ γ₂` at `t` equals the velocity
of the affine reparametrization `fun s => γ₁ (2 * s)` at `t`. Reason: both
functions agree on the open neighborhood `Set.Iio (1/2)` of `t`, so their
manifold derivatives at `t` coincide. -/
private lemma velocity_concatHalf_left {γ₁ γ₂ : ℝ → M} {t : ℝ}
    (ht : t < (1/2 : ℝ)) :
    Geodesic.velocity (I := I) (concatHalf (M := M) γ₁ γ₂) t =
      (Geodesic.velocity (I := I) (fun s : ℝ => γ₁ (2 * s)) t :
        TangentSpace I (γ₁ (2 * t))) := by
  classical
  have h_eq_pt : concatHalf (M := M) γ₁ γ₂ t = γ₁ (2 * t) :=
    concatHalf_eq_left ht
  -- Express both velocities as `mfderiv ... 1` and use the eventually-equal mfderiv.
  unfold Geodesic.velocity
  have h_ev : concatHalf (M := M) γ₁ γ₂ =ᶠ[𝓝 t] (fun s : ℝ => γ₁ (2 * s)) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact concatHalf_eq_left hs
  -- mfderiv depends only on the eventually-equal germ of the function.
  have h_mfderiv_eq : mfderiv 𝓘(ℝ, ℝ) I (concatHalf (M := M) γ₁ γ₂) t =
      mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γ₁ (2 * s)) t :=
    Filter.EventuallyEq.mfderiv_eq h_ev
  rw [h_mfderiv_eq]
  rfl

private lemma velocity_concatHalf_right {γ₁ γ₂ : ℝ → M} {t : ℝ}
    (ht : (1/2 : ℝ) < t) :
    Geodesic.velocity (I := I) (concatHalf (M := M) γ₁ γ₂) t =
      (Geodesic.velocity (I := I) (fun s : ℝ => γ₂ (2 * s - 1)) t :
        TangentSpace I (γ₂ (2 * t - 1))) := by
  classical
  have h_eq_pt : concatHalf (M := M) γ₁ γ₂ t = γ₂ (2 * t - 1) :=
    concatHalf_eq_right ht
  unfold Geodesic.velocity
  have h_ev : concatHalf (M := M) γ₁ γ₂ =ᶠ[𝓝 t] (fun s : ℝ => γ₂ (2 * s - 1)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact concatHalf_eq_right hs
  rw [Filter.EventuallyEq.mfderiv_eq h_ev]
  rfl

/-- Speed of `concatHalf γ₁ γ₂` at `t < 1/2` equals the speed of the affine
reparametrization `fun s => γ₁ (2 * s)`. -/
lemma speed_concatHalf_eq_left
    (g : SmoothRiemannianMetric I M) (γ₁ γ₂ : ℝ → M) {t : ℝ}
    (ht : t < (1/2 : ℝ)) :
    speed (I := I) g (concatHalf (M := M) γ₁ γ₂) t =
      speed (I := I) g (fun s : ℝ => γ₁ (2 * s)) t := by
  unfold speed
  have h_pt : concatHalf (M := M) γ₁ γ₂ t = γ₁ (2 * t) := concatHalf_eq_left ht
  rw [h_pt]
  have h_vel := velocity_concatHalf_left (I := I) (γ₁ := γ₁) (γ₂ := γ₂) ht
  rw [h_vel]

lemma speed_concatHalf_eq_right
    (g : SmoothRiemannianMetric I M) (γ₁ γ₂ : ℝ → M) {t : ℝ}
    (ht : (1/2 : ℝ) < t) :
    speed (I := I) g (concatHalf (M := M) γ₁ γ₂) t =
      speed (I := I) g (fun s : ℝ => γ₂ (2 * s - 1)) t := by
  unfold speed
  have h_pt : concatHalf (M := M) γ₁ γ₂ t = γ₂ (2 * t - 1) := concatHalf_eq_right ht
  rw [h_pt]
  have h_vel := velocity_concatHalf_right (I := I) (γ₁ := γ₁) (γ₂ := γ₂) ht
  rw [h_vel]

/-- Speed of `fun s => γ (2 * s)` equals `2 * speed γ (2 * t)`. -/
lemma speed_double_reparam
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    speed (I := I) g (fun s : ℝ => γ (2 * s)) t =
      2 * speed (I := I) g γ (2 * t) := by
  have h := speed_reparam_unconditional (I := I) g γ 2 0 t
  -- `|2| = 2`.
  simp only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  rw [show (fun s : ℝ => γ (2 * s + 0)) = (fun s : ℝ => γ (2 * s)) by funext s; ring_nf] at h
  rw [show (2 * t + 0 : ℝ) = 2 * t by ring] at h
  exact h

lemma speed_double_shift_reparam
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    speed (I := I) g (fun s : ℝ => γ (2 * s - 1)) t =
      2 * speed (I := I) g γ (2 * t - 1) := by
  have h := speed_reparam_unconditional (I := I) g γ 2 (-1) t
  simp only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  rw [show (fun s : ℝ => γ (2 * s + (-1))) = (fun s : ℝ => γ (2 * s - 1))
    by funext s; ring_nf] at h
  rw [show (2 * t + (-1) : ℝ) = 2 * t - 1 by ring] at h
  exact h

/-! ### Length of a constant-speed curve

If the speed of `γ` is the constant `c ≥ 0` on every parameter `t`, then the
length over `[a, b]` (with `a ≤ b`) is `c · (b - a)`. -/

/-- For a `C¹` curve with constant speed `c ≥ 0`, the length over `[a, b]` is
`c · (b - a)`. -/
theorem length_eq_speed_mul_of_constSpeed [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    {c : ℝ} (_hc : 0 ≤ c)
    (hSpeed : ∀ t, speed (I := I) g γ t = c) (a b : ℝ) (_hab : a ≤ b) :
    length (I := I) g γ a b = c * (b - a) := by
  unfold length
  have hcongr : ∫ t in a..b, speed (I := I) g γ t = ∫ _ in a..b, (c : ℝ) := by
    refine intervalIntegral.integral_congr ?_
    intro u _
    exact hSpeed u
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  -- `intervalIntegral.integral_const` gives `(b - a) • c`; rearrange to `c * (b - a)`.
  ring

/-! ### Length subadditivity over an arbitrary midpoint

Per `length_concat`, the length splits as an equality on `a ≤ b ≤ c`. The
corresponding `≤` direction is recorded here for callers that only need the
inequality. -/

/-- For `a ≤ b ≤ c` and a `C¹` curve `γ`, the length over `[a, c]` is bounded
above by the sum of the lengths over `[a, b]` and `[b, c]`. (In fact it is
equal — see `length_concat` — but the `≤` form is convenient in optimisation
arguments.) -/
theorem length_le_concat_split [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    length (I := I) g γ a c ≤
      length (I := I) g γ a b + length (I := I) g γ b c := by
  exact le_of_eq (length_concat (I := I) hγ a b c hab hbc)

/-! ### Length is zero when velocity vanishes identically -/

/-- If the intrinsic velocity of `γ` vanishes at every parameter, the length
over any interval is zero. -/
theorem length_of_velocity_zero [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (h_zero : ∀ t, velocity (I := I) γ t = 0) (a b : ℝ) :
    length (I := I) g γ a b = 0 := by
  classical
  unfold length
  have hspeed_zero : ∀ t, speed (I := I) g γ t = 0 := by
    intro t
    unfold speed
    have hv : velocity (I := I) γ t = 0 := h_zero t
    have hmap : g.inner (γ t) (0 : TangentSpace I (γ t)) =
        (0 : TangentSpace I (γ t) →L[ℝ] ℝ) := map_zero _
    rw [hv, hmap]
    -- The continuous linear map `0` evaluated at `0` is `0`; then `sqrt 0 = 0`.
    change Real.sqrt ((0 : TangentSpace I (γ t) →L[ℝ] ℝ) 0) = 0
    rw [ContinuousLinearMap.zero_apply, Real.sqrt_zero]
  have hcongr : ∫ t in a..b, speed (I := I) g γ t = ∫ _ in a..b, (0 : ℝ) := by
    refine intervalIntegral.integral_congr ?_
    intro u _
    exact hspeed_zero u
  rw [hcongr]
  simp [intervalIntegral.integral_zero]

/-- **Fundamental theorem of calculus for Riemannian arc length.** For a
`C¹` curve `γ` and a fixed lower endpoint `a`, the function `t ↦ length g γ a t`
is differentiable at every `t : ℝ` with derivative equal to the speed at `t`.

The speed is continuous (`speed_continuous`), so the standard `Continuous.deriv_integral`
applies directly. -/
theorem deriv_length_right
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a t : ℝ) :
    deriv (fun u : ℝ => length (I := I) g γ a u) t = speed (I := I) g γ t := by
  unfold length
  exact (speed_continuous (I := I) g hγ).deriv_integral _ _ _

/-- **Strict differentiability of the arc-length function.** As a
strengthening of `deriv_length_right`: for a `C¹` curve, the map
`t ↦ length g γ a t` has the speed at `t` as its derivative in the
strong `HasDerivAt` sense (not merely the weak `deriv`-extraction). -/
theorem hasDerivAt_length_right
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a t : ℝ) :
    HasDerivAt (fun u : ℝ => length (I := I) g γ a u)
      (speed (I := I) g γ t) t := by
  unfold length
  exact ((speed_continuous (I := I) g hγ).integral_hasStrictDerivAt a t).hasDerivAt

end Length
end Riemannian
end Geometry
end DifferentialGeometry

end
