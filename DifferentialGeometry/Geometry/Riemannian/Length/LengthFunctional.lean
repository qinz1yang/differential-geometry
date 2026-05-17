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

/-! ### Reversal of a piecewise-`C¹` curve on `Icc 0 1` -/

/-- The reversal of a piecewise-`C¹` curve `γ` on `Icc 0 1`: the curve
`t ↦ γ (1 - t)` is also piecewise-`C¹` on `Icc 0 1`. -/
theorem IsPiecewiseC1On.reverse_unitInterval
    {γ : ℝ → M} (hγ : IsPiecewiseC1On (I := I) γ (Set.Icc (0:ℝ) 1)) :
    IsPiecewiseC1On (I := I) (fun t : ℝ => γ (1 - t)) (Set.Icc (0:ℝ) 1) := by
  classical
  obtain ⟨L, hL_sorted, hL_mem, hL_pieces⟩ := hγ
  -- Use the reversed and shifted partition `L.reverse.map (1 - ·)`.
  refine ⟨L.reverse.map (fun x => 1 - x), ?_, ?_, ?_⟩
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

end Length
end Riemannian
end Geometry
end DifferentialGeometry

end
