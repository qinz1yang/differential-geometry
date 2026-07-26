import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BernsteinShiHigher
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Components

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The variable-rank iterated covariant-derivative tower `∇ᵏRm`

This file builds the **eq-7.4 derivative tower producer** for the
Bernstein–Bando–Shi estimate: for a Ricci-flow solution it supplies the tower of
curvature-derivative squared norms `w k = |∇ᵏRm|²` as rank-`(4+k)` component
arrays, so that the general-`k` `∗`-reaction bound `abs_nablaRmReactionMulti_le`
of `Evolution/NablaRiemannHeat.lean` applies and the per-level heat inequality of
`Evolution/BernsteinShiHigher.lean` (`TowerHeatBoundOn`) is produced.

It is the variable-rank bridge between

* the order-`0`/order-`1` producers (`RiemannNormHeatProducer.lean`,
  `NablaRiemannHeat.lean`), which work at the concrete ranks `4` and `5`, and
* the general-`k` maximum-principle tower (`BernsteinShiHigher.lean`), which
  consumes `w : ℕ → ℝ → M → ℝ` with the schematic heat inequality at every level.

## The three pieces (the task's three steps)

1. **The variable-rank component recursion** `iteratedRmComp`
   (`§ ComponentRecursion`).  Working entirely at the component level
   `(Fin (4+k) → Idx) → ℝ` — the array's element type is always `ℝ`, only the
   arity `4+k` varies — we define `∇ᵏRm` by recursion on `k`:
   * `k = 0` is the rank-`4` lowered Riemann component array;
   * `k+1` is the explicit frame covariant-derivative formula
     `(∇A)(d ::ₘ m) = ∂_d A(m) − Σ_slot Σ_p Γᵖ_{d,m(slot)} · A(m[slot ↦ p])`,
     the rank-uniform generalization of `ricciSecondCovDerivCompInFrame`
     (`Evolution/Connection/Components.lean`).
   The `Fin (4+(k+1)) = Fin ((4+k)+1)` arity step is handled by
   `Fin.tail`/`Function.update`, with no dependent-type recursion in the element
   type.

2. **The general orthonormal reduction** `multiNormInFrame_eq_compNormSqMulti`
   (`§ OrthonormalReduction`).  In an orthonormal frame the multi-index squared
   norm `g^{m₀n₀}···g^{mₖnₖ} Aₘ Aₙ` collapses to the plain component norm
   `compNormSqMulti A = Σₘ (A m)²`.  This is the rank-uniform generalization of
   `rm04NormSqInFrame_eq_compNormSq4` / `nablaRm04NormSqInFrame_eq_compNormSq5`.

3. **The tower heat inequality** `iteratedRmTower_heatBound`
   (`§ TowerHeatInequality`).  Packaging the Uhlenbeck time derivative `∂ₜRm`,
   the connection evolution, the Bochner Laplacian split, and the iterated
   Laplacian commutator `[∇ᵏ,Δ]A = Σⱼ ∇ʲRm ∗ ∇^{k−j}A` as component hypotheses
   (matching the `k=0`/`k=1` architecture), we discharge the reaction half with
   `abs_nablaRmReactionMulti_le` and produce the `TowerHeatBoundOn` predicate

   `(∂ₜ − Δ)(w k) ≤ −2·(w (k+1)) + Σⱼ c·√(wⱼ)·√(w_{k−j})·√(wₖ)`,  `c = 2·card^{6+k}`.

Everything algebraic is phrased in a fixed **orthonormal** frame, matching the
`InverseMetricOrthonormalAt` convention of the lower producers.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

/-! ## Variable-rank component recursion for `∇ᵏRm`

We work at the pure component level: a rank-`r` array is a function
`(Fin r → Idx) → ℝ`.  The single covariant-derivative step takes a rank-`r`
array to a rank-`(r+1)` array, prepending the derivative slot.  This is
frame-free real algebra given the directional-derivative data `ext` and the
Christoffel data `chr`; no curvature, metric, or Ricci-flow hypothesis enters,
so it lives at the reusable abstraction level mandated by the project's
tensor-calculation workflow. -/

section ComponentRecursion

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The single covariant-derivative step at the component level, rank `r → r+1`.

For a rank-`r` array `A`, the directional-derivative data `ext m d` (the
derivative of the scalar `· ↦ A m` in the `d`-th frame direction), and the
Christoffel data `chr d a p = Γᵖ_{d a}`, the covariant derivative is the
rank-`(r+1)` array

`(∇A)(n) = ext (tail n) (n 0) − Σ_{slot s} Σ_p Γᵖ_{(n 0),(tail n) s} · A((tail n)[s ↦ p])`,

i.e. the leading index `n 0` is the new derivative slot, the remaining indices
`tail n` index the original `r` slots, and there is exactly one Christoffel
correction per original slot.  This is the rank-uniform generalization of the
explicit frame formula in `ricciSecondCovDerivCompInFrame`. -/
def covDerivStepComp {r : ℕ}
    (ext : (Fin r → Idx) → Idx → Real)
    (chr : Idx → Idx → Idx → Real)
    (A : (Fin r → Idx) → Real) : (Fin (r + 1) → Idx) → Real :=
  fun n =>
    ext (Fin.tail n) (n 0) -
      ∑ s : Fin r, ∑ p : Idx,
        chr (n 0) (Fin.tail n s) p * A (Function.update (Fin.tail n) s p)

/-- The frame directional-derivative data of a base-point-dependent rank-`r`
component array `A : M → (Fin r → Idx) → ℝ`, at multi-index `m` and direction
`d`: the `frame d`-directional derivative of `y ↦ A y m`. -/
def frameExtData {r : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (A : M → (Fin r → Idx) → Real) (x : M) :
    (Fin r → Idx) → Idx → Real :=
  fun m d => extDerivFun (I := I) (fun y : M => A y m) x (frame d x)

/-- The iterated covariant-derivative component tower `∇ᵏRm`, by recursion on
`k`, as a rank-`(4+k)` array depending on `(t, x)`.

* `k = 0`: the lowered Riemann component array `base`.
* `k+1`: one `covDerivStepComp` applied to level `k`, using the frame
  directional derivative of level `k` (`frameExtData`) and the supplied
  Christoffel data `chr`.

The element type is always `ℝ`; only the arity `4+k` varies, with
`Fin (4+(k+1)) = Fin ((4+k)+1)` handled definitionally.  Working at the
component level avoids any bundled-tensor dependent-type recursion. -/
def iteratedRmComp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : Real → M → Idx → Idx → Idx → Real)
    (base : Real → M → (Fin 4 → Idx) → Real) :
    (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real
  | 0 => base
  | (k + 1) => fun t x =>
      covDerivStepComp
        (frameExtData (I := I) frame
          (fun y : M => iteratedRmComp frame chr base k t y) x)
        (chr t x)
        (iteratedRmComp frame chr base k t x)

@[simp] theorem iteratedRmComp_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : Real → M → Idx → Idx → Idx → Real)
    (base : Real → M → (Fin 4 → Idx) → Real) :
    iteratedRmComp (I := I) frame chr base 0 = base := rfl

theorem iteratedRmComp_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : Real → M → Idx → Idx → Idx → Real)
    (base : Real → M → (Fin 4 → Idx) → Real) (k : ℕ) (t : Real) (x : M) :
    iteratedRmComp (I := I) frame chr base (k + 1) t x =
      covDerivStepComp
        (frameExtData (I := I) frame
          (fun y : M => iteratedRmComp (I := I) frame chr base k t y) x)
        (chr t x)
        (iteratedRmComp (I := I) frame chr base k t x) := rfl

end ComponentRecursion

/-! ## The general orthonormal reduction

For the eq-7.4 tower one needs, at every rank `r = 4 + k`, the multi-index
squared norm of the component array to reduce, in an orthonormal frame, to the
plain component norm `compNormSqMulti`.  We define the multi-index norm with the
standard delta-metric raising and prove the reduction once and for all, for an
arbitrary rank-`r` array.  This is the rank-uniform generalization of
`rm04NormSqInFrame_eq_compNormSq4` and `nablaRm04NormSqInFrame_eq_compNormSq5`. -/

section OrthonormalReduction

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The multi-index squared norm of a rank-`r` component array, with each slot
raised by the inverse metric `gInv`:
`|A|² = Σ_{m,n} (∏_{s} g^{m_s n_s}) · A m · A n`.

In an orthonormal frame (`gInv = δ`) this reduces to `compNormSqMulti A`
(`multiNormInFrame_eq_compNormSqMulti`). -/
def multiNormRaised {r : ℕ}
    (gInv : Idx → Idx → Real) (A : (Fin r → Idx) → Real) : Real :=
  ∑ m : Fin r → Idx, ∑ n : Fin r → Idx,
    (∏ s : Fin r, gInv (m s) (n s)) * A m * A n

/-- The product of Kronecker deltas over the slots is `1` when the two
multi-indices agree and `0` otherwise. -/
theorem prod_delta_eq {r : ℕ} (m n : Fin r → Idx) :
    (∏ s : Fin r, (if m s = n s then (1 : Real) else 0)) =
      (if m = n then 1 else 0) := by
  classical
  by_cases h : m = n
  · subst h
    simp
  · rw [if_neg h]
    -- some slot disagrees, killing the product
    obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    rw [if_neg hs]

/-- **General orthonormal reduction.**  In an orthonormal frame the multi-index
squared norm collapses to the plain component norm:
`multiNormRaised δ A = compNormSqMulti A`.

This is the multi-index orthonormal reduction underlying the tower: the
rank-uniform generalization of `rm04NormSqInFrame_eq_compNormSq4`
(`k = 0`) and `nablaRm04NormSqInFrame_eq_compNormSq5` (`k = 1`). -/
theorem multiNormInFrame_eq_compNormSqMulti {r : ℕ}
    (gInv : Idx → Idx → Real)
    (A : (Fin r → Idx) → Real)
    (horth : ∀ i j : Idx, gInv i j = if i = j then 1 else 0) :
    multiNormRaised (r := r) gInv A = compNormSqMulti A := by
  classical
  unfold multiNormRaised compNormSqMulti
  -- Collapse the inner `n`-sum against the delta product.
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single m]
  · have hprod : (∏ s : Fin r, gInv (m s) (m s)) = 1 := by
      refine Finset.prod_eq_one fun s _ => ?_
      rw [horth (m s) (m s), if_pos rfl]
    rw [hprod]; ring
  · intro n _ hn
    have hprod : (∏ s : Fin r, gInv (m s) (n s)) = 0 := by
      have : (∏ s : Fin r, gInv (m s) (n s)) =
          ∏ s : Fin r, (if m s = n s then (1 : Real) else 0) := by
        refine Finset.prod_congr rfl fun s _ => ?_
        rw [horth (m s) (n s)]
      rw [this, prod_delta_eq, if_neg (fun h => hn h.symm)]
    rw [hprod]; ring
  · intro h; exact absurd (Finset.mem_univ m) h

end OrthonormalReduction

/-! ## The tower heat inequality producer

We now assemble the eq-7.4 per-level heat inequality `TowerHeatBoundOn` for the
derivative tower `w k = |∇ᵏRm|²`.  Following the `k=0`/`k=1` architecture
(`RiemannNormHeatProducer.lean`, `NablaRiemannHeat.lean`) we take the raw
component facts as hypotheses, bundled as the interface predicate
`IteratedRmTowerOn`:

* `wDef k` — the level field `w k` equals `compNormSqMulti (level k)` (the
  orthonormal-frame squared norm of `∇ᵏRm`; via
  `multiNormInFrame_eq_compNormSqMulti` this is the genuine `|∇ᵏRm|²`);
* `heatEq k` — the assembled heat **equation**
  `∂ₜ(w k) = wLap k + (−2·(w (k+1)) + reactionMulti)`,
  where `reactionMulti` is the schematic `Σⱼ 2⟨∇ʲRm ∗ ∇^{k−j}Rm, ∇ᵏRm⟩` of eq 7.4
  (this single identity packages the Uhlenbeck `∂ₜRm`, the connection evolution,
  the Bochner Laplacian split, and the iterated commutator
  `[∇ᵏ,Δ]A = Σⱼ ∇ʲRm ∗ ∇^{k−j}A`, exactly as the `k=0`/`k=1` heat-equation
  hypotheses do);
* `starBound k` — the per-entry `∗`-norm bound on each commutator factor, the
  only property a `∗`-product is ever used through.

On top of these we discharge the reaction half with `abs_nablaRmReactionMulti_le`
and drop the favourable `−2|∇^{k+1}Rm|² ≤ 0` term, producing the
`TowerHeatBoundOn` predicate consumed by the maximum-principle stage. -/

section TowerHeatInequality

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The general-`k` schematic reaction realized on the tower: the `∗`-reaction
`nablaRmReactionMulti` of eq 7.4 at level `k`, contracting `∇ᵏRm` (`level k`)
against the abstractly-supplied star arrays `star k j` (the `j`-th commutator
factor `∇ʲRm ∗ ∇^{k−j}Rm`). -/
def towerReactionMulti
    (level : (k : ℕ) → (Fin (4 + k) → Idx) → Real)
    (star : (k : ℕ) → ℕ → (Fin (4 + k) → Idx) → Real)
    (k : ℕ) : Real :=
  nablaRmReactionMulti (level k) (star k)

/-- **The iterated-`∇ᵏRm` tower interface.**  This bundles the raw per-level
component facts that the eq-7.4 producer rests on, exactly mirroring the
hypotheses of the `k=0`/`k=1` heat-equation producers but at every rank.

* `level k` is the rank-`(4+k)` component array of `∇ᵏRm` in the frame (e.g.
  `iteratedRmComp … k t x`);
* `star k j` is the `j`-th `∗`-commutator factor at level `k`, supplied
  abstractly (we never pin a contraction tensor);
* `w`, `wLap` are the scalar tower fields and their realized Laplacians. -/
structure IteratedRmTowerOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (level : (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real)
    (star : (k : ℕ) → Real → M → ℕ → (Fin (4 + k) → Idx) → Real)
    (w wLap : ℕ → Real → M → Real) : Prop where
  /-- Each tower field is the orthonormal-frame squared norm of `∇ᵏRm`. -/
  wDef : ∀ (k : ℕ) (t : Real) (x : M),
    w k t x = compNormSqMulti (level k t x)
  /-- The assembled heat **equation** at every level: the Uhlenbeck time
  derivative, connection evolution, Bochner split, and iterated commutator,
  packaged into `∂ₜ(w k) = wLap k + (−2·(w (k+1)) + reaction)` with the eq-7.4
  `∗`-reaction. -/
  heatEq : ∀ (k : ℕ)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M),
    HasDerivWithinAt (fun s : Real => w k s x)
      (wLap k (t : Real) x +
        (-2 * w (k + 1) (t : Real) x +
          towerReactionMulti (level · (t : Real) x) (star · (t : Real) x) k))
      D.carrier (t : Real)
  /-- The per-entry `∗`-norm bound on each commutator factor (the eq-7.4
  Cauchy–Schwarz input): the `j`-th star factor is controlled by
  `√(w j)·√(w (k−j))`. -/
  starBound : ∀ (k : ℕ) (t : Real) (x : M),
    ∀ j ∈ Finset.range (k + 1), ∀ m : Fin (4 + k) → Idx,
      |star k t x j m| ≤
        (Fintype.card Idx : Real) ^ 2 *
          (Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x))

/-- **The reaction half of the tower inequality** (eq 7.4 estimate).  From the
tower interface, the schematic reaction at level `k` obeys the
`towerReactionSum` shape with tower constant `c = 2·card^{6+k}`:

`|reaction k| ≤ Σⱼ (2·card^{6+k})·√(w j)·√(w (k−j))·√(w k)`.

This is the bridge: it plugs the variable-rank `∇ᵏRm` straight into
`abs_nablaRmReactionMulti_le`. -/
theorem abs_towerReactionMulti_le
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {level : (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real}
    {star : (k : ℕ) → Real → M → ℕ → (Fin (4 + k) → Idx) → Real}
    {w wLap : ℕ → Real → M → Real}
    (T : IteratedRmTowerOn (D := D) level star w wLap)
    (k : ℕ) (t : Real) (x : M) :
    |towerReactionMulti (level · t x) (star · t x) k| ≤
      ∑ j ∈ Finset.range (k + 1),
        (2 * (Fintype.card Idx : Real) ^ (6 + k)) *
          Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x) := by
  unfold towerReactionMulti
  refine abs_nablaRmReactionMulti_le (level k t x) (star k t x) (fun j => w j t x) ?_ ?_
  · exact (T.wDef k t x).symm
  · intro j hj m
    exact T.starBound k t x j hj m

/-- **The eq-7.4 tower heat inequality (sharp form).**  From the tower interface,
at every regular time and point the time derivative `d = ∂ₜ(w k)` satisfies

`d ≤ wLap k − 2·(w (k+1)) + Σⱼ (2·card^{6+k})·√(w j)·√(w (k−j))·√(w k)`,

i.e. the sharp `−2|∇^{k+1}Rm|²` form of eq 7.4 with tower constant
`c = 2·card^{6+k}`. -/
theorem iteratedRmTower_heatBoundSharp
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {level : (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real}
    {star : (k : ℕ) → Real → M → ℕ → (Fin (4 + k) → Idx) → Real}
    {w wLap : ℕ → Real → M → Real}
    (T : IteratedRmTowerOn (D := D) level star w wLap)
    (k : ℕ)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) :
    ∃ d : Real,
      HasDerivWithinAt (fun s : Real => w k s x) d D.carrier (t : Real) ∧
      d ≤ wLap k (t : Real) x +
        (-2 * w (k + 1) (t : Real) x +
          towerReactionSum (M := M) w (2 * (Fintype.card Idx : Real) ^ (6 + k))
            k (t : Real) x) := by
  refine ⟨_, T.heatEq k t x, ?_⟩
  -- The reaction is at most its absolute value, controlled by the `∗`-bound,
  -- which is exactly `towerReactionSum` at `c = 2·card^{6+k}`.
  have hreact_le :
      towerReactionMulti (level · (t : Real) x) (star · (t : Real) x) k ≤
        towerReactionSum (M := M) w (2 * (Fintype.card Idx : Real) ^ (6 + k))
          k (t : Real) x := by
    refine le_trans (le_abs_self _) ?_
    refine le_trans (abs_towerReactionMulti_le T k (t : Real) x) ?_
    -- match `towerReactionSum` term-by-term
    unfold towerReactionSum
    apply le_of_eq
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  linarith [hreact_le]

/-- **The eq-7.4 tower heat inequality** (`TowerHeatBoundOn`), the producer
output.  Dropping the favourable `−2|∇^{k+1}Rm|² ≤ 0` term from the sharp form
yields exactly the `TowerHeatBoundOn` predicate consumed by the
`BernsteinTower` maximum-principle stage, with tower constant
`c = 2·card^{6+k}`:

`(∂ₜ − Δ)(w k) ≤ −2·(w (k+1)) + Σⱼ c·√(w j)·√(w (k−j))·√(w k)`.

This is the variable-rank `∇ᵏRm` producer, the exact analogue at every level of
the `k=1` producer `nablaRm04NormHeatBoundOn_of_components`. -/
theorem iteratedRmTower_heatBound
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {level : (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real}
    {star : (k : ℕ) → Real → M → ℕ → (Fin (4 + k) → Idx) → Real}
    {w wLap : ℕ → Real → M → Real}
    (T : IteratedRmTowerOn (D := D) level star w wLap)
    (k : ℕ) :
    TowerHeatBoundOn (D := D) w wLap
      (2 * (Fintype.card Idx : Real) ^ (6 + k)) k := by
  intro t x
  obtain ⟨d, hderiv, hle⟩ := iteratedRmTower_heatBoundSharp T k t x
  exact ⟨d, hderiv, hle⟩

end TowerHeatInequality

end DifferentialGeometry.PDE.RicciFlow
