import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.TowerHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BernsteinShiSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeatFrameInvariant

/-!
# TowerProducer: the BBS all-`m` bound for a solution (BernsteinTower-direct path)

The StarSum residual bound (`TowerHeat.resStarBoundLF`) is a *summed* bound
`|residual| ≤ C·Σⱼ√wⱼ√w_{k−j}`, which the per-`j`/`card²` `IteratedRmTowerOn` interface cannot accept
(see `TowerProducer.md`).  The compatible target is the *summed-reaction* `TowerHeatBoundOn` /
`BernsteinTower` (arbitrary constant `c`), whose `estimate_div` yields the same all-`m` Shi bound.

This file builds the pure-tensor core toward `towerHeatBound_of_solution`, in three steps; the standing
analytic inputs of `resStarLFU` and the intrinsic heat equation are CARRIED as hypotheses (their
discharge from the solution is a later brick).  **Step 1** (below) is the intrinsic L² residual-norm
bound; steps 2–3 (reaction bound, heat-bound assembly) follow.
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- **Step 1a (generic component bound → L² bound).**  If every component of
`f : (Fin r → Idx) → ℝ` has `|f m| ≤ B`, then `compNormSqMulti f ≤ card·B²`. -/
theorem compNormSqMulti_le_card {Idx : Type*} [Fintype Idx] {r : ℕ}
    (f : (Fin r → Idx) → Real) (B : Real) (hB : ∀ m : Fin r → Idx, |f m| ≤ B) :
    compNormSqMulti f ≤ (Fintype.card (Fin r → Idx) : Real) * B ^ 2 := by
  have hsq : ∀ m : Fin r → Idx, (f m) ^ 2 ≤ B ^ 2 := by
    intro m
    obtain ⟨hl, hr⟩ := abs_le.mp (hB m)
    exact sq_le_sq' hl hr
  calc compNormSqMulti f = ∑ _m : Fin r → Idx, (f _m) ^ 2 := rfl
    _ ≤ ∑ _m : Fin r → Idx, B ^ 2 := Finset.sum_le_sum fun m _ => hsq m
    _ = (Fintype.card (Fin r → Idx) : Real) * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

set_option linter.unusedSectionVars false in
/-- **Step 1b (intrinsic L² residual-norm bound).**  At a `g`-orthonormal `basis`, the intrinsic
squared norm `normSq0S` of `A` is at most `card·B²` if every frame component `A (basis ∘ m)` is
bounded by `B`.  Applied to the StarSum residual `T`, with `B := C·Σⱼ√wⱼ√w_{k−j}` from
`resStarBoundLF`, this is the residual-norm input to the reaction bound (step 2). -/
theorem normSq0S_le_card {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (B : Real) (hB : ∀ m : Fin s → Idx, |A (fun p => basis (m p))| ≤ B) :
    normSq0S (I := I) g x s A ≤ (Fintype.card (Fin s → Idx) : Real) * B ^ 2 := by
  rw [← compNormSqMulti_orthoBasis_eq_normSq0S (I := I) g basis horth A]
  exact compNormSqMulti_le_card (fun idx : Fin s → Idx => A (fun p => basis (idx p))) B hB

set_option linter.unusedSectionVars false in
/-- **Step 2 (generic reaction bound).**  The combined-star reaction
`2·Σ_m level_m·(ricStarArray ric level + resid)_m` — with `level` the `∇ᵏRm` components
(`compNormSqMulti level ≤ w k`), Ricci components `≤ card·√(w 0)`, and the residual controlled
per-component by the summed `Cres·Σⱼ√wⱼ√w_{k−j}` — is bounded by the `towerReactionSum` shape
`Σⱼ c·√wⱼ·√w_{k−j}·√wₖ` with the single constant `c := 2·√(card^{4+k})·((4+k)·card² + Cres)`.
The Ricci (`j = 0`) half is absorbed via `√(w 0)·√(w k) ≤ Σⱼ √wⱼ√w_{k−j}`. -/
theorem reactionContract_le {k : ℕ} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (level resid : (Fin (4 + k) → Idx) → Real) (ric : Idx → Idx → Real)
    (w : ℕ → Real)
    (hlevel : compNormSqMulti level ≤ w k)
    (hRic : ∀ p q : Idx, |ric p q| ≤ (Fintype.card Idx : Real) * Real.sqrt (w 0))
    (Cres : Real) (hCres : 0 ≤ Cres)
    (hresid : ∀ m : Fin (4 + k) → Idx, |resid m| ≤
        Cres * ∑ j ∈ Finset.range (k + 1), Real.sqrt (w j) * Real.sqrt (w (k - j))) :
    |2 * ∑ m : Fin (4 + k) → Idx, level m * (ricStarArray ric level m + resid m)|
      ≤ ∑ j ∈ Finset.range (k + 1),
          (2 * Real.sqrt ((Fintype.card (Fin (4 + k) → Idx) : Real)) *
            (((4 + k : ℕ) : Real) * (Fintype.card Idx : Real) ^ 2 + Cres)) *
          (Real.sqrt (w j) * Real.sqrt (w (k - j)) * Real.sqrt (w k)) := by
  classical
  set card : Real := (Fintype.card Idx : Real) with hcard
  set Ncard : Real := (Fintype.card (Fin (4 + k) → Idx) : Real) with hNcard
  set Ssum : Real := ∑ j ∈ Finset.range (k + 1), Real.sqrt (w j) * Real.sqrt (w (k - j)) with hSsum
  have hcard0 : 0 ≤ card := by positivity
  have hNcard0 : 0 ≤ Ncard := by positivity
  have hSsum0 : 0 ≤ Ssum :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  set Br : Real := ((4 + k : ℕ) : Real) * card ^ 2 * Real.sqrt (w 0) * Real.sqrt (w k) with hBr
  set Bres : Real := Cres * Ssum with hBres
  have hBr0 : 0 ≤ Br := by rw [hBr]; positivity
  have hBres0 : 0 ≤ Bres := by rw [hBres]; positivity
  -- per-component bound on `combined = ricStar + resid`
  have hcomb : ∀ m : Fin (4 + k) → Idx,
      |ricStarArray ric level m + resid m| ≤ Br + Bres := by
    intro m
    refine le_trans (abs_add_le _ _) (add_le_add ?_ (hresid m))
    refine le_trans (abs_ricStarArray_le ric level (card * Real.sqrt (w 0))
      (mul_nonneg hcard0 (Real.sqrt_nonneg _)) hRic m) ?_
    have hsq : Real.sqrt (compNormSqMulti level) ≤ Real.sqrt (w k) := Real.sqrt_le_sqrt hlevel
    calc ((4 + k : ℕ) : Real) * card * (card * Real.sqrt (w 0)) *
            Real.sqrt (compNormSqMulti level)
        ≤ ((4 + k : ℕ) : Real) * card * (card * Real.sqrt (w 0)) * Real.sqrt (w k) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = Br := by rw [hBr]; ring
  -- L² bound on combined via step 1
  have hcombnorm :
      compNormSqMulti (fun m : Fin (4 + k) → Idx => ricStarArray ric level m + resid m)
        ≤ Ncard * (Br + Bres) ^ 2 :=
    compNormSqMulti_le_card _ (Br + Bres) hcomb
  -- Cauchy–Schwarz on the contraction
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ level
    (fun m : Fin (4 + k) → Idx => ricStarArray ric level m + resid m)
  have hAbs : |∑ m : Fin (4 + k) → Idx, level m * (ricStarArray ric level m + resid m)|
      ≤ Real.sqrt (compNormSqMulti level) *
          Real.sqrt (compNormSqMulti
            (fun m : Fin (4 + k) → Idx => ricStarArray ric level m + resid m)) := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (compNormSqMulti_nonneg _)]
    exact Real.sqrt_le_sqrt hcs
  -- chain into `Br + Bres`
  have hsqcomb : Real.sqrt (compNormSqMulti
        (fun m : Fin (4 + k) → Idx => ricStarArray ric level m + resid m))
      ≤ Real.sqrt Ncard * (Br + Bres) := by
    refine le_trans (Real.sqrt_le_sqrt hcombnorm) ?_
    rw [Real.sqrt_mul hNcard0, Real.sqrt_sq (by positivity)]
  have hsqlevel : Real.sqrt (compNormSqMulti level) ≤ Real.sqrt (w k) := Real.sqrt_le_sqrt hlevel
  -- assemble `|2·Σ| ≤ 2·√w_k·√Ncard·(Br+Bres)`
  have hmain : |2 * ∑ m : Fin (4 + k) → Idx, level m * (ricStarArray ric level m + resid m)|
      ≤ 2 * (Real.sqrt (w k) * (Real.sqrt Ncard * (Br + Bres))) := by
    rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine le_trans hAbs ?_
    exact mul_le_mul hsqlevel hsqcomb (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine le_trans hmain ?_
  -- final algebra: `√w₀·√w_k ≤ Ssum` (j=0 term) absorbs the Ricci part
  have hj0 : Real.sqrt (w 0) * Real.sqrt (w k) ≤ Ssum := by
    have hmem : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.succ_pos k)
    have := Finset.single_le_sum
      (f := fun j => Real.sqrt (w j) * Real.sqrt (w (k - j)))
      (fun j _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hmem
    simpa using this
  -- RHS = c·√w_k·Ssum
  have hRHS : ∑ j ∈ Finset.range (k + 1),
        (2 * Real.sqrt Ncard * (((4 + k : ℕ) : Real) * card ^ 2 + Cres)) *
          (Real.sqrt (w j) * Real.sqrt (w (k - j)) * Real.sqrt (w k))
      = (2 * Real.sqrt Ncard * (((4 + k : ℕ) : Real) * card ^ 2 + Cres)) * Real.sqrt (w k) * Ssum := by
    rw [hSsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hRHS]
  -- `2√w_k√Ncard(Br+Bres) ≤ c·√w_k·Ssum`
  have hBrBres : Br + Bres ≤ (((4 + k : ℕ) : Real) * card ^ 2 + Cres) * Ssum := by
    rw [hBr, hBres, add_mul]
    refine add_le_add ?_ (le_of_eq (by ring))
    calc ((4 + k : ℕ) : Real) * card ^ 2 * Real.sqrt (w 0) * Real.sqrt (w k)
        = (((4 + k : ℕ) : Real) * card ^ 2) * (Real.sqrt (w 0) * Real.sqrt (w k)) := by ring
      _ ≤ (((4 + k : ℕ) : Real) * card ^ 2) * Ssum :=
          mul_le_mul_of_nonneg_left hj0 (by positivity)
  calc 2 * (Real.sqrt (w k) * (Real.sqrt Ncard * (Br + Bres)))
      = 2 * Real.sqrt Ncard * Real.sqrt (w k) * (Br + Bres) := by ring
    _ ≤ 2 * Real.sqrt Ncard * Real.sqrt (w k) *
          ((((4 + k : ℕ) : Real) * card ^ 2 + Cres) * Ssum) :=
        mul_le_mul_of_nonneg_left hBrBres (by positivity)
    _ = (2 * Real.sqrt Ncard * (((4 + k : ℕ) : Real) * card ^ 2 + Cres)) * Real.sqrt (w k) * Ssum := by
        ring

set_option linter.unusedSectionVars false in
/-- Pointwise form of the intrinsic tower-reaction estimate at an orthonormal
basis. -/
theorem nablaKReactionAt_le {k : ℕ} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv ric : Idx → Idx → Real)
    (Tdot : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x)
    (w : ℕ → Real → M → Real)
    (horth : ∀ i j : Idx,
      (S.base.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (hgInv : gInv = identityInvMetric (Idx := Idx))
    (hlevel : compNormSqMulti (fun I0 : Fin (4 + k) → Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
          (fun i => basis i) I0) ≤ w k t x)
    (hRic : ∀ p q : Idx, |ric p q| ≤
      (Fintype.card Idx : Real) * Real.sqrt (w 0 t x))
    (Cres : Real) (hCres : 0 ≤ Cres)
    (hresid : ∀ m : Fin (4 + k) → Idx,
      |tensor0SComponent (I := I)
          (Tdot - metricTrace0S2TensorInBasis (I := I) basis gInv
            (nablaKRm04Field (I := I) S t (k + 2) x))
          (fun i => basis i) m| ≤
        Cres * ∑ j ∈ Finset.range (k + 1),
          Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x)) :
    |nablaKReactionAt (I := I) S k t x basis gInv ric Tdot| ≤
      towerReactionSum (M := M) w
        (2 * Real.sqrt ((Fintype.card (Fin (4 + k) → Idx) : Real)) *
          (((4 + k : ℕ) : Real) * (Fintype.card Idx : Real) ^ 2 + Cres)) k t x := by
  rw [nablaKReactionAt_eq (I := I) S k t x basis gInv ric Tdot horth hgInv]
  refine le_trans (reactionContract_le
    (fun I0 : Fin (4 + k) → Idx =>
      tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
        (fun i => basis i) I0)
    (fun m : Fin (4 + k) → Idx =>
      tensor0SComponent (I := I)
        (Tdot - metricTrace0S2TensorInBasis (I := I) basis gInv
          (nablaKRm04Field (I := I) S t (k + 2) x))
        (fun i => basis i) m)
    ric (fun j => w j t x) hlevel hRic Cres hCres hresid) ?_
  rw [towerReactionSum]
  refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
  ring

set_option linter.unusedSectionVars false in
/-- **Step 2 (the intrinsic reaction bound).**  The actual heat-equation reaction
`nablaKRm04ReactionIntrinsic` — at a `g`-orthonormal basis (`gInv = δ`), with the `∇ᵏRm` components'
norm `≤ w k`, Ricci components `≤ card·√(w 0)`, and the residual `(∂ₜ − Δ)∇ᵏRm = Tdot − roughLap`
controlled per-component by `Cres·Σⱼ√wⱼ√w_{k−j}` — is bounded (in absolute value) by the schematic
`towerReactionSum` with the single constant `c := 2·√(card^{4+k})·((4+k)·card² + Cres)`.  Composes
`nablaKRm04Reaction_orthoBasis_eq_compContract` (the orthonormal collapse to a plain contraction) with
`reactionContract_le`.  This is the `TowerHeatBoundOn` reaction input (step 3). -/
theorem nablaKReaction_le {k : ℕ} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basis : (x : M) → Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real → M → Idx → Idx → Real)
    (ric : Real → M → Idx → Idx → Real)
    (Tdot : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (4 + k) x)
    (t : Real) (x : M) (w : ℕ → Real → M → Real)
    (horth : ∀ i j : Idx,
      (S.base.metric t).inner x (basis x i) (basis x j) = if i = j then (1 : Real) else 0)
    (hgInv : gInv t x = identityInvMetric (Idx := Idx))
    (hlevel : compNormSqMulti (fun I0 : Fin (4 + k) → Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x) (fun i => basis x i) I0)
        ≤ w k t x)
    (hRic : ∀ p q : Idx, |ric t x p q| ≤ (Fintype.card Idx : Real) * Real.sqrt (w 0 t x))
    (Cres : Real) (hCres : 0 ≤ Cres)
    (hresid : ∀ m : Fin (4 + k) → Idx,
        |tensor0SComponent (I := I)
            (Tdot t x - metricTrace0S2TensorInBasis (I := I) (basis x) (gInv t x)
              (nablaKRm04Field (I := I) S t (k + 2) x)) (fun i => basis x i) m|
          ≤ Cres * ∑ j ∈ Finset.range (k + 1),
              Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x)) :
    |nablaKRm04ReactionIntrinsic (I := I) S k basis gInv ric Tdot t x|
      ≤ towerReactionSum (M := M) w
          (2 * Real.sqrt ((Fintype.card (Fin (4 + k) → Idx) : Real)) *
            (((4 + k : ℕ) : Real) * (Fintype.card Idx : Real) ^ 2 + Cres)) k t x := by
  change |nablaKReactionAt (I := I) S k t x (basis x) (gInv t x)
      (ric t x) (Tdot t x)| ≤ _
  exact nablaKReactionAt_le (I := I) S t x (basis x) (gInv t x) (ric t x)
    (Tdot t x) w horth hgInv hlevel hRic Cres hCres hresid

set_option linter.unusedSectionVars false in
/-- **Step 3 (TowerHeatBoundOn from heat equation + reaction bound).**
Given:
- the intrinsic heat equation `NablaRm04NormHeatEquationOn w nablaKRmNormLap w' reaction`
  (= `∀ t x, HasDerivWithinAt (w · x) (nablaKRmNormLap + (-2·w' + reaction)) D.carrier t`),
- the reaction bound `∀ t x, |reaction t x| ≤ towerReactionSum w c k t x`,
- the Laplacian alignment `∀ t x, nablaKRmNormLap t x = wLap k t x`,

produce `TowerHeatBoundOn w wLap c k`.  The core step is `reaction ≤ |reaction| ≤ towerReactionSum`
(= `le_abs_self`).  The hypotheses are discharged from `nablaKRm04NormHeatEquationOn_intrinsic` +
`nablaKReaction_le` in a later assembly brick (the pointwise-basis construction). -/
theorem towerHeatBoundOn_of_heatReact
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {w wLap : ℕ → Real → M → Real}
    {c : Real} {k : ℕ}
    {nablaKRmNormLap reaction : Real → M → Real}
    (hHeatEq : NablaRm04NormHeatEquationOn (D := D) (w k) nablaKRmNormLap (w (k + 1)) reaction)
    (hReact : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
        (x : M),
      |reaction (t : Real) x| ≤ towerReactionSum (M := M) w c k (t : Real) x)
    (hLap : ∀ (t : Real) (x : M), nablaKRmNormLap t x = wLap k t x) :
    TowerHeatBoundOn (D := D) w wLap c k := by
  intro t x
  refine ⟨nablaKRmNormLap (↑t) x + (-2 * w (k + 1) (↑t) x + reaction (↑t) x), hHeatEq t x, ?_⟩
  rw [hLap]
  linarith [le_abs_self (reaction (↑t) x), hReact t x]

end DifferentialGeometry.PDE.RicciFlow
