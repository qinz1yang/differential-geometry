import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedNablaRmTower

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The all-`m` Bernstein–Bando–Shi estimate for a Ricci-flow solution

This file assembles the **complete derivative tower** of the
Bernstein–Bando–Shi estimate for a Ricci-flow solution.  Combining

* the variable-rank tower heat-inequality *producer* `iteratedRmTower_heatBound`
  of `Evolution/IteratedNablaRmTower.lean`, which for each level `k` supplies the
  schematic eq-7.4 inequality `TowerHeatBoundOn w wLap (2·card^{6+k}) k` from the
  raw component facts bundled as an `IteratedRmTowerOn` interface, and
* the strong-induction maximum-principle *consumer* `BernsteinTower.estimate_div`
  of `Evolution/BernsteinShiHigher.lean`, which from a `BernsteinTower` with a
  single uniform reaction constant `c` concludes
  `w m (t,x) ≤ (towerConst c α m)²·K²/tᵐ`,

we obtain, for a Ricci-flow solution with `|Rm|² ≤ K²` on the slab `[0,T]` and
`T ≤ α/K`, the on-diagonal Bernstein–Bando–Shi bound at **every** order `m`:

  `|∇ᵐRm|²(t,x) ≤ (towerConst (2·card^{6+m}) α m)²·K²/tᵐ`  for `t ∈ (0,T]`.

## The uniform-constant resolution (the "zero above `m`" trick)

`estimate_div` needs a `BernsteinTower` with a *single* reaction constant `c`
valid at every level, but the producer only gives the level-dependent constant
`c_k = 2·card^{6+k}`.  For each **target** order `m` we therefore build a
*truncated* tower `truncTower` with the uniform constant `c := 2·card^{6+m}` and
the levels above `m` zeroed out:

  `w' k := if k ≤ m then w k else 0`,   `wLap' k := if k ≤ m then wLap k else 0`.

The schematic heat inequality `hheat` at constant `c` then holds at every level:

* `k < m`: the producer at level `k` gives the inequality with the *smaller*
  constant `c_k ≤ c`, and `towerReactionSum` is monotone increasing in the
  constant (all summands are `≥ 0`), so it lifts to `c`.  All referenced levels
  are `≤ m`, where `w' = w`.
* `k = m`: the producer at level `m` has the favourable term `−2·w(m+1)`, whereas
  the truncated inequality needs only `−2·w'(m+1) = −2·0 = 0`; dropping the
  nonnegative term `2·w(m+1) ≥ 0` only weakens the bound, so it still holds.
* `k > m`: `w' k = 0`, so the time derivative is `0`, the Laplacian field is `0`,
  and the reaction sum vanishes (it carries a factor `√(w' k) = 0`); the
  inequality `0 ≤ 0` is trivial.

The remaining `BernsteinTower` regularity fields are inherited from the solution's
fields at the levels `≤ m`, and are discharged for the zeroed levels `> m` from
the regularity of the constant-zero scalar field (whose gradient is the zero
section).

## Main result

* `bernsteinShi_solution_estimate` — the all-`m` Bernstein–Bando–Shi bound for a
  solution, taking the `IteratedRmTowerOn` component interface and the scalar
  bound/regularity data as hypotheses (exactly as the `k=0`/`k=1` producers take
  their component facts as hypotheses).
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [I.Boundaryless] [CompactSpace M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-! ## Monotonicity of the tower reaction sum in the constant -/

/-- `towerReactionSum` is monotone increasing in its constant: every summand is a
nonnegative multiple of the constant (the `√`-product factors are unconditionally
nonnegative).  Used to lift the level-`k` producer's constant `c_k = 2·card^{6+k}`
up to the uniform target constant `c = 2·card^{6+m}` (`c_k ≤ c` for `k ≤ m`). -/
theorem towerReactionSum_mono_const
    (w : ℕ -> Real -> M -> Real) {c c' : Real} (hcc : c <= c')
    (k : ℕ) (t : Real) (x : M) :
    towerReactionSum (M := M) w c k t x <= towerReactionSum (M := M) w c' k t x := by
  unfold towerReactionSum
  apply Finset.sum_le_sum
  intro j _
  have h1 : 0 <= Real.sqrt (w j t x) := Real.sqrt_nonneg _
  have h2 : 0 <= Real.sqrt (w (k - j) t x) := Real.sqrt_nonneg _
  have h3 : 0 <= Real.sqrt (w k t x) := Real.sqrt_nonneg _
  have hprod : 0 <= Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x) :=
    mul_nonneg (mul_nonneg h1 h2) h3
  calc c * Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x)
      = c * (Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x)) := by ring
    _ <= c' * (Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x)) :=
        mul_le_mul_of_nonneg_right hcc hprod
    _ = c' * Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x) := by ring

/-- The level constants are monotone in the level: `2·card^{6+k} ≤ 2·card^{6+m}`
for `k ≤ m`.  (Handles `card = 0`, where both exponents `≥ 6 > 0` give `0`.) -/
theorem towerLevelConst_mono {k m : ℕ} (hkm : k <= m) :
    2 * (Fintype.card Idx : Real) ^ (6 + k) <= 2 * (Fintype.card Idx : Real) ^ (6 + m) := by
  have hcard : (0 : Real) <= (Fintype.card Idx : Real) := by positivity
  have hpow : (Fintype.card Idx : Real) ^ (6 + k) <= (Fintype.card Idx : Real) ^ (6 + m) := by
    rcases Nat.eq_zero_or_pos (Fintype.card Idx) with hc0 | hcpos
    · -- card = 0: both powers are 0 (exponents are positive)
      rw [hc0]
      simp only [Nat.cast_zero]
      rw [zero_pow (by omega : 6 + k ≠ 0), zero_pow (by omega : 6 + m ≠ 0)]
    · -- card ≥ 1: monotone in the exponent
      have h1 : (1 : Real) <= (Fintype.card Idx : Real) := by
        have : (1 : ℕ) <= Fintype.card Idx := hcpos
        exact_mod_cast this
      exact pow_le_pow_right₀ h1 (by omega)
  linarith [mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : Real) <= 2)]

/-! ## The truncated tower and the all-`m` estimate -/

/-- **All-`m` Bernstein–Bando–Shi estimate for a Ricci-flow solution.**

For a solution presented through the iterated-`∇ᵏRm` component interface
`IteratedRmTowerOn` (the established component-fact frontier, taken as a
hypothesis exactly as the `k=0`/`k=1` producers do), together with the scalar
curvature bound `w 0 ≤ K²`, the parabolic time bound `T ≤ α/K`, and the per-level
regularity needed to run the maximum principle, every covariant-derivative norm
`w m = |∇ᵐRm|²` obeys the on-diagonal Bernstein–Bando–Shi bound

  `w m (t,x) ≤ (towerConst (2·card^{6+m}) α m)²·K²/tᵐ`  for all `t ∈ (0,T]`.

The reaction constant at order `m` is `2·card^{6+m}`, matching the level-`m`
producer constant; this is the all-`m` analogue of the `k=1` Stage-1 estimate. -/
theorem bernsteinShi_solution_estimate
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {level : (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real}
    {star : (k : ℕ) → Real → M → ℕ → (Fin (4 + k) → Idx) → Real}
    {w wLap : ℕ → Real → M → Real}
    (tower : IteratedRmTowerOn (D := D) level star w wLap)
    (K α T : Real)
    (hT : 0 < T) (hK : 0 < K) (hα : 0 <= α)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hw_nonneg : ∀ k : ℕ, ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, 0 <= w k t x)
    (hw0_bound : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, w 0 t x <= K ^ 2)
    (hTK : T <= α / K)
    (hLap : ∀ k : ℕ, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
        (fun _y : M => (0 : TangentSpace I _y)) (w k t) x = wLap k t x)
    (hw_cont : ∀ k : ℕ, ContinuousOn (fun p : Real × M => w k p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T))
    (hw_space : ∀ k : ℕ, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (w k t) y)
    (hw_grad : ∀ k : ℕ, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (w k t) y) x)
    (m : ℕ) {t : Real} (htmem : t ∈ Set.Icc 0 T) (htpos : 0 < t) (x : M) :
    w m t x <=
      (towerConst (2 * (Fintype.card Idx : Real) ^ (6 + m)) α m) ^ 2 * K ^ 2 / t ^ m := by
  classical
  -- The uniform reaction constant for this target order.
  set c : Real := 2 * (Fintype.card Idx : Real) ^ (6 + m) with hc_def
  have hc_nonneg : (0 : Real) <= c := by rw [hc_def]; positivity
  -- The truncated tower fields: real below `m`, zero above.
  set w' : ℕ -> Real -> M -> Real := fun k => if k <= m then w k else fun _ _ => 0 with hw'_def
  set wLap' : ℕ -> Real -> M -> Real := fun k => if k <= m then wLap k else fun _ _ => 0
    with hwLap'_def
  -- Pointwise rewriting helpers for the truncated fields.
  have hw'_le : ∀ k : ℕ, k <= m -> w' k = w k := by
    intro k hk; simp only [hw'_def, if_pos hk]
  have hw'_gt : ∀ k : ℕ, ¬ k <= m -> w' k = fun _ _ => 0 := by
    intro k hk; simp only [hw'_def, if_neg hk]
  have hwLap'_le : ∀ k : ℕ, k <= m -> wLap' k = wLap k := by
    intro k hk; simp only [hwLap'_def, if_pos hk]
  have hwLap'_gt : ∀ k : ℕ, ¬ k <= m -> wLap' k = fun _ _ => 0 := by
    intro k hk; simp only [hwLap'_def, if_neg hk]
  -- Pointwise values.
  have hw'_val_le : ∀ k : ℕ, k <= m -> ∀ (s : Real) (y : M), w' k s y = w k s y := by
    intro k hk s y; rw [hw'_le k hk]
  have hw'_val_gt : ∀ k : ℕ, ¬ k <= m -> ∀ (s : Real) (y : M), w' k s y = 0 := by
    intro k hk s y; rw [hw'_gt k hk]
  have hwLap'_val_le : ∀ k : ℕ, k <= m -> ∀ (s : Real) (y : M), wLap' k s y = wLap k s y := by
    intro k hk s y; rw [hwLap'_le k hk]
  have hwLap'_val_gt : ∀ k : ℕ, ¬ k <= m -> ∀ (s : Real) (y : M), wLap' k s y = 0 := by
    intro k hk s y; rw [hwLap'_gt k hk]
  -- Nonnegativity of the truncated levels (used in the reaction monotonicity).
  have hw'_nonneg : ∀ k : ℕ, ∀ s : Real, s ∈ Set.Icc 0 T -> ∀ y : M, 0 <= w' k s y := by
    intro k s hs y
    by_cases hk : k <= m
    · rw [hw'_val_le k hk]; exact hw_nonneg k s hs y
    · rw [hw'_val_gt k hk]
  -- The reaction sum only sees levels `≤ k`, so truncation below `m` is invisible
  -- when `k ≤ m`: `towerReactionSum w' c k = towerReactionSum w c k` there.
  have hreact_eq : ∀ k : ℕ, k <= m -> ∀ (s : Real) (y : M),
      towerReactionSum (M := M) w' c k s y = towerReactionSum (M := M) w c k s y := by
    intro k hk s y
    unfold towerReactionSum
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjk : j <= k := by omega
    have hj_le : j <= m := le_trans hjk hk
    have hkj_le : k - j <= m := le_trans (Nat.sub_le k j) hk
    rw [hw'_val_le j hj_le, hw'_val_le (k - j) hkj_le, hw'_val_le k hk]
  -- Build the truncated `BernsteinTower`.
  set B : BernsteinTower (I := I) G :=
    { D := D
      w := w'
      wLap := wLap'
      c := c
      K := K
      α := α
      T := T
      hT := hT
      hc := hc_nonneg
      hK := hK
      hα := hα
      hslab := hslab
      hregular := hregular
      hw_nonneg := hw'_nonneg
      hw0_bound := by
        intro s hs y
        rw [hw'_val_le 0 (Nat.zero_le m)]
        exact hw0_bound s hs y
      hTK := hTK
      hheat := by
        -- The truncated schematic heat inequality at every level, constant `c`.
        intro k τ y
        rcases lt_trichotomy k m with hlt | heq | hgt
        · -- `k < m`: lift the level-`k` producer from `c_k` to `c`.
          have hk_le : k <= m := le_of_lt hlt
          have hk1_le : k + 1 <= m := hlt
          obtain ⟨d, hderiv, hle⟩ :=
            iteratedRmTower_heatBound tower k τ y
          refine ⟨d, ?_, ?_⟩
          · -- derivative of the truncated field `w' k = w k`
            have : (fun s : Real => w' k s y) = (fun s : Real => w k s y) := by
              funext s; rw [hw'_val_le k hk_le]
            rw [this]; exact hderiv
          · -- bound: rewrite truncated fields and lift the constant
            rw [hwLap'_val_le k hk_le, hw'_val_le (k + 1) hk1_le,
              hreact_eq k hk_le]
            have hmono : towerReactionSum (M := M) w
                  (2 * (Fintype.card Idx : Real) ^ (6 + k)) k (τ : Real) y <=
                towerReactionSum (M := M) w c k (τ : Real) y :=
              towerReactionSum_mono_const w (towerLevelConst_mono (Idx := Idx) hk_le)
                k (τ : Real) y
            linarith [hle, hmono]
        · -- `k = m`: drop the favourable `−2·w(m+1) ≤ 0` term.
          subst heq
          have hk_le : k <= k := le_refl k
          have hk1_gt : ¬ k + 1 <= k := by omega
          obtain ⟨d, hderiv, hle⟩ :=
            iteratedRmTower_heatBound tower k τ y
          -- at the top level the producer constant `2·card^{6+k}` *is* the uniform `c`
          rw [← hc_def] at hle
          refine ⟨d, ?_, ?_⟩
          · have : (fun s : Real => w' k s y) = (fun s : Real => w k s y) := by
              funext s; rw [hw'_val_le k hk_le]
            rw [this]; exact hderiv
          · rw [hwLap'_val_le k hk_le, hw'_val_gt (k + 1) hk1_gt,
              hreact_eq k hk_le]
            -- producer: `d ≤ wLap k + (−2·w(k+1) + react)`; goal RHS has `−2·0`.
            -- `w (k+1)` is a sum of squares (`compNormSqMulti`), hence `≥ 0`, at
            -- every regular time (no `[0,T]` membership needed).
            have hnn : 0 <= w (k + 1) (τ : Real) y := by
              rw [tower.wDef (k + 1) (τ : Real) y]
              exact compNormSqMulti_nonneg _
            nlinarith [hle, hnn]
        · -- `k > m`: every truncated field is zero.
          have hk_gt : ¬ k <= m := by omega
          have hk1_gt : ¬ k + 1 <= m := by omega
          refine ⟨0, ?_, ?_⟩
          · have : (fun s : Real => w' k s y) = (fun _s : Real => (0 : Real)) := by
              funext s; rw [hw'_val_gt k hk_gt]
            rw [this]; exact hasDerivWithinAt_const _ _ _
          · rw [hwLap'_val_gt k hk_gt, hw'_val_gt (k + 1) hk1_gt]
            -- reaction sum carries the factor `√(w' k) = √0 = 0`.
            have hreact0 : towerReactionSum (M := M) w' c k (τ : Real) y = 0 := by
              unfold towerReactionSum
              apply Finset.sum_eq_zero
              intro j _
              rw [hw'_val_gt k hk_gt]
              simp
            rw [hreact0]; norm_num
      hLap := by
        intro k s hs hspos y
        by_cases hk : k <= m
        · -- real level: `heatOp (w' k s) = heatOp (w k s)`, then use the hypothesis
          have hfun : (w' k s) = (w k s) := by funext z; rw [hw'_val_le k hk]
          rw [hwLap'_val_le k hk, hfun]
          exact hLap k s hs hspos y
        · -- zeroed level: heat operator of the constant-zero field is zero
          have hfun : (w' k s) = (fun _z : M => (0 : Real)) := by
            funext z; rw [hw'_val_gt k hk]
          rw [hwLap'_val_gt k hk, hfun]
          rw [DifferentialGeometry.Integral.Connection.heatOperatorWithDrift_zero_drift,
            DifferentialGeometry.Integral.Connection.heatOperator_eq_laplacianAt,
            DifferentialGeometry.Integral.Connection.laplacianAt_eq]
          exact DifferentialGeometry.Integral.Connection.laplacian_const
            (I := I) (G.connection s) (G.metric s) 0 y
      hw_cont := by
        intro k
        by_cases hk : k <= m
        · have hfun : (fun p : Real × M => w' k p.1 p.2) =
              (fun p : Real × M => w k p.1 p.2) := by
            funext p; rw [hw'_val_le k hk]
          rw [hfun]; exact hw_cont k
        · have hfun : (fun p : Real × M => w' k p.1 p.2) =
              (fun _p : Real × M => (0 : Real)) := by
            funext p; rw [hw'_val_gt k hk]
          rw [hfun]; exact continuousOn_const
      hw_space := by
        intro k s hs hspos y
        by_cases hk : k <= m
        · have hfun : (w' k s) = (w k s) := by funext z; rw [hw'_val_le k hk]
          rw [hfun]; exact hw_space k s hs hspos y
        · have hfun : (w' k s) = (fun _z : M => (0 : Real)) := by
            funext z; rw [hw'_val_gt k hk]
          rw [hfun]; exact mdifferentiableAt_const
      hw_grad := by
        intro k s hs hspos y
        by_cases hk : k <= m
        · have hfun : (w' k s) = (w k s) := by funext z; rw [hw'_val_le k hk]
          simp only [hfun]; exact hw_grad k s hs hspos y
        · have hfun : (w' k s) = (fun _z : M => (0 : Real)) := by
            funext z; rw [hw'_val_gt k hk]
          simp only [hfun]
          -- gradient of the constant-zero field is the zero section
          refine (mdifferentiableAt_zeroSection (𝕜 := Real) (F := E)
            (E := (TangentSpace I : M -> Type _)) (x := y)).congr_of_eventuallyEq ?_
          filter_upwards with z
          exact congrArg (fun v => (⟨z, v⟩ : TotalSpace E (TangentSpace I)))
            (DifferentialGeometry.Integral.Connection.gradientFun_const (I := I) (G.metric s) 0 z) }
    with hB_def
  -- Apply the maximum-principle consumer at level `m`; `B.w m = w' m = w m`.
  have hkey : B.w m t x <= (towerConst B.c B.α m) ^ 2 * B.K ^ 2 / t ^ m :=
    B.estimate_div m htmem htpos x
  -- Reduce `B`'s projections (`B.w = w'`, `B.c = c`, `B.α = α`, `B.K = K`).
  simp only [hB_def] at hkey
  -- `B.w m = w' m = w m` (since `m ≤ m`).
  rw [hw'_val_le m (le_refl m) t x] at hkey
  exact hkey

end DifferentialGeometry.PDE.RicciFlow
