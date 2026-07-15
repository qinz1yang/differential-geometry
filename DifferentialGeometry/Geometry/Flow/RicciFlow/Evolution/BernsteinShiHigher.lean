import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BernsteinShi

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Bernstein–Bando–Shi higher derivative estimates (parametric core)

This file formalizes the general-`m` parametric Bernstein–Bando–Shi derivative
estimate on a closed manifold, following the strong-induction maximum-principle
proof of Chow–Knopf, *The Ricci Flow: An Introduction*, Theorem 7.1
(eqs 7.4–7.6).

We work with an abstract "derivative tower" of scalar fields
`w : ℕ → ℝ → M → ℝ` with `w k = |∇ᵏRm|²` (so `w 0 = |Rm|²`), each nonnegative,
with per-level Laplacian fields `wLap k` and the schematic heat inequalities

  `(∂ₜ − Δ)(w k) ≤ −2·(w (k+1)) + Σ_{j=0}^{k} c·√(w j)·√(w (k−j))·√(w k)`

together with `w 0 ≤ K²` on `[0,T]`, `T ≤ α/K`, and per-level regularity
hypotheses analogous to the `m = 1` Stage-1 file `Evolution/BernsteinShi.lean`.

The conclusion is: for every `m`,

  `w m (t,x) ≤ C_m² · K² / tᵐ`  for `t ∈ (0,T]`,

with `C_m` depending only on `m, α` (and the tower constant `c`).
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

/-! ## Finite-sum differentiability helpers -/

/-- Differentiability of a finite scalar sum `Σ_{i ∈ s} c i · f i`. -/
theorem mdifferentiableAt_finset_sum_smul
    {ι : Type*} (s : Finset ι) (f : ι -> M -> Real) (c : ι -> Real) (y : M)
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(Real, Real) (f i) y) :
    MDifferentiableAt I 𝓘(Real, Real) (fun z : M => ∑ i ∈ s, c i * f i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mdifferentiableAt_const (I := I) (I' := 𝓘(Real, Real)) (c := (0 : Real))
  | insert a s has ih =>
      have hfa : MDifferentiableAt I 𝓘(Real, Real) (f a) y := hf a (by simp)
      have htail := ih (fun i hi => hf i (by simp [hi]))
      have heqfun :
          (fun z : M => ∑ i ∈ insert a s, c i * f i z) =
            (fun z : M => c a * f a z) + (fun z : M => ∑ i ∈ s, c i * f i z) := by
        funext z; simp only [Pi.add_apply]; rw [Finset.sum_insert has]
      rw [heqfun]
      exact ((hfa.const_smul (c a)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => by simp [smul_eq_mul])).add htail

/-- Differentiability of the gradient section of a finite scalar sum
`Σ_{i ∈ s} c i · f i`, given the per-summand gradient-section data. -/
theorem mdiffAt_gradientFun_finset_sum_smul
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {ι : Type*} (s : Finset ι)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (t : Real) (f : ι -> M -> Real) (c : ι -> Real) (x : M)
    (hf : ∀ i ∈ s, ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (f i) y)
    (hgradf : ∀ i ∈ s, MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f i) y) x) :
    MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
        (fun z : M => ∑ i ∈ s, c i * f i z) y) x := by
  classical
  -- The gradient of the sum is the sum of `c i •` the per-summand gradients.
  have hgrad_eq :
      (fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
            (fun z : M => ∑ i ∈ s, c i * f i z) y) =
        (fun y : M => ∑ i ∈ s,
          (c i • fun w : M =>
            DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f i) w) y) := by
    funext y
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        rw [show (fun z : M => (0 : Real)) =
            (fun _z : M => (0 : Real)) from rfl]
        exact DifferentialGeometry.Integral.Connection.gradientFun_const (I := I) (G.metric t) 0 y
    | insert a s has ih =>
        have hfa : MDifferentiableAt I 𝓘(Real, Real) (fun z : M => c a * f a z) y := by
          simpa [smul_eq_mul] using (hf a (by simp) y).const_smul (c a)
        have htail_diff : MDifferentiableAt I 𝓘(Real, Real)
            (fun z : M => ∑ i ∈ s, c i * f i z) y :=
          mdifferentiableAt_finset_sum_smul (I := I) s f c y
            (fun i hi => hf i (by simp [hi]) y)
        rw [show (fun z : M => ∑ i ∈ insert a s, c i * f i z) =
              (fun z : M => c a * f a z + ∑ i ∈ s, c i * f i z) from by
          funext z; rw [Finset.sum_insert has]]
        rw [DifferentialGeometry.Integral.Connection.gradientFun_add (I := I) (G.metric t) hfa htail_diff]
        rw [show (fun z : M => c a * f a z) = (c a • f a) from by funext z; simp [smul_eq_mul]]
        rw [DifferentialGeometry.Integral.Connection.gradientFun_const_smul (I := I) (G.metric t) (c a) (hf a (by simp) y)]
        rw [ih (fun i hi => hf i (by simp [hi])) (fun i hi => hgradf i (by simp [hi]))]
        rw [Finset.sum_insert has]
        rfl
  -- Differentiability of that sum of scaled sections.
  have hsection_eq :
      (T% fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
            (fun z : M => ∑ i ∈ s, c i * f i z) y) =
        (T% fun y : M => ∑ i ∈ s,
          (c i • fun w : M =>
            DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f i) w) y) := by
    funext y
    have hy := congrFun hgrad_eq y
    simp only [hy]
  rw [hsection_eq]
  -- Differentiability of the sum of scaled gradient sections, by induction on `s`.
  clear hgrad_eq hsection_eq hf
  induction s using Finset.induction_on with
  | empty =>
      refine (mdifferentiableAt_zeroSection (𝕜 := Real) (F := E)
        (E := (TangentSpace I : M -> Type _)) (x := x)).congr_of_eventuallyEq ?_
      filter_upwards with y
      simp only [Finset.sum_empty]
      rfl
  | insert a s has ih =>
      have hgradfa : MDiffAt (T% fun w : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f a) w) x :=
        hgradf a (by simp)
      have htail := ih (fun i hi => hgradf i (by simp [hi]))
      have hsplit :
          (fun y : M => ∑ i ∈ insert a s,
            (c i • fun w : M =>
              DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f i) w) y) =
          ((c a • fun w : M =>
              DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f a) w) +
            fun y : M => ∑ i ∈ s,
              (c i • fun w : M =>
                DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f i) w) y) := by
        funext y
        simp only [Pi.add_apply]
        rw [Finset.sum_insert has]
      have hgoal_eq :
          (T% fun y : M => ∑ i ∈ insert a s,
            (c i • fun w : M =>
              DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f i) w) y) =
          (T% ((c a • fun w : M =>
              DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f a) w) +
            fun y : M => ∑ i ∈ s,
              (c i • fun w : M =>
                DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f i) w) y)) := by
        funext y
        exact congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I))) (congrFun hsplit y)
      rw [hgoal_eq]
      exact mdifferentiableAt_add_section (hgradfa.smul_const_section (a := c a)) htail

/-! ## Finite-sum linearity of the driftless Laplacian and heat operator -/

/-- The realized Laplacian is linear over a `Finset.sum` of scaled fields:
`Δ(Σ_{i ∈ s} c i · f i) = Σ_{i ∈ s} c i · Δ(f i)`.

This is the multi-term extension of `laplacianAt_linear_combo`. -/
theorem laplacianAt_linear_combo_finset
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {ι : Type*} (s : Finset ι)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (t : Real) (f : ι -> M -> Real) (c : ι -> Real) (x : M)
    (hf : ∀ i ∈ s, ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (f i) y)
    (hgradf : ∀ i ∈ s, MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f i) y) x) :
    DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
        (fun z : M => ∑ i ∈ s, c i * f i z) x =
      ∑ i ∈ s, c i * DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [DifferentialGeometry.Integral.Connection.laplacianAt_eq]
      unfold DifferentialGeometry.Integral.Connection.laplacian
      rw [show DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
            (fun _z : M => (0 : Real)) = (0 : (x : M) -> TangentSpace I x) by
        funext y; exact DifferentialGeometry.Integral.Connection.gradientFun_const (I := I) (G.metric t) 0 y]
      simp
  | insert a s has ih =>
      have hfa : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (f a) y := hf a (by simp)
      have hgradfa : MDiffAt (T% fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f a) y) x :=
        hgradf a (by simp)
      have hft : ∀ i ∈ s, ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (f i) y :=
        fun i hi => hf i (by simp [hi])
      have hgradft : ∀ i ∈ s, MDiffAt (T% fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f i) y) x :=
        fun i hi => hgradf i (by simp [hi])
      -- differentiability of the tail sum and its gradient section
      have htail_diff : ∀ y : M,
          MDifferentiableAt I 𝓘(Real, Real) (fun z : M => ∑ i ∈ s, c i * f i z) y :=
        fun y => mdifferentiableAt_finset_sum_smul (I := I) s f c y (fun i hi => hft i hi y)
      have htail_grad : MDiffAt (T% fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
            (fun z : M => ∑ i ∈ s, c i * f i z) y) x :=
        mdiffAt_gradientFun_finset_sum_smul (I := I) s G t f c x hft hgradft
      -- split off the `a` summand
      have hsplit :
          (fun z : M => ∑ i ∈ insert a s, c i * f i z) =
            (fun z : M => c a * f a z + 1 * (fun w : M => ∑ i ∈ s, c i * f i w) z) := by
        funext z; simp only [one_mul]; rw [Finset.sum_insert has]
      rw [hsplit]
      rw [laplacianAt_linear_combo (I := I) G t (f a)
        (fun w : M => ∑ i ∈ s, c i * f i w) (c a) 1 x hfa htail_diff hgradfa htail_grad]
      rw [ih hft hgradft]
      rw [Finset.sum_insert has]
      ring

/-- The zero-drift heat operator is linear over a `Finset.sum` of scaled fields. -/
theorem heatOperator_linear_combo_finset
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {ι : Type*} (s : Finset ι)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (t : Real) (f : ι -> M -> Real) (c : ι -> Real) (x : M)
    (hf : ∀ i ∈ s, ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (f i) y)
    (hgradf : ∀ i ∈ s, MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (f i) y) x) :
    DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
        (fun _y : M => (0 : TangentSpace I _y)) (fun z : M => ∑ i ∈ s, c i * f i z) x =
      ∑ i ∈ s, c i * DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
        (fun _y : M => (0 : TangentSpace I _y)) (f i) x := by
  rw [DifferentialGeometry.Integral.Connection.heatOperatorWithDrift_zero_drift,
    DifferentialGeometry.Integral.Connection.heatOperator_eq_laplacianAt]
  rw [laplacianAt_linear_combo_finset (I := I) s G t f c x hf hgradf]
  apply Finset.sum_congr rfl
  intro i _
  rw [DifferentialGeometry.Integral.Connection.heatOperatorWithDrift_zero_drift,
    DifferentialGeometry.Integral.Connection.heatOperator_eq_laplacianAt]

/-! ## The Bernstein constants

We package the recursion of Chow–Knopf eqs 7.5–7.6 into explicit constants.
Given the lower-level constants `C : ℕ → ℝ` (with `C j` the bound constant at
level `j`), we form:

* `towerBarGood c C k = c · C k · Σ_{j=0}^{k} C j · C (k−j)` — the 7.6 reaction
  aggregate, so that the retained-good reaction at level `k` is bounded by
  `towerBarGood · K³ / tᵏ`;
* `towerBarTop c C m = 2·c + c · (Σ_{j=1}^{m−1} C j · C (m−j)) / 2` — the 7.5
  reaction aggregate, so that `(∂ₜ−Δ)(w m) ≤ towerBarTop · K · (w m + K²/tᵐ)`;
* `towerBeta`, `towerFactCoeff`, and the squared bound constant
  `towerConstSq`/`towerConst` assembled from these. -/

/-- The 7.6 retained-good reaction aggregate at level `k`, as a function of the
lower-level constants `C`. -/
def towerBarGood (c : Real) (C : ℕ -> Real) (k : ℕ) : Real :=
  c * C k * ∑ j ∈ Finset.range (k + 1), C j * C (k - j)

/-- The 7.5 top-level reaction aggregate at level `m`, as a function of the
lower-level constants `C`. -/
def towerBarTop (c : Real) (C : ℕ -> Real) (m : ℕ) : Real :=
  2 * c + c * (∑ j ∈ Finset.Ico 1 m, C j * C (m - j)) / 2

/-- The factorial coefficient `a_i = (m−1)!/i!` appearing in the indexed
Bernstein quantity `G`. -/
def towerFactCoeff (m i : ℕ) : Real :=
  (Nat.factorial (m - 1) : Real) / (Nat.factorial i : Real)

/-- The Bernstein weight `β` at level `m`, chosen `≥ (C̄_m α + m)/2` so that the
top-level bad term is dominated. -/
def towerBeta (c α : Real) (C : ℕ -> Real) (m : ℕ) : Real :=
  (towerBarTop c C m * α + (m : Real)) / 2

/-- The squared bound constant at level `m`, defined by strong recursion from the
lower-level constants.  For `m ≥ 1` it equals
`β(m−1)! + (C̄_m + β·Σ_{i<m} a_i C̄_i')·α`, which is exactly `(a + b·α/K)/K²` for
the maximum-principle data `a, b` (and is manifestly independent of `K`).  For
`m = 0` it is `1` (the base curvature bound `w 0 ≤ K²`). -/
noncomputable def towerConstSq (c α : Real) (m : ℕ) : Real :=
  Nat.strongRecOn' m fun n ih =>
    if n = 0 then 1
    else
      let C : ℕ -> Real := fun j =>
        if hj : j < n then Real.sqrt (ih j hj) else 0
      towerBeta c α C n * (Nat.factorial (n - 1) : Real) +
        (towerBarTop c C n +
          towerBeta c α C n *
            ∑ i ∈ Finset.range n, towerFactCoeff n i * towerBarGood c C i) * α

/-- The (non-squared) Bernstein bound constant at level `m`. -/
noncomputable def towerConst (c α : Real) (m : ℕ) : Real :=
  Real.sqrt (towerConstSq c α m)

/-- Unfolding of `towerConstSq` at level `0`. -/
@[simp] theorem towerConstSq_zero (c α : Real) : towerConstSq c α 0 = 1 := by
  rw [towerConstSq, Nat.strongRecOn'_beta]
  simp

/-- The level-`0` bound constant is `1`. -/
@[simp] theorem towerConst_zero (c α : Real) : towerConst c α 0 = 1 := by
  rw [towerConst, towerConstSq_zero, Real.sqrt_one]

/-- The bound constant is nonnegative. -/
theorem towerConst_nonneg (c α : Real) (m : ℕ) : 0 <= towerConst c α m :=
  Real.sqrt_nonneg _

/-- `towerBarGood` only reads `C` at indices `≤ k`, hence is congruent under
agreement of `C` on `Finset.range (k + 1)`. -/
theorem towerBarGood_congr (c : Real) {C C' : ℕ -> Real} {k : ℕ}
    (h : ∀ j ∈ Finset.range (k + 1), C j = C' j) :
    towerBarGood c C k = towerBarGood c C' k := by
  unfold towerBarGood
  have hk : C k = C' k := h k (by simp)
  rw [hk]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j hj, h (k - j) (by
    simp only [Finset.mem_range] at hj ⊢; omega)]

/-- `towerBarTop` only reads `C` at indices `< m`, hence is congruent under
agreement of `C` on `Finset.range m`. -/
theorem towerBarTop_congr (c : Real) {C C' : ℕ -> Real} {m : ℕ}
    (h : ∀ j ∈ Finset.range m, C j = C' j) :
    towerBarTop c C m = towerBarTop c C' m := by
  unfold towerBarTop
  have hsum : (∑ j ∈ Finset.Ico 1 m, C j * C (m - j)) =
      ∑ j ∈ Finset.Ico 1 m, C' j * C' (m - j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_Ico] at hj
    rw [h j (by simp only [Finset.mem_range]; omega),
      h (m - j) (by simp only [Finset.mem_range]; omega)]
  rw [hsum]

/-- `towerBeta` only reads `C` at indices `< m`, hence is congruent under
agreement of `C` on `Finset.range m`. -/
theorem towerBeta_congr (c α : Real) {C C' : ℕ -> Real} {m : ℕ}
    (h : ∀ j ∈ Finset.range m, C j = C' j) :
    towerBeta c α C m = towerBeta c α C' m := by
  unfold towerBeta
  rw [towerBarTop_congr c h]

/-- Unfolding of `towerConstSq` at a positive level `n`, in terms of the
lower-level constants `towerConst c α j` for `j < n`. -/
theorem towerConstSq_pos (c α : Real) {n : ℕ} (hn : 0 < n) :
    towerConstSq c α n =
      towerBeta c α (towerConst c α) n * (Nat.factorial (n - 1) : Real) +
        (towerBarTop c (towerConst c α) n +
          towerBeta c α (towerConst c α) n *
            ∑ i ∈ Finset.range n, towerFactCoeff n i * towerBarGood c (towerConst c α) i) * α := by
  -- The local `C j = if j < n then √(towerConstSq c α j) else 0` agrees with
  -- `towerConst c α j` on the indices actually used (`j < n`).
  set Cloc : ℕ -> Real := fun j =>
    if hj : j < n then Real.sqrt (towerConstSq c α j) else 0 with hCloc
  have hCeq : ∀ j ∈ Finset.range n, Cloc j = towerConst c α j := by
    intro j hj
    rw [hCloc]
    simp only [dif_pos (Finset.mem_range.mp hj)]
    rw [towerConst]
  -- Rewrite the strong-recursion value at `n` in terms of `Cloc` (defeq), then
  -- transport along `hCeq` to `towerConst c α`.
  have hLHS : towerConstSq c α n =
      towerBeta c α Cloc n * (Nat.factorial (n - 1) : Real) +
        (towerBarTop c Cloc n +
          towerBeta c α Cloc n *
            ∑ i ∈ Finset.range n, towerFactCoeff n i * towerBarGood c Cloc i) * α := by
    conv_lhs => rw [towerConstSq, Nat.strongRecOn'_beta]
    rw [if_neg (by omega : ¬ n = 0)]
    rfl
  have hgoodsum :
      (∑ i ∈ Finset.range n, towerFactCoeff n i * towerBarGood c Cloc i) =
        ∑ i ∈ Finset.range n, towerFactCoeff n i * towerBarGood c (towerConst c α) i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [towerBarGood_congr c (C := Cloc) (C' := towerConst c α) (k := i)
      (fun j hj => hCeq j (by
        simp only [Finset.mem_range] at hi hj ⊢; omega))]
  rw [hLHS, towerBeta_congr c α hCeq, towerBarTop_congr c hCeq, hgoodsum]

/-- The factorial coefficient is nonnegative. -/
theorem towerFactCoeff_nonneg (m i : ℕ) : 0 <= towerFactCoeff m i := by
  rw [towerFactCoeff]; positivity

/-- The key factorial identity for telescoping: `k · (m−1)!/k! = (m−1)!/(k−1)!`,
i.e. `k · towerFactCoeff m k = towerFactCoeff m (k−1)`, for `k ≥ 1`. -/
theorem nat_mul_towerFactCoeff (m : ℕ) {k : ℕ} (hk : 1 <= k) :
    (k : Real) * towerFactCoeff m k = towerFactCoeff m (k - 1) := by
  rw [towerFactCoeff, towerFactCoeff]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
  have hjfac : (0 : Real) < (Nat.factorial j : Real) := by
    exact_mod_cast Nat.factorial_pos j
  have hjsucc : ((j : Real) + 1) ≠ 0 := by positivity
  field_simp

/-- The 7.6 reaction aggregate is nonnegative when `c ≥ 0`. -/
theorem towerBarGood_nonneg {c : Real} (hc : 0 <= c) (α : Real) (k : ℕ) :
    0 <= towerBarGood c (towerConst c α) k := by
  rw [towerBarGood]
  apply mul_nonneg (mul_nonneg hc (towerConst_nonneg _ _ _))
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (towerConst_nonneg _ _ _) (towerConst_nonneg _ _ _)

/-- The 7.5 reaction aggregate is nonnegative when `c ≥ 0`. -/
theorem towerBarTop_nonneg {c : Real} (hc : 0 <= c) (α : Real) (m : ℕ) :
    0 <= towerBarTop c (towerConst c α) m := by
  rw [towerBarTop]
  have h1 : (0 : Real) <= 2 * c := by linarith
  have h2 : 0 <= c * (∑ j ∈ Finset.Ico 1 m, towerConst c α j * towerConst c α (m - j)) / 2 := by
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg hc
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (towerConst_nonneg _ _ _) (towerConst_nonneg _ _ _)
  linarith

/-- The Bernstein weight `β` is nonnegative when `c, α ≥ 0`. -/
theorem towerBeta_nonneg {c α : Real} (hc : 0 <= c) (hα : 0 <= α) (m : ℕ) :
    0 <= towerBeta c α (towerConst c α) m := by
  rw [towerBeta]
  apply div_nonneg _ (by norm_num)
  have := towerBarTop_nonneg hc α m
  positivity

/-- The squared bound constant is nonnegative when `c, α ≥ 0`. -/
theorem towerConstSq_nonneg {c α : Real} (hc : 0 <= c) (hα : 0 <= α) (m : ℕ) :
    0 <= towerConstSq c α m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; rw [towerConstSq_zero]; norm_num
  · rw [towerConstSq_pos c α hm]
    have hβ := towerBeta_nonneg hc hα m
    have hbt := towerBarTop_nonneg hc α m
    have hsum : 0 <= ∑ i ∈ Finset.range m, towerFactCoeff m i * towerBarGood c (towerConst c α) i := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (towerFactCoeff_nonneg _ _) (towerBarGood_nonneg hc α i)
    have h1 : 0 <= towerBeta c α (towerConst c α) m * (Nat.factorial (m - 1) : Real) := by positivity
    have h2 : 0 <= (towerBarTop c (towerConst c α) m +
        towerBeta c α (towerConst c α) m *
          ∑ i ∈ Finset.range m, towerFactCoeff m i * towerBarGood c (towerConst c α) i) * α := by
      apply mul_nonneg _ hα; positivity
    linarith

/-- `(towerConst c α m)² = towerConstSq c α m` when `c, α ≥ 0`. -/
theorem towerConst_sq {c α : Real} (hc : 0 <= c) (hα : 0 <= α) (m : ℕ) :
    (towerConst c α m) ^ 2 = towerConstSq c α m := by
  rw [towerConst, Real.sq_sqrt (towerConstSq_nonneg hc hα m)]

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## The derivative tower -/

/-- The schematic reaction sum of eq 7.4 at level `k`:
`Σ_{j=0}^{k} c·√(w j)·√(w (k−j))·√(w k)`. -/
def towerReactionSum (w : ℕ -> Real -> M -> Real) (c : Real) (k : ℕ) (t : Real) (x : M) : Real :=
  ∑ j ∈ Finset.range (k + 1),
    c * Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x)

/-- The schematic heat inequality of eq 7.4 at level `k`, in `HasDerivWithinAt`
form (mirroring `NablaRm04NormHeatBoundOn`):
`(∂ₜ − Δ)(w k) ≤ −2·(w (k+1)) + Σ_{j=0}^{k} c·√(w j)·√(w (k−j))·√(w k)`,
where `wLap k` realizes `Δ(w k)`. -/
def TowerHeatBoundOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (w wLap : ℕ -> Real -> M -> Real) (c : Real) (k : ℕ) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    ∃ d : Real,
      HasDerivWithinAt (fun s : Real => w k s x) d D.carrier (t : Real) ∧
      d ≤ wLap k (t : Real) x +
        (-2 * w (k + 1) (t : Real) x + towerReactionSum (M := M) w c k (t : Real) x)

/-- A uniform Bernstein–Bando–Shi derivative tower on a closed manifold over the
slab `[0,T]`.  This bundles the level fields `w k = |∇ᵏRm|²`, their realized
Laplacian fields `wLap k`, the schematic heat inequalities (eq 7.4), the
curvature bound `w 0 ≤ K²`, the time bound `T ≤ α/K`, and the per-level
regularity hypotheses needed to run the maximum principle, all in the style of
the Stage-1 first-derivative estimate. -/
structure BernsteinTower
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real) where
  /-- The time interval the flow lives on. -/
  D : DifferentialGeometry.Integral.Connection.RealTimeInterval
  /-- The derivative tower `w k = |∇ᵏRm|²`. -/
  w : ℕ -> Real -> M -> Real
  /-- Per-level realized Laplacian fields. -/
  wLap : ℕ -> Real -> M -> Real
  /-- The reaction-coefficient constant of eq 7.4. -/
  c : Real
  /-- The curvature bound constant. -/
  K : Real
  /-- The time-scale constant. -/
  α : Real
  /-- The slab endpoint. -/
  T : Real
  hT : 0 < T
  hc : 0 <= c
  hK : 0 < K
  hα : 0 <= α
  /-- The slab `[0,T]` lies in the carrier, with positive times regular. -/
  hslab : Set.Icc 0 T ⊆ D.carrier
  hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular
  /-- Each level is nonnegative on the slab. -/
  hw_nonneg : ∀ k : ℕ, ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, 0 <= w k t x
  /-- The base curvature bound `|Rm|² ≤ K²`. -/
  hw0_bound : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, w 0 t x <= K ^ 2
  /-- The parabolic time bound `T ≤ α/K`. -/
  hTK : T <= α / K
  /-- The schematic heat inequality at every level. -/
  hheat : ∀ k : ℕ, TowerHeatBoundOn (D := D) w wLap c k
  /-- The Laplacian fields realize the driftless heat operator. -/
  hLap : ∀ k : ℕ, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
    DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
      (fun _y : M => (0 : TangentSpace I _y)) (w k t) x = wLap k t x
  /-- Joint continuity of each level on the closed slab (needed for the maximum
  principle, mirroring the Stage-1 `hF_cont` hypothesis). -/
  hw_cont : ∀ k : ℕ, ContinuousOn (fun p : Real × M => w k p.1 p.2)
    (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T)
  /-- Spatial differentiability of each level. -/
  hw_space : ∀ k : ℕ, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ y : M,
    MDifferentiableAt I 𝓘(Real, Real) (w k t) y
  /-- Gradient-section differentiability of each level. -/
  hw_grad : ∀ k : ℕ, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
    MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (w k t) y) x

namespace BernsteinTower

variable [I.Boundaryless] [CompactSpace M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable {G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real}

/-- From the inductive estimate `w j ≤ Cⱼ²K²/tʲ` (rewritten as
`tʲ·wⱼ ≤ Cⱼ²K²`), we get `√(tʲ·wⱼ) ≤ Cⱼ·K`.  This is the division-free root
bound used in the reaction analysis. -/
theorem sqrt_pow_mul_w_le (B : BernsteinTower (I := I) G) (j : ℕ)
    {t : Real} {x : M}
    (hbound : t ^ j * B.w j t x <= (towerConst B.c B.α j) ^ 2 * B.K ^ 2) :
    Real.sqrt (t ^ j * B.w j t x) <= towerConst B.c B.α j * B.K := by
  have hrhs_nonneg : 0 <= towerConst B.c B.α j * B.K :=
    mul_nonneg (towerConst_nonneg _ _ _) (le_of_lt B.hK)
  have hsq : (towerConst B.c B.α j * B.K) ^ 2 = (towerConst B.c B.α j) ^ 2 * B.K ^ 2 := by ring
  calc Real.sqrt (t ^ j * B.w j t x)
      <= Real.sqrt ((towerConst B.c B.α j * B.K) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [hsq]; exact hbound
    _ = towerConst B.c B.α j * B.K := Real.sqrt_sq hrhs_nonneg

/-- The product root identity at the heart of the reaction analysis: for `t ≥ 0`,
`tᵏ · √(wⱼ)·√(w_{k−j})·√(wₖ) = √(tʲ wⱼ)·√(t^{k−j} w_{k−j})·√(tᵏ wₖ)`
(using `j + (k−j) + k = 2k`).  Stated abstractly for nonnegative reals. -/
theorem tpow_mul_sqrt_triple {t : Real} (ht : 0 <= t) (k j : ℕ) (hj : j <= k)
    (a b d : Real) :
    t ^ k * (Real.sqrt a * Real.sqrt b * Real.sqrt d) =
      Real.sqrt (t ^ j * a) * Real.sqrt (t ^ (k - j) * b) * Real.sqrt (t ^ k * d) := by
  rw [Real.sqrt_mul (pow_nonneg ht j), Real.sqrt_mul (pow_nonneg ht (k - j)),
    Real.sqrt_mul (pow_nonneg ht k)]
  have hsplit : Real.sqrt (t ^ j) * Real.sqrt (t ^ (k - j)) * Real.sqrt (t ^ k) = t ^ k := by
    rw [← Real.sqrt_mul (pow_nonneg ht j), ← Real.sqrt_mul (mul_nonneg (pow_nonneg ht j) (pow_nonneg ht (k - j)))]
    rw [← pow_add, ← pow_add]
    have hexp : j + (k - j) + k = k * 2 := by omega
    rw [hexp, pow_mul, Real.sqrt_sq (pow_nonneg ht k)]
  calc t ^ k * (Real.sqrt a * Real.sqrt b * Real.sqrt d)
      = (Real.sqrt (t ^ j) * Real.sqrt (t ^ (k - j)) * Real.sqrt (t ^ k)) *
          (Real.sqrt a * Real.sqrt b * Real.sqrt d) := by rw [hsplit]
    _ = Real.sqrt (t ^ j) * Real.sqrt a * (Real.sqrt (t ^ (k - j)) * Real.sqrt b) *
          (Real.sqrt (t ^ k) * Real.sqrt d) := by ring

/-- The retained-good reaction bound (eq 7.6): at a level `k` all of whose
sub-levels are controlled by the inductive estimate `tⁱ·wᵢ ≤ Cᵢ²K²`, the
schematic reaction sum is bounded by `towerBarGood c C k · K³ / tᵏ`.

Stated in the `tᵏ`-multiplied, division-free form. -/
theorem tpow_mul_reactionSum_le (B : BernsteinTower (I := I) G) (k : ℕ)
    {t : Real} (htpos : 0 < t) {x : M}
    (hIH : ∀ j, j <= k -> t ^ j * B.w j t x <= (towerConst B.c B.α j) ^ 2 * B.K ^ 2) :
    t ^ k * towerReactionSum (M := M) B.w B.c k t x <=
      towerBarGood B.c (towerConst B.c B.α) k * B.K ^ 3 := by
  set C : ℕ -> Real := towerConst B.c B.α with hC
  have hht : (0 : Real) <= t := le_of_lt htpos
  -- Reshape both sides as sums over `Finset.range (k+1)`.
  rw [towerReactionSum, Finset.mul_sum]
  have hRHS : towerBarGood B.c C k * B.K ^ 3 =
      ∑ j ∈ Finset.range (k + 1),
        B.c * (C j * C (k - j)) * C k * B.K ^ 3 := by
    rw [towerBarGood,
      show B.c * C k * (∑ j ∈ Finset.range (k + 1), C j * C (k - j)) * B.K ^ 3 =
        (B.c * C k * B.K ^ 3) * (∑ j ∈ Finset.range (k + 1), C j * C (k - j)) from by ring,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [hRHS]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j <= k := by simp only [Finset.mem_range] at hj; omega
  -- The `j`-th reaction term, multiplied by `tᵏ`, equals a triple-root product.
  have hterm :
      t ^ k * (B.c * Real.sqrt (B.w j t x) * Real.sqrt (B.w (k - j) t x) * Real.sqrt (B.w k t x)) =
        B.c * (Real.sqrt (t ^ j * B.w j t x) * Real.sqrt (t ^ (k - j) * B.w (k - j) t x) *
          Real.sqrt (t ^ k * B.w k t x)) := by
    rw [show B.c * Real.sqrt (B.w j t x) * Real.sqrt (B.w (k - j) t x) * Real.sqrt (B.w k t x) =
        B.c * (Real.sqrt (B.w j t x) * Real.sqrt (B.w (k - j) t x) * Real.sqrt (B.w k t x)) from by ring]
    rw [← mul_assoc, mul_comm (t ^ k) B.c, mul_assoc]
    rw [tpow_mul_sqrt_triple hht k j hjk _ _ _]
  rw [hterm]
  -- Bound each root factor by `Cᵢ · K`.
  have hb1 : Real.sqrt (t ^ j * B.w j t x) <= C j * B.K :=
    B.sqrt_pow_mul_w_le j (hIH j hjk)
  have hb2 : Real.sqrt (t ^ (k - j) * B.w (k - j) t x) <= C (k - j) * B.K :=
    B.sqrt_pow_mul_w_le (k - j) (hIH (k - j) (by omega))
  have hb3 : Real.sqrt (t ^ k * B.w k t x) <= C k * B.K :=
    B.sqrt_pow_mul_w_le k (hIH k (le_refl k))
  have hs1 : 0 <= Real.sqrt (t ^ j * B.w j t x) := Real.sqrt_nonneg _
  have hs2 : 0 <= Real.sqrt (t ^ (k - j) * B.w (k - j) t x) := Real.sqrt_nonneg _
  have hs3 : 0 <= Real.sqrt (t ^ k * B.w k t x) := Real.sqrt_nonneg _
  have hCK1 : 0 <= C j * B.K := mul_nonneg (towerConst_nonneg _ _ _) (le_of_lt B.hK)
  have hCK2 : 0 <= C (k - j) * B.K := mul_nonneg (towerConst_nonneg _ _ _) (le_of_lt B.hK)
  have hprod_le :
      Real.sqrt (t ^ j * B.w j t x) * Real.sqrt (t ^ (k - j) * B.w (k - j) t x) *
        Real.sqrt (t ^ k * B.w k t x) <=
      (C j * B.K) * (C (k - j) * B.K) * (C k * B.K) := by
    apply mul_le_mul (mul_le_mul hb1 hb2 hs2 hCK1) hb3 hs3
    exact mul_nonneg hCK1 hCK2
  calc B.c * (Real.sqrt (t ^ j * B.w j t x) * Real.sqrt (t ^ (k - j) * B.w (k - j) t x) *
        Real.sqrt (t ^ k * B.w k t x))
      <= B.c * ((C j * B.K) * (C (k - j) * B.K) * (C k * B.K)) :=
        mul_le_mul_of_nonneg_left hprod_le B.hc
    _ = B.c * (C j * C (k - j)) * C k * B.K ^ 3 := by ring

/-- Decomposition of a `range (m+1)` sum into its bottom term, middle block, and
top term, valid for `m ≥ 1`. -/
theorem sum_range_succ_split {α : Type*} [AddCommMonoid α] (f : ℕ -> α) {m : ℕ} (hm : 1 <= m) :
    ∑ j ∈ Finset.range (m + 1), f j =
      f 0 + (∑ j ∈ Finset.Ico 1 m, f j) + f m := by
  rw [Finset.sum_range_succ]
  congr 1
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < m)]

/-- The top-level reaction bound (eq 7.5): at the top level `m`, with all strict
sub-levels controlled by the inductive estimate `tⁱ·wᵢ ≤ Cᵢ²K²`, the schematic
reaction sum is bounded by `towerBarTop c C m · K · (wₘ + K²/tᵐ)`. -/
theorem reactionSum_top_le (B : BernsteinTower (I := I) G) {m : ℕ} (hm : 1 <= m)
    {t : Real} (htpos : 0 < t) {x : M}
    (hmem : t ∈ Set.Icc 0 B.T)
    (hIH : ∀ j, j < m -> t ^ j * B.w j t x <= (towerConst B.c B.α j) ^ 2 * B.K ^ 2) :
    towerReactionSum (M := M) B.w B.c m t x <=
      towerBarTop B.c (towerConst B.c B.α) m * B.K *
        (B.w m t x + B.K ^ 2 / t ^ m) := by
  classical
  set C : ℕ -> Real := towerConst B.c B.α with hC
  have hht : (0 : Real) <= t := le_of_lt htpos
  have htm_pos : 0 < t ^ m := pow_pos htpos m
  have hwm_nonneg : 0 <= B.w m t x := B.hw_nonneg m t hmem x
  have hw0_nonneg : 0 <= B.w 0 t x := B.hw_nonneg 0 t hmem x
  have hsqrt_w0 : Real.sqrt (B.w 0 t x) <= B.K := by
    have : B.w 0 t x <= B.K ^ 2 := B.hw0_bound t hmem x
    calc Real.sqrt (B.w 0 t x) <= Real.sqrt (B.K ^ 2) := Real.sqrt_le_sqrt this
      _ = B.K := Real.sqrt_sq (le_of_lt B.hK)
  -- the root `r = √(tᵐ)`, with `r² = tᵐ`.
  set r : Real := Real.sqrt (t ^ m) with hr
  have hr_pos : 0 < r := Real.sqrt_pos.mpr htm_pos
  have hr_sq : r ^ 2 = t ^ m := Real.sq_sqrt (le_of_lt htm_pos)
  -- Bound on a single middle term `j ∈ Ico 1 m`.
  have hmid : ∀ j ∈ Finset.Ico 1 m,
      B.c * Real.sqrt (B.w j t x) * Real.sqrt (B.w (m - j) t x) * Real.sqrt (B.w m t x) <=
        B.c * (C j * C (m - j)) * B.K * (1 / 2 * (B.K ^ 2 / t ^ m + B.w m t x)) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have hjm : j < m := hj.2
    have hmjm : m - j < m := by omega
    -- IH bounds, in root form.
    have hbj : Real.sqrt (t ^ j * B.w j t x) <= C j * B.K :=
      B.sqrt_pow_mul_w_le j (hIH j hjm)
    have hbmj : Real.sqrt (t ^ (m - j) * B.w (m - j) t x) <= C (m - j) * B.K :=
      B.sqrt_pow_mul_w_le (m - j) (hIH (m - j) hmjm)
    -- `√(wⱼ)·√(w_{m-j}) = √(wⱼ w_{m-j})`, and `r·√(wⱼ w_{m-j}) = √(tᵐ wⱼ w_{m-j})`
    --  = √(tʲwⱼ · t^{m-j} w_{m-j}) = √(tʲwⱼ)·√(t^{m-j}w_{m-j}) ≤ CⱼC_{m-j}K².
    have hpair : r * (Real.sqrt (B.w j t x) * Real.sqrt (B.w (m - j) t x)) <=
        C j * C (m - j) * B.K ^ 2 := by
      have hid : r * (Real.sqrt (B.w j t x) * Real.sqrt (B.w (m - j) t x)) =
          Real.sqrt (t ^ j * B.w j t x) * Real.sqrt (t ^ (m - j) * B.w (m - j) t x) := by
        rw [hr, Real.sqrt_mul (pow_nonneg hht j), Real.sqrt_mul (pow_nonneg hht (m - j))]
        rw [show m = j + (m - j) from by omega, pow_add]
        rw [Real.sqrt_mul (pow_nonneg hht j)]
        rw [show j + (m - j) - j = m - j from by omega]
        ring
      rw [hid]
      have hs2 : 0 <= Real.sqrt (t ^ (m - j) * B.w (m - j) t x) := Real.sqrt_nonneg _
      have hCK1 : 0 <= C j * B.K := mul_nonneg (towerConst_nonneg _ _ _) (le_of_lt B.hK)
      calc Real.sqrt (t ^ j * B.w j t x) * Real.sqrt (t ^ (m - j) * B.w (m - j) t x)
          <= (C j * B.K) * (C (m - j) * B.K) := mul_le_mul hbj hbmj hs2 hCK1
        _ = C j * C (m - j) * B.K ^ 2 := by ring
    -- AM-GM on `√wₘ` against `K/r`.
    have hAMGM : (B.K / r) * Real.sqrt (B.w m t x) <=
        1 / 2 * (B.K ^ 2 / t ^ m + B.w m t x) := by
      have hsqm : (Real.sqrt (B.w m t x)) ^ 2 = B.w m t x := Real.sq_sqrt hwm_nonneg
      have hKr : (B.K / r) ^ 2 = B.K ^ 2 / t ^ m := by
        rw [div_pow, hr_sq]
      nlinarith [sq_nonneg (B.K / r - Real.sqrt (B.w m t x)), hsqm, hKr]
    -- Assemble the middle term bound.
    have hCmid_nonneg : 0 <= C j * C (m - j) :=
      mul_nonneg (towerConst_nonneg _ _ _) (towerConst_nonneg _ _ _)
    have hsqrtwm_nonneg : 0 <= Real.sqrt (B.w m t x) := Real.sqrt_nonneg _
    -- term = c · (√wⱼ √w_{m-j}) · √wₘ.  Multiply the pair bound by √wₘ/r and use AM-GM.
    have hterm_eq : B.c * Real.sqrt (B.w j t x) * Real.sqrt (B.w (m - j) t x) * Real.sqrt (B.w m t x) =
        B.c * ((Real.sqrt (B.w j t x) * Real.sqrt (B.w (m - j) t x)) * Real.sqrt (B.w m t x)) := by
      ring
    rw [hterm_eq]
    -- `(√wⱼ √w_{m-j}) ≤ CⱼC_{m-j}K²/r`, then times √wₘ and K-factor.
    have hpair' : Real.sqrt (B.w j t x) * Real.sqrt (B.w (m - j) t x) <=
        C j * C (m - j) * B.K ^ 2 / r := by
      rw [le_div_iff₀ hr_pos]
      calc Real.sqrt (B.w j t x) * Real.sqrt (B.w (m - j) t x) * r
          = r * (Real.sqrt (B.w j t x) * Real.sqrt (B.w (m - j) t x)) := by ring
        _ <= C j * C (m - j) * B.K ^ 2 := hpair
    calc B.c * ((Real.sqrt (B.w j t x) * Real.sqrt (B.w (m - j) t x)) * Real.sqrt (B.w m t x))
        <= B.c * ((C j * C (m - j) * B.K ^ 2 / r) * Real.sqrt (B.w m t x)) := by
          apply mul_le_mul_of_nonneg_left _ B.hc
          exact mul_le_mul_of_nonneg_right hpair' hsqrtwm_nonneg
      _ = B.c * (C j * C (m - j)) * B.K * ((B.K / r) * Real.sqrt (B.w m t x)) := by
          ring
      _ <= B.c * (C j * C (m - j)) * B.K * (1 / 2 * (B.K ^ 2 / t ^ m + B.w m t x)) := by
          apply mul_le_mul_of_nonneg_left hAMGM
          exact mul_nonneg (mul_nonneg B.hc hCmid_nonneg) (le_of_lt B.hK)
  -- Boundary terms `j = 0` and `j = m`.
  have hbdry0 :
      B.c * Real.sqrt (B.w 0 t x) * Real.sqrt (B.w (m - 0) t x) * Real.sqrt (B.w m t x) <=
        B.c * B.K * B.w m t x := by
    rw [Nat.sub_zero]
    have hsqm : Real.sqrt (B.w m t x) * Real.sqrt (B.w m t x) = B.w m t x := by
      rw [← Real.sqrt_mul hwm_nonneg, Real.sqrt_mul_self hwm_nonneg]
    calc B.c * Real.sqrt (B.w 0 t x) * Real.sqrt (B.w m t x) * Real.sqrt (B.w m t x)
        = B.c * Real.sqrt (B.w 0 t x) * (Real.sqrt (B.w m t x) * Real.sqrt (B.w m t x)) := by ring
      _ = B.c * Real.sqrt (B.w 0 t x) * B.w m t x := by rw [hsqm]
      _ <= B.c * B.K * B.w m t x := by
          apply mul_le_mul_of_nonneg_right _ hwm_nonneg
          exact mul_le_mul_of_nonneg_left hsqrt_w0 B.hc
  have hbdrym :
      B.c * Real.sqrt (B.w m t x) * Real.sqrt (B.w (m - m) t x) * Real.sqrt (B.w m t x) <=
        B.c * B.K * B.w m t x := by
    rw [Nat.sub_self]
    have hsqm : Real.sqrt (B.w m t x) * Real.sqrt (B.w m t x) = B.w m t x := by
      rw [← Real.sqrt_mul hwm_nonneg, Real.sqrt_mul_self hwm_nonneg]
    calc B.c * Real.sqrt (B.w m t x) * Real.sqrt (B.w 0 t x) * Real.sqrt (B.w m t x)
        = B.c * Real.sqrt (B.w 0 t x) * (Real.sqrt (B.w m t x) * Real.sqrt (B.w m t x)) := by ring
      _ = B.c * Real.sqrt (B.w 0 t x) * B.w m t x := by rw [hsqm]
      _ <= B.c * B.K * B.w m t x := by
          apply mul_le_mul_of_nonneg_right _ hwm_nonneg
          exact mul_le_mul_of_nonneg_left hsqrt_w0 B.hc
  -- Sum up.
  rw [towerReactionSum, sum_range_succ_split _ hm]
  have hmidsum :
      (∑ j ∈ Finset.Ico 1 m,
        B.c * Real.sqrt (B.w j t x) * Real.sqrt (B.w (m - j) t x) * Real.sqrt (B.w m t x)) <=
      (B.c * B.K * (1 / 2 * (B.K ^ 2 / t ^ m + B.w m t x))) *
        ∑ j ∈ Finset.Ico 1 m, C j * C (m - j) := by
    calc (∑ j ∈ Finset.Ico 1 m,
          B.c * Real.sqrt (B.w j t x) * Real.sqrt (B.w (m - j) t x) * Real.sqrt (B.w m t x))
        <= ∑ j ∈ Finset.Ico 1 m,
            B.c * (C j * C (m - j)) * B.K * (1 / 2 * (B.K ^ 2 / t ^ m + B.w m t x)) :=
          Finset.sum_le_sum hmid
      _ = (B.c * B.K * (1 / 2 * (B.K ^ 2 / t ^ m + B.w m t x))) *
            ∑ j ∈ Finset.Ico 1 m, C j * C (m - j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _; ring
  -- Combine the boundary and middle contributions.
  have hStop : towerBarTop B.c C m = 2 * B.c + B.c * (∑ j ∈ Finset.Ico 1 m, C j * C (m - j)) / 2 := by
    rw [towerBarTop]
  have hKtm_nonneg : 0 <= B.K ^ 2 / t ^ m := by positivity
  rw [hStop]
  -- Now a pure arithmetic inequality.
  set S : Real := ∑ j ∈ Finset.Ico 1 m, C j * C (m - j) with hS
  nlinarith [hbdry0, hbdrym, hmidsum, mul_nonneg (mul_nonneg B.hc (le_of_lt B.hK)) hKtm_nonneg,
    hwm_nonneg, hKtm_nonneg, B.hc, le_of_lt B.hK]

/-! ## The indexed Bernstein quantity `G` and the strong-induction estimate -/

/-- The coefficient of `sⁱ · w i` in the indexed Bernstein quantity at level `m`:
`1` at the top level `i = m`, and `β · (m−1)!/i!` at the lower levels `i < m`. -/
def Gcoef (B : BernsteinTower (I := I) G) (m i : ℕ) : Real :=
  if i = m then 1 else towerBeta B.c B.α (towerConst B.c B.α) m * towerFactCoeff m i

/-- The indexed Bernstein quantity
`G(s,y) = Σ_{i=0}^{m} Gcoef·sⁱ·(w i s y)` of Chow–Knopf eq (between 7.5 and 7.6),
written as a single `Finset.range (m+1)` sum. -/
def Gfun (B : BernsteinTower (I := I) G) (m : ℕ) (s : Real) (y : M) : Real :=
  ∑ i ∈ Finset.range (m + 1), Gcoef (I := I) B m i * s ^ i * B.w i s y

/-- The driftless heat operator of `Gfun B m t` splits linearly over the tower
levels: `Δ(G t) = Σ_i Gcoef·tⁱ·Δ(w i t)`. -/
theorem Gfun_heatOp (B : BernsteinTower (I := I) G) (m : ℕ)
    {t : Real} (hmem : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (x : M) :
    DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
        (fun _y : M => (0 : TangentSpace I _y)) (Gfun (I := I) B m t) x =
      ∑ i ∈ Finset.range (m + 1),
        (Gcoef (I := I) B m i * t ^ i) *
          DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
            (fun _y : M => (0 : TangentSpace I _y)) (B.w i t) x := by
  have hGfun_eq : (Gfun (I := I) B m t) =
      (fun y : M => ∑ i ∈ Finset.range (m + 1), (Gcoef (I := I) B m i * t ^ i) * B.w i t y) := by
    funext y
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hGfun_eq]
  exact heatOperator_linear_combo_finset (I := I) (Finset.range (m + 1)) G t
    (fun i => B.w i t) (fun i => Gcoef (I := I) B m i * t ^ i) x
    (fun i _ y => B.hw_space i t hmem htpos y)
    (fun i _ => B.hw_grad i t hmem htpos x)

/-- The time derivative of `s ↦ Gfun B m s x` at `t`, in terms of the per-level
time derivatives `dvec i` of `w i`. -/
theorem Gfun_hasDerivWithin (B : BernsteinTower (I := I) G) (m : ℕ)
    {t : Real} (_htmem : t ∈ Set.Icc 0 B.T) (_htpos : 0 < t) (x : M)
    (dvec : ℕ -> Real)
    (hd : ∀ i ∈ Finset.range (m + 1),
      HasDerivWithinAt (fun s : Real => B.w i s x) (dvec i) (Set.Icc 0 B.T) t) :
    HasDerivWithinAt (fun s : Real => Gfun (I := I) B m s x)
      (∑ i ∈ Finset.range (m + 1),
        Gcoef (I := I) B m i * ((i : Real) * t ^ (i - 1) * B.w i t x + t ^ i * dvec i))
      (Set.Icc 0 B.T) t := by
  have hfun : (fun s : Real => Gfun (I := I) B m s x) =
      ∑ i ∈ Finset.range (m + 1), (fun s : Real => Gcoef (I := I) B m i * s ^ i * B.w i s x) := by
    funext s
    rw [Finset.sum_apply]
    rfl
  rw [hfun]
  apply HasDerivWithinAt.sum
  intro i hi
  -- derivative of `s ↦ Gcoef i · s^i · w i s x`
  have hpow : HasDerivWithinAt (fun s : Real => s ^ i) ((i : Real) * t ^ (i - 1)) (Set.Icc 0 B.T) t := by
    simpa using (hasDerivWithinAt_id t (Set.Icc 0 B.T)).pow i
  have hprod : HasDerivWithinAt (fun s : Real => s ^ i * B.w i s x)
      ((i : Real) * t ^ (i - 1) * B.w i t x + t ^ i * dvec i) (Set.Icc 0 B.T) t :=
    hpow.mul (hd i hi)
  have := hprod.const_mul (Gcoef (I := I) B m i)
  refine this.congr_of_eventuallyEq ?_ ?_
  · filter_upwards with s using by simp [mul_assoc]
  · simp [mul_assoc]

/-- The parabolic operator of `Gfun B m`, in terms of the per-level time
derivatives `dvec` (with `wLap` realizing the per-level Laplacians):
`(∂ₜ − Δ)G = Σ_i Gcoef·i·tⁱ⁻¹·(w i) + Σ_i Gcoef·tⁱ·(dvecᵢ − wLap i)`. -/
theorem Gfun_parabolic_eq (B : BernsteinTower (I := I) G) (m : ℕ)
    {t : Real} (htmem : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (x : M)
    (dvec : ℕ -> Real)
    (hd : ∀ i ∈ Finset.range (m + 1),
      HasDerivWithinAt (fun s : Real => B.w i s x) (dvec i) (Set.Icc 0 B.T) t) :
    DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G B.T
        (fun _t x => (0 : TangentSpace I x)) (Gfun (I := I) B m) t x =
      (∑ i ∈ Finset.range (m + 1),
          Gcoef (I := I) B m i * ((i : Real) * t ^ (i - 1) * B.w i t x)) +
        ∑ i ∈ Finset.range (m + 1),
          Gcoef (I := I) B m i * t ^ i * (dvec i - B.wLap i t x) := by
  have htime :
      derivWithin (fun s : Real => Gfun (I := I) B m s x) (Set.Icc 0 B.T) t =
        ∑ i ∈ Finset.range (m + 1),
          Gcoef (I := I) B m i * ((i : Real) * t ^ (i - 1) * B.w i t x + t ^ i * dvec i) := by
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 B.T) t :=
      (uniqueDiffOn_Icc B.hT).uniqueDiffWithinAt htmem
    exact (Gfun_hasDerivWithin (I := I) B m htmem htpos x dvec hd).derivWithin huniq
  rw [DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift_eq, htime]
  rw [Gfun_heatOp (I := I) B m htmem htpos x]
  -- combine the two sums termwise
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [B.hLap i t htmem htpos x]
  ring

/-- **Telescoping core.**  The `w`-dependent part of `(∂ₜ−Δ)G`, after substituting
the reaction bounds (7.5)/(7.6), is nonpositive.  This packages the factorial
identity `k·a_k = a_{k−1}` and the choice `β = towerBeta`. -/
theorem Wterms_nonpos (B : BernsteinTower (I := I) G) {m : ℕ} (hm : 1 <= m)
    {t : Real} (htmem : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (htK : t * B.K <= B.α) (x : M) :
    (∑ i ∈ Finset.range (m + 1),
        Gcoef (I := I) B m i * ((i : Real) * t ^ (i - 1) * B.w i t x)) +
      towerBarTop B.c (towerConst B.c B.α) m * B.K * (t ^ m * B.w m t x) -
        2 * towerBeta B.c B.α (towerConst B.c B.α) m *
          (∑ i ∈ Finset.range m,
            towerFactCoeff m i * t ^ i * B.w (i + 1) t x) <= 0 := by
  classical
  set C : ℕ -> Real := towerConst B.c B.α with hC
  set β : Real := towerBeta B.c B.α C m with hβ
  set bt : Real := towerBarTop B.c C m with hbt
  have hβ_nonneg : 0 <= β := towerBeta_nonneg B.hc B.hα m
  have hbt_nonneg : 0 <= bt := towerBarTop_nonneg B.hc B.α m
  have hht : (0 : Real) <= t := le_of_lt htpos
  have hwnn : ∀ i, 0 <= B.w i t x := fun i => B.hw_nonneg i t htmem x
  -- Reindex the first sum to `Finset.Icc 1 m` (the `i = 0` term vanishes).
  have hIcc_eq : Finset.Ico 1 (m + 1) = Finset.Icc 1 m := by
    ext j; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  have hS1 :
      (∑ i ∈ Finset.range (m + 1),
          Gcoef (I := I) B m i * ((i : Real) * t ^ (i - 1) * B.w i t x)) =
        ∑ k ∈ Finset.Icc 1 m, Gcoef (I := I) B m k * ((k : Real) * t ^ (k - 1) * B.w k t x) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < m + 1)]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
    rw [hIcc_eq]
  -- Reindex the third sum to `Finset.Icc 1 m` via `i ↦ i + 1`.
  have hS3 :
      (∑ i ∈ Finset.range m, towerFactCoeff m i * t ^ i * B.w (i + 1) t x) =
        ∑ k ∈ Finset.Icc 1 m, towerFactCoeff m (k - 1) * t ^ (k - 1) * B.w k t x := by
    rw [← hIcc_eq, Finset.sum_Ico_eq_sum_range]
    rw [show m + 1 - 1 = m from by omega]
    apply Finset.sum_congr rfl
    intro i _
    rw [show 1 + i - 1 = i from by omega, show 1 + i = i + 1 from by omega]
  rw [hS1, hS3]
  -- Combine the two `Icc 1 m` sums into one (using `2β·Σ = Σ 2β·`).
  have hcombine :
      (∑ k ∈ Finset.Icc 1 m, Gcoef (I := I) B m k * ((k : Real) * t ^ (k - 1) * B.w k t x)) -
        2 * β * (∑ k ∈ Finset.Icc 1 m, towerFactCoeff m (k - 1) * t ^ (k - 1) * B.w k t x) =
      ∑ k ∈ Finset.Icc 1 m,
        (Gcoef (I := I) B m k * ((k : Real) * t ^ (k - 1) * B.w k t x) -
          2 * β * (towerFactCoeff m (k - 1) * t ^ (k - 1) * B.w k t x)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- rearrange the goal so the two sums are adjacent.
  rw [show (∑ k ∈ Finset.Icc 1 m, Gcoef (I := I) B m k * ((k : Real) * t ^ (k - 1) * B.w k t x)) +
        bt * B.K * (t ^ m * B.w m t x) -
        2 * β * (∑ k ∈ Finset.Icc 1 m, towerFactCoeff m (k - 1) * t ^ (k - 1) * B.w k t x) =
      ((∑ k ∈ Finset.Icc 1 m, Gcoef (I := I) B m k * ((k : Real) * t ^ (k - 1) * B.w k t x)) -
        2 * β * (∑ k ∈ Finset.Icc 1 m, towerFactCoeff m (k - 1) * t ^ (k - 1) * B.w k t x)) +
        bt * B.K * (t ^ m * B.w m t x) from by ring]
  rw [hcombine]
  -- split off the top index `k = m`.
  have hmIcc : m ∈ Finset.Icc 1 m := by simp only [Finset.mem_Icc]; omega
  rw [← Finset.sum_erase_add _ _ hmIcc]
  -- coefficient identities
  have ham : towerFactCoeff m (m - 1) = 1 := by
    rw [towerFactCoeff]
    rw [div_self (by exact_mod_cast (Nat.factorial_pos (m - 1)).ne')]
  have hGm : Gcoef (I := I) B m m = 1 := by rw [Gcoef]; simp
  -- middle terms (k ∈ Icc 1 m with k ≠ m, i.e. 1 ≤ k < m): coefficient is `-β·a_{k-1} ≤ 0`.
  have hmid : ∀ k ∈ (Finset.Icc 1 m).erase m,
      Gcoef (I := I) B m k * ((k : Real) * t ^ (k - 1) * B.w k t x) -
        2 * β * (towerFactCoeff m (k - 1) * t ^ (k - 1) * B.w k t x) <= 0 := by
    intro k hk
    have hkne : k ≠ m := Finset.ne_of_mem_erase hk
    have hkmem : k ∈ Finset.Icc 1 m := Finset.mem_of_mem_erase hk
    simp only [Finset.mem_Icc] at hkmem
    have hkm : k < m := by omega
    have hk1 : 1 <= k := hkmem.1
    have hGk : Gcoef (I := I) B m k = β * towerFactCoeff m k := by
      rw [Gcoef, if_neg (by omega : ¬ k = m)]
    rw [hGk]
    -- `k · a_k = a_{k-1}`, so `β·a_k·k − 2β·a_{k-1} = −β·a_{k-1} ≤ 0`.
    have hfac : (k : Real) * towerFactCoeff m k = towerFactCoeff m (k - 1) :=
      nat_mul_towerFactCoeff m hk1
    have hcoef :
        β * towerFactCoeff m k * ((k : Real) * t ^ (k - 1) * B.w k t x) -
          2 * β * (towerFactCoeff m (k - 1) * t ^ (k - 1) * B.w k t x) =
        (- β * towerFactCoeff m (k - 1)) * (t ^ (k - 1) * B.w k t x) := by
      have : β * towerFactCoeff m k * ((k : Real) * t ^ (k - 1) * B.w k t x) =
          β * ((k : Real) * towerFactCoeff m k) * (t ^ (k - 1) * B.w k t x) := by ring
      rw [this, hfac]; ring
    rw [hcoef]
    apply mul_nonpos_of_nonpos_of_nonneg
    · have := towerFactCoeff_nonneg m (k - 1)
      nlinarith [hβ_nonneg, this]
    · exact mul_nonneg (pow_nonneg hht (k - 1)) (hwnn k)
  -- the middle sum is ≤ 0.
  have hmidsum :
      (∑ k ∈ (Finset.Icc 1 m).erase m,
        (Gcoef (I := I) B m k * ((k : Real) * t ^ (k - 1) * B.w k t x) -
          2 * β * (towerFactCoeff m (k - 1) * t ^ (k - 1) * B.w k t x))) <= 0 :=
    Finset.sum_nonpos hmid
  -- the top term (k = m) plus the `bt·K·t^m·w m` term is ≤ 0.
  have htop :
      (Gcoef (I := I) B m m * ((m : Real) * t ^ (m - 1) * B.w m t x) -
        2 * β * (towerFactCoeff m (m - 1) * t ^ (m - 1) * B.w m t x)) +
        bt * B.K * (t ^ m * B.w m t x) <= 0 := by
    rw [hGm, ham, one_mul, one_mul]
    -- `(m − 2β + bt·K·t)·t^{m-1}·w m ≤ 0`, using `2β = bt·α + m` and `K·t ≤ α`.
    have htfac : t ^ m = t * t ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h2β : 2 * β = bt * B.α + (m : Real) := by
      rw [hβ, towerBeta]; rw [← hbt]; ring
    have hwtm_nonneg : 0 <= t ^ (m - 1) * B.w m t x :=
      mul_nonneg (pow_nonneg hht (m - 1)) (hwnn m)
    have hcoef_nonpos : (m : Real) - 2 * β + bt * B.K * t <= 0 := by
      rw [h2β]
      have hbtKt : bt * (B.K * t) <= bt * B.α := by
        apply mul_le_mul_of_nonneg_left _ hbt_nonneg
        rw [mul_comm]; exact htK
      nlinarith [hbtKt]
    have hrewrite :
        (m : Real) * t ^ (m - 1) * B.w m t x -
          2 * β * (t ^ (m - 1) * B.w m t x) + bt * B.K * (t ^ m * B.w m t x) =
        ((m : Real) - 2 * β + bt * B.K * t) * (t ^ (m - 1) * B.w m t x) := by
      rw [htfac]; ring
    rw [hrewrite]
    exact mul_nonpos_of_nonpos_of_nonneg hcoef_nonpos hwtm_nonneg
  -- assemble.
  linarith [hmidsum, htop]

/-- **Bernstein–Bando–Shi higher derivative estimate (parametric core).**

For a uniform derivative tower on a closed manifold, every level satisfies the
on-diagonal bound `tᵐ · w m ≤ (towerConst c α m)² · K²` on positive times of the
slab `[0,T]`, where `towerConst c α m` depends only on `m`, `α` and the tower
constant `c`.  Equivalently `w m (t,x) ≤ (towerConst c α m)² K² / tᵐ`. -/
theorem estimate (B : BernsteinTower (I := I) G) :
    ∀ m : ℕ, ∀ t : Real, t ∈ Set.Icc 0 B.T -> 0 < t -> ∀ x : M,
      t ^ m * B.w m t x <= (towerConst B.c B.α m) ^ 2 * B.K ^ 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- base case `m = 0`
      subst hm0
      intro t htmem htpos x
      simp only [pow_zero, one_mul, towerConst_zero, one_pow]
      exact B.hw0_bound t htmem x
    · -- inductive step `m ≥ 1`
      classical
      set C : ℕ -> Real := towerConst B.c B.α with hC
      set β : Real := towerBeta B.c B.α C m with hβ
      have hβ_nonneg : 0 <= β := towerBeta_nonneg B.hc B.hα m
      set bt : Real := towerBarTop B.c C m with hbt
      have hbt_nonneg : 0 <= bt := towerBarTop_nonneg B.hc B.α m
      -- The barrier data.
      set aBar : Real := β * (Nat.factorial (m - 1) : Real) * B.K ^ 2 with haBar
      set bBar : Real :=
        (bt + β * ∑ i ∈ Finset.range m, towerFactCoeff m i * towerBarGood B.c C i) * B.K ^ 3
        with hbBar
      -- helper: `t' * K ≤ α` on the slab
      have htK_slab : ∀ s : Real, s ∈ Set.Icc 0 B.T -> s * B.K <= B.α := by
        intro s hs
        have hsle : s <= B.α / B.K := le_trans hs.2 B.hTK
        calc s * B.K <= (B.α / B.K) * B.K := mul_le_mul_of_nonneg_right hsle (le_of_lt B.hK)
          _ = B.α := div_mul_cancel₀ B.α (ne_of_gt B.hK)
      -- ===== The subsolution inequality `(∂ₜ−Δ)G ≤ bBar` at positive times. =====
      have hsub : ∀ s : Real, s ∈ Set.Icc 0 B.T -> 0 < s -> ∀ y : M,
          DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G B.T
            (fun _t x => (0 : TangentSpace I x)) (Gfun (I := I) B m) s y <= bBar := by
        intro s hsmem hspos y
        -- regular-time wrapper
        let τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime B.D :=
          ⟨s, B.hregular s hsmem hspos⟩
        -- per-level derivatives via choice
        set dvec : ℕ -> Real := fun i => Classical.choose (B.hheat i τ y) with hdvec
        have hspec : ∀ i : ℕ,
            HasDerivWithinAt (fun r : Real => B.w i r y) (dvec i) B.D.carrier s ∧
            dvec i <= B.wLap i s y +
              (-2 * B.w (i + 1) s y + towerReactionSum (M := M) B.w B.c i s y) := by
          intro i
          have := Classical.choose_spec (B.hheat i τ y)
          simpa [hdvec, τ] using this
        -- restrict derivatives to the slab
        have hd : ∀ i ∈ Finset.range (m + 1),
            HasDerivWithinAt (fun r : Real => B.w i r y) (dvec i) (Set.Icc 0 B.T) s :=
          fun i _ => (hspec i).1.mono B.hslab
        -- IH at `(s, y)`, division-free form.
        have hIHs : ∀ j, j < m -> s ^ j * B.w j s y <= (C j) ^ 2 * B.K ^ 2 :=
          fun j hj => by simpa [hC] using IH j hj s hsmem hspos y
        -- compute the parabolic operator
        rw [Gfun_parabolic_eq (I := I) B m hsmem hspos y dvec hd]
        have hht : (0 : Real) <= s := le_of_lt hspos
        have htm_pos : 0 < s ^ m := pow_pos hspos m
        -- split the second sum at the top level `i = m`.
        have hsplit2 :
            (∑ i ∈ Finset.range (m + 1),
                Gcoef (I := I) B m i * s ^ i * (dvec i - B.wLap i s y)) =
              (∑ i ∈ Finset.range m,
                Gcoef (I := I) B m i * s ^ i * (dvec i - B.wLap i s y)) +
                Gcoef (I := I) B m m * s ^ m * (dvec m - B.wLap m s y) :=
          Finset.sum_range_succ _ m
        -- IH in `≤ k` form, for the reaction lemmas.
        have hIHle : ∀ k, k < m -> ∀ j, j <= k -> s ^ j * B.w j s y <= (C j) ^ 2 * B.K ^ 2 :=
          fun k hk j hj => hIHs j (lt_of_le_of_lt hj hk)
        -- (7.5): top-level reaction bound, in division form.
        have hR75 : B.wLap m s y + (-2 * B.w (m + 1) s y + towerReactionSum (M := M) B.w B.c m s y) -
            B.wLap m s y <= bt * B.K * (B.w m s y + B.K ^ 2 / s ^ m) := by
          have hreact := reactionSum_top_le (I := I) B hmpos hspos hsmem
            (fun j hj => hIHs j hj)
          rw [← hC, ← hbt] at hreact
          have hneg : -2 * B.w (m + 1) s y <= 0 := by
            have := B.hw_nonneg (m + 1) s hsmem y; linarith
          linarith
        -- top-level term, after multiplying by `s^m`.
        have htop_le :
            Gcoef (I := I) B m m * s ^ m * (dvec m - B.wLap m s y) <=
              bt * B.K * (s ^ m * B.w m s y) + bt * B.K ^ 3 := by
          have hPm : dvec m - B.wLap m s y <= bt * B.K * (B.w m s y + B.K ^ 2 / s ^ m) := by
            have hb := (hspec m).2
            calc dvec m - B.wLap m s y
                <= (B.wLap m s y + (-2 * B.w (m + 1) s y + towerReactionSum (M := M) B.w B.c m s y))
                    - B.wLap m s y := by linarith
              _ <= bt * B.K * (B.w m s y + B.K ^ 2 / s ^ m) := hR75
          have hGm : Gcoef (I := I) B m m = 1 := by rw [Gcoef]; simp
          rw [hGm, one_mul]
          have hsm_nonneg : (0 : Real) <= s ^ m := le_of_lt htm_pos
          calc s ^ m * (dvec m - B.wLap m s y)
              <= s ^ m * (bt * B.K * (B.w m s y + B.K ^ 2 / s ^ m)) :=
                mul_le_mul_of_nonneg_left hPm hsm_nonneg
            _ = bt * B.K * (s ^ m * B.w m s y) + bt * B.K ^ 3 := by
                field_simp
        -- per-term bound on the lower-level terms via (7.6).
        have hmid_term : ∀ i ∈ Finset.range m,
            Gcoef (I := I) B m i * s ^ i * (dvec i - B.wLap i s y) <=
              β * towerFactCoeff m i * (-2 * (s ^ i * B.w (i + 1) s y)) +
                β * towerFactCoeff m i * towerBarGood B.c C i * B.K ^ 3 := by
          intro i hi
          have him : i < m := Finset.mem_range.mp hi
          have hGi : Gcoef (I := I) B m i = β * towerFactCoeff m i := by
            rw [Gcoef, if_neg (by omega : ¬ i = m)]
          -- `s^i · reactionSum_i ≤ barGood_i K³`
          have hR76 := tpow_mul_reactionSum_le (I := I) B i hspos (fun j hj => hIHle i him j hj)
          rw [← hC] at hR76
          -- `P_i ≤ −2 w(i+1) + reactionSum_i`
          have hPi : dvec i - B.wLap i s y <=
              -2 * B.w (i + 1) s y + towerReactionSum (M := M) B.w B.c i s y := by
            have := (hspec i).2; linarith
          have hcoef_nonneg : 0 <= β * towerFactCoeff m i :=
            mul_nonneg hβ_nonneg (towerFactCoeff_nonneg _ _)
          have hsi_nonneg : (0 : Real) <= s ^ i := pow_nonneg hht i
          rw [hGi]
          calc β * towerFactCoeff m i * s ^ i * (dvec i - B.wLap i s y)
              = (β * towerFactCoeff m i) * (s ^ i * (dvec i - B.wLap i s y)) := by ring
            _ <= (β * towerFactCoeff m i) *
                  (s ^ i * (-2 * B.w (i + 1) s y + towerReactionSum (M := M) B.w B.c i s y)) := by
                apply mul_le_mul_of_nonneg_left _ hcoef_nonneg
                exact mul_le_mul_of_nonneg_left hPi hsi_nonneg
            _ = (β * towerFactCoeff m i) *
                  (-2 * (s ^ i * B.w (i + 1) s y)) +
                (β * towerFactCoeff m i) * (s ^ i * towerReactionSum (M := M) B.w B.c i s y) := by ring
            _ <= (β * towerFactCoeff m i) * (-2 * (s ^ i * B.w (i + 1) s y)) +
                  (β * towerFactCoeff m i) * (towerBarGood B.c C i * B.K ^ 3) := by
                have := mul_le_mul_of_nonneg_left hR76 hcoef_nonneg
                linarith
            _ = β * towerFactCoeff m i * (-2 * (s ^ i * B.w (i + 1) s y)) +
                  β * towerFactCoeff m i * towerBarGood B.c C i * B.K ^ 3 := by ring
        have hmid_le :
            (∑ i ∈ Finset.range m,
              Gcoef (I := I) B m i * s ^ i * (dvec i - B.wLap i s y)) <=
              -2 * β * (∑ i ∈ Finset.range m, towerFactCoeff m i * s ^ i * B.w (i + 1) s y) +
                β * (∑ i ∈ Finset.range m, towerFactCoeff m i * towerBarGood B.c C i) * B.K ^ 3 := by
          calc (∑ i ∈ Finset.range m,
              Gcoef (I := I) B m i * s ^ i * (dvec i - B.wLap i s y))
              <= ∑ i ∈ Finset.range m,
                  (β * towerFactCoeff m i * (-2 * (s ^ i * B.w (i + 1) s y)) +
                    β * towerFactCoeff m i * towerBarGood B.c C i * B.K ^ 3) :=
                Finset.sum_le_sum hmid_term
            _ = -2 * β * (∑ i ∈ Finset.range m, towerFactCoeff m i * s ^ i * B.w (i + 1) s y) +
                  β * (∑ i ∈ Finset.range m, towerFactCoeff m i * towerBarGood B.c C i) * B.K ^ 3 := by
                rw [Finset.sum_add_distrib]
                congr 1
                · rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl; intro i _; ring
                · rw [Finset.mul_sum, Finset.sum_mul]
                  apply Finset.sum_congr rfl; intro i _; ring
        -- assemble: parabolicOp = sum1 + (mid + top) ≤ Wterms + bBar ≤ bBar.
        rw [hsplit2]
        have hWnonpos := Wterms_nonpos (I := I) B hmpos hsmem hspos (htK_slab s hsmem) y
        rw [← hC, ← hbt, ← hβ] at hWnonpos
        -- expand `bBar` into a sum of products that `linarith` can use.
        have hbBar' : bBar =
            bt * B.K ^ 3 +
              β * (∑ i ∈ Finset.range m, towerFactCoeff m i * towerBarGood B.c C i) * B.K ^ 3 := by
          rw [hbBar]; ring
        rw [hbBar']
        linarith [hmid_le, htop_le, hWnonpos]
      -- ===== Regularity of `Gfun` (for the maximum principle). =====
      -- Each level's gradient/spatial differentiability transfers to the sum.
      have hGspace : ∀ s : Real, s ∈ Set.Icc 0 B.T -> 0 < s -> ∀ y : M,
          MDifferentiableAt I 𝓘(Real, Real) (Gfun (I := I) B m s) y := by
        intro s hsmem hspos y
        have heq : (Gfun (I := I) B m s) =
            (fun z : M => ∑ i ∈ Finset.range (m + 1), (Gcoef (I := I) B m i * s ^ i) * B.w i s z) := by
          funext z; rw [Gfun]
        rw [heq]
        exact mdifferentiableAt_finset_sum_smul (I := I) (Finset.range (m + 1))
          (fun i => B.w i s) (fun i => Gcoef (I := I) B m i * s ^ i) y
          (fun i _ => B.hw_space i s hsmem hspos y)
      have hGgrad : ∀ s : Real, s ∈ Set.Icc 0 B.T -> 0 < s -> ∀ y : M,
          MDiffAt (T% fun z : M =>
            DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric s)
              (Gfun (I := I) B m s) z) y := by
        intro s hsmem hspos y
        have heq : (Gfun (I := I) B m s) =
            (fun z : M => ∑ i ∈ Finset.range (m + 1), (Gcoef (I := I) B m i * s ^ i) * B.w i s z) := by
          funext z; rw [Gfun]
        rw [heq]
        exact mdiffAt_gradientFun_finset_sum_smul (I := I) (Finset.range (m + 1)) G s
          (fun i => B.w i s) (fun i => Gcoef (I := I) B m i * s ^ i) y
          (fun i _ z => B.hw_space i s hsmem hspos z)
          (fun i _ => B.hw_grad i s hsmem hspos y)
      have hGtime : ∀ s : Real, s ∈ Set.Icc 0 B.T -> 0 < s -> ∀ y : M,
          DifferentiableWithinAt Real (fun r : Real => Gfun (I := I) B m r y) (Set.Icc 0 B.T) s := by
        intro s hsmem hspos y
        let τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime B.D :=
          ⟨s, B.hregular s hsmem hspos⟩
        set dvec : ℕ -> Real := fun i => Classical.choose (B.hheat i τ y) with hdvec
        have hd : ∀ i ∈ Finset.range (m + 1),
            HasDerivWithinAt (fun r : Real => B.w i r y) (dvec i) (Set.Icc 0 B.T) s := by
          intro i _
          have := (Classical.choose_spec (B.hheat i τ y)).1
          exact (by simpa [hdvec, τ] using this : HasDerivWithinAt (fun r : Real => B.w i r y) (dvec i) B.D.carrier s).mono B.hslab
        exact (Gfun_hasDerivWithin (I := I) B m hsmem hspos y dvec hd).differentiableWithinAt
      -- continuity of the barrier on the slab
      have hGcont : ContinuousOn
          (fun p : Real × M =>
            (aBar + bBar * p.1) - Gfun (I := I) B m p.1 p.2)
          (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) B.T) := by
        apply ContinuousOn.sub
        · exact (continuous_const.add (continuous_const.mul continuous_fst)).continuousOn
        · -- `Gfun p.1 p.2 = Σ_i Gcoef·p.1^i·(w i p.1 p.2)`
          have heq : (fun p : Real × M => Gfun (I := I) B m p.1 p.2) =
              (fun p : Real × M =>
                ∑ i ∈ Finset.range (m + 1),
                  Gcoef (I := I) B m i * p.1 ^ i * B.w i p.1 p.2) := by
            funext p; rw [Gfun]
          rw [heq]
          apply continuousOn_finset_sum
          intro i _
          apply ContinuousOn.mul
          · exact ((continuous_const.mul (continuous_fst.pow i)).continuousOn)
          · exact B.hw_cont i
      -- ===== Apply the maximum principle. =====
      have hPartA : ∀ s : Real, s ∈ Set.Icc 0 B.T -> ∀ y : M,
          Gfun (I := I) B m s y <= aBar + bBar * s := by
        apply scalar_subsolution_affine_bound (I := I) G B.T (le_of_lt B.hT)
          (fun _t x => (0 : TangentSpace I x)) (Gfun (I := I) B m) aBar bBar hGcont
          (fun s hs hsp y => hGtime s hs hsp y)
          (fun s hs hsp y => hGspace s hs hsp y)
          (fun s hs hsp y => hGgrad s hs hsp y)
        · -- initial bound `Gfun 0 y ≤ aBar`
          intro y
          have h0 : Gfun (I := I) B m 0 y =
              Gcoef (I := I) B m 0 * B.w 0 0 y := by
            rw [Gfun]
            rw [Finset.sum_eq_single 0]
            · simp
            · intro i _ hi0
              rcases Nat.eq_zero_or_pos i with h | h
              · exact absurd h hi0
              · simp [zero_pow (by omega : i ≠ 0)]
            · intro h; simp at h
          rw [h0, haBar]
          have hGc0 : Gcoef (I := I) B m 0 = β * (Nat.factorial (m - 1) : Real) := by
            rw [Gcoef, if_neg (by omega : ¬ (0 : ℕ) = m), towerFactCoeff]
            rw [Nat.factorial_zero, Nat.cast_one, div_one, ← hC, ← hβ]
          rw [hGc0]
          have h0mem : (0 : Real) ∈ Set.Icc 0 B.T := ⟨le_rfl, le_of_lt B.hT⟩
          have hw00 : B.w 0 0 y <= B.K ^ 2 := B.hw0_bound 0 h0mem y
          have hcoef_nn : 0 <= β * (Nat.factorial (m - 1) : Real) := by positivity
          calc β * (Nat.factorial (m - 1) : Real) * B.w 0 0 y
              <= β * (Nat.factorial (m - 1) : Real) * B.K ^ 2 :=
                mul_le_mul_of_nonneg_left hw00 hcoef_nn
            _ = β * (Nat.factorial (m - 1) : Real) * B.K ^ 2 := rfl
        · exact hsub
      -- ===== Extract `t^m · w m`. =====
      intro t htmem htpos x
      -- `t^m w m ≤ Gfun t x` since the other terms are nonnegative.
      have hwm_le_G : t ^ m * B.w m t x <= Gfun (I := I) B m t x := by
        rw [Gfun]
        have hmem' : m ∈ Finset.range (m + 1) := by simp
        rw [← Finset.sum_erase_add _ _ hmem']
        have hGm : Gcoef (I := I) B m m * t ^ m * B.w m t x = t ^ m * B.w m t x := by
          rw [Gcoef]; simp
        rw [hGm]
        have hrest : 0 <= ∑ i ∈ (Finset.range (m + 1)).erase m,
            Gcoef (I := I) B m i * t ^ i * B.w i t x := by
          apply Finset.sum_nonneg
          intro i hi
          have him : i ∈ Finset.range (m + 1) := Finset.mem_of_mem_erase hi
          have hine : i ≠ m := Finset.ne_of_mem_erase hi
          have hGci : 0 <= Gcoef (I := I) B m i := by
            rw [Gcoef, if_neg hine]
            exact mul_nonneg hβ_nonneg (towerFactCoeff_nonneg _ _)
          have : 0 <= t ^ i := pow_nonneg (le_of_lt htpos) i
          have : 0 <= B.w i t x := B.hw_nonneg i t htmem x
          positivity
        linarith
      -- `aBar + bBar t ≤ towerConstSq · K²`
      have hfinal : aBar + bBar * t <= towerConstSq B.c B.α m * B.K ^ 2 := by
        rw [towerConstSq_pos B.c B.α hmpos, haBar, hbBar, ← hβ, ← hC, ← hbt]
        have htK : t * B.K <= B.α := htK_slab t htmem
        have hbBarnn : 0 <= (bt + β * ∑ i ∈ Finset.range m, towerFactCoeff m i * towerBarGood B.c C i) := by
          have hsum : 0 <= ∑ i ∈ Finset.range m, towerFactCoeff m i * towerBarGood B.c C i := by
            apply Finset.sum_nonneg; intro i _
            exact mul_nonneg (towerFactCoeff_nonneg _ _) (towerBarGood_nonneg B.hc B.α i)
          positivity
        have hKnn : (0 : Real) <= B.K ^ 2 := by positivity
        -- bBar·t = (..)·K³·t = (..)·K²·(K·t) ≤ (..)·K²·α
        nlinarith [hbBarnn, hKnn, htK, mul_nonneg hbBarnn hKnn]
      have hGle : Gfun (I := I) B m t x <= aBar + bBar * t := hPartA t htmem x
      rw [towerConst_sq B.hc B.hα]
      linarith [hwm_le_G, hGle, hfinal]

/-- **Bernstein–Bando–Shi higher derivative estimate, divided form.**

The on-diagonal bound in the textbook shape `w m (t,x) ≤ (towerConst c α m)² K²/tᵐ`
for `t ∈ (0,T]`, an immediate corollary of `estimate`. -/
theorem estimate_div (B : BernsteinTower (I := I) G)
    (m : ℕ) {t : Real} (htmem : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (x : M) :
    B.w m t x <= (towerConst B.c B.α m) ^ 2 * B.K ^ 2 / t ^ m := by
  rw [le_div_iff₀ (pow_pos htpos m)]
  calc B.w m t x * t ^ m = t ^ m * B.w m t x := by ring
    _ <= (towerConst B.c B.α m) ^ 2 * B.K ^ 2 := B.estimate m t htmem htpos x

end BernsteinTower

end DifferentialGeometry.PDE.RicciFlow
