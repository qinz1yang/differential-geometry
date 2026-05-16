import RicciFlower.Analysis.Volume.ChartDensity
import RicciFlower.Analysis.Volume.Glue
import RicciFlower.Analysis.Volume.Invariance
import RicciFlower.Analysis.Volume.Properties
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Compactness.LocallyFinite

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Time-parameterised Riemannian volume measure and Jacobi formula for the density

Given a smoothly-time-parameterised Riemannian metric family
`g_fam : ℝ → SmoothRiemannianMetric I M`, we define the associated family of
Riemannian volume measures and prove the pointwise time-derivative of the
chart-local density via Jacobi's formula for the determinant.

## Main definitions

* `riemannianMeasureFamily g_fam` : the family `t ↦ riemannianVolumeMeasure (g_fam t)`.
* `MetricFamilyRegularAt g_fam t₀` : the pointwise regularity interface used by
  the volume variation machinery (pointwise `HasDerivAt` + joint continuity on
  chart base sets — no joint smoothness).
* `FunctionRegularAt f t₀` : the analogous interface for a scalar integrand.
* `traceTimeDerivMetric g_fam t x` : the intrinsic metric trace `tr_g(∂_t g)(x)`,
  computed in the canonical chart at `x`.

## Main results

* `hasDerivAt_det_of_entries` : derivative of `det ∘ G(t)` in the parameter `t`,
  expressed as the canonical permutation-sum form coming from `Matrix.det_apply'`.
* `perm_sum_eq_trace_adjugate_mul` : the permutation sum above equals
  `trace (adjugate A · B)`.
* `hasDerivAt_det_eq_trace_adjugate_mul` : Jacobi's formula in the form
  `d/dt det G(t) = trace (adjugate (G t) · G'(t))`.
* `hasDerivAt_det_eq_det_mul_trace_inv_mul` : the classical form
  `d/dt det G(t) = det(G t) · trace(G(t)⁻¹ · G'(t))` when `(G t).det` is a unit.
* `hasDerivAt_sqrt_det_of_entries` : derivative of `√(det G(t))` via chain rule.
* `hasDerivAt_sqrt_det_eq_half_trace_inv_mul` : the geometric form
  `d/dt √(det G(t)) = ½ · trace(G(t)⁻¹ · G'(t)) · √(det G(t))` under positivity.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace RicciFlower
namespace Analysis
namespace Volume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Canonical measurable-space and Borel-space instances on `E` and `M`

File-local canonical Borel structures, matching those in the other `Measure` files.
Declared `local` so they do not pollute external typeclass search. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The time-parameterised Riemannian volume measure -/

/-- Given a smoothly-time-parameterised Riemannian metric family, the associated
family of Riemannian volume measures on `M`. -/
def riemannianMeasureFamily
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) : ℝ → MeasureTheory.Measure M :=
  fun t => riemannianVolumeMeasure (I := I) (M := M) (g_fam t)

/-- Unfolding lemma for the time-parameterised Riemannian volume measure. -/
lemma riemannianMeasureFamily_def
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) :
    riemannianMeasureFamily (I := I) (M := M) g_fam t =
      riemannianVolumeMeasure (I := I) (M := M) (g_fam t) := rfl

/-! ## Weak regularity interfaces for time-varying metric families

Rather than committing to a joint-smoothness hypothesis on `(t, x) ↦ g_t(x)`, the
volume-variation machinery below is phrased in terms of two minimal interfaces:

* `MetricFamilyRegularAt g_fam t₀` — encapsulates, for a family of Riemannian
  metrics `g_fam : ℝ → SmoothRiemannianMetric I M` and a base time `t₀`,
  exactly the pointwise-in-time differentiability plus joint `(t, x)`-continuity
  data required. No joint smoothness in `(t, x)` is imposed at this level.

* `FunctionRegularAt f t₀` — the analogue for a time-varying function
  `f : ℝ → M → ℝ`.

Downstream users with a genuinely jointly-smooth family may package the required
regularity via a thin separate bridge file; the engine itself sees only the two
interfaces above. -/

/-- Minimum regularity interface for a time-varying Riemannian metric family at a
base time. Encapsulates exactly the pointwise time-differentiability and joint
`(t, x)`-continuity required by the volume-variation formula.

Note: the first field asserts differentiability at every time `t`, not just `t₀`.
The parametric-integral theorem used downstream requires the time-derivative to
exist in a neighbourhood of `t₀`, and supplying it at every time is the natural
minimal strengthening (and is automatic for any family arising from a smooth
Ricci-flow solution or any other jointly-smooth source). -/
structure MetricFamilyRegularAt
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t₀ : ℝ) : Prop where
  /-- Each chart-local Gram-matrix entry is time-differentiable at every time,
  per base point in the chart base set. -/
  hasDerivAt_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)) {x : M},
      x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j)
          (deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) t
  /-- Joint `(t, x)` continuity of each chart-local Gram-matrix entry on
  `Set.univ ×ˢ (trivializationAt ... x₀).baseSet`. -/
  continuousOn_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
  /-- Joint `(t, x)` continuity of the time-derivative of each chart-local
  Gram-matrix entry on `Set.univ ×ˢ (trivializationAt ... x₀).baseSet`. -/
  continuousOn_deriv_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ p.2 i j) p.1)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)

/-- The regularity interface is time-agnostic: its fields depend on the base
time only as an existential quantifier parameter. So `MetricFamilyRegularAt g_fam t`
yields `MetricFamilyRegularAt g_fam s` for any other time `s` trivially. -/
lemma MetricFamilyRegularAt.at_any
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (s : ℝ) :
    MetricFamilyRegularAt (I := I) g_fam s :=
  { hasDerivAt_chartGramMatrix := hreg.hasDerivAt_chartGramMatrix
    continuousOn_chartGramMatrix := hreg.continuousOn_chartGramMatrix
    continuousOn_deriv_chartGramMatrix := hreg.continuousOn_deriv_chartGramMatrix }

/-- If an explicit time derivative agrees with `HasDerivAt` on a spacetime
domain and is continuous there, then the classical `deriv` expression is
continuous on the same domain. -/
theorem continuousOn_deriv_of_hasDerivAt_eq_continuousOn
    {α : Type*} [TopologicalSpace α]
    {S : Set (ℝ × α)} {f D : ℝ → α → ℝ}
    (hderiv :
      ∀ p ∈ S, HasDerivAt (fun t : ℝ => f t p.2) (D p.1 p.2) p.1)
    (hD : ContinuousOn (fun p : ℝ × α => D p.1 p.2) S) :
    ContinuousOn
      (fun p : ℝ × α => deriv (fun t : ℝ => f t p.2) p.1)
      S := by
  have h_eq : Set.EqOn
      (fun p : ℝ × α => deriv (fun t : ℝ => f t p.2) p.1)
      (fun p : ℝ × α => D p.1 p.2) S := by
    intro p hp
    exact (hderiv p hp).deriv
  exact hD.congr h_eq

/-- Explicit continuous time derivatives of the chart Gram entries produce the
regularity package needed by the volume-variation theorem. -/
theorem MetricFamilyRegularAt.of_chartGram_timeDeriv
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t₀ : ℝ}
    (h :
      ∀ x₀ i j, ∃ D : ℝ → M → ℝ,
        (∀ t x,
          x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
            HasDerivAt
              (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j)
              (D t x) t) ∧
        ContinuousOn
          (fun p : ℝ × M =>
            chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) ∧
        ContinuousOn
          (fun p : ℝ × M => D p.1 p.2)
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    MetricFamilyRegularAt (I := I) g_fam t₀ := by
  refine
    { hasDerivAt_chartGramMatrix := ?_
      continuousOn_chartGramMatrix := ?_
      continuousOn_deriv_chartGramMatrix := ?_ }
  · intro x₀ i j x hx t
    rcases h x₀ i j with ⟨D, hD_deriv, -, -⟩
    have hderiv := hD_deriv t x hx
    exact hderiv.congr_deriv hderiv.deriv.symm
  · intro x₀ i j
    rcases h x₀ i j with ⟨D, -, hG_cont, -⟩
    exact hG_cont
  · intro x₀ i j
    rcases h x₀ i j with ⟨D, hD_deriv, -, hD_cont⟩
    refine continuousOn_deriv_of_hasDerivAt_eq_continuousOn
      (S := Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
      (f := fun t x => chartGramMatrix (I := I) (g_fam t) x₀ x i j)
      (D := D) ?_ hD_cont
    intro p hp
    exact hD_deriv p.1 p.2 hp.2

/-- Minimum regularity interface for a time-varying real-valued function on `M`.

Note: `hasDerivAt_time` asserts differentiability at every time, not just `t₀`.
The parametric-integral theorem used downstream requires differentiability in a
neighbourhood of `t₀`; supplying it at every time is the natural minimal
strengthening (and is automatic for any jointly-smooth source). -/
structure FunctionRegularAt (f : ℝ → M → ℝ) (t₀ : ℝ) : Prop where
  /-- Pointwise time-differentiability at every time, per spatial point. -/
  hasDerivAt_time :
    ∀ (x : M) (t : ℝ), HasDerivAt (fun s : ℝ => f s x) (deriv (fun s : ℝ => f s x) t) t
  /-- Joint `(t, x)`-continuity of `f`. -/
  continuous_joint : Continuous (fun p : ℝ × M => f p.1 p.2)
  /-- Joint `(t, x)`-continuity of the pointwise time-derivative. -/
  continuous_deriv_joint :
    Continuous (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)

/-- Constant-in-time-and-space functions satisfy the regularity interface used by
the volume variation theorem. -/
theorem FunctionRegularAt_const (c : ℝ) (t₀ : ℝ) :
    FunctionRegularAt (fun _ : ℝ => fun _ : M => c) t₀ := by
  refine
    { hasDerivAt_time := ?_
      continuous_joint := ?_
      continuous_deriv_joint := ?_ }
  · intro _ t
    have hderiv : deriv (fun _ : ℝ => c) t = 0 :=
      (hasDerivAt_const (x := t) (c := c)).deriv
    simpa [hderiv] using (hasDerivAt_const (x := t) (c := c))
  · simpa using (continuous_const : Continuous (fun _ : ℝ × M => c))
  · have hfun :
        (fun p : ℝ × M => deriv (fun _ : ℝ => c) p.1) =
          fun _ : ℝ × M => (0 : ℝ) := by
      funext p
      exact (hasDerivAt_const (x := p.1) (c := c)).deriv
    simpa [hfun] using (continuous_const : Continuous (fun _ : ℝ × M => (0 : ℝ)))

/-- The constant one integrand satisfies the regularity interface used by the
volume variation theorem. -/
theorem FunctionRegularAt_one (t₀ : ℝ) :
    FunctionRegularAt (fun _ : ℝ => fun _ : M => (1 : ℝ)) t₀ :=
  FunctionRegularAt_const (M := M) 1 t₀

/-! ## Jacobi's formula for the determinant of a smooth matrix family

We develop the time-derivative of `t ↦ (G t).det` in full generality, for any
smooth family `G : ℝ → Matrix n n ℝ` whose entries each have a derivative at
the base point. The derivation is elementary: we expand the determinant via
`Matrix.det_apply'` and apply the product rule `HasDerivAt.finset_prod`
componentwise.

Throughout this section, `n` is an arbitrary index type with `Fintype n` and
`DecidableEq n`. Concretely, in the application `n = Fin (Module.finrank ℝ E)`.
-/

section Jacobi

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Product rule for a single term of the determinant expansion: the derivative
of `t ↦ ∏ i, G t (σ i) i` equals the standard Leibniz sum. -/
lemma hasDerivAt_prod_of_entries
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (σ : Equiv.Perm n) :
    HasDerivAt (fun t => ∏ i, G t (σ i) i)
      (∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) • G' (σ k) k) t := by
  classical
  have hfactor : ∀ k ∈ (Finset.univ : Finset n),
      HasDerivAt (fun t : ℝ => G t (σ k) k) (G' (σ k) k) t :=
    fun k _ => hG (σ k) k
  exact HasDerivAt.fun_finset_prod hfactor

/-- Jacobi's formula, permutation-sum form: the derivative of the determinant of
a smooth family of real matrices equals the signed sum of products obtained by
differentiating one factor at a time in the Leibniz expansion. -/
theorem hasDerivAt_det_of_entries
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t) :
    HasDerivAt (fun t => (G t).det)
      (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k) t := by
  classical
  have hexpand : (fun s : ℝ => (G s).det)
      = (fun s : ℝ =>
          ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ i, G s (σ i) i) := by
    funext s
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexpand]
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      HasDerivAt
        (fun s : ℝ => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, G s (σ i) i)
        (((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k) t := by
    intro σ _
    have hprod := hasDerivAt_prod_of_entries (n := n) G G' t hG σ
    have hmul := hprod.const_mul (((Equiv.Perm.sign σ : ℤ) : ℝ))
    -- Replace `smul` inside the sum by `mul` on `ℝ` (they coincide).
    have hsum_eq :
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) • G' (σ k) k
          = ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k := by
      simp [smul_eq_mul]
    rw [← hsum_eq]
    exact hmul
  exact HasDerivAt.fun_sum hterm

/-! ### Identification of the permutation-sum with trace-of-adjugate -/

/-- Key algebraic identity: the Leibniz-product derivative sum equals
`trace (adjugate A · B)`. Proof via the cofactor expansion of `adjugate A i j`
combined with swapping the order of the σ- and k-summations. -/
theorem perm_sum_eq_trace_adjugate_mul
    (A B : Matrix n n ℝ) :
    (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ k, (∏ i ∈ Finset.univ.erase k, A (σ i) i) * B (σ k) k)
      = trace (adjugate A * B) := by
  classical
  -- Expand the trace.
  have hrhs :
      trace (adjugate A * B)
        = ∑ k, ∑ v, adjugate A k v * B v k := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diag]
  rw [hrhs]
  -- Distribute the scalar factor inside the permutation sum, then swap sums.
  have hLHS_rewrite :
      (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, A (σ i) i) * B (σ k) k)
        = ∑ σ : Equiv.Perm n, ∑ k,
            ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ((∏ i ∈ Finset.univ.erase k, A (σ i) i) * B (σ k) k) := by
    refine Finset.sum_congr rfl ?_
    intro σ _
    rw [Finset.mul_sum]
  rw [hLHS_rewrite, Finset.sum_comm]
  -- Goal: `∑ k, ∑ σ, sign σ * (…(σ) * B (σ k) k) = ∑ k, ∑ v, adjugate A k v * B v k`.
  refine Finset.sum_congr rfl ?_
  intro k _
  -- Partition σ by the fibre `σ k = v`.
  have hpart :
      (Finset.univ : Finset (Equiv.Perm n)) =
        Finset.univ.biUnion fun v : n =>
          (Finset.univ : Finset (Equiv.Perm n)).filter fun σ => σ k = v := by
    ext σ; simp
  have hdisj :
      ∀ v ∈ (Finset.univ : Finset n), ∀ w ∈ (Finset.univ : Finset n), v ≠ w →
        Disjoint
          ((Finset.univ : Finset (Equiv.Perm n)).filter fun σ => σ k = v)
          ((Finset.univ : Finset (Equiv.Perm n)).filter fun σ => σ k = w) := by
    intro v _ w _ hvw
    refine Finset.disjoint_left.mpr ?_
    intro σ hσv hσw
    rw [Finset.mem_filter] at hσv hσw
    exact hvw (hσv.2.symm.trans hσw.2)
  rw [hpart, Finset.sum_biUnion hdisj]
  -- Now: ∑ v, ∑_{σ : σ k = v} sign σ * (∏_{i≠k} A(σi, i) * B (σ k) k)
  --    = ∑ v, adjugate A k v * B v k.
  refine Finset.sum_congr rfl ?_
  intro v _
  -- On the filter `σ k = v`, we can pull out `B v k` from the sum.
  have hBpull :
      (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm n)).filter fun σ => σ k = v,
          ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ((∏ i ∈ Finset.univ.erase k, A (σ i) i) * B (σ k) k))
        = (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm n)).filter fun σ => σ k = v,
            ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∏ i ∈ Finset.univ.erase k, A (σ i) i) * B v k := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [hσ.2]
    ring
  rw [hBpull]
  -- Remaining: the signed sum equals `adjugate A k v`. Use `adjugate_apply`.
  congr 1
  rw [adjugate_apply, Matrix.det_apply']
  -- Split the det-expansion sum (over all permutations) using
  -- `Finset.sum_filter_add_sum_filter_not`.
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Equiv.Perm n)))
    (p := fun τ => τ k = v)]
  -- The "τ k ≠ v" piece vanishes.
  have hsecond :
      ∀ τ ∈ (Finset.univ : Finset (Equiv.Perm n)).filter fun τ => ¬ τ k = v,
        ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          ∏ i, (A.updateRow v (Pi.single k 1)) (τ i) i = 0 := by
    intro τ hτ
    rw [Finset.mem_filter] at hτ
    have hinv : τ⁻¹ v ≠ k := by
      intro h
      apply hτ.2
      have hτkv : τ (τ⁻¹ v) = v := by
        change (τ * τ⁻¹) v = v
        rw [mul_inv_cancel]; rfl
      have := congrArg τ h
      rw [hτkv] at this
      exact this.symm
    have hzero :
        (A.updateRow v (Pi.single k 1)) (τ (τ⁻¹ v)) (τ⁻¹ v) = 0 := by
      have hτv : τ (τ⁻¹ v) = v := by
        change (τ * τ⁻¹) v = v
        rw [mul_inv_cancel]; rfl
      rw [hτv, Matrix.updateRow_self]
      exact Pi.single_eq_of_ne (M := fun _ : n => ℝ) hinv 1
    have hprod_zero :
        (∏ i, (A.updateRow v (Pi.single k 1)) (τ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (τ⁻¹ v)) hzero
    rw [hprod_zero, mul_zero]
  rw [Finset.sum_eq_zero hsecond, add_zero]
  -- Swap sides to match the signed sum on the LHS.
  symm
  -- First piece: show ∀ τ with τ k = v,
  -- `∏ i, (A.updateRow v (Pi.single k 1)) (τ i) i = ∏ i ∈ univ.erase k, A (τ i) i`.
  refine Finset.sum_congr rfl ?_
  intro τ hτ
  rw [Finset.mem_filter] at hτ
  -- Split product at index k.
  have hsplit_prod :
      (∏ i, (A.updateRow v (Pi.single k 1)) (τ i) i)
        = (A.updateRow v (Pi.single k 1)) (τ k) k *
            ∏ i ∈ Finset.univ.erase k,
              (A.updateRow v (Pi.single k 1)) (τ i) i :=
    (Finset.mul_prod_erase (Finset.univ : Finset n)
      (fun i => (A.updateRow v (Pi.single k 1)) (τ i) i)
      (Finset.mem_univ k)).symm
  rw [hsplit_prod]
  -- (A.updateRow v ...)(τ k) k = (Pi.single k 1) k = 1 since τ k = v.
  have h_topfactor :
      (A.updateRow v (Pi.single k 1)) (τ k) k = 1 := by
    rw [hτ.2, Matrix.updateRow_self]
    simp
  rw [h_topfactor, one_mul]
  -- For i ≠ k, show the entry equals A (τ i) i.
  have hrest :
      (∏ i ∈ Finset.univ.erase k, (A.updateRow v (Pi.single k 1)) (τ i) i)
        = ∏ i ∈ Finset.univ.erase k, A (τ i) i := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hi_ne_k : i ≠ k := (Finset.mem_erase.mp hi).1
    have hτi_ne_v : τ i ≠ v := by
      intro hτiv
      have hinv_self : ∀ y, τ⁻¹ (τ y) = y := by
        intro y
        change (τ⁻¹ * τ) y = y
        rw [inv_mul_cancel]; rfl
      have h1 : i = τ⁻¹ v := by
        have := congrArg (⇑(τ⁻¹ : Equiv.Perm n)) hτiv
        rw [hinv_self i] at this
        exact this
      have hkinv : τ⁻¹ v = k := by
        have := congrArg (⇑(τ⁻¹ : Equiv.Perm n)) hτ.2
        rw [hinv_self k] at this
        exact this.symm
      exact hi_ne_k (h1.trans hkinv)
    rw [Matrix.updateRow_apply]
    exact if_neg hτi_ne_v
  rw [hrest]

/-- Jacobi's formula in trace-of-adjugate form. -/
theorem hasDerivAt_det_eq_trace_adjugate_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t) :
    HasDerivAt (fun t => (G t).det)
      (trace (adjugate (G t) * G')) t := by
  have h := hasDerivAt_det_of_entries (n := n) G G' t hG
  rw [perm_sum_eq_trace_adjugate_mul (n := n) (G t) G'] at h
  exact h

/-- When `A.det` is a unit, `adjugate A = A.det • A⁻¹`. -/
lemma adjugate_eq_det_smul_inv
    {A : Matrix n n ℝ} (h : IsUnit A.det) :
    adjugate A = A.det • A⁻¹ := by
  -- `A⁻¹ = A.det⁻¹ʳ • adjugate A`, so `A.det • A⁻¹ = A.det * A.det⁻¹ʳ • adj A = adj A`.
  rw [Matrix.inv_def]
  rw [smul_smul]
  rw [Ring.mul_inverse_cancel _ h]
  rw [one_smul]

/-- When the determinant is a unit, Jacobi's trace-adjugate form simplifies to the
classical formula `d/dt det G(t) = det(G t) · trace(G(t)⁻¹ · G'(t))`. -/
theorem hasDerivAt_det_eq_det_mul_trace_inv_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (hunit : IsUnit (G t).det) :
    HasDerivAt (fun t => (G t).det)
      ((G t).det * trace ((G t)⁻¹ * G')) t := by
  have h := hasDerivAt_det_eq_trace_adjugate_mul (n := n) G G' t hG
  -- Rewrite `adjugate (G t) * G'` using `adjugate = det • inv`.
  have hadj := adjugate_eq_det_smul_inv (n := n) (A := G t) hunit
  have hrewrite : trace (adjugate (G t) * G') = (G t).det * trace ((G t)⁻¹ * G') := by
    rw [hadj]
    rw [Matrix.smul_mul]
    rw [Matrix.trace_smul]
    rfl
  rw [hrewrite] at h
  exact h

/-! ### Chain rule with `Real.sqrt` -/

/-- Chain-rule version: derivative of `t ↦ √(det G(t))` at a time where the
determinant is nonzero, in permutation-sum form. -/
theorem hasDerivAt_sqrt_det_of_entries
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (hpos : 0 < (G t).det) :
    HasDerivAt (fun s => Real.sqrt (G s).det)
      ((1 / (2 * Real.sqrt (G t).det)) *
        ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k) t := by
  have hdet := hasDerivAt_det_of_entries (n := n) G G' t hG
  have hne : (G t).det ≠ 0 := ne_of_gt hpos
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (G t).det)) (G t).det :=
    Real.hasDerivAt_sqrt hne
  have hcomp := hsqrt.comp t hdet
  simpa [Function.comp] using hcomp

/-- The geometric form of Jacobi's identity applied to the square-root:
`d/dt √(det G(t)) = ½ · trace(G(t)⁻¹ · G'(t)) · √(det G(t))`, under the
hypothesis that `(G t).det > 0`. -/
theorem hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (hpos : 0 < (G t).det) :
    HasDerivAt (fun s => Real.sqrt (G s).det)
      ((1 / 2) * trace ((G t)⁻¹ * G') * Real.sqrt (G t).det) t := by
  have hunit : IsUnit (G t).det := (ne_of_gt hpos).isUnit
  have hdet := hasDerivAt_det_eq_det_mul_trace_inv_mul (n := n) G G' t hG hunit
  have hne : (G t).det ≠ 0 := ne_of_gt hpos
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (G t).det)) (G t).det :=
    Real.hasDerivAt_sqrt hne
  have hcomp := hsqrt.comp t hdet
  -- `hcomp : HasDerivAt (√ ∘ (fun s => (G s).det))
  --   ((1 / (2 * √(G t).det)) * ((G t).det * trace ((G t)⁻¹ * G'))) t`.
  -- Arithmetic: `(1/(2*√d)) * (d * x) = x * √d / 2` since `d / √d = √d`.
  have hsqrt_ne : Real.sqrt (G t).det ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hkey :
      (1 / (2 * Real.sqrt (G t).det)) * ((G t).det * trace ((G t)⁻¹ * G'))
        = (1 / 2) * trace ((G t)⁻¹ * G') * Real.sqrt (G t).det := by
    -- Simplify `(G t).det / √(G t).det = √(G t).det`.
    have hdiv : (G t).det / Real.sqrt (G t).det = Real.sqrt (G t).det := by
      rw [eq_comm, eq_div_iff hsqrt_ne]
      exact Real.mul_self_sqrt hpos.le
    calc (1 / (2 * Real.sqrt (G t).det))
            * ((G t).det * trace ((G t)⁻¹ * G'))
        = ((G t).det / Real.sqrt (G t).det) * ((1 / 2) * trace ((G t)⁻¹ * G')) := by
          ring
      _ = Real.sqrt (G t).det * ((1 / 2) * trace ((G t)⁻¹ * G')) := by
          rw [hdiv]
      _ = (1 / 2) * trace ((G t)⁻¹ * G') * Real.sqrt (G t).det := by ring
  rw [hkey] at hcomp
  simpa [Function.comp] using hcomp

end Jacobi

/-! ## Application to the chart-local density

We specialise the abstract Jacobi formula to the concrete Gram-matrix family
`Gfam t x := chartGramMatrix (g_fam t) x₀ x` arising from a time-parameterised
Riemannian metric family on `M`, at a fixed base point `x₀` and a fixed
evaluation point `x` in the chart source. -/

section ChartDensityFamily

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

/-- The Gram matrix of the chart-local basis, as a family in time. At each time
`t`, `Gfam t x = chartGramMatrix (g_fam t) x₀ x`. -/
def chartGramMatrixFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun t => chartGramMatrix (I := I) (g_fam t) x₀ x

@[simp] lemma chartGramMatrixFamily_apply
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartGramMatrixFamily (I := I) g_fam x₀ x t =
      chartGramMatrix (I := I) (g_fam t) x₀ x := rfl

/-- The chart density of the time-parameterised family at a fixed spatial point. -/
def chartDensityFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → ℝ :=
  fun t => chartDensity (I := I) (g_fam t) x₀ x

@[simp] lemma chartDensityFamily_apply
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartDensityFamily (I := I) g_fam x₀ x t =
      chartDensity (I := I) (g_fam t) x₀ x := rfl

lemma chartDensityFamily_eq_sqrt_det
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartDensityFamily (I := I) g_fam x₀ x t =
      Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x t).det := rfl

/-- Pointwise Jacobi formula applied to the chart density: given a family
of Gram matrices with each entry differentiable in time, the derivative of the
density is given by the standard half-trace-of-inverse formula multiplied by
the density itself, at any point in the chart base set. -/
theorem hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ : M) (t : ℝ) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (Gprime : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hEntries : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => chartGramMatrixFamily (I := I) g_fam x₀ x s i j)
        (Gprime i j) t) :
    HasDerivAt
      (fun s => chartDensityFamily (I := I) g_fam x₀ x s)
      ((1 / 2) *
        trace ((chartGramMatrixFamily (I := I) g_fam x₀ x t)⁻¹ * Gprime) *
        Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x t).det) t := by
  have hpos : 0 < (chartGramMatrixFamily (I := I) g_fam x₀ x t).det := by
    simpa [chartGramMatrixFamily_apply] using
      chartGramMatrix_det_pos (I := I) (g_fam t) x₀ hx
  have hderiv := hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (G := chartGramMatrixFamily (I := I) g_fam x₀ x)
    (G' := Gprime) (t := t) hEntries hpos
  -- Convert the goal to the `sqrt det` form.
  have hfun :
      (fun s => chartDensityFamily (I := I) g_fam x₀ x s)
        = (fun s => Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x s).det) := by
    funext s
    exact chartDensityFamily_eq_sqrt_det (I := I) g_fam x₀ x s
  rw [hfun]
  exact hderiv

end ChartDensityFamily

/-! ## Coordinate-invariant metric trace of the time-derivative

Given a time-parameterised Riemannian metric family and a point `x : M`, we
define the intrinsic scalar `tr_g(∂_t g)(x)`, computed as the trace
`trace (G⁻¹ · G')` where `G t = chartGramMatrix (g_fam t) x x` uses the chart
source at `x` itself as the basis chart (so `x` is always in the base set, and
the canonical choice avoids any well-definedness issue).

Note: the definition uses `deriv`, which returns `0` whenever the underlying
function is not differentiable at the base time. Consequently the definition
is total and requires no regularity hypothesis; callers supply regularity only
where they need the concrete identification `deriv = ∂_t G`. -/

variable (I) in
/-- The metric trace `tr_g(∂_t g)(x)` at time `t`, computed in the canonical
chart at `x`. Concretely, with `G(s) := chartGramMatrix (g_fam s) x x`, this is
`trace(G(t)⁻¹ · G'(t))`, where `G'(t)` is the matrix of pointwise time
derivatives. Since `x ∈ (chartAt H x).source` always, the base set contains
`x` and the Jacobi machinery applies. -/
def traceTimeDerivMetric
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) : ℝ :=
  Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
    (Matrix.of fun i j =>
      deriv (fun s => chartGramMatrix (I := I) (g_fam s) x x i j) t))

/-- Unfolding lemma for `traceTimeDerivMetric`. -/
lemma traceTimeDerivMetric_eq
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) :
    traceTimeDerivMetric (I := I) g_fam t x =
      Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
        (Matrix.of fun i j =>
          deriv (fun s => chartGramMatrix (I := I) (g_fam s) x x i j) t)) := rfl

/-! ## Bochner integral representation of the chart-local measure

The Bochner-valued analogue of `chartLocalMeasure_lintegral`. Given a bounded
continuous real-valued function on `M`, its Bochner integral against the
chart-local measure expands as a Bochner integral on the model space against
the restricted canonical Haar measure. -/

/-- Bochner integral characterisation of the chart-local measure for a
measurable, integrable real-valued function. -/
theorem integral_chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (h : M → ℝ) (hh_meas : Measurable h) :
    ∫ x, h x ∂(chartLocalMeasure (I := I) g x₀)
      = ∫ y in (extChartAt I x₀).target,
          chartDensity g x₀ ((extChartAt I x₀).symm y) *
            h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E)) := by
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  -- Set up the two-step measure as `Measure.map symm (withDensity (…))`.
  set μ₀ : MeasureTheory.Measure E :=
    (modelHaar (E := E)).restrict (extChartAt I x₀).target with hμ₀
  set w : E → ℝ≥0∞ :=
    fun y => ENNReal.ofReal
      (chartDensity g x₀ ((extChartAt I x₀).symm y)) with hw
  set μ₁ : MeasureTheory.Measure E := μ₀.withDensity w with hμ₁
  -- Step 1: unfold `chartLocalMeasure` to `Measure.map symm μ₁`.
  have h_unfold :
      chartLocalMeasure (I := I) g x₀ =
        MeasureTheory.Measure.map (extChartAt I x₀).symm μ₁ := rfl
  rw [h_unfold]
  -- Step 2: use `integral_map` for the pushforward step.
  have haem_symm : AEMeasurable ((extChartAt I x₀).symm) μ₁ := by
    have haem_base : AEMeasurable ((extChartAt I x₀).symm) μ₀ :=
      aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) x₀
    have hac : μ₁ ≪ μ₀ := by
      simpa [hμ₁] using MeasureTheory.withDensity_absolutelyContinuous (μ := μ₀) w
    exact haem_base.mono_ac hac
  have h_integral_map :
      ∫ x, h x ∂(MeasureTheory.Measure.map (extChartAt I x₀).symm μ₁)
        = ∫ y, h ((extChartAt I x₀).symm y) ∂μ₁ := by
    exact MeasureTheory.integral_map haem_symm hh_meas.aestronglyMeasurable
  rw [h_integral_map]
  -- Step 3: use `integral_withDensity_eq_integral_toReal_smul₀`.
  have hwd_aem : AEMeasurable w μ₀ :=
    aemeasurable_chartDensity_symm_pullback (I := I) g x₀
  have hw_lt_top : ∀ᵐ y ∂μ₀, w y < (⊤ : ℝ≥0∞) := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp [hw]
  have h_withDensity :
      ∫ y, h ((extChartAt I x₀).symm y) ∂μ₁
        = ∫ y, (w y).toReal • h ((extChartAt I x₀).symm y) ∂μ₀ := by
    simpa [hμ₁] using
      integral_withDensity_eq_integral_toReal_smul₀ (μ := μ₀)
        (f := w) hwd_aem hw_lt_top
        (g := fun y : E => h ((extChartAt I x₀).symm y))
  rw [h_withDensity]
  -- Step 4: unfold w.toReal = chartDensity (…), using density_nonneg.
  have hw_toReal : ∀ y ∈ (extChartAt I x₀).target,
      (w y).toReal = chartDensity g x₀ ((extChartAt I x₀).symm y) := by
    intro y hy
    have hsource : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      have := (extChartAt I x₀).map_target hy
      rw [extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    have hbase : (extChartAt I x₀).symm y ∈
        (trivializationAt E (TangentSpace I) x₀).baseSet := hsource
    have hpos : 0 < chartDensity g x₀ ((extChartAt I x₀).symm y) :=
      chartDensity_pos (I := I) g x₀ hbase
    change (ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))).toReal
        = chartDensity g x₀ ((extChartAt I x₀).symm y)
    exact ENNReal.toReal_ofReal hpos.le
  -- Step 5: convert `∫ y ∂μ₀` to `∫ y in target` and pointwise rewrite.
  have h_restrict :
      ∫ y, (w y).toReal • h ((extChartAt I x₀).symm y) ∂μ₀
        = ∫ y in (extChartAt I x₀).target,
            (w y).toReal • h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E)) := by
    simp [hμ₀]
  rw [h_restrict]
  refine setIntegral_congr_fun htarget_meas (fun y hy => ?_)
  rw [hw_toReal y hy, smul_eq_mul]

/-! ## Finite-support form of the chart atlas POU on a compact manifold

On a compact `M`, the chart-atlas POU has finite nonempty support, hence its
tsum-based glue formula is a Finset sum. -/

/-- On a compact manifold, the set of indices where the chart-atlas POU has
nonempty support is finite. -/
lemma chartAtlasPOU_finite_support
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] :
    {α : M | (Function.support ((chartAtlasPOU I M) α)).Nonempty}.Finite :=
  LocallyFinite.finite_nonempty_of_compact
    (chartAtlasPOU I M).locallyFinite

/-- A designated finite set of POU indices on a compact manifold, covering the
full nonempty support. -/
noncomputable def chartAtlasPOU_finset
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] : Finset M :=
  (chartAtlasPOU_finite_support (I := I) (M := M)).toFinset

lemma chartAtlasPOU_finset_mem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] {α : M} :
    α ∈ chartAtlasPOU_finset (I := I) (M := M) ↔
      (Function.support ((chartAtlasPOU I M) α)).Nonempty := by
  unfold chartAtlasPOU_finset
  rw [Set.Finite.mem_toFinset]
  rfl

/-- Outside the finite support Finset, the POU weight is identically zero. -/
lemma chartAtlasPOU_weight_zero_of_notMem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {α : M} (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M)) (x : M) :
    (chartAtlasPOU I M) α x = 0 := by
  rw [chartAtlasPOU_finset_mem] at hα
  rw [Set.not_nonempty_iff_eq_empty] at hα
  by_contra hne
  have hx : x ∈ Function.support ((chartAtlasPOU I M) α) := hne
  rw [hα] at hx
  exact (Set.notMem_empty _) hx

/-- For a POU index outside the finite-support set, the weighted chart-local measure
is the zero measure. -/
lemma chartAtlasPOU_withDensity_zero_of_notMem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {α : M} (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M)) :
    (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) = 0 := by
  have hzero : (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) = 0 := by
    funext x
    rw [chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x]
    simp
  rw [hzero, MeasureTheory.withDensity_zero]

/-! ## Chart-local parametric `HasDerivAt` for the model-space integral

The core parametric derivative lemma used in the volume-variation formula,
stated chart-locally on the model space side (before pushing forward to `M`).
Given an integrand `F : ℝ → E → ℝ` depending smoothly on a parameter `t`, with
pointwise time derivative `F'`, bound `b : E → ℝ` dominating `F'` on a
neighborhood of `t₀`, and the relevant measurability and integrability
hypotheses, we obtain both integrability of `F' t₀` and the parametric
`HasDerivAt` formula. This is the direct wrapper of
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` specialised to the
real-valued setting used below. -/
theorem hasDerivAt_setIntegral_model
    (target : Set E) (_htarget_meas : MeasurableSet target)
    {F : ℝ → E → ℝ} (F' : ℝ → E → ℝ) {b : E → ℝ}
    (t₀ : ℝ) {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    (hF_meas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (F t) ((modelHaar (E := E)).restrict target))
    (hF_int : Integrable (F t₀) ((modelHaar (E := E)).restrict target))
    (hF'_meas : AEStronglyMeasurable (F' t₀)
      ((modelHaar (E := E)).restrict target))
    (h_bound : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ t ∈ s, ‖F' t y‖ ≤ b y)
    (h_bound_int : Integrable b ((modelHaar (E := E)).restrict target))
    (h_diff : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ t ∈ s, HasDerivAt (fun r => F r y) (F' t y) t) :
    Integrable (F' t₀) ((modelHaar (E := E)).restrict target) ∧
      HasDerivAt (fun t => ∫ y in target, F t y ∂(modelHaar (E := E)))
        (∫ y in target, F' t₀ y ∂(modelHaar (E := E))) t₀ := by
  -- Apply the Mathlib theorem.
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (α := E) (E := ℝ) (μ := (modelHaar (E := E)).restrict target)
    (F := F) (F' := F') (x₀ := t₀) (s := s) (bound := b)
    hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  -- Reinterpret the integrals as set integrals.
  refine ⟨this.1, ?_⟩
  have hfun : (fun t => ∫ y, F t y ∂((modelHaar (E := E)).restrict target))
      = fun t => ∫ y in target, F t y ∂(modelHaar (E := E)) := by
    funext t
    rfl
  have hfun' : (∫ y, F' t₀ y ∂((modelHaar (E := E)).restrict target))
      = ∫ y in target, F' t₀ y ∂(modelHaar (E := E)) := rfl
  rw [← hfun, ← hfun']
  exact this.2

/-! ## Pointwise time differentiability of Gram matrix entries

Each Gram-matrix entry is assumed (via `MetricFamilyRegularAt`) to be
time-differentiable at the base point, with derivative obtained by taking the
classical `deriv` at that point. -/

/-- Each Gram-matrix entry has a time derivative at every point, equal to its
classical `deriv`. This is simply a restatement of the
`MetricFamilyRegularAt.hasDerivAt_chartGramMatrix` field convenient for
downstream use. -/
lemma hasDerivAt_chartGramMatrix_entry
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t₀ : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i j : Fin (Module.finrank ℝ E)) (t : ℝ) :
    HasDerivAt (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j)
      (deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) t :=
  hreg.hasDerivAt_chartGramMatrix x₀ i j hx t

/-! ## Chart-invariance of the metric trace of the time derivative

The intrinsic scalar `traceTimeDerivMetric gFam t x = trace(G_x⁻¹ · ∂_t G_x)`,
computed in the canonical chart at `x` itself, coincides with the same trace
computed in any other chart whose base set contains `x`. The proof uses the
matrix pullback `G_{x₁}(x) = Jᵀ · G_{x₀}(x) · J` with `J` time-independent
(the chart-transition Jacobian depends only on the manifold structure), so
`∂_t G_{x₁} = Jᵀ · ∂_t G_{x₀} · J`, and the invariance of trace under
conjugation yields the conclusion. -/

section ChartInvarianceOfTraceTimeDeriv

/-- The pointwise time derivative of the Gram matrix under chart change:
`∂_t G_{x₁}(x) = Jᵀ · ∂_t G_{x₀}(x) · J`, where `J := transitionMatrix x₀ x₁ x`
is independent of `t` (it depends only on the chart structure). -/
lemma deriv_chartGramMatrix_pullback
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t)
      = (transitionMatrix (I := I) x₀ x₁ x)ᵀ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) *
          transitionMatrix (I := I) x₀ x₁ x := by
  classical
  -- Abbreviations.
  set n := Fin (Module.finrank ℝ E) with hn_def
  set J : Matrix n n ℝ := transitionMatrix (I := I) x₀ x₁ x with hJ_def
  -- Entry-wise pullback formula (time-dependent).
  have hentry : ∀ (t₀ : ℝ) (i j : n),
      chartGramMatrix (I := I) (g_fam t₀) x₁ x i j
        = ∑ k, ∑ l, J k i * J l j *
            chartGramMatrix (I := I) (g_fam t₀) x₀ x k l := by
    intro t₀ i j
    exact chartGramMatrix_pullback_eq_sum (I := I) (g_fam t₀) x₀ x₁ hx0 hx1 i j
  -- For each (i, j), the time derivative of `s ↦ G_{x₁}(x) i j` equals the
  -- matrix product entry.
  ext i j
  -- Entry-level HasDerivAt for G_{x₀}.
  have hG0_entry : ∀ k l : n,
      HasDerivAt (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x k l)
        (deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x k l) t) t := by
    intro k l
    exact hasDerivAt_chartGramMatrix_entry (I := I) (M := M) hreg x₀ hx0 k l t
  -- Form the linear combination: G_{x₁}(x) i j = ∑_{k,l} J_{k,i} J_{l,j} G_{x₀}(x) k l.
  -- Its derivative is the same linear combination of the entry derivatives.
  have hsum_hasDeriv :
      HasDerivAt
        (fun s => ∑ k : n, ∑ l : n, J k i * J l j *
            chartGramMatrix (I := I) (g_fam s) x₀ x k l)
        (∑ k : n, ∑ l : n, J k i * J l j *
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x k l) t) t := by
    -- Outer sum.
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    -- Inner sum.
    refine HasDerivAt.fun_sum (fun l _ => ?_)
    -- Constant (J k i * J l j) times a differentiable function.
    have hcm := (hG0_entry k l).const_mul (J k i * J l j)
    exact hcm
  -- The function `s ↦ G_{x₁}(x) i j s` equals the linear combination.
  have hfun_eq :
      (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j)
        = (fun s => ∑ k : n, ∑ l : n, J k i * J l j *
            chartGramMatrix (I := I) (g_fam s) x₀ x k l) := by
    funext s
    exact hentry s i j
  -- Transport: deriv of the LHS equals deriv of the linear combination.
  have hderiv_eq :
      deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t
        = ∑ k : n, ∑ l : n, J k i * J l j *
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x k l) t := by
    rw [hfun_eq]
    exact hsum_hasDeriv.deriv
  -- Now compute the matrix-product entry and match.
  change deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t
      = (Jᵀ *
          (Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) *
          J) i j
  rw [hderiv_eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  -- LHS: ∑_k ∑_l J[k,i] · J[l,j] · G'[k,l]
  -- RHS: ∑_p (∑_q J[q,i] · G'[q,p]) · J[p,j]
  -- These match via sum_comm (swap k ↔ p).
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  ring

/-- The transition matrix is invertible on the chart overlap: composing with the
reverse transition matrix (from `x₁` to `x₀`) yields the identity. Hence J has
a two-sided inverse and is a unit in the matrix ring. -/
lemma transitionMatrix_mul_reverse
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    transitionMatrix (I := I) x₀ x₁ x * transitionMatrix (I := I) x₁ x₀ x = 1 := by
  classical
  -- The transition matrix sends coordinate vectors via `tangentCoordChange x₁ x₀`.
  -- Composing gives `tangentCoordChange x₀ x₀ = id` on the overlap.
  -- Work entry-wise.
  ext i j
  have hx0' : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]
    exact hx0
  have hx1' : x ∈ (extChartAt I x₁).source := by
    rw [extChartAt_source]
    exact hx1
  have hmem : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source ∩
      (extChartAt I x₀).source := ⟨⟨hx0', hx1'⟩, hx0'⟩
  -- Key identity on the basis vectors: tang x₁ x₀ ∘ tang x₀ x₁ = tang x₀ x₀ = id.
  have hcomp : ∀ i : Fin (Module.finrank ℝ E),
      (tangentCoordChange I x₁ x₀ x) ((tangentCoordChange I x₀ x₁ x)
          ((Module.finBasis ℝ E) i))
        = (Module.finBasis ℝ E) i := by
    intro i
    have := tangentCoordChange_comp (I := I) (𝕜 := ℝ) (E := E) (H := H) (M := M)
        (w := x₀) (x := x₁) (y := x₀) (z := x)
        (v := (Module.finBasis ℝ E) i) hmem
    rw [this]
    have hself := tangentCoordChange_self (I := I) (x := x₀) (z := x)
      (v := (Module.finBasis ℝ E) i) hx0'
    exact hself
  -- Now compute the matrix product entry.
  change (transitionMatrix (I := I) x₀ x₁ x *
      transitionMatrix (I := I) x₁ x₀ x) i j = (1 : Matrix _ _ _) i j
  simp only [Matrix.mul_apply, transitionMatrix_apply, Matrix.one_apply]
  -- Apply `finBasis_repr_sum` to `tangentCoordChange x₀ x₁ (e j)`, then apply
  -- `tangentCoordChange x₁ x₀`. The composition is `tangentCoordChange x₀ x₀ = id`,
  -- so we recover `e j = ∑ k, repr(tang x₀ x₁ (e j)) k • tang x₁ x₀ (e k)`.
  have hexp :
      (tangentCoordChange I x₀ x₁ x) ((Module.finBasis ℝ E) j)
        = ∑ k, (Module.finBasis ℝ E).repr
            ((tangentCoordChange I x₀ x₁ x) ((Module.finBasis ℝ E) j)) k
          • (Module.finBasis ℝ E) k :=
    finBasis_repr_sum (tangentCoordChange I x₀ x₁ x) j
  -- Apply `tangentCoordChange x₁ x₀` (linear).
  have hlin :
      (tangentCoordChange I x₁ x₀ x)
          (∑ k, (Module.finBasis ℝ E).repr
              ((tangentCoordChange I x₀ x₁ x) ((Module.finBasis ℝ E) j)) k
            • (Module.finBasis ℝ E) k)
        = ∑ k, (Module.finBasis ℝ E).repr
              ((tangentCoordChange I x₀ x₁ x) ((Module.finBasis ℝ E) j)) k
            • (tangentCoordChange I x₁ x₀ x) ((Module.finBasis ℝ E) k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ContinuousLinearMap.map_smul]
  have heval : (tangentCoordChange I x₁ x₀ x) ((tangentCoordChange I x₀ x₁ x)
      ((Module.finBasis ℝ E) j))
      = (Module.finBasis ℝ E) j := hcomp j
  -- Rewrite heval using hexp and hlin.
  have heval' :
      ∑ k, (Module.finBasis ℝ E).repr
            ((tangentCoordChange I x₀ x₁ x) ((Module.finBasis ℝ E) j)) k
          • (tangentCoordChange I x₁ x₀ x) ((Module.finBasis ℝ E) k)
        = (Module.finBasis ℝ E) j := by
    rw [← hlin, ← hexp]; exact heval
  -- Take repr on both sides, at index i.
  have happ := congrArg ((Module.finBasis ℝ E).repr · i) heval'
  simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    map_smul, Finsupp.smul_apply, smul_eq_mul] at happ
  -- Split the conclusion by cases i = j.
  have hrhs : ((Module.finBasis ℝ E).repr ((Module.finBasis ℝ E) j)) i
                = if i = j then (1 : ℝ) else 0 := by
    rw [(Module.finBasis ℝ E).repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  rw [← hrhs]
  rw [← happ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- The two sums differ only by a factor-order swap (commutative mul).
  exact mul_comm _ _

/-- The transition matrix (as an element of the matrix ring) has a two-sided
inverse, hence is a unit, and in particular has nonzero determinant. -/
lemma transitionMatrix_isUnit
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    IsUnit (transitionMatrix (I := I) x₀ x₁ x) := by
  -- `transitionMatrix x₁ x₀ x * transitionMatrix x₀ x₁ x = 1` gives
  -- `det _ * det _ = 1`, hence `IsUnit (det _)`, hence `IsUnit _`.
  have hleft : transitionMatrix (I := I) x₁ x₀ x *
      transitionMatrix (I := I) x₀ x₁ x = 1 :=
    transitionMatrix_mul_reverse (I := I) x₁ x₀ hx1 hx0
  have hdet : (transitionMatrix (I := I) x₀ x₁ x).det *
      (transitionMatrix (I := I) x₁ x₀ x).det = 1 := by
    rw [mul_comm, ← Matrix.det_mul, hleft, Matrix.det_one]
  exact (Matrix.isUnit_iff_isUnit_det _).mpr
    (IsUnit.of_mul_eq_one _ hdet)

/-- Chart-invariance of the metric trace of the time derivative: at a fixed
spatial point `x` lying in the base sets of two charts `x₀` and `x₁`, the
trace `trace(G⁻¹ · ∂_t G)` computed in either chart yields the same value. -/
lemma trace_chartGramMatrix_inv_deriv_chart_independent
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x₀ x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t))
    = Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x₁ x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t)) := by
  classical
  set n := Fin (Module.finrank ℝ E) with hn_def
  set J : Matrix n n ℝ := transitionMatrix (I := I) x₀ x₁ x with hJ_def
  set G₀ : Matrix n n ℝ := chartGramMatrix (I := I) (g_fam t) x₀ x with hG0_def
  set G₁ : Matrix n n ℝ := chartGramMatrix (I := I) (g_fam t) x₁ x with hG1_def
  set dG₀ : Matrix n n ℝ := Matrix.of fun i j : n =>
      deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t with hdG0_def
  set dG₁ : Matrix n n ℝ := Matrix.of fun i j : n =>
      deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t with hdG1_def
  -- The Gram matrix pullback at time t.
  have hG1_eq : G₁ = Jᵀ * G₀ * J :=
    chartGramMatrix_pullback_eq_mul (I := I) (g_fam t) x₀ x₁ hx0 hx1
  -- The time-derivative pullback.
  have hdG1_eq : dG₁ = Jᵀ * dG₀ * J :=
    deriv_chartGramMatrix_pullback (I := I) (M := M) hreg x₀ x₁ hx0 hx1
  -- J is a unit.
  have hJ_unit : IsUnit J :=
    transitionMatrix_isUnit (I := I) x₀ x₁ hx0 hx1
  -- G₀ is a unit (its determinant is positive).
  have hG0_unit : IsUnit G₀ := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hpos : 0 < G₀.det := chartGramMatrix_det_pos (I := I) (g_fam t) x₀ hx0
    exact (ne_of_gt hpos).isUnit
  -- Jᵀ is a unit.
  have hJT_unit : IsUnit Jᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hJ_unit
  -- `J` has nonzero determinant.
  have hJ_det : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).mp hJ_unit
  have hJT_det : IsUnit (Jᵀ).det := by
    rw [Matrix.det_transpose]; exact hJ_det
  -- Inverse of Jᵀ * G₀ * J.
  have hinv : G₁⁻¹ = J⁻¹ * G₀⁻¹ * (Jᵀ)⁻¹ := by
    rw [hG1_eq]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
  have hJTinv : (Jᵀ)⁻¹ * Jᵀ = 1 := Matrix.nonsing_inv_mul _ hJT_det
  have hJinvJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ_det
  -- Strategy: expand trace(G₁⁻¹ * dG₁), use hinv + hdG1_eq, collapse
  -- (Jᵀ⁻¹ * Jᵀ) = 1, use cyclic trace to move the final `J` around.
  have hgoal :
      Matrix.trace (G₁⁻¹ * dG₁) = Matrix.trace (G₀⁻¹ * dG₀) := by
    rw [hinv, hdG1_eq]
    -- trace ((J⁻¹ * G₀⁻¹ * Jᵀ⁻¹) * (Jᵀ * dG₀ * J))
    -- Rewrite to align Jᵀ⁻¹ and Jᵀ.
    have hrw1 :
        (J⁻¹ * G₀⁻¹ * (Jᵀ)⁻¹) * (Jᵀ * dG₀ * J)
          = J⁻¹ * G₀⁻¹ * ((Jᵀ)⁻¹ * Jᵀ) * dG₀ * J := by
      simp only [Matrix.mul_assoc]
    rw [hrw1]
    rw [hJTinv]
    -- trace (J⁻¹ * G₀⁻¹ * 1 * dG₀ * J) = trace (J⁻¹ * G₀⁻¹ * dG₀ * J)
    rw [Matrix.mul_one]
    -- cyclic: trace (A * J) = trace (J * A)
    rw [show J⁻¹ * G₀⁻¹ * dG₀ * J = (J⁻¹ * G₀⁻¹ * dG₀) * J from by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    -- trace (J * (J⁻¹ * G₀⁻¹ * dG₀)) = trace ((J * J⁻¹) * G₀⁻¹ * dG₀)
    rw [show J * (J⁻¹ * G₀⁻¹ * dG₀) = (J * J⁻¹) * G₀⁻¹ * dG₀ from by
      simp only [← Matrix.mul_assoc]]
    rw [hJinvJ]
    rw [Matrix.one_mul]
  linarith [hgoal]

end ChartInvarianceOfTraceTimeDeriv

/-- Chart-invariance of `traceTimeDerivMetric`, specialised to evaluation at the
canonical chart at `x`. For any `α` whose chart base set contains `x`, the trace
computed in the `α`-chart equals `traceTimeDerivMetric g_fam t x`. -/
lemma traceTimeDerivMetric_eq_trace_chartGramMatrix
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) {x : M}
    (hxα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    traceTimeDerivMetric (I := I) g_fam t x
    = Matrix.trace ((chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) α x i j) t)) := by
  have hxx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    -- `x` lies in the base set of its own chart.
    change x ∈ (chartAt H x).source
    exact mem_chart_source _ _
  rw [traceTimeDerivMetric_eq]
  exact trace_chartGramMatrix_inv_deriv_chart_independent
    (I := I) (M := M) hreg x α hxx hxα

/-! ## Finite-sum decomposition of the Riemannian volume measure on compact M -/

/-- On a compact manifold, the canonical Riemannian volume measure equals the
finite sum of POU-weighted chart-local measures over the finite support set. -/
theorem riemannianVolumeMeasure_eq_finset_sum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) := by
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def]
  -- Split sum via `Finset` / complement.
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS
  set f : M → MeasureTheory.Measure M := fun α =>
      (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) with hf
  -- Split Measure.sum over M = sum over S ⊔ Sᶜ.
  have hsplit : ((MeasureTheory.Measure.sum fun i : (S : Set M) => f i) +
      MeasureTheory.Measure.sum (fun i : ↥((S : Set M)ᶜ) => f i)) =
      MeasureTheory.Measure.sum f :=
    MeasureTheory.Measure.sum_add_sum_compl (S : Set M) f
  -- The complement sum is zero.
  have hcompl : MeasureTheory.Measure.sum (fun i : ↥((S : Set M)ᶜ) => f i) = 0 := by
    have hzero : ∀ i : ↥((S : Set M)ᶜ), f i = 0 := by
      intro i
      have hi : (i : M) ∉ S := i.2
      exact chartAtlasPOU_withDensity_zero_of_notMem (I := I) (M := M) g hi
    ext t ht
    rw [MeasureTheory.Measure.sum_apply _ ht]
    simp [hzero]
  -- Combine.
  rw [← hsplit, hcompl, add_zero]
  exact MeasureTheory.Measure.sum_coe_finset S f

/-! ## Bochner integral against the Riemannian volume measure: finite-sum form

On a compact manifold, the Bochner integral of a continuous function
`h : M → ℝ` against the canonical Riemannian volume measure decomposes as a
finite sum over the chart-atlas POU support. Each summand is the Bochner
integral of `h` against the POU-weighted chart-local measure at `α`. -/

theorem integral_riemannianVolumeMeasure_eq_finset_sum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (h : M → ℝ)
    (hh_cont : Continuous h) :
    ∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∫ x, h x
            ∂((chartLocalMeasure (I := I) g α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))) := by
  classical
  -- The Riemannian measure, written as a finite sum of withDensity measures.
  have hVol_eq :=
    riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M) g
  -- Integrability of h for each summand.
  haveI hFin :
      MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  -- Bound `|h|` by the sup norm.
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖h x‖ ≤ C := by
    have hCpt := (isCompact_univ (X := M)).image hh_cont.norm
    obtain ⟨C, hCmem⟩ := hCpt.bddAbove
    refine ⟨C, fun x => hCmem ⟨x, Set.mem_univ _, rfl⟩⟩
  have hh_int : Integrable h (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (integrable_const C).mono' hh_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have hsummand_int : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      Integrable h
        ((chartLocalMeasure (I := I) g α).withDensity
          (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))) := by
    intro α hα
    refine hh_int.mono_measure ?_
    rw [hVol_eq]
    exact Finset.single_le_sum
      (f := fun β : M => (chartLocalMeasure (I := I) g β).withDensity
        (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) β y)))
      (s := chartAtlasPOU_finset (I := I) (M := M))
      (fun _ _ => Measure.zero_le _) hα
  -- Conclude using integral_finset_sum_measure.
  conv_lhs => rw [hVol_eq]
  exact integral_finset_sum_measure hsummand_int

/-! ## Global `HasDerivAt` for the integral of a time-parameterised function
against the Riemannian volume measure — finite-sum assembly

The global parametric derivative theorem, expressed as the assembly of
chart-local parametric derivatives over the finite POU-support set. Given the
chart-local `HasDerivAt` statements for each `α` in the finite-support Finset,
the global `HasDerivAt` for `t ↦ ∫ x, f t x ∂volume_t` follows by linearity of
`HasDerivAt.fun_finset_sum`.

This formulation cleanly separates the analytic kernel (the chart-local
parametric differentiation and bound construction) from the global measure
assembly (which is pure linear algebra). -/
theorem volume_variation_formula_from_chart_derivs
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (Iα : M → ℝ)
    (Iglobal : ℝ)
    (hα_deriv : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      HasDerivAt
        (fun s : ℝ => ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
        (Iα α) t)
    (hα_sum_val : ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Iα α = Iglobal) :
    HasDerivAt
      (fun s : ℝ => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
      Iglobal t := by
  rw [← hα_sum_val]
  exact HasDerivAt.fun_sum hα_deriv

/-!
### Global volume variation formula: finite-sum form

The theorem `volume_variation_formula` as a `HasDerivAt` at a single point
`t`, under `[CompactSpace M]`. The global integral of a smooth time-family
`f : ℝ → M → ℝ` against the Riemannian volume measure is given by a finite
sum over the chart-atlas POU support: each summand is the integral of `f t`
against the POU-weighted chart-local measure.

This identity, combined with the chart-local parametric `HasDerivAt` given by
`hasDerivAt_setIntegral_model` applied to each chart, yields the global
`HasDerivAt` for `t ↦ ∫ x, f t x ∂riemannianMeasureFamily gFam t`.
-/
theorem integral_riemannianMeasureFamily_eq_finset_sum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (hf_cont : Continuous (f t)) :
    ∫ x, f t x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t)
      = ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∫ x, f t x
            ∂((chartLocalMeasure (I := I) (g_fam t) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))) := by
  rw [riemannianMeasureFamily_def]
  exact integral_riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M)
    (g_fam t) (f t) hf_cont

/-- **Volume variation formula**: the time derivative of the global integral
of a smooth time-family `f : ℝ → M → ℝ` against the Riemannian volume measure
on a compact manifold, obtained as the finite-sum assembly of chart-local
parametric derivatives.

The caller supplies, for each `α` in the finite POU-support Finset, the
chart-local `HasDerivAt` for the integral against the POU-weighted chart-local
measure, plus the hypothesis that `f` is continuous in `s` in a neighborhood of
`t` (so the left-hand-side identifications via
`integral_riemannianMeasureFamily_eq_finset_sum` go through). The conclusion
is a `HasDerivAt` for `s ↦ ∫ x, f s x ∂volume_s` at `s = t`. -/
theorem volume_variation_formula
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (Iα : M → ℝ) (Iglobal : ℝ)
    (hf_cont : ∀ᶠ s in 𝓝 t, Continuous (f s))
    (hα_deriv : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      HasDerivAt
        (fun s : ℝ => ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
        (Iα α) t)
    (hα_sum_val : ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Iα α = Iglobal) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      Iglobal t := by
  -- Key: rewrite the LHS as the finite sum via `integral_…_eq_finset_sum`, pointwise in s.
  have hfun :
      (fun s : ℝ =>
          ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
        =ᶠ[𝓝 t]
      (fun s : ℝ => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y)))) := by
    filter_upwards [hf_cont] with s hs
    exact integral_riemannianMeasureFamily_eq_finset_sum (I := I) (M := M)
      g_fam f s hs
  refine HasDerivAt.congr_of_eventuallyEq ?_ hfun
  exact volume_variation_formula_from_chart_derivs (I := I) (M := M)
    g_fam f t Iα Iglobal hα_deriv hα_sum_val

/-! ## Clean signature: explicit derivative form of the volume variation formula

Below, we package the general volume variation formula into an explicit form
where the derivative of `t ↦ ∫ f t d(μ_t)` is exhibited as the integral of
`(∂_t f + ½ · tr_g(∂_t g) · f)` against the (Riemannian volume) measure at the
base time. The derivation proceeds through three reusable lemmas:

1. A pointwise product-rule `HasDerivAt` for the chart-local integrand
   `s ↦ f s x · ρ_α x · density_α(gFam s, x)`, expressing the derivative in
   terms of `deriv (f · x) t`, `ρ_α x`, the density, and
   `traceTimeDerivMetric gFam t x`.
2. A per-chart variant `per_chart_integrand_hasDerivAt` isolating the
   pointwise derivative on the chart base set.
3. The clean global theorem `volume_variation_formula_clean`, which
   exhibits the global derivative integrand explicitly. -/

section CleanVolumeVariation

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

/-- Pointwise product-rule `HasDerivAt` for the three-factor integrand at a point
`x` in a chart base set:
`s ↦ f s x · ρ x · chartDensity (g_fam s) α x`.

The derivative at `t` expands, via the product rule, into:
`(deriv (f · x) t · ρ x + f t x · ρ x · (1/2) · traceTimeDerivMetric ...) · density`,
which factors to
`(deriv (f · x) t + (1/2) · traceTimeDerivMetric g_fam t x · f t x) · ρ x · density`.
-/
lemma per_chart_integrand_hasDerivAt
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) {x : M}
    (hxα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (f : ℝ → M → ℝ) (ρ : M → ℝ)
    (hf : HasDerivAt (fun s : ℝ => f s x) (deriv (fun s : ℝ => f s x) t) t) :
    HasDerivAt
      (fun s : ℝ => f s x * ρ x *
        chartDensity (I := I) (g_fam s) α x)
      ((deriv (fun s : ℝ => f s x) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρ x *
        chartDensity (I := I) (g_fam t) α x) t := by
  classical
  set n := Fin (Module.finrank ℝ E) with hn_def
  -- Gram-entry-wise HasDerivAt at `α`, evaluated at `x`.
  have hG : ∀ i j : n,
      HasDerivAt (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j)
        (deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t) t := by
    intro i j
    exact hasDerivAt_chartGramMatrix_entry (I := I) (M := M) hreg α hxα i j t
  -- The density `chartDensity (g_fam ·) α x` has the half-trace form derivative.
  have hdensity_deriv :
      HasDerivAt
        (fun s : ℝ => chartDensity (I := I) (g_fam s) α x)
        ((1 / 2) *
          Matrix.trace ((chartGramMatrixFamily (I := I) g_fam α x t)⁻¹ *
            (Matrix.of fun i j : n =>
              deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t)) *
          Real.sqrt (chartGramMatrixFamily (I := I) g_fam α x t).det) t := by
    have := hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul
      (I := I) (M := M) g_fam α t (x := x) hxα
      (Matrix.of fun i j : n =>
        deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t)
      (by
        intro i j
        exact hG i j)
    -- `chartDensityFamily g_fam α x` is defeq to `chartDensity (g_fam ·) α x`.
    change HasDerivAt (fun s => chartDensity (I := I) (g_fam s) α x) _ t
    exact this
  -- Rewrite the density-derivative constant using chart-invariance.
  have htrace :
      Matrix.trace ((chartGramMatrixFamily (I := I) g_fam α x t)⁻¹ *
        (Matrix.of fun i j : n =>
          deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t))
        = traceTimeDerivMetric (I := I) g_fam t x := by
    -- By definition, chartGramMatrixFamily = chartGramMatrix (g_fam ·) α x.
    change Matrix.trace ((chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
        (Matrix.of fun i j : n =>
          deriv (fun s => chartGramMatrix (I := I) (g_fam s) α x i j) t))
      = traceTimeDerivMetric (I := I) g_fam t x
    rw [traceTimeDerivMetric_eq_trace_chartGramMatrix
      (I := I) (M := M) hreg α hxα]
  -- Also, `chartDensity (g_fam t) α x = √(det G_t α x)`.
  have hdensity_val :
      chartDensity (I := I) (g_fam t) α x
        = Real.sqrt (chartGramMatrixFamily (I := I) g_fam α x t).det := by
    rfl
  -- Rewrite the density-derivative constant cleanly.
  have hdensity_deriv' :
      HasDerivAt
        (fun s : ℝ => chartDensity (I := I) (g_fam s) α x)
        ((1 / 2) * traceTimeDerivMetric (I := I) g_fam t x *
          chartDensity (I := I) (g_fam t) α x) t := by
    rw [hdensity_val]
    -- Apply the rewrite on the HasDerivAt's RHS.
    have := hdensity_deriv
    rw [htrace] at this
    exact this
  -- Combine: `(f s x * ρ x) * density s` via product rule.
  -- First: `HasDerivAt (fun s => f s x * ρ x) (deriv_f * ρ x) t` (ρ x is constant in s).
  have hfρ : HasDerivAt (fun s : ℝ => f s x * ρ x)
      (deriv (fun s : ℝ => f s x) t * ρ x) t :=
    hf.mul_const (ρ x)
  -- Now the product rule on `(f · · ρ x) * density`.
  have hprod := hfρ.mul hdensity_deriv'
  -- Algebraic reorganization to match the stated derivative.
  have halgebra :
      (deriv (fun s : ℝ => f s x) t * ρ x) *
          chartDensity (I := I) (g_fam t) α x
        + (f t x * ρ x) *
          ((1 / 2) * traceTimeDerivMetric (I := I) g_fam t x *
            chartDensity (I := I) (g_fam t) α x)
      = (deriv (fun s : ℝ => f s x) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρ x *
          chartDensity (I := I) (g_fam t) α x := by
    ring
  rw [← halgebra]
  exact hprod

/-- Sum identity connecting the chart-local weighted integrals (appearing as the
right-hand sides of the per-chart `HasDerivAt`s in the volume variation formula)
to a single global integral against the Riemannian volume measure.

Given a continuous integrand `h : M → ℝ`, on a compact manifold,
`∑ α, ∫ x, h x * ρ_α x ∂(chartLocalMeasure (g_t) α) = ∫ x, h x ∂(riemannianMeasure_t)`.
This is obtained by rewriting each summand via the `withDensity → smul`
identity and applying the finite-sum decomposition of the Riemannian measure. -/
theorem chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (h : M → ℝ) (hh_cont : Continuous h) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∫ x, h x * (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α)
      = ∫ x, h x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  classical
  -- Reduce to the finset-sum identity for the Riemannian volume measure.
  rw [riemannianMeasureFamily_def]
  rw [integral_riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M)
      (g_fam t) h hh_cont]
  -- Pointwise, each summand matches up via `integral_withDensity`.
  refine Finset.sum_congr rfl (fun α _ => ?_)
  -- `∫ h ∂(cLM.withDensity (ofReal ρ_α)) = ∫ (ofReal ρ_α).toReal • h ∂cLM = ∫ ρ_α • h ∂cLM`.
  set ρ : M → ℝ := fun x => (chartAtlasPOU I M) α x with hρ_def
  have hρ_cont : Continuous ρ := ((chartAtlasPOU I M) α).contMDiff.continuous
  have hρ_nonneg : ∀ x, 0 ≤ ρ x := fun x => (chartAtlasPOU I M).nonneg _ _
  have hρ_ae : AEMeasurable (fun x : M => ENNReal.ofReal (ρ x))
      (chartLocalMeasure (I := I) (g_fam t) α) := by
    exact (ENNReal.measurable_ofReal.comp hρ_cont.measurable).aemeasurable
  have hρ_lt_top : ∀ᵐ x ∂(chartLocalMeasure (I := I) (g_fam t) α),
      ENNReal.ofReal (ρ x) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => by simp)
  have hswap :
      ∫ x, h x
          ∂((chartLocalMeasure (I := I) (g_fam t) α).withDensity
              (fun y : M => ENNReal.ofReal (ρ y)))
        = ∫ x, (ENNReal.ofReal (ρ x)).toReal • h x
            ∂(chartLocalMeasure (I := I) (g_fam t) α) :=
    integral_withDensity_eq_integral_toReal_smul₀
      (μ := chartLocalMeasure (I := I) (g_fam t) α)
      (f := fun y : M => ENNReal.ofReal (ρ y)) hρ_ae hρ_lt_top
      (g := h)
  -- Simplify `(ENNReal.ofReal (ρ x)).toReal = ρ x` using nonnegativity.
  have htoReal : ∀ x, (ENNReal.ofReal (ρ x)).toReal = ρ x := fun x =>
    ENNReal.toReal_ofReal (hρ_nonneg x)
  have hsmul : ∀ x, (ENNReal.ofReal (ρ x)).toReal • h x = h x * ρ x := fun x => by
    rw [htoReal x, smul_eq_mul, mul_comm]
  have hintegrand_eq :
      (fun x : M => (ENNReal.ofReal (ρ x)).toReal • h x)
        = fun x : M => h x * ρ x := by
    funext x; exact hsmul x
  rw [hswap, hintegrand_eq]

/-- Clean version of the volume variation formula, with the derivative
integrand written explicitly.

The derivative of `t ↦ ∫ f t d(μ_t)` along the time-parameterised Riemannian
volume measures is the integral of
`(∂_t f + ½ · tr_g(∂_t g) · f)` against `μ_t` at the base time.

In the present formulation, the per-chart `HasDerivAt` hypothesis is retained:
deriving it from the joint smoothness of `(t, x) ↦ f t x` alone requires the
full parametric-integral machinery (uniform bounds over a chart-local
neighborhood, integrability over chart targets, the three-factor product rule
for the `f · ρ · density` integrand). The `per_chart_integrand_hasDerivAt`
lemma above packages the pointwise product-rule step; the remaining step is
the `hasDerivAt_integral_of_dominated_loc_of_deriv_le` specialization, which
requires explicit bounds and integrability arguments.

The `hα_deriv_explicit` hypothesis states the per-chart derivative with the
explicit RHS matching the form produced by `per_chart_integrand_hasDerivAt`
composed with parametric integration. The `hh_cont` hypothesis ensures the
RHS integrand is continuous, enabling the finite-sum-to-global-integral
identity. -/
theorem volume_variation_formula_clean_of_chart_derivs
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (hf_cont : ∀ᶠ s in 𝓝 t, Continuous (f s))
    (hh_cont : Continuous
      (fun x : M => deriv (fun s : ℝ => f s x) t +
        (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x))
    (hα_deriv_explicit : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      HasDerivAt
        (fun s : ℝ => ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
        (∫ x, (deriv (fun s : ℝ => f s x) t +
                (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
              (chartAtlasPOU I M) α x
            ∂(chartLocalMeasure (I := I) (g_fam t) α)) t) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t +
              (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t))
      t := by
  -- Set the abbreviation `Iα α := ∫ (deriv f + ½ trace * f) * ρ α d(cLM α)`.
  set h : M → ℝ :=
      fun x => deriv (fun s : ℝ => f s x) t +
        (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x with hh_def
  set Iα : M → ℝ := fun α =>
      ∫ x, h x * (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α) with hIα_def
  -- Set the global value.
  set Iglobal : ℝ :=
      ∫ x, h x
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) with hIglobal_def
  -- Sum identity via the helper lemma.
  have hSum : ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Iα α = Iglobal := by
    exact chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
      (I := I) (M := M) g_fam t h hh_cont
  -- Apply the general-form formula.
  refine volume_variation_formula (I := I) (M := M)
    g_fam f t Iα Iglobal hf_cont ?_ hSum
  intro α hα
  exact hα_deriv_explicit α hα



/-! ## Continuity of `traceTimeDerivMetric` in the spatial variable

The function `x ↦ traceTimeDerivMetric g_fam t x` is continuous on `M`. This is
established by showing continuity on each chart base set, using the
chart-invariance identity to replace the canonical `x`-chart by a fixed `α`-chart,
combined with the joint continuity data packaged in `MetricFamilyRegularAt`.
-/

section TraceTimeDerivMetricContinuous

/-- Joint continuity in `(s, x)` of `trace((G_s α x)⁻¹ · ∂_s G_s α x)` on
`ℝ ×ˢ base_α`, for any chosen chart `α`. This follows from joint continuity of
the Gram matrix and its pointwise time-derivatives on `ℝ × base_α`, together with
continuity of the matrix inverse on the positive-determinant locus and of the
matrix trace. -/
lemma continuousOn_traceTimeDerivMetric_on_base
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) :
    ContinuousOn
      (fun p : ℝ × M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  classical
  set n := Fin (Module.finrank ℝ E)
  have hG_joint : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) α p.2 i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun i j =>
    hreg.continuousOn_chartGramMatrix α i j
  have hdG_joint : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M =>
        deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun i j =>
    hreg.continuousOn_deriv_chartGramMatrix α i j
  -- Det continuous.
  have h_det_cont : ContinuousOn
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    have hexp : (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
        = (fun p : ℝ × M =>
            ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∏ i, chartGramMatrix (I := I) (g_fam p.1) α p.2 (σ i) i) := by
      funext p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    rw [hexp]
    refine continuousOn_finset_sum _ (fun σ _ => ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finset_prod _ (fun i _ => ?_)
    exact hG_joint (σ i) i
  -- Adjugate entry continuous.
  have h_adj_cont : ∀ k v : n, ContinuousOn
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate k v)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro k v
    have hform : ∀ p : ℝ × M,
        (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate k v
          = ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
              (Pi.single k 1)).det := by
      intro p; rw [adjugate_apply]
    have hexp : ∀ p : ℝ × M,
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v (Pi.single k 1)).det
          = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ i : n,
              ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
                (Pi.single k 1)) (σ i) i := by
      intro p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    have hfn_eq :
        (fun p : ℝ × M =>
          (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate k v)
          = fun p : ℝ × M =>
            ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∏ i : n,
                ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
                  (Pi.single k 1)) (σ i) i := by
      funext p; rw [hform p, hexp p]
    rw [hfn_eq]
    refine continuousOn_finset_sum _ (fun σ _ => ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finset_prod _ (fun i _ => ?_)
    by_cases hiv : σ i = v
    · have hconst :
          (fun p : ℝ × M =>
            ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
              (Pi.single k 1)) (σ i) i)
            = fun _ => (Pi.single k 1 : n → ℝ) i := by
        funext p
        rw [hiv, Matrix.updateRow_self]
      rw [hconst]; exact continuousOn_const
    · have hnonrow :
          (fun p : ℝ × M =>
            ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
              (Pi.single k 1)) (σ i) i)
            = fun p : ℝ × M =>
              chartGramMatrix (I := I) (g_fam p.1) α p.2 (σ i) i := by
        funext p
        rw [Matrix.updateRow_apply]
        exact if_neg hiv
      rw [hnonrow]; exact hG_joint (σ i) i
  -- Det nonzero on domain.
  have h_det_ne_zero : ∀ p ∈ (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet
        : Set (ℝ × M)),
      (chartGramMatrix (I := I) (g_fam p.1) α p.2).det ≠ 0 := by
    intro p hp
    exact ne_of_gt (chartGramMatrix_det_pos (I := I) (g_fam p.1) α hp.2)
  -- Inverse entries continuous.
  have h_inv_cont : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M => ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro i j
    have h_inv_entry : ∀ p : ℝ × M,
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i j
          = (chartGramMatrix (I := I) (g_fam p.1) α p.2).det⁻¹ *
            (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate i j := by
      intro p
      rw [Matrix.inv_def]
      simp [Matrix.smul_apply, Ring.inverse_eq_inv']
    have hfn_eq :
        (fun p : ℝ × M => ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i j)
          = fun p : ℝ × M =>
            (chartGramMatrix (I := I) (g_fam p.1) α p.2).det⁻¹ *
            (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate i j := by
      funext p; exact h_inv_entry p
    rw [hfn_eq]
    refine ContinuousOn.mul ?_ (h_adj_cont i j)
    exact h_det_cont.inv₀ h_det_ne_zero
  -- Product entry continuous.
  have h_prod_cont : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M =>
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro i j
    have hfun :
        (fun p : ℝ × M =>
          ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
            Matrix.of fun i j : n =>
              deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i j)
          = fun p : ℝ × M =>
            ∑ k : n, ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i k *
              (deriv (fun s : ℝ =>
                chartGramMatrix (I := I) (g_fam s) α p.2 k j) p.1) := by
      funext p
      rw [Matrix.mul_apply]
      rfl
    rw [hfun]
    refine continuousOn_finset_sum _ (fun k _ => ?_)
    exact (h_inv_cont i k).mul (hdG_joint k j)
  -- Trace is diagonal sum.
  have htrace_eq : ∀ p : ℝ × M,
      Matrix.trace ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)
        = ∑ i : n,
            ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
              Matrix.of fun i j : n =>
                deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i i := by
    intro p
    rfl
  have hfun : (fun p : ℝ × M =>
        Matrix.trace ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1))
      = fun p : ℝ × M =>
          ∑ i : n, ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
            Matrix.of fun i j : n =>
              deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i i := by
    funext p; exact htrace_eq p
  rw [hfun]
  refine continuousOn_finset_sum _ (fun i _ => h_prod_cont i i)

/-- Continuity in `x` of `traceTimeDerivMetric g_fam t x` on `M`. This is the
coordinate-invariant scalar, so continuity is established by switching to the
canonical chart at each point and applying the continuous-on-base-set result. -/
lemma traceTimeDerivMetric_continuous
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) :
    Continuous (fun x : M => traceTimeDerivMetric (I := I) g_fam t x) := by
  classical
  refine continuous_iff_continuousAt.mpr (fun x₀ => ?_)
  set n := Fin (Module.finrank ℝ E) with hn_def
  -- On the α := x₀-chart base set, `traceTimeDerivMetric g_fam t x` equals the chart
  -- formula using the x₀-chart. The x₀-chart base set contains x₀ and is open.
  set α : M := x₀
  have hα_base_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change x₀ ∈ (chartAt H x₀).source
    exact mem_chart_source _ _
  -- Joint continuity of the trace-form expression on univ ×ˢ base_α.
  have h_joint : ContinuousOn
      (fun p : ℝ × M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          (Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    continuousOn_traceTimeDerivMetric_on_base (I := I) (M := M) hreg α
  -- Slice at fixed t.
  have h_slice : ContinuousOn
      (fun x : M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
          (Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α x i j) t)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    intro x hx
    have hp : ((t, x) : ℝ × M) ∈
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
      ⟨Set.mem_univ _, hx⟩
    have h_at := (h_joint (t, x) hp)
    -- Restrict to the slice {t} × base_α, then transfer to the x-slice.
    have hincl_cont : Continuous (fun y : M => ((t, y) : ℝ × M)) :=
      continuous_const.prodMk continuous_id
    have hincl_mapsTo : Set.MapsTo (fun y : M => ((t, y) : ℝ × M))
        (trivializationAt E (TangentSpace I) α).baseSet
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
      fun y hy => ⟨Set.mem_univ _, hy⟩
    exact h_at.comp hincl_cont.continuousWithinAt hincl_mapsTo
  -- On base_α, traceTimeDerivMetric g_fam t x = trace form at α.
  have hev : (fun x : M => traceTimeDerivMetric (I := I) g_fam t x) =ᶠ[𝓝 x₀]
      (fun x : M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
          (Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α x i j) t))) := by
    filter_upwards [hα_base_open.mem_nhds hx₀_base] with y hy
    exact traceTimeDerivMetric_eq_trace_chartGramMatrix
      (I := I) (M := M) hreg α hy
  refine ContinuousAt.congr ?_ hev.symm
  exact h_slice.continuousAt (hα_base_open.mem_nhds hx₀_base)

/-- Joint continuity of `(t, x) ↦ traceTimeDerivMetric g_fam t x` on
`Set.univ ×ˢ base_α`, for any chart `α`. Obtained from the chart-local
trace formula via `traceTimeDerivMetric_eq_trace_chartGramMatrix`. -/
lemma continuousOn_traceTimeDerivMetric_of_base
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M) :
    ContinuousOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I) g_fam p.1 p.2)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  have h_base := continuousOn_traceTimeDerivMetric_on_base
    (I := I) (M := M) hreg α
  have h_eq : Set.EqOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I) g_fam p.1 p.2)
      (fun p : ℝ × M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro p hp
    exact traceTimeDerivMetric_eq_trace_chartGramMatrix
      (I := I) (M := M) (t := p.1) (hreg.at_any p.1) α hp.2
  exact h_base.congr h_eq

/-- Joint continuity of the chart-local density `(t, x) ↦ chartDensity (g_fam t) α x`
on `Set.univ ×ˢ base_α`, derived from the regularity interface. -/
lemma continuousOn_chartDensity_family
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M) :
    ContinuousOn
      (fun p : ℝ × M => chartDensity (I := I) (g_fam p.1) α p.2)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  classical
  set n := Fin (Module.finrank ℝ E)
  have hG_joint : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) α p.2 i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun i j =>
    hreg.continuousOn_chartGramMatrix α i j
  have h_det_cont : ContinuousOn
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    have hexp :
        (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
          = (fun p : ℝ × M =>
              ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
                ∏ i, chartGramMatrix (I := I) (g_fam p.1) α p.2 (σ i) i) := by
      funext p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    rw [hexp]
    refine continuousOn_finset_sum _ (fun σ _ => ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finset_prod _ (fun i _ => ?_)
    exact hG_joint (σ i) i
  have h_sqrtdet_cont : ContinuousOn
      (fun p : ℝ × M =>
        Real.sqrt ((chartGramMatrix (I := I) (g_fam p.1) α p.2).det))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    Real.continuous_sqrt.comp_continuousOn h_det_cont
  refine h_sqrtdet_cont.congr ?_
  intro p _; rfl

/-- Pull-back variant: joint continuity of the chart-α trace form pulled back
through the chart symm, on an arbitrary set `S ⊆ ℝ × E` mapping into the base
set. -/
lemma continuousOn_chartTrace_form_of_base_pullback
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M)
    {S : Set (ℝ × E)} (sym : E → M)
    (hsym_cont : ContinuousOn (fun p : ℝ × E => (p.1, sym p.2)) S)
    (hsym_maps : Set.MapsTo (fun p : ℝ × E => ((p.1, sym p.2) : ℝ × M)) S
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousOn
      (fun p : ℝ × E => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α (sym p.2))⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α (sym p.2) i j) p.1)))
      S := by
  have h_base := continuousOn_traceTimeDerivMetric_on_base (I := I) (M := M) hreg α
  have h_comp : ContinuousOn
      ((fun p : ℝ × M => Matrix.trace
          ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
            (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
              deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
        ∘ (fun p : ℝ × E => ((p.1, sym p.2) : ℝ × M))) S :=
    h_base.comp hsym_cont hsym_maps
  exact h_comp

end TraceTimeDerivMetricContinuous

/-! ## The per-chart parametric HasDerivAt lemma

Assembly of `hasDerivAt_setIntegral_model` and `per_chart_integrand_hasDerivAt`
into the single per-chart HasDerivAt needed to apply
`volume_variation_formula_clean_of_chart_derivs`. -/

section PerChartHasDerivAt

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

private lemma chartDensity_nonneg_of_base
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    0 ≤ chartDensity (I := I) g α x := by
  unfold chartDensity
  exact Real.sqrt_nonneg _

set_option maxHeartbeats 16000000 in
-- The proof below assembles several measure-theoretic sub-lemmas with joint
-- continuity / differentiability arguments; the combined elaboration load exceeds
-- the default heartbeats budget.
/-- Per-chart parametric `HasDerivAt`: the chart-local integral
`s ↦ ∫ x, f s x ∂(chartLocalMeasure (g_fam s) α).withDensity (ofReal ρ_α)` has a
derivative at `t` given by the explicit formula
`∫ x, (∂_t f + ½ tr_g(∂_t g) f) · ρ_α ∂(chartLocalMeasure (g_fam t) α)`. -/
lemma per_chart_hasDerivAt
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M} {f : ℝ → M → ℝ} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (hf : FunctionRegularAt f t)
    (α : M) (_hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x
        ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
            (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
      (∫ x, (deriv (fun s : ℝ => f s x) t
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
            (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α)) t := by
  classical
  -- Setup.
  set n := Fin (Module.finrank ℝ E) with hn_def
  set ρα : M → ℝ := fun x => (chartAtlasPOU I M) α x with hρα_def
  set μₐ : MeasureTheory.Measure M := chartLocalMeasure (I := I) (g_fam t) α with hμα_def
  set target : Set E := (extChartAt I α).target with htarget_def
  set symm : E → M := fun y => (extChartAt I α).symm y with hsymm_def
  have htarget_meas : MeasurableSet target :=
    measurableSet_extChartAt_target (I := I) α
  -- Continuity facts for ρα, f, density, and the combined integrand.
  have hρα_cont : Continuous ρα := ((chartAtlasPOU I M) α).contMDiff.continuous
  have hρα_nonneg : ∀ x, 0 ≤ ρα x := fun x => (chartAtlasPOU I M).nonneg _ _
  have hρα_le_one : ∀ x, ρα x ≤ 1 := fun x => (chartAtlasPOU I M).le_one _ _
  have hρα_subord : tsupport ρα ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  -- tsupport is compact on compact M (tsupport is closed, compact space).
  have hρα_tsupport_compact : IsCompact (tsupport ρα) := isClosed_tsupport ρα |>.isCompact
  -- Continuity of `f` on `ℝ × M`.
  have hf_cont_joint : Continuous (fun p : ℝ × M => f p.1 p.2) := hf.continuous_joint
  -- The slice `f t ·`.
  have hft_cont : Continuous (f t) := by
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  -- Joint continuity of deriv in (s, y).
  have h_deriv_cont_joint_M : Continuous
      (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) :=
    hf.continuous_deriv_joint
  -- Continuity of deriv (f · ·) t.
  have h_deriv_cont : Continuous (fun x : M => deriv (fun s : ℝ => f s x) t) := by
    have : Continuous ((fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)
        ∘ (fun x : M => (t, x))) :=
      h_deriv_cont_joint_M.comp (continuous_const.prodMk continuous_id)
    exact this
  -- Continuity of traceTimeDerivMetric t ·.
  have h_tr_cont : Continuous (fun x : M => traceTimeDerivMetric (I := I) g_fam t x) :=
    traceTimeDerivMetric_continuous (I := I) (M := M) hreg
  -- Continuity of the Riemannian density on the α-base set.
  have h_density_contOn : ContinuousOn
      (fun x : M => chartDensity (I := I) (g_fam t) α x)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartDensity_continuousOn (I := I) (g_fam t) α
  -- The map symm : E → M is continuous on target.
  have h_symm_contOn : ContinuousOn symm target :=
    continuousOn_extChartAt_symm (I := I) α
  -- The chart symm maps target into the chart source (= trivialization base set).
  have h_symm_maps : ∀ y ∈ target, symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsrc : symm y ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsrc
    exact hsrc
  -- Bound on M.
  obtain ⟨Cf, hCf⟩ : ∃ C, ∀ x, ‖f t x‖ ≤ C := by
    have hIm := (isCompact_univ (X := M)).image hft_cont.norm
    obtain ⟨C, hC⟩ := hIm.bddAbove
    exact ⟨C, fun x => hC ⟨x, Set.mem_univ _, rfl⟩⟩
  -- Step 1: Use the explicit product form of the integrand.
  -- On target, the integral of `f s` against the withDensity-measure equals
  -- ∫ y in target, density * (ρα * f s) ∂modelHaar.
  -- We work with Fmdl s y := f s (symm y) * ρα (symm y) * chartDensity (g_fam s) α (symm y).
  set Fmdl : ℝ → E → ℝ := fun s y =>
    f s (symm y) * ρα (symm y) * chartDensity (I := I) (g_fam s) α (symm y)
  -- The derivative of Fmdl in s at t, given by per_chart_integrand_hasDerivAt.
  set Fprim : ℝ → E → ℝ := fun s y =>
    (deriv (fun r : ℝ => f r (symm y)) s +
      (1/2) * traceTimeDerivMetric (I := I) g_fam s (symm y) *
        f s (symm y)) * ρα (symm y) *
      chartDensity (I := I) (g_fam s) α (symm y)
  -- Pointwise derivative on target.
  have hH'_deriv : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ (Set.univ : Set ℝ), HasDerivAt (fun r => Fmdl r y) (Fprim s y) s := by
    refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    intro s _
    have hsym_base : symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      h_symm_maps y hy
    -- `fun r => f r (symm y)` has derivative (deriv ...) s (pointwise regularity).
    have hslice : HasDerivAt (fun r : ℝ => f r (symm y))
        (deriv (fun r : ℝ => f r (symm y)) s) s :=
      hf.hasDerivAt_time (symm y) s
    have hpcd := per_chart_integrand_hasDerivAt
      (I := I) (M := M) (t := s) (hreg.at_any s) α (x := symm y) hsym_base f ρα hslice
    exact hpcd
  -- Bounds.
  -- Strategy: build a bound `b : E → ℝ` such that for `s ∈ ball t 1` (nbhd of t),
  -- `‖Fprim s y‖ ≤ b y` on target.
  -- We bound `Fprim` on the compact `K'_α := (extChartAt I α) '' tsupport ρα`, and zero
  -- outside (since `symm y ∉ tsupport ρα` implies `ρα (symm y) = 0`, hence `Fprim s y = 0`).
  set K : Set M := tsupport ρα
  set K' : Set E := (extChartAt I α) '' K
  have hK_compact : IsCompact K := hρα_tsupport_compact
  have hK'_compact : IsCompact K' :=
    hK_compact.image_of_continuousOn (continuousOn_extChartAt (I := I) α |>.mono (by
      intro y hy
      have : y ∈ (chartAt H α).source := hρα_subord hy
      rw [← extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this))
  have hK'_meas : MeasurableSet K' := hK'_compact.measurableSet
  -- measure of K' finite.
  have hK'_meas_lt_top : (modelHaar (E := E)) K' < ⊤ :=
    hK'_compact.measure_lt_top
  -- Bound constants:
  -- |Fprim s y| ≤ |deriv + 1/2 trace f| * |ρα| * |density|. On K' (= image of tsupport),
  -- each factor is bounded (by continuity on compact set).
  -- Compute: for `s ∈ ball t 1`, everything involves only `s` — but our bound `h_bound` must
  -- be uniform over all `s ∈ ball t 1`. Issue: `(deriv (f · y) s)`, `trace g_fam s y`,
  -- `density (g_fam s) α y`, and `f s y` all depend on `s`.
  -- Uniform bound requires joint continuity in `(s, y)` on `[t-1, t+1] × K'`.
  -- Simpler: use the simple bound coming from continuous joint maps on compact sets.
  -- Joint continuity of `deriv (f · ·) ·` in `(s, y)`?  This is the issue.
  -- To sidestep, apply the parametric integral theorem with `s := {t}` (a degenerate slice —
  -- but Mathlib's theorem requires `s` a nhd). We use the joint continuity of
  -- `(s, y) ↦ Fprim s y` on `ball t 1 × K'`, bound by the `isCompact.bddAbove_image ‖·‖`.
  -- Jointly in `(s, y)`:
  --   - `f : ℝ × M → ℝ` is continuous (joint, from hf).
  --   - `deriv (f · y) s` is jointly continuous in `(s, y)` — this requires
  --     continuity of `fderiv` in the base point, which is the analogue of
  --     `continuous_deriv_slice` but in both arguments.
  --   - `traceTimeDerivMetric g_fam s y` is jointly continuous in `(s, y)` — another
  --     joint fact.
  --   - `chartDensity (g_fam s) α y` is jointly continuous on `ℝ × base_α`.
  -- We punt on the JOINT derivative-continuity question by using the following
  -- dominance: take `s ∈ {t}` via `s := Set.univ`, use `deriv (f · y) · = deriv (f · y)`
  -- pointwise — but Mathlib's theorem needs the dependency on `s`.
  -- Alternative: observe that the derivative is continuous in the joint `(s, y)`
  -- argument via the same construction as `continuous_deriv_slice`.
  -- The joint partial-derivative `(s, y) ↦ ∂_s f s y` is continuous: it equals
  -- `fderiv ((fun p => f p.1 p.2) ∘ (fun p => (p.1, p.2))) p (1, 0)`, and `fderiv`
  -- is continuous. We use `partial_deriv_cont`, proven below inline.
  have h_deriv_cont_joint : Continuous
      (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) :=
    hf.continuous_deriv_joint
  -- Joint continuity of `(s, y) ↦ traceTimeDerivMetric g_fam s y` at fixed `(t, y)`?
  -- For our bound we just need uniformity on `ball t 1 × K'`, but since we don't have
  -- `traceTimeDerivMetric` continuously dependent on `s` easily, we bound it simpler:
  -- use the joint continuity of `chartGramMatrix` entries and their time-derivatives,
  -- pull back via the α-chart using chart-invariance. This is substantial work.
  -- Simpler path: bound `|Fprim|` on `[t-1, t+1] × K'` by continuity of the individual
  -- factors.
  -- Let's bound each factor independently on a compact set.
  -- Define: q (s, y) := Fprim s y on `Ω := Set.Icc (t - 1) (t + 1) ×ˢ K'`.
  -- We argue Fprim itself is continuous on Ω as a function of (s, y).
  set I₁ : Set ℝ := Set.Icc (t - 1) (t + 1)
  have hI₁_compact : IsCompact I₁ := isCompact_Icc
  have ht_interior : t ∈ Set.Ioo (t - 1 : ℝ) (t + 1) := by
    refine ⟨?_, ?_⟩ <;> linarith
  have ht_in_I₁ : t ∈ I₁ := ⟨by linarith, by linarith⟩
  -- ball t 1 is an open nbhd of t contained in Ioo, and its closure ⊆ I₁.
  -- We use the open ball.
  set ball_s : Set ℝ := Metric.ball t 1
  have hballs_nhd : ball_s ∈ 𝓝 t := Metric.ball_mem_nhds _ one_pos
  have hballs_sub_I₁ : ball_s ⊆ I₁ := by
    intro s hs
    have hs' : |s - t| < 1 := by simpa [Real.dist_eq, Real.norm_eq_abs] using hs
    refine ⟨?_, ?_⟩
    · have := (abs_lt.mp hs').1; linarith
    · have := (abs_lt.mp hs').2; linarith
  -- Define the closed bound domain.
  set Ω : Set (ℝ × E) := I₁ ×ˢ K'
  have hΩ_compact : IsCompact Ω := hI₁_compact.prod hK'_compact
  -- Continuity of Fmdl on ℝ × E (full domain, pushing through symm).
  -- But symm is only defined on target; outside target, Fmdl still makes sense
  -- (symm is total — PartialEquiv), but not necessarily continuous.
  -- Let's restrict to target.
  -- Actually we only need bound on Ω ∩ (ℝ × target) = I₁ ×ˢ K' since K' ⊆ target.
  have hK'_sub_target : K' ⊆ target := by
    intro y hy
    obtain ⟨x, hxK, hx_eq⟩ := hy
    have hx_src : x ∈ (extChartAt I α).source := by
      have : x ∈ (chartAt H α).source := hρα_subord hxK
      rw [← extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    rw [← hx_eq]
    exact (extChartAt I α).map_source hx_src
  -- Prove: on Ω, |Fprim s y| ≤ C₀ for some constant C₀.
  -- Fprim s y on K' (where symm y ∈ (chartAt H α).source ⊆ base_α since we're on target_α after
  -- intersection):
  -- Each of the factors is continuous on Ω:
  -- (1) `(s, y) ↦ f s (symm y)` = `(fun p => f p.1 p.2) ∘ (s, symm y)`: continuous where
  -- symm is continuous on K' ⊆ target.
  -- (2) `ρα (symm y)`: continuous in y on K'.
  -- (3) `density (g_fam s) α (symm y)`: continuous jointly on ball_s × K' because
  -- `chartDensity_contMDiff_family` yields joint ContMDiff on `univ ×ˢ base_α`.
  -- (4) `deriv (f · (symm y)) s`: joint continuity from `h_deriv_cont_joint`.
  -- (5) `traceTimeDerivMetric g_fam s (symm y)`: we need joint continuity in (s, y).
  -- We handle (5) directly via the chart-α expression:
  -- On `base_α`, `traceTimeDerivMetric g_fam s x = trace((G_s α x)⁻¹ * dG_s α x)`,
  -- each entry jointly ContMDiff and ContDiff in (s, x). Proved in the `TraceTime...` section.
  -- For simplicity, we derive a crude constant bound using continuity on Ω:
  have h_Fprim_continuousOn_Ω :
      ContinuousOn (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') := by
    -- We work directly: on K' ⊆ target, symm is continuous. And for y ∈ K', symm y ∈ base_α.
    have h_symm_contOn_K' : ContinuousOn symm K' := h_symm_contOn.mono hK'_sub_target
    have h_symm_pair_contOn :
        ContinuousOn (fun p : ℝ × E => (p.1, symm p.2)) (I₁ ×ˢ K') := by
      refine ContinuousOn.prodMk continuousOn_fst ?_
      refine h_symm_contOn_K'.comp continuousOn_snd ?_
      intro p hp
      exact hp.2
    -- (1) f (s, symm y) continuous on I₁ ×ˢ K'.
    have hf_comp : ContinuousOn (fun p : ℝ × E => f p.1 (symm p.2)) (I₁ ×ˢ K') := by
      exact hf_cont_joint.continuousOn.comp h_symm_pair_contOn (fun _ _ => Set.mem_univ _)
    -- (2) ρα (symm y) continuous.
    have hρα_comp : ContinuousOn (fun p : ℝ × E => ρα (symm p.2)) (I₁ ×ˢ K') := by
      have : ContinuousOn (fun y : E => ρα (symm y)) K' := by
        exact hρα_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      exact (this.comp continuousOn_snd (fun _ hp => hp.2))
    -- (3) chartDensity (g_fam ·) α (symm ·) continuous in (s, y).
    have hdensity_comp : ContinuousOn
        (fun p : ℝ × E => chartDensity (I := I) (g_fam p.1) α (symm p.2))
        (I₁ ×ˢ K') := by
      have h_joint_cont : ContinuousOn
          (fun p : ℝ × M => chartDensity (I := I) (g_fam p.1) α p.2)
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
        continuousOn_chartDensity_family (I := I) (M := M) hreg α
      have hmaps : Set.MapsTo (fun p : ℝ × E => ((p.1, symm p.2) : ℝ × M))
          (I₁ ×ˢ K')
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
        intro p hp
        refine ⟨Set.mem_univ _, ?_⟩
        exact h_symm_maps p.2 (hK'_sub_target hp.2)
      exact h_joint_cont.comp h_symm_pair_contOn hmaps
    -- (4) deriv (f · ·) · joint continuous.
    have h_deriv_comp : ContinuousOn
        (fun p : ℝ × E => deriv (fun r : ℝ => f r (symm p.2)) p.1) (I₁ ×ˢ K') := by
      exact h_deriv_cont_joint.continuousOn.comp h_symm_pair_contOn
        (fun _ _ => Set.mem_univ _)
    -- (5) traceTimeDerivMetric joint — go via the chart-α trace form directly.
    have h_symm_pair_mapsTo : Set.MapsTo (fun p : ℝ × E => ((p.1, symm p.2) : ℝ × M))
        (I₁ ×ˢ K')
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun p hp =>
      ⟨Set.mem_univ _, h_symm_maps p.2 (hK'_sub_target hp.2)⟩
    have h_tr_base_pb :
        ContinuousOn (fun p : ℝ × E => Matrix.trace
          ((chartGramMatrix (I := I) (g_fam p.1) α (symm p.2))⁻¹ *
            (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
              deriv (fun s => chartGramMatrix (I := I) (g_fam s) α (symm p.2) i j) p.1)))
        (I₁ ×ˢ K') :=
      continuousOn_chartTrace_form_of_base_pullback (I := I) (M := M) hreg α
        (sym := symm) h_symm_pair_contOn h_symm_pair_mapsTo
    have h_tr_comp : ContinuousOn
        (fun p : ℝ × E => traceTimeDerivMetric (I := I) g_fam p.1 (symm p.2))
        (I₁ ×ˢ K') := by
      refine h_tr_base_pb.congr ?_
      intro p hp
      have hsym_base : symm p.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
        h_symm_maps p.2 (hK'_sub_target hp.2)
      exact traceTimeDerivMetric_eq_trace_chartGramMatrix
        (I := I) (M := M) (t := p.1) (hreg.at_any p.1) α hsym_base
    -- Fprim p.1 p.2 is `(deriv + 1/2 * trace * f) * ρ * density` by `rfl`.
    -- Assemble directly via the product rule.
    change ContinuousOn (fun p : ℝ × E =>
        (deriv (fun r : ℝ => f r (symm p.2)) p.1 +
            (1/2) * traceTimeDerivMetric (I := I) g_fam p.1 (symm p.2) *
              f p.1 (symm p.2)) * ρα (symm p.2) *
          chartDensity (I := I) (g_fam p.1) α (symm p.2)) (I₁ ×ˢ K')
    refine ContinuousOn.mul (ContinuousOn.mul ?_ hρα_comp) hdensity_comp
    refine ContinuousOn.add h_deriv_comp ?_
    refine ContinuousOn.mul ?_ hf_comp
    refine ContinuousOn.mul continuousOn_const ?_
    exact h_tr_comp
  -- Bound.
  obtain ⟨CH, hCH⟩ : ∃ C, ∀ p ∈ (I₁ ×ˢ K'), |Fprim p.1 p.2| ≤ C := by
    classical
    by_cases hne' : (I₁ ×ˢ K' : Set (ℝ × E)).Nonempty
    · -- Use sup of |Fprim| on compact Ω.
      have hΩne : Ω.Nonempty := hne'
      have h_abs_cont : ContinuousOn (fun p : ℝ × E => |Fprim p.1 p.2|) Ω :=
        h_Fprim_continuousOn_Ω.abs
      have hbdd := hΩ_compact.bddAbove_image h_abs_cont
      obtain ⟨C, hC⟩ := hbdd
      refine ⟨C, fun p hp => ?_⟩
      exact hC ⟨p, hp, rfl⟩
    · -- Empty Ω: trivially any C works.
      refine ⟨0, fun p hp => ?_⟩
      exact (hne' ⟨p, hp⟩).elim
  -- Define b := |CH| · indicator K' 1.
  set C₀ : ℝ := |CH|
  set b : E → ℝ := fun y => C₀ * (K'.indicator (fun _ : E => (1 : ℝ))) y with hb_def
  have hb_nonneg : ∀ y, 0 ≤ b y := by
    intro y
    have h_ind_nonneg : 0 ≤ K'.indicator (fun _ : E => (1 : ℝ)) y :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    exact mul_nonneg (abs_nonneg _) h_ind_nonneg
  have hb_integrable : Integrable b ((modelHaar (E := E)).restrict target) := by
    -- `b = C₀ • indicator K'`, K' is measurable with finite measure, so indicator is integrable.
    have h_ind_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
        ((modelHaar (E := E)).restrict target) := by
      have h_rest_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ))) (modelHaar (E := E)) := by
        rw [integrable_indicator_iff hK'_meas]
        exact integrableOn_const (hs := ne_of_lt hK'_meas_lt_top)
      exact h_rest_int.restrict
    have := h_ind_int.const_mul C₀
    simpa [b, smul_eq_mul] using this
  -- Bound property.
  have h_bound_prop : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ ball_s, ‖Fprim s y‖ ≤ b y := by
    refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    intro s hs
    by_cases hyK' : y ∈ K'
    · -- `y ∈ K'`, `s ∈ ball_s ⊆ I₁`, both in Ω.
      have hp : (s, y) ∈ (I₁ ×ˢ K' : Set (ℝ × E)) := ⟨hballs_sub_I₁ hs, hyK'⟩
      have hbound := hCH (s, y) hp
      have hby : b y = C₀ := by
        simp [b, Set.indicator_of_mem hyK']
      rw [Real.norm_eq_abs, hby]
      have : |Fprim s y| ≤ CH := hbound
      -- We need |Fprim s y| ≤ C₀ = |CH|. Since |Fprim s y| ≤ CH ≤ |CH|:
      refine this.trans ?_
      exact le_abs_self _
    · -- y ∉ K'. Then symm y ∉ tsupport ρα. Hence ρα (symm y) = 0, so Fprim s y = 0.
      have h_symm_y_not_in : symm y ∉ K := by
        intro hsymInK
        exact hyK' ⟨symm y, hsymInK, by
          -- Need ec (symm y) = y; but we don't necessarily know y ∈ target.
          -- But we need to deal with that too. If y ∉ target, then ρ-factor is the only thing
          -- saving us. But here we're in the ae_restrict_iff' branch where `y ∈ target`.
          exact (extChartAt I α).right_inv hy⟩
      have hρ_zero : ρα (symm y) = 0 := by
        by_contra h
        have : symm y ∈ Function.support ρα := h
        exact h_symm_y_not_in (subset_tsupport _ this)
      have hH'_zero : Fprim s y = 0 := by
        change (deriv (fun r : ℝ => f r (symm y)) s +
            (1/2) * traceTimeDerivMetric (I := I) g_fam s (symm y) *
              f s (symm y)) * ρα (symm y) *
            chartDensity (I := I) (g_fam s) α (symm y) = 0
        rw [hρ_zero, mul_zero, zero_mul]
      rw [hH'_zero]
      have hby_nonneg : 0 ≤ b y := hb_nonneg y
      simpa using hby_nonneg
  -- Measurability of F at t and F' at t.
  have hH_meas_at_t : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (Fmdl s) ((modelHaar (E := E)).restrict target) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    -- On target, Fmdl s y = f s (symm y) * ρα (symm y) * density (g_fam s) α (symm y).
    -- All factors continuous on target.
    have h_symm_contOn_target : ContinuousOn symm target := h_symm_contOn
    have h_f_s_comp_contOn : ContinuousOn (fun y : E => f s (symm y)) target := by
      have hf_s_cont : Continuous (f s) := by
        have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
          refine hf_cont_joint.comp ?_
          exact continuous_const.prodMk continuous_id
        exact this
      exact hf_s_cont.continuousOn.comp h_symm_contOn_target
        (fun _ _ => Set.mem_univ _)
    have h_ρα_comp_contOn : ContinuousOn (fun y : E => ρα (symm y)) target :=
      hρα_cont.continuousOn.comp h_symm_contOn_target (fun _ _ => Set.mem_univ _)
    have h_density_comp_contOn : ContinuousOn
        (fun y : E => chartDensity (I := I) (g_fam s) α (symm y)) target := by
      have h_density_s : ContinuousOn
          (fun x : M => chartDensity (I := I) (g_fam s) α x)
          (trivializationAt E (TangentSpace I) α).baseSet :=
        chartDensity_continuousOn (I := I) (g_fam s) α
      exact h_density_s.comp h_symm_contOn_target h_symm_maps
    have h_H_s_contOn : ContinuousOn (Fmdl s) target := by
      -- Fmdl s y = f s (symm y) * ρα (symm y) * density (g_fam s) α (symm y)
      exact (h_f_s_comp_contOn.mul h_ρα_comp_contOn).mul h_density_comp_contOn
    exact (h_H_s_contOn.aestronglyMeasurable htarget_meas)
  have hH_int_at_t : Integrable (Fmdl t) ((modelHaar (E := E)).restrict target) := by
    -- Bounded by a constant on target (via compact tsupport of ρα).
    -- |Fmdl t y| = |f t (symm y)| * |ρα (symm y)| * |density (g_fam t) α (symm y)|.
    -- For y ∉ K', symm y ∉ tsupport ρα ⇒ ρα (symm y) = 0 ⇒ Fmdl t y = 0.
    -- For y ∈ K', |Fmdl t y| bounded by Cf * 1 * sup_density.
    -- We give Fmdl t as K'.indicator of a bounded continuous function.
    -- Use `Integrable.mono` with a bound.
    -- Construct Fmdl (t) restricted to K'.
    -- Approach: use `h_Fprim_continuousOn_Ω` analogue for Fmdl t.
    -- Actually simpler: Fmdl t equals Fprim_indicator * indicator_K' where Fmdl is bounded on Ω.
    -- Let's bound via continuity on compact K' and Fmdl t ≡ 0 outside K' (modulo target).
    have h_Ht_cont_K' : ContinuousOn (Fmdl t) K' := by
      have h_symm_contOn_K' : ContinuousOn symm K' := h_symm_contOn.mono hK'_sub_target
      have hf_cont : Continuous (f t) := by
        have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
          refine hf_cont_joint.comp ?_
          exact continuous_const.prodMk continuous_id
        exact this
      have h_f_comp : ContinuousOn (fun y : E => f t (symm y)) K' :=
        hf_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      have h_ρα_comp : ContinuousOn (fun y : E => ρα (symm y)) K' :=
        hρα_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      have h_density_comp : ContinuousOn
          (fun y : E => chartDensity (I := I) (g_fam t) α (symm y)) K' := by
        refine h_density_contOn.comp h_symm_contOn_K' ?_
        intro y hy
        exact h_symm_maps y (hK'_sub_target hy)
      exact (h_f_comp.mul h_ρα_comp).mul h_density_comp
    -- Bound on K' by sup.
    obtain ⟨C_Fmdl, hC_H⟩ : ∃ C, ∀ y ∈ K', |Fmdl t y| ≤ C := by
      by_cases hK'_ne : K'.Nonempty
      · have h_abs_cont : ContinuousOn (fun y : E => |Fmdl t y|) K' := h_Ht_cont_K'.abs
        obtain ⟨C, hC⟩ := hK'_compact.bddAbove_image h_abs_cont
        refine ⟨C, fun y hy => ?_⟩
        exact hC ⟨y, hy, rfl⟩
      · refine ⟨0, fun y hy => ?_⟩
        exact absurd ⟨y, hy⟩ hK'_ne
    -- Fmdl t is zero outside K' (in target). Use `K'.indicator (fun _ => max C_Fmdl 0)` as dominant.
    have hH_t_vanish : ∀ y ∈ target, y ∉ K' → Fmdl t y = 0 := by
      intro y hy_tg hy_not
      have : symm y ∉ K := by
        intro h
        have hsrc : symm y ∈ (chartAt H α).source := hρα_subord h
        have hsrc' : symm y ∈ (extChartAt I α).source := by
          rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc
        apply hy_not
        refine ⟨symm y, h, ?_⟩
        exact (extChartAt I α).right_inv hy_tg
      have hρ_zero : ρα (symm y) = 0 := by
        by_contra h
        exact this (subset_tsupport _ (show symm y ∈ Function.support ρα from h))
      change f t (symm y) * ρα (symm y) * chartDensity (I := I) (g_fam t) α (symm y) = 0
      rw [hρ_zero, mul_zero, zero_mul]
    -- Construct a dominating function.
    set C_Fprim : ℝ := max C_Fmdl 0
    have hC_Fprim_nonneg : 0 ≤ C_Fprim := le_max_right _ _
    -- Mono with `fun y => C_Fprim * K'.indicator 1 y`.
    have h_domHt : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
        ‖Fmdl t y‖ ≤ C_Fprim * K'.indicator (fun _ : E => (1 : ℝ)) y := by
      refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      by_cases hyK' : y ∈ K'
      · rw [Set.indicator_of_mem hyK', mul_one, Real.norm_eq_abs]
        calc |Fmdl t y| ≤ C_Fmdl := hC_H y hyK'
          _ ≤ C_Fprim := le_max_left _ _
      · rw [hH_t_vanish y hy hyK']
        rw [Set.indicator_of_notMem hyK', mul_zero, norm_zero]
    have h_bound_int' : Integrable
        (fun y : E => C_Fprim * K'.indicator (fun _ : E => (1 : ℝ)) y)
        ((modelHaar (E := E)).restrict target) := by
      have h_ind_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
          ((modelHaar (E := E)).restrict target) := by
        have h_rest_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
            (modelHaar (E := E)) := by
          rw [integrable_indicator_iff hK'_meas]
          exact integrableOn_const (hs := ne_of_lt hK'_meas_lt_top)
        exact h_rest_int.restrict
      simpa [smul_eq_mul] using h_ind_int.const_mul C_Fprim
    -- Measurability of Fmdl t.
    have h_meas_Ht : AEStronglyMeasurable (Fmdl t) ((modelHaar (E := E)).restrict target) := by
      have h_symm_contOn_target : ContinuousOn symm target := h_symm_contOn
      have hf_cont : Continuous (f t) := by
        have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
          refine hf_cont_joint.comp ?_
          exact continuous_const.prodMk continuous_id
        exact this
      have h_f_cont : ContinuousOn (fun y : E => f t (symm y)) target :=
        hf_cont.continuousOn.comp h_symm_contOn_target (fun _ _ => Set.mem_univ _)
      have h_ρ_cont : ContinuousOn (fun y : E => ρα (symm y)) target :=
        hρα_cont.continuousOn.comp h_symm_contOn_target (fun _ _ => Set.mem_univ _)
      have h_d_cont : ContinuousOn
          (fun y : E => chartDensity (I := I) (g_fam t) α (symm y)) target :=
        h_density_contOn.comp h_symm_contOn_target h_symm_maps
      exact ((h_f_cont.mul h_ρ_cont).mul h_d_cont).aestronglyMeasurable htarget_meas
    exact h_bound_int'.mono' h_meas_Ht h_domHt
  have hH'_meas_at_t : AEStronglyMeasurable (Fprim t)
      ((modelHaar (E := E)).restrict target) := by
    -- Fprim t is continuous on K' (and 0 off K' target-ae).
    -- We represent Fprim t = K'.indicator (Fprim_main t ·) + 0 off-K' modulo null.
    -- We use the bound: Fprim t equals a function that is continuous on K' and 0 outside tsupport-pullback.
    -- Simpler: since Fprim t = if symm y ∈ base then _ else 0, and we work ae on target,
    -- provide a ae-strongly-measurable witness.
    -- Use the fact Fprim is ContinuousOn (I₁ ×ˢ K') at the slice t.
    have h_t_in_I₁ : t ∈ I₁ := ht_in_I₁
    -- Slice: `fun y => Fprim t y` on K'.
    have h_Ht'_cont_K' : ContinuousOn (fun y : E => Fprim t y) K' := by
      have := h_Fprim_continuousOn_Ω
      have : ContinuousOn (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') := this
      -- Slice by fixing p.1 := t.
      intro y hy
      have hp : (t, y) ∈ (I₁ ×ˢ K') := ⟨h_t_in_I₁, hy⟩
      -- ContinuousOn at (t, y) → ContinuousAt within K' at y via composition with constant map.
      have hat : ContinuousWithinAt (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') (t, y) :=
        this (t, y) hp
      have hincl_cont : Continuous (fun e : E => (t, e)) :=
        continuous_const.prodMk continuous_id
      have hincl_mapsTo : Set.MapsTo (fun e : E => (t, e)) K' (I₁ ×ˢ K') :=
        fun e he => ⟨h_t_in_I₁, he⟩
      exact hat.comp hincl_cont.continuousWithinAt hincl_mapsTo
    -- Off K' ∩ target, Fprim t vanishes. Fprim t is not necessarily continuous on all of target.
    -- But target = (K' ∩ target) ∪ (target \ K'), both measurable.
    -- Fprim t is strongly measurable on both: continuous on K' ∩ target ⊆ K', and 0 on target \ K'.
    -- Build via piecewise.
    -- Fprim t = K'.indicator (fun y => Fprim t y) modulo off-K' where Fprim t may be nonzero only if `symm y ∈ base` AND outside K', but ρα = 0 then, so Fprim t = 0.
    have h_Ht'_zero_off : ∀ y ∈ target, y ∉ K' → Fprim t y = 0 := by
      intro y hy hyK'
      have h_symm_y_not_K : symm y ∉ K := by
        intro h
        apply hyK'
        refine ⟨symm y, h, ?_⟩
        exact (extChartAt I α).right_inv hy
      have hρ_zero : ρα (symm y) = 0 := by
        by_contra h
        exact h_symm_y_not_K (subset_tsupport _
          (show symm y ∈ Function.support ρα from h))
      change (deriv (fun r : ℝ => f r (symm y)) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t (symm y) *
            f t (symm y)) * ρα (symm y) *
          chartDensity (I := I) (g_fam t) α (symm y) = 0
      rw [hρ_zero, mul_zero, zero_mul]
    -- Build `Fprim t` as `K'.indicator ∘ F + (target \ K').indicator ∘ 0`, using piecewise.
    -- Use `Indicator.aestronglyMeasurable` and continuity.
    have h_ind_Ht : Fprim t =ᵐ[(modelHaar (E := E)).restrict target]
        K'.indicator (fun y => Fprim t y) := by
      refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      by_cases hyK' : y ∈ K'
      · rw [Set.indicator_of_mem hyK']
      · rw [Set.indicator_of_notMem hyK']
        exact h_Ht'_zero_off y hy hyK'
    refine AEStronglyMeasurable.congr ?_ h_ind_Ht.symm
    -- K'.indicator of a function continuous on K'.
    have h_ind_meas : AEStronglyMeasurable
        (K'.indicator (fun y : E => Fprim t y))
        ((modelHaar (E := E)).restrict target) := by
      have h_restrict : AEStronglyMeasurable (fun y : E => Fprim t y)
          ((modelHaar (E := E)).restrict K') := by
        exact h_Ht'_cont_K'.aestronglyMeasurable hK'_meas
      have : AEStronglyMeasurable (K'.indicator (fun y : E => Fprim t y))
          (modelHaar (E := E)) := by
        refine (aestronglyMeasurable_indicator_iff hK'_meas).mpr ?_
        exact h_restrict
      exact this.restrict
    exact h_ind_meas
  -- Apply hasDerivAt_setIntegral_model.
  have h_s_mem : ball_s ∈ 𝓝 t := hballs_nhd
  have h_diff_ballsupersed : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ ball_s, HasDerivAt (fun r => Fmdl r y) (Fprim s y) s := by
    filter_upwards [hH'_deriv] with y hy
    intro s' _
    exact hy s' (Set.mem_univ _)
  have h_setInt := hasDerivAt_setIntegral_model (E := E) target htarget_meas
    (F := Fmdl) (F' := Fprim) (b := b) t (s := ball_s) h_s_mem hH_meas_at_t hH_int_at_t
    hH'_meas_at_t h_bound_prop hb_integrable h_diff_ballsupersed
  obtain ⟨_, h_inner⟩ := h_setInt
  -- Convert `∫ y in target, Fmdl t y ∂modelHaar` and `∫ y in target, Fprim t y ∂modelHaar`
  -- back to integrals against the withDensity chart-local measure.
  -- LHS: `fun s => ∫ y in target, Fmdl s y ∂modelHaar = fun s => ∫ x, f s x ∂(withDensity)`.
  have h_lhs_eq : ∀ s : ℝ,
      (∫ y in target, Fmdl s y ∂(modelHaar (E := E)))
        = ∫ x, f s x
            ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
                (fun y : M => ENNReal.ofReal (ρα y))) := by
    intro s
    -- chain: withDensity → ∫ scale • integrand → ∫ ρα · f s d(clm)
    -- then applying integral_chartLocalMeasure to get the target-side integral.
    have hρα_meas : AEMeasurable (fun y : M => ENNReal.ofReal (ρα y))
        (chartLocalMeasure (I := I) (g_fam s) α) :=
      (ENNReal.measurable_ofReal.comp hρα_cont.measurable).aemeasurable
    have hρα_lt_top : ∀ᵐ y ∂(chartLocalMeasure (I := I) (g_fam s) α),
        ENNReal.ofReal (ρα y) < ⊤ := Filter.Eventually.of_forall (fun _ => by simp)
    -- LHS unfold using withDensity.
    have h_withD :
        ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal (ρα y)))
          = ∫ x, (ENNReal.ofReal (ρα x)).toReal • f s x
              ∂(chartLocalMeasure (I := I) (g_fam s) α) :=
      integral_withDensity_eq_integral_toReal_smul₀
        (μ := chartLocalMeasure (I := I) (g_fam s) α)
        (f := fun y : M => ENNReal.ofReal (ρα y)) hρα_meas hρα_lt_top
        (g := f s)
    -- Convert smul to mul.
    have h_smul_eq : (fun x : M =>
        (ENNReal.ofReal (ρα x)).toReal • f s x) = fun x : M => f s x * ρα x := by
      funext x
      rw [ENNReal.toReal_ofReal (hρα_nonneg x), smul_eq_mul, mul_comm]
    -- Apply `integral_chartLocalMeasure` with h_fn := fun x => f s x * ρα x.
    have hfs_cont : Continuous (f s) := by
      have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
        refine hf_cont_joint.comp ?_
        exact continuous_const.prodMk continuous_id
      exact this
    have h_fρ_meas : Measurable (fun x : M => f s x * ρα x) :=
      (hfs_cont.mul hρα_cont).measurable
    have h_ICLM := integral_chartLocalMeasure (I := I) (M := M) (g_fam s) α
      (fun x => f s x * ρα x) h_fρ_meas
    -- Stitch together.
    rw [h_withD, h_smul_eq, h_ICLM]
    -- Rearrange integrand on RHS.
    have h_integrand_eq : (fun y : E =>
        chartDensity (I := I) (g_fam s) α (symm y) * (f s (symm y) * ρα (symm y)))
          = fun y : E => Fmdl s y := by
      funext y
      change chartDensity (I := I) (g_fam s) α ((extChartAt I α).symm y) *
            (f s ((extChartAt I α).symm y) * ρα ((extChartAt I α).symm y))
        = f s ((extChartAt I α).symm y) * ρα ((extChartAt I α).symm y) *
            chartDensity (I := I) (g_fam s) α ((extChartAt I α).symm y)
      ring
    rw [h_integrand_eq]
  -- RHS: `∫ y in target, Fprim t y ∂modelHaar = ∫ x, (∂_t f + 1/2 trace * f) * ρα ∂(clm g_fam t α)`.
  have h_rhs_eq :
      (∫ y in target, Fprim t y ∂(modelHaar (E := E)))
        = ∫ x, (deriv (fun s : ℝ => f s x) t
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
              ρα x
            ∂(chartLocalMeasure (I := I) (g_fam t) α) := by
    -- On target ae, Fprim t y = density * (...) * ρα(symm y).
    -- Use `integral_chartLocalMeasure` on g := fun x => (...) * ρα x.
    -- First: set g.
    set gFn : M → ℝ := fun x =>
      (deriv (fun s : ℝ => f s x) t +
        (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρα x
    have hg_cont : Continuous gFn := by
      refine Continuous.mul ?_ hρα_cont
      refine h_deriv_cont.add ?_
      refine Continuous.mul ?_ hft_cont
      exact (continuous_const.mul h_tr_cont)
    have hg_meas : Measurable gFn := hg_cont.measurable
    have h_ICLM := integral_chartLocalMeasure (I := I) (M := M) (g_fam t) α gFn hg_meas
    -- Right side: integral against modelHaar over target.
    rw [h_ICLM]
    -- Compare the two integrals via pointwise equality modulo zero-sets.
    refine MeasureTheory.setIntegral_congr_ae htarget_meas ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    -- Fprim t y equals the RHS integrand.
    change (deriv (fun r : ℝ => f r (symm y)) t +
            (1/2) * traceTimeDerivMetric (I := I) g_fam t (symm y) *
              f t (symm y)) * ρα (symm y) *
            chartDensity (I := I) (g_fam t) α (symm y)
      = chartDensity (I := I) (g_fam t) α ((extChartAt I α).symm y) *
          gFn ((extChartAt I α).symm y)
    change _ = chartDensity (I := I) (g_fam t) α (symm y) * gFn (symm y)
    change _ = chartDensity (I := I) (g_fam t) α (symm y) *
        ((deriv (fun r : ℝ => f r (symm y)) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t (symm y) *
            f t (symm y)) * ρα (symm y))
    ring
  -- Combine.
  rw [show (fun s : ℝ => ∫ x, f s x
        ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
            (fun y : M => ENNReal.ofReal (ρα y))))
      = fun s : ℝ => ∫ y in target, Fmdl s y ∂(modelHaar (E := E)) from ?_]
  · rw [h_rhs_eq.symm]
    exact h_inner
  · funext s
    exact (h_lhs_eq s).symm

end PerChartHasDerivAt

/-! ## The clean volume variation formula -/

section CleanTheorem

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

/-- **Clean volume variation formula.** The time derivative of
`t ↦ ∫ f t d(vol_t)` along a regular family `g_fam` of Riemannian metrics and a
regular integrand `f : ℝ → M → ℝ`, at a base time `t₀`, equals the integral of
`∂_t f + ½ tr_g(∂_t g) · f` against the Riemannian volume measure at `t₀`.

Hypotheses: compact σ-compact Hausdorff manifold `M`, a regularity
interface `MetricFamilyRegularAt g_fam t₀` for the metric family, and a
regularity interface `FunctionRegularAt f t₀` for the integrand. -/
theorem volume_variation_formula_clean
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M}
    {f : ℝ → M → ℝ} {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t₀
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t₀))
      t₀ := by
  -- Joint continuity of f.
  have hf_cont_joint : Continuous (fun p : ℝ × M => f p.1 p.2) := hf.continuous_joint
  -- Continuity of `f s` for every `s`.
  have hf_cont : ∀ᶠ s in 𝓝 t₀, Continuous (f s) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  -- Continuity of `f t₀`.
  have hft₀_cont : Continuous (f t₀) := by
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t₀, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  -- Continuity of `deriv (f · x) t₀` in `x`.
  have h_deriv_cont : Continuous (fun x : M => deriv (fun s : ℝ => f s x) t₀) := by
    have : Continuous ((fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)
        ∘ (fun x : M => (t₀, x))) :=
      hf.continuous_deriv_joint.comp (continuous_const.prodMk continuous_id)
    exact this
  -- Continuity of the RHS integrand.
  have hh_cont : Continuous (fun x : M =>
      deriv (fun s : ℝ => f s x) t₀ +
      (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x) := by
    refine Continuous.add h_deriv_cont ?_
    refine Continuous.mul ?_ hft₀_cont
    refine Continuous.mul continuous_const ?_
    exact traceTimeDerivMetric_continuous (I := I) (M := M) hg
  -- Apply the clean-of-chart-derivs helper, providing per-chart HasDerivAt.
  refine volume_variation_formula_clean_of_chart_derivs
    (I := I) (M := M) g_fam f t₀ hf_cont hh_cont ?_
  intro α hα
  exact per_chart_hasDerivAt (I := I) (M := M) hg hf α hα

end CleanTheorem

end CleanVolumeVariation

end Volume
end Analysis
end RicciFlower
