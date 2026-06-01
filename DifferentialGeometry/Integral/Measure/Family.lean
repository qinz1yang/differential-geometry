import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Integral.Measure.Glue
import DifferentialGeometry.Integral.Measure.Invariance
import DifferentialGeometry.Integral.Measure.Properties
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

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

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
    have hsum_eq :
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) • G' (σ k) k
          = ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k := by
      simp [smul_eq_mul]
    rw [← hsum_eq]
    exact hmul
  exact HasDerivAt.fun_sum hterm

/-- Key algebraic identity: the Leibniz-product derivative sum equals
`trace (adjugate A · B)`. Proof via the cofactor expansion of `adjugate A i j`
combined with swapping the order of the σ- and k-summations. -/
theorem perm_sum_eq_trace_adjugate_mul
    (A B : Matrix n n ℝ) :
    (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ k, (∏ i ∈ Finset.univ.erase k, A (σ i) i) * B (σ k) k)
      = trace (adjugate A * B) := by
  classical
  have hrhs :
      trace (adjugate A * B)
        = ∑ k, ∑ v, adjugate A k v * B v k := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diag]
  rw [hrhs]
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
  refine Finset.sum_congr rfl ?_
  intro k _
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
  refine Finset.sum_congr rfl ?_
  intro v _
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
  congr 1
  rw [adjugate_apply, Matrix.det_apply']
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Equiv.Perm n)))
    (p := fun τ => τ k = v)]
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
  symm
  refine Finset.sum_congr rfl ?_
  intro τ hτ
  rw [Finset.mem_filter] at hτ
  have hsplit_prod :
      (∏ i, (A.updateRow v (Pi.single k 1)) (τ i) i)
        = (A.updateRow v (Pi.single k 1)) (τ k) k *
            ∏ i ∈ Finset.univ.erase k,
              (A.updateRow v (Pi.single k 1)) (τ i) i :=
    (Finset.mul_prod_erase (Finset.univ : Finset n)
      (fun i => (A.updateRow v (Pi.single k 1)) (τ i) i)
      (Finset.mem_univ k)).symm
  rw [hsplit_prod]
  have h_topfactor :
      (A.updateRow v (Pi.single k 1)) (τ k) k = 1 := by
    rw [hτ.2, Matrix.updateRow_self]
    simp
  rw [h_topfactor, one_mul]
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
  have hadj := adjugate_eq_det_smul_inv (n := n) (A := G t) hunit
  have hrewrite : trace (adjugate (G t) * G') = (G t).det * trace ((G t)⁻¹ * G') := by
    rw [hadj]
    rw [Matrix.smul_mul]
    rw [Matrix.trace_smul]
    rfl
  rw [hrewrite] at h
  exact h

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
  have hsqrt_ne : Real.sqrt (G t).det ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hkey :
      (1 / (2 * Real.sqrt (G t).det)) * ((G t).det * trace ((G t)⁻¹ * G'))
        = (1 / 2) * trace ((G t)⁻¹ * G') * Real.sqrt (G t).det := by
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
  have hfun :
      (fun s => chartDensityFamily (I := I) g_fam x₀ x s)
        = (fun s => Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x s).det) := by
    funext s
    exact chartDensityFamily_eq_sqrt_det (I := I) g_fam x₀ x s
  rw [hfun]
  exact hderiv

end ChartDensityFamily

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
  set μ₀ : MeasureTheory.Measure E :=
    (modelHaar (E := E)).restrict (extChartAt I x₀).target with hμ₀
  set w : E → ℝ≥0∞ :=
    fun y => ENNReal.ofReal
      (chartDensity g x₀ ((extChartAt I x₀).symm y)) with hw
  set μ₁ : MeasureTheory.Measure E := μ₀.withDensity w with hμ₁
  have h_unfold :
      chartLocalMeasure (I := I) g x₀ =
        MeasureTheory.Measure.map (extChartAt I x₀).symm μ₁ := rfl
  rw [h_unfold]
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
  have h_restrict :
      ∫ y, (w y).toReal • h ((extChartAt I x₀).symm y) ∂μ₀
        = ∫ y in (extChartAt I x₀).target,
            (w y).toReal • h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E)) := by
    simp [hμ₀]
  rw [h_restrict]
  refine setIntegral_congr_fun htarget_meas (fun y hy => ?_)
  rw [hw_toReal y hy, smul_eq_mul]

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
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (α := E) (E := ℝ) (μ := (modelHaar (E := E)).restrict target)
    (F := F) (F' := F') (x₀ := t₀) (s := s) (bound := b)
    hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  refine ⟨this.1, ?_⟩
  have hfun : (fun t => ∫ y, F t y ∂((modelHaar (E := E)).restrict target))
      = fun t => ∫ y in target, F t y ∂(modelHaar (E := E)) := by
    funext t
    rfl
  have hfun' : (∫ y, F' t₀ y ∂((modelHaar (E := E)).restrict target))
      = ∫ y in target, F' t₀ y ∂(modelHaar (E := E)) := rfl
  rw [← hfun, ← hfun']
  exact this.2

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
  set n := Fin (Module.finrank ℝ E) with hn_def
  set J : Matrix n n ℝ := transitionMatrix (I := I) x₀ x₁ x with hJ_def
  have hentry : ∀ (t₀ : ℝ) (i j : n),
      chartGramMatrix (I := I) (g_fam t₀) x₁ x i j
        = ∑ k, ∑ l, J k i * J l j *
            chartGramMatrix (I := I) (g_fam t₀) x₀ x k l := by
    intro t₀ i j
    exact chartGramMatrix_pullback_eq_sum (I := I) (g_fam t₀) x₀ x₁ hx0 hx1 i j
  ext i j
  have hG0_entry : ∀ k l : n,
      HasDerivAt (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x k l)
        (deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x k l) t) t := by
    intro k l
    exact hasDerivAt_chartGramMatrix_entry (I := I) (M := M) hreg x₀ hx0 k l t
  have hsum_hasDeriv :
      HasDerivAt
        (fun s => ∑ k : n, ∑ l : n, J k i * J l j *
            chartGramMatrix (I := I) (g_fam s) x₀ x k l)
        (∑ k : n, ∑ l : n, J k i * J l j *
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x k l) t) t := by
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    refine HasDerivAt.fun_sum (fun l _ => ?_)
    have hcm := (hG0_entry k l).const_mul (J k i * J l j)
    exact hcm
  have hfun_eq :
      (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j)
        = (fun s => ∑ k : n, ∑ l : n, J k i * J l j *
            chartGramMatrix (I := I) (g_fam s) x₀ x k l) := by
    funext s
    exact hentry s i j
  have hderiv_eq :
      deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t
        = ∑ k : n, ∑ l : n, J k i * J l j *
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x k l) t := by
    rw [hfun_eq]
    exact hsum_hasDeriv.deriv
  change deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t
      = (Jᵀ *
          (Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) *
          J) i j
  rw [hderiv_eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
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
  ext i j
  have hx0' : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]
    exact hx0
  have hx1' : x ∈ (extChartAt I x₁).source := by
    rw [extChartAt_source]
    exact hx1
  have hmem : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source ∩
      (extChartAt I x₀).source := ⟨⟨hx0', hx1'⟩, hx0'⟩
  have hcomp : ∀ i : Fin (Module.finrank ℝ E),
      (tangentCoordChange I x₁ x₀ x) ((tangentCoordChange I x₀ x₁ x)
          ((chartModelBasis E) i))
        = (chartModelBasis E) i := by
    intro i
    have := tangentCoordChange_comp (I := I) (𝕜 := ℝ) (E := E) (H := H) (M := M)
        (w := x₀) (x := x₁) (y := x₀) (z := x)
        (v := (chartModelBasis E) i) hmem
    rw [this]
    have hself := tangentCoordChange_self (I := I) (x := x₀) (z := x)
      (v := (chartModelBasis E) i) hx0'
    exact hself
  change (transitionMatrix (I := I) x₀ x₁ x *
      transitionMatrix (I := I) x₁ x₀ x) i j = (1 : Matrix _ _ _) i j
  simp only [Matrix.mul_apply, transitionMatrix_apply, Matrix.one_apply]
  have hexp :
      (tangentCoordChange I x₀ x₁ x) ((chartModelBasis E) j)
        = ∑ k, (chartModelBasis E).repr
            ((tangentCoordChange I x₀ x₁ x) ((chartModelBasis E) j)) k
          • (chartModelBasis E) k :=
    chartModelBasis_repr_sum (tangentCoordChange I x₀ x₁ x) j
  have hlin :
      (tangentCoordChange I x₁ x₀ x)
          (∑ k, (chartModelBasis E).repr
              ((tangentCoordChange I x₀ x₁ x) ((chartModelBasis E) j)) k
            • (chartModelBasis E) k)
        = ∑ k, (chartModelBasis E).repr
              ((tangentCoordChange I x₀ x₁ x) ((chartModelBasis E) j)) k
            • (tangentCoordChange I x₁ x₀ x) ((chartModelBasis E) k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ContinuousLinearMap.map_smul]
  have heval : (tangentCoordChange I x₁ x₀ x) ((tangentCoordChange I x₀ x₁ x)
      ((chartModelBasis E) j))
      = (chartModelBasis E) j := hcomp j
  have heval' :
      ∑ k, (chartModelBasis E).repr
            ((tangentCoordChange I x₀ x₁ x) ((chartModelBasis E) j)) k
          • (tangentCoordChange I x₁ x₀ x) ((chartModelBasis E) k)
        = (chartModelBasis E) j := by
    rw [← hlin, ← hexp]; exact heval
  have happ := congrArg ((chartModelBasis E).repr · i) heval'
  simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    map_smul, Finsupp.smul_apply, smul_eq_mul] at happ
  have hrhs : ((chartModelBasis E).repr ((chartModelBasis E) j)) i
                = if i = j then (1 : ℝ) else 0 := by
    rw [(chartModelBasis E).repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  rw [← hrhs]
  rw [← happ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact mul_comm _ _

/-- The transition matrix (as an element of the matrix ring) has a two-sided
inverse, hence is a unit, and in particular has nonzero determinant. -/
lemma transitionMatrix_isUnit
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    IsUnit (transitionMatrix (I := I) x₀ x₁ x) := by
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
  have hG1_eq : G₁ = Jᵀ * G₀ * J :=
    chartGramMatrix_pullback_eq_mul (I := I) (g_fam t) x₀ x₁ hx0 hx1
  have hdG1_eq : dG₁ = Jᵀ * dG₀ * J :=
    deriv_chartGramMatrix_pullback (I := I) (M := M) hreg x₀ x₁ hx0 hx1
  have hJ_unit : IsUnit J :=
    transitionMatrix_isUnit (I := I) x₀ x₁ hx0 hx1
  have hG0_unit : IsUnit G₀ := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hpos : 0 < G₀.det := chartGramMatrix_det_pos (I := I) (g_fam t) x₀ hx0
    exact (ne_of_gt hpos).isUnit
  have hJT_unit : IsUnit Jᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hJ_unit
  have hJ_det : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).mp hJ_unit
  have hJT_det : IsUnit (Jᵀ).det := by
    rw [Matrix.det_transpose]; exact hJ_det
  have hinv : G₁⁻¹ = J⁻¹ * G₀⁻¹ * (Jᵀ)⁻¹ := by
    rw [hG1_eq]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
  have hJTinv : (Jᵀ)⁻¹ * Jᵀ = 1 := Matrix.nonsing_inv_mul _ hJT_det
  have hJinvJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ_det
  have hgoal :
      Matrix.trace (G₁⁻¹ * dG₁) = Matrix.trace (G₀⁻¹ * dG₀) := by
    rw [hinv, hdG1_eq]
    have hrw1 :
        (J⁻¹ * G₀⁻¹ * (Jᵀ)⁻¹) * (Jᵀ * dG₀ * J)
          = J⁻¹ * G₀⁻¹ * ((Jᵀ)⁻¹ * Jᵀ) * dG₀ * J := by
      simp only [Matrix.mul_assoc]
    rw [hrw1]
    rw [hJTinv]
    rw [Matrix.mul_one]
    rw [show J⁻¹ * G₀⁻¹ * dG₀ * J = (J⁻¹ * G₀⁻¹ * dG₀) * J from by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
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
    change x ∈ (chartAt H x).source
    exact mem_chart_source _ _
  rw [traceTimeDerivMetric_eq]
  exact trace_chartGramMatrix_inv_deriv_chart_independent
    (I := I) (M := M) hreg x α hxx hxα

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
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS
  set f : M → MeasureTheory.Measure M := fun α =>
      (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) with hf
  have hsplit : ((MeasureTheory.Measure.sum fun i : (S : Set M) => f i) +
      MeasureTheory.Measure.sum (fun i : ↥((S : Set M)ᶜ) => f i)) =
      MeasureTheory.Measure.sum f :=
    MeasureTheory.Measure.sum_add_sum_compl (S : Set M) f
  have hcompl : MeasureTheory.Measure.sum (fun i : ↥((S : Set M)ᶜ) => f i) = 0 := by
    have hzero : ∀ i : ↥((S : Set M)ᶜ), f i = 0 := by
      intro i
      have hi : (i : M) ∉ S := i.2
      exact chartAtlasPOU_withDensity_zero_of_notMem (I := I) (M := M) g hi
    ext t ht
    rw [MeasureTheory.Measure.sum_apply _ ht]
    simp [hzero]
  rw [← hsplit, hcompl, add_zero]
  exact MeasureTheory.Measure.sum_coe_finset S f

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
  have hVol_eq :=
    riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M) g
  haveI hFin :
      MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
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
  conv_lhs => rw [hVol_eq]
  exact integral_finset_sum_measure hsummand_int

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
  have hG : ∀ i j : n,
      HasDerivAt (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j)
        (deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t) t := by
    intro i j
    exact hasDerivAt_chartGramMatrix_entry (I := I) (M := M) hreg α hxα i j t
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
    change HasDerivAt (fun s => chartDensity (I := I) (g_fam s) α x) _ t
    exact this
  have htrace :
      Matrix.trace ((chartGramMatrixFamily (I := I) g_fam α x t)⁻¹ *
        (Matrix.of fun i j : n =>
          deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t))
        = traceTimeDerivMetric (I := I) g_fam t x := by
    change Matrix.trace ((chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
        (Matrix.of fun i j : n =>
          deriv (fun s => chartGramMatrix (I := I) (g_fam s) α x i j) t))
      = traceTimeDerivMetric (I := I) g_fam t x
    rw [traceTimeDerivMetric_eq_trace_chartGramMatrix
      (I := I) (M := M) hreg α hxα]
  have hdensity_val :
      chartDensity (I := I) (g_fam t) α x
        = Real.sqrt (chartGramMatrixFamily (I := I) g_fam α x t).det := by
    rfl
  have hdensity_deriv' :
      HasDerivAt
        (fun s : ℝ => chartDensity (I := I) (g_fam s) α x)
        ((1 / 2) * traceTimeDerivMetric (I := I) g_fam t x *
          chartDensity (I := I) (g_fam t) α x) t := by
    rw [hdensity_val]
    have := hdensity_deriv
    rw [htrace] at this
    exact this
  have hfρ : HasDerivAt (fun s : ℝ => f s x * ρ x)
      (deriv (fun s : ℝ => f s x) t * ρ x) t :=
    hf.mul_const (ρ x)
  have hprod := hfρ.mul hdensity_deriv'
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
  rw [riemannianMeasureFamily_def]
  rw [integral_riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M)
      (g_fam t) h hh_cont]
  refine Finset.sum_congr rfl (fun α _ => ?_)
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
  set h : M → ℝ :=
      fun x => deriv (fun s : ℝ => f s x) t +
        (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x with hh_def
  set Iα : M → ℝ := fun α =>
      ∫ x, h x * (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α) with hIα_def
  set Iglobal : ℝ :=
      ∫ x, h x
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) with hIglobal_def
  have hSum : ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Iα α = Iglobal := by
    exact chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
      (I := I) (M := M) g_fam t h hh_cont
  refine volume_variation_formula (I := I) (M := M)
    g_fam f t Iα Iglobal hf_cont ?_ hSum
  intro α hα
  exact hα_deriv_explicit α hα

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
  have h_det_ne_zero : ∀ p ∈ (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet
        : Set (ℝ × M)),
      (chartGramMatrix (I := I) (g_fam p.1) α p.2).det ≠ 0 := by
    intro p hp
    exact ne_of_gt (chartGramMatrix_det_pos (I := I) (g_fam p.1) α hp.2)
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
  set α : M := x₀
  have hα_base_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change x₀ ∈ (chartAt H x₀).source
    exact mem_chart_source _ _
  have h_joint : ContinuousOn
      (fun p : ℝ × M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          (Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    continuousOn_traceTimeDerivMetric_on_base (I := I) (M := M) hreg α
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
    have hincl_cont : Continuous (fun y : M => ((t, y) : ℝ × M)) :=
      continuous_const.prodMk continuous_id
    have hincl_mapsTo : Set.MapsTo (fun y : M => ((t, y) : ℝ × M))
        (trivializationAt E (TangentSpace I) α).baseSet
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
      fun y hy => ⟨Set.mem_univ _, hy⟩
    exact h_at.comp hincl_cont.continuousWithinAt hincl_mapsTo
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

section PerChartHasDerivAt

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

private lemma chartDensity_nonneg_of_base
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    0 ≤ chartDensity (I := I) g α x := by
  unfold chartDensity
  exact Real.sqrt_nonneg _

set_option maxHeartbeats 16000000 in
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
  set n := Fin (Module.finrank ℝ E) with hn_def
  set ρα : M → ℝ := fun x => (chartAtlasPOU I M) α x with hρα_def
  set μₐ : MeasureTheory.Measure M := chartLocalMeasure (I := I) (g_fam t) α with hμα_def
  set target : Set E := (extChartAt I α).target with htarget_def
  set symm : E → M := fun y => (extChartAt I α).symm y with hsymm_def
  have htarget_meas : MeasurableSet target :=
    measurableSet_extChartAt_target (I := I) α
  have hρα_cont : Continuous ρα := ((chartAtlasPOU I M) α).contMDiff.continuous
  have hρα_nonneg : ∀ x, 0 ≤ ρα x := fun x => (chartAtlasPOU I M).nonneg _ _
  have hρα_le_one : ∀ x, ρα x ≤ 1 := fun x => (chartAtlasPOU I M).le_one _ _
  have hρα_subord : tsupport ρα ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hρα_tsupport_compact : IsCompact (tsupport ρα) := isClosed_tsupport ρα |>.isCompact
  have hf_cont_joint : Continuous (fun p : ℝ × M => f p.1 p.2) := hf.continuous_joint
  have hft_cont : Continuous (f t) := by
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  have h_deriv_cont_joint_M : Continuous
      (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) :=
    hf.continuous_deriv_joint
  have h_deriv_cont : Continuous (fun x : M => deriv (fun s : ℝ => f s x) t) := by
    have : Continuous ((fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)
        ∘ (fun x : M => (t, x))) :=
      h_deriv_cont_joint_M.comp (continuous_const.prodMk continuous_id)
    exact this
  have h_tr_cont : Continuous (fun x : M => traceTimeDerivMetric (I := I) g_fam t x) :=
    traceTimeDerivMetric_continuous (I := I) (M := M) hreg
  have h_density_contOn : ContinuousOn
      (fun x : M => chartDensity (I := I) (g_fam t) α x)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartDensity_continuousOn (I := I) (g_fam t) α
  have h_symm_contOn : ContinuousOn symm target :=
    continuousOn_extChartAt_symm (I := I) α
  have h_symm_maps : ∀ y ∈ target, symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsrc : symm y ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsrc
    exact hsrc
  obtain ⟨Cf, hCf⟩ : ∃ C, ∀ x, ‖f t x‖ ≤ C := by
    have hIm := (isCompact_univ (X := M)).image hft_cont.norm
    obtain ⟨C, hC⟩ := hIm.bddAbove
    exact ⟨C, fun x => hC ⟨x, Set.mem_univ _, rfl⟩⟩
  set Fmdl : ℝ → E → ℝ := fun s y =>
    f s (symm y) * ρα (symm y) * chartDensity (I := I) (g_fam s) α (symm y)
  set Fprim : ℝ → E → ℝ := fun s y =>
    (deriv (fun r : ℝ => f r (symm y)) s +
      (1/2) * traceTimeDerivMetric (I := I) g_fam s (symm y) *
        f s (symm y)) * ρα (symm y) *
      chartDensity (I := I) (g_fam s) α (symm y)
  have hH'_deriv : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ (Set.univ : Set ℝ), HasDerivAt (fun r => Fmdl r y) (Fprim s y) s := by
    refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    intro s _
    have hsym_base : symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      h_symm_maps y hy
    have hslice : HasDerivAt (fun r : ℝ => f r (symm y))
        (deriv (fun r : ℝ => f r (symm y)) s) s :=
      hf.hasDerivAt_time (symm y) s
    have hpcd := per_chart_integrand_hasDerivAt
      (I := I) (M := M) (t := s) (hreg.at_any s) α (x := symm y) hsym_base f ρα hslice
    exact hpcd
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
  have hK'_meas_lt_top : (modelHaar (E := E)) K' < ⊤ :=
    hK'_compact.measure_lt_top
  have h_deriv_cont_joint : Continuous
      (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) :=
    hf.continuous_deriv_joint
  set I₁ : Set ℝ := Set.Icc (t - 1) (t + 1)
  have hI₁_compact : IsCompact I₁ := isCompact_Icc
  have ht_interior : t ∈ Set.Ioo (t - 1 : ℝ) (t + 1) := by
    refine ⟨?_, ?_⟩ <;> linarith
  have ht_in_I₁ : t ∈ I₁ := ⟨by linarith, by linarith⟩
  set ball_s : Set ℝ := Metric.ball t 1
  have hballs_nhd : ball_s ∈ 𝓝 t := Metric.ball_mem_nhds _ one_pos
  have hballs_sub_I₁ : ball_s ⊆ I₁ := by
    intro s hs
    have hs' : |s - t| < 1 := by simpa [Real.dist_eq, Real.norm_eq_abs] using hs
    refine ⟨?_, ?_⟩
    · have := (abs_lt.mp hs').1; linarith
    · have := (abs_lt.mp hs').2; linarith
  set Ω : Set (ℝ × E) := I₁ ×ˢ K'
  have hΩ_compact : IsCompact Ω := hI₁_compact.prod hK'_compact
  have hK'_sub_target : K' ⊆ target := by
    intro y hy
    obtain ⟨x, hxK, hx_eq⟩ := hy
    have hx_src : x ∈ (extChartAt I α).source := by
      have : x ∈ (chartAt H α).source := hρα_subord hxK
      rw [← extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    rw [← hx_eq]
    exact (extChartAt I α).map_source hx_src
  have h_Fprim_continuousOn_Ω :
      ContinuousOn (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') := by
    have h_symm_contOn_K' : ContinuousOn symm K' := h_symm_contOn.mono hK'_sub_target
    have h_symm_pair_contOn :
        ContinuousOn (fun p : ℝ × E => (p.1, symm p.2)) (I₁ ×ˢ K') := by
      refine ContinuousOn.prodMk continuousOn_fst ?_
      refine h_symm_contOn_K'.comp continuousOn_snd ?_
      intro p hp
      exact hp.2
    have hf_comp : ContinuousOn (fun p : ℝ × E => f p.1 (symm p.2)) (I₁ ×ˢ K') := by
      exact hf_cont_joint.continuousOn.comp h_symm_pair_contOn (fun _ _ => Set.mem_univ _)
    have hρα_comp : ContinuousOn (fun p : ℝ × E => ρα (symm p.2)) (I₁ ×ˢ K') := by
      have : ContinuousOn (fun y : E => ρα (symm y)) K' := by
        exact hρα_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      exact (this.comp continuousOn_snd (fun _ hp => hp.2))
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
    have h_deriv_comp : ContinuousOn
        (fun p : ℝ × E => deriv (fun r : ℝ => f r (symm p.2)) p.1) (I₁ ×ˢ K') := by
      exact h_deriv_cont_joint.continuousOn.comp h_symm_pair_contOn
        (fun _ _ => Set.mem_univ _)
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
  obtain ⟨CH, hCH⟩ : ∃ C, ∀ p ∈ (I₁ ×ˢ K'), |Fprim p.1 p.2| ≤ C := by
    classical
    by_cases hne' : (I₁ ×ˢ K' : Set (ℝ × E)).Nonempty
    · have hΩne : Ω.Nonempty := hne'
      have h_abs_cont : ContinuousOn (fun p : ℝ × E => |Fprim p.1 p.2|) Ω :=
        h_Fprim_continuousOn_Ω.abs
      have hbdd := hΩ_compact.bddAbove_image h_abs_cont
      obtain ⟨C, hC⟩ := hbdd
      refine ⟨C, fun p hp => ?_⟩
      exact hC ⟨p, hp, rfl⟩
    · refine ⟨0, fun p hp => ?_⟩
      exact (hne' ⟨p, hp⟩).elim
  set C₀ : ℝ := |CH|
  set b : E → ℝ := fun y => C₀ * (K'.indicator (fun _ : E => (1 : ℝ))) y with hb_def
  have hb_nonneg : ∀ y, 0 ≤ b y := by
    intro y
    have h_ind_nonneg : 0 ≤ K'.indicator (fun _ : E => (1 : ℝ)) y :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    exact mul_nonneg (abs_nonneg _) h_ind_nonneg
  have hb_integrable : Integrable b ((modelHaar (E := E)).restrict target) := by
    have h_ind_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
        ((modelHaar (E := E)).restrict target) := by
      have h_rest_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ))) (modelHaar (E := E)) := by
        rw [integrable_indicator_iff hK'_meas]
        exact integrableOn_const (hs := ne_of_lt hK'_meas_lt_top)
      exact h_rest_int.restrict
    have := h_ind_int.const_mul C₀
    simpa [b, smul_eq_mul] using this
  have h_bound_prop : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ ball_s, ‖Fprim s y‖ ≤ b y := by
    refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    intro s hs
    by_cases hyK' : y ∈ K'
    · have hp : (s, y) ∈ (I₁ ×ˢ K' : Set (ℝ × E)) := ⟨hballs_sub_I₁ hs, hyK'⟩
      have hbound := hCH (s, y) hp
      have hby : b y = C₀ := by
        simp [b, Set.indicator_of_mem hyK']
      rw [Real.norm_eq_abs, hby]
      have : |Fprim s y| ≤ CH := hbound
      refine this.trans ?_
      exact le_abs_self _
    · have h_symm_y_not_in : symm y ∉ K := by
        intro hsymInK
        exact hyK' ⟨symm y, hsymInK, by
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
  have hH_meas_at_t : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (Fmdl s) ((modelHaar (E := E)).restrict target) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
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
      exact (h_f_s_comp_contOn.mul h_ρα_comp_contOn).mul h_density_comp_contOn
    exact (h_H_s_contOn.aestronglyMeasurable htarget_meas)
  have hH_int_at_t : Integrable (Fmdl t) ((modelHaar (E := E)).restrict target) := by
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
    obtain ⟨C_Fmdl, hC_H⟩ : ∃ C, ∀ y ∈ K', |Fmdl t y| ≤ C := by
      by_cases hK'_ne : K'.Nonempty
      · have h_abs_cont : ContinuousOn (fun y : E => |Fmdl t y|) K' := h_Ht_cont_K'.abs
        obtain ⟨C, hC⟩ := hK'_compact.bddAbove_image h_abs_cont
        refine ⟨C, fun y hy => ?_⟩
        exact hC ⟨y, hy, rfl⟩
      · refine ⟨0, fun y hy => ?_⟩
        exact absurd ⟨y, hy⟩ hK'_ne
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
    set C_Fprim : ℝ := max C_Fmdl 0
    have hC_Fprim_nonneg : 0 ≤ C_Fprim := le_max_right _ _
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
    have h_t_in_I₁ : t ∈ I₁ := ht_in_I₁
    have h_Ht'_cont_K' : ContinuousOn (fun y : E => Fprim t y) K' := by
      have := h_Fprim_continuousOn_Ω
      have : ContinuousOn (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') := this
      intro y hy
      have hp : (t, y) ∈ (I₁ ×ˢ K') := ⟨h_t_in_I₁, hy⟩
      have hat : ContinuousWithinAt (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') (t, y) :=
        this (t, y) hp
      have hincl_cont : Continuous (fun e : E => (t, e)) :=
        continuous_const.prodMk continuous_id
      have hincl_mapsTo : Set.MapsTo (fun e : E => (t, e)) K' (I₁ ×ˢ K') :=
        fun e he => ⟨h_t_in_I₁, he⟩
      exact hat.comp hincl_cont.continuousWithinAt hincl_mapsTo
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
    have h_ind_Ht : Fprim t =ᵐ[(modelHaar (E := E)).restrict target]
        K'.indicator (fun y => Fprim t y) := by
      refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      by_cases hyK' : y ∈ K'
      · rw [Set.indicator_of_mem hyK']
      · rw [Set.indicator_of_notMem hyK']
        exact h_Ht'_zero_off y hy hyK'
    refine AEStronglyMeasurable.congr ?_ h_ind_Ht.symm
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
  have h_lhs_eq : ∀ s : ℝ,
      (∫ y in target, Fmdl s y ∂(modelHaar (E := E)))
        = ∫ x, f s x
            ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
                (fun y : M => ENNReal.ofReal (ρα y))) := by
    intro s
    have hρα_meas : AEMeasurable (fun y : M => ENNReal.ofReal (ρα y))
        (chartLocalMeasure (I := I) (g_fam s) α) :=
      (ENNReal.measurable_ofReal.comp hρα_cont.measurable).aemeasurable
    have hρα_lt_top : ∀ᵐ y ∂(chartLocalMeasure (I := I) (g_fam s) α),
        ENNReal.ofReal (ρα y) < ⊤ := Filter.Eventually.of_forall (fun _ => by simp)
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
    have h_smul_eq : (fun x : M =>
        (ENNReal.ofReal (ρα x)).toReal • f s x) = fun x : M => f s x * ρα x := by
      funext x
      rw [ENNReal.toReal_ofReal (hρα_nonneg x), smul_eq_mul, mul_comm]
    have hfs_cont : Continuous (f s) := by
      have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
        refine hf_cont_joint.comp ?_
        exact continuous_const.prodMk continuous_id
      exact this
    have h_fρ_meas : Measurable (fun x : M => f s x * ρα x) :=
      (hfs_cont.mul hρα_cont).measurable
    have h_ICLM := integral_chartLocalMeasure (I := I) (M := M) (g_fam s) α
      (fun x => f s x * ρα x) h_fρ_meas
    rw [h_withD, h_smul_eq, h_ICLM]
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
  have h_rhs_eq :
      (∫ y in target, Fprim t y ∂(modelHaar (E := E)))
        = ∫ x, (deriv (fun s : ℝ => f s x) t
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
              ρα x
            ∂(chartLocalMeasure (I := I) (g_fam t) α) := by
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
    rw [h_ICLM]
    refine MeasureTheory.setIntegral_congr_ae htarget_meas ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
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
  rw [show (fun s : ℝ => ∫ x, f s x
        ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
            (fun y : M => ENNReal.ofReal (ρα y))))
      = fun s : ℝ => ∫ y in target, Fmdl s y ∂(modelHaar (E := E)) from ?_]
  · rw [h_rhs_eq.symm]
    exact h_inner
  · funext s
    exact (h_lhs_eq s).symm

end PerChartHasDerivAt

section CleanTheorem

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

/-- **First variation of volume.** At a base time `t₀`, the map
`s ↦ ∫ x, f s x ∂(riemannianMeasureFamily g_fam s)` has derivative
`∫ x, (∂_t f + ½ · tr_g(∂_t g) · f) ∂(riemannianMeasureFamily g_fam t₀)`, where
`∂_t f := deriv (fun s => f s x) t₀` and `tr_g(∂_t g) := traceTimeDerivMetric g_fam t₀ x`
is the metric trace of the time-derivative of the metric; the conclusion is a
`HasDerivAt` statement.

Hypotheses: `M` is a compact, σ-compact, Hausdorff manifold; `g_fam` satisfies the
regularity interface `MetricFamilyRegularAt g_fam t₀` (pointwise-in-time
differentiability and joint `(t, x)`-continuity of the chart Gram-matrix entries and
their time-derivatives) and `f` satisfies `FunctionRegularAt f t₀` (pointwise-in-time
differentiability and joint `(t, x)`-continuity of `f` and its time-derivative). No
joint smoothness of `(t, x) ↦ g_t(x)` is assumed. -/
theorem first_variation_of_volume
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
  have hf_cont_joint : Continuous (fun p : ℝ × M => f p.1 p.2) := hf.continuous_joint
  have hf_cont : ∀ᶠ s in 𝓝 t₀, Continuous (f s) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  have hft₀_cont : Continuous (f t₀) := by
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t₀, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  have h_deriv_cont : Continuous (fun x : M => deriv (fun s : ℝ => f s x) t₀) := by
    have : Continuous ((fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)
        ∘ (fun x : M => (t₀, x))) :=
      hf.continuous_deriv_joint.comp (continuous_const.prodMk continuous_id)
    exact this
  have hh_cont : Continuous (fun x : M =>
      deriv (fun s : ℝ => f s x) t₀ +
      (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x) := by
    refine Continuous.add h_deriv_cont ?_
    refine Continuous.mul ?_ hft₀_cont
    refine Continuous.mul continuous_const ?_
    exact traceTimeDerivMetric_continuous (I := I) (M := M) hg
  refine volume_variation_formula_clean_of_chart_derivs
    (I := I) (M := M) g_fam f t₀ hf_cont hh_cont ?_
  intro α hα
  exact per_chart_hasDerivAt (I := I) (M := M) hg hf α hα

end CleanTheorem

end CleanVolumeVariation

end Measure
end Integral
end DifferentialGeometry
