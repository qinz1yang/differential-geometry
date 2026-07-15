import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Corollary *Norms of covariant derivatives of tensors, II* (`lbl370`, F4)

The book derives Corollary II from Lemma I (`lemma45_F3`) by applying Lemma I to
the pulled-back tensor `Φ*T` and converting the `Φ*h`-derivatives and the
`g`-norms into `h`-norms.  In the **same-domain formulation** the pullback metric
`Φ*h` is a fixed reference metric `gRef`, `∇_{Φ*h} = ∇_gRef`, the pulled-back
tensor `Φ*T` is just a tensor `T'` on the domain, and the target `h`-norm of `T`
equals the `gRef`-norm of `T'` (the pullback is an isometry `(N,h) → (M,Φ*h)`).
So pullback-naturality is automatic, and the only remaining content is:

* convert each `gRef`-tower norm measured in `g` to the `gRef`-norm, paying the
  factor `√(C^{q₂+k})` (`sqrt_normSq0S_le_of_metric_equiv`, `C = 1+ε`); and
* factor out the largest power `√(C^{q₂+r})` over `0 ≤ k ≤ r` (monotonicity).

`lemma45_cor_II_of_intrinsic` packages exactly this, taking the **intrinsic**
Lemma I (the `normSq0S`-form of `lemma45_F3`) as a hypothesis `hF3`.  The
remaining frontier is the lift of the component `lemma45_F3` to this intrinsic
`normSq0S` form (the `gRef`-orthonormal-frame `B5` bridge); once that is built,
`hF3` is discharged and Corollary II is fully proven.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- **Corollary II from the intrinsic Lemma I** (MSM135 `lbl370`, same-domain F4).
Let `g`, `gRef` be metrics with `C⁻¹ gRef ≤ g ≤ C gRef` (`C = 1+ε`, the
approximate-isometry equivalence), and `T` a `(0,q₂)` tensor field.  Given the
intrinsic Lemma I bound `hF3`
`|∇_g^r T|_g ≤ |∇_gRef^r T|_g + ε·Cc·Σ_{k<r}|∇_gRef^k T|_g`
(all norms in `g`; `∇_gRef = ∇_{Φ*h}`), then for `0 < r ≤ p`
`|∇_g^r T|_g ≤ √(C^{q₂+r})·(|∇_gRef^r T|_gRef + ε·Cc·Σ_{k<r}|∇_gRef^k T|_gRef)`.
The factor `√(C^{q₂+r}) = (1+ε)^{(r+q₂)/2}` is the book's. -/
theorem lemma45_cor_II_of_intrinsic
    (g gRef : SmoothRiemannianMetric I M) {q₂ : ℕ}
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) q₂)
    (p : ℕ) {x : M} {C : Real} (hC : 1 ≤ C)
    (hequiv : ∀ v : TangentSpace I x,
      C⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧ g.inner x v v ≤ C * gRef.inner x v v)
    (eps Cc : Real) (heps0 : 0 ≤ eps) (hCc0 : 0 ≤ Cc)
    (hF3 : ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (normSq0S (I := I) g x (q₂ + r) (iterCov (I := I) g q₂ T r x)) ≤
        Real.sqrt (normSq0S (I := I) g x (q₂ + r) (iterCov (I := I) gRef q₂ T r x)) +
        eps * Cc * ∑ k ∈ Finset.range r,
          Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x))) :
    ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (normSq0S (I := I) g x (q₂ + r) (iterCov (I := I) g q₂ T r x)) ≤
        Real.sqrt (C ^ (q₂ + r)) *
          (Real.sqrt (normSq0S (I := I) gRef x (q₂ + r) (iterCov (I := I) gRef q₂ T r x)) +
            eps * Cc * ∑ k ∈ Finset.range r,
              Real.sqrt (normSq0S (I := I) gRef x (q₂ + k)
                (iterCov (I := I) gRef q₂ T k x))) := by
  intro r hr0 hrp
  classical
  have hC0 : (0 : Real) ≤ C := le_trans zero_le_one hC
  -- the master factor `√(C^{q₂+r})` and its nonnegativity
  have hFr0 : (0 : Real) ≤ Real.sqrt (C ^ (q₂ + r)) := Real.sqrt_nonneg _
  -- per-order conversion `|·|_g ≤ √(C^{q₂+k})·|·|_gRef`, with the factor pushed up to `q₂+r`
  have hconv : ∀ k : ℕ, k ≤ r →
      Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) ≤
        Real.sqrt (C ^ (q₂ + r)) *
          Real.sqrt (normSq0S (I := I) gRef x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) := by
    intro k hk
    have hbase := sqrt_normSq0S_le_of_metric_equiv (I := I) gRef g x (q₂ + k) hC hequiv
      (iterCov (I := I) gRef q₂ T k x)
    -- `√(C^{q₂+k}) ≤ √(C^{q₂+r})` since `C ≥ 1` and `q₂+k ≤ q₂+r`
    have hpow : C ^ (q₂ + k) ≤ C ^ (q₂ + r) := pow_le_pow_right₀ hC (by omega)
    have hfac : Real.sqrt (C ^ (q₂ + k)) ≤ Real.sqrt (C ^ (q₂ + r)) := Real.sqrt_le_sqrt hpow
    have hgRefnn : (0 : Real) ≤
        Real.sqrt (normSq0S (I := I) gRef x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) :=
      Real.sqrt_nonneg _
    calc Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x))
        ≤ Real.sqrt (C ^ (q₂ + k)) *
            Real.sqrt (normSq0S (I := I) gRef x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) := hbase
      _ ≤ Real.sqrt (C ^ (q₂ + r)) *
            Real.sqrt (normSq0S (I := I) gRef x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) :=
          mul_le_mul_of_nonneg_right hfac hgRefnn
  -- leading term (k = r) and the sum block
  have hlead := hconv r le_rfl
  have hsum : (∑ k ∈ Finset.range r,
        Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x))) ≤
      Real.sqrt (C ^ (q₂ + r)) * ∑ k ∈ Finset.range r,
        Real.sqrt (normSq0S (I := I) gRef x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => hconv k (le_of_lt (Finset.mem_range.mp hk))
  -- assemble: the `g`-RHS of `hF3` is bounded by `√(C^{q₂+r})·(gRef-RHS)`
  have hsum0 : (0 : Real) ≤ eps * Cc := mul_nonneg heps0 hCc0
  have hrhs :
      Real.sqrt (normSq0S (I := I) g x (q₂ + r) (iterCov (I := I) gRef q₂ T r x)) +
        eps * Cc * ∑ k ∈ Finset.range r,
          Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) ≤
      Real.sqrt (C ^ (q₂ + r)) *
        (Real.sqrt (normSq0S (I := I) gRef x (q₂ + r) (iterCov (I := I) gRef q₂ T r x)) +
          eps * Cc * ∑ k ∈ Finset.range r,
            Real.sqrt (normSq0S (I := I) gRef x (q₂ + k)
              (iterCov (I := I) gRef q₂ T k x))) := by
    have hmulsum : eps * Cc * ∑ k ∈ Finset.range r,
          Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) ≤
        eps * Cc * (Real.sqrt (C ^ (q₂ + r)) * ∑ k ∈ Finset.range r,
          Real.sqrt (normSq0S (I := I) gRef x (q₂ + k) (iterCov (I := I) gRef q₂ T k x))) :=
      mul_le_mul_of_nonneg_left hsum hsum0
    rw [mul_add]
    nlinarith [hlead, hmulsum, hFr0, hsum0]
  exact le_trans (hF3 r hr0 hrp) hrhs

end HCGCompactness
end DifferentialGeometry
