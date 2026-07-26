import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.Lemma45F4
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ProductMFoldNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsometryComp
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# MSM135 Composition of approximate isometries, I/II — derivative (`C^p`) layer

The `C^p` part of `lbl371`/`lbl372`, same-domain.  `ApproxIsometryComp.lean` has the
`C⁰` part (`metricEquiv_trans`, the scalar fold `compEpsAccum`); here is the
covariant-derivative composition bound, built on the F4 endpoint
`lemma45_corII` (`Lemma45F4.lean`).

* **`comp_cov_le`** (F5, `lbl371` derivative side): for error tensors `δ₀ = g₁−g₀`,
  `δ₁ = g₂−g₁` on a common domain with `|∇_{g₀}^r δ₀|_{g₀} ≤ ε₀` and
  `|∇_{g₁}^k δ₁|_{g₁} ≤ ε₁`, the composed error `δ₀+δ₁ = g₂−g₀` obeys
  `|∇_{g₀}^r(δ₀+δ₁)|_{g₀} ≤ ε₀ + ε₁·C_p`.  Triangle (fiber Minkowski at a `g₀`-ON
  basis) + the `δ₁` term via `lemma45_corII (g₀, g₁, δ₁)` + `|∇_{g₁}^k δ₁|_{g₁} ≤ ε₁`.
* **`comp_cov_accum`** (F6, `lbl372`): the `n`-fold accumulation of the per-step
  `ε`'s via `compEpsAccum` (`ApproxIsometryComp.lean`).
-/

universe u

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

/-- **MSM135 `lbl371`, derivative (`C^p`) side** (same-domain, F5).  Let `g₀ ≈ g₁`
be an `(ε₀,p)`-approximate isometry, and `δ₀`, `δ₁` be `(0,2)` error tensors with
`|∇_{g₀}^r δ₀|_{g₀} ≤ ε₀` and `|∇_{g₁}^k δ₁|_{g₁} ≤ ε₁` up to order `p`.  Then the
composed error `δ₀ + δ₁` obeys `|∇_{g₀}^r(δ₀+δ₁)|_{g₀} ≤ ε₀ + ε₁·C_p` for
`0 < r ≤ p`, with `C_p` uniform over the domain.

Proof: fiber Minkowski at a `g₀`-orthonormal basis splits the composed tower into
the `δ₀` term (`≤ ε₀`) and the `δ₁` term, which `lemma45_corII` (the F4 endpoint,
applied with `gRef := g₁`, `T := δ₁`) bounds by
`√((1+ε₀)^{2+r})·(|∇_{g₁}^r δ₁|_{g₁} + ε₀·Cc·Σ|∇_{g₁}^k δ₁|_{g₁}) ≤ ε₁·C_p`. -/
theorem comp_cov_le
    {u : Set M} (hu : IsOpen u)
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (δ₀ δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ) (eps0 eps1 : Real)
    (heps0_0 : 0 ≤ eps0) (heps0_1 : eps0 ≤ 1) (heps1_0 : 0 ≤ eps1)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps0)⁻¹ * g₁.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ (1 + eps0) * g₁.inner x v v)
    (hgK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + j)
        (iterCov (I := I) g₁ 2 (Tensor0SBundle.metricTensorField (I := I) g₀) j x)) ≤ eps0)
    (hδ₀ : ∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r) (iterCov (I := I) g₀ 2 δ₀ r x)) ≤ eps0)
    (hδ₁ : ∀ x ∈ u, ∀ k, k ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k) (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1) :
    ∃ Cp : Real, 0 ≤ Cp ∧ ∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
        (iterCov (I := I) g₀ 2 (δ₀ + δ₁) r x)) ≤ eps0 + eps1 * Cp := by
  classical
  obtain ⟨Cc, hCc0, hcorII⟩ :=
    lemma45_corII (I := I) hu g₀ g₁ δ₁ p eps0 heps0_0 heps0_1 hequiv hgK
  have hCp0 : (0 : Real) ≤ Real.sqrt ((2 : Real) ^ (2 + p)) * (1 + Cc * (p : Real)) :=
    mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  refine ⟨Real.sqrt ((2 : Real) ^ (2 + p)) * (1 + Cc * (p : Real)), hCp0, fun x hx r hr0 hrp => ?_⟩
  -- a `g₀`-orthonormal basis at `x` for the fiber triangle inequality
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g₀ x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON
  -- split the composed tower and bound by the triangle
  have hsplit : iterCov (I := I) g₀ 2 (δ₀ + δ₁) r x =
      iterCov (I := I) g₀ 2 δ₀ r x + iterCov (I := I) g₀ 2 δ₁ r x := by
    rw [iterCov_add]
    rfl
  rw [hsplit]
  have htri := sqrt_normSq0S_add_le (I := I) g₀ (iterCov (I := I) g₀ 2 δ₀ r x)
    (iterCov (I := I) g₀ 2 δ₁ r x) basis hinv
  -- the `δ₀` term
  have ht0 := hδ₀ x hx r hr0 hrp
  -- the `δ₁` term, via `lemma45_corII`
  have ht1 := hcorII x hx r hr0 hrp
  -- bound the `lemma45_corII` right-hand side by `eps1·Cp`
  have hfac : Real.sqrt ((1 + eps0) ^ (2 + r)) ≤ Real.sqrt ((2 : Real) ^ (2 + p)) := by
    apply Real.sqrt_le_sqrt
    calc (1 + eps0) ^ (2 + r) ≤ (2 : Real) ^ (2 + r) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
      _ ≤ (2 : Real) ^ (2 + p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfac0 : (0 : Real) ≤ Real.sqrt ((1 + eps0) ^ (2 + r)) := Real.sqrt_nonneg _
  have hsq0 : (0 : Real) ≤ Real.sqrt ((2 : Real) ^ (2 + p)) := Real.sqrt_nonneg _
  -- leading `δ₁` norm ≤ eps1
  have hlead : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + r)
      (iterCov (I := I) g₁ 2 δ₁ r x)) ≤ eps1 := hδ₁ x hx r hrp
  -- the sum of lower `δ₁` norms ≤ r·eps1 ≤ p·eps1
  have hsum : (∑ k ∈ Finset.range r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
        (iterCov (I := I) g₁ 2 δ₁ k x))) ≤ (r : Real) * eps1 := by
    have hb : ∀ k ∈ Finset.range r,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
          (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1 :=
      fun k hk => hδ₁ x hx k (le_trans (le_of_lt (Finset.mem_range.mp hk)) hrp)
    have h1 := Finset.sum_le_card_nsmul (Finset.range r) _ eps1 hb
    rwa [Finset.card_range, nsmul_eq_mul] at h1
  -- the bracket `≤ eps1·(1 + Cc·p)`
  have hsum0 : (0 : Real) ≤ ∑ k ∈ Finset.range r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
        (iterCov (I := I) g₁ 2 δ₁ k x)) :=
    Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _
  have hrp' : (r : Real) ≤ (p : Real) := by exact_mod_cast hrp
  have hCcS0 : (0 : Real) ≤ Cc * ∑ k ∈ Finset.range r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
        (iterCov (I := I) g₁ 2 δ₁ k x)) := mul_nonneg hCc0 hsum0
  have hbracket :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + r)
        (iterCov (I := I) g₁ 2 δ₁ r x)) +
        eps0 * Cc * ∑ k ∈ Finset.range r,
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
            (iterCov (I := I) g₁ 2 δ₁ k x)) ≤
      eps1 * (1 + Cc * (p : Real)) := by
    nlinarith [hlead, mul_le_mul_of_nonneg_left hsum hCc0,
      mul_nonneg (sub_nonneg.mpr heps0_1) hCcS0,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrp' heps1_0) hCc0]
  -- assemble: `δ₁` term ≤ Cp·eps1, then add the `δ₀` term and the triangle
  have ht1' : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
      (iterCov (I := I) g₀ 2 δ₁ r x)) ≤
      Real.sqrt ((2 : Real) ^ (2 + p)) * (eps1 * (1 + Cc * (p : Real))) := by
    refine le_trans ht1 ?_
    refine le_trans (mul_le_mul_of_nonneg_left hbracket hfac0) ?_
    exact mul_le_mul_of_nonneg_right hfac (by positivity)
  refine le_trans htri ?_
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r) (iterCov (I := I) g₀ 2 δ₀ r x)) +
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r) (iterCov (I := I) g₀ 2 δ₁ r x))
      ≤ eps0 + Real.sqrt ((2 : Real) ^ (2 + p)) * (eps1 * (1 + Cc * (p : Real))) :=
        add_le_add ht0 ht1'
    _ = eps0 + eps1 * (Real.sqrt ((2 : Real) ^ (2 + p)) * (1 + Cc * (p : Real))) := by ring

/-- **MSM135 `lbl372`** (F6): the `n`-fold accumulation of the per-step composition
errors.  If composing into step `k` costs at most `C` times the new `εₖ`, the
composite error after `n` steps is `≤ C·Σ_{i≤n} εᵢ`.  Scalar fold `compEpsAccum`
(`ApproxIsometryComp.lean`) over the per-step `comp_cov_le` bound. -/
theorem comp_cov_accum {C : Real} {e δ : Nat → Real}
    (h0 : e 0 ≤ C * δ 0)
    (hstep : ∀ k : Nat, e (k + 1) ≤ e k + C * δ (k + 1)) (n : Nat) :
    e n ≤ C * Finset.sum (Finset.range (n + 1)) (fun i => δ i) :=
  compEpsAccum h0 hstep n

/-- **Uniform-constant variant of `comp_cov_le` (F5, the D1b-facing form).**  The composed
constant `Cp` depends only on the order `p` (through the dimension-level `lemma45_corII_unif`
constant), NOT on the metrics, fields, or set — the quantifier order the lbl406 recursion
needs (STEPD_PLAN codas 37–38).  Proof: take `Cc` from `lemma45_corII_unif`, witness
`Cp := √(2^{2+p})·(1 + Cc·p)`, then replay the `comp_cov_le` body with the specialized
Corollary II. -/
theorem comp_cov_le_unif (p : ℕ) :
    ∃ Cp : Real, 0 ≤ Cp ∧
      ∀ {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
        [T2Space M'] [IsManifold I ∞ M'] [SigmaCompactSpace M']
        [IsManifold I 1 M'] [IsManifold I 2 M']
        [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
        {u : Set M'} (_ : IsOpen u)
        (g₀ g₁ : SmoothRiemannianMetric I M')
        (δ₀ δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2)
        (eps0 eps1 : Real), 0 ≤ eps0 → eps0 ≤ 1 → 0 ≤ eps1 →
        (∀ x ∈ u, ∀ v : TangentSpace I x,
          (1 + eps0)⁻¹ * g₁.inner x v v ≤ g₀.inner x v v ∧
            g₀.inner x v v ≤ (1 + eps0) * g₁.inner x v v) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + j)
            (iterCov (I := I) g₁ 2
              (Tensor0SBundle.metricTensorField (I := I) g₀) j x)) ≤ eps0) →
        (∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 δ₀ r x)) ≤ eps0) →
        (∀ x ∈ u, ∀ k, k ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
            (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1) →
        ∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 (δ₀ + δ₁) r x)) ≤ eps0 + eps1 * Cp := by
  classical
  obtain ⟨Cc, hCc0, hcorII⟩ := lemma45_corII_unif (E := E) (H := H) (I := I) 2 p
  have hCp0 : (0 : Real) ≤ Real.sqrt ((2 : Real) ^ (2 + p)) * (1 + Cc * (p : Real)) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (by nlinarith [mul_nonneg hCc0 (Nat.cast_nonneg (α := ℝ) p)])
  refine ⟨Real.sqrt ((2 : Real) ^ (2 + p)) * (1 + Cc * (p : Real)), hCp0, ?_⟩
  intro M' _ _ _ _ _ _ _ _ u hu g₀ g₁ δ₀ δ₁ eps0 eps1 heps0_0 heps0_1 heps1_0
    hequiv hgK hδ₀ hδ₁ x hx r hr0 hrp
  have hcorII' := hcorII hu g₀ g₁ δ₁ eps0 heps0_0 heps0_1 hequiv hgK
  -- a `g₀`-orthonormal basis at `x` for the fiber triangle inequality
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g₀ x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON
  -- split the composed tower and bound by the triangle
  have hsplit : iterCov (I := I) g₀ 2 (δ₀ + δ₁) r x =
      iterCov (I := I) g₀ 2 δ₀ r x + iterCov (I := I) g₀ 2 δ₁ r x := by
    rw [iterCov_add]
    rfl
  rw [hsplit]
  have htri := sqrt_normSq0S_add_le (I := I) g₀ (iterCov (I := I) g₀ 2 δ₀ r x)
    (iterCov (I := I) g₀ 2 δ₁ r x) basis hinv
  -- the `δ₀` term
  have ht0 := hδ₀ x hx r hr0 hrp
  -- the `δ₁` term, via `lemma45_corII`
  have ht1 := hcorII' x hx r hr0 hrp
  -- bound the `lemma45_corII` right-hand side by `eps1·Cp`
  have hfac : Real.sqrt ((1 + eps0) ^ (2 + r)) ≤ Real.sqrt ((2 : Real) ^ (2 + p)) := by
    apply Real.sqrt_le_sqrt
    calc (1 + eps0) ^ (2 + r) ≤ (2 : Real) ^ (2 + r) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
      _ ≤ (2 : Real) ^ (2 + p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfac0 : (0 : Real) ≤ Real.sqrt ((1 + eps0) ^ (2 + r)) := Real.sqrt_nonneg _
  have hsq0 : (0 : Real) ≤ Real.sqrt ((2 : Real) ^ (2 + p)) := Real.sqrt_nonneg _
  -- leading `δ₁` norm ≤ eps1
  have hlead : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + r)
      (iterCov (I := I) g₁ 2 δ₁ r x)) ≤ eps1 := hδ₁ x hx r hrp
  -- the sum of lower `δ₁` norms ≤ r·eps1 ≤ p·eps1
  have hsum : (∑ k ∈ Finset.range r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
        (iterCov (I := I) g₁ 2 δ₁ k x))) ≤ (r : Real) * eps1 := by
    have hb : ∀ k ∈ Finset.range r,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
          (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1 :=
      fun k hk => hδ₁ x hx k (le_trans (le_of_lt (Finset.mem_range.mp hk)) hrp)
    have h1 := Finset.sum_le_card_nsmul (Finset.range r) _ eps1 hb
    rwa [Finset.card_range, nsmul_eq_mul] at h1
  -- the bracket `≤ eps1·(1 + Cc·p)`
  have hsum0 : (0 : Real) ≤ ∑ k ∈ Finset.range r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
        (iterCov (I := I) g₁ 2 δ₁ k x)) :=
    Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _
  have hrp' : (r : Real) ≤ (p : Real) := by exact_mod_cast hrp
  have hCcS0 : (0 : Real) ≤ Cc * ∑ k ∈ Finset.range r,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
        (iterCov (I := I) g₁ 2 δ₁ k x)) := mul_nonneg hCc0 hsum0
  have hbracket :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + r)
        (iterCov (I := I) g₁ 2 δ₁ r x)) +
        eps0 * Cc * ∑ k ∈ Finset.range r,
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
            (iterCov (I := I) g₁ 2 δ₁ k x)) ≤
      eps1 * (1 + Cc * (p : Real)) := by
    nlinarith [hlead, mul_le_mul_of_nonneg_left hsum hCc0,
      mul_nonneg (sub_nonneg.mpr heps0_1) hCcS0,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrp' heps1_0) hCc0]
  -- assemble: `δ₁` term ≤ Cp·eps1, then add the `δ₀` term and the triangle
  have ht1' : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
      (iterCov (I := I) g₀ 2 δ₁ r x)) ≤
      Real.sqrt ((2 : Real) ^ (2 + p)) * (eps1 * (1 + Cc * (p : Real))) := by
    refine le_trans ht1 ?_
    refine le_trans (mul_le_mul_of_nonneg_left hbracket hfac0) ?_
    exact mul_le_mul_of_nonneg_right hfac (by positivity)
  refine le_trans htri ?_
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r) (iterCov (I := I) g₀ 2 δ₀ r x)) +
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r) (iterCov (I := I) g₀ 2 δ₁ r x))
      ≤ eps0 + Real.sqrt ((2 : Real) ^ (2 + p)) * (eps1 * (1 + Cc * (p : Real))) :=
        add_le_add ht0 ht1'
    _ = eps0 + eps1 * (Real.sqrt ((2 : Real) ^ (2 + p)) * (1 + Cc * (p : Real))) := by ring

end HCGCompactness
end DifferentialGeometry
