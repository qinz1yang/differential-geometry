Below is a Codex-ready formalization plan. The key is to **not formalize the printed proof directly**. The printed proof uses hidden phrases like “a sum of terms” and “putting it all together”; those need to become separate lemmas with explicit constants. The uploaded source proves Lemma 4.5 from the approximate-isometry definition, norm comparison Corollary 4.3, the connection-difference estimate, and an induction on derivative order. 

---

# Codex plan: formalizing Lemma 4.5

## Target theorem

Formalize a version of:

[
|\nabla_g^r T|*g
\le
|\nabla_H^r T|*g
+
\varepsilon C*{p,q_1,q_2}
\sum*{k=0}^{r-1}|\nabla_H^k T|_g,
]

where

[
H := \Phi^*h.
]

In Lean, do **not** start with the full mixed ((q_1,q_2))-tensor theorem. Start with the covariant-tensor case:

[
(q_1,q_2)=(0,s).
]

Then later generalize to mixed tensors after the slot-action API exists.

---

# Phase 0: Repository inspection and setup

Give Codex this first instruction:

```text
Inspect the repository and identify the existing definitions for:
1. Riemannian metric
2. Levi-Civita connection / covariant derivative
3. iterated covariant derivatives
4. tensor fields, especially covariant tensors `(0,s)`
5. tensor norms
6. pullback metrics
7. approximate isometry, if already present

Do not create new geometry infrastructure if an equivalent one already exists.
Produce a short map of existing names before editing.
Run `lake build` before and after every meaningful change.
```

Expected output from Codex should be a name map like:

```lean
-- placeholder examples only
Metric
CovDeriv
iterCovDeriv
TensorField
tensorNorm
pullbackMetric
```

If Codex cannot find these names, have it use shell search:

```bash
grep -R "covariant" -n .
grep -R "nabla" -n .
grep -R "Tensor" -n .
grep -R "Levi" -n .
grep -R "Metric" -n .
grep -R "norm" -n .
```

Do **not** let Codex begin proving Lemma 4.5 before this map exists.

---

# Phase 1: Create a constants-only file

Create a file, for example:

```text
DifferentialGeometry/Compactness/Lemma45Constants.lean
```

This file should import only algebra/order/sum facts, not geometry.

Use `ℝ`, not `ℝ≥0`, unless the project already strongly prefers `ℝ≥0`. Norms are usually `ℝ`, and using `ℝ≥0` causes coercion overhead.

Define the one-step constants:

```lean
noncomputable def oneStepConst (B : ℕ → ℝ) (k m : ℕ) : ℝ :=
  (m : ℝ) *
    ∑ a in Finset.range (k + 1),
      (Nat.choose k a : ℝ) * B a
```

Here:

* `B a` controls (|\nabla_H^a A|_g),
* `m` is the tensor rank, initially `m = s` for ((0,s))-tensors,
* `A := ∇ᵍ - ∇ᴴ`.

Then define the main recursive constant:

```lean
noncomputable def lemma45Const (B : ℕ → ℝ) : ℕ → ℕ → ℝ
| 0,     m => 1
| p + 1, m =>
    lemma45Const B p m
    + 1
    + oneStepConst B p m
    + lemma45Const B p (m + 1) *
        (1 + ∑ k in Finset.range p, oneStepConst B k m)
```

The extra `+ 1` is deliberate. It makes positivity and monotonicity easier.

---

## Constants lemmas

Ask Codex to prove:

```lean
lemma oneStepConst_nonneg
  (hB : ∀ i, 0 ≤ B i) :
  0 ≤ oneStepConst B k m := by
  ...
```

```lean
lemma lemma45Const_pos
  (hB : ∀ i, 0 ≤ B i) :
  0 < lemma45Const B p m := by
  ...
```

```lean
lemma lemma45Const_nonneg
  (hB : ∀ i, 0 ≤ B i) :
  0 ≤ lemma45Const B p m := by
  exact le_of_lt (lemma45Const_pos hB)
```

```lean
lemma lemma45Const_le_succ
  (hB : ∀ i, 0 ≤ B i) :
  lemma45Const B p m ≤ lemma45Const B (p + 1) m := by
  ...
```

The last lemma replaces the paper’s informal sentence:

> “Certainly we may choose (C_{\rho+1,q_1,q_2}) to be greater than (C_{\rho,q_1,q_2}).”

In Lean, constants must be explicitly monotone by construction.

---

# Phase 2: Prove finite-sum algebra lemmas

Create:

```text
DifferentialGeometry/Compactness/SumLemmas.lean
```

These lemmas should be geometry-free.

## Lemma 2.1: partial range sum bounded by larger range sum

For nonnegative `N`:

```lean
lemma sum_range_le_sum_range
  (hN : ∀ i, 0 ≤ N i)
  (hkp : k ≤ p) :
  (∑ i in Finset.range (k + 1), N i)
    ≤
  (∑ i in Finset.range (p + 1), N i) := by
  ...
```

Use this constantly. It turns

[
\sum_{i=0}^{k}N_i
]

into

[
\sum_{i=0}^{p}N_i.
]

---

## Lemma 2.2: shifted derivative sum is bounded by full derivative sum

```lean
lemma sum_shift_le_full
  (hN : ∀ i, 0 ≤ N i) :
  (∑ k in Finset.range p, N (k + 1))
    ≤
  (∑ i in Finset.range (p + 1), N i) := by
  ...
```

Mathematically:

[
\sum_{k=0}^{p-1}N_{k+1}
=======================

N_1+\cdots+N_p
\le
N_0+\cdots+N_p.
]

This avoids a bad extra factor of `p`.

---

## Lemma 2.3: one-step partial estimate upgraded to full estimate

This can be an algebra lemma, not a geometry lemma.

```lean
lemma oneStep_partial_to_full
  (hε : 0 ≤ ε)
  (hE : 0 ≤ E)
  (hN : ∀ i, 0 ≤ N i)
  (hkp : k ≤ p)
  (h :
    G ≤ N (k + 1)
      + ε * E * ∑ i in Finset.range (k + 1), N i) :
    G ≤ N (k + 1)
      + ε * E * ∑ i in Finset.range (p + 1), N i := by
  ...
```

This is useful because the geometric one-step lemma naturally produces a partial sum, but the induction wants the full sum.

---

## Lemma 2.4: induction-step algebra

This is the most useful pure lemma.

Let:

[
S_p := \sum_{i=0}^p N_i.
]

Assume:

[
A \le G_p + \varepsilon C\sum_{k=0}^{p-1}G_k,
]

[
G_p \le N_{p+1}+\varepsilon E_pS_p,
]

and for (k<p),

[
G_k \le N_{k+1}+\varepsilon E_kS_p.
]

Then prove:

[
A
\le
N_{p+1}
+
\varepsilon
\left[
E_p+C\left(1+\sum_{k=0}^{p-1}E_k\right)
\right]S_p.
]

Lean shape:

```lean
lemma main_step_algebra
  (hε0 : 0 ≤ ε)
  (hε1 : ε ≤ 1)
  (hC : 0 ≤ C)
  (hE : ∀ k, 0 ≤ E k)
  (hN : ∀ i, 0 ≤ N i)
  (hA :
    A ≤ G p + ε * C * ∑ k in Finset.range p, G k)
  (hGp :
    G p ≤ N (p + 1)
      + ε * E p * ∑ i in Finset.range (p + 1), N i)
  (hGk :
    ∀ k ∈ Finset.range p,
      G k ≤ N (k + 1)
        + ε * E k * ∑ i in Finset.range (p + 1), N i) :
  A ≤
    N (p + 1)
      + ε * (E p + C * (1 + ∑ k in Finset.range p, E k))
        * ∑ i in Finset.range (p + 1), N i := by
  ...
```

This lemma should be proven before any geometry. Once this is available, the main induction becomes manageable.

---

# Phase 3: Abstract connection-difference hypothesis

Before formalizing approximate isometries, prove Lemma 4.5 under an abstract hypothesis.

Introduce:

[
A := \nabla^g-\nabla^H.
]

Assume constants `B : ℕ → ℝ` satisfying:

```lean
hA_bound :
  ∀ k < p,
    norm_g (iterNabla H k A x) ≤ ε * B k
```

or, if the project uses bundled tensor fields:

```lean
hA_bound :
  ∀ k < p,
    ‖∇[H]^k A‖_g x ≤ ε * B k
```

Do **not** expand `A` as Christoffel symbols inside Lemma 4.5.

The actual approximate-isometry theorem later proves this hypothesis from the approximate-isometry assumptions.

---

# Phase 4: Formalize the slot-action identity for covariant tensors

Start only with ((0,s))-tensors.

For a covariant tensor (T) of rank `s`, the connection difference acts by one term per slot:

[
\nabla_g T
==========

\nabla_H T
+
A\diamond T.
]

For covariant tensors, in coordinates this has the schematic form:

[
(\nabla_g T)_{i j_1\ldots j_s}
==============================

## (\nabla_H T)_{i j_1\ldots j_s}

\sum_{\alpha=1}^{s}
A^m_{i j_\alpha}
T_{j_1\ldots m\ldots j_s}.
]

The sign is irrelevant for the norm estimate.

Codex task:

```text
Prove the first-order connection comparison identity for `(0,s)`-tensors.
Do not attempt mixed tensors yet.
The output should be a lemma whose corollary is the norm bound:
‖∇ᵍ T‖_g ≤ ‖∇ᴴ T‖_g + s * ‖A‖_g * ‖T‖_g.
```

Lean shape:

```lean
lemma nablaG_eq_nablaH_add_connDiff_action_covariant
  :
  nabla g T = nabla H T + connDiffAction A T := by
  ...
```

Then:

```lean
lemma norm_connDiffAction_covariant_le
  :
  ‖connDiffAction A T‖_g
    ≤ (s : ℝ) * ‖A‖_g * ‖T‖_g := by
  ...
```

Then:

```lean
lemma norm_nablaG_le_nablaH_covariant
  :
  ‖nabla g T‖_g
    ≤ ‖nabla H T‖_g
      + (s : ℝ) * ‖A‖_g * ‖T‖_g := by
  ...
```

This proves the (r=1) case abstractly.

---

# Phase 5: Leibniz estimate for iterated (H)-derivatives

Prove the formal replacement for the hidden phrase “a sum of terms.”

The desired estimate is:

[
|\nabla_H^k(A\diamond T)|*g
\le
s
\sum*{a=0}^k
\binom{k}{a}
|\nabla_H^a A|_g
|\nabla_H^{k-a}T|_g.
]

Codex task:

```text
Prove a Leibniz-type norm estimate for iterated `H`-covariant derivatives of the slot action `A ⋄ T`.
It is acceptable to prove a coarse version with a finite constant, but the preferred version uses binomial coefficients.
```

Lean shape:

```lean
lemma iterNabla_connDiffAction_covariant_le
  :
  ‖iterNabla H k (connDiffAction A T)‖_g
    ≤ (s : ℝ) *
      ∑ a in Finset.range (k + 1),
        (Nat.choose k a : ℝ)
          * ‖iterNabla H a A‖_g
          * ‖iterNabla H (k - a) T‖_g := by
  ...
```

If subtraction `k - a` becomes painful, use indices over pairs:

```lean
∑ ab in Finset.antidiagonal k,
  ...
```

That may be more formalization-friendly:

```lean
∑ ab in Nat.antidiagonal k,
  (Nat.choose k ab.1 : ℝ)
    * ‖iterNabla H ab.1 A‖_g
    * ‖iterNabla H ab.2 T‖_g
```

Then `ab.1 + ab.2 = k` is available from membership in the antidiagonal.

---

# Phase 6: Prove the one-step estimate

This is the key bridge lemma.

Let

[
N_i(T):=|\nabla_H^iT|_g.
]

Assume

[
|\nabla_H^aA|_g\le \varepsilon B_a
]

for all (a\le k).

Then prove:

[
|\nabla_H^k\nabla_gT|*g
\le
|\nabla_H^{k+1}T|*g
+
\varepsilon E*{k,s}
\sum*{i=0}^{k}|\nabla_H^iT|_g,
]

where

[
E_{k,s}:=\mathrm{oneStepConst}(B,k,s).
]

Lean shape:

```lean
lemma iterNablaH_nablaG_bound_covariant
  (hε0 : 0 ≤ ε)
  (hB_nonneg : ∀ i, 0 ≤ B i)
  (hA :
    ∀ a ≤ k,
      ‖iterNabla H a A‖_g ≤ ε * B a) :
  ‖iterNabla H k (nabla g T)‖_g
    ≤ ‖iterNabla H (k + 1) T‖_g
      + ε * oneStepConst B k s *
          ∑ i in Finset.range (k + 1),
            ‖iterNabla H i T‖_g := by
  ...
```

Proof structure:

1. Rewrite:

   [
   \nabla_gT=\nabla_HT+A\diamond T.
   ]

2. Apply (\nabla_H^k):

   [
   \nabla_H^k\nabla_gT
   ===================

   \nabla_H^{k+1}T+\nabla_H^k(A\diamond T).
   ]

3. Use triangle inequality:

   [
   \le
   |\nabla_H^{k+1}T|
   +
   |\nabla_H^k(A\diamond T)|.
   ]

4. Apply the Leibniz estimate.

5. Use `hA`.

6. Bound each (|\nabla_H^{k-a}T|) by the full partial sum:

   [
   |\nabla_H^{k-a}T|
   \le
   \sum_{i=0}^{k}|\nabla_H^iT|.
   ]

7. Pull out the common sum.

This is where `oneStepConst` appears.

---

# Phase 7: Prove the abstract Lemma 4.5 for covariant tensors

Create:

```text
DifferentialGeometry/Compactness/Lemma45CovariantAbstract.lean
```

The theorem should be abstract in `B`.

```lean
theorem lemma45_covariant_abstract
  (hε0 : 0 ≤ ε)
  (hε1 : ε < 1)
  (hB_nonneg : ∀ i, 0 ≤ B i)
  (hA :
    ∀ k < p,
      ‖iterNabla H k A‖_g ≤ ε * B k)
  (hr0 : 0 < r)
  (hrp : r ≤ p) :
  ‖iterNabla g r T‖_g
    ≤ ‖iterNabla H r T‖_g
      + ε * lemma45Const B p s *
          ∑ i in Finset.range r,
            ‖iterNabla H i T‖_g := by
  ...
```

## Main proof structure

Use induction on `p`.

### Base case: `p = 0`

No `r` satisfies:

```lean
0 < r ∧ r ≤ 0
```

So solve by contradiction:

```lean
omega
```

or:

```lean
exact (Nat.not_lt_zero r (lt_of_lt_of_le hr0 hrp)).elim
```

---

### Inductive step: `p → p + 1`

You need to prove the result for all `r ≤ p+1`.

Split cases:

```lean
by_cases hrp' : r ≤ p
```

#### Case 1: `r ≤ p`

Use the induction hypothesis:

```lean
have hIH := ih r hr0 hrp'
```

Then enlarge the constant using:

```lean
lemma45Const_le_succ
```

You need a small helper:

```lean
lemma mul_sum_const_mono
  (hε : 0 ≤ ε)
  (hC : C ≤ C')
  (hS : 0 ≤ S) :
  ε * C * S ≤ ε * C' * S := by
  nlinarith
```

Then finish by transitivity.

---

#### Case 2: `¬ r ≤ p`

Since `r ≤ p+1`, get:

```lean
have hr_eq : r = p + 1 := by omega
```

Rewrite using `hr_eq`.

Let:

```lean
S := ∇ᵍ T
```

Then:

[
\nabla_g^{p+1}T = \nabla_g^p(\nabla_gT).
]

The tensor `S` has rank `s+1`.

Apply the induction hypothesis to `S` with rank `s+1`:

[
|\nabla_g^pS|*g
\le
|\nabla_H^pS|*g
+
\varepsilon C*{p,s+1}
\sum*{k=0}^{p-1}|\nabla_H^kS|_g.
]

This produces:

```lean
‖iterNabla g (p + 1) T‖_g
  ≤ ‖iterNabla H p (nabla g T)‖_g
    + ε * lemma45Const B p (s + 1) *
        ∑ k in Finset.range p,
          ‖iterNabla H k (nabla g T)‖_g
```

Then define:

```lean
N i := ‖iterNabla H i T‖_g
G k := ‖iterNabla H k (nabla g T)‖_g
```

Apply the one-step lemma to:

```lean
G p
```

and to every:

```lean
G k, k ∈ Finset.range p.
```

Convert partial sums to the full sum

[
\sum_{i=0}^{p}N_i
]

using `oneStep_partial_to_full`.

Then invoke `main_step_algebra`.

Finally, use the definition of `lemma45Const`:

```lean
simp [lemma45Const]
```

or a helper lemma:

```lean
lemma main_step_coeff_le_lemma45Const
  (hB : ∀ i, 0 ≤ B i) :
  oneStepConst B p s
    + lemma45Const B p (s + 1)
        * (1 + ∑ k in Finset.range p, oneStepConst B k s)
    ≤ lemma45Const B (p + 1) s := by
  simp [lemma45Const]
  nlinarith [
    lemma45Const_nonneg hB p s
  ]
```

---

# Phase 8: Base case (p=1) is no longer special

The paper separately proves (p=1). In the formalized version, do **not** need a special (p=1) theorem.

Why?

The recursive theorem with `p = 1` and `r = 1` follows from the induction step with `p = 0`, plus the one-step lemma at `k = 0`.

For `k = 0`, the one-step lemma says:

[
|\nabla_gT|_g
\le
|\nabla_HT|*g
+
\varepsilon E*{0,s}|T|_g.
]

Since

[
E_{0,s}
=======

sB_0,
]

this matches the paper’s first-order argument. If later you instantiate (B_0=12), this gives:

[
|\nabla_gT|_g
\le
|\nabla_HT|_g
+
12\varepsilon s|T|_g.
]

So Codex should not duplicate the paper’s (p=1) proof inside the main theorem.

---

# Phase 9: Prove the approximate-isometry connection-difference input

Only after the abstract theorem compiles should Codex connect it to approximate isometries.

Create:

```text
DifferentialGeometry/Compactness/ConnDiffApproxIsometry.lean
```

Target:

```lean
theorem connDiff_iter_bound_of_approxIso
  (hΦ : ApproxIsometry Φ g h ε p)
  (hε0 : 0 ≤ ε)
  (hε1 : ε < 1) :
  ∃ B : ℕ → ℝ,
    (∀ k, 0 ≤ B k)
    ∧
    (∀ k < p,
      ‖iterNabla H k A‖_g ≤ ε * B k) := by
  ...
```

where:

```lean
H := pullbackMetric Φ h
A := connDiff g H
```

For the first version, it is acceptable to make `B` explicit:

```lean
noncomputable def connDiffConst (k : ℕ) : ℝ :=
  if k = 0 then 12 else someLargeConstant k
```

But a cleaner version is:

```lean
noncomputable def connDiffConst : ℕ → ℝ
| 0 => 12
| k + 1 => Cconn (k + 1) * (k + 2) * 2 ^ (k + 5)
```

Do not optimize the constant. Use something coarse.

The source proof uses:

[
|\Gamma_g-\Gamma_H|_g\le 12\varepsilon
]

for (k=0), and for (k\ge 1) uses the Lemma 3.11-style estimate:

[
|\nabla_H^k(\Gamma_g-\Gamma_H)|*g
\le
C_k
\sum*{j=1}^{k+1}|\nabla_H^j g|_g
\le
C'_k\varepsilon.
]

Formalize this as two separate lemmas:

```lean
lemma connDiff_zero_bound_of_approxIso :
  ‖A‖_g ≤ ε * 12 := by
  ...
```

```lean
lemma connDiff_iter_bound_of_metric_deriv_bounds
  :
  ‖iterNabla H k A‖_g
    ≤ Cconn k *
      ∑ j in Finset.Icc 1 (k + 1),
        ‖iterNabla H j g‖_g := by
  ...
```

Then:

```lean
lemma metric_deriv_bound_of_approxIso
  :
  ‖iterNabla H j g‖_g ≤ ε * metricDerivConst j := by
  ...
```

Then combine.

---

# Phase 10: Final covariant approximate-isometry theorem

After Phase 9, prove:

```lean
theorem lemma45_covariant_of_approxIso
  (hΦ : ApproxIsometry Φ g h ε p)
  (hε0 : 0 ≤ ε)
  (hε1 : ε < 1)
  (hr0 : 0 < r)
  (hrp : r ≤ p) :
  ‖iterNabla g r T‖_g
    ≤ ‖iterNabla H r T‖_g
      + ε * lemma45Const connDiffConst p s *
          ∑ i in Finset.range r,
            ‖iterNabla H i T‖_g := by
  obtain ⟨B, hB_nonneg, hA_bound⟩ :=
    connDiff_iter_bound_of_approxIso hΦ hε0 hε1
  exact lemma45_covariant_abstract
    hε0 hε1 hB_nonneg hA_bound hr0 hrp
```

Then package the constant:

```lean
noncomputable def C_lemma45_covariant (p s : ℕ) : ℝ :=
  lemma45Const connDiffConst p s
```

Prove positivity:

```lean
lemma C_lemma45_covariant_pos :
  0 < C_lemma45_covariant p s := by
  unfold C_lemma45_covariant
  exact lemma45Const_pos connDiffConst_nonneg
```

---

# Phase 11: Mixed tensors only after covariant tensors compile

Do not let Codex jump to mixed tensors early.

The mixed case needs the slot count:

[
m=q_1+q_2.
]

For a mixed tensor (T), the connection difference acts on every slot:

[
\nabla_gT
=========

\nabla_HT
+
A\diamond T,
]

with `q1 + q2` terms.

The norm estimate becomes:

```lean
‖connDiffActionMixed A T‖_g
  ≤ ((q1 + q2 : ℕ) : ℝ) * ‖A‖_g * ‖T‖_g
```

Then the same constants work with:

```lean
m := q1 + q2
```

Do not use raising/lowering to derive the mixed case unless the project already has strong lemmas saying musical isomorphisms commute with the relevant induced covariant derivatives. Otherwise, converting mixed tensors into covariant tensors creates extra metric-derivative terms and will derail the proof.

---

# Codex task breakdown

Give Codex small tasks in this order.

## Task 1

```text
Create `Lemma45Constants.lean`.
Define `oneStepConst` and `lemma45Const`.
Prove nonnegativity, positivity, and monotonicity in the derivative-order parameter.
Do not import geometry.
Run `lake build`.
```

Acceptance checks:

```lean
#check oneStepConst
#check lemma45Const
#check oneStepConst_nonneg
#check lemma45Const_pos
#check lemma45Const_le_succ
```

---

## Task 2

```text
Create `SumLemmas.lean`.
Prove finite-sum lemmas needed for the induction:
1. partial range sum bounded by larger range sum,
2. shifted sum bounded by full sum,
3. partial one-step estimate upgraded to full one-step estimate,
4. main_step_algebra.
No geometry imports.
Run `lake build`.
```

Acceptance checks:

```lean
#check sum_range_le_sum_range
#check sum_shift_le_full
#check oneStep_partial_to_full
#check main_step_algebra
```

---

## Task 3

```text
Find the repository's existing representation of `(0,s)` tensor fields and iterated covariant derivatives.
Write a short comment block mapping the proof notation to existing Lean names:
H = pullback metric
A = connection difference ∇g - ∇H
N i = norm of i-th H-derivative of T
G k = norm of k-th H-derivative of ∇g T
Do not prove anything yet.
Run `lake build`.
```

Acceptance check: file compiles with only definitions/notation.

---

## Task 4

```text
Formalize the first-order connection comparison for `(0,s)` tensors:
∇g T = ∇H T + A ⋄ T.
Then prove:
‖∇g T‖g ≤ ‖∇H T‖g + s * ‖A‖g * ‖T‖g.
Keep the statement pointwise if tensor norms are pointwise in this repository.
Run `lake build`.
```

Acceptance checks:

```lean
#check nablaG_eq_nablaH_add_connDiffAction_covariant
#check norm_connDiffAction_covariant_le
#check norm_nablaG_le_nablaH_covariant
```

---

## Task 5

```text
Prove the Leibniz estimate for iterated H-derivatives of the slot action:
‖∇H^k (A ⋄ T)‖g
≤ s * ∑_{a=0}^k choose(k,a) ‖∇H^a A‖g ‖∇H^{k-a}T‖g.
Use `Nat.antidiagonal k` if subtraction indices are painful.
Run `lake build`.
```

Acceptance check:

```lean
#check iterNabla_connDiffAction_covariant_le
```

---

## Task 6

```text
Prove the one-step estimate:
‖∇H^k (∇g T)‖g
≤ ‖∇H^(k+1) T‖g
  + ε * oneStepConst B k s * ∑_{i=0}^k ‖∇H^i T‖g,
assuming
∀ a ≤ k, ‖∇H^a A‖g ≤ ε * B a.
Run `lake build`.
```

Acceptance check:

```lean
#check iterNablaH_nablaG_bound_covariant
```

---

## Task 7

```text
Prove the abstract Lemma 4.5 for `(0,s)` tensors under the abstract connection-difference bound:
∀ k < p, ‖∇H^k A‖g ≤ ε * B k.
Use induction on p.
Use `main_step_algebra` for the r = p + 1 case.
Run `lake build`.
```

Acceptance check:

```lean
#check lemma45_covariant_abstract
```

---

## Task 8

```text
Formalize the connection-difference bounds supplied by approximate isometry.
First prove the k=0 estimate.
Then prove or wrap the existing Lemma 3.11-style estimate for k>0.
Package these into:
connDiff_iter_bound_of_approxIso.
Run `lake build`.
```

Acceptance check:

```lean
#check connDiff_iter_bound_of_approxIso
```

---

## Task 9

```text
Combine `lemma45_covariant_abstract` with `connDiff_iter_bound_of_approxIso`
to prove the final covariant approximate-isometry version.
Define the final constant as `C_lemma45_covariant p s`.
Prove it is positive.
Run `lake build`.
```

Acceptance checks:

```lean
#check C_lemma45_covariant
#check C_lemma45_covariant_pos
#check lemma45_covariant_of_approxIso
```

---

## Task 10

```text
Only after the covariant theorem compiles, generalize to mixed `(q1,q2)` tensors.
Add a mixed slot-action operator.
Prove the norm bound with coefficient `q1 + q2`.
Reuse the same abstract theorem with `m = q1 + q2`.
Do not use raising/lowering unless the relevant commutation lemmas already exist.
Run `lake build`.
```

Acceptance check:

```lean
#check lemma45_mixed_of_approxIso
```

---

# Recommended file dependency graph

Use this dependency structure:

```text
Lemma45Constants.lean
        ↓
SumLemmas.lean
        ↓
ConnDiffActionCovariant.lean
        ↓
OneStepCovariant.lean
        ↓
Lemma45CovariantAbstract.lean
        ↓
ConnDiffApproxIsometry.lean
        ↓
Lemma45CovariantApproxIso.lean
        ↓
Lemma45Mixed.lean
```

The important rule: **geometry depends on algebra, not the other way around**.

---

# Main proof skeleton for Codex

Use this as a high-level theorem comment in the abstract file:

```lean
/-
Proof plan for `lemma45_covariant_abstract`.

Let H be the comparison connection and A = ∇g - ∇H.
Let N i = ‖∇H^i T‖g and G k = ‖∇H^k (∇g T)‖g.

We prove by induction on p.

For r ≤ p, use the induction hypothesis and monotonicity of `lemma45Const`.

For r = p+1:
  Apply the induction hypothesis to S = ∇g T, whose covariant rank is s+1:
    ‖∇g^(p+1) T‖g
      ≤ G p + ε * lemma45Const B p (s+1) * ∑_{k<p} G k.

  Apply the one-step estimate:
    G p ≤ N (p+1) + ε * oneStepConst B p s * ∑_{i≤p} N i.
    G k ≤ N (k+1) + ε * oneStepConst B k s * ∑_{i≤p} N i.

  Use `main_step_algebra`.

  The resulting coefficient is
    oneStepConst B p s
      + lemma45Const B p (s+1)
          * (1 + ∑_{k<p} oneStepConst B k s),

  which is ≤ `lemma45Const B (p+1) s` by definition.
-/
```

---

# Things Codex should avoid

1. **Do not unfold approximate isometry inside the main induction.**
   That belongs only in `ConnDiffApproxIsometry.lean`.

2. **Do not use the exact printed constant.**
   The printed constant is intentionally vague. Use coarse recursive constants.

3. **Do not formalize “a sum of terms” inline.**
   This must become the Leibniz estimate and one-step estimate.

4. **Do not begin with mixed tensors.**
   Start with ((0,s))-tensors.

5. **Do not prove global supremum versions first.**
   Prove pointwise norm estimates first. Supremum estimates can be corollaries.

6. **Do not fight coercions from `ℝ≥0` unless the project already uses them.**
   Prefer `ℝ` constants with nonnegativity lemmas.

---

# Final intended theorem progression

The formalization should end with this chain:

```lean
oneStepConst
lemma45Const

iterNablaH_nablaG_bound_covariant

lemma45_covariant_abstract

connDiff_iter_bound_of_approxIso

lemma45_covariant_of_approxIso

lemma45_mixed_of_approxIso
```

That route is much more Codex-friendly than the paper’s route because every hidden bounded-coefficient argument has been converted into a named lemma with an explicit constant.
