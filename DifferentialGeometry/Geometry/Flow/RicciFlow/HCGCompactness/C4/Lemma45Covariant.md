# Lemma45Covariant.lean — MSM135 Corollary II (F4), same-domain

## Chapter 4, F4 = Corollary *Norms of covariant derivatives of tensors, II* (`lbl370`)

Book statement (line 369, chapter4.tex): for an (ε,p)-approx isometry
Φ:(M,g)→(N,h) and a (0,q₂)-tensor T on N,
`|∇_g^r(Φ*T)|_g ≤ (1+ε)^{(r+q₂)/2}(|∇_h^r T|_h + ε·C·Σ_{k<r}|∇_h^k T|_h)`, 1≤r≤p.

Proof = Lemma I (F3 = `lemma45_F3`) applied to `Φ*T` + pullback naturality
`∇_{Φ*h}(Φ*T)=Φ*(∇_h T)` + norm comparison `|Φ*S|_g ≤ (1+ε)^{deg/2}|S|_h`.

**KEY (same-domain formulation):** drop the map Φ; work on ONE domain with two
metrics `g` and `gRef = Φ*h`.  Then `Φ*T = T'` (a tensor on the domain),
`∇_{Φ*h} = ∇_gRef`, and `|S|_h = |Φ*S|_{Φ*h} = |·|_gRef` (Φ is an isometry
`(N,h)→(M,Φ*h)`).  So **pullback-naturality is automatic** (no pullback-connection
object — which is ABSENT in the repo — is needed), and the corollary becomes a
relation between `g`- and `gRef`-norms of towers of `T'`.

## What's GREEN (2 bricks this session, Ch4 switch)

1. **`sqrt_normSq0S_le_of_metric_equiv`** (Tensor/RSTensor/Tensor0SRiemannian/
   Comparison.lean, the `MetricEquiv` section) — the book's `(1+ε)^{(r+q₂)/2}`
   factor: `√normSq0S h x s T ≤ √(C^s)·√normSq0S g x s T` from
   `normSq0S_upper_le_of_equiv` + `Real.sqrt_mul`.  Pure fiber, no frame.
2. **`lemma45_cor_II_of_intrinsic`** (this file) — Corollary II from the
   **intrinsic** Lemma I (`hF3`, the `normSq0S`-form, taken as hypothesis):
   per-term `sqrt_normSq0S_le_of_metric_equiv` (convert each `gRef`-tower norm
   from `g` to `gRef`) + factor-out `√(C^{q₂+r})` over `0≤k≤r` (pow-monotone).
   `∃C`-free; quantified `∀ 0<r≤p`.  Uses `pow_le_pow_right'` (NOT
   `pow_le_pow_right₀`, which doesn't exist).

## Remaining frontier for the BOOK F4 = the intrinsic Lemma I lift

`lemma45_cor_II_of_intrinsic`'s `hF3` is the **intrinsic** (`normSq0S`-form)
Lemma I:
`√normSq0S g (∇_g^r T') ≤ √normSq0S g (∇_gRef^r T') + εC·Σ√normSq0S g (∇_gRef^k T')`.
`lemma45_F3` (Lemma45Engine.lean, green) is the COMPONENT (`compL2`) form over a
local frame.  The lift compL2 ↔ √normSq0S is the **`B5` bridge**
(`compL2_tower_eq`, Claim1Wiring.lean) at a `gRef`-orthonormal frame point —
i.e. it needs the **good gRef-ON-centered smooth frame** (constant Gram–Schmidt
of a trivialization frame), the SAME infrastructure as the ric_bound R4 frontier.
Once that frame producer exists, `hF3` is discharged and F4 is fully proven
(and the same producer also closes the ric_bound endpoint).

NOTE the LHS of `hF3` keeps the `g`-norm of the `g`-tower (NOT converted) — only
the `gRef`-towers (measured in `g`) are converted to `gRef`-norms.  This matches
the book: the leading `|∇_h^r T|_h` and the lower `|∇_h^k T|_h` are the converted
terms; the `|∇_g^r(Φ*T)|_g` LHS is untouched.

## Downstream (Ch4 Track α)

F4 feeds F5 (`lbl371`, Composition of approx isometries I): the book applies
Corollary II to `T' := Φ₁*g₂ − g₁`.  F5's C⁰ part is already green
(`ApproxIsometryComp.lean`); its C^p part consumes F4.  Then F6, F7→F8,
F9–F13 (done) → Step B (`lbl404/405`) → Steps C, D → `metricCompactness`.
