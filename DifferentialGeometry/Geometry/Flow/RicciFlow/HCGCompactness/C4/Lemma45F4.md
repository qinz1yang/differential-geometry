# Lemma45F4.lean — MSM135 Corollary II endpoint (`lemma45_corII`, F4)

The book-facing F4 endpoint that F5/F6/Step B consume: Cor II with the intrinsic
Lemma I `hF3` discharged from the approximate-isometry data, so consumers need
no `hF3` hypothesis.

## Complete 2026-07-09

`lemma45_corII`, `lemma45_corII_unif`, and the exact-constant core
`lemma45_corII_bound` are proved and verified with no local `sorry` warning.
The proof chooses a smooth frame that is `g`-orthonormal at the evaluation point,
works on `u' ∩ u`, uses `metricComp_mul` to absorb the good-frame and metric-swap
loss into `4^(2+p)`, applies the explicit-constant `lemma45_F3_bound`, lifts via
`hF3_term`, and closes with `lemma45_cor_II_of_intrinsic`.

## 2026-07-09 feasibility route used

The proof was not a direct plumbing call.  The good-frame bridge gives component
smallness with an explicit factor: the new checked lemma
`RicBoundGoodFrame.metricComp_le` proves
`compL2(...) <= 2^(2+j) * eps` from the intrinsic `sqrt(normSq0S) <= eps`
hypothesis.  However, `lemma45_F3` currently consumes an unscaled component
smallness parameter satisfying `eps <= 1`.

The implemented route was the first option: `claim1MulConst` makes the Claim-1
constant data-independent, `lemma45_F3_bound` accepts `L * eps`, and
`metricComp_mul` supplies the uniform `L = 4^(2+p)` after the metric swap.

## Statement (consumers depend only on this)

`lemma45_corII (hu) (g gRef) (T : Tensor0SField q₂) (p eps) (heps0 heps1)
  (hequiv : C⁻¹gRef ≤ g ≤ CgRef on u, C = 1+eps)
  (hgK : √normSq0S gRef (∇_gRef^j g) ≤ eps, 1≤j≤p, on u)
  : ∃ Cc ≥ 0, ∀ x ∈ u, ∀ 0 < r ≤ p,
     √normSq0S g (∇_g^r T) ≤ √((1+eps)^{q₂+r})·(√normSq0S gRef (∇_gRef^r T) +
        eps·Cc·Σ_{k<r} √normSq0S gRef (∇_gRef^k T))`.

Imports the checked component engine, intrinsic/covariant lifts, and good-frame
producer used by the completed proof.

## What consumes it: F5 (Composition I, C^p)

Same-domain, three metrics on a common domain. Apply `lemma45_corII` with
`g:=g₀, gRef:=g₁, T:=g₂−g₁`; triangle through `g₁`; the lower-order terms via the
approx data + `compEpsAccum` (ApproxIsometryComp, green). Pieces present:
`sqrt_normSq0S_add_le` (fiber Minkowski, basis form), `iterCov_add`.
**Confirmed: F5/F6 need only F4, not the absent map-level pullback-naturality**
(the project is same-domain throughout, so Cor II applies directly to the metric
difference — no `Φ*`-of-tensor, no `∇_{Φ*h}(Φ*T)=Φ*(∇_h T)`).
