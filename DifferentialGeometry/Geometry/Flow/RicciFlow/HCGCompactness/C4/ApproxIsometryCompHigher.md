# ApproxIsometryCompHigher.lean — F5/F6 derivative (C^p) layer (green 2026-06-11)

MSM135 Composition of approximate isometries, I/II (`lbl371`/`lbl372`), derivative
side, same-domain. Both sorry-free; they rest only on the F4 endpoint
`lemma45_corII` (`Lemma45F4.lean`), which carries the single documented
assembly-`sorry` (the real lift math is green in `Lemma45Intrinsic.lean`).

## `comp_cov_le` (F5, `lbl371` C^p)

For error tensors `δ₀`, `δ₁` on a common domain with `|∇_{g₀}^r δ₀|_{g₀} ≤ ε₀` and
`|∇_{g₁}^k δ₁|_{g₁} ≤ ε₁`, the composed error obeys
`|∇_{g₀}^r(δ₀+δ₁)|_{g₀} ≤ ε₀ + ε₁·C_p`, `C_p = √(2^{2+p})·(1+Cc·p)`.

Proof chain: `iterCov_add` splits the composed tower; fiber Minkowski at a g₀-ON
basis (`exists_gOrthonormalBasis` → `metricInverseInBasis_of_orthonormal` →
`sqrt_normSq0S_add_le`) bounds it by the `δ₀` term (`≤ ε₀`) + the `δ₁` term; the
`δ₁` term via `lemma45_corII (g₀, g₁, δ₁)` + `|∇_{g₁}^k δ₁|_{g₁} ≤ ε₁`; the
`(1+ε₀)^{2+r}/Cc` constants collapse to `C_p` (one `nlinarith` over product hints).

## `comp_cov_accum` (F6, `lbl372`)

`e n ≤ C·Σ_{i≤n} εᵢ` — the scalar fold `compEpsAccum` (ApproxIsometryComp.lean).

## Lean gotchas

- `δ₀ + δ₁` on `Tensor0SField` needs `set_option backward.isDefEq.respectTransparency
  false` for the `Add` instance to synthesize (same as `•`).
- the field-sum eval `(A+B) x = A x + B x` is `rw [iterCov_add]; rfl` (under that
  option).
- `pow_le_pow_left₀` (not `pow_le_pow_left`); `nlinarith` is a tactic, not a term
  (`:= by nlinarith`, not `:= nlinarith`).
- fiber Minkowski `sqrt_normSq0S_add_le` is the basis form — needs a g₀-ON basis
  (intrinsic norm triangle is realized through `exists_gOrthonormalBasis` per point,
  NOT a smooth frame; no good-frame producer needed for F5).
