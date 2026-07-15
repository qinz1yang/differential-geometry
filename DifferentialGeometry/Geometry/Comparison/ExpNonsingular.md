# ExpNonsingular.lean — `d exp` injective from Jacobi nonvanishing (B3)

Verification passed, sorry-free (2026-06-11). Step A item-3a: the reduction from the
covariant-Grönwall conclusion to injectivity of `d(exp_p)_x` (the `hloc` input that
`ExpBallDiffeo.exists_expBall_diffeo` needs, modulo the manifold-IFT brick (d)).

## What's here

- `injective_of_ball_ne_zero` (generic, reusable): a CLM `L : E →L[ℝ] F` nonzero on a
  punctured ball around `0` is injective. Proof: `injective_iff_map_eq_zero` (note: NO
  `LinearMap.` prefix — the general `AddMonoidHomClass` lemma applies to CLMs); a kernel
  vector scales into the ball, contradiction.
- `mfderiv_exp_injective_of_jacobi`: if `∀ small w ≠ 0, J_w(1) ≠ 0` (the radial Jacobi
  field nonzero at the endpoint), then `d(exp_p)_x` is injective. Endpoint identity
  `J_w(1) = d(exp_p)_x w` is `radial_jacobi_one` (JacobiVariation.lean).

The `hjac` hypothesis is exactly `covGronwall_ne_zero`'s output (once the radial
regularity, curvature-norm bound, t=0 endpoint, and Grönwall smallness are supplied).

## Status in the B3 chain

This closes the "Jacobi nonvanishing ⟹ mfderiv injective" link. Remaining to reach
`exists_expBall_diffeo`'s `hloc`: the radial instantiation of `covGronwall_ne_zero`
(regularity export + curvature-norm + t=0) AND the manifold IFT brick (d)
`mfderiv-injective(→bijective in fin-dim) ⟹ IsLocalDiffeomorphOn` (Mathlib TODO; mimic
`Exponential/LocalDiffeomorphism.lean`'s at-zero `ContDiffAt.toOpenPartialHomeomorph`
construction with a general invertible derivative).

## Lean gotchas

- `injective_iff_map_eq_zero` is the unprefixed `AddMonoidHomClass` lemma (works on CLM
  directly); `LinearMap.injective_iff_map_eq_zero` does NOT exist.
- `radial_jacobi_one` requires `[T2Space M] [SigmaCompactSpace M]` in scope — carry them
  in the variable block (the HCG consumer has them) rather than deriving `T2Space M` via
  `gauss_t2Space_base` (which lives in `GaussLemmaPullback`, not the `Exponential` ns).
