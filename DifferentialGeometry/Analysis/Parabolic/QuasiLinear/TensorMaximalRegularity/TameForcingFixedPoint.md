# TameForcingFixedPoint

## Status

The source implementation is complete, its focused Lean check passed with no
warnings or errors, and its named export was refreshed successfully.  No
`sorry`, `admit`, axiom, or replacement hypothesis is present in this file.

## Proved interfaces in the source

- `dense_cont_on_balls`: if `F : D -> Y` is defined on a dense subset of an
  arbitrary pseudometric state space and is Lipschitz on every closed ball
  about one fixed centre, then `Dense.extend hD F` is continuous.  The proof
  uses local Cauchy preservation, not a nonexistent global Lipschitz constant.
  The pseudometric formulation is essential: the intended ambient object is
  the `lowerState` ball subtype, which is not closed under addition.
- `tame_lip_balls`: when the state space embeds isometrically into the top
  normed space and the chosen centre maps to zero, the three-arm estimate is
  Lipschitz on every finite top-size ball.  Its local constant is
  `A*R + B*||J|| + 2*C*max(r,0)*||J||`; it makes no false global-Lipschitz
  claim.
- `dense_tame_extend`: if the state space is continuously realized in a normed
  vector space, a three-arm tame estimate holding on the dense core passes to
  `Dense.extend`.  The proof first identifies the extension with the core map,
  then uses continuity of both sides and density of the product core to close
  the inequality.  This is the exact bridge from `smoothCore` estimates to a
  nonlinearity on all of `lowerState`.
- `partial_sol_tame`: a continuous nonlinearity on the lower Sobolev state ball
  has a forcing-space fixed point when it satisfies

  ```text
  ||N u - N v|| <=
      A R ||u-v||_top
    + B ||J(u-v)||_low
    + C (||u||_top + ||v||_top) ||J(u-v)||_low.
  ```

  The explicit assumptions are `A*R <= 1/16`, `C*R <= 1/16`, and
  `||N 0|| <= D`.  It chooses forcing radius `rho = R/4` and

  ```text
  T0 = min 1 (min (1 / (64*(B+1)^2))
                    ((rho / (2*(D+1)))^2)).
  ```

  On `T <= T0`, the contraction coefficient is

  ```text
  A R (1+T) + 2 B sqrt(T)
    + 2 C rho sqrt(1+T) (1+T) <= 1/2.
  ```

  The output has the same solution-space, state-set, pointwise forcing,
  trace, PDE, and forcing-radius fields as `partial_sol_const`.

## Mathematical route ruling

The old proposed global `H3 -> H1` Lipschitz bound on the entire lower `H2`
state ball is false: the ball leaves the `H3` norm unbounded, while the
linearized cometric term contains a highest-derivative contribution of the
form `U * nabla^3 g`.  A fixed radial `H3` truncation is also insufficient,
because maximal regularity controls the top norm only in time `L2`, so the
fixed point cannot be shown to remain inside a pointwise `H3` ball.

The three-arm tame estimate is the correct replacement.  The third arm is
integrable because the lower difference has an a.e. time-uniform bound while
both endpoint top norms are in time `L2`.

## Verification

A focused source check passed with no warnings or errors after refreshing
`PartialForcingFixedPoint.lean` and its import chain.  The final elaboration
repair was to prove the repeated scalar inequality `ha12` once and reuse it;
this removed a deterministic `whnf` heartbeat timeout caused by asking many
separate `linarith` calls to normalize the same large expression.  No heartbeat
limit was raised.  The named export refresh also completed successfully.

Endpoint accounting is unchanged: this is solver machinery, not a proof of
`ricci_flow_unif_existence`.  In particular the current low-regularity chain is
dimension three and still needs uniform-family constants, fixed-background
Sobolev comparison, uniform zero-forcing control, and smoothing on the same
horizon.

## Generic-endpoint API audit

The existing dimension-generic family front end is
`exists_low_reg_coeff`: the exact ellipticity and order-`<= 3`
`MetricCovDerivOrderBoundOn` hypotheses of the public endpoint already produce
one family-uniform `LowRegCoeff`.  Its current consumers include
`rhs_h1_bdd`, `rhs_h0_lip`, and `rhs_h1_lip`.  The last estimate cannot be used
for the critical contraction because its `H3` coefficient is not small.

No shorter generic closure was found.  The finite-chart APIs
`chartGram_pou_bnd`, `chartGram_pou_d1/d2/d3`, `chartRHS_pou_lip/bnd`, and
`chartRHSD_pou_lip/bnd` supply the expected uniform `C3` coefficient data, but
the repository has neither a Schauder/`W2p` quasilinear parabolic solver nor a
theorem making the lifetime stable on a `C2` or `C^{2,alpha}` initial-data
neighbourhood.  It also lacks integrated cross-metric Sobolev equivalence
through order three.  Thus the unchanged generic endpoint remains
mathematically true but needs a new dimension-generic low-order parabolic
engine (including same-horizon smoothing); finite covering alone cannot turn
this dimension-three tame solver into that theorem.
