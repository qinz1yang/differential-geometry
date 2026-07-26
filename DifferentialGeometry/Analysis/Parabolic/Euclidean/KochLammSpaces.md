# KochLammSpaces

## Why this replaces the earlier rough carrier

The Ricci--DeTurck space in Koch--Lamm, Section 4, does not contain the arm
`sup sqrt(t) |∇h|`.  That stronger arm is not stable under the divergence heat
potential for a general rough flux: the near-terminal operator approaches a
second-order Riesz transform, which is not uniformly bounded from `L∞` to
`L∞`.

The earlier `GradWt`-based `RoughComplete` / `RoughSourceComplete` drafts and
their differentiated heat-potential drafts were therefore deleted before
verification and are not part of the dependency route.  The abstract
`HeatRoughBound.flux_norm` field in the old HMF draft must likewise not be used
as a producer.

## Exact spaces

For `p = n+4` and `q = (n+4)/2`, `KLPath` stores:

1. `L∞` control of the value;
2. `R^(-n/2) L²` control of the gradient on
   `B_R(x) × (0,R²]`;
3. `R^(2/(n+4)) L^p` control of the gradient on
   `B_R(x) × (R²/2,R²]`.

`KLSource0` stores the corresponding `R^(-n) L¹` and
`R^(4/(n+4)) L^q` ordinary-source arms.  `KLSource1` stores the same local
`L²` and late `L^p` arms as a gradient.  `KLSplit` packages
`f₀ + div f₁` without assuming a heat mapping theorem.  Its two fields now
have independent codomains.  This is essential: the ordinary source is
`F`-valued, while the genuine geometric flux is operator-valued
`V →L[ℝ] F`.

The four quantitative radii are `NNReal`, not `ENNReal`.  This records the
finite norm ball needed by the contraction argument and prevents a vacuous
`top` bound from entering the complete carrier.  Each real radius scale also
has an explicit real-valued form used to scale the local `Lp` germ.

## Verification state

- Definitions, scaling exponents, and the two-codomain split-source interface:
  source-complete.
- Focused Lean check: GREEN, with no local warning.  The targeted `.olean`
  refresh completed successfully and is available to immediate consumers.
- Complete carrier: not yet proved; this is the next producer.
- Heat potential: value, local energy, and late singular-integral components
  remain separate proof obligations.
- Endpoint `ricci_flow_forward_unique`: 0%.

Primary reference: Koch--Lamm, *Geometric flows with rough initial data*,
Section 4, Definition of `X_T`, `Y_T` and Lemma 4.3.
