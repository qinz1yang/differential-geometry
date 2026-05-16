# MSM135 Chapter 6 Progress

The first pass pauses MSM110 work and starts MSM135 Chapter 6 as a formal
statement layer.  RicciFlower owns the reusable definitions; BK owns the
book-label wrappers.

## Main Formulas Recorded

`W` entropy is represented by:

```text
W(g,f,tau) = integral_M [tau * (R + |grad f|^2) + f - n] u dmu
u = (4*pi*tau)^(-n/2) * exp(-f)
```

Current Lean handle:

```text
RicciFlower.RicciFlow.Perelman.WEntropyFormula
RicciFlower.RicciFlow.Perelman.wFunctional
RicciFlower.RicciFlow.Perelman.perelmanDensity
RicciFlower.RicciFlow.Perelman.perelmanWeightedMeasure
```

The concrete integral layer now records:

```text
u(x) = (4*pi*tau)^(-n/2) * exp(-f(x))
W(mu,n,tau,R,G,f)
  = integral_M [tau * (R(x) + G(x)) + f(x) - n] d(u mu)
```

The two elementary properties are represented as proved interface bridges:

```text
Scale invariance:
if d(u_{c*tau,f} mu_scaled) = d(u_{tau,f} mu)
and c * R_scaled = R, c * G_scaled = G pointwise,
then W(mu_scaled,n,c*tau,R_scaled,G_scaled,f) = W(mu,n,tau,R,G,f).

Diffeomorphism invariance:
if phi maps the pulled-back weighted measure to the original weighted measure,
then W(mu,n,tau,R,G,f)
  = W(mu_pullback,n,tau,R o phi,G o phi,f o phi).
```

Lemma 6.1 is now represented by a proved algebraic final step:

```text
W_path(s) = W(mu_s, n, tau_s, R_s, G_s, f_s)
delta W at s0 = d/ds W_path(s) | s=s0

delta W = integral preIBP_integrand d(u mu)
g_ij*(Ric_ij + Hess_ij f) = R + Delta f
integral (Delta f - |grad f|^2) d(u mu) = 0
------------------------------------------------
delta W = integral lemma61_integrand d(u mu)
```

The final integrand is the scalar-contracted form of:

```text
(-tau*v_ij + zeta*g_ij) *
  (Ric_ij + Hess_ij f - (1/(2*tau))*g_ij)
+ tau*(V/2 - h - n*zeta/(2*tau)) *
  (R + 2*Delta f - |grad f|^2 + (f - n - 1)/tau)
```

Current Lean handles:

```text
RicciFlower.RicciFlow.Perelman.wEntropyWeightedMeasureVariationFactor
RicciFlower.RicciFlow.Perelman.WEntropyWeightedMeasurePreservingVariation
RicciFlower.RicciFlow.Perelman.wEntropyFirstVariationPreIBPIntegrand
RicciFlower.RicciFlow.Perelman.wEntropyFirstVariationLemma61Integrand
RicciFlower.RicciFlow.Perelman.wFunctionalAlong
RicciFlower.RicciFlow.Perelman.WEntropyHasFirstVariationAt
RicciFlower.RicciFlow.Perelman.wEntropyFirstVariation
RicciFlower.RicciFlow.Perelman.wEntropyFirstVariation_lemma61_of_preIBP
RicciFlower.RicciFlow.Perelman.wEntropyFirstVariation_eq_lemma61_of_hasFirstVariationAt_preIBP
RicciFlower.RicciFlow.Perelman.perelmanDensity_hasDerivAt
RicciFlower.RicciFlow.Perelman.wEntropyBracket_hasDerivAt
RicciFlower.RicciFlow.Perelman.weightedMeasureIntegral_hasDerivAt_at
RicciFlower.RicciFlow.Perelman.wEntropyBaseIntegral_hasDerivAt_at
RicciFlower.RicciFlow.Perelman.WEntropyHasFirstVariationAt_of_volumeVariation
```

The elementary producer layer now proves:

```text
d/ds [(4*pi*tau_s)^(-n/2) exp(-f_s)]
  = (-n*zeta/(2*tau) - h) * u

d/ds [tau_s * (R_s + G_s) + f_s - n]
  = zeta * (R + G) + tau * (Rdot + Gdot) + h

d/ds integral_M u_s * phi_s dmu_s
  = integral_M u * (phiDot + phi * (-n*zeta/(2*tau) - h + V/2)) dmu
```

For `phi = tau*(R+G)+f-n`, this gives the scalar/base-integral first
variation producer for `W`.  The remaining bridge to the full Lemma 6.1
pre-IBP expression is formula 5.10, the first variation of Perelman's
`F` functional.

The monotonicity display is represented abstractly as:

```text
d/dt W = nonnegative square term >= 0
```

Current Lean handles:

```text
RicciFlower.RicciFlow.Perelman.WEntropyDerivativeFormula
RicciFlower.RicciFlow.Perelman.WEntropyMonotoneOn
```

The `mu` and `nu` layers are represented as lower-bound/minimizer predicates:

```text
mu(g,tau) <= W(g,f,tau) for every admissible f
nu(g) <= mu(g,tau) for every tau > 0
```

Current Lean handles:

```text
RicciFlower.RicciFlow.Perelman.MuFunctionalLowerBound
RicciFlower.RicciFlow.Perelman.MuFunctionalHasMinimizer
RicciFlower.RicciFlow.Perelman.NuFunctionalLowerBound
RicciFlower.RicciFlow.Perelman.NuFunctionalHasMinimizer
```

Noncollapsing is represented by scale-controlled balls:

```text
if |Rm| <= r^(-2) on the relevant parabolic/geometric neighborhood,
then Vol(B(x,r)) >= kappa * r^n
```

Current Lean handles:

```text
RicciFlower.RicciFlow.Perelman.ScaleControlledBall
RicciFlower.RicciFlow.Perelman.RicciFlowKappaNoncollapsedBelowScale
RicciFlower.RicciFlow.Perelman.NoLocalCollapsingTheoremA
RicciFlower.RicciFlow.Perelman.NoLocalCollapsingTheoremB
```

## What Is Proved

The concrete `W` definition, the two elementary invariance bridges, the actual
path derivative definition of first variation, and the algebraic final step of
Lemma 6.1 are proved.  The bridges do not yet prove the metric scaling laws or
pullback volume/scalar/gradient compatibility.  Lemma 6.1 still needs geometric
producers turning a metric/potential/time-scale path into the scalar path
derivative, the three variation inputs, and the weighted integration-by-parts
identity.

## What Is Missing

The real frontier is not notation.  It is the analytic and global geometry
infrastructure needed to interpret the predicates with actual Ricci-flow data:
Riemannian integration, conjugate heat solutions, Sobolev spaces, entropy
infima/minimizers, pointed Cheeger-Gromov convergence, Hamilton compactness,
metric ball volume comparison, and singularity models.
