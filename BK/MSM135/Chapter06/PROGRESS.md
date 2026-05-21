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

The formula 5.10 route now has a RicciFlower statement layer:

```text
F(mu,R,G,f) = integral_M (R + G) e^{-f} dmu

d/ds [exp(-f_s)] = -h exp(-f)

d/ds integral_M exp(-f_s) phi_s dmu_s
  = integral_M exp(-f) * (phiDot + phi*(V/2 - h)) dmu

delta F =
  - integral_M v_ij (Ric_ij + Hess_ij f) e^{-f} dmu
  + integral_M (V/2 - h)
      (R + 2 Delta f - |grad f|^2) e^{-f} dmu
```

Current Lean handles:

```text
RicciFlower.RicciFlow.Perelman.fFunctional
RicciFlower.RicciFlow.Perelman.expNegPotentialDensity_hasDerivAt
RicciFlower.RicciFlow.Perelman.expWeightedMeasureIntegral_hasDerivAt_at
RicciFlower.RicciFlow.Perelman.FFunctionalHasFirstVariationAt_of_volumeVariation
RicciFlower.RicciFlow.Perelman.weightedIBP
RicciFlower.LeviCivita.lcGammaVar
RicciFlower.LeviCivita.lcRicciVarCoord
RicciFlower.LeviCivita.lcHessVarCoord
RicciFlower.LeviCivita.lcRicciHessVarCoord
RicciFlower.LeviCivita.lcRicciHessVarShifted
RicciFlower.LeviCivita.gammaTraceVar_of_lcGammaVar
RicciFlower.LeviCivita.gammaTraceCovVar
RicciFlower.Analysis.DivergenceTheorem.expNegWeightedGreen
RicciFlower.Analysis.DivergenceTheorem.expNegLap
RicciFlower.Analysis.DivergenceTheorem.expNegGreen
RicciFlower.RicciFlow.Perelman.MetricVariationChristoffelInFrame
RicciFlower.RicciFlow.Perelman.MetricVariationChristoffelTraceInFrame
RicciFlower.RicciFlow.Perelman.RicciVariationByChristoffelInFrame
RicciFlower.RicciFlow.Perelman.HessianPotentialVariationByChristoffelInFrame
RicciFlower.RicciFlow.Perelman.ricciHessianWeightedDivergence_of_ricci_hessian
RicciFlower.RicciFlow.Perelman.ricciHessianWeightedDensity_of_divergence
RicciFlower.RicciFlow.Perelman.inverseMetricVariationContractionTermInFrame
RicciFlower.RicciFlow.Perelman.RicciHessianWeightedDensityVariationInFrame
RicciFlower.RicciFlow.Perelman.FFunctionalFormula510
RicciFlower.RicciFlow.Perelman.formula510_of_steps
RicciFlower.RicciFlow.Perelman.weightedGreen
RicciFlower.RicciFlow.Perelman.weightedDivZero
RicciFlower.RicciFlow.Perelman.connTraceVec
RicciFlower.RicciFlow.Perelman.connTraceDivEq
RicciFlower.RicciFlow.Perelman.weightedDivZero_of_connTrace
RicciFlower.RicciFlow.Perelman.shiftIntEq
RicciFlower.RicciFlow.Perelman.formula510_of_ints
RicciFlower.RicciFlow.Perelman.formula510_of_connTrace
RicciFlower.Realized.connTraceField
RicciFlower.RicciFlow.Perelman.formula510_of_connTraceField
RicciFlower.RicciFlow.Perelman.connTraceAction_coord
RicciFlower.RicciFlow.Perelman.connTraceAction_eq_gamma
RicciFlower.RicciFlow.Perelman.gammaRawDivergenceTrace
RicciFlower.RicciFlow.Perelman.christoffelWeightedDivergenceTrace
RicciFlower.RicciFlow.Perelman.weightedTrace_eq
RicciFlower.RicciFlow.Perelman.weightedTrace_of_raw
RicciFlower.RicciFlow.Perelman.connTraceChartCoeff_eventually
RicciFlower.RicciFlow.Perelman.connTraceChartCoeffOnE_eventually
RicciFlower.RicciFlow.Perelman.connTraceChartCoeff_partial
RicciFlower.RicciFlow.Perelman.connTraceChartCoeff_center
RicciFlower.RicciFlow.Perelman.connTraceRawDiv_voss
RicciFlower.RicciFlow.Perelman.connTraceRawDiv_chart_product
RicciFlower.RicciFlow.Perelman.connTraceRawDiv_chart_explicit
RicciFlower.Analysis.DivergenceTheorem.divergence_g_chart_product
RicciFlower.RicciFlow.Perelman.formula510_of_trace
RicciFlower.Variation.MetricPotentialVariationPath
RicciFlower.Variation.IsMetricPotentialVariationPath
RicciFlower.RicciFlow.Perelman.FHasVariation
RicciFlower.RicciFlow.Perelman.f_firstVariation_formula510
```

The newest reformulation adds the canonical path-based meaning of
`delta_(v,h)F(g,f)`.  The coordinate and divergence formulas above are now
proof-layer infrastructure feeding that endpoint, not the book-facing
definition of first variation.

The remaining formula 5.10 frontier is no longer the local `delta Ric` or
`delta Hess f` calculation, and the arbitrary-test `Delta(exp(-f))` expansion
is now proved.  The metric-trace derivative bridge is also now produced by
`RicciFlower.LeviCivita.lcTraceShifted`.  The actual smooth divergence field
used by the closed divergence theorem is now constructed in the form:

```text
X = e^{-f} traceVec
div X = e^{-f} * (div traceVec - traceVec(f)).
```

The smooth trace vector is now constructed intrinsically as
`RicciFlower.Realized.connTraceField`, with coordinate formula
`(tr_g A)^p = sum_i sum_j g^{ij} A^p_ij`.  The current gap is now the
covariant normalization of the raw divergence realization for that constructed
field.  The action realization is now proved:

```text
tr_g A acting on f
  = sum_p (sum_i sum_j g^{ij} A^p_ij) * partial_p f
```

The scalar contraction of the weighted connection variation has also been
normalized:

```text
sum_i sum_j g^{ij} (nabla_p A^p_ij - A^p_ij partial_p f)
  = gammaRawDivergenceTrace - gammaActionTrace.
```

Equivalently, once the raw divergence bridge
`connTraceRawDiv = gammaRawDivergenceTrace` is supplied,
`weightedTrace_of_raw` gives:

```text
christoffelWeightedDivergenceTrace
  = connTraceRawDiv - connTraceAction.
```

The chart side of the raw divergence is also now exposed:

```text
chartCoeff(tr_g A)^p
  = sum_i sum_j g^{ij} A^p_ij

divergence_g(tr_g A)
  = Voss-Weyl chart expression using partial_p
      (chartCoeff(tr_g A)^p * chartDensity).
```

The Voss-Weyl expression is now split by the product rule:

```text
divergence_g(tr_g A)
  = sum_p partial_p (tr_g A)^p
    + (sum_p (tr_g A)^p partial_p rho) / rho.
```

The chart coefficient has also been normalized on the model chart:

```text
chartCoeffOnE(tr_g A)^p(y)
  = sum_i sum_j g^{ij}(y) A^p_ij(y)

partial_p chartCoeffOnE(tr_g A)^p(center)
  = partial_p [sum_i sum_j g^{ij}(y) A^p_ij(y)](center).
```

Thus the raw divergence now has a checked explicit Voss-Weyl form:

```text
divergence_g(tr_g A)
  = sum_p partial_p [sum_i sum_j g^{ij} A^p_ij]
    + (sum_p [sum_i sum_j g^{ij} A^p_ij] partial_p rho) / rho.
```

The remaining normalization is the standard density/Christoffel trace
identity together with metric compatibility, turning the two displayed terms
into

```text
sum_i sum_j g^{ij} sum_p nabla_p A^p_ij.
```

The assembly theorem now has a cleaner intrinsic form:

```text
formula510_of_trace
```

It supplies `rawTrace` and `actionTrace` from the constructed field itself and
leaves one pointwise bridge:

```text
weightedDivergenceTrace =
  divergence_g(tr_g A) - (tr_g A)(f).
```

Once those component identities are available, applications can feed the
produced pre-cancellation first variation into
`formula510_of_trace`.
The weighted integration-by-parts interface exists as
`BK.MSM135.Chapter06.Section01.lbl552_weighted_ibp`, aliasing
`RicciFlower.RicciFlow.Perelman.weightedIBP`.

The weighted IBP statement is:

```text
integral_M (Delta_g f - |grad_g f|^2) d(e^{-f} mu_g) = 0.
```

It is not yet a completely closed smooth-compact corollary: it keeps the
weighted-density measurability and two base integrability hypotheses explicit.
The previous analysis-layer frontier `gradFun_exp_neg` has been proved.

The first formula 5.10 geometry producer is now proved as the arbitrary
Levi-Civita metric-variation Christoffel formula:

```text
delta Gamma^k_ij =
  1/2 g^{kl} (nabla_i v_jl + nabla_j v_il - nabla_l v_ij).
```

Current Lean handle:

```text
RicciFlower.LeviCivita.lcGammaVar
```

It assumes raw metric component derivatives, fixed-base covariant metric
derivatives, Christoffel component derivatives, and inverse metric components
at the base time.

The next geometry producer is also now proved in coordinate-frame form:

```text
d/ds Ric_ij(g_s)|base =
  nabla_p(delta Gamma^p_ij) - nabla_i(delta Gamma^p_pj).
```

Current Lean handle:

```text
RicciFlower.LeviCivita.lcRicciVarCoord
```

This is the right local-coordinate shape for formula 5.10.  It assumes the
Christoffel component derivative and mixed time/spatial derivative packages
rather than deriving them from metric regularity in this pass.

The scalar-potential Hessian variation producer is also now proved in
coordinate-frame form:

```text
d/ds Hess_ij(f_s)|base =
  Hess_ij(h) - (delta Gamma^p_ij) partial_p f.
```

Current Lean handle:

```text
RicciFlower.LeviCivita.lcHessVarCoord
```

It consumes explicit scalar first- and second-coordinate derivative variation
packages.

The combined coordinate producer is now also proved:

```text
delta(Ric_ij + Hess_ij f)
  =
  nabla_p A^p_ij - A^p_ij partial_p f
  + Hess_ij h - nabla_i A^p_pj.
```

Current Lean handle:

```text
RicciFlower.LeviCivita.lcRicciHessVarCoord
```

After supplying the trace bridge
`nabla_i A^p_pj = (1/2) Hess_ij V`, the shifted book form is:

```text
delta(Ric_ij + Hess_ij f)
  =
  nabla_p A^p_ij - A^p_ij partial_p f
  + Hess_ij(h - V/2).
```

Current Lean handle:

```text
RicciFlower.LeviCivita.lcRicciHessVarShifted
```

The Perelman-facing algebra bridges now package this into the density and
contraction interfaces:

```text
RicciFlower.RicciFlow.Perelman.ricciHessianWeightedDivergence_of_ricci_hessian
RicciFlower.RicciFlow.Perelman.ricciHessianWeightedDensity_of_divergence
RicciFlower.RicciFlow.Perelman.inverseMetricVariationContractionTermInFrame
```

The Green layer also has the arbitrary-test pre-expansion identity:

```text
integral e^{-f} Delta q dmu =
  integral q Delta(e^{-f}) dmu.
```

Current Lean handle:

```text
RicciFlower.Analysis.DivergenceTheorem.expNegWeightedGreen
```

The Green layer now also has the expanded arbitrary-test identity:

```text
Delta(exp(-f)) = exp(-f) * (-Delta f + |grad f|^2)

integral e^{-f} Delta q dmu =
  integral q * e^{-f} * (-Delta f + |grad f|^2) dmu.
```

Current Lean handles:

```text
RicciFlower.Analysis.DivergenceTheorem.expNegLap
RicciFlower.Analysis.DivergenceTheorem.expNegGreen
```

The remaining formula 5.10 bridge is no longer this exponential expansion, nor
the metric-trace derivative input to `gammaTraceCovVar`.  The final scalar
integral assembly is now represented by:

```text
RicciFlower.RicciFlow.Perelman.weightedGreen
RicciFlower.RicciFlow.Perelman.weightedDivZero
RicciFlower.RicciFlow.Perelman.shiftIntEq
RicciFlower.RicciFlow.Perelman.formula510_of_ints
```

What remains is the geometric realization of the divergence field in the
contracted Christoffel term, plus connecting the produced pre-cancellation
first variation to `formula510_of_ints`.

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
