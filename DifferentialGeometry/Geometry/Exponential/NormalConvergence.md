# NormalConvergence

## 2026-07-15

`normalGeodesicSpray_conv` is the thin exponential-layer specialization of the
generic metric-spray convergence theorem.  It consumes open-domain `C∞`
metric convergence and pointwise coercivity and concludes `C∞` convergence on
the full phase domain `U × Set.univ`; no velocity bound or endpoint-radius
assumption is introduced.

Focused verification passed.  The next analytic frontier is the generic
`MapCInfConvOnCompacts.ode_solutionAt` theorem in `Analysis/ODE`, not another
normal-coordinate wrapper.  The concrete `StepB1RawInput` producer statement is
already exposed as `MetricCompactBase.exists_b1_raw`, but its proof remains 0%
complete; this checked spray specialization is only dedicated infrastructure.
