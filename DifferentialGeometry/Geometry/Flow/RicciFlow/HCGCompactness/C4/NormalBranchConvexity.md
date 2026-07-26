# NormalBranchConvexity

## 2026-07-14 checked result

`HasNormalBrFull.strict_dist` turns the selected normal branch's positive
Hessian bound into complete `StrictDistInput` for the intrinsic minimizing
join. It proves nonzero speed for every nonconstant `minJoin`, strict
convexity for every active target, the two endpoints, and midpoint confinement
by applying the same strict-convexity result with the source center as target.

The physical ledger is exactly `R + 6 * rad < rho / 2`: `R` is the
source-to-branch-center distance, `2 * rad` controls the active endpoint, and
`4 * rad` controls the joining geodesic. No manifold-ball convexity
assumption, endpoint radius field, glued weights, or new branch hierarchy was
introduced. Focused verification and exact target refresh passed.

The fixed-configuration `StrictDistInput` producer is **100%**. The concrete
`StepB1RawInput` producer, textbook B1 theorem, and compactness endpoints remain
theorem-level **0%**.
