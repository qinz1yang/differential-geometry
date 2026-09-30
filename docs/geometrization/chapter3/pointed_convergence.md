# Pointed metric convergence: MC11

`PointedGHConverges p q` means that the target metric space is complete and,
for every pair of real parameters `0 < ε < R`, eventually there is a
`PointedBallApprox (p n) q R ε`. The varying source types share one universe;
the target may be in another universe. No source completeness or properness
is imposed. The index threshold depends on radius and error; no point-dependent
threshold and no map uniform in all tolerances is claimed.

This is exactly the chapter's convergence definition at master207A.tex:1115ff,
with `R > 0` following from `0 < ε < R`. The completeness condition is retained
as part of the proposition, rather than silently omitted. Source references
and convention checks are the unchanged MC11 record in metric_geometry_contracts.csv
and reference_checks_revision58/60.md: BBI8.1.1 printed272/PDF287 and KL3.2
printed21–22/PDF16–17. The basic derived implications below use the blueprint's
written restriction and quasi-inverse calculations.

Proved consequences:

- Every strictly increasing natural subsequence has the same pointed limit.
- All-radius eventual forward approximations are equivalent to all-radius
  eventual reverse approximations, with completeness still required on the
  named limit. The proof starts on radius R+ε with error ε/4 and uses the
  actual quasi-inverse. No same-error inverse is assumed.
- Every constant sequence in a complete metric space converges to itself.
- The all-radius convergence criterion is equivalent to the corresponding
  open-ball criterion. Each direction first enlarges radius to R+1 and
  reduces error to ε/2. Fixed-parameter predicates are not identified.

These are verified by the scoped Chapter 3 build and declaration axiom gate.
They do not yet prove pointed extraction, uniqueness, the complete KL sequence
criterion, or any Riemannian convergence bridge.
