# LeviCivita.lean

## 2026-06-13

Moved the local covariant-derivative smoothness producer inside the public
Levi-Civita curvature wrappers whose connection is definitionally
`leviCivitaConnectionOfMetric g`.  Generic `cov` lemmas still keep their
explicit local smoothness hypothesis.

Verification: focused check passed and the module was rebuilt for downstream
signature refresh.  No new `sorry` or `admit`.

## 2026-06-14 metric LC smoothness cleanup

Additional Levi-Civita-specific curvature wrappers now derive the
`leviCivitaConnectionOfMetric` local-smoothness proof internally.  The remaining
`rm04PairSymm_ofLC` hypothesis is intentionally generic: it is stated for an
arbitrary `cov` with an `IsLeviCivita cov g` proof, while the concrete metric
connection wrapper below it is already hypothesis-free.

Verification passed for the edited file.
