# ContDiffOnOne

## 2026-07-10

Added `opNorm_sub_le_of_var`, a reusable operator-norm wrapper around
`variationalSolution_compare_norm`.  It compares two continuous-linear-map
families when their evaluations solve the variational equations along two
central orbits.  In contrast with the chosen `variationalLinearMapAt`
constructor, the statement does not require the auxiliary `M * T < 1`
restriction, so it can be used on the unit-time geodesic phase interval.

Focused verification passed.  The remaining quantitative diagonal-exp work is
geometric: supply the phase linearization bounds and identify the flat
zero-orbit variational family.
