# AC28 finite hierarchy and maximal packet selection

Eleven public theorems and one definition prove the finite selection portion
of AC28. Actual continuous almost-short curves give distinct points at any
positive scale. AC25 then gives a rank-one packet whose two anchors and
balanced center all lie in the requested nonempty open set O. This seed needs
no comparison or completeness.

`pairedChartQuality n k` is 200^k/(400*(n+1)*200^(n+1)), exactly the blueprint
quality written without integer exponents. Its reciprocal form
1/(400*(n+1)*200^(n+1-k)) for k<=n+1 is proved. Positivity, monotonicity,
the exact factor-200 successor relation, top value, and rank quality bounds
are all kernel-checked. No tolerance or normalization has been changed.

`exists_maximal_paired_rank` assumes the same explicit curve property,
comparison on Omega, nonempty open O contained in Omega, local complete
closed balls at points of Omega, and dimH(Omega)<=n with n>=1. It returns
1<=m<=n, an actual point q in O, its actual Fin(m)-indexed anchors in Omega,
a quality-tau_m packet at q, and exclusion of EVERY quality-tau_(m+1) packet
centered anywhere in O with anchors in Omega. The latter uses Option(Fin m)
indices, equivalent to Fin(m+1) by proved reindexing. The point and anchor
family are chosen once before any smaller working neighborhood or chart.

The maximal rank is a bounded natural maximum. Every admissible positive
rank <=n+1 is bounded by n using the proved pointwise packet dimension theorem;
the next rank is in the same finite range. No arbitrary quality improvement,
regular point/tangent theorem, stratification or approximate comparison is
asserted. AC28's final centered chart and common distortion are not yet claimed
at this checkpoint; AC27 is available for that remaining assembly.

Blueprint207A AC28's full proof (3442–3515) and revision66 were reread. BGP1992
English Remark6.9, printed22/PDF23, was freshly reopened: it motivates a finite
rank-dependent hierarchy but also discusses approximate comparison and
stratification, neither imported here. The explicit exact-comparison constants
are project proofs. The unchanged BGP/BBI author-errata checks are reused.
Earlier mathematical leaves, blueprint207 and the PC migration boundary are
preserved.
