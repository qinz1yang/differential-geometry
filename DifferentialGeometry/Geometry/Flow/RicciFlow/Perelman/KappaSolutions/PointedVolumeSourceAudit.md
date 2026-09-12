# Pointed volume source audit

2026-09-08, independent bounded SOURCE-ONLY review. Read both complete
OpenRestrictionVolume and PointedAsymptoticVolumeRatio sources and notes,
and checked the relevant native POU/overlap, chart-Gram, open-subtype
derivative, measure restriction/comap, countable-cover and ENNReal limit
declarations. The native theorem-workflow skill guided actual-object and
dependency checking. No reviewed source/note was edited. This Markdown-only
record has no Lean-file claim; no Lean/Lake/REPL, artifact, root or commit
operation ran.

## Result

No confirmed mathematical or native-signature defect was found in this
bounded source review. This is NOT a compiler pass or instantiated axiom
audit. The two pending leaves still require the parent's verification DAG.

## Countable gluing and actual restriction

- OpenRestrictionVolume.lean:47-86 uses the actual countable subtype of
  nonempty POU supports, not a finite chart cover of a noncompact manifold.
  The native countability theorem requires sigma-compactness, supplied here.
  The POU sum is one; each weighted integrand vanishes outside the overlap
  because of either POU subordination or the explicit support premise.
  Native overlap equality and lintegral_tsum then legitimately reconstruct
  the chart integral, including infinite values.
- Lines 119-245 retain actual source and extended-target memberships.
  Native chartGram_open compares the canonical restricted metric with the
  ambient metric in the SAME model basis; chartDensity has no extra factor.
  The subtype target lies inside the ambient target. Outside the smaller
  target, membership in the measured image would put the coordinate back
  into that smaller target, so the ambient indicator really vanishes.
  No boundaryless-chart or full-target premise is silently used.
- Lines 252-281 use the actual Lindelof countable chart subcover and native
  Measure.ext_of_biUnion_eq_univ. The local restricted measures agree on
  every measurable test set. Lines 285-301 then use genuine Borel inclusion
  measurable-embedding comap/map laws; the all-sets formula follows from
  measure equality and is not an unsupported nonmeasurable-set extension.

## No misuse of global naturality

PointedAsymptoticVolumeRatio.lean:61-114 first constructs U=F.source and
the actual open image V, derives both subtype sigma-compact instances via
Geometry.isSigmaCompact_of_isOpen, and builds the genuine GLOBAL
e:U Diffeomorph V with PartialDiffeomorph.toOpensDiffeoCross (line 72).
The earlier volumeMeasurePreserving_pullbackMetric is applied to hV and
THIS e at line 92, never to the raw partial map F:M->N. The inverse-image
identity uses e.injective. Native mfderiv_toOpensDiffeoCross at line 102
identifies the true restricted differential with the ambient one.
OpenRestrictionVolume is used on BOTH open domains (lines 107 and 114),
so no missing source/target restriction identity is being hidden inside
the earlier global theorem. The only explicit admitted input here is that
previously authorized global volume-naturality theorem.

## Strict buffer and ENNReal limits

Lines 156-215 use the SAME C, Phi and subsequence for inverse capture and
metric control. The actual preimage set A=F.source intersect F.preimage B
is open; capture plus the actual left/right inverse laws prove F.image A=B
and A is in the fixed compact limit closed ball of radius (1+epsilon)*s.
The strict inequality (1+epsilon)*s<r then puts A in the OPEN radius-r ball
(line 189). No assertion that sphere boundaries have zero volume is needed.

Lines 238-309 use the native denominator omega_n*ofReal(r^n), nonzero and
finite for r>0. With epsilon_j=1/(j+1) and s_j=r/(1+epsilon_j)^2, the capture
radius is r/(1+epsilon_j)<r and the exact multiplier is
ofReal(sqrt((1+epsilon_j)^n)), tending to one. Native ENNReal const_mul at
line 265 uses the NONZERO limiting denominator, so v may equal top;
mul_const at line 279 uses the NONZERO limit one, so the limit-ball volume
may equal top. Both match the actual native disjunctive hypotheses.
The pointwise cross-multiplied inequalities pass to the limit, then the
positive-radius iInf is taken. There is no infimum/limit interchange or
unproved finite-volume assumption. Choosing a separate k0 for each j is
legitimate because hsource bounds every source index uniformly by the SAME v.

The endpoint is exactly the AVR infimum inequality. The separate book
Ricci-sign and noncompact-limit clauses are not proved by these two leaves.
Their stated stronger source-side generality is consistent with this
infimum inequality and is not a claim of arbitrary Ricci-limit preservation.
