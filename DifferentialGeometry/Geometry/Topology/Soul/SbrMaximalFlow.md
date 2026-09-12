# SbrMaximalFlow.lean

Verified 2026-09-08 in the dev checkout. Actual finite ascent curves are glued by proved uniqueness and extended continuously to an actual maximum-level point. Full closed-interval calibration and preterminal normalized right derivatives are produced without a supplied flow or compatible family.

Empty focused output: 14.8s. Lint-clean named build: 17.2s.
Fresh external public axiom audit: 13s; all 1 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrMaximalFlow-result2.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

2026-09-08 parent source work. Claim
`18ccafb1-6977-4fb8-8507-5e48e9c9002d` retained. SOURCE-ONLY while
Chapter23 owns the compiler window. No focused check, named build or
public axiom audit has run. Pending imports are themselves source-only.

The public producer `exists_maximal_normalized_ascent_curve` addresses
the existence assertion of book `thm:sbr-maximal-flow`, master05a.tex
around lines 7895-7926. It constructs the curve from SbrFiniteFlow's actual
finite ascent curves, not from a supplied compatible family or flow.
SbrFlowUniqueness proves that all finite curves with the same start agree
on their overlapping closed intervals.

At a time s below m, select the finite curve with upper endpoint (s+m)/2.
Overlap agreement proves that this selected function agrees with every
finite curve throughout the latter's closed interval. Consequently the
selected function inherits continuity, the actual normalized right
manifold derivative, and the finite-interval Lipschitz estimates locally.
The initial point, exact levels and compact containment are retained.

Fixed-point distance comparison, instantiated with each actual finite
curve and any point of maximum level, gives antitonicity on the entire
half-open interval. SbrMaxLevelLimit then constructs its maximum-level
point and continuous extension by compactness and monotonicity. No limit,
Cauchy condition, compatible-family input or terminal point is assumed.
Changing the function at m leaves every preterminal right derivative
unchanged because the two functions agree on a right neighborhood there.

The endpoint includes continuity and calibration on the full closed
interval, nonzero actual generalized gradient and normalized right
derivative before m, and the quantitative Lipschitz estimate on every
strictly smaller closed interval. Full-interval uniqueness is supplied by
SbrFlowUniqueness, since the displayed derivative and calibration are its
actual inputs. Retraction maps, semigroup laws, joint continuity and
Busemann-level surjectivity are subsequent obligations.

Verification order: SbrFiniteFlow, SbrFlowUniqueness and SbrMaxLevelLimit
must be checked and refreshed first. The present source is not a verified
maximum-flow theorem until its own triple and dependency audit pass.

The bounded read-only source review at
E:/lean-tools/soul-audits-20260907/SbrMaximalFlow-source-review.md found no
concrete mismatch in construction, overlap, terminal extension or retained
derivatives. Reviewed source SHA256:
BE6FEBD993F01BE86C41A7B5F445C9FF982BD5AB91EE96F851CEC1B64AE44E60.
This is source review only; the verification boundary above is unchanged.
