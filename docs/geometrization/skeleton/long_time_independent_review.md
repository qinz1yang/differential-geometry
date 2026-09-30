# Independent review of the selected-flow integration

Reviewer: hyperbolic/cusp subtask, separate from the author of the root
integration. This is a mathematical statement review, not proof of the
remaining producer. Blueprint207 is the source of record.

## Findings in the first draft

**Parameter order needed correction.** The first draft quantified
`exists A, forall w₀, exists δ F, ...` and promised the same derivative-control
function on all sufficiently late slices. TCF06 (master207A.tex31801–31847)
uses a different order: finite K, one fixed admissible surgery flow, a proposed
bad sequence, one A from LC89 absorbing finite initial sequence segments,
static threshold w₀(K,A), and then a sufficiently late sequence index.
LAU's normalization/dependency discussion (31966–32003) explicitly forbids
changing surgery accuracy after the future collapse tolerance and does not
extract a common time for infinitely many individual thresholds T_K(w).
The initial stronger ordering was not source-supported.

**Closed nonnegative components must be retained separately.** TCF05–TCF06
separate closed nonnegative-curvature components before LC89 and restore their
recognized graph presentations. A dichotomy with only hyperbolic and tested
collapsed components would need another argument to force these components
through the finite-curvature-scale tests. The mathematical interface should
include the actual nonnegative metric/closed-component recognition alternative,
or an already supplied graph presentation for those components.

**Initial scalar normalization needed an explicit adapter.** The fixed
coefficient 3/[4(t+1/4)] in IMS09/IAU03 uses normalized initial data. A theorem
beginning with an arbitrary initial smooth metric may not silently assert that
same scalar bound. The elementary area comparison is valid with t+c whenever
T+c>0; c can record the positive scalar lower-bound shift for the initial
metric, while the asymptotic metric normalization remains t⁻¹g(t). This is a
source-normalization adapter, not proof that arbitrary initial data satisfy the
normalized scalar estimate verbatim.

These findings were sent to the root author before the skeleton was finalized.

## Revised signature reviewed

The revised `hasLateSequenceTests` fixes F before quantifying over a sequence
of actual `RegularSlice F.observation` records, with j < time(slices j) and
nonempty actual slice carriers. It then chooses A before any static tolerance,
and gives one eventual sequence threshold for each tolerance. This matches
TCF06/LC89's sequence method and is sufficient for a real contradiction proof
against arbitrarily late bad slices. It does not assert a universal A for all
continuous times.

The final area obstruction is `hasExteriorAreaObstructionAfter F D t₀`. It
uses the SAME F.observation to define `postStage` and `postMetric`, the actual
post-event stage and physical metric at every nonnegative real time. It
requires prescribed embedded exterior minimizers at all t≥T and defines A
as `exteriorDiskArea F.observation W T γ`, the actual infimum of inherited
Riemannian disk area on those carriers. It supplies a positive c and the
strict bound 3A/[4(t+c)]−π, whole-half-line continuity and a smooth upper
barrier at every contact. Nonnegativity is proved from the actual infimum.
The loops γ exist only after T, with T≥t₀ and the selected slice time t₀>0;
no loop on an empty earlier carrier is required. The exact reconstructed
seam map and every source basepoint remain in the failure premise. The
root uses `incompressible_of_shifted_area_barriers` on this specific area
function. This corrects both the arbitrary numerical-function interface
and the false fixed-normalization implication.

The broad selected-flow producer remains a `sorry` theorem combining global
flow/profile choice, thick persistence, actual thin tests, and the geometric
area producer. Its common-neck-accuracy field is a precise assertion about
actual history records and one δ, but is not by itself a definition or proof
of all analytic admissibility hypotheses. Those are obligations inside that
large producer. No claim of a separate Lean implementation of HPI or IMS is
licensed by its statement.

The final `HyperbolicOrCollapsed.nonnegative` constructor was inspected. It
retains the actual induced cut metric, empty boundary and sectional curvature
bounded below by zero. The real downstream match uses the separate
`exists_rawGraphPresentation_of_nonnegative` leaf. Thus the nonnegative
branch is not forced into LC89 finite-radius tests. The classifier proof
itself is a source-qualified skeleton leaf, not a newly verified theorem.

## RegularSlice and common-time review

`RegularSlice` records a strictly positive non-event time, the exact finite
observation prefix, and a strict separation from that prefix's last event. Its
stage and metric are computed from that same observation. It does not choose
an unrelated isomorphic carrier or unrelated initial marking. The normalized
metric is t⁻¹g(t); its curvature-one variant is (4t)⁻¹g(t).

The finite-predicate common-time proof chooses maxima of time thresholds and
uses the explicitly required arbitrarily-late nonempty-slice hypothesis. For
an empty finite family it retains only the user's time bound. This matches
LP04/LAU01. The separate empty-slice alternative is not mistaken for a
nonempty late choice and does not assert finite-time extinction. No issue was
found in those statements or their finite-threshold proof.

## Remaining limits

This review checks quantifier direction and the geometric/analytic meaning of
the exported data, not the whole source proof or the adequacy of every future
subdivision of the coarse producer. In particular the eventual same-flow
HPI/TCF/IMS implementation still must retain actual boundary markings,
physical versus normalized units, all-ball derivative estimates, regularity,
compact minimizing carriers through each surgery, and source-qualified
foundations. The actual time-dependent exterior sets and loops are now concrete and tied
to the same observation tower, but this projection does not yet export their
prescribed-meridian homotopy, kernel preservation, persistent cusp embedding,
compact mean-convex exterior, or the common avoiding carrier. Those geometric
controls remain inside the coarse existence producer and must be exposed when
its proof is subdivided. The existence of the actual minimum and its barriers
is still asserted by a `sorry` producer, not proved by this review.

## Final inspected files

The final review read `LongTime/LateDecomposition.lean`,
`LongTime/ExteriorDiskFlow.lean`, `Collapse/TorusDecomposition.lean` and the
nonnegative classifier signature after the above corrections. The six owned
hyperbolic/minimal-area leaves compile; the root records whole-library and
end-to-end assembly compilation separately. No further owned code changes are
planned after this review.
