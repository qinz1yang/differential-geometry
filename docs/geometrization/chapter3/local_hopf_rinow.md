# Local compact balls and controlled minimizing segments: AC01 and ALG05

Files:

- `DifferentialGeometry/Topology/MetricSpace/LocalHopfRinow.lean`
- `DifferentialGeometry/Topology/MetricSpace/CompactMinimizingCurve.lean`

This completes AC01 and the metric compactness/geodesic-production step of
ALG05. It does not prove ALG05's Alexandrov comparison conclusion.

## Exact hypotheses and conclusions

All spaces use their finite ambient `MetricSpace` distance. The length-space
hypothesis is the already established explicit interface: for every pair
`a,b` and every real `epsilon>0`, there is a continuous curve
`c : [0,1] -> X`, with endpoints `a,b`, whose actual partition variation
`eVariationOn c univ` is strictly less than `dist(a,b)+epsilon`.
This is a hypothesis about actual curves and Mathlib's variation; it does
not assume compact balls, minimizing paths, or an unspecified length function.

1. **Complete buffer.**
   `Metric.isCompact_closedBall_of_complete_buffer` assumes `L>0`, local
   compactness of the open subtype `B(p,L)`, and completeness of the set
   `closedBall p L` with its ambient uniformity. Every closed `r`-ball at
   `p`, for `r<L`, is compact in `X`. There is **no ambient completeness or
   ambient local compactness assumption**. The conclusion includes zero and
   negative radii, and does not assert compactness at `r=L`.
2. **AC01 compactness.**
   `Metric.isCompact_closedBall_of_locallyCompact_ball` is the corollary
   where `X` is complete. It retains local compactness only on `B(p,L)`.
3. **Controlled closed-ball joins.**
   `Metric.exists_metric_segment_in_closedBall_of_complete_buffer` assumes
   local compactness of `B(p,L)`, completeness of the closed `L`-ball,
   `2*r<L`, and `a,b` in the closed `r`-ball. It produces a continuous
   `f : [0,1] -> X`, with exact endpoints `a,b`, image in the closed `2*r`-ball,
   and the exact identity

   `dist(f(s),f(t)) = dist(a,b) * dist(s,t)` for every `s,t`.

   This is a constant-speed ambient minimizing segment. The endpoint
   hypotheses force `r>=0`; no extra positive-radius hypothesis is imposed.
   Coincident endpoints give a constant segment. The theorem makes no
   uniqueness or geodesic-extension assertion.
4. **AC01 geodesics.**
   `Metric.exists_metric_segment_in_closedBall_of_locallyCompact_ball`
   supplies the same conclusion when `X` is complete. These two AC01
   corollaries are actual applications of the weaker complete-buffer results.
5. **ALG05 open-ball joins.**
   `Metric.exists_metric_segment_in_ball_of_complete_buffer` assumes `X`
   locally compact, the same explicit length property, `r>0`, and completeness
   of the closed `3*r`-ball at `p`. For `a,b` in the **open** `r`-ball it
   constructs an exact ambient minimizing segment lying in the **open**
   `2*r`-ball. No completeness of `X` is used.
6. **Moving the center.**
   `Metric.isComplete_closedBall_of_add_dist_le` transfers completeness
   from `closedBall o L` to `closedBall p r` under
   `dist(p,o)+r <= L`. No length or local compactness hypothesis is needed.
   `Metric.exists_metric_segment_in_ball_of_recentered_complete_buffer`
   composes this with step 5 under `dist(p,o)+3*r <= L`.
   This is the join interface needed after ALG05 changes center to `p_*`.
7. **Endpoint-distance control.**
   `Metric.dist_center_le_of_metric_segment` proves for any exact segment

   `dist(f(t),p) <= (dist(a,p)+dist(b,p)+dist(a,b))/2`.

   This general estimate yields both the closed and strict open bounds.
8. **Compact minimizing-curve producer.**
   `Metric.exists_metric_segment_of_compact_arbitrarily_short_curves`
   assumes a fixed compact subset `K` and, for the specified endpoints,
   continuous curves of variation less than `dist(a,b)+epsilon` inside
   `K` for every positive epsilon. It constructs an exact segment inside
   that same `K`. Neither the ambient space nor the restricted metric on
   `K` is assumed to be a length space. No ambient completeness or local
   compactness is assumed in this lemma.
9. **Three-piece variation.**
   `Metric.edist_add_edist_add_edist_le_eVariationOn` bounds the three
   consecutive distances through parameters `0 <= s <= t <= 1` by the
   actual variation of any curve. Continuity and finite variation are not
   needed for this extended-real inequality.

## Proof audit

The compact-radius proof localizes the existing global Hopf--Rinow proof.
A compact neighborhood in the open subtype maps to a compact ambient
neighborhood because the subtype inclusion is open and continuous. A finite
cover of a compact smaller ball then gives a compact ambient neighborhood
of that ball. Radial trimming of actual near-short curves puts a slightly
larger closed ball inside this neighborhood, with the enlargement chosen
strictly smaller than the remaining margin to `L`.

The set of positive compact radii less than `L` is nonempty and bounded
above. If its supremum were less than `L`, radial trimming and finite nets
would make the supremum ball totally bounded. This ball is a closed subset
of the complete buffer, so it is complete and hence compact. The preceding
enlargement contradicts the supremum. This proves compactness at every
strictly smaller radius without assuming compactness of the boundary buffer.

The compact minimizing-curve proof deliberately avoids an arbitrary-curve
arclength-reparameterization dependency. On each near-short continuous
curve, the intermediate value theorem selects a point at radial distance
`t*dist(a,b)` from `a`; endpoint parameters are fixed explicitly. The
three-piece variation inequality, in either order of the selected curve
parameters, proves

`dist(g_n(s),g_n(t)) <= dist(a,b)*dist(s,t) + epsilon_n`.

The radial selections need not be monotone or continuous. One fixed
ultrafilter refining `atTop` gives pointwise limits in `K` at every parameter.
Taking limits in the displayed inequalities gives a genuine Lipschitz
map with exact endpoints. The existing endpoint-saturating Lipschitz lemma
then gives equality in every pairwise distance. Using the same ultrafilter
for all parameters is essential; unrelated accumulation points would not
justify this limit inequality.

For local joins choose `2*r < R < L`. Given any requested epsilon, use a
near-short curve with error at most both epsilon and `R-2*r`. The two-piece
variation estimate and the two endpoint-to-center triangle inequalities
place the whole curve inside `closedBall p R`, which is now known compact.
The compact minimizing-curve producer supplies an exact segment; the
endpoint-distance estimate sharpens its range to the closed `2*r`-ball.
Strict endpoint radii give the open `2*r` conclusion used in ALG05.

No closed restricted ball is asserted to be a length space. Every variation,
endpoint distance, and segment distance is measured in the ambient metric.
No curvature, dimension, Riemannian, PC, or local-to-global comparison
assumption enters these metric proofs.

## Sources and version identity

- Blueprint `master207A.tex`, AC01, label
  `lem:alexandrov-local-balls`, lines 2102--2144; ALG05, label
  `thm:alexandrov-written-coarse-local-globalization`, lines 7486--7537.
  Both statements and proofs were reopened, including the complete-buffer,
  shifted-center, and strict open-ball clauses. Blueprint SHA-256:
  `277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b`.
- BBI, *A Course in Metric Geometry*, archived AMS 2001 English edition:
  Proposition 2.5.19 and Corollary 2.5.20, Definition 2.5.21,
  Proposition 2.5.22 and its full proof, Theorem 2.5.23 and adjacent
  qualifications, printed 49--51 / PDF 64--66, reopened for this work.
  The actual book calls 2.5.22 a **Proposition**, at printed 49--50 / PDF
  64--65; AC01's historical citation calls it a theorem and gives a later
  page range. The mathematical compact-radius proof is the one used here.
  The source is a global theorem; its localized, complete-buffer version
  is proved in Lean, not silently imported under weaker hypotheses.
  Archive SHA-256:
  `4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971`.
- Retained author errata dated July 6, 2024, PDF 2--4, reopened.
  Finite-distance qualifications for Sections 2.4--2.5 are enforced by
  `MetricSpace`. No separate correction of Proposition 2.5.22 or Theorem
  2.5.23 occurs there. The corrections to curve compactness and naturally
  parameterized geodesics are not bypassed by claiming those corrected
  statements as proved; the radial-selection argument above is an explicit
  alternative proof of the needed compact minimizing-segment statement.
  Errata SHA-256:
  `68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e`.
  This reuses the retained author-errata check, not a fresh remote retrieval.

Source comparison and prior identities remain in the existing
`hopf_rinow.md`, `reference_checks_revision58.md`,
`reference_checks_revision59.md`, `reference_checks_revision68.md`, and
`reference_checks_revision140.md`. The archived sources, blueprint and its
historical inventories were not modified. The active manifest and coverage
map record this new proved scope.

## Remaining boundary

AC01 is proved. Only ALG05's compactness and controlled-join input is proved
here. Its point-selection argument, short-hinge improvement, Alexandrov
comparison and the subsequent ambient comparison producer remain separate.
The full MC18/AC41 geometric-input theorem and the full migrated PC root
are not claimed complete. A source manifold must still be connected to
the explicit ambient metric and near-short-curve interface.

## Verification

The combined gate passed for all 42 new modules (2730 Lake jobs), auditing
443 owned declarations including all 17 declarations in these two new files.
Every axiom closure is contained in `propext`, `Classical.choice`, and
`Quot.sound`. No admissions or new mathematical axioms occur. Results and
source hashes are recorded in `evidence/verification.json` and its build
and all-declaration axiom logs. The final review also checks
zero radius, coincident endpoints, arbitrary ambient incompleteness in the
elaborated signatures, strict versus closed range control, and ALG05's
shifted-center numerical margin. These are scoped checks of the new
metric development, not a full PC-root or blueprint mathematical audit.
The final self-review is `local_hopf_rinow_review.md`; its three compiled
applications passed, including the exact ALG05 shifted-center constants.

The required blueprint static audit was rerun. It stops in the historical
revision127 source-hash check because that inventory retains the archive's
former absolute path. The failure is recorded in
`evidence/blueprint_static_local_hopf_rinow.log`; no source hash assertion
was bypassed and no successful blueprint-audit result is claimed. This
external path issue did not affect the completed Lean build or axiom audit.
