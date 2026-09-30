# Independent review of MC13's pointed precompactness proof

This review read the full statements and proofs in DistanceMatrixLimit.lean,
CountableNetLabels.lean, and PointedPrecompactness.lean, independently of their
authors. It also read the complete ofPairedNets constructor, the defining fields
of PointedBallApprox and PointedGHConverges, and blueprint master207A.tex
lines 1312–1446, including the eventual-net proof. No mathematical defect or
statement mismatch was found in this scope. This is a scoped mathematical
review, not an audit of every imported Mathlib theorem or of all Chapter 3.

## Contracts and corner cases checked

- The input quantifiers are exactly `∀ R > 0, ∀ η > 0, ∃ N I, ∀ n ≥ I`.
  Both bounds can depend on radius and accuracy; no common threshold for
  infinitely many scales is assumed. Centers belong to the indicated closed
  source ball, cardinality is bounded by N, and coverage includes its boundary.
- Source completeness and properness are absent intentionally. This matches
  the blueprint's eventual-net refinement; it is not an unsupported weakening
  of the separate BBI proper-space specialization. Source nonemptiness follows
  from the supplied basepoints. No length, curvature, or dimension result is
  hidden in the conclusion.
- Before each level's threshold the chosen finite set is empty and every
  padded label is the basepoint. Thus its radial bound holds at all indices
  without inventing early net coverage. Fin (N+1) handles empty finite sets and
  N=0 without selecting a nonexistent point. Repeated labels are allowed.
- A compact countable product extracts one strictly increasing subsequence
  for all pairwise distances. The bound is allowed to depend on the pair.
  Each separate net threshold transfers along this same subsequence by
  StrictMono.tendsto_atTop; no second incompatible subsequence is selected.
- The limiting object is a pseudometric until Mathlib's separated completion
  is taken. Distinct labels at limiting distance zero are identified there.
  Neither injectivity of the label map nor density of source labels in each
  original source is used. Density is used only in the constructed completion.
- For a target label with radius strictly below m+1, convergence eventually
  places its source representatives inside that source ball. Finite frequent
  selection passes the non-strict net bound to a limit center. The finite union
  of closed net balls is closed, so this coverage extends from dense labels
  throughout the target open ball. Closed target balls are then covered using
  a strictly larger level radius.
- Properness is proved for arbitrary target centers and radii, not only
  basepoint balls. Ambient finite nets suffice for Mathlib total boundedness;
  completeness of each closed ball follows from completeness of the target.
  There is no omitted factor-two conversion to an internal net, because that
  conversion is unnecessary for the actual total-boundedness interface.
- At a requested radius R and error ε, the level is chosen once with
  R < m+1 and η = 1/(m+1) < ε/4. This cofinal scale sequence replaces the
  blueprint's dyadic errors without changing any theorem quantifier. The
  subsequence and target were fixed before this choice. The finite matrix
  error is eventually less than η simultaneously for all needed label pairs.
- The actual map fixes the basepoint by a special label choice. Distortion is
  less than 3η. For target radius at most R−ε, its nearby label's source point
  has radius less than R−ε+2η < R. That point is a legitimate preimage in the
  actual closed source ball. Its selected map label may differ from the first
  label; the second matrix estimate still bounds coverage by less than 3η.
  Thus coverage does not presume that labels are preserved or distinct.
- The generic matrix theorem permits arbitrary countable label universes and
  varying source carriers. The final extraction uses a particular small label
  type, Option (Σ m, Fin (N m+1)), so its small target `Y : Type` is justified
  even for source spaces in an arbitrary fixed universe. No source carrier
  identification is assumed. Completeness of Y is an explicit conjunct of
  PointedGHConverges, in addition to the separately returned ProperSpace Y.

## Evidence and source boundary

The existing source comparison in reference_checks_revision61.md was reread.
It records BBI Theorem 7.4.15, printed page 264/PDF page 279, and Theorem 8.1.10
and its outline, printed pages 274–275/PDF pages 289–290, and the retained
July 6, 2024 author errata. The arbitrary-source eventual-net extension is the
blueprint's proved adaptation, not a stronger theorem attributed verbatim to
BBI. This independent review reuses that source and errata check; it did not
freshly reopen the archived book or remote errata.

On Lean 4.35.0-rc3 with Mathlib
c55e6e786f49471c72fbddbec5415808896aec1e, the targeted
PointedPrecompactness build passed (1,578 jobs including cached dependencies).
A successful stdin check inspected the final universe-polymorphic statement
and axiom closures of all three pointed extraction theorems, both matrix
extraction theorems, and the countable-label producer. Each closure was exactly
propext, Classical.choice, and Quot.sound. No source edits were needed.

The reviewed source SHA-256 values are:

| File | SHA-256 |
| --- | --- |
| DistanceMatrixLimit.lean | df83a6224e9e00a39b5913fd4a3947bbcd5a8994687c89ab0568b63824bcf16b |
| CountableNetLabels.lean | 09261a99db474f2d83eae761476e6a934ff9b1b6b4cb8ba9e7a4aec145245ae7 |
| PointedPrecompactness.lean | 96ce97e82b2d132641fe43c27900c1e560bcceac06af5c0bca813a151bd1fa4d |
| PairedNets.lean | bd3023f5ca5a2e97f1ad017d12022514de7d608c14a021b4aae6caf611790eee |
| master207A.tex | 277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b |

The geometric production of the finite nets remains a separate consumer-facing
obligation. This theorem does not prove Alexandrov comparison, packing bounds
from curvature, or compatibility with the full migrating Poincare library.
