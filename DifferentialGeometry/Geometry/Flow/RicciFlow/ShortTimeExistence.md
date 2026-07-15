# ShortTimeExistence audit

## 2026-07-13 latest-progress resync

After the completed branch-alignment merge `d842bedee`, the two newer committed
updates from our `short-time-existence` branch (`17de115b1` and `2a2ce366e`)
were merged into the alignment worktree.  The source merge was conflict-free.
The resulting tensor-API compatibility points were repaired in nine consumers
using public `Tensor0SSpace` evaluation lemmas, without changing theorem
statements or adding assumptions.

The resynced tree passes the latest targeted C4/spectral/entropy build, the
explicit 9,924-job Hamilton consumer, and the 10,258-job default full build.
The headline axiom audit remains exactly `[propext, Classical.choice,
Quot.sound]`.  Thus the short-time-existence theorem remains 100% proved, its
dedicated machinery remains 100% integrated, and the latest progress resync is
100% verified.  HCG endpoint status is separate: the conditional compactness
endpoint and textbook B1 theorem remain 0%, while their shared machinery is
tracked in `HCGCompactness/PROJECT_MAP.md`.

## 2026-07-12 corrected branch-alignment audit

This section supersedes the `main`-based integration route recorded below on 2026-07-10. The
actual merge preparation aligns the current local short-time-existence progress
(`e5d37bce`) with qinz's short-time-existence semantic branch (`8b8814e2`) in the isolated
`codex/short-time-existence-align` worktree. It is not an attempt to merge either branch into
`main`.

The headline `ShortTimeExistence.lean` theorem is source-complete and its focused check passed;
its axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`. The large upstream
dependency `CurvatureCoefficientDifferenceJetTower.lean` is also source-verified after replacing
an elaboration-heavy generic congruence with the existing double-frame trace-independence route.
The direct `CinftyLimitGlue` consumer passed focused verification and a targeted module build, and
the explicit downstream `HamiltonPositiveRicci` target completed all 9,924 jobs after the merged
tensor API compatibility repairs.  Its existing endpoint `sorry`s are independent of this merge.
The default project build also completed all 10,258 jobs after removing an unused duplicate
DeTurck short-time endpoint that collided with the canonical proved producer; the declaration
index contains 24,613 declarations.

The final tree is not globally sorry-free: it contains 37 actual `sorry`/`admit` proof lines,
seven more than the local-progress parent, distributed across six separate Sobolev, spectral,
and curvature auxiliary-frontier files.  None is in the headline proof's axiom closure, as the
checked axiom audit above confirms.

Honest progress: the headline theorem itself is proved (100%); its dedicated construction
machinery is integration-verified (100%); alignment/merge preparation is 100% through focused,
targeted-consumer, downstream-Hamilton, and default-root verification. The merge commit carrying
this audit completes the branch alignment (100%). This is separate from Hamilton
positive-Ricci or HCG compactness endpoint completion, whose existing theorem frontiers are not
advanced merely by this successful integration build.

## 2026-06-05 exhaustive source audit

Scope: the headline `ShortTimeExistence.lean`, the short-time assembly/flow
directories, the direct DeTurck and Pullback files used by the headline, and the
Hamilton consumer adapter.

What was learned:

- `ricci_flow_short_time_existence` returns a global
  `Real -> SmoothRiemannianMetric I M` family.  The chart-Gram hypotheses are
  coordinate read-offs from that global family, not independent local chart data.
- The actual proof-body `sorry`s in the short-time dependency surface are the
  DeTurck-Ricci parabolic short-time theorem and the Weyl/on-diagonal spectral
  analytic input.
- The old comment in `ShortTimeFlow/ConjugatingFlowProperties.lean` about a
  labeled flow-continuity `sorry` is not an active proof placeholder in the
  current source.
- A direct source check of `Pullback/Defs.lean` initially failed at the
  bilinear-pullback smoothness proof because the `flip` smoothness route was
  using the continuous-linear-map seminormed instance instead of the normed
  instance expected by `ContDiff`.  That was repaired in `Pullback/Defs.lean`.

Verification passed for the checked source files in this audit and for the
Hamilton consumer.  No target `.olean` refresh was run because the project lock
script is absent in this checkout and an existing Lake server is active; the
claim here is source-level focused verification.

## 2026-07-10 upstream completion and merge audit

Audited upstream `qinz1yang/differential-geometry` at
`short-time-existence` tip `9c01f29f` against upstream `main`.

### Theorem status

- `ricci_flow_short_time_existence` is stated as a genuine existence theorem:
  from a smooth initial Riemannian metric on a compact boundaryless manifold it
  constructs `T > 0` and a metric family with `g 0 = g0`, jointly smooth
  chart-Gram entries on `[0,T)`, and the Ricci-flow equation (as a right
  derivative at `t = 0`).
- The headline proof calls the concrete DeTurck solution producer
  `deTurckRicci_solution_with_jointReg`, the jointly smooth conjugating-flow
  producer, pullback naturality/regularity, and the endpoint derivative lemma.
  It does not assume a Ricci-flow solution or a proposition definitionally
  equivalent to its conclusion.
- The short-time-specific source surface has no explicit `sorry`.  The
  declaration has an embedded `#print axioms` audit intended to show only
  `propext`, `Classical.choice`, and `Quot.sound`.
- This does not make the whole branch sorry-free.  The tip still has six
  explicit `sorry` bodies: four in `Tensor/Exterior/Basic.lean` and two in
  `Tensor/RSTensor/Derivation/NablaOnTensors.lean`.  The latter module is in the
  import closure, but the reported axiom audit says the headline does not use
  those two declarations transitively.
- GitHub records no CI/status checks for the tip.  An independent clean
  targeted build in an isolated worktree produced 166 branch-local modules
  without a Lean error before hitting the audit's 20-minute performance wall.
  The headline import closure contains 1,331 local modules, so this is an
  incomplete verification result, not a pass.  A completed clean build remains
  the merge gate.

Honest progress: the theorem on the upstream branch is source-complete (100% as
a stated/proved theorem, pending the independent clean-build gate); its
dedicated upstream machinery is approximately 100%.  The theorem on current
`main` remains dependent on deferred inputs, so the completed theorem is 0%
integrated into `main`.  Merge preparation is approximately 75% (source,
soundness-shape, history, and conflict audits done, and the integration
worktree created; clean verification and semantic replay remain).  The actual
merge is 0%.

### Merge audit

- The upstream branch and current `main` have diverged substantially: the
  branch has 1,244 unique commits and `main` has 58 unique commits from their
  merge base.
- The branch delta is 1,557 files (1,552 Lean files), approximately 304k added
  and 129k deleted lines.  Much of this is library-wide comment/docstring
  stripping and unrelated cleanup, not short-time-existence mathematics.
- A synthetic merge into current `main` reports 47 conflicted paths, including
  `ShortTimeExistence.lean` and most of the short-time/DeTurck/flow proof path.
- PR #56 was closed unmerged shortly after creation and has no CI result.  Its
  head predates the audited branch tip by one cleanup commit.
- The local working branch is a different divergent history and contains
  unrelated in-flight edits.  Do not merge or switch it in place.

### Required integration route

Do not raw-merge the upstream branch.  Create a clean integration worktree from
current upstream `main`, preserve `main` versions by default, and replay the
semantic short-time producer chain in dependency order.  In particular, reject
the branch-wide comment stripping, unrelated theorem deletions, regenerated
root-import churn, and the two unrelated tensor files that still contain
`sorry`.  After each producer layer, run a narrow build; finish with the
headline module, its embedded axiom audit, the root import, and a branch-wide
`sorry` inventory before opening a draft merge PR.

Replay in five layers: (1) calculus extensions and closed-slab/joint-smooth
time-dependent flow; (2) the Sobolev/spectral/semigroup/maximal-regularity
producers actually consumed by DeTurck; (3) the concrete DeTurck solution and
joint chart regularity; (4) conjugating diffeomorphisms, pullback/naturality,
the interior equation, and the `t = 0` endpoint; (5) the headline, axiom audit,
consumers, root import, and documentation.  Stop rather than widening the patch
if a layer requires an unrelated deletion, depends on one of the six residual
`sorry` declarations, or cannot preserve the current `main` API.

The documentation-preserving baseline is `62d33e61`, the parent of the
library-wide comment-strip commit `2e920d67`.  It produces 19 synthetic merge
conflicts against `main`, compared with 47 at the audited tip.  The completed
proof still requires the later semantic work (481 commits follow the strip
commit), so this baseline is not itself a completed theorem.  Use it only to
preserve infrastructure and documentation, then replay or consolidate later
proof changes while skipping `2e920d67` and the final library-wide cleanup
commit `9c01f29f`.

Comment-stripped/whitespace-normalized comparison reduces the apparent
1,532-file post-baseline delta to 53 semantically modified files, 111 new files,
and 20 deleted files.  Intersecting that set with the headline's 1,331-module
local import closure leaves 154 relevant files: 46 modified and 108 new, with
no relevant deletions.  The replay can therefore be zero-deletion.  Use
`c3f8a482` (the parent of the final cleanup) as the completed proof source; the
headline is unchanged by `9c01f29f`.

Including the pre-baseline infrastructure absent from current `main`, the full
normalized headline-closure delta is 344 files: 75 semantically modified and
269 new, with no relevant deletions.  The 154-file count above is only the
post-baseline portion.  The integration is therefore a layered medium-size
port, not a single theorem patch.
