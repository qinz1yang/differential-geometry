# Chapter25Entropy

Owner: Chapter25 task01a07c8d-49fa-7373-9948-022395d0119a.
Scope: Chapter25 arguments in book order; earlier integration remains separate.

CURRENT ACCEPTED 2026-09-10 20:59UTC: saved check5 (22.63s), named build3
(33.64s), fresh15-public axioms (19.61s), exact4-endpoint frontier (30.53s),
unchanged Chapter25Theorems regression check3 (25.05s). Frozen receipt:
E:/lean-tools/chapter25-book-20260910/book-noncollapse-completion.json.
There are ZERO own Chapter25 admissions in this file and THREE earlier ones.
The additional local Bishop admission is in BookLocalVolumeDoubling.

Exact open frontiers: local_entropy_volume -> local_volume_doubling;
strong_scalar_no_local_collapsing -> mu_monotone, mu_compact_scale_lower;
spatial_no_local_collapsing -> those three inputs;
noncollapse_and_metric_injectivity -> those three plus local_metric_injectivity.
All other proof dependencies of these four endpoints are checked. The earlier
mu_sobolev_relaxation, cutoff_entropy_doubling and parabolic consumer remain
standard-only. The full compact-slab and exact3^n dyadic producers are also
standard-only. Current counts:5/39 standard-only,3 conditional,31 own open.

Native bridge details: rewrite SolutionOn.scalar and SolutionFamily.scalar
explicitly; use the exact finrank(TangentSpace)=finrank(E) equality. The Ricci
quadratic bound uses Geometry.Curvature.vec2 explicitly, avoiding shadowed
short-name unfolding. scalar_le_of_spatial_rm is in the Perelman namespace,
not FlowMetricBall. No public mathematical hypothesis was changed.

Next book target: noncollapse_passes_to_limit. Current ownership and compiler
window remain in WORKING_STATUS.md. The following paragraphs are historical
preparation and the earlier accepted relaxation/cutoff checkpoint.

2026-09-10 20:25UTC SOURCE-ONLY follow-up: local_entropy_volume now has the
book's exact composition proof using BookLocalVolumeDoubling. The latter
exposes one missing earlier local Bishop comparison input. This follow-up
has not been checked; acceptance counts below remain the frozen prior batch.
Current source claim c3bef7f9; Chapter23 owns the compiler until explicit
handback. A fresh axiom audit must classify local_entropy_volume conditional.

20:33UTC source continuation: spatial_no_local_collapsing now follows the
book directly. CompactSlabVolume provides the full prescribed [0,T/2] slab;
the late branch composes initial compact-scale mu, entropy monotonicity,
weak/smooth relaxation, and local_entropy_volume. Actual pointwise tensor
contraction bounds supply a=b=n^2 in the native norm convention. The old
dependency on the unproved strong_scalar_no_local_collapsing is removed.
This is still SOURCE-ONLY, and will remain conditional on the three exact
earlier inputs even after acceptance. Public theorem semantics unchanged.

20:39UTC source continuation: the original strong_scalar_no_local_collapsing
body now follows the first 3^n-doubling scale, the cutoff entropy estimate,
and the same initial-to-late mu lower bound. BookDyadicVolume retains the
volume ratio and smaller concentric scalar control on actual FlowMetricBall.
It uses no local Bishop input; only the two earlier entropy inputs remain in
this proof. Pending verification, this removes both own entropy-file slots
from the source census, but no acceptance count changes until all checks pass.

2026-09-10 20:06UTC: the original mu_sobolev_relaxation and
cutoff_entropy_doubling bodies are proved. Saved check2 and named build2 pass
with exactly five remaining placeholders; fresh BookEntropyAxioms1 finds
only propext, Classical.choice and Quot.sound for both original endpoints.
The existing parabolic consumer is also standard-only. The other six original
theorems retain their explicit proof debt. Current receipt:
E:/lean-tools/chapter25-book-20260910/book-entropy-completion.json.

EntropyTest is unchanged: actual weak gradient, scalar L2, metric-gradient L2,
nonnegativity and unit mass. The proof retains n>=2, disconnected compact M,
and the empty case. Strong metric L2 approximation is derived from smooth
chart approximants and weak-gradient uniqueness. Higher moments give entropy
uniform integrability. Exact normalization and existing positive smoothing
give equality of the EReal infima. The analytic20-public audit is frozen in
weak-entropy-completion.json in the same receipt directory.

The cutoff uses the actual distance tent at4r/3, hence the3/r gradient bound
and36D energy coefficient. Its gradient is zero at zeros, including sphere
boundary points. Support/Jensen bounds negative entropy by log ball volume;
the nonnegative D/e restores the exact displayed book constant. The book's
dimension and b>=0 arguments are retained as unused underscored binders;
no native callers used their old binder names. No mathematical hypothesis
or geometric object is changed.

Next: local_entropy_volume. Check the existing local Bishop comparison's
actual ball, local Ricci domain, radius and connectedness assumptions before
using it for arbitrary closed M. Earlier mu_monotone, mu_compact_scale_lower
and local_metric_injectivity remain explicit inputs. Strong-scalar
noncollapsing is still an open Chapter25 argument; its spatial consumer is
conditional. Original-file count: two own placeholders and three earlier ones.

Definition25.1 fixed-terminal-ball migration remains accepted in the earlier
completion.json. Chapter25Theorems regression check2 passes24.88s with its
eleven unchanged placeholders. No broad build or foreign file edit.
Root/endpoint claim2197d1f8 release and current compiler windows are recorded
in WORKING_STATUS.md and authoritative script status.
