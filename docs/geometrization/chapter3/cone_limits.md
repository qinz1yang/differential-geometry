# Full AC85–86: cone closure and geometric cone compactness

Three public theorems in two leaves preserve actual full radial cone data on the SAME specified or constructed pointed limit. AC85 accepts metric cone sources and either actual growing-ball maps or original pointed convergence into a proper target. No source completeness, properness, curvature, dimension or length assumption is needed. The given-map engine uses one shared ultrafilter above atTop for every parameter and target point, passes the entire two-parameter distance law, and produces one actual radial map family. Every use of an original partial map is guarded by an eventual original-domain proof. This is an explicit alternative to the written dense-set/rational-parameter diagonal proof; the mathematical conclusion and hypotheses are unchanged.

AC86 starts with original complete source spaces, global arbitrarily short curves, global CBB0 comparison, dimension at most n with n>=1, and actual cone data. Existing geometric extraction returns a Type0 target, its basepoint, one strict subsequence, pointed convergence, completeness, properness, dimension bound, global comparison, metric segments, strong side inequality and exact nets. AC85 supplies a cone on that SAME target/basepoint, preserving this entire package. The implementation uses curvature allowance identically0 and radii i+1, which the accepted extraction theorem permits; reciprocal-curvature weakening in the written proof is unnecessary. No source properness or nontriviality is added. The dimension bound may be strict; no dimension equality is asserted.

The incomplete-source test constructs the actual dense union of planar rays S={(x,y):x!=0 or y=0}, proves it is incomplete, gives full radial maps and actual inclusion approximations with own coverage, and obtains cone data on the SAME Euclidean plane. Original AC86 tests use real cones centered3 with n2 and singleton cones with n1; the SAME extracted targets are proved respectively isometric to the real line/dimension1 and singleton/dimension0. These test loose dimension bounds and the point case, not actual loss of source dimension along a sequence.

Full AC85 and AC86 are proved. AC83's full KL convention equivalence and AC87 remain separate. Blueprint207 and migration interfaces are unchanged. The original candidate source record follows; final canonical-leaf acceptance is recorded separately.

# AC85 closure of radial cone data: temporary acceptance record

## Frozen candidates and checks

Two public theorems, no new definitions or private helpers: `/tmp/gc_RadialConeLimit_body.lean`, SHA256 `f86836c8e301c3c7d20c5644bbe568560da6dd949cf00bdc736a1d1348adfcae` (143 lines).

- `GC.MetricGeometry.nonempty_radialConeData_of_pointed_approximations`: source metric spaces with actual cone data, actual pointed ball approximations into the specified proper Y, radii tending to infinity and errors tending to zero; concludes `Nonempty (RadialConeData p)` on that exact Y/p.
- `GC.MetricGeometry.PointedGHConverges.nonempty_radialConeData`: original MC06 pointed convergence and source cone data give the same conclusion. There is no source properness, completeness, curvature, dimension, or length-space assumption. Properness of the target is the only added geometric hypothesis.

Combined baseline driver `/tmp/gc_RadialConeLimit_agent.lean`, SHA256 `064065b46099131d4a0b5c279ca81e97c6894d5d662818d670f87efaeae8e5fd`, compiles with an empty log. `/tmp/gc_RadialConeLimit_lint.lean` compiles with only the standard three axioms (`propext`, `Classical.choice`, `Quot.sound`) printed for both theorems, and no `unusedArguments simpNF synTaut` diagnostics. Both actual compiler sessions exited 0.

A separate `/tmp/gc_RadialConeLimit_minimports.lean` successfully compiles the final cone snapshot (SHA `55709e9d4fb8704ae699ba38887c0bab154bd0c64953292d86fccb136626b759`) and this body without the Mathlib.Tactic umbrella. In addition to the cone dependency, the closure uses PointedConvergence, Mathlib.Topology.MetricSpace.ProperSpace, Mathlib.Analysis.SpecificLimits.Basic, and the Choose tactic. The combined minimal-import probe replaces the cone snapshot's Mathlib.Tactic umbrella with FieldSimp and Choose. The cone and project source files were not edited.

## Source reading and proof-route departure

Frozen `GEOMETRIZATION_BLUEPRINT/master207A.tex`, SHA256 `277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b`: AC85 `prop:alexandrov-cone-limit-closure`, lines 6447-6503, statement and full proof read. AC82's exact radial-map convention was reread; the structure is the shared actual `RadialConeData` API, not a rescaling-invariance substitute.

Kleiner--Lott, *Locally collapsed 3-manifolds*, Asterisque 365 (2014), archived `KleinerLottAsterisqueLocalCollapse.pdf`, SHA256 `7a860b4dd95b35fe33b06bf040100ec243d72c80528d927f4763391aaf79cb6e`: section 4.5, Lemmas 4.19-4.20 and proofs, printed pp. 33-34 / PDF pp. 28-29, extracted actual text lines 1427-1471 reread. The limiting cone assertion is compressed in the source. This theorem establishes that metric closure step; it does not assert the entire overlapping-almost-cones conclusion of Lemma4.20.

Retained May 15, 2015 author corrections, `GEOMETRIZATION_BLUEPRINT/references/chapter13_2026-09-26/KL_corrections.pdf`, SHA256 `b5849571508231ce7328ef842eaa0a8a74e34804de7741dab548c406dea11e19`, have no correction to these selected statements. This reuses the previously checked snapshot, not a new current-web errata audit.

The implementation explicitly uses a DIFFERENT compactness proof from the blueprint's countable dense-set/rational-parameter construction. It fixes ONE ultrafilter extending atTop for every parameter/point pair in NNReal × Y, takes compact-ball limits, and passes the full two-parameter distance identity directly. It does not claim to implement the blueprint's countable diagonal or rational extension. The conclusion and hypotheses are unchanged. Parent reviewed and authorized this proof route, then independently read the complete body.

The route reuses the pattern actually inspected in accepted `DifferentialGeometry/Geometry/Metric/Approximation/PointedIsometry.lean`, lines25-46. Exact Mathlib revision: `c55e6e786f49471c72fbddbec5415808896aec1e`. Load-bearing APIs whose bodies were read:

- `Ultrafilter.of`, `Ultrafilter.of_le`: `Mathlib/Order/Filter/Ultrafilter/Defs.lean`, lines292-306; the chosen ultrafilter refines the same nontrivial atTop filter.
- `IsCompact.ultrafilter_le_nhds`: `Mathlib/Topology/Compactness/Compact.lean`, lines138-145; compactness supplies a limit for the mapped ultrafilter whenever it eventually lies in the compact set.
- `Filter.Tendsto.congr_dist`: `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`, lines1165-1174; vanishing metric error transfers convergence.

## Contract and domain audit

For each fixed target y, actual coverage chooses a source lift z_i(y) inside the ORIGINAL f_i carrier; the finite undefined prefix uses the original basepoint. Its f_i-image tends to y. Actual distortion shows source lift distances and radial distances converge to the corresponding distances in Y. No source compactness is used.

For each fixed real nonnegative t and y, radial norm equality bounds d(o_i,H^i_t z_i(y)) eventually by t(d(p,y)+2). Radii tending to infinity therefore put this radial image inside the ORIGINAL map domain before f_i is evaluated. Its mapped image eventually lies in the compact target ball of radius t(d(p,y)+2)+1. The single fixed ultrafilter gives a limit G_t(y) for every pair. Zero and one identities are passed using exact source map identities, actual basepoint equality, and the chosen lifts' convergence.

For fixed s,t,x,y, the SAME ultrafilter is used jointly for both radial images and both original lifts. Eventual source domain guards justify actual distortion, then the full source squared-distance law passes to the limit using convergent source kernels. Thus every real nonnegative parameter and every target point participates in ONE actual cone structure; no independent isometries of rescaled spaces are substituted. The shared cone API supplies semigroup and positive-scale surjectivity afterward.

## Compiled non-vacuity regression

`/tmp/gc_ac85_incomplete_review_body.lean`, SHA256 `2bf6e95f33ef44192524885032bd6643ac1dfbe11415043af09577d1e3e7ba08`; combined `/tmp/gc_ac85_incomplete_review_agent.lean`, SHA256 `1cdb05602561778d9ea9244e08fca5aea199c394411b71719a27c438f49b5305`. Actual compile exit 0, no warnings, all four test theorems use only the standard three axioms; lint clean.

The source S={(x,y) in R² | x≠0 or y=0} is a dense union of full rays. The actual maps H_t(z)=t*z have the exact cone identity. S is formally proved incomplete: (0,1) lies in its closure and is missing. For EVERY 0<ε<R, actual inclusion PBAs into the Euclidean plane are constructed, with own target coverage obtained by perturbing the first coordinate by ε/2 when needed and proving the witness stays within the original R-ball. These give original MC06 pointed convergence. Applying the new wrapper yields actual cone data on the SAME plane/basepoint, and the resulting full two-parameter identity is exposed in a separate compiled consumer.

No repository changes, shared builds, admissions, or custom axioms were introduced by this subtask. These are temporary candidates for parent integration and do not claim chapter completion.



Implemented `/tmp/gc_NonnegativeConeCompactness_body.lean`, SHA256 `efb9c4e073e74d74c1d77ed167464558a85dce20b9642c35d0941b0452a25aa6`; combined driver SHA256 `ad09f2e244d1385d78bf6f5d2f11c62e645ee5c4b4af85bffd63488d8dc2e667`.

One public theorem accepts a complete metric source family in arbitrary Type u, global arbitrarily short curves, global dimension bound at most n with n>=1, global four-point comparison at curvature0, and actual cone data. It invokes accepted growing-region extraction with curvature allowance identically0 and radii i+1; that API permits nonnegative zero allowances directly, so the written reciprocal-curvature weakening is unnecessary. Root approved this minor proof-route simplification. The theorem retains the exact constructed Type0 target, basepoint and strict subsequence; complete/proper geometry, convergence, dimension bound, global comparison, actual segments, strong side inequality and the exact existing net constant remain intact. AC85 adds cone data at that SAME target basepoint. No source properness or nontriviality is added, and no equality of source/target dimensions is claimed. Fresh compile/lint exited0 with standard-three axioms.

Original-input regression body `/tmp/gc_nonnegative_cone_compactness_review_body.lean` SHA256 `0207ac48bee6917a3678bc96b1c5337b0054c536e2e1cccb44d01d1331f1604c`; full driver SHA256 `e0a36c4ad1b45020eb8abf620fcfadbb27364d6b1703a9af2ba8bd6954361214`. The actual constant real-cone family centered3 with bound n=2 yields the same target proved isometric to the real line, with dimension exactly1 and actual radial points at every nonnegative radius. The actual singleton family with bound n=1 yields the same target proved singleton, dimension0, and constant radial maps. These verify nontrivial and point cases and absence of a forced dimension=n conclusion; they are not a claimed example whose actual source dimensions drop along the sequence. Fresh compile/lint exited0; both public tests have standard-three axiom closure.

All work by this agent was in `/tmp`; no repository edits or shared builds were performed. Main combined drivers contain no proof-print output; axiom output is isolated in the corresponding `_lint.lean`/`_lint.log` files.
