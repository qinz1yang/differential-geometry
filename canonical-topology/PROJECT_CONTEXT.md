# Poincare local-homology checkpoint

This directory is a separate portable `PoincareLean` project prepared for
additive publication within the shared DifferentialGeometry Git repository.
Its sources retain the original mathematical objects and namespaces.

The recovered Chapter 35 baseline is commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`, supplemented by recovered working-tree
proofs with separately recorded provenance. This checkpoint includes 155 modules
and 226 curated tracked added public exports.

## Compact-support cap naturality under open embeddings

This 155-module checkpoint tracks 226 curated added public exports. Two new
public theorems construct the cap maps from actual coherent relative-homology
families and prove the square with compact-support extension and ordinary
homology pushforward. Both representative laws remain public. The absolute-class
specialization uses the actual image of the source class and identifies both
maps with ordinary cap after forgetting compact support.

The statements cover all natural degrees and open embeddings into Hausdorff
spaces, without a manifold, compactness or positive-degree assumption. The
proper point-to-integers consumer produces nonzero source, target and
compact-support classes and checks the actual cap values and full square.
The three representative, excision-extensionality and cap-square helpers stay
private. All 154 preceding source leaves and public APIs remain unchanged.

Source `1789419937125041916-topology-d82efff4` passed in 16.86 seconds with 243 guards and 39 signature/axiom pairs. Original `1789423067944195099-topology-01d7710a` passed in 48.69 seconds with 1321 guards and 143 pairs; portable `1789423068007160847-topology_checkpoint-d240eeba` passed in 96.31 seconds with 1617 guards and 443 pairs. Both ran in Slurm 13879784. The portable CapNaturality leaf and root freshly compiled in 0:16.86, maximum RSS 1,831,844 KiB, with zero diagnostics. All 136 preceding original and 436 preceding portable readback pairs are byte-identical. All 39 source types are byte-identical in the original check, with 36 complete pairs unchanged. The three new private axiom heads and one ordered axiom-line wrap are explicit. All 39 source and 143 shared imported readbacks agree through exact private heads, qualification and whitespace, without binder changes. Strict source and stock declaration linters pass, transitive axioms are standard-only, and all 154 preceding source leaves remain unchanged.

General integral manifold duality, positive-dimensional outward homology
normalization, the adjunction sign and the missing frozen contract remain open.
Neither full theorem suite is complete.

## Local constancy of outward sphere orientations

This 154-module checkpoint tracks 224 curated added public exports. The actual
outward tangent orientation is locally constant after transport through each
fixed native sphere chart. The ambient orientation and chart center remain
ordinary inputs; the conclusion holds in every dimension, including zero.
The S2 consumers use actual tangent vectors and transported orientations, and
the real zero-sphere consumer retains the negative endpoint orientation.

Source `1789419839469028859-topology-0c249c94` passed in 20.92 seconds with 79 guards and 14 signature/axiom pairs. Original `1789421445432683568-topology-f85de60d` passed in 36.45 seconds with 1285 guards and 136 pairs; portable `1789421445488001509-topology_checkpoint-0b7ae135` passed in 84.33 seconds with 1581 guards and 436 pairs. Both run in Slurm 13879784. Unchanged-source build `1789421119629364733-topology_checkpoint-c89d5038` freshly compiled both affected leaves and the portable root in 0:28.79, maximum RSS 1,933,852 KiB, with zero compilation diagnostics. Its failed consumer harness remains failed history; the repaired strict checks above supply final acceptance evidence. All 127 preceding original and 427 preceding portable readback pairs are byte-identical. All fourteen source readbacks agree through exact private names, qualification and whitespace, with one recorded ordered axiom-line wrap. The prior private binder spelling change remains explicitly recorded. Strict source and stock declaration linters pass, transitive axioms are standard-only, and all 153 other leaves remain unchanged.

Positive-dimensional outward homology normalization, the adjunction sign,
general integral manifold duality and the missing frozen contract remain open.
This checkpoint does not close either full theorem suite.

## Compactly supported cohomology and cap maps

This 154-module checkpoint tracks 223 curated added public exports. The twenty
new public declarations use actual integral relative cohomology, compact sets
and Mathlib's ModuleCat colimit. Representatives, eventual-zero detection,
descent and the forgetful map are explicit. For compact spaces the forgetful
map is bijective in every degree, including zero and the empty space.

Open-embedding excision supplies extension maps for compactly supported
cohomology into Hausdorff spaces, with actual representative and forgetful
squares and public identity and composition laws. A coherent family in actual
relative homology determines a unique cap map to ordinary homology. For a
family induced by an absolute class, this is ordinary cap after forgetting
compact supports. These results do not assert cap bijectivity or general
manifold Poincare duality.

Source `1789418778428144132-topology-b70d689d` passed in 15.62 seconds with 477 guards and 46 signature/axiom pairs. Original imported `1789419477860964482-topology-d3393e9d` passed in 134.39 seconds with 1207 guards and 127 pairs. Portable `1789420070970770813-topology_checkpoint-07293782` passed in 96.63 seconds with 1503 guards and 427 pairs in Slurm 13879784. Unchanged-source build `1789419477997391095-topology_checkpoint-650f90d8` freshly compiled all 12 affected leaves and the portable root in 1:35.19, maximum RSS 2,012,168 KiB, with zero compilation diagnostics. Its duplicate-universe harness failure is retained as failed history; the repaired final harness above is the accepted strict result. All 393 preceding portable and 82 preceding original readback pairs are byte-identical. All 41 non-helper accepted source readbacks are byte-identical; the helper changes only its axiom declaration name. All 46 source readbacks agree with both imported checks modulo the exact seven private-name mappings, qualification and whitespace; ordered axioms are exact and standard-only, with two recorded private-name line-wrap changes. Strict source and stock declaration linters pass. All 150 preceding unedited leaves remain unchanged.

The six external consumers cover a proper open interval, nonzero extension from
a point into the integers, compact manifold generators, a nonzero sphere unit
cap, degree-zero vanishing on the real line and the empty compact space.
Open-embedding cap naturality, general integral manifold duality,
positive-dimensional outward homology normalization, adjunction signs and the
missing frozen topology contract remain open. Neither full theorem suite is
claimed complete.

## Outward sphere orientations and the real zero-sphere boundary

This 151-module checkpoint tracks 203 curated added public exports. The nine
new public declarations use the existing sphere, tangent, chain and homology
objects. Two reusable degree-zero vertex laws extend RelativeZero; the actual
chart/excision vertex equation extends LocalCharts. SphereOrientation contains
the outward tangent construction, and ZeroSphereOrientation proves its real
zero-sphere homology normalization. The chart center and tested point remain
independent. Three private mechanics and three external consumers retain the
actual maps and nonzero classes.

Source `1789415403088387390-topology-d59cc6b9` passed in 20.69 seconds with 335 guards and 19 signature/axiom pairs. Original imported `1789415898956497386-topology-2f1867f5` passed in 203.72 seconds with 1139 guards and 82 pairs. Portable `1789415899102782476-topology_checkpoint-acf37420` passed in 266.69 seconds with 1427 guards and 393 pairs in Slurm 13879784. All 19 affected leaves and the portable root freshly compiled in 2:46.11, maximum RSS 2,835,528 KiB, with zero diagnostics. All 380 preceding portable and 66 preceding original readback pairs are byte-identical. New public and consumer types agree with the accepted source modulo only qualification and whitespace; transitive axioms are exact and standard-only. Strict source and stock declaration linters pass. All 147 preceding unedited leaves remain unchanged.

Positive-dimensional outward homology normalization, the adjunction sign,
general integral manifold duality and the missing frozen topology contract
remain open. This checkpoint does not close the full topology suite.


The preceding global-generator and local-cap checkpoints remain available.
The 149-module layer proves actual top local cap bijections at every generator
on finite-dimensional real normed spaces and preconnected native-chart
manifolds, including ranks zero and one. On a compact simply connected
manifold, the same global class supplies every local cap argument.

The earlier global-generator evidence is preserved below:

Actual top local integral homology now has a generator in every finite-dimensional
real normed space, including ranks zero and one. On a compact simply connected
Hausdorff C1 manifold without boundary, the actual top-degree absolute-to-point
restriction is bijective. Every prescribed local class therefore has a unique
absolute preimage. These statements construct the model generator and tangent
orientation internally and require no supplied orientation field or locality.

The manifold now also has one actual top integral homology class generating the
absolute group, whose restriction generates the local group at every point.
The new theorem constructs that class internally. Consumers verify nonzero
global and local classes in rank zero and unique integer coefficients for every
point-local class through the same global generator.

Source 85d8e937 passed in 30.87s with 1004 guards and 38 pairs. Original imported
9479252d passed in 46.21s with 996 guards and 37 pairs. Portable ffc421f5 passed
in Slurm 13879784 in 103.89s with 1284 guards and 353 pairs. The changed
ManifoldFundamentalClass leaf and portable root freshly compiled in 21.29s,
maximum RSS 1965752KiB, with zero diagnostics. All 350 preceding portable and
34 original pairs are byte-identical; all 145 other leaves are unchanged.
All three new shared source/original/portable types agree modulo qualification
and whitespace, with exact standard-only axioms. Strict source and stock
declaration linters pass. Outward normalization and general integral manifold
duality remain open.

The preceding local-generator and restriction-bijection checkpoint is preserved:

Source 67ea80b6 passed in 52.58s with 222 guards and seven pairs. Original
imported 303a2b3a passed in 137.86s with 984 guards and 34 pairs. Portable efa87b9b
passed in Slurm 13879784 in 217.19s with 1272 guards and 350 pairs. Nine affected
leaves and the portable root freshly compiled in 2:01.42, maximum RSS 2844500KiB,
with zero diagnostics. All 344 previous portable and 28 previous original
pairs are byte-identical; all 144 other source leaves are unchanged. All six
shared new source/original/portable pairs agree modulo qualification and
whitespace, with exact standard-only axioms. Strict source and stock declaration
linters pass. Rank-zero and real-line consumers force actual nonzero generators;
the rank-zero unique absolute-preimage consumer also passes.

The preceding orientation checkpoint remains available unchanged:

A simply connected finite-dimensional real C1 manifold now has an actual tangent
orientation field prescribed at any supplied point, with locally constant
orientation coordinates in every fixed native chart. The proof constructs the
orientation covering from actual tangent transitions and lifts the identity.
It requires no compactness, Hausdorffness, positive rank, supplied global frame
or orientation field. The model and manifold universes are independent.

Three external consumers preserve a negative rank-zero orientation and feed the
produced field into the existing unique local integral-class family and global
fundamental-class engines, retaining all actual chart, excision and translation
equations. Those general oriented engines retain an explicit model local class;
their generator conclusions accept a model generator and a nonempty compact
connected manifold. The new simply connected corollaries construct these inputs. Existing
local-frame and locality-based public interfaces remain unchanged.

Source 0413d3cf passed in 75.81s with 249 guards and 46 signature/axiom pairs.
Original imported 926c3536 passed in 192.45s with 966 guards and 28 pairs.
Portable 6e8cae83 passed in Slurm 13864417 in 278.82s with 1254 guards and 344 pairs.
Four affected leaves and the portable root freshly compiled in 2:39.99,
maximum RSS 1985332KiB, with zero diagnostics. All 339 previous pairs are
byte-identical and all 143 other preceding leaves unchanged. All 28 common
source/original/portable types agree modulo only qualification and whitespace;
axiom readbacks are exact. Strict source and stock declaration linters and
standard-only transitive axioms pass.

Outward sphere normalization, general manifold duality and the missing frozen
canonical-topology contract remain open. The historical results below retain
their established public statements and proof bodies except for sharing the
general orientation-map composition law in Poincare.LinearAlgebra.Orientation.

The preceding all-degree sphere, Euclidean point and bounded star-convex cap
bijections retain their exact public statements and proof bodies. Their classes,
normalizations and degree-zero consumers are unchanged.

The preceding cohomology cover shift, its actual forward/inverse equations,
and relative-to-absolute comparison in every positive degree are unchanged.

The preceding unique real-line local class, its normalization and actual cap
bijection, and the generic pair-map cap transport remain unchanged.

The preceding actual relative homology/cohomology comparison theorem and its
sphere-to-puncture consumer retain their exact statements and bodies.

The preceding empty-pair cohomology equivalence and its actual forward-map
equation retain their exact statements and bodies.

The preceding degree-zero relative and empty-space cohomology results retain
their exact statements and bodies, including the nonempty-subspace assumption
for relative H0 vanishing and its nonzero empty-subspace consumer.

The earlier relative cohomology connecting-map bijections and higher-degree
vanishing retain their exact statements and bodies.

The previously published positive-degree cohomology vanishing, including its
nonzero H0 consumer, retains its exact statements and bodies.

The actual cochain comparison, naturality, homotopy invariance and excision
results retain their exact public statements and bodies.

The earlier uniquely normalized two-point cap-duality theorem and its fifteen
unchanged recovered working-tree prerequisites retain their exact statements
and bodies. Those prerequisites were absent from the recovered Git baseline;
their provenance remains separately recorded. The concrete simply connected
T1 two-point duality case does not close general manifold duality or the full
canonical theorem suite.

The preceding signed-chart extension retains its exact public statements.

The signed-chart theorem identifies the change between the actual normalized
local top-homology maps of two manifold charts with the sign of their actual
transition derivative determinant. C¹ regularity and finite-dimensional real
normed models suffice, including rank zero. The earlier oriented-map theorem
retains its exact statement and now follows from this general sign formula;
the compact oriented-neighborhood class theorem is unchanged.

The actual absolute-to-relative-empty map is now a linear equivalence in
every degree and topological space, with its defining map equation exposed.
Nonzero degree-zero and naturality consumers pass.

The new results construct a compact neighborhood on which a class's
restriction vanishes when its actual point restriction is zero. Compact
relative homology on any Hausdorff manifold charted over a finite-dimensional
real normed model vanishes above the model dimension. In the model dimension
or above, point restrictions determine compact classes, and every nonzero
compact class has a nonzero point restriction. Rank zero, nonclosed supports
for local vanishing, and noncompact ambient manifolds are included.
No orientation or smoothness is required by these results.

The earlier actual Mayer–Vietoris lifts, conditional uniqueness, compact
carrier and neighborhood-extension results, and oriented compact chart classes
retain their public statements and proof bodies. Coherent generators now follow
from tangent locality and a supplied model generator.
[provenance/SNAPSHOT.json](provenance/SNAPSHOT.json) records exact source and
configuration identity and preserves the earlier validation records. It is not
the full recovered Chapter 35 project.

Preserve Lean `leanprover/lean4:v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and DifferentialGeometry `v0.1.2`
at `1b535dd102b94cc42b107cca27059687888f08b3`. Use DifferentialGeometry only
as a pinned upstream dependency; no included Lean module currently imports it.

The mathematical work belongs to the canonical-topology workstream described
in the enclosing Schoenflies controller's
[two-project prompt](../../plan/della_two_projects_prompt.md),
[topology brief](../../plan/CANONICAL_TOPOLOGY_SPINOFF_BRIEF.md), and
[active plan](../../plan/plan_smooth_schoenflies.md). Those controller records
are external to this portable package. The package README records its limited
delivered scope and checkpoint status independently.

The frozen topology handoff is still missing. Do not reconstruct its public
contract from this foundations checkpoint. Neither the full canonical topology
suite nor the combined Schoenflies/topology goal is complete.

The older project context and agent instructions are preserved under
`provenance/RECOVERED_*.md` as historical source records. Their old machine paths,
branch destinations and release claims are not current operating instructions.
