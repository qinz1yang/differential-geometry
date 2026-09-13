# Local homology and global classes from coherent local generators

This separate `PoincareLean` project contains a dependency-closed checkpoint of
115 Poincare modules. It extends the recovered Chapter 35 source at commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad` and preserves its mathematical objects
and `Poincare` namespaces. `Poincare.lean` imports every included leaf.

The additions prove:

- the actual relative-cohomology/relative-homology cap product with absolute
  homology output, its cycle formula, naturality and both projection laws;

- the bilinear cap product of actual relative cochains and relative chains
  with absolute-chain output, its projection, naturality and signed boundary laws;

- compatibility of the actual relative cap product with the original connecting
  map, including its degree sign, and a general cycle-class connecting formula;

- the ordinary-cohomology/relative-homology cap product on the original groups,
  its cycle formula, naturality, unit and absolute-to-relative compatibility;

- the actual ordinary-cochain/relative-chain cap product, its projection law,
  pair-map naturality, signed boundary identity, unit and cycle laws;

- normalized degree-zero cohomology of any path-connected space as the integers,
  its class-evaluation law and naturality, and the actual degree-zero cap action;

- the bilinear pairing on actual integral cohomology and homology, its cycle
  representative law, naturality, constant-one unit and unit naturality;

- the actual bilinear integral cap product, simplex formula, map naturality,
  signed boundary identity, augmentation unit and preservation of cycles;

- excision for the actual relative integral cochain and cohomology maps;

- relative cochains as the kernel of the actual singular-cochain restriction,
  their contravariant pair maps, and the natural exact cohomology sequence;

- compact gluing and unique absolute classes from locally realized local classes;
- a global integral generator and bijective actual point restrictions on a
  nonempty compact connected manifold, from coherent local generators;
- the determinant-sign formula for the actual normalized top local-homology
  maps of arbitrary overlapping C¹ manifold charts, including rank zero;
- an equivalence from actual absolute integral homology to homology relative
  to the empty subspace, with its forward map equal to the original
  absolute-to-relative map, in every natural degree and topological space;
- composition, neighborhood naturality, restriction and germ laws for the
  actual local integral singular-homology maps;
- the actual chart/excision commuting square;
- invariance of induced positive-degree relative maps under homotopy of their
  subspace restrictions, when the relevant target absolute group vanishes;
- a punctured-ball homotopy from an invertible derivative to the given map,
  with a positive radius, continuous endpoints and the interpolation formula;
- equality of the corresponding relative-homology maps on one produced ball
  in every positive homological degree;
- equality of the original ambient relative maps with the invertible derivative
  in every natural homological degree, including degree zero;
- equality of relative H0 maps for pointwise joined continuous maps preserving
  the given subspaces;
- multiplication by the sign of the determinant for the actual top local
  integral homology map of any continuous linear equivalence of a finite-dimensional
  real normed space, including dimension zero;
- the actual local-homology map of a differentiable open partial homeomorphism
  with differentiable inverse equals its derivative determinant sign after
  translating source and target basepoints to zero, including dimension zero;
- composition and neighborhood restriction laws for actual open-partial-homeomorphism
  local maps in every natural degree;
- equality of the normalized local top-homology maps from the same manifold
  point under two charts whose actual tangent trivializations preserve the
  same orientation, for finite-dimensional real normed models including rank zero;
- the actual closed-ball-to-center restriction isomorphism and its induced-map
  equation, together with a unique relative class whose local restrictions
  agree after translation, in every natural degree and real normed space,
  for every center and nonnegative radius including boundary points;
- the actual compact-pair chart isomorphism, its excision map equation and its
  point-restriction square, together with a produced compact chart neighborhood
  and a unique relative class whose normalized local restrictions agree;
- a unique compact-neighborhood class with the same normalization in every
  chart whose actual tangent trivialization preserves the base-chart orientation.

The thirty-one new/changed modules and their exact baseline/current hashes are listed in
[provenance/SNAPSHOT.json](provenance/SNAPSHOT.json). The derivative homotopy
retains its [upstream attribution and modification record](provenance/README.md).

## Environment and validation

The portable package files preserve Lean `v4.33.1`, Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, and the original DifferentialGeometry
`v0.1.2` dependency at `1b535dd102b94cc42b107cca27059687888f08b3`.
The selected source closure imports Mathlib only; no DifferentialGeometry source
is copied into this project. The toolchain file has only its extra trailing
blank line removed. Its original and normalized hashes are recorded.

The package root target is `lake build Poincare`, run from this directory.
On Della all sustained checks belong to the shared Slurm CPU worker. Use the
existing exact caches offline; local cache paths and any validation-only path
manifest stay outside the published package files.

The 74-module checkpoint passed its final affected-module/root build and
consumer/linter/axiom gate in Slurm 13781140, request
1789229647248153045-topology_checkpoint-a464ec28. The six additional leaves,
changed derivative-comparison source and root freshly compiled with zero
diagnostics; unchanged leaves retain their verified prior compilation. All 12
public exports, four nonidentity consumers, and a nonzero degree-zero class
consumer passed exact signatures and standard-only axiom guards, with stock
declaration linters over the entire
imported package and the consumers. The previous 68-module checkpoint was
published as `76917c5e2`.

The new 88-module snapshot retains those 74 sources unchanged and adds 13
unchanged baseline dependencies plus `LocalLinearMaps`. The latter passed its
fresh module and imported consumer gate in the original isolated project,
request `1789235551579974740-topology-d57a1cb3`. Its sole new public result uses
the given continuous linear equivalence directly; reflection, sphere and matrix
proof machinery remains private. Consumers checked nonidentity positive and
negative maps, an actual nonzero class moved by negation, and rank zero.

The final portable 88-module gate passed in Slurm 13781140, request
`1789236250289124336-topology_checkpoint-db7e7dbe`. All 14 added leaves and the
root freshly compiled with zero diagnostics in 5:55.36; the full request took
401.64 seconds. All 93 source/configuration/harness guards and 22 exact
signature/axiom pairs passed, including all 13 public exports. Stock declaration
linters and standard-only axiom checks covered the imported package and consumers.
The unchanged 74 leaves retain their earlier compilation evidence.
Source hashes and the separate validation records are recorded in
[provenance/SNAPSHOT.json](provenance/SNAPSHOT.json). No acceptance of the larger
topology suite is asserted.

The derivative-sign extension keeps the same 88 leaves and exposes one further
public result in the existing `LocalDerivativeComparison` module. The forward
and inverse differentiability hypotheses concern the actual local map; no
chosen derivative equivalence, point-fixing equation or global puncture
preservation is required. Four private helpers handle the produced small ball,
translations and neighborhood cancellation once. Both previous public derivative
proofs are preserved.

Final portable request `1789239376984243943-topology_checkpoint-ed89b504`
passed in Slurm 13781140 in 124.07 seconds. The changed leaf and `Poincare`
root freshly compiled without diagnostics in 1:16.87. All 99 guards and 25
signature/axiom pairs passed, covering all 14 public exports, the unchanged
prior consumers, an actual restricted nonidentity map with negative derivative,
and dimension zero. All-package and consumer declaration linters and
standard-only transitive axioms pass. The 87 unchanged leaves retain their
earlier compilation evidence; the previous 88-leaf checkpoint's evidence is
preserved in the snapshot record.

The oriented-chart extension adds `LocalOrientation`, bringing the checkpoint to
89 leaves and 17 public exports. Its primary theorem compares maps from the
same actual manifold local-homology group to the model's group at zero. The
hypothesis concerns one tangent orientation and the actual two trivializations;
no independent local generators or locally constant charts are supplied.
Two shared neighborhood/composition laws now live in `LocalCharts`. The old
55-line private neighborhood helper was moved there unchanged, and all three
retained public derivative-comparison proofs are unchanged.

Final portable request `1789242935902017893-topology_checkpoint-96e8ea73`
passed in Slurm 13781140 in 183.53 seconds. `LocalCharts`,
`LocalDerivativeComparison`, `LocalOrientation` and `Poincare` freshly compiled
without diagnostics in 2:14.67. All 99 guards and 32 signature/axiom pairs
passed, including all 17 public exports and every previous consumer readback.
The new consumers use actual translated manifold charts and a restricted
composition whose source is a proper intersection. All-package and consumer
stock declaration linters and standard-only transitive axioms pass. The 86
unchanged leaves retain their earlier compilation evidence. The original
full-source gate separately checks a rank-zero oriented chart transition.
These results establish pointwise chart compatibility. The following extension
constructs the required class on model-space closed balls.

The closed-ball extension adds `LocalBallHomology`, bringing the checkpoint to
90 leaves and 21 public exports. It identifies the actual center restriction
with an isomorphism and proves a unique class whose translated local
restrictions agree at every point of the closed ball. The statements allow
arbitrary real normed spaces, all natural homology degrees, arbitrary centers,
radius zero and boundary points. They assume a prescribed local class, not a
fundamental class or coherence certificate.

Final portable request `1789247905874477991-topology_checkpoint-baeeac80`
passed in Slurm 13781140 in 118.75 seconds. The new leaf and `Poincare` root
freshly compiled without diagnostics in 1:06.46. All 102 guards and 40
signature/axiom pairs passed, including all 21 public exports and all 32
previous readback pairs unchanged. New consumers checked both inverse laws,
a nonzero rank-zero H0 class, a real boundary-point translation and uniqueness.
All-package/current-consumer stock declaration linters and standard-only
axioms passed. The 89 previous leaves remain byte-identical and retain their
earlier compilation evidence.

The compact-chart extension adds `LocalCompactHomology` and three unchanged
baseline dependencies used by the nonzero Euclidean3 consumer. The checkpoint
now contains 94 leaves and 25 public exports. Its main theorem constructs a
compact neighborhood inside the supplied chart and a unique relative class
with every normalized restriction equal to one prescribed model class. The
chart isomorphism and actual map equations work in every natural degree.
No preconstructed compact neighborhood or coherent family is supplied.

Request `1789250063643581109-topology_checkpoint-2f2e02e3` freshly compiled
the four added leaves and root without diagnostics in 2:18.61. The final
consumer replay `1789250353396415278-topology_checkpoint-c6197cda` passed in
52.24 seconds after duplicate universe declarations were removed from the
combined test harness. All 94 source files remained unchanged between those
checks. All 109 guards and 48 signature/axiom pairs passed, including all
40 previous readback pairs unchanged. New consumers verify the inverse
restriction square, nonzero classes at every point of an actual translated
Euclidean3 chart, and the exact negative-class law on the same compact set.
All-package/current-consumer stock linters and standard-only axioms passed.
The 90 previous leaves remain byte-identical and retain their earlier evidence.

The oriented-neighborhood extension keeps the same 94 leaves and adds one
public theorem to `LocalOrientation`, for 26 public exports. All previous
source blocks in that module remain unchanged. It produces one compact
neighborhood and one unique relative class whose normalization agrees in
every chart with compatible actual tangent orientation. A prescribed model
class may be arbitrary; no global orientation or fundamental class is assumed.

Final portable request `1789251985955893192-topology_checkpoint-9c57dab9`
passed in Slurm 13781140 in 127.77 seconds. The changed leaf and root freshly
compiled without diagnostics in 1:09.90. All 115 guards and 51 signature/axiom
pairs passed; all 48 previous readback pairs are byte-identical. Consumers
verify nonzero restrictions at every point and an actual Euclidean3 class.
All-package/current-consumer stock linters and standard-only axioms passed.
The other 93 leaves and the aggregate are unchanged and retain prior evidence.

The bounded star-convex extension adds two leaves and four public results,
for 96 modules and 30 public exports. It proves that the actual inclusion
from the complement of a bounded star-convex set to its center's complement
is a homotopy equivalence. The induced original relative-homology restriction
is an isomorphism in every natural degree. The center must belong to the set;
no finite dimension, closedness or nonempty interior is required.

The existing closed-ball construction now uses this common radial engine.
Its four public statements and their entire proof bodies are unchanged,
as are the final 241 source lines. Consumers include a segment endpoint,
rank zero, the actual forward inclusion, inverse restriction, and agreement
with the previous closed-ball restriction map.

Final portable request `1789254131971909628-topology_checkpoint-8c2ff12b`
passed in Slurm 13781140 in 235.92 seconds. The two new leaves, refactored
`LocalBallHomology`, affected `LocalCompactHomology` and `LocalOrientation`,
and `Poincare` freshly compiled without diagnostics in 2:54.59. All 122
source/configuration/harness guards and 61 signature/axiom pairs passed.
All 51 previous pairs and the ten new public/consumer pairs match their earlier
readbacks byte for byte. All-package/current-consumer stock linters and
standard-only transitive axioms passed. The 91 unchanged leaves not rebuilt
in this run retain their earlier compilation evidence.

The high-degree vanishing extension adds three checkpoint leaves and five
public results, for 99 modules and 35 added exports. It proves actual
H_n(X,X) vanishing for arbitrary topological spaces and all natural degrees,
and local homology vanishing above the dimension of any finite-dimensional
real normed space. The latter reuses the existing higher-dimensional theorem
and extends it to ranks zero and one and arbitrary norms and centers.
The four existing Euclidean/manifold vanishing statements and proofs remain
unchanged. The new bounded star-convex, bounded convex and compact convex
corollaries allow empty sets and do not assume nonempty interior.

Final portable request `1789256733392947972-topology_checkpoint-e20ea2ab`
passed in Slurm 13781140 in 172.69 seconds. The three added leaves and root
freshly compiled without diagnostics in 1:50.75, with maximum RSS 1923004 KiB.
All 131 guards and 77 signature/axiom pairs passed. The 61 previous pairs are
byte-identical; 16 additional public/consumer pairs match the original check
except for namespace qualification of `Set.univ` and `Module.finrank`.
Consumers include rank zero, rank one, a sup norm, arbitrary-radius closed-ball
intersections and open balls. All-package/current-consumer stock linters and
standard-only axioms passed. All 96 previous leaves remain byte-identical and
retain their earlier compilation evidence.

The relative Mayer–Vietoris extension adds one 815-line leaf and five public
results, for 100 modules and 40 added exports. Compatible classes over two
open subspaces lift to their intersection through the actual relative maps.
The lift is unique when the next-degree relative group of their union
vanishes. Closed-support union and disjoint-union gluing are corollaries.
Neither a preconstructed gluing class nor an ambient-cover equality is assumed.

Final portable request `1789257537165329093-topology_checkpoint-6a6afc66`
passed in Slurm 13781140 in 133.73 seconds. The new leaf and root freshly
compiled without diagnostics in 1:12.59, maximum RSS 1778292 KiB. All 138
guards and 86 signature/axiom pairs passed. All 77 prior pairs and the nine
new public/consumer pairs match their earlier readbacks byte for byte.
Consumers verify a nonzero two-point class with local values +1 and -1,
its uniqueness, a nonzero rank-zero H0 class with unique lift, and degree-zero
shared-support lifting. Stock linters and standard-only axioms pass.
All 99 previous leaves remain unchanged and retain earlier build evidence.

The compact-support extension adds `CompactSupport` and extends
`CompactVanishing`, for 101 modules and 43 added exports. Every actual finite
singular chain has a compact carrier inside its given carrier set. Every
relative class supported on a compact set extends to a compact neighborhood
inside a prescribed open set, in any locally compact Hausdorff space and all
degrees. These are actual classes with the original restriction-map equation.

The general vanishing theorem proves H_n(E,E\K)=0 whenever K is compact and
n exceeds the dimension of the finite-dimensional real normed space E.
There is no convexity hypothesis; empty supports and rank zero are included.
It reuses the published local/convex vanishing and actual Mayer–Vietoris
restriction injectivity through a finite closed-ball neighborhood.

Final portable request `1789259440438453253-topology_checkpoint-e60efd1d`
passed in Slurm 13781140 in 151.16 seconds. The new leaf, changed leaf and
root freshly compiled without diagnostics in 1:26.53, maximum RSS 1914684 KiB.
All 146 guards and 95 signature/axiom pairs passed. All 86 previous pairs are
byte-identical; the nine added pairs match the original imported gate except
for `Module.finrank` and `Set.Ioo` qualification. Consumers check a nonzero
singular chain and its prescribed compact carrier, extension of a nonzero
Euclidean3 local class, empty-space and degree-zero cases, nonconvex compact
supports and rank zero. Stock linters and standard-only transitive axioms pass.
The other 99 previous leaves remain unchanged and retain their earlier evidence.

The manifold extension adds `ManifoldCompactHomology` and extends
`CompactSupport`, for 102 modules and 48 added exports. A class whose actual
point restriction is zero vanishes on a produced compact neighborhood
intersection inside any prescribed open neighborhood. This permits arbitrary
supports, all degrees, and locally compact Hausdorff ambient spaces.

For Hausdorff manifolds charted over any finite-dimensional real normed model,
compact-support relative homology vanishes above the model dimension. In the
model dimension or above, the actual point restrictions determine a compact
class uniquely; every nonzero compact class has a nonzero point restriction.
Rank zero is included. No smoothness, orientation, connectedness, second
countability, or compactness of the entire manifold is required.

Final portable request `1789261428531126275-topology_checkpoint-fa830b31`
passed in Slurm 13781140 in 211.17 seconds. Changed `CompactSupport`, affected
`CompactVanishing`, new `ManifoldCompactHomology`, and the root freshly compiled
without diagnostics in 2:26.11, maximum RSS 1928476 KiB. All 199 guards and
106 signature/axiom pairs passed. The 95 previous pairs are byte-identical;
the eleven added public/consumer pairs match the original imported gate up to
`Module.finrank`/`Set.Ioo` qualification and formatting. Consumers include a
nonzero two-point class, nonclosed support, arbitrary three-manifolds and
rank-zero manifolds. Stock linters and standard-only axioms pass. The other
100 prior leaves remain byte-identical and retain earlier compilation evidence.

The relative-empty extension adds `RelativeEmpty`, for 103 leaves and 50
added exports. It uses the actual zero chain inclusion and cokernel map to
construct the absolute-to-relative equivalence, retaining the exact forward
map equation. No connectivity, dimension or nonemptiness assumption is required.

The new leaf and root freshly compiled in Slurm 13781140, request
`1789262781992230755-topology_checkpoint-e5804880`, in 1:18.48 with maximum
RSS 1778200 KiB and zero diagnostics. Final request
`1789264345451073915-topology_checkpoint-f04d0bd9` passed in 91.29 seconds
after fixing a duplicate universe declaration in the combined consumer harness.
Production sources were unchanged; the final root build reused those artifacts.
All 206 guards and 111 signature/axiom pairs pass. The 106 prior pairs and
five new public/consumer pairs exactly match their earlier readbacks.
Consumers check a nonzero relative H0 class and both actual-map and equivalence
naturality. Stock linters and standard-only axioms pass. All 102 prior leaves
remain byte-identical and retain their earlier compilation evidence.

The signed-chart extension keeps 103 leaves and adds one public theorem,
for 51 added exports. It compares the actual chart/excision maps after
translation to the model origin using the determinant sign of the actual
coordinate transition. No chosen orientation is required by the new theorem.
The previous orientation-preserving equality is now a corollary with its exact
public statement retained; the compact oriented-chart class proof is unchanged.

LocalOrientation and root freshly compiled in Slurm 13821107, request
`1789296881793495986-topology_checkpoint-0b7eb007`, in 1:11.42 with maximum
RSS 1944864 KiB and zero diagnostics. Final request
`1789297108056477917-topology_checkpoint-27c4be25` passed in 88.14 seconds
after removing a duplicate universe declaration in the combined consumer.
Production sources were unchanged. All 212 guards and 115 signature/axiom
pairs pass; the 111 prior pairs are byte-identical. New consumers check
nonzero local classes under arbitrary overlapping charts and the actual
Euclidean3 model. Stock linters and standard-only axioms pass. The other
102 leaves remain byte-identical and retain their earlier build evidence.

The compact-gluing and fundamental-class extension adds one leaf, for 104
modules and 55 added exports. A locally realized family determines a unique
compact relative class, and a unique absolute class when the manifold is compact.
If the manifold is nonempty and connected and each local class generates its
integral group, the absolute class generates global homology and every actual
point restriction is bijective. The proof uses actual Mayer–Vietoris gluing,
compact point detection, local vanishing and connectedness. It assumes neither
an absolute class nor a preconstructed global homology isomorphism.

Final portable request `1789299823301815112-topology_checkpoint-2584f507`
passed in Slurm 13821107 in 159.33 seconds. Changed ManifoldCompactHomology,
new ManifoldFundamentalClass and root freshly compiled without diagnostics
in 1:32.34, maximum RSS 1937172 KiB. All 222 guards and 120 signature/axiom
pairs pass; all 115 previous pairs are byte-identical. The new consumer produces
an actual nonzero rank-zero global generator with coordinate one. Stock
linters and standard-only axioms pass. The other 102 leaves remain unchanged.

The relative-cochain extension adds one coherent leaf, for 105 modules and
80 added public exports. It constructs the actual kernel of singular-cochain
restriction, its inclusion and pair maps, and the induced relative cohomology
maps. Identity, composition, evaluation and naturality equations expose the
original maps. Degreewise extension of cochains makes the actual sequence
short exact, giving its connecting map, naturality and all three exactness laws.
No compactness or manifold hypotheses are needed; all natural degrees are included.
The private degreewise chain retraction is not asserted to be a chain map.

Final portable request `1789303157293002715-topology_checkpoint-d51aac36`
passed in Slurm 13821107 in 143.79 seconds. The new leaf and root freshly
compiled without diagnostics in 1:14.73, maximum RSS 1778808 KiB. All 230 guards
and 147 signature/axiom pairs pass; all 120 previous pairs are byte-identical.
The 25 new public and two consumer readbacks match the original imported gate.
Consumers test a relative degree-zero cochain with value one on the actual
constant-one singular simplex, and connecting-map naturality for x ↦ 2x.
Stock declaration linters and standard-only axioms pass. All 104 previous
leaves remain byte-identical and retain earlier compilation evidence.
This is a foundation for cohomological excision and duality, not a cap-product
or Poincare-duality theorem.

The cohomological-excision extension adds one coherent 321-line leaf and two
public theorems, for 106 modules and 82 added exports. It proves a
quasi-isomorphism for the actual relative-cochain pair map and bijectivity
of the actual induced cohomology map in every natural degree, for any two
open sets covering the original space. It reuses the small-chain inclusion,
projective-complex homotopy equivalence, the public cochain-extension theorem
and the actual relative-cochain kernel. Comparison and gluing mechanics remain
private; no second chain or cohomology theory is introduced.

Final portable request `1789305906138803485-topology_checkpoint-d1009f2e`
passed in Slurm 13821107 in 135.55 seconds. The new leaf and root freshly
compiled in 1:06.21, maximum RSS 1813796 KiB, with zero diagnostics. All 238 guards
and 151 signature/axiom pairs pass; all 147 previous pairs are byte-identical.
Both new public and two consumer readbacks match the original imported gate
up to scoped set notation. Consumers test actual punctured-real-line excision
and unique inverse images under the actual map in every natural degree.
The source gate also checks evaluation of the dual-to-kernel comparison on
original singular chains. Stock declaration linters and standard-only axioms
pass. All 105 earlier leaves remain byte-identical. Actual cap products,
normalization and the Poincare-duality isomorphism still require proofs.

The cap-product extension adds one coherent 433-line leaf and six public
exports, for 107 modules and 88 added exports. It uses the original singular
chains, cochains, differential and augmentation. The front/back simplex formula
is explicit, and naturality uses the original maps. The boundary identity has
the standard degree sign; a cocycle caps cycles to cycles in positive output
degree. The augmentation acts as the identity in every degree, including zero.
Simplex-index, summation and degree-transport mechanics remain private.

Final portable request `1789311873800562167-topology_checkpoint-2d616ff1`
passed in Slurm 13821107 in 144.28 seconds, with 246 guards and 160 signature/
axiom pairs. All 151 previous pairs are byte-identical. New CapProduct and the
root freshly compiled without diagnostics in 1:11.29, maximum RSS 1814116 KiB.
All 106 prior leaves are unchanged. The six public and three consumer readbacks
match the original imported gate. Consumers test a nonzero degree-zero vertex,
its images under augmentation and negative augmentation, the actual unit
cocycle and the negative sign in the degree-one boundary law. Stock declaration
linters and standard-only transitive axioms pass. Source dea3b95f separately
checks every private helper. That chain-level checkpoint did not yet include
homology/cohomology descent, relative cap products or the Poincare-duality
isomorphism.

The cap-homology extension adds one coherent 381-line leaf and eight public
exports, for 108 modules and 96 added exports. The actual integral cap product
descends through both canonical cycles/boundaries quotients, giving
H^k(X; Z) →L (H_(k+m)(X; Z) →L H_m(X; Z)) for every space and natural k,m.
Its representative law uses the public cycle map and the original chain cap
product. Naturality uses the original cohomology and homology maps. The actual
constant-one cocycle defines the unit in H^0; cap with that unit acts by the
canonical degree identification in every degree. The unit is natural under
all continuous maps. Boundary witnesses, quotient lifts and degree transports
remain private. No new chain or homology representation is introduced.

Final portable request `1789315948183120646-topology_checkpoint-62c7e035`
passed in Slurm 13821107 in 152.18 seconds, with 254 guards and 171 signature/
axiom pairs. All 160 prior pairs are byte-identical, and all 107 prior leaves
are unchanged. CapHomology and the root freshly compiled without diagnostics
in 1:15.15, maximum RSS 1814324 KiB. The eight public and three consumer
readbacks match original imported 204a2b9d, which passed in 98.08 seconds with
42 guards and 11 pairs. Source 57c362c8 passes in 44.16 seconds with 40 guards
and 24 pairs, checking every private helper as well.
Consumers prove nonzero H0 and H^0-unit classes, identity and negative-unit
action on actual homology, actual-map naturality for doubling, and the degree-one
cohomology/degree-two cycle representative formula. Stock declaration linters
and standard-only transitive axioms pass. Relative cap products, the duality
isomorphism and the complete orientation-to-duality theorem remain open.

The connected degree-zero cohomology extension adds one 178-line leaf and seven
public exports, for 109 modules and 103 added exports. Actual singular H^0 of
any path-connected space is linearly equivalent to the integers, normalized by
the actual constant-one unit. The inverse is integer multiplication of that
unit. Its coordinate on a cocycle class is evaluation at any actual vertex;
the equivalence is natural under the original cohomology maps. Cap with any
degree-zero class acts on actual homology by that normalized integer. The
actual cap map with a fixed homology class is bijective exactly when integer
multiplication of that class is bijective. This is a generator criterion;
it does not assert a general Poincare-duality isomorphism.

Final portable request `1789317973755893458-topology_checkpoint-3343921c`
passed in Slurm 13821107 in 154.94 seconds, with 262 guards and 181 signature/
axiom pairs. All 171 previous pairs are byte-identical, and all 108 previous
leaves are unchanged. ConnectedZeroCohomology and the root freshly compiled
without diagnostics in 1:14.10, maximum RSS 1812808 KiB. The seven public and
three consumer pairs match original imported 18a032ba, which passed in 82.01
seconds with 49 guards and ten pairs. Final source b66ae903 passes in 6.80
seconds with 47 guards and 15 pairs, including every private helper.
Consumers check a nonzero class with normalized coordinate -3, bijectivity of
the actual cap map with a vertex class, negative-unit action, and the actual
doubling map inducing the identity on H^0. Stock declaration linters and
standard-only transitive axioms pass. Relative cap products, general duality
and the native orientation producer remain open.

The relative cap-product extension adds one coherent 234-line leaf and six
public exports, for 110 modules and 109 added exports. It descends the existing
ordinary cochain cap product to the original categorical relative chain complex.
The projection equation, naturality under actual continuous pair maps, signed
boundary identity, augmentation unit and cycle preservation hold in every
natural degree and topological space. This is an absolute-cochain/relative-chain
pairing; it does not assert a general relative cohomology pairing or duality.

Final portable request `1789320638820840783-topology_checkpoint-ed0e45ce`
passed in Slurm 13821107 in 145.89 seconds, with 270 guards and 189 signature/
axiom pairs. All 181 previous pairs are byte-identical and all 109 previous
leaves are unchanged. RelativeCapProduct and the root freshly compiled without
diagnostics in 1:13.41, maximum RSS 1814244 KiB. The six public and two consumer
pairs match original imported 7a8adef4 up to scoped set notation; that gate
passed in 69.03 seconds with 41 guards and eight pairs. Source c465c911 passed
in 30.60 seconds with 39 guards and 14 pairs, including every private helper.
Consumers check a nonzero actual projected vertex, identity and negative-unit
actions, and naturality for doubling on the pair (real line, nonpositive
halfline). Stock declaration linters and standard-only transitive axioms pass.
Relative homology descent and general Poincare duality remain open.

The relative cap-homology extension adds one coherent 337-line leaf and seven
public exports, for 111 modules and 116 added exports. It constructs the actual
bilinear pairing H^k(X; Z) x H_(k+m)(X,A; Z) -> H_m(X,A; Z), in every natural
degree and topological space. The public cycle map and its value formula pin
this pairing to the original relative chain cap product. Its class formula,
naturality under the original pair and cohomology maps, actual constant-one
unit, and compatibility with absolute-to-relative projection are proved.
Mathlib's existing bilinear quotient lift and the original categorical homology
isomorphisms perform the descent. Boundary witnesses and integer-module
elaboration helpers remain private. No new chain or homology representation
is introduced. This is ordinary cohomology acting on relative homology; a
relative-cohomology pairing and the duality isomorphism are separate steps.

Final portable request `1789323402557190933-topology_checkpoint-28c15b3f`
passed in Slurm 13821107 in 151.30 seconds, with 278 guards and 200 signature/
axiom pairs. All 189 previous pairs are byte-identical and all 110 previous
leaves are unchanged. RelativeCapHomology and the root freshly compiled without
diagnostics in 1:13.03, maximum RSS 1814496 KiB. The seven public and four
consumer pairs match original imported 80bb4f3a up to scoped set notation;
that gate passed in 72.44 seconds with 54 guards and eleven pairs. Final source
d9b0d60a passed in 15.67 seconds with 52 guards and 21 pairs, including every
private helper. Consumers check nonzero relative H0 with unit and negative-unit
action, actual doubling pair-map naturality, the degree-one/degree-two cycle
formula, and compatibility with the original relative-empty equivalence in
all degrees. Stock declaration linters and standard-only transitive axioms
pass. General Poincare duality and the complete oriented-manifold suite remain open.

The connecting-map extension adds ModuleHomologyConnecting (48 lines) and
RelativeCapConnecting (124 lines), for 113 modules and 118 added exports.
The general formula computes the original connecting map on concrete cycle
classes for arbitrary rings and complex shapes. It uses Mathlib's existing
connecting-map computation. The topological theorem proves
`δ(α ∩ c) = (-1)^k (i*α ∩ δc)` on the actual integral groups for any pair,
any cohomological degree k and every nonnegative output degree. Actual chain
lifts, the existing signed boundary formula and naturality supply the proof.
No new homology object or assumed compatibility law is introduced.

Final portable request `1789325313509362620-topology_checkpoint-9c71d0f8`
passed in Slurm 13821107 in 177.11 seconds, with 289 guards and 205 signature/
axiom pairs. All 200 prior pairs are byte-identical and all 111 prior leaves
are unchanged. The two new leaves and root freshly compiled in 1:30.09,
maximum RSS 1815000 KiB, with zero diagnostics. The two public and three
consumer pairs match original imported dc5e47d2, which passed in 96.53 seconds
with 130 guards and five pairs. Its two fresh leaves took 55.92 seconds with
maximum RSS 1581632 KiB and zero diagnostics. Final source 377c15d2 passes
in 10.71 seconds with 127 guards and nine pairs, including every private helper.
Consumers check the negative degree-one and positive degree-two signs and an
actual relative H1 class of the real line modulo its unit zero-sphere with
nonzero connecting image preserved by cap with the unit. Stock declaration
linters and standard-only transitive axioms pass. General Poincare duality
and the complete oriented-manifold suite remain open.

The relative-to-absolute cap extension adds one coherent 226-line leaf and six
public exports, for 114 modules and 124 added exports. It constructs
`C^k(X,A; Z) x C_(k+m)(X,A; Z) -> C_m(X; Z)` on the original relative cochain
kernel and relative chain cokernel. Naturality of the original cap product
shows that cochains vanishing on A annihilate chains from A, so the quotient
lift has absolute output. Its original projection formula, compatibility with
the earlier relative cap product, pair-map naturality, signed boundary identity
and cycle preservation are proved in all natural degrees and topological spaces.
No alternative chain representation or compatibility assumption is introduced.

Final portable request `1789328051059665070-topology_checkpoint-3eafcb3e`
passed in Slurm 13821107 in 160.12 seconds, with 297 guards and 214 signature/
axiom pairs. All 205 prior pairs are byte-identical and all 113 earlier leaves
are unchanged. RelativeCapToAbsolute and root freshly compiled in 1:14.06,
maximum RSS 1813376 KiB, with zero diagnostics. The six public and three new
consumer pairs match original imported c9515b2c, which passed in 80.48 seconds
with 60 guards and ten pairs; its unchanged cochain producer is reused in the
portable harness. Final source 98ee7c44 passes in 44.28 seconds with 58 guards
and 14 pairs, checking all private helpers. Consumers check a nonzero actual
relative vertex with positive and negative cap values, the odd-degree boundary
sign and actual doubling-map naturality. Stock declaration linters and
standard-only transitive axioms pass. Descent of this pairing to relative
cohomology and absolute homology, and general duality, remain open.

The relative-to-absolute homology extension adds one coherent 343-line leaf
and seven public exports, for 115 modules and 131 added exports. It constructs
`H^k(X,A; Z) x H_(k+m)(X,A; Z) -> H_m(X; Z)` using the original relative
cochain and chain complexes and actual absolute homology. The cycle map,
representative formula, naturality under actual pair maps, compatibility with
absolute-to-relative projection on output, and compatibility with projected
absolute input are proved. Signed boundary witnesses and Mathlib's bilinear
quotient lift give the descent through both actual cycles/boundaries quotients.
No alternate homology representation or assumed compatibility is introduced.

Final portable request `1789329891086424933-topology_checkpoint-e37273b4`
passed in Slurm 13821107 in 165.88 seconds, with 305 guards and 225 signature/
axiom pairs. All 214 prior pairs are byte-identical and all 114 earlier leaves
are unchanged. RelativeCapToAbsoluteHomology and root freshly compiled in
1:18.25, maximum RSS 1812900 KiB, with zero diagnostics. All seven public and
four consumer pairs match original imported 3bbfb6aa up to scoped set notation;
that gate passed in 80.21 seconds with 69 guards and eleven pairs. Final source
da3ec091 passed in 18.51 seconds with 67 guards and twenty pairs, including
all private helpers. Consumers produce a nonzero relative cohomology class for
the empty pair whose positive and negative cap actions on a nonzero homology
class are the identity and negation. They also check actual doubling pair-map
naturality and the positive-degree cycle formula. Stock declaration linters
and standard-only transitive axioms pass. General duality and the full native
oriented-manifold theorem suite remain open.

## Remaining topology work

The bridge from tangent orientation must still produce the coherent local
generators consumed by the new global theorem. Simply connected orientability,
integral duality, outward sphere normalization, normalized homotopy and loop-family
classes, and canonical width specializations remain open. This checkpoint does
not claim the full oriented-manifold theorem suite.

The separate frozen 87-declaration handoff, its registry and consumers, and
`handoff/CANONICAL_TOPOLOGY_READY.md` remain unavailable. This package does not
replace that contract or assert completion of T1--T9/C1--C5. It introduces no
deferred inputs. The recovered full Poincare project remains separate from this
selected source checkpoint.
