# Current collapse changes — September 30, 2026

Curvature-radius positivity, the infinite-radius/nonnegative equivalence, finite-radius volume reformulation, common derivative bounds, compact whole-carrier bounds, boundary partition matching, monotonicity, order restriction and closed/boundary exclusion now have proofs. `exists_closed_graph_threshold` is a proved case split from `exists_closed_graph_threshold_of_finite_scales` and the separate nonnegative branch. The strict r<Rp is PBR03's convention, not the differing KL14 table. The boundary producer keeps its explicit component bijection; `RawGraphPresentation.external_matching` independently derives such a bijection, but does not identify a finite-C cusp parametrization with a smooth graph collar.

The nonnegative branch is now a proved composition of a geometric classification admission and three graph-recognition admissions. Classification returns an actual complete spherical, spherical-product, or flat metric on the same compact carrier; it does not preserve the original metric. The spherical-product supplier includes RP³#RP³ as well as S²×S¹. The flat supplier includes all orientable compact flat quotients. Chow–Lu–Ni GSM77, label `seac 3-manifolds with nonnegative curvature`, TeX18472–18708 was freshly read; model-metric realization remains an explicit adapter. The precise graph suppliers are Blueprint FC41 contracts, with Matveev's graph/connected-sum conventions freshly compared.

The two finite-scale/boundary thresholds remain coarse admissions: genuine LC87 local fibration/zero/edge/slim packets, cloud compatibility, and BSA collar incorporation have not been implemented. Their replacement by a renamed RawGraphPresentation would not constitute the requested split. No such placeholder was installed. KL14 Theorem16.1 is used only through the Blueprint record A:19797–19832; the scanned source was not newly read.

Conventions retained: intrinsic length distance and volume in the actual compact carrier; diameter measured in that same carrier; one-sided derivatives at manifold boundary; arbitrary flat reference torus; cusp metric ds²+e^(−s)h of curvature−1/4; C^(K+1) embedding and relative C^K metric error; no literal extension of finite-C metrics to the existing smooth-only curvature API. Numerical constants are `cuspDepth=100`, `boundaryBufferDistance=10`, `staticDerivativeOrder=10`, and `lateDerivativeOrder=20`. The volume constant is `euclideanThreeUnitBallVolume`. The κ=0 infinite-scale branch stays separate from real-radius calculations.

The E1 endpoint requires finite volume only for hyperbolic tags. The SL₂ coframe's Lean coordinate is the logarithm of the positive upper-half-plane height: with v=exp(y), dv/v=dy and dx/v=exp(−y)dx, the existing coframe matches the GM03 displayed formula. No model coframe was changed. KL Remark92.4 is the primary finite-order context; it does not by itself prove the stronger whole-ball skeleton test.

Current evidence supersedes the compilation/admission status in the historical review below.

---
# Static collapse skeleton: statement and corner-case review

This is the principal static interface and common-parameter skeleton against
blueprint207, not a formalization of every local model, cloud, or atlas node.
The seven admitted theorem bodies are deliberate `sorry` producers requested by the
user. Their downstream threshold/composition theorems are ordinary Lean proofs
and consequently still depend on `sorryAx`. No metric, curvature, volume, collar,
graph presentation, or hypothesis is defined using `sorry` or an arbitrary `Prop`.
No pre-existing proved source was edited.

## Contracts actually reread

- `master207A.tex` lines19751–19925, independent source comparison; LC81 at
  24760–24808; LC88 at31096–31163; LC89 at31165–31204; LC90 at31206–31253.
- `master207B.tex` lines7549–7590, FC43 and the intrinsic boundary convention;
  PBR03 at10277–10339; BBR03 at10592–10651; CAA02 and retained foundations
  at10774–10826; FC45 at10828–10848; FC46 at9979ff.
- Retained source and category reviews: `reference_checks_revision143.md` and
  `reference_checks_revision159.md`. The finite model route uses finite metric
  regularity, with the documented losses, and never upgrades a metric by merely
  smoothing its atlas.
- Fresh body extraction of the archived Kleiner–Lott *Locally collapsed
  3-manifolds*, Asterisque365 (2014),
  `BooksPapers/KleinerLottAsterisqueLocalCollapse.pdf`, SHA256
  `7a860b4dd95b35fe33b06bf040100ec243d72c80528d927f4763391aaf79cb6e`:
  Definition1.1–1.2 and Theorem1.3 printed8/PDF3;
  Definition3.4–Lemma3.5 printed22/PDF17;
  Lemma3.11 and its compact/no-ends proof printed24–25/PDF19–20;
  Section15 recognition/gluing printed86/PDF81;
  Proposition15.3, Section15.2/(15.4), Theorem16.1 and proof setup,
  Lemmas16.4–16.5 printed87–89/PDF82–84.
  This was targeted source reading, not a new audit of the entire article.
- Fresh external body check on September28,2026 of the author's correction
  sheet at <https://math.berkeley.edu/~lott/corrections.pdf>, one page dated
  May15,2015. Its three corrections remain the interval in6.5, the omitted
  3-ball in14.1(2), and the pointed rescaling/basepoints in20.2. None changes
  the principal theorem contracts declared here. No Morgan–Tian theorem is
  substituted for the selected KL output definition.

## Declarations and meaning

`CurvatureScale.lean` defines balls and volumes through the accepted metric's
actual intrinsic Riemannian distance and volume measure. `curvatureRadius` is
extended-real: the supremum of positive radii on which sectional curvature is
at least minus the inverse squared radius. Positivity and its equality to
infinity precisely for nonnegative curvature on a compact connected carrier
are admitted helper theorems. The real volume-collapse test only evaluates
finite positive radii equal to that scale; it never evaluates infinity cubed.
The static closed producer retains the globally nonnegative classification
branch. `exists_rawGraphPresentation_of_nonnegative` states that FC41/smooth
classification branch separately, without any derivative or collapse-radius
hypothesis; it can restore components removed before LC89. The definition is not a center-only curvature test.

The raw repeated tensor derivatives live in
`Geometry/Connection/TensorNabla/Iterated/Metric.lean`, and the curvature norm
in `Geometry/Curvature/Metric/DerivativeNorm.lean`. The final placement review
searched the accepted `tensor0SCovariantDerivative` and `totalNabla0SFun` APIs:
the latter requires a globally smooth bundled section, whereas the new raw
iteration must also evaluate finite-regularity pulled-back tensors. It reuses
the canonical coordinate operation and actual Levi-Civita connection; no
alternate connection geometry or compatibility aliases were introduced.
The iterated tensor derivative uses the existing Levi-Civita connection and
existing chartwise covariant tensor derivative operation. It accepts raw tensor
sections so that finite-regularity pulled-back metric errors are meaningful;
no artificial smoothness is imposed on the finite-regularity cusp map.
`curvatureDerivativeNorm` is the actual Hilbert–Schmidt tensor norm.
`curvatureDerivativesControlled` quantifies over every point in each triggered
ball, every integer0≤k≤K, every w0≤w<4π/3 and every0<r<Rp.

`Hyperbolic/Cusp.lean` is the shared exact cusp object, placed in its mathematical
home. It uses an arbitrary flat smooth metric on the actual torus and the exact
metric formula dz²+exp(-z)gT on the half-cylinder. The sectional curvature −1/4
calculation is an admitted theorem. No bound on lattice aspect ratio is imposed.

`CuspBoundary.lean` has actual C^{K+1} embeddings/immersions of pairs of the
open depth100 half-cylinder, including its boundary, into the original carrier.
The C^K error is measured by covariant derivatives with respect to that exact
reference metric on the same whole collar. Its finite connected closed disjoint
boundary sets cover the original boundary, so they are its actual components.
`count_pos` retains nonempty boundary. The diameter is computed using the same
intrinsic carrier distance as the volume and curvature tests. Boundary collapse
is requested only where intrinsic distance to boundary is strictly greater than10.

`GraphManifold.lean` declares the selected PBR03 and BBR03 producers with
quantifier order

    forall K>=10, forall A positive on(0,omega3), exists w0 in(0,omega3),
      forall compact connected oriented smooth carriers W and metrics g, ...

A is real-valued, hence finite, and has no monotonicity/continuity assumption.
The hypotheses contain no graph-manifold predicate or existence of the target.
The output is the genuine `GC.GraphManifold.RawGraphPresentation W` on the same
carrier: finite collared torus cuts into regular circle bundles over surfaces.
No incompressibility, prime decomposition, complete geometric metrics, flow
construction, or reconstruction of the initial manifold is asserted here.
The boundary producer additionally returns an explicit bijection between the
supplied cusp boundary indices and the produced external torus indices, with
actual image-set equalities. It does not claim a finite-C cusp parametrization
is identical to a smooth graph collar.

The common-threshold theorem is proved by taking the minimum of the two
thresholds. Smaller thresholds strengthen collapse/closeness and enlarge the
required derivative-trigger interval; all three monotonicities are proved.
The componentwise theorem uses the same K,A,w0 on all original component
carriers, and retains each component index. A finite family of size zero is
allowed; an individual connected carrier is nonempty. This is the static
componentwise part of LC90, not production of the late flow carriers.

`UniformDerivativeBounds.lean` states LC89 with actual carriers, metrics,
curvature derivatives and balls. It retains a finite radius bound and a finite
whole-carrier derivative bound for each sequence member. The tail N may depend
on w; one global tail over an interval of w is not assumed. The output A is
fixed for all sequence members before any static w0 is chosen. Nonnegative
components cannot be silently passed through the finite-radius-bound premise.
Its elementary finite-initial-segment proof is currently admitted.

## Double-check findings and fixes

1. Use the active PBR03/BBR03 strict radius r<Rp and boundary distance>10.
   Earlier historical blueprint rows with r≤Rp or distance≥10 are not silently
   conflated with this selected contract.
2. The boundary-label cross-review initially found that an unlabeled existential
   raw presentation could lose the supplied indices. The producer was revised
   to return the explicit index equivalence and image equalities above; its
   generic common-threshold corollary intentionally forgets this extra field.
3. Empty boundary is the separate closed disjunct. No boundary collar is requested
   for it. Although the extended infimum definition of boundary distance is
   mathematically valid for an empty set, no closed theorem uses that value.
4. Infinity is retained in curvature scales, but never passed to real powers
   or ball-volume evaluation. Nonnegative classification remains a proof
   obligation of the admitted closed producer.
5. A source copy and its theorem are not themselves an adapter: actual intrinsic
   balls, the whole-ball derivative norm, the exact reference cusp and actual
   maps are encoded. Ambient-flow to intrinsic-carrier transport remains separate.
6. The finite-C^K local model output is NOT represented by a smooth-metric
   structure or a conclusion-only dummy proposition. This bounded pass does not
   provide LC81/local packet/cloud/smoothing/parameter-register node statements.
   They remain unrepresented subproducers, not claimed covered by this manifest.

A further integration audit found that the first proposed global long-time
statement quantified A before choosing the actual flow and promised all late
slice estimates. TCF06 instead has the explicit order K, fixed flow, proposed
bad sequence, A, static threshold, late sequence index. The root task corrected
its analytic producer to that sequential order, and the final
`hasLateSequenceTests` and its contradiction proof were independently reread.
The scalar barrier retains its positive initial-data-dependent time shift. Its separate nonnegative
constructor must use the classification producer above, not ask for finite
curvature-radius bounds. `TorusDecomposition.lean` was independently checked:
the collapsed component metric is literally the pullback of the fixed slice
metric along the actual cut/reconstruction map, and the application retains
that exact component's carrier. No ambient-to-intrinsic ball assertion occurs
in this assembly lemma.

The separate bounded finite-category coefficient extraction and metric pullback
leaves were independently checked: K=1 gives C0 convergence, empty U is vacuous,
and m=4 gives a continuous metric pulled back by a C1 diffeomorphism. None
asserts an entire finite-regularity limit atlas, completeness, or a smooth metric.

The topology agent independently reviewed the metric/collar/static contracts;
this agent independently reviewed its concrete raw graph and endpoint-refinement
contracts. These are mathematical statement reviews, not proofs of admitted
producers. Neither review is advertised as a full fresh audit of blueprint207.

## Checks actually run

- `LEAN_NUM_THREADS=2 lake build DifferentialGeometry.Geometry.Collapse.GraphManifold`
  succeeded, including the final seven-leaf dependency placement. The final
  combined target build also included UniformDerivativeBounds (4412 cached jobs).
- The same bounded build for `...Collapse.UniformDerivativeBounds` succeeded.
- `#print axioms` on the two threshold/composition theorems and the uniform
  derivative producer includes `sorryAx`, as expected. The hypothesis monotonicity
  proof uses only propext, Classical.choice and Quot.sound.
- No full-root rebuild, no PC-foundation edit, and no standalone Lean file outside
  DifferentialGeometry were performed by this subtask. The root task owns
  aggregation, branch verification and publication.
