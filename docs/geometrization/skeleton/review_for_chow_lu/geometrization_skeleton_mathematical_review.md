# Reading guide and actual proof map {#overview}

## Scope, authority, and how to read this report {#reading-guide}

This report describes the Lean skeleton at commit
`ea0fae60ee01ef8c8d9b57a51794c6538f679c5d`, on the private branch
`codex/geometrization-blueprint-skeleton-207`. The associated mathematical
blueprint is revision 207. The report translates the code as it stands; it
does not silently add hypotheses, strengthen outputs, or supply missing
geometric constructions. No Lean mathematical source is changed by this report.

The immediate review question is: **Are these the mathematical objects and
claims that we intend to formalize, and are their stated assumptions sufficient?**
A second, separate question is whether their current decomposition gives
independent formalizers sufficiently precise tasks. A true but very large
existence theorem can be acceptable for the first question while still being
too coarse for the second.

The skeleton adds 22 mathematical files and 121 explicitly authored
declarations. Of its 55 named theorems, 17 have `sorry` proofs and 38 have
written proof terms. Some of those 38 proofs use admitted theorems. The
other declarations define objects, conditions, structures, or abbreviations.
The compiler also generates constructors, projections, and auxiliary
declarations; the corresponding audit covers 542 declarations.

We use four status descriptions throughout:

| Status | Mathematical meaning |
| --- | --- |
| Definition | The displayed data or condition is what the Lean name means; no existence theorem follows merely from defining it. |
| Admitted | The statement is asserted using `sorry`. It remains a mathematical and formalization obligation. |
| Proved, conditional | The code supplies a real argument from explicit hypotheses or admitted upstream results. It does not prove those inputs. |
| Proved, independent of the new admissions | The code supplies a proof using the inherited library and none of the 17 new `sorry` statements. This is not a fresh audit of the entire inherited library. |

In mathematical prose, “there exists data” translates Lean's `Nonempty` or
existential quantifier. It does not mean that the data is computable or
canonically selected. “Smooth” means $C^\infty$, unless a finite order is
explicitly written. “Connected” includes nonempty in the relevant Lean
manifold structures. A finite set or family may be empty unless positivity
of its size is explicitly required.

For an efficient first reading, review the exact endpoint, the six main
admissions, the order of quantifiers in the selected-flow claim, and the
written contradiction/assembly proof. Then review the detailed collapse,
hyperbolic/area, topology, and finite-regularity sections. The declaration
register provides a route back from every one of the 121 names to its
translation and original file. The source snapshot and its hashes are the
authority when checking a formula or a binder.

## The proof that is actually assembled {#actual-proof-map}

The following is the mathematical shape of the present endpoint proof.
It is not a claim that the analytic inputs have been proved.

1. Start with an arbitrary connected, compact, boundaryless, oriented smooth
   three-manifold $M$. Obtain an arbitrary smooth Riemannian metric $g$ from
   the inherited metric-existence theorem.
2. Invoke the admitted **selected-flow theorem**, at derivative order $K=20$.
   It supplies one surgery flow with an additional sequence-level late
   decomposition property. A merely existing raw surgery flow does not
   suffice.
3. Suppose that arbitrarily late nonempty regular slices fail to have
   geometrized components. Choose one such bad slice at a time $t_j>j$ for
   every integer $j\geq0$.
4. For this fixed flow and this fixed sequence, the selected-flow property
   gives one function $A(w)$ controlling the required finite-order derivative
   tests on the collapsed cut pieces.
   The static collapse theorem is then used to choose one tolerance $w_0$.
   The flow property gives a sufficiently late index $N$ valid for all later
   slices in the sequence and all their connected components.
5. Every cut piece of the selected component at index $N$ is either an
   actual complete finite-volume hyperbolic interior, an intrinsically
   collapsed piece with its induced normalized flow metric, or a closed
   nonnegative-curvature piece. Static recognition turns the last two kinds
   into raw graph presentations.
6. If one of the actual cutting tori failed to inject on fundamental groups,
   the selected-flow property would supply a nonnegative physical disk-area
   function on a future half-line with an impossible differential upper
   barrier. The admitted scalar area lemma rules this out. Thus the actual
   cutting tori are incompressible in the component being decomposed.
7. The admitted **mixed graph/hyperbolic refinement theorem** supplies prime
   factors and geometric decompositions. The written assembly turns those
   outputs into the existing geometrization certificate. This contradicts
   the choice of the bad slice. Consequently all sufficiently late nonempty
   regular slices have geometrized components.
8. The inherited reconstruction theorem uses a finite observed surgery
   history, standard discarded-factor geometries, and its recorded smooth
   identifications to recover a certificate for the original $M$. If the
   flow has an actual empty observation, the existing empty-observation
   branch supplies the reconstruction instead. No finite-extinction theorem
   is assumed for all initial manifolds.

Only **six** of the new admitted statements occur in the declaration
dependency closure of this proof:

| Main admitted input | Content |
| --- | --- |
| Selected flow | One flow with the exact late-sequence tests and common neck accuracy described below. |
| Closed static collapse | A compact connected closed carrier satisfying the chosen intrinsic collapse tests has a raw graph presentation. |
| Boundary static collapse | The corresponding assertion with the explicit nearly cuspidal boundary conditions. |
| Closed nonnegative classification | A compact connected closed oriented three-manifold with sectional curvature at least zero has a raw graph presentation. |
| Shifted scalar area contradiction | A continuous nonnegative function cannot have the prescribed strict upper barriers forever. |
| Mixed graph/hyperbolic refinement | Actual incompressible torus gluing of graph and hyperbolic pieces yields the chosen prime/geometric endpoint data. |

The other eleven admissions are independent prepared statements: Mostow--Prasad
rigidity; a local hyperbolic atlas theorem; cusp curvature; positivity and the
infinite case of the curvature radius; common derivative bounds for a sequence;
finite-order metric pullback; finite-order coefficient compactness; continuity
of least exterior disk area from disk comparisons; and two raw-graph prime and
geometric refinement producers. Some have proved consumers of their own.
They are **not** already being applied inside the selected-flow or mixed
refinement `sorry`. A dependency edge suggested by the blueprint is not a Lean
application until the corresponding proof body actually uses it.

## What the successful build does and does not establish {#meaning-of-build}

The recorded full `DifferentialGeometry` build passed with 26,440 Lake jobs.
The new declaration audit checks the 542 elaborated declarations, permits
exactly the 17 registered direct admissions, and records their dependencies.
The existing baseline audit passed for 4,311 declarations. The 155 existing
GC baseline Lean modules, the accepted toolchain/dependency pins, and the
endpoint definitions were left unchanged by the skeleton.

These checks establish that the definitions are well-formed and the written
compositions type-check with the asserted admitted statements. They do not
establish that an admitted statement is true, that every mathematical name
matches its intended standard meaning, or that every source theorem has
already been translated correctly. Those are precisely the matters for this
review. A report with a faithful translation is evidence for review, not a
substitute for your mathematical approval.

The skeleton is the principal argument, not a node-by-node translation of
all 649 selected DAG entries. Canonical JSJ uniqueness, all relative marking
exports, every local collapse/cloud construction, and the full analytic
decomposition of the selected-flow claim are not supplied as separate Lean
interfaces here. The detailed sections identify narrower conclusions and
unexported data explicitly.


# The exact endpoint and the actual flow-to-endpoint argument {#endpoint-flow}

## E1. The initial manifold and the conclusion {#e1-endpoint}

The public theorem concerns every **connected, compact, Hausdorff,
boundaryless smooth three-manifold with a specified orientation**. Connected
includes nonempty. No metric, simple connectedness, finite fundamental group,
curvature bound, irreducibility, or primeness is assumed. It is a smooth
oriented statement. The displayed second formulation with explicit manifold
instances is the same smooth statement; the skeleton does not add a separate
Moise-based theorem about arbitrary topological three-manifolds or a theorem
about nonorientable manifolds.

Its conclusion is existence of the following data.

**Prime stage.** There is a finite **nonempty ordered list**
$P_1,\ldots,P_m$ of connected closed oriented smooth three-manifolds, each
prime, and an orientation-preserving diffeomorphism
$P_1\#\cdots\#P_m\longrightarrow M$. Here the actual definition of prime is:
for every pair of connected closed oriented smooth three-manifolds $A,B$, if
$P_i$ is smoothly diffeomorphic to $A\#B$, then $A$ or $B$ is smoothly
diffeomorphic to the standard $S^3$. The diffeomorphisms in this test of
primeness are not required to preserve orientation. The reconstruction of
$M$ is required to preserve orientation.

The definition does not exclude $S^3$ from the list and does not require the
list to be irredundant or canonical. Although the inherited finite connected
sum operation defines the sum of the empty list to be $S^3$, the certificate
itself requires a nonempty list. It does not assert uniqueness of the prime
decomposition.

**Torus-cut stage for each $P_i$.** There is a compact oriented smooth
three-dimensional carrier $C_i$, either boundaryless or modeled on the
three-dimensional half-space. It has a finite **positive** number of
pairwise disjoint connected clopen pieces covering it. Every piece's
intrinsic interior is also connected and nonempty. There are finitely many
pairs of boundary tori, with exact parametrizations, smooth matching maps,
and collars. Gluing these pairs gives an actual quotient, a smooth oriented
structure on that quotient, and an orientation-preserving diffeomorphism
from it to $P_i$. The boundary of $C_i$ is exactly the union of the paired
boundary tori; there is no unaccounted boundary.

Each glued seam torus is required to induce an injective homomorphism
$\pi_1(T^2,x)\to\pi_1(P_i,f(x))$ for **every** basepoint $x\in T^2$, using
the actual seam map followed by the actual reconstruction. The definition
supplies a signed smooth collar around each seam. Thus “torus cut” here is
not just an abstract graph or a collection of fundamental groups.

The number of seam pairs may be zero. Their left and right sides may belong
to the same connected cut piece, so nonseparating cuts are allowed. The data
record which piece owns each side. There is no canonical-JSJ, minimality,
nonparallelness, or uniqueness requirement. In particular, do not read
“essential tori” as silently including any additional condition beyond the
actual embedded collared seams and the stated fundamental-group injections.

**Metric stage.** On the entire intrinsic interior of every connected cut
piece there is a complete smooth Riemannian metric locally isometric to one
of the eight fixed models described next. Hyperbolic interiors must have
finite total Riemannian volume. No finite-volume condition is imposed on
the other seven model types. The metric need not extend over the boundary
of the compact cut carrier. No metric matching across the reglued tori is
required; these are complete metrics on the separate interiors.

These are the actual fields of `GeometrizationCertificate` and
`GeometricDecomposition`, unfolded through `PrimeDecomposition`,
`CompactCarrier.Components`, `TorusGluing`, and `SmoothAssembly`. These
definitions are inherited and unchanged by the new skeleton.

## E2. What “one of the eight geometries” literally means {#e2-models}

A geometric structure contains a model label, a smooth positive definite
metric $h$, completeness for its intrinsic Riemannian extended distance,
and a metric-preserving local smooth atlas from the designated model. On
the connected interiors in the endpoint this is the usual intrinsic metric
completeness condition. It is **not** a bare geometry label, a hypothesis
that an arbitrary homogeneous metric exists, or a metric on an unrelated
abstract manifold.

For the spherical, Euclidean, and spherical-product labels, the fixed
metrics are respectively the round unit $S^3$, Euclidean $\mathbb R^3$,
and the product of the round unit $S^2$ with Euclidean $\mathbb R$.
For the other five labels, the code uses the following coframes on
$\mathbb R^3$ with coordinates $(x,y,z)$. The model inner product is the
sum of the squares of the three displayed one-forms.

| Label | Fixed coframe |
| --- | --- |
| Hyperbolic | $e^{-z}dx,\ e^{-z}dy,\ dz$ |
| Hyperbolic product | $e^{-y}dx,\ dy,\ dz$ |
| Universal $\widetilde{\mathrm{SL}}_2$ | $e^{-y}dx,\ dy,\ dz+e^{-y}dx$ |
| Nil | $dx,\ dy,\ dz-x\,dy$ |
| Sol | $e^zdx,\ e^{-z}dy,\ dz$ |

More explicitly, at every point of a geometric interior there must be a
smooth partial diffeomorphism from an open subset of the selected model
whose target contains that point and which pulls the interior metric back
to the displayed model metric at every source point and on all tangent
vectors. The atlas is not required to be orientation-preserving. There is
no explicit discrete group, developing map, holonomy representation, or
maximal-isometry-group action in this endpoint record. The identification
of these fixed models with the standard eight geometries and the usual
global quotient interpretation are matters of the inherited model theory,
not extra fields that can be assumed present in the certificate.

The code also defines local and global homogeneity predicates elsewhere,
but neither is an additional field of `GeometricStructure`; the fixed
local-model atlas is its actual requirement. The finite-volume field is
the implication “if the label is hyperbolic, then the total volume is
finite,” not a blanket finite-volume requirement.

**Source dictionary.** The exact inherited definitions are in
`Geometrization/Prime.lean`, `Carrier.lean`, `Statement.lean`,
`TorusGluing.lean`, `SmoothTorusReconstruction.lean`, and
`Geometry/Thurston/{Atlas,Models,ModelAtlas,ElementaryModels}.lean`.
The review snapshot includes exact paths and source hashes.

## F1. The raw flow and its actual observations {#f1-raw-flow}

The selected-flow claim uses an existing type `RawSurgery(P,g)`. Here $P$
is a compact Hausdorff oriented smooth three-dimensional stage, possibly
disconnected or empty, and $g$ is a smooth Riemannian metric on that actual
stage. This type already contains considerably more than a sequence of
unrelated manifolds:

- For each integer $n\geq0$, an actual finite retained-core surgery history
  through time $n$, with a marked identification of its initial stage and
  initial metric with $(P,g)$.
- Strictly increasing event times beginning after time zero, incoming
  Ricci-flow slabs, output metrics, actual cut-and-cap transitions and
  retained-core maps, and a final regular slab whenever its interval has
  positive length. The flow equation and the stipulated time/spatial
  smoothness on these slabs are fields of the inherited history type.
- Compatibility under restriction from $[0,n+1]$ to $[0,n]$, including the
  initial identification. These are coherent histories of one flow, not
  fresh choices for unrelated finite intervals.
- At every event: a singular incoming endpoint, the recorded boundary-frame
  reversal, and the inherited standard classification of discarded
  components. These are the precise three clauses of `HistoryEventControl`.

Observation at a real time $b\geq0$ means: take the history through
$\lceil b\rceil$ and restrict it to $[0,b]$. The existing compatibility
theorems identify this with any longer observation restricted to the same
interval. Event times are locally finite. At an event time the active
stage is the post-event stage. Empty stages remain empty in later
observations.

The inherited library already constructs a `RawSurgery(P,g)`. The new
admitted selected-flow theorem asks for a flow with additional common
accuracy and late-geometric properties; it does **not** claim that every
raw flow, or the previously chosen arbitrary raw flow, has those properties.
No global canonical-neighborhood/noncollapse/parameter profile beyond the
fields actually stated below should be silently attached to the words
“raw flow.”

## F2. Regular slices, normalizations, and finite common-time selection {#f2-slices}

**Definition: `RegularSlice`.** For an observation tower, a regular slice
is a real time $t>0$ which is not an event time, together with the condition
that the start time of its last observed stage is strictly smaller than
$t$. Its history is exactly the observation through $t$; its stage is the
last stage of that history; and its metric is that stage's actual physical
metric at $t$. A regular slice is allowed to be empty.

The accompanying definitions `history`, `stage`, `metric`, and `initial`
are exactly these projections and the inherited initial identification.
The two new metric definitions are
$$
 \bar g(t)=t^{-1}g(t),\qquad \widehat g(t)=(4t)^{-1}g(t).
$$
They are called `normalizedMetric` and `curvatureOneMetric` respectively.
The name of the latter is not itself an assertion that the metric has
curvature $-1$. It is the normalization suited to a curvature $-1/4$
hyperbolic limit for $\bar g$. For a connected component $C$ of the actual
slice, `componentMetric` is precisely the restriction of $\bar g(t)$ to
that component's open subtype, not a newly chosen metric.

**Definition: arbitrarily late nonempty slices.** For every real $B$, there
is a regular slice at a time $t>B$ with nonempty stage. There is no assertion
that all towers have this property.

**Proved helper: regular times exist after every bound.** For every tower
and every real $B$, there is a regular slice later than $B$. This does not
assert that its stage is nonempty.

**Proved helper: empty slice or arbitrarily late nonempty slices.** Every
tower has an empty regular slice, or has arbitrarily late nonempty regular
slices. The displayed theorem is a disjunction, not an assertion that a
nonempty late component must survive. It is proved by negating the
late-nonempty property and then choosing a sufficiently late regular time.

**Proved helper: a finite common late slice.** Suppose a tower has
arbitrarily late nonempty regular slices. Given a finite set $I$ of
conditions $q_i$ on slices, assume for every $i\in I$ that some bound
$B_i$ makes $q_i$ true on **every** regular slice after $B_i$. Then, past
any additionally prescribed bound $B$, one can choose a nonempty regular
slice satisfying every $q_i$. The proof takes a finite maximum. The set
$I$ may be empty; the conclusion still requires a nonempty slice later
than $B$. This does not intersect arbitrary subsequences and does not take
a maximum over infinitely many derivative orders or thickness parameters.

**Proved reconstruction adapter.** If one particular `RawSurgery` from
$(M,g)$ has a bound $B$ after which every nonempty regular slice has a
geometrization certificate on each connected component, then $M$
geometrizes. This is `geometrizes_of_late_slice_supply`. Its proof passes
the supplied certificates to the existing reconstruction theorem for the
**same** tower. The empty-observation case is handled by that inherited
theorem; nonempty late slices need not be assumed separately.

The preceding selection and reconstruction adapters contain no new
admission of their own and do not need any of the 17 new admitted claims
when their stated hypotheses are supplied.

## F3. The actual cut carrier and its metric {#f3-induced-cut-metric}

Let $D$ be a torus decomposition of an actual connected closed oriented
component $M$, in the precise sense spelled out in the topology section:
an actual compact cut carrier, its connected pieces, paired boundary tori,
a smooth quotient atlas, and a reconstruction to $M$. At this point neither
incompressibility nor primeness is required in $D$.

For its $i$th cut piece $C_i$, define
$$
 q_i:C_i\longrightarrow M
$$
to be inclusion into the cut carrier, followed by the torus quotient map,
followed by the reconstruction. This is `cutPieceMap`.

For a given metric $g$ on $M$, `isInducedCutMetric(g,D,i,h)` is exactly
$$
 h_x(v,w)=g_{q_i(x)}\bigl(dq_i(v),dq_i(w)\bigr)
 \quad\text{for all }x\in C_i\text{ and all }v,w\in T_xC_i.
$$
The equality includes boundary points and uses the manifold derivative.
The cut piece metric $h$ is itself required to be a smooth Riemannian
metric. A favorable metric on an abstract diffeomorphic model cannot be
substituted without this equality.

**Definition: `HyperbolicOrCollapsed`.** For given $g,D,K,A,w_0$ and $i$,
the data have exactly one of the following constructor forms. The type
does not assert that the three cases are mutually exclusive.

1. A geometric structure on the **whole intrinsic interior** of $C_i$
   whose model label is hyperbolic. Completeness and finite volume are part
   of that structure. This hyperbolic metric is not required to equal the
   restriction of the finite-time flow metric $g$.
2. A smooth metric $h$ on $C_i$, the equality $h=q_i^*g$ above, and the
   selected static-collapse hypotheses with parameters $K,A,w_0$.
3. A smooth metric $h=q_i^*g$ on $C_i$, empty boundary, and sectional
   curvature at least zero everywhere.

Case 3 is explicitly separate: the assembly does not need to obtain a
finite curvature radius for a globally nonnegative closed component. In
case 2, balls, boundary distances and volume tests use the intrinsic
geometry of $C_i$ with $h$; they are not automatically ambient balls in $M$.
No comparison with ambient balls is smuggled into the definition.

**Proved conditional assembly.** Suppose every connected compact carrier
satisfying the static tests for the given $K,A,w_0$ has a raw graph
presentation. Suppose also that the actual seam maps of $D$ are
fundamental-group injective and that every cut piece has one of the three
forms just listed. Then $M$ geometrizes. The proof invokes the supplied
static theorem in case 2, the admitted nonnegative classification in case
3, and the admitted mixed graph/hyperbolic refinement for the resulting
collection. It does not prove any of those admitted producers. The written
topological assembly explicitly discards the induced-metric equalities.
Those equalities constrain what the geometric producer must supply; this
assembly does not use them or require them of the final geometric metrics.

## F4. What common neck accuracy actually requires {#f4-common-accuracy}

For a fixed flow $F$ and function $\delta:\mathbb R\to\mathbb R$,
`hasCommonNeckAccuracy(F,delta)` says:
$$
 \forall n\in\mathbb N\quad\exists p_n\quad
 \bigl(p_n.\delta=\delta\bigr)\ \text{and}\
 \bigl(\forall\text{ events }i\text{ in }F|_{[0,n]},\
       \exists\text{ a GeometricCutoffRecord for }i\text{ with }p_n\bigr).
$$
The equality of the delta functions is on **all real arguments**, not just
the event times. The other fields of $p_n$ may depend on $n$. In particular
the definition does not provide one global choice of the neck-radius and
protected-radius functions, cap scaffold, model radius, model order, model
accuracy, or recentering constant. Nor are records chosen for different
prefixes required to agree as data. The predicate is a precise common-delta
condition, not the full global analytic parameter register.

The parameter object contains positive neck-radius and protected-radius
functions on nonnegative times, $0<\delta(t)<1$ there, a cap scaffold,
positive model radius and model accuracy, a natural-number model order,
and a recentering constant at least $4$.

A cutoff record is an inherited, concrete geometric condition. To prevent
the abbreviation from hiding assumptions, its fields are summarized here:

- The incoming event is singular. If the cut index set is nonempty there
  is a positive common nominal radius $r$, satisfying
  $r<\delta(t)^2\,r_{\rm neck}(t)$ and $r^2\leq t$.
- Each cut has $0<\delta_\alpha\leq\delta(t)$ and a normalized neck of
  integer order at least
  $\max\{m+6,\,2\lfloor\delta_\alpha^{-1}\rfloor_++4\}$.
  Its metric scaling factor is $r^{-2}$. The neck buffers are pairwise
  disjoint, contain the actual tube domains, and their charts agree with
  the actual surgery tube maps. The incoming backward-neck condition is
  recorded for these necks and this radius.
- The retained set lies in the incoming terminal regular region.
  Points with scalar curvature at most $r_{\rm protected}(t)^{-2}$ lie
  in the interior of the actual retained set, and every retained connected
  core component meets that protected region.
- Exactly one side of each cut is retained. If there are no cuts, some
  point of the pre-event core is discarded. Retained boundary components
  have presented static caps with the chosen scaffold and model parameters.
- The recentered cap neck has scaling factor equal to the terminal scalar
  curvature at its center, the specified sphere marking, and accuracy
  $c\delta_\alpha$. Its relative scaling error is at most
  $c\delta_\alpha$. Its chart equals the original neck chart after the
  specified side-dependent change of axial coordinate
  $s\mapsto\pm(1+s)$, and the transformed domain lies in the original buffer.
- The event's old region is exactly the retained core. Every fixed
  Hamilton--Ivey region indexed by $a>0$ that contains the entire terminal
  regular metric is preserved on the output. Every scalar lower bound
  $L\leq0$ valid on that entire regular region is also preserved on the
  output.

The exact incoming-backward-neck and presented-static-cap notions are
inherited geometric structures, not newly admitted predicates defined as
`True`. Their detailed cap/neck fields remain part of the inherited PC
foundation boundary of this report. This field-by-field summary is not a
new mathematical source audit of those inherited structures.

## F5. The physical exterior-area obstruction {#f5-area-obstruction}

For a flow $F$, any connected closed oriented manifold $M$ with a torus
decomposition $D$, and any real $t_0$, the predicate
`hasExteriorAreaObstructionAfter(F,D,t0)` says the following for **each seam
index $i$ and each torus basepoint $x$**. This predicate alone does not
identify $M$ as a flow component or $t_0$ as its observation time. In F6,
the surrounding late-sequence predicate supplies those exact identifications.

If the actual reconstructed seam map fails to inject on fundamental groups
at $x$, then there exist numbers $T,c$, subsets $W(t)$ of the actual
post-event stage $M_t$ of this **same** flow, and parametrized continuous
loops $\gamma_t:S^1\to M_t$ for $t\geq T$, such that
$$
 T\geq0,\qquad c>0,\qquad T\geq t_0.
$$
Let $a(t)$, for $t\geq T$, be the infimum of the physical areas of the
admissible embedded exterior disks in $W(t)$ with boundary trace exactly
$\gamma_t$. The metric is the actual unnormalized post-event metric
$g_F(t)$. The admissible disk class and the infimum convention are unfolded
in the hyperbolic/area section. The predicate then requires:

1. At every $t\geq T$ an admissible disk exists and attains this infimum.
2. The real function $a$ is continuous on $[T,\infty)$.
3. At every $t\geq T$ there is a smooth upper test function touching $a$
   at $t$, dominating it locally on the half-line, whose derivative at
   contact is strictly less than
   $$\frac{3a(t)}{4(t+c)}-\pi.$$

These are conditions at every real time on the half-line, including surgery
times. All $T,c,W,\gamma$ may depend on the seam and basepoint under
consideration. No uniform bound on these choices over the whole sequence
of slices is stated. The loops are not required before $T$; all-time
definitions use a specified zero extension of the scalar area before $T$.
The use of a post-event carrier at a surgery time is explicit.

**What is not a field.** The predicate does not identify $\gamma_t$ with a
primitive meridian or a transported kernel class of the failed seam. It
does not give a time-continuous family of loops, a persistent cusp embedding,
a specified topological exterior, a common unchanged compact carrier across
surgery, or maps transporting disks through that carrier. The sets $W(t)$
are arbitrary subsets subject to the disk conditions. Stability, minimal
surface equations and boundary estimates are not separate exported fields.
The coarse producer is expected to construct the displayed consequence
using that geometric mathematics; it has not yet been split into those
interfaces.

This limitation has an exact logical expression. Given the scalar area
contradiction and the proved nonnegativity of the infimum, the obstruction
predicate implies incompressibility. Conversely, if the seams are already
incompressible, every failed-injection premise is false, so the obstruction
predicate holds vacuously. Thus this is a geometric-looking *conditional
obstruction consequence*, logically equivalent to incompressibility once
the scalar lemma is available. It is not an independent construction of
least-area disks merely because the quantified data appear in its statement.
This equivalence is mathematical analysis of the definitions in this report;
the skeleton does not contain a separately named equivalence theorem.

## F6. The late-sequence tests: full quantifier order {#f6-sequence-tests}

Fix one flow $F$ and one natural number $K$. Put $\omega_3=4\pi/3$.
The predicate `hasLateSequenceTests(F,K)` has the following order:
$$
 \begin{gathered}
 \forall (s_j)_{j\geq0}\ \text{of actual regular slices of }F,\\
 [\ t_j>j\text{ for every }j\ ]\ \land\
 [\ M_{t_j}\ne\varnothing\text{ for every }j\ ]\quad\Longrightarrow\\
 \exists A:\mathbb R\to\mathbb R,
 \quad A(w)>0\quad(0<w<\omega_3),\\
 \forall w_0\in(0,\omega_3)\quad\exists N\in\mathbb N\quad
 \forall j\geq N\quad\forall\text{ connected components }C\subset M_{t_j},\\
 \exists\text{ a torus decomposition }D\text{ of that actual }C,\\
 [\ \text{every piece has }\mathrm{HyperbolicOrCollapsed}
       (t_j^{-1}g_F(t_j)|_C,D,K,A,w_0)\ ]\\
 \land\ [\ \mathrm{hasExteriorAreaObstructionAfter}(F,D,t_j)\ ].
 \end{gathered}
$$

The sequence of times need not be increasing; $t_j>j$ suffices. The choice
of $A$ may depend on the entire sequence and the already fixed $F,K$.
It is one function for all components and all tested late indices in that
sequence. It has no continuity or monotonicity hypothesis. The choice of
$N$ may depend on the sequence and $w_0$, but is uniform in $j\geq N$ and
in the component $C$. The decomposition may depend on $w_0,j,C$; it is not
required to be nested, isotopic, or consistent between different slices or
different tolerances. The area-obstruction data may depend on this chosen
decomposition.

In particular, this is not a theorem of the form “one function $A$ works
for every late time on this flow.” Nor does it select a new flow after
seeing $w_0$. It supplies exactly the sequence-level uniformity used in
the contradiction proof. The universal quantifier over sequences is
vacuous if the flow has no sequence of arbitrarily late nonempty slices;
that is compatible with the separate actual-empty reconstruction branch.

## F7. The admitted selected-flow theorem {#f7-selected-flow}

**Admitted statement.** For every compact oriented smooth three-stage $P$,
every smooth Riemannian metric $g$ on $P$, and every integer $K\geq20$,
there exist a real function $\delta$ and one raw surgery flow $F$ starting
from that same $(P,g)$ such that:

1. $0<\delta(t)<1$ for every $t\geq0$.
2. $\delta$ is nonincreasing on $[0,\infty)$.
3. For every $\varepsilon>0$ there is $B\in\mathbb R$ such that
   $\delta(t)<\varepsilon$ for every real $t>B$.
4. $F$ has common neck accuracy $\delta$ in the precise prefix sense of F4.
5. $F$ has the late-sequence tests of F6 at order $K$.

The positivity, monotonicity and eventual smallness are separate clauses;
monotonicity alone would not imply decay to zero. There is no assumed
normalization of $g$, and no positivity or smallness assumption on its
curvature. The selected flow and $\delta$ may depend on $P,g,K$.
This does not assert a single flow working simultaneously for every $K$.
There are no requirements on $\delta$ at negative times apart from the
literal all-real function equalities in the prefix condition and the
eventual inequality just written.

The exact declaration is `GC.LongTime.exists_surgery_with_late_sequence_tests`.
This is the largest new admitted composite. The claim does not take
`Geometrizes` as a hypothesis, but it incorporates most of the still
unseparated long-time geometric work in its conclusion. The extra common
delta/profile clauses are *not used* in the current capstone after this
theorem has been invoked; the proof projects only the selected flow and
its late-sequence tests. This is a legitimate use of a stronger conclusion,
not evidence that the unused analytic conditions have been derived elsewhere.

## F8. The written bad-sequence proof {#f8-bad-sequence-proof}

**Proved, conditional statement.** If a fixed raw flow $F$ satisfies the
late-sequence tests for an integer $K\geq10$, then some real $B$ has the
following property: every nonempty regular slice of this same flow at a
time greater than $B$ has a geometrization certificate on each actual
connected component.

Here is the actual proof, including the order in which its inputs are used.

1. Negate the conclusion. For each integer $j\geq0$, choose a nonempty
   regular slice $s_j$ at time $t_j>j$ for which not every component
   geometrizes. The code uses classical choice. It does not assume this
   sequence is monotone in time.
2. Apply the given late-sequence tests to obtain $A$. Apply the admitted
   closed and boundary static theorems to this $K,A$. Their proved
   minimum-threshold combination gives one $w_0\in(0,\omega_3)$ valid
   for all connected compact carriers satisfying the appropriate tests.
3. Apply the sequence tests at this $w_0$ to obtain $N$. Fix any actual
   connected component $C$ of the slice $s_N$, and obtain its decomposition
   $D$ and its three-way piece data.
4. To prove incompressibility, suppose one actual seam map fails to inject.
   Its area obstruction supplies $T,c,a$. The scalar area is nonnegative
   by the definition and proved nonnegativity of the disk-area infimum.
   It is continuous and has the displayed strict upper barriers. Since
   $T\geq0$ and $c>0$, the denominator has the required positivity.
   The admitted shifted area lemma contradicts these properties.
5. Apply the conditional assembly in F3, using the static threshold from
   step 2, the now established seam injections, and the actual piece data.
   Thus $C$ geometrizes. Since $C$ was arbitrary, all components of $s_N$
   geometrize, contradicting the choice of $s_N$.

The proof uses the obstruction's continuity and barriers but does not use
its separate attainment field or its bound $T\geq t_N$. Those stronger
clauses remain part of the admitted geometric output. It also does not
use the separate common-derivative-bound lemma, Mostow--Prasad, local
compactness, or cusp-family transport inside this proof; such inputs belong
under the admitted producer when that proof is eventually written.

This theorem is `components_geometrize_of_late_sequence_tests`. The regular
slice, component, metric and decomposition in every application refer to
the same chosen flow and the same selected index. There is no unrecorded
change of carrier in the composition.

## F9. From the late flow to the original manifold {#f9-capstone}

**Proved, conditional theorem with a supplied initial metric.** For every
connected closed oriented smooth $M$ and every smooth metric $g$ on its
corresponding stage, $M$ geometrizes. The actual proof of
`geometrizes_of_metric` invokes F7 at $K=20$, applies F8 using $20\geq10$,
and then applies the already proved same-flow reconstruction adapter in F2.
Its status is conditional on the admitted producers, even though its
statement has no explicit analytic hypothesis: the proof references the
globally asserted `sorry` theorems.

The inherited reconstruction runs backward through one finite observation
history. At each event it uses the actual smooth cut-and-cap completion,
geometrization of the classified discarded components, and the standard
$S^2\times S^1$ factor for graph cycles. It keeps track of the initial
oriented diffeomorphism. If the final observed manifold is empty, the
componentwise endpoint assertion there is vacuous, and the same history
reconstruction still supplies the original certificate. Neither this
argument nor F8 asserts that every flow becomes extinct.

**Public capstone and its two reformulations.** `GC.Endpoint.geometrization`
obtains a smooth metric on the compact $M$ and applies `geometrizes_of_metric`.
`geometrization_conjecture` is the same theorem viewed as a universally
quantified proposition. `smooth_geometrization_conjecture` is its equivalent
formulation with the topology, smooth atlas, compactness, connectedness and
orientation supplied as explicit arguments. These are three names for the
same endpoint conclusion in the smooth oriented category. They are not
three separate proofs and do not remove any admission.

## F10. Review decisions for the integration {#f10-review-decisions}

Five decisions deserve explicit review before independent proof tasks are
assigned. The joint-review worksheet returns to these with source references.

1. **Endpoint:** Approve E1's noncanonical prime and torus data, E2's model
   normalizations, and hyperbolic-only finite volume. Topological and
   nonorientable statements need separate formulations.
2. **Uniformity:** Approve F6's sequence-level quantifiers. They suffice for
   the contradiction but supply neither an all-times derivative function
   nor persistent geometric data between slices.
3. **Flow parameters:** Decide whether the common-delta condition is a
   sufficient exported interface. Other cutoff parameters may vary with
   the finite prefix.
4. **Incompressibility:** Meridians, persistent cusp families and surgery
   transports remain inside the admitted producer. The scalar contradiction
   does not supply those independent interfaces.
5. **Relative reconstruction:** The mixed producer can choose new primes,
   seams and metrics. Its conclusion, expanded in T9, governs which incoming
   markings are retained.

These scope distinctions do not assert that the statements or written
implications are false. They identify precisely what approval would cover.


# Static collapse: faithful mathematical reading of the Lean skeleton

## C0. Scope, conventions, and proof status {#collapse-scope}

This section translates **all 35 authored declarations in the seven collapse-related modules** at commit `ea0fae60ee01ef8c8d9b57a51794c6538f679c5d`. It is a description of the actual Lean code, not a proposed improvement or a claim that all collapse nodes in the blueprint have been formalized. No Lean code was changed in preparing this report.

There are **seven admitted theorem bodies**, **four independently proved elementary monotonicity theorems**, and **two composition theorems with genuine Lean proofs that use admitted collapse theorems**. The other 22 declarations are definitions, structures, or abbreviations, including two explicitly constructed weakening operations. “Independently proved” here means their axiom audit does not contain `sorryAx`; it does not mean their entire inherited mathematical foundation was re-audited for this report. A theorem with an actual proof can still depend on admissions through the theorems it invokes.

In the three-dimensional statements, a **compact carrier** means an oriented compact Hausdorff second-countable smooth 3-manifold, modeled either on Euclidean 3-space or the standard half-space. Its orientation is part of the supplied data. It need not be connected or nonempty merely by being a compact carrier. Whenever the collapse theorems assume “connected,” the Lean `ConnectedSpace` assumption includes nonemptiness. There are smooth boundaries here, not arbitrary manifolds with corners. The notation \(\partial W\) denotes the boundary determined by the actual manifold model, not a selected subset or a boundary imported from another carrier.

Every metric \(g\) in these seven modules is a **smooth positive-definite Riemannian metric**. Finite regularity enters through cusp embeddings, not through nonsmooth input metrics to the static collapse theorem.

Write

\[
 d_g(x,y)\in[0,\infty],\qquad B_g(p,r)=\{q:d_g(p,q)<r\},\qquad
 V_g(p,r)=\operatorname{Vol}_g B_g(p,r),\qquad \omega_3=4\pi/3.
\]

The distance is the intrinsic Riemannian distance **within the specified carrier**, defined using lengths of curves in that carrier. Thus a ball in a cut piece is not automatically the intersection of that piece with a ball in a larger flow manifold. Volume is the actual Riemannian volume measure on the same carrier. The code uses extended nonnegative reals for distance and volume. For real \(r\leq0\), its open-ball definition gives the empty set; the substantive tests below always impose \(r>0\).

For the dimension-independent auxiliary definitions, the setting is a smooth manifold with a finite-dimensional real normed model, a model with corners, and the indicated Hausdorff and sigma-compact assumptions. They do not silently assume dimension three, compactness, orientation, or connectedness. The constant \(\omega_3\) and the exponent three are nevertheless explicitly three-dimensional in the collapse predicates.

The convention for sectional curvature is fixed by the identity

\[
 \sec_g\geq a\quad\Longleftrightarrow\quad
 a\bigl(g(v,v)g(w,w)-g(v,w)^2\bigr)\leq \mathrm{Rm}_g(v,w,w,v)
\]

for every point and every pair of tangent vectors. Dependent and zero vectors are included; division by a possibly zero Gram determinant is avoided.

## C1. What the curvature-derivative notation actually means {#collapse-tensor}

**Definitions, with no admitted proofs.** For a raw covariant \(s\)-tensor field \(T\), the code defines \(\nabla_g T\) by the usual coordinate expression for the Levi–Civita covariant derivative: differentiate the coordinate tensor and subtract the connection action in each covariant slot. The differentiation slot is prepended to the existing tensor slots. At a boundary point the derivative is taken within the range of the manifold's model with corners. The result is converted from coordinates back to a tensor in the actual tangent space.

The iteration is defined recursively:

\[
 \nabla_g^0T=T,\qquad \nabla_g^{k+1}T=\nabla_g(\nabla_g^kT).
\]

The curvature quantity used everywhere below is

\[
 D_k(g,x):=\left|\nabla_g^k\mathrm{Rm}_g(x)\right|_g,
\]

where \(\mathrm{Rm}_g\) is the actual covariant four-tensor of the Levi–Civita connection and the norm is the induced tensor Hilbert–Schmidt norm, not the operator norm or the coordinate sup norm. The norm is the square root of the corresponding tensor inner product.

**Total-definition qualification.** Lean's derivative operation is defined even for functions that are not differentiable. Consequently the raw operation \(T\mapsto\nabla_gT\) accepts an arbitrary tensor field without a regularity premise. For differentiable tensor fields its displayed formula is the ordinary covariant derivative. For arbitrary nonsmooth fields one must not read its value as asserting that a classical covariant derivative exists. Here the curvature field comes from a smooth metric; the cusp-error application below has the explicit \(C^{K+1}\) map regularity that is intended to justify the derivatives through order \(K\). The new modules do not separately prove a general finite-regularity compatibility theorem for this raw operation. This is an implementation obligation, not an extra regularity theorem already obtained from the definition.

**Lean references:** `metricCovariantDerivative` (Metric.lean:17), `iteratedMetricCovariantDerivative` (Metric.lean:30), and `curvatureDerivativeNorm` (DerivativeNorm.lean:18).

## C2. Curvature radius, volume collapse, and derivative tests {#collapse-radius}

**Definitions.** The curvature radius is the extended-real supremum

\[
 R_g(p)=\sup\left\{r>0:\sec_g(q)\geq-r^{-2}\ \text{for every }q\in B_g(p,r)\right\}.
\]

This radius is **not capped at 1**. It is permitted to equal \(+\infty\). It uses a sectional lower bound on the whole ball, not a curvature condition only at its center. The code does not insert a separately supplied scale function into this definition.

“Volume collapsed at curvature scale with parameter \(w\)” means exactly

\[
 \forall r>0,\quad R_g(p)=r\ \Longrightarrow\ V_g(p,r)\leq wr^3.
\]

The equality is equality in extended nonnegative reals. Therefore this condition tests the one finite positive curvature radius when it exists. **It is vacuous when \(R_g(p)=+\infty\)**, and also vacuous if a radius were zero. The latter possibility is excluded by the first admitted lemma below for the stated smooth-manifold setting. No expression \(\operatorname{Vol}B(p,\infty)/\infty^3\) is used.

For a nonnegative integer \(K\), a real-valued function \(A:\mathbb R\to\mathbb R\), and a real threshold \(w_0\), “curvature derivatives controlled” means:

\[
\begin{split}
&\text{for every }p,\ w,r\in\mathbb R\text{ with }w_0\leq w<\omega_3,\quad 0<r<R_g(p),\\
&V_g(p,r)\geq wr^3
\quad\Longrightarrow\quad
 D_k(g,q)\leq A(w)r^{-k-2}
 \quad\text{for every }0\leq k\leq K\text{ and every }q\in B_g(p,r).
\end{split}
\]

The derivative bound includes \(k=0\) and \(k=K\). The radius inequality is **strict**. The volume inequality is **nonstrict**. The estimate is on **every point of the entire same ball**. The definition by itself does not require \(A\) to be positive or \(w_0\) to be positive; the main existence theorems supply these hypotheses. No continuity or monotonicity of \(A\) is built into the predicate. The metric and the function \(A\) are the same in all tests.

**Admitted lemma 1.** For every smooth metric in the auxiliary smooth-manifold setting and every point \(p\),

\[
 R_g(p)>0.
\]

There is no compactness, completeness, connectedness, or boundaryless assumption in this lemma.

**Admitted lemma 2.** If that manifold is compact and connected, then, for every point \(p\),

\[
 R_g(p)=+\infty\quad\Longleftrightarrow\quad \sec_g\geq0\text{ everywhere}.
\]

This includes manifolds with boundary and other allowed models with corners; the lemma is not restricted to closed 3-manifolds. Its forward direction uses connectedness to reach every point from \(p\). Compactness is an explicit hypothesis even if a stronger result might be possible.

**Independently proved lemma.** If \(w_1\leq w_2\), derivative control at threshold \(w_1\) implies derivative control at threshold \(w_2\). The latter condition asks about fewer values of \(w\). This implication requires no positivity assumption on the thresholds or on \(A\).

**Lean references:** all eight declarations in CurvatureScale.lean: `curvatureRadius` (23), `ballVolume` (28), `euclideanUnitBallVolume` (31), `volumeCollapsedAtCurvatureScale` (33), `curvatureDerivativesControlled` (38), `curvatureRadius_pos` (46), `curvatureRadius_eq_top_iff` (50), and `curvatureDerivativesControlled_mono_threshold` (55).

## C3. The exact model cusp and its curvature normalization {#collapse-cuspmodel}

**Definitions.** The fixed topological torus is \(T^2=S^1\times S^1\), with its product smooth structure. The half-cylinder is

\[
 \mathcal H=T^2\times[0,\infty),
\]

with the product manifold-with-boundary model. The collar domain is the relatively open subset

\[
 \mathcal U=T^2\times[0,100).
\]

In particular, \(z=0\) is included and \(z=100\) is excluded.

An exact cusp consists of a **supplied** smooth metric \(q\) on this torus, the condition

\[
 \mathrm{Rm}_q(v,w,w,v)=0\quad\text{for every point and all tangent vectors},
\]

and a supplied smooth metric \(h\) on the whole half-cylinder satisfying exactly

\[
 h=dz^2+e^{-z}q.
\]

These are data and equations, not an existence theorem producing \(q\) or \(h\). No diameter, area, injectivity-radius, lattice-shape, or aspect-ratio restriction is imposed on \(q\) at this stage. There is no quotient group or chosen lattice basis in this definition.

**Admitted lemma 3.** For every such cusp and every point and pair of tangent vectors,

\[
 \mathrm{Rm}_h(v,w,w,v)
 =-\frac14\bigl(h(v,v)h(w,w)-h(v,w)^2\bigr).
\]

Thus the normalization is sectional curvature \(-1/4\), not \(-1\). The statement is a tensor identity including degenerate vector pairs. It is asserted on the whole half-cylinder, including its boundary, not merely on the depth-100 collar. It does not assert completeness of the interior \(T^2\times(0,\infty)\), finite volume for any arbitrary metric on an ambient manifold, or existence of a cusp embedding.

**Lean references:** Hyperbolic/Cusp.lean: `CuspHalfSpace` (10), `cuspDomain` (12), `HyperbolicCusp` (14), `cusp_constant_sectional_curvature` (23).

## C4. Exactly what a nearly cuspidal boundary supplies {#collapse-cuspembedding}

Let \(W\) be a compact carrier with smooth metric \(g\). Fix \(K\in\mathbb N\) and \(\delta\in\mathbb R\).

**Definitions of the error.** For a chosen exact cusp \((\mathcal H,h)\) and a map \(f:\mathcal H\to W\), set

\[
 E=f^*g-h,\qquad
 (f^*g)_p(v,w)=g_{f(p)}(df_pv,df_pw).
\]

The code forms this as an actual covariant two-tensor using the manifold derivative of \(f\). The error bound means

\[
 |\nabla_h^k E(p)|_h\leq\delta
 \quad(0\leq k\leq K,\ p\in T^2\times[0,100)).
\]

Both the derivatives and their tensor norms use the **reference cusp metric** \(h\). This is a pointwise uniform bound on each derivative order, not a sum over orders. It is not a coordinate coefficient norm or a bound on derivatives measured with the target metric \(g\).

**Definition of a cusp embedding onto a prescribed boundary set \(X\subset W\).** The supplied data must satisfy all of the following:

1. An exact cusp as in C3 and a map \(f:\mathcal H\to W\).
2. The map is \(C^{K+1}\) on \(\mathcal U\), including its boundary points.
3. Its restriction to \(\mathcal U\), with the subspace topology, is a topological embedding.
4. Its differential is injective at every point of \(\mathcal U\).
5. Its depth-zero torus has exactly the prescribed image: \(f(T^2\times\{0\})=X\).
6. For every \((t,z)\in\mathcal U\), \(f(t,z)\in\partial W\) if and only if \(z=0\). Thus positive-depth points do not meet any ambient boundary component.
7. The error bounds displayed above hold through order \(K\).

There are no conditions on \(f\) outside \(\mathcal U\). The map is defined there because Lean represents maps as total functions. There is no explicit field asserting a smooth inverse, a proper map on the noncompact half-open collar, or a prescribed orientation for the embedding.

**Definition of a nearly cuspidal boundary.** This consists of a positive integer \(n\), subsets \(X_i\subset W\), \(i\in\{0,\ldots,n-1\}\), and cusp embeddings onto those sets, with:

\[
 X_i\text{ connected and closed},\qquad X_i\cap X_j=\varnothing\ (i\ne j),\qquad
 \bigcup_iX_i=\partial W,
\]

and

\[
 d_g(x,y)\leq\delta\quad\text{for all }x,y\in X_i.
\]

Here connected sets are nonempty. The finite disjoint closed cover by connected sets gives the actual boundary components, not arbitrary pieces of one component. The diameter is measured by curves in **all of \(W\)**. It is not the intrinsic length distance constrained to \(X_i\), and it is not measured with the model torus metric \(q_i\). This precise convention matters for comparison with sources.

**No disjointness of the positive-depth cusp collars is required.** The sets \(X_i\) are pairwise disjoint, and each collar individually is embedded, but there is no field saying the images \(f_i(\mathcal U)\) and \(f_j(\mathcal U)\) are disjoint. Nor does the definition give common torus coordinates or compatible fiber structures on different collars.

**Constructed operations, with no admissions.** If \(\delta_1\leq\delta_2\), either a cusp embedding or a nearly cuspidal boundary with error parameter \(\delta_1\) can be viewed as one with error parameter \(\delta_2\), keeping the exact same maps, component sets, and indices. Only the inequalities are weakened. The operations impose no positivity assumption; substantive applications choose positive thresholds.

**Lean references:** CuspBoundary.lean: `cuspMetricError` (15), `cuspMetricErrorBound` (22), `CuspEmbedding` (29), `NearlyCuspidalBoundary` (43), `CuspEmbedding.weaken` (64), `NearlyCuspidalBoundary.weaken` (70).

## C5. Which points must satisfy volume collapse near boundary {#collapse-boundarydistance}

**Definitions.** Distance to the actual boundary is

\[
 d_g(p,\partial W)=\inf_{q\in\partial W}d_g(p,q)\in[0,\infty].
\]

For empty boundary the infimum is \(+\infty\). The boundary volume-collapse predicate requires exactly

\[
 d_g(p,\partial W)>10\quad\Longrightarrow\quad
 p\text{ is volume collapsed at curvature scale with parameter }w.
\]

The strict inequality is \(>10\), not \(\geq10\). No curvature-scale volume-collapse condition is imposed by this predicate at a point whose distance to boundary is at most 10. Whole-ball curvature-derivative tests will still be imposed at every center in the boundary theorem below.

Although the distance-to-boundary function has a mathematically defined value for empty boundary, the principal boundary theorem requires a positive number of cusp boundary components. The closed theorem uses its own separate predicate.

**Lean references:** CuspBoundary.lean: `distanceToBoundary` (56), `boundaryVolumeCollapsed` (60).

## C6. The three static hypothesis packages and their monotonicity {#collapse-hypotheses}

**Definitions.** For fixed \((W,g,K,A,w_0)\), the closed package is the conjunction of these three conditions:

1. \(\partial W=\varnothing\).
2. Volume collapse at curvature scale with \(w_0\) holds at every point.
3. Derivative control as in C2 holds with \(K,A,w_0\).

The boundary package is the conjunction of these three conditions:

1. There exists a nearly cuspidal boundary with \(K\) and \(\delta=w_0\).
2. The volume-collapse condition of C5 holds with \(w=w_0\).
3. Derivative control as in C2 holds with \(K,A,w_0\).

The combined static package is the **disjunction** of these two packages. None of the three definitions itself contains a graph-manifold predicate or the desired graph presentation as a hypothesis. Connectedness, the lower bound on \(K\), and positivity of \(A\) are supplied separately by the theorems, not hidden inside the definitions.

**Three independently proved monotonicity lemmas.** If \(w_1\leq w_2\), then:

- volume collapse at curvature scale with \(w_1\) implies it with \(w_2\);
- the closed package with \(w_1\) implies the closed package with \(w_2\);
- the boundary package with \(w_1\) implies the boundary package with \(w_2\).

The second and third claims combine the easier volume and collar-error inequalities with the fact that the derivative-trigger interval \([w_2,\omega_3)\) is a subset of \([w_1,\omega_3)\). These proofs do not appeal to any of the seven admissions. They are what later permits taking the minimum of two independently supplied thresholds.

**Lean references:** GraphManifold.lean: `closedCollapseHypotheses` (11), `boundaryCollapseHypotheses` (17), `staticCollapseHypotheses` (22), `volumeCollapsedAtCurvatureScale_mono` (26), `closedCollapseHypotheses_mono` (35), `boundaryCollapseHypotheses_mono` (43).

## C7. What “a raw graph presentation” means in the conclusions {#collapse-output}

This output is a concrete presentation on the **same supplied carrier \(W\)**. It is not an abstract assertion that some homeomorphic manifold is a graph manifold. Its complete definition is translated in the topology section of this report; the parts needed for interpreting the collapse claims are these.

The output supplies a compact oriented cut carrier with finitely many nonempty connected components. Each component is a smooth, locally trivial **ordinary circle bundle** over a compact connected smooth surface, whose base may have boundary and need not be orientable. Exceptional Seifert fibers are not encoded as exceptional fibers of these particular bundles: a further decomposition, for example separating appropriate solid-torus blocks, must account for them when such a presentation is constructed.

There are finitely many paired boundary tori, specified smooth matching maps, actual collars, a quotient reconstruction homeomorphism onto \(W\), smoothness and orientation conditions on that reconstruction, a diffeomorphism on cut interiors, and smooth signed collars across the reassembled seams. Original external boundary tori have explicit collars and labels. Their cut-side and reassembled collars agree under reconstruction. Component ownership of the paired and external tori is recorded.

The paired tori are **not required incompressible**. Neither primeness, irreducibility, a JSJ uniqueness statement, geometric metrics on the blocks, nor a geometrization certificate is part of this output. Those belong to later refinements. The collapse theorems return existence of this data; they do not construct it in their current `sorry` proofs.

**Lean dependency:** `GC.GraphManifold.RawGraphPresentation`, Presentation.lean:129, together with its `CircleFibration`, `TorusPairing`, and `BoundaryTori` fields. Its topology translation remains the authority for the full field-by-field expansion.

## C8. The three admitted graph-presentation producers {#collapse-admitted}

**Admitted lemma 4: the separate nonnegative-curvature case.** Let \(W\) be a connected compact oriented smooth 3-manifold, with empty boundary, and let \(g\) be any smooth metric with \(\sec_g\geq0\) everywhere. Then there exists a raw graph presentation of \(W\), in the exact sense of C7.

There is **no small-volume assumption**, no prescribed \(K\), no derivative function \(A\), and no curvature-radius finiteness assumption here. This is a topological recognition/classification input for closed nonnegative-curvature 3-manifolds. It is separate because curvature-scale volume collapse is vacuous for infinite curvature radius, and the finite-radius argument in C10 cannot absorb such components.

**Admitted theorem 5: closed static collapse.** In precisely this order:

\[
 \forall K\in\mathbb N\ (K\geq10),\quad
 \forall A:\mathbb R\to\mathbb R\ \relax
 [\forall w\in(0,\omega_3),\ A(w)>0],\quad
 \exists w_0\in(0,\omega_3),
\]

such that **for every** connected compact oriented smooth 3-carrier \(W\) and **every** smooth metric \(g\) on it, the closed package of C6 implies existence of a raw graph presentation of \(W\).

The threshold depends on \(K,A\), not on \(W\), \(g\), or a finite family chosen later. The function \(A\) is real-valued and hence finite; no monotonicity, continuity, measurability, or local boundedness of it is assumed. Its values outside \((0,\omega_3)\) are unrestricted and irrelevant to these tests. The theorem does not give an explicit numerical threshold. The output need not respect any previously chosen circle fibration because no such fibration is an input.

**Admitted theorem 6: static collapse with nearly cuspidal boundary.** The same quantifier order supplies a possibly different \(w_0\in(0,\omega_3)\). For every connected compact oriented smooth carrier \(W\), smooth metric \(g\), and **supplied specific nearly cuspidal boundary** \(B\) with \(K\) and \(\delta=w_0\), assume the C5 volume-collapse condition and the C2 derivative control. Then there exist:

\[
 G:\text{a raw graph presentation of }W,
 \qquad e:\{0,\ldots,B.n-1\}\ \xrightarrow{\ \cong\ }\ \relax
 \{0,\ldots,G.n_{\rm ext}-1\},
\]

with

\[
 \operatorname{image}(G\text{'s external torus map numbered }e(i))=B.X_i
 \quad\text{for every }i.
\]

Thus the number and identity of the original boundary components are retained through an explicit index bijection and equality of actual image sets. The theorem does **not** say that the output torus parametrization equals the supplied cusp parametrization, that the output external collar equals the finite-regularity cusp collar, that prescribed longitude/meridian classes are retained, or that their circle fibrations agree. Such stronger relative assertions cannot be read into this statement merely from the word “labels.” The raw presentation itself has its own smooth marked collars, whose compatibility is part of C7.

The boundary theorem applies at nonempty boundary because \(B.n>0\). The derivative condition is imposed at every center, including the boundary and its depth-10 neighborhood; the volume-collapse condition alone has the C5 exception there.

**Lean references:** GraphManifold.lean: `exists_rawGraphPresentation_of_nonnegative` (52), `exists_closed_graph_threshold` (60), `exists_boundary_graph_threshold` (68).

## C9. The common threshold and finite-family conclusion {#collapse-composition}

**Composition theorem with a genuine Lean proof.** With exactly the \(K,A\) hypotheses of C8, there is one \(w_0\in(0,\omega_3)\) such that the combined static package of C6 yields a raw graph presentation for every connected compact carrier and metric.

The proof chooses the minimum of the admitted closed and boundary thresholds, uses the proved monotonicity statements, and applies the appropriate admitted theorem. Therefore it has no `sorry` in its own body but **does depend on `sorryAx`**. In the boundary case this combined theorem deliberately discards the additional boundary-index bijection and image identities returned by the stronger producer; its conclusion only says that a raw graph presentation exists.

**Finite-family composition theorem with a genuine Lean proof.** The same choice of \(w_0\) works simultaneously for every natural number \(n\), every family of connected compact carriers \(W_i\), \(i<n\), and every family of smooth metrics \(g_i\), provided each satisfies the combined static package with the same \(K,A,w_0\). The result is a family of actual raw graph presentations, one on each \(W_i\).

The threshold is chosen **before** \(n\) and the family. The family may be empty, \(n=0\), in which case the conclusion is the empty function. Each individual connected carrier is still nonempty. The conclusion retains the family index. It does not turn the disjoint union into a single connected manifold, identify any flow carriers, or produce one set of surgery/flow parameters.

**Lean references:** GraphManifold.lean: `exists_graph_threshold` (80), `exists_componentwise_graph_threshold` (97).

## C10. Absorbing a sequence of eventual bounds into one derivative function {#collapse-uniform}

**Admitted lemma 7.** Fix any \(K\in\mathbb N\); this lemma does not require \(K\geq10\). Let \((W_j,g_j)\), \(j\in\mathbb N\), be a sequence of compact carriers with smooth metrics. They are not assumed connected, nonempty, or boundaryless. Supply real numbers \(R_j>0\) and \(B_j\geq0\), with the following two bounds for each \(j\):

\[
 0<r<R_{g_j}(p)\quad\Longrightarrow\quad r\leq R_j
 \quad\text{for every }p\in W_j,
\]

and

\[
 D_k(g_j,p)\leq B_j\quad
 \text{for every }p\in W_j\text{ and every }0\leq k\leq K.
\]

The same \(B_j\) bounds all these derivative orders, although it may vary arbitrarily with \(j\). The finite radius bound is a substantive premise: if a nonempty component has infinite curvature radius, it fails, since all positive real radii would have to be at most \(R_j\). An empty carrier creates no difficulty because the pointwise premises are vacuous.

Assume in addition that for each \(w\in(0,\omega_3)\) there are an integer \(N(w)\) and a finite positive real \(C(w)\) such that, for all \(j\geq N(w)\), all centers \(p\), and all \(0<r<R_{g_j}(p)\),

\[
 V_{g_j}(p,r)\geq wr^3
 \quad\Longrightarrow\quad
 D_k(g_j,q)\leq C(w)r^{-k-2}
 \quad(0\leq k\leq K,\ q\in B_{g_j}(p,r)).
\]

The conclusion is the existence of **one** function \(A:\mathbb R\to\mathbb R\) satisfying \(A(w)>0\) for every \(w>0\), such that for **every** sequence index \(j\) and **every** \(w_0>0\), the derivative-control predicate of C2 holds for \((g_j,K,A,w_0)\).

In expanded form, all the above volume-triggered tests hold for every \(j\) and every \(0<w<\omega_3\), with \(C(w)\) replaced by this one \(A(w)\). No common tail \(N\) for all \(w\) is assumed or concluded. The output \(A\) may depend on the entire sequence and all its supplied bounds. It is chosen before the static collapse theorem selects \(w_0\). The conclusion for \(w_0\geq\omega_3\) is harmlessly vacuous, because its derivative-trigger interval is empty.

The intended elementary proof, still admitted in Lean, takes a maximum of the tail bound \(C(w)\) and finitely many quantities such as

\[
 B_jR_j^{k+2},\qquad j<N(w),\quad 0\leq k\leq K,
\]

then adds a positive constant. This explains why no uniform-in-\(w\) tail is needed. It is not a proof that these bounds arise from a Ricci flow: producing the sequence, intrinsic radius bounds, and eventual whole-ball estimates belongs elsewhere.

**Lean reference:** UniformDerivativeBounds.lean: `exists_common_curvature_derivative_bound` (10).

## C11. Mathematical review findings and approval points {#collapse-review}

No definite false assertion or explicit logical contradiction was found in this read-through of these seven modules and their directly relevant definitions. This is a qualified review conclusion: the seven admitted claims remain mathematical obligations, and the stronger output notion of a raw graph presentation must be checked against the topology translation. A successful Lean build is not evidence that the admitted mathematics is true.

The main distinctions that must survive subsequent implementation are:

1. **Intrinsic balls and all-point estimates.** The static assumptions use the carrier's own metric distance and volume and estimate derivatives at all points of the same ball. Center estimates or estimates on ambient flow balls are not interchangeable with them.
2. **Infinite curvature radius is handled separately.** The collapse-at-radius predicate is vacuous at infinity. The closed theorem asserts a graph conclusion even in that situation; it must use nonnegative-curvature recognition. The sequence lemma cannot be applied to a nonempty infinite-radius component.
3. **Finite cusp regularity is explicit.** Maps are \(C^{K+1}\), error derivatives are measured through \(K\), and the reference metric is smooth. No assertion that an arbitrary finite-order metric can be smoothed while preserving curvature is present here.
4. **Boundary control has exact scope.** There is no requirement that different cusp collars be disjoint. Boundary diameter uses the distance in \(W\), not its induced boundary metric. The distance-10 volume exception does not remove any derivative tests. These should be accepted deliberately, not supplied by readers from habit.
5. **Retained boundary labels are weaker than retained markings.** The stronger boundary theorem returns a bijection of indices with equality of image sets; it does not retain a prescribed parametrization, slope basis, fibration, or finite-regularity collar. The generic common-threshold theorem forgets even that extra bijection.
6. **The quantifier order is load-bearing.** Fix \(K,A\); then choose one \(w_0\); then allow all carriers and metrics. In the sequence lemma, fix the sequence first, then construct one \(A\), then invoke static collapse for \(w_0\). No uniform bound across all possible flows or sequences is asserted.
7. **This is an interface for the principal static theorem.** It does not separately state the local model, marker, cloud, one-sheet, or simultaneous cutoff constructions from the blueprint. Their proof work is currently inside the two large admitted threshold producers. It would be misleading to assign every Chapter 14 construction a separate Lean statement already present here.

For this report, actual source definitions were reread in the seven modules and in the dependent carrier, graph-presentation, Riemannian distance/ball/volume, pullback, curvature, tensor metric, and coordinate covariant-derivative files. Blueprint BBR03 (`master207B.tex`, lines 10592–10651) and LC89 (`master207A.tex`, lines 31165–31204) were reread to check the selected boundary and sequence contracts. Their strict inequalities and order of quantifiers agree with the translation above. Existing exact Kleiner–Lott source and errata checks recorded in `collapse_review.md` were not rerun and are not represented here as a new literature audit. No source archive, Lean file, theorem contract, or blueprint text was changed.

## C12. File key and declaration coverage {#collapse-files}

All paths below are relative to the checked code repository `GC_BASELINE_EXPORT` and lie under `DifferentialGeometry/`.

| Short file reference | Actual file |
|---|---|
| CurvatureScale.lean | `Geometry/Collapse/CurvatureScale.lean` |
| CuspBoundary.lean | `Geometry/Collapse/CuspBoundary.lean` |
| GraphManifold.lean | `Geometry/Collapse/GraphManifold.lean` |
| UniformDerivativeBounds.lean | `Geometry/Collapse/UniformDerivativeBounds.lean` |
| Hyperbolic/Cusp.lean | `Geometry/Hyperbolic/Cusp.lean` |
| Metric.lean | `Geometry/Connection/TensorNabla/Iterated/Metric.lean` |
| DerivativeNorm.lean | `Geometry/Curvature/Metric/DerivativeNorm.lean` |
| Presentation.lean (dependent definition) | `Topology/ThreeManifold/GraphManifold/Presentation.lean` |

The accompanying `collapse_coverage.json` maps every authored declaration to its exact section, original source line, admitted/independent/composition/definition status, and inspected audit axiom status. It covers all 35 authored declarations in the seven modules; automatically generated structure projections and recursors are represented through the complete field-by-field descriptions of their parent structures.


# Hyperbolic geometry, exterior disk area, and the incompressibility consumers

This report translates the **actual Lean statements** at commit
`ea0fae60ee01ef8c8d9b57a51794c6538f679c5d`. It covers all **28 authored declarations
in six files**: nine definitions, four directly admitted theorems, and fifteen
theorems with written Lean proofs. A written proof can still depend on an
admitted theorem; that distinction is recorded below. The code has not been
changed in preparing this report.

The six reviewed source files are:

- [Analysis/ODE/AreaUpperBarrier.lean](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Analysis/ODE/AreaUpperBarrier.lean)
- [Geometry/Hyperbolic/Rigidity.lean](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Hyperbolic/Rigidity.lean)
- [Geometry/Hyperbolic/ModelAtlas.lean](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Hyperbolic/ModelAtlas.lean)
- [Geometry/MinimalSurface/ExteriorDiskArea.lean](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/MinimalSurface/ExteriorDiskArea.lean)
- [Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean)
- [Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean)


The central distinction for mathematical approval is this: **the area argument
is encoded as a correct conditional deduction, but the existence of the required
geometric area data is not established in these files.** The continuous
nonnegative area function and all-time upper barriers would be contradictory.
Producing them from a hypothetical compressing torus is the difficult geometric
work; that work remains inside the broader admitted flow producer reviewed
elsewhere.

## HA-0. Conventions and status labels {#ha-0}

- **Definition:** an explicit mathematical object or predicate, not a theorem
  asserting that the predicate holds.
- **Admitted:** the theorem body is `sorry`. Lean has checked its type, not its
  mathematical truth.
- **Written proof, admission-dependent:** a real Lean proof whose audited
  dependency closure contains `sorryAx`.
- **Written proof, no skeleton admission:** the recorded declaration audit
  found no `sorryAx` in its closure. This is about the code's proof dependencies,
  not an independent reproof of all inherited mathematics.

Unless a subsection says otherwise, a smooth 3-manifold here is modeled on
all of \(\mathbb R^3\), hence has no boundary as a manifold. Subsets \(W\) may
have boundary. The Mostow and model-atlas statements explicitly assume
Hausdorffness and sigma compactness. The generic disk-area definitions and
consumers do not add these assumptions. Their use on the actual compact flow
carriers supplies the customary manifold conditions.

The loop parameter is \(\mathbb R/\mathbb Z\). The closed parameter disk is
\(\overline{\mathbb D}\subset\mathbb C\), with boundary parametrization
\(\theta\mapsto e^{2\pi i\theta}\). An equality of boundary traces below is an
equality of **parametrized maps**, not merely of their images or homotopy
classes.

## HA-1. Constant-curvature geometry and rigidity {#ha-1}

### HA-1.1. Constant sectional curvature {#ha-1-1}

**Lean:** `DifferentialGeometry.Geometry.Hyperbolic.hasConstantSectionalCurvature`.
**Status:** definition. Source: `Geometry/Hyperbolic/Rigidity.lean`, line 20.

For a smooth Riemannian metric \(g\) on a smooth 3-manifold \(M\), the predicate
\(\operatorname{ConstSec}(g,K)\) means
\[
 \forall p\in M\ \forall v,w\in T_pM,
 \quad (v,w)\text{ linearly independent}
 \ \Longrightarrow\ \sec_g(p;v,w)=K.
\]
There is no assertion about the library's value of sectional curvature on
linearly dependent vectors. The definition itself does not require
connectedness, completeness, finite volume, Hausdorffness, or sigma compactness.
Its elaborated signature retains only the smooth manifold and metric data it
uses.

### HA-1.2. Marked finite-volume Mostow–Prasad rigidity {#ha-1-2}

**Lean:** `DifferentialGeometry.Geometry.Hyperbolic.mostow_prasad`.
**Status:** admitted. Source: `Geometry/Hyperbolic/Rigidity.lean`, line 24.

Let \(M,N\) be connected, nonempty, Hausdorff, sigma compact smooth
3-manifolds without boundary. Let \(g,h\) be smooth Riemannian metrics, and
let \(K<0\) be **the same constant for both metrics**. Assume:

1. \(\operatorname{ConstSec}(g,K)\) and
   \(\operatorname{ConstSec}(h,K)\).
2. Both Riemannian metrics are complete.
3. Both total Riemannian volumes are finite.
4. A specified continuous homotopy equivalence \(u:M\to N\) is given.

Then there is a unique smooth diffeomorphism \(f:M\to N\) satisfying both
\[
 h_{f(p)}(df_pv,df_pw)=g_p(v,w)
 \quad\text{for every }p,v,w,
 \qquad f\simeq u.
\]
Thus uniqueness is **within the specified unbased homotopy class**, among
smooth diffeomorphisms preserving the metric. It is not uniqueness among all
isometries. It is not an equation between arbitrarily chosen based
fundamental-group homomorphisms. The input homotopy equivalence includes a
continuous inverse up to homotopy; no smoothness of \(u\) is required.

“Complete” is implemented as completeness of the intrinsic Riemannian
extended distance. In the connected case here this is the customary metric
completeness notion. Finite volume is literally
\(\operatorname{vol}_g(M)<+\infty\), and similarly for \(h\).

No orientability or compactness assumption is imposed. Empty manifolds are
excluded by `ConnectedSpace`; noncompact finite-volume cusped manifolds are
included. This declaration contains no quantitative closeness conclusion,
control of cusp coordinates, or time-dependent family of isometries.

### HA-1.3. Local curvature gives a hyperbolic model atlas {#ha-1-3}

**Lean:**
`DifferentialGeometry.Geometry.Hyperbolic.has_hyperbolic_atlas_of_curvature_neg_one`.
**Status:** admitted. Source: `Geometry/Hyperbolic/ModelAtlas.lean`, line 17.

Let \(M\) be a Hausdorff, sigma compact smooth 3-manifold, with smooth metric
\(g\) and \(\operatorname{ConstSec}(g,-1)\). Then every point has a smooth
local isometry from an open set in the fixed hyperbolic coordinate model.
That model is \(\mathbb R^3\), with coordinates \((x,y,z)\) and metric
\[
 h_{\mathbb H}=e^{-2z}(dx^2+dy^2)+dz^2.
\]
More literally, for each \(x\in M\), there is a partial smooth
diffeomorphism \(e\) from this coordinate model into \(M\), with
\(x\) in its target, for which \(e^*g=h_{\mathbb H}\) everywhere in its
source. This is precisely the inherited predicate `HasThurstonAtlas g
.hyperbolic`.

No completeness, finite volume, connectedness, or nonemptiness is assumed.
On the empty manifold the pointwise assertion is vacuous. The output is local
model charts; it does not supply a global developing map, a deck group, an
explicit quotient presentation, or a selected cusp decomposition.

### HA-1.4. Complete finite-volume geometric structure from curvature -1/4 {#ha-1-4}

**Lean:** `DifferentialGeometry.Geometry.Hyperbolic.finiteVolumeGeometricStructure`.
**Status:** explicit construction, admission-dependent through HA-1.3.
Source: `Geometry/Hyperbolic/ModelAtlas.lean`, line 23.

On a Hausdorff, sigma compact smooth 3-manifold \(M\), assume \(g\) is
smooth, complete, finite volume, and has constant sectional curvature
\(-1/4\). The construction returns a `GeometricStructure` on the **same
whole carrier \(M\)**, having:

- model label `hyperbolic`;
- metric \(\widehat g=\tfrac14g\);
- completeness of \(\widehat g\);
- a hyperbolic model atlas for \(\widehat g\);
- finite total volume for \(\widehat g\).

The scaling is deliberate: \(\sec_{\frac14g}=4\sec_g=-1\), and in
dimension three volumes scale by \((1/4)^{3/2}=1/8\). Completeness and volume
scaling use existing proved lemmas; the atlas uses HA-1.3. There is no
connectedness assumption. The returned metric is **not literally the input
metric**, and this construction does not assert that a truncated cusp core
with its restricted original metric is complete.

**Companion declaration:**
`DifferentialGeometry.Geometry.Hyperbolic.finiteVolumeGeometricStructure_model`,
line 42, says exactly that the model label of this construction is
`hyperbolic`. Its proof is `rfl`; the recorded full declaration closure still
contains the admitted atlas theorem through the construction. It adds no
new geometric content.

## HA-2. The real-variable area contradiction {#ha-2}

### HA-2.1. A strict local smooth upper barrier {#ha-2-1}

**Lean:** `DifferentialGeometry.Analysis.hasLocalSmoothUpperBarrier`.
**Status:** definition. Source: `Analysis/ODE/AreaUpperBarrier.lean`, line 13.

Given \(A:\mathbb R\to\mathbb R\), a set \(S\subseteq\mathbb R\), and real
numbers \(t,b\), this means that there are an open set \(U\subseteq\mathbb R\)
and a function \(F:\mathbb R\to\mathbb R\) such that:
\[
 t\in U,\qquad F\in C^\infty(U),\qquad F(t)=A(t),
 \qquad A(s)\le F(s)\ (s\in U\cap S),\qquad F'(t)<b.
\]
\(F\) is only required smooth on \(U\), despite being a function defined
on all of \(\mathbb R\). The bound on its derivative is **strict**, and is
required only at the contact time. The area function \(A\) is not assumed
differentiable. The definition alone does not even require \(t\in S\);
the consumers below impose it.

When \(S=[T,\infty)\), the neighborhood \(U\) is open in \(\mathbb R\).
Domination at \(t=T\) is required only to the right, whereas at any
\(t>T\), including a surgery time in an application, it is required on
both sides sufficiently near the contact.

### HA-2.2. The general shifted contradiction {#ha-2-2}

**Lean:** `DifferentialGeometry.Analysis.not_nonnegative_area_upper_barriers_shift`.
**Status:** admitted. Source: `Analysis/ODE/AreaUpperBarrier.lean`, line 18.

Let \(A:\mathbb R\to\mathbb R\), and let \(T,c,D\in\mathbb R\) satisfy
\[
 T+c>0,\qquad 0<D<2\pi.
\]
Assume \(A\) is continuous on \([T,\infty)\), is nonnegative there, and
at **every** \(t\ge T\) has a local smooth upper barrier with
\[
 F'(t)<\frac{3A(t)}{4(t+c)}-2\pi+D.
\]
Then these assumptions imply a contradiction. Neither \(T\) nor \(c\)
separately needs to be positive. The condition \(T+c>0\) makes every
denominator on the half-line positive. There is no boundedness assumption
on \(A\), no uniform contact-neighborhood radius, and no differentiability
assumption on \(A\).

The intended elementary argument uses \((t+c)^{-3/4}A(t)\) and the divergent
integral of \((t+c)^{-3/4}\). This is an explanation of the admitted
statement, **not a claim that this proof has been formalized**. A finite time
interval, barriers only at regular flow times, or continuity only between
surgeries would not satisfy the statement.

### HA-2.3. The three written specializations {#ha-2-3}

Each row is a separate authored declaration in the same file, proved from
HA-2.2 and therefore admission-dependent.

| Lean name after `DifferentialGeometry.Analysis.` | Exact specialization | Line |
|---|---|---:|
| `not_nonnegative_area_upper_barriers` | Set \(c=1/4\); require \(T>-1/4\), \(0<D<2\pi\), continuity and nonnegativity on the whole half-line, and the bound \(3A/[4(t+1/4)]-2\pi+D\). | 28 |
| `not_nonnegative_area_upper_barriers_pi_shift` | Set \(D=\pi\); require \(T+c>0\), continuity and nonnegativity on the half-line, and the bound \(3A/[4(t+c)]-\pi\). | 39 |
| `not_nonnegative_area_upper_barriers_pi` | Set \(c=1/4,D=\pi\); require the stronger endpoint condition \(T\ge0\), continuity and nonnegativity, and the bound \(3A/[4(t+1/4)]-\pi\). | 52 |

All three conclude `False`, meaning their complete collections of hypotheses
cannot occur. None is a theorem producing barriers for a Ricci flow.

## HA-3. What the exterior disk area actually means {#ha-3}

### HA-3.1. The competitor class {#ha-3-1}

**Lean:** `DifferentialGeometry.Geometry.MinimalSurface.isExteriorSpanningDisk`.
**Status:** definition. Source: `Geometry/MinimalSurface/ExteriorDiskArea.lean`,
line 15.

Fix a subset \(W\subseteq M\), a continuous loop
\(\gamma:\mathbb R/\mathbb Z\to M\), and a continuous map
\(u:\overline{\mathbb D}\to M\). It is an admissible exterior spanning disk
precisely when all the following hold:

1. \(u(e^{2\pi i\theta})=\gamma(\theta)\) for every \(\theta\).
2. \(\gamma(\mathbb R/\mathbb Z)\subseteq\operatorname{frontier}(W)\).
3. \(u\) is a topological embedding.
4. \(u(\overline{\mathbb D})\subseteq W\).
5. \(u(\mathbb D)\subseteq\operatorname{interior}(W)\).
6. There exists a function \(U:\mathbb C\to M\), equal to \(u\) on
   \(\overline{\mathbb D}\), that is smooth on an open neighborhood of the
   closed disk, and whose differential is injective at every point of the
   closed disk.

Thus the competitors are smoothly immersed up to and across their parameter
boundary, and topologically embedded. No branch point is allowed, including
at the boundary. The extension need not be smooth outside the specified
neighborhood or have image in \(W\) outside the closed disk.

There is **no metric in this predicate**. In particular it does not mean
minimal, stable, conformal, least area, or orthogonal to the frontier. It
does not require \(W\) to be closed, compact, connected, a submanifold, or
mean convex, nor identify \(W\) as the complement of any particular
hyperbolic core. The word “exterior” is a name for this precisely specified
side condition. For an open \(W\), the boundary requirement and
\(u(\overline{\mathbb D})\subseteq W\) usually make the class empty;
actual applications intend a compact exterior including its boundary.

The elaborated predicate requires just topology and charts on \(M\); it
does not retain the surrounding file's unused smooth-manifold instance.
Its use with the area below does require the smooth metric/manifold data.

### HA-3.2. The infimum and the meaning of “area” {#ha-3-2}

**Lean:** `DifferentialGeometry.Geometry.MinimalSurface.leastExteriorDiskArea`.
**Status:** definition. Source: `Geometry/MinimalSurface/ExteriorDiskArea.lean`,
line 22.

For a smooth metric \(g\), define
\[
 a(g,W,\gamma)=\inf\{\operatorname{Area}_g(u):
       u\text{ satisfies HA-3.1}\}\in\mathbb R.
\]
This is a **real-valued infimum**, not an extended-real infimum. The inherited
`riemannianDiskArea` is the integral over the Euclidean closed unit disk of
the ordinary two-dimensional metric Jacobian:
\[
 \int_{\overline{\mathbb D}}
 \sqrt{g(U_x,U_x)g(U_y,U_y)-g(U_x,U_y)^2}\,dx\,dy.
\]
Formally the library first extends a continuous disk map to \(\mathbb C\)
using the radial metric projection onto the closed disk. Its derivative at
the circle need not be the derivative of a smooth extension. This causes no
area discrepancy: the circle has measure zero, and the inherited theorem
`riemannianDiskArea_eq_of_extension` proves equality with the displayed
integral for any agreeing extension. For the admitted competitor class, the
smooth extension on a neighborhood of the compact disk gives an integrable
Jacobian by the inherited compact integrability theorem. Thus these
competitors have the ordinary finite Riemannian area; the integral's totalized
value on nonintegrable arbitrary maps is not being used to manufacture
competitor areas.

The real infimum of the empty set is **zero in Lean**. Therefore
\(a(g,W,\gamma)\ge0\) by itself does not assert that a disk exists. Attainment
must be supplied separately. No strict positivity theorem, minimality theorem,
stability theorem, or Meeks–Yau theorem is asserted by this definition.

Two authored helpers are proved with no skeleton admission:

- `leastExteriorDiskArea_nonneg` (line 27): for every \(g,W,\gamma\),
  \(0\le a(g,W,\gamma)\), including the empty-class case.
- `leastExteriorDiskArea_le` (line 33): if a specified \(u\) is admissible,
  \(a(g,W,\gamma)\le\operatorname{Area}_g(u)\). The proof explicitly
  bounds all competitor areas below by zero before applying the infimum rule.

### HA-3.3. Time-varying carriers and late-only loops {#ha-3-3}

**Lean:** `DifferentialGeometry.Geometry.MinimalSurface.exteriorDiskAreaOn`.
**Status:** definition. Source: `Geometry/MinimalSurface/ExteriorDiskArea.lean`,
line 43.

One may specify a different smooth 3-manifold \(M_t\) for each real \(t\),
a smooth metric \(g_t\) on each \(M_t\), a subset \(W_t\subseteq M_t\), a
real starting time \(T\), and a continuous loop \(\gamma_t\) **only for
\(t\ge T\)**. Set
\[
 A(t)=\begin{cases}
       a(g_t,W_t,\gamma_t),&t\ge T,\\
       0,&t<T.
      \end{cases}
\]
There is no topology on the total family \(\coprod_tM_t\), no continuity of
\(g_t,W_t,\gamma_t\), no Ricci equation, and no surgery assumption in this
definition. The manifolds are allowed to change their underlying types.
The loop parameter depending on a proof of \(T\le t\) is Lean bookkeeping;
proof irrelevance makes it a single loop for each permitted time.

**Companion theorem:** `exteriorDiskAreaOn_nonneg` (line 52), proved with no
skeleton admission, says \(A(t)\ge0\) for every real \(t\), including
\(t<T\). No continuity from the left at \(T\) is asserted. No loop is
required on an earlier empty carrier.

### HA-3.4. Continuity from two-direction comparisons of minimizers {#ha-3-4}

**Lean:**
`DifferentialGeometry.Geometry.MinimalSurface.continuousOn_leastExteriorDiskArea_of_local_disk_comparisons`.
**Status:** admitted. Source: `Geometry/MinimalSurface/ExteriorDiskArea.lean`,
line 65.

Use exactly the time-dependent data of HA-3.3. Assume:

1. **Attainment at every late time.** For every \(t\ge T\), an admissible
   \(u_t\) exists with \(\operatorname{Area}_{g_t}(u_t)=A(t)\).
2. **Local two-direction comparison.** For every \(t_0\ge T\) and every
   \(\epsilon>0\), there is \(\delta>0\) such that, whenever
   \(t\ge T\) and \(|t-t_0|<\delta\), both statements hold:
   - For **every** attaining admissible disk \(u\) at \(t_0\), an
     admissible disk \(v\) at \(t\) exists with
     \(\operatorname{Area}_{g_t}(v)\le e^\epsilon
       \operatorname{Area}_{g_{t_0}}(u)\).
   - For **every** attaining admissible disk \(v\) at \(t\), an
     admissible disk \(u\) at \(t_0\) exists with
     \(\operatorname{Area}_{g_{t_0}}(u)\le e^\epsilon
       \operatorname{Area}_{g_t}(v)\).

Then \(A\) is continuous on \([T,\infty)\).

The comparison disks need not themselves attain the infimum. The radius
\(\delta\) may depend on \(t_0,\epsilon\), but works for all nearby
times and all minimizing disks in the two quantifiers. The statement does
not require comparison maps between whole manifolds, or a continuously
chosen minimizer. It does not supply the two comparisons from surgery
geometry; it assumes them. The blueprint uses \(e^{2\epsilon}\), whereas
the Lean statement uses \(e^\epsilon\); universal quantification over
all positive \(\epsilon\) makes these formulations equivalent by
renaming \(\epsilon/2\). No uniformity is lost in that renaming.

The direct numerical consequence is
\(e^{-\epsilon}A(t_0)\le A(t)\le e^\epsilon A(t_0)\).
This handles \(A(t_0)=0\) as well, without taking a logarithm of zero.
The theorem's assertion is mathematically elementary once its strong
comparison premises are available; its Lean proof is still admitted.

## HA-4. What is, and is not, proved about torus injectivity {#ha-4}

### HA-4.1. A finite time-dependent family of continuous torus maps {#ha-4-1}

**Lean:**
`DifferentialGeometry.Geometry.RicciFlow.cusp_injective_of_exterior_area_barriers`.
**Status:** written proof, admission-dependent through HA-2.2.
Source: `Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean`, line 15.

Let \(M_t,g_t\) be any family as in HA-3.3, let \(n\in\mathbb N\), and
let \(T_0\in\mathbb R\). For each \(t\ge T_0\) and each
\(i\in\{0,\ldots,n-1\}\), suppose a continuous map
\(f_{t,i}:T^2\to M_t\) is given. Assume the following implication for
**each** \(t\ge T_0\), each \(i\), and each basepoint \(x\in T^2\):

> If \((f_{t,i})_*:\pi_1(T^2,x)\to\pi_1(M_t,f_{t,i}(x))\) is not
> injective, there exist \(T\ge0\) with \(T\ge t\), subsets \(W_s\),
> and loops \(\gamma_s\) for all \(s\ge T\), such that the associated
> actual disk-area function \(A\) of HA-3.3 has an admissible attaining
> disk at every \(s\ge T\), is continuous on \([T,\infty)\), and has
> at every \(s\ge T\) a strict local smooth upper barrier with derivative
> less than \(3A(s)/[4(s+1/4)]-\pi\).

Then all the displayed homomorphisms \((f_{t,i})_*\) are injective.

The proof takes a hypothetical noninjectivity, obtains the promised area
function, proves its nonnegativity from the definition, and applies HA-2.3.
It does not use the attainment conjunct; attainment is retained as a
geometric requirement of the premise. Nor does the contradiction need
\(t\le T\) once the premise has supplied a half-line with \(T\ge0\).

**Exact scope:** the maps \(f_{t,i}\) need not be smooth, embedded,
time-continuous, or actual cusp maps. No Ricci flow is assumed. There is no
condition in this theorem relating \(\gamma_s\) to a particular primitive
kernel element of \(f_{t,i}\), or \(W_s\) to its exterior. Such relations
must be used inside the proof that produces the displayed implication. If
\(n=0\), both that implication and the conclusion are vacuous.

### HA-4.2. Moving the torus along a product collar {#ha-4-2}

**Lean:** `DifferentialGeometry.Geometry.RicciFlow.cusp_slice_injective_iff`.
**Status:** written proof, no skeleton admission.
Source: `Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean`, line 43.

For any topological space \(M\), any continuous
\(c:T^2\times\mathbb R\to M\), any \(r,s\in\mathbb R\), and any
\(x\in T^2\), the map \(y\mapsto c(y,r)\) is injective on fundamental
groups at \(x\) if and only if \(y\mapsto c(y,s)\) is.

The proof uses the actual product homotopy and the existing theorem that
homotopic maps have equivalent injectivity properties, with the induced
basepoint track. No metric or smoothness is involved; \(c\) need not be
an embedding. It is not an inference from injection into an abstract
hyperbolic model to injection into a different ambient manifold.

### HA-4.3. Injectivity for the actual reconstruction seams {#ha-4-3}

**Lean:** `DifferentialGeometry.Geometry.RicciFlow.incompressible_of_area_barriers`.
**Status:** written proof, admission-dependent through HA-2.2.
Source: `Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean`, line 51.

Let \(C\) be the existing compact carrier, \(G\) its actual paired-torus
gluing data, \(S\) a smooth assembly of that gluing, and
\(r:S.\mathrm{assembled}\to P\) an orientation-preserving smooth
reconstruction onto a connected closed oriented 3-manifold \(P\).
Despite the code name `torusInPrime`, this type **does not assume that
\(P\) is prime**. For every gluing label \(i\), the relevant map is
the actual quotient seam followed by \(r\), denoted \(j_i:T^2\to P\).

Assume for every \(i\) and every basepoint \(x\), failure of injectivity
of \((j_i)_*\) produces real data \(T\ge0\) and
\(A:\mathbb R\to\mathbb R\) which are continuous and nonnegative
on \([T,\infty)\), with a strict smooth local upper barrier at each
\(t\ge T\) having derivative less than
\(3A(t)/[4(t+1/4)]-\pi\). Then `S.Incompressible r` holds: every
actual seam map is injective on fundamental groups at every basepoint.

This adapter does not itself require that \(A\) be an area, or that it
be attached to a flow. It is a numerical contradiction consumer whose
conclusion is precisely the existing reconstruction's injectivity predicate.

**Shifted companion:**
`DifferentialGeometry.Geometry.RicciFlow.incompressible_of_shifted_area_barriers`,
line 67, has exactly the same reconstruction data and conclusion. Its
noninjectivity premise produces \(T\ge0\), \(c>0\), and \(A\), with
the bound \(3A(t)/[4(t+c)]-\pi\). The proof derives \(T+c>0\) and
uses HA-2.3. The shift can depend on the failed seam and basepoint. This
theorem also has a written admission-dependent proof.

### HA-4.4. Approval issue: the consumers do not expose the producer's substance {#ha-4-4}

After granting the area contradiction, each “noninjectivity produces an
impossible area function” premise above is logically equivalent to the
corresponding injectivity conclusion: the forward implication is the written
proof, while if injectivity already holds, the premise follows vacuously.
This does **not** make the conditional proof false. It does mean these
consumers by themselves provide almost no independent check of the
geometric proof of incompressibility.

The broader selected-flow producer in `LateDecomposition.lean` uses the actual
same-flow disk area defined below. That rules out an unrelated numerical
function, but does not yet expose, as separately checked fields, the fixed
primitive meridian, its preservation through surgery, actual persistent cusp
embeddings, mean-convex exterior geometry, or the common unchanged carrier
and boundary-moving isotopy. Mathematicians should review that producer as a
large remaining theorem, not treat the short `...of_area_barriers` proofs as
having formalized Meeks–Yau or surgery avoidance.

## HA-5. The same-flow physical area and the event-time convention {#ha-5}

All seven declarations in this section are in
`Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean`. None has `sorryAx`
in its recorded dependency closure. They take an existing
`ObservationTower P g`, a compatible collection of actual finite surgery
histories with specified initial carrier \(P\) and initial metric \(g\).
This section does not construct such a tower or strengthen its analytic
control.

### HA-5.1. The carrier at every real time {#ha-5-1}

**Lean:** `GC.LongTime.postStage`. **Status:** definition. Line 18.

For \(t\in\mathbb R\), put \(\tau=\max\{t,0\}\), restrict the tower to
its observation through \(\tau\), and take that observation's last stage.
This defines \(M_t^{\mathrm{post}}\), including its existing orientation
and manifold structure. For \(t\ge0\), this is the actual carrier at time
\(t\). At an exact surgery time it is the **post-surgery** stage. For
\(t<0\), it is the time-zero stage; this is a totalization convention,
not a backward flow.

This event convention follows from the inherited restriction rule: the active
stage is the largest stage index whose start time is \(\le t\), not
\(<t\). The last stage of the observation is that active stage at the
observation horizon. A stage may be empty.

### HA-5.2. The physical metric on that carrier {#ha-5-2}

**Lean:** `GC.LongTime.postMetric`. **Status:** definition. Line 22.

On `postStage O t`, take the last stage's actual `stageMetric` evaluated at
the same \(\tau=\max\{t,0\}\). At a surgery time this is the post-surgery
output metric. This is the **physical metric**. It is neither
\(t^{-1}g(t)\) nor \((4t)^{-1}g(t)\). No value is divided by zero at
\(t=0\).

### HA-5.3. Agreement with a regular slice {#ha-5-3}

Two separate authored theorems have written proofs without skeleton admissions:

- `GC.LongTime.postStage_regularSlice` (line 26): for any `RegularSlice O`
  with time \(s.time>0\), the carrier `postStage O s.time` equals the
  stage stored by the regular slice.
- `GC.LongTime.postMetric_regularSlice` (line 37): the physical metric
  `postMetric O s.time` is the same metric as `s.metric`, after accounting
  for that equality of the carriers. The Lean conclusion is heterogeneous
  equality because the metric types mention their respective carriers.

These are exact identifications of two descriptions of the same observation,
not a diffeomorphism between different surgery slices or a metric-comparison
estimate across surgery.

### HA-5.4. The actual same-flow area function {#ha-5-4}

**Lean:** `GC.LongTime.exteriorDiskArea`. **Status:** definition. Line 57.

Choose, for every real time, a subset
\(W_t\subseteq M_t^{\mathrm{post}}\), a starting time \(T\in\mathbb R\),
and a loop \(\gamma_t\) in that carrier for every \(t\ge T\). Define
\[
 A_O(t)=\begin{cases}
 a(\mathrm{postMetric}(O,t),W_t,\gamma_t),&t\ge T,\\
 0,&t<T.
 \end{cases}
\]
This is HA-3.3 applied to the actual observation tower. The definition itself
still permits arbitrary \(W_t\) and \(\gamma_t\), imposes no continuity
or persistence on them, and does not require \(T\ge0\). Its intended root
application chooses \(T\) after a positive regular slice, so only actual
nonnegative flow times are used in the area contradiction.

Two authored written helpers, without skeleton admissions, are:

- `GC.LongTime.exteriorDiskArea_nonneg` (line 62): \(A_O(t)\ge0\) for all
  real \(t\).
- `GC.LongTime.exteriorDiskArea_eq` (line 68): if \(t\ge T\),
  \(A_O(t)=a(\mathrm{postMetric}(O,t),W_t,\gamma_t)\), exactly.

They provide no assertion of attainment, positive area, continuity, smooth
upper barriers, or identification of any \(W_t\) with a specified thin
complement. At a surgery contact, the future producer must use the actual
post-surgery infimum and prove the two-sided numerical barrier using a common
unchanged region. These helpers do not assert a global identification of
pre- and post-surgery manifolds.

## HA-6. Mathematical review findings and decisions needed {#ha-6}

This reading found **no concrete counterexample to the four admitted leaf
statements** in these six files. Their principal formulations are compatible
with the corresponding natural-language arguments, subject to the explicit
limitations above. That conclusion is a targeted mathematical review, not
proof verification of admitted claims.

The following distinctions should remain visible when approving the skeleton:

| Point for review | What the code actually does | What remains outside these six files |
|---|---|---|
| Mostow–Prasad | Admits the finite-volume, same-curvature, marked homotopy-class theorem in dimension three. | Its proof, quantitative rigidity, controlled persistent families, and cusp coverage. |
| Hyperbolic geometric metric | Uses \(g/4\) on the same whole carrier when \(\sec g=-1/4\). | A full-interior map from each actual cut piece to the complete hyperbolic carrier. |
| Fixed-boundary disks | Uses embedded, unbranched smooth disks with exactly parametrized boundary, on the specified side. | Actual existence in the chosen exterior; source-to-class comparison; minimality and stability. |
| Empty disk class | Gives real infimum zero, and proves nonnegativity. | Attainment must rule out emptiness wherever geometry is claimed. |
| Continuity through surgery | Admits continuity from explicit forward and backward minimizing-disk comparisons. | Common compact carrier, its two-sided smooth metric, and actual boundary-preserving transports. |
| Area barrier | Requires a strict smooth upper barrier at every time of one entire half-line. | Scalar bound, boundary estimates, first variation, Gauss–Bonnet, and surgery-neck avoidance in the actual flow. |
| Torus injection | Has genuine contradiction consumers for the actual maps supplied to them. | Producer premises currently encapsulate the essential geometric argument. |
| Empty families | Permits zero tori, with vacuous injection obligations; permits empty stages in the tower helpers. | No fictitious loop is required before its threshold; late loops themselves force nonempty carriers where used. |

In particular, there is no new standalone Lean theorem here saying “Meeks–Yau
holds for the actual exterior,” “every least-area disk avoids the surgery
necks,” or “the chosen meridian is preserved through every event.” Those
would be natural future statements when the large root producer is split
into independently assignable tasks. Approving the present statement layer
does not approve a completed proof of those facts.

## HA-7. Evidence for this translation {#ha-7}

Freshly inspected for this report:

- The complete six Lean source files, all 28 authored declarations, and their
  full elaborated signatures and recorded axiom closures in
  `evidence/declarations.json`.
- The inherited definitions `SmoothDiskExtension`, `freeLoop`, `closedDisk`,
  `diskTrace`, `riemannianDiskArea`, `riemannianAreaDensity`, and
  `tangentTwoJacobian`; the existing extension-invariance and compact
  integrability statements for disk area.
- `RiemannianMetricComplete`, `HasThurstonAtlas`, `CoordinateModelAtlas`,
  the hyperbolic `coordinateInner`, and `GeometricStructure`.
- `SmoothAssembly.Reconstruction`, `torusInPrime`, and `Incompressible`;
  `ObservationTower.observe`, `ObservedHistory.activeStage`, and the
  exact-event and observation-horizon rules.
- Blueprint `master207A.tex`, MPR79 lines 15392–15424; IMS02–IMS03 around
  lines 18251–18338; IMS08–IMS09 around lines 18533–18607; IAU02–IAU03
  around lines 18724–18855. These were used to compare the actual predicates,
  not to substitute prose for code.
- Archived `BooksPapers/MSM206.tex`, `MosTowSection`, lines 17115–17166,
  for the Mostow statement and its homotopy-equivalence formulation. Its
  shorthand based-group equation is not copied into the Lean theorem.

The prior source review is `hyperbolic_review.md`, with exact source identities
in `hyperbolic_crosswalk.json`. This report reuses unchanged source/errata
checks only at their documented scope; it does not claim a fresh literature
or errata search. It does not rerun the Lean build. Compilation and the axiom
classification above are read from the final recorded verification of the
pinned commit, supplemented by direct source inspection. The machine-readable
`hyperbolic_area_coverage.json` maps every declaration to the subsection that
translates it.


# Mathematical reading of the topology and finite-regularity skeleton {#topology-finite-regularity}

This report translates the actual Lean source at commit `ea0fae60ee01ef8c8d9b57a51794c6538f679c5d`. It covers all 32 authored declarations in the five files listed below. It is a reading of what the code says, including its weaker conclusions and omitted data; it does not replace those statements by the stronger blueprint assertions.

There are **five admitted theorems** in this part: three topology producers, one finite-order compactness theorem, and one finite-regularity pullback theorem. Seven further theorem bodies contain actual proofs: three elementary collar facts independent of these admissions, two corollaries of the admitted pullback theorem, and two assemblies of admitted topology producers. The remaining 20 authored declarations define mathematical objects or construct data. Anonymous instances and compiler-generated structure projections are not separate authored declarations in these counts.

The five source files are:

| Short name in this report | Actual source |
|---|---|
| Presentation | [GraphManifold/Presentation.lean](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean) |
| Refinement | [GraphManifold/Refinement.lean](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean) |
| TorusDecomposition | [TorusCut/Decomposition.lean](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/TorusCut/Decomposition.lean) |
| Pullback | [Metric/Pullback/FiniteRegularity.lean](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Metric/Pullback/FiniteRegularity.lean) |
| Compactness | [Calculus/Compactness/FiniteOrder.lean](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Analysis/Calculus/Compactness/FiniteOrder.lean) |

## T0. The mathematical types used throughout {#t0}

The carrier of a compact piece is an **actual compact, Hausdorff, second-countable, oriented smooth 3-manifold**, possibly with boundary. It is not a homeomorphism type, a fundamental group, or a model name. Its chart model is either all of Euclidean 3-space or a Euclidean half-space. A half-space chart model permits a manifold whose boundary happens to be empty. The carrier type by itself need not be connected or nonempty.

`CompactCarrier.Components` adds a finite decomposition into actual subsets of that carrier. More precisely, it supplies a positive integer \(n>0\), open-and-closed subsets \(C_i\), \(0\leq i<n\), which are pairwise disjoint and cover the carrier, with each \(C_i\) connected **and nonempty**. Each \(\operatorname{int}(C_i)=C_i\cap\operatorname{int}(C)\) is also required to be connected and nonempty. In Lean, `ConnectedSpace` includes nonemptiness. Thus this component record cannot describe an empty carrier or an empty component list. Individual torus-index lists below may nevertheless be empty.

These inherited definitions are in [Carrier.lean:32](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/Geometrization/Carrier.lean#L32) and [Carrier.lean:56](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/Geometrization/Carrier.lean#L56).

An `InteriorGeometry` on \(C_i\) means a smooth Riemannian metric on **the whole actual interior** \(C_i\cap\operatorname{int}(C)\), complete in its own Riemannian distance, together with local isometric charts for one specified member of the eight fixed Thurston models. If the model is hyperbolic, its total volume is finite. For the other seven models, finite volume is **not** required. This is the existing endpoint convention. It permits, for example, complete infinite-volume flat product interiors. It does not mean merely “there is some locally homogeneous metric on some abstract manifold related to this component.” See [Atlas.lean:56](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Thurston/Atlas.lean#L56).

For a connected closed oriented smooth 3-manifold \(M\), a `PrimeDecomposition M` supplies a nonempty finite list of actual connected closed oriented manifolds \(P_i\), each prime, and an orientation-preserving smooth diffeomorphism

\[
       P_1\#\cdots\#P_m\;\longrightarrow\;M.
\]

Here prime means that every smooth connected-sum decomposition has a summand diffeomorphic to \(S^3\). Primeness is formulated without an orientation requirement on that summand-identifying diffeomorphism. In particular, \(S^3\) is allowed as a recorded prime identity, and \(S^2\times S^1\) is not excluded. The record does not itself supply an embedded sphere system or cap balls in \(M\). See [Prime.lean:11](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/Geometrization/Prime.lean#L11).

A `GeometricDecomposition P` consists of actual compact cut components, paired torus boundaries, their smooth oriented reconstruction to \(P\), injection of each reconstructed torus into \(\pi_1(P)\), and an `InteriorGeometry` for each cut component. The type can be formed for any connected closed \(P\); it does not itself assume that \(P\) is prime. A `GeometrizationCertificate M` additionally requires its chosen factors \(P_i\) to be prime. The proposition `Geometrizes M` means that such a certificate exists. See [Statement.lean:11](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/Geometrization/Statement.lean#L11).

## T1. Surfaces and ordinary circle bundles {#t1}

**Declarations:** `SurfaceModel` (Presentation:10), `SurfaceModel.Space` (:13), `SurfaceModel.model` (:22), `CompactSurface` (:28), and `CircleFibration` (:43). All five define data; none asserts an existence theorem.

`SurfaceModel` has two choices: the plane and the closed half-plane. The `Space` and `model` declarations associate their usual smooth manifold models to those choices. `CompactSurface` is a compact, connected, nonempty, Hausdorff, second-countable smooth surface with one of these models. **There is no assumption that the surface is orientable.** The half-plane choice does not require nonempty boundary.

For an open subset \(U\subset C\), a `CircleFibration C U` supplies:

1. A compact surface \(B\) as just defined.
2. A continuous, smooth, surjective map \(\pi:U\to B\).
3. For every \(b\in B\), an open neighborhood \(V_b\ni b\) and an actual smooth diffeomorphism
   \[
        \tau_b:\pi^{-1}(V_b)\longrightarrow V_b\times S^1
   \]
   whose first coordinate is exactly \(\pi\).

The domain in item 3 is the inverse image **inside the actual subset \(U\)**. This is an ordinary smooth circle bundle with local product trivializations. Every fiber is a smooth circle. The record does not require principal \(S^1\)-bundle transition functions, a global circle action, a chosen fiber orientation, or an orientable base. Arbitrary smooth fiberwise changes of circle coordinates are allowed. It also has no exceptional fibers or orbifold base. Thus it represents the regular circle-bundle blocks of the raw graph presentation, not a definition of every Seifert fibration.

In the later `RawGraphPresentation`, \(U\) is one of the compact clopen connected cut components. The generic definition of `CircleFibration C U` itself does not separately assume that \(U\) is compact or connected.

## T2. Actual labelled boundary tori and their elementary properties {#t2}

**Declaration:** `BoundaryTori C n` (Presentation:55), a definition of data.

For each label \(i\in\{0,\ldots,n-1\}\), the record supplies a smooth collar diffeomorphism from \(T^2\times[0,1)\) onto an open subset of \(C\). Technically the object is a partial diffeomorphism defined on ambient \(T^2\times[0,\infty)\), with designated source exactly \(T^2\times[0,1)\). Only its restriction to the source carries the asserted inverse and regularity properties. The zero slice lies in the intrinsic boundary of \(C\). The target open sets of distinct collars are disjoint.

This record **does not by itself say that these tori exhaust the boundary**, or that they are incompressible. Boundary exhaustion is a separate field of `RawGraphPresentation`. The number \(n\) may be zero.

The following seven declarations make the convention precise:

| Declaration and location | Exact mathematical content | Status |
|---|---|---|
| `BoundaryTori.torusMap`, Presentation:64 | \(j_i(t)=\operatorname{collar}_i(t,0)\). | Definition |
| `BoundaryTori.image`, :67 | The union \(\bigcup_i j_i(T^2)\). | Definition |
| `BoundaryTori.zero_mem_source`, :70 | Every \((t,0)\) is in the designated collar source because \(0<1\). This helper is private. | Proved, independent of admissions |
| `BoundaryTori.torusMap_smooth`, :77 | Each \(j_i:T^2\to C\) is smooth. | Proved, independent of admissions |
| `BoundaryTori.boundaryMap`, :82 | The same \(j_i\), now packaged as a continuous map for use with \(\pi_1\). | Definition using the proved smoothness |
| `BoundaryTori.torusMap_isEmbedding`, :86 | Each \(j_i\) is a topological embedding. The proof uses collar injectivity and compactness of the torus into the Hausdorff carrier. | Proved, independent of admissions |
| `BoundaryTori.incompressible`, :93 | For every label \(i\) and **every** basepoint \(x\in T^2\), the map \(\pi_1(T^2,x)\to\pi_1(C,j_i(x))\) induced by this actual \(j_i\) is injective. | Definition, not an asserted theorem |

There is no implicit distinction here between “injects into a block” and “injects into an ambient manifold”: the target is exactly the carrier \(C\) passed to this record. At \(n=0\), the last predicate is vacuously true, as expected for an empty torus family.

## T3. Paired torus ports and the quotient they actually define {#t3}

**Declarations:** `TorusPairing` (Presentation:98), `TorusPairing.QuotientSpace` (:118), and `TorusPairing.quotientMap` (:124). These define data, not new existence theorems.

For a compact carrier \(C\), `TorusPairing C` supplies finitely many pairs \((L_i,R_i)\) of closed subsets of \(C\). Each is parametrized by \(T^2\). All the subsets are disjoint, including \(L_i\cap R_i=\varnothing\), and there is a homeomorphism \(a_i:L_i\to R_i\). In the selected parametrizations, \(a_i\) is represented by an actual smooth torus diffeomorphism \(m_i:T^2\to T^2\):

\[
       a_i(\ell_i(t))=r_i(m_i(t)).
\]

Both parametrizations are the zero slices of supplied smooth half-collars, each with source \(T^2\times[0,1)\). The left and matched-right collar derivatives induce opposite orientations from the orientation on \(C\). Precisely, pull back the ambient three-dimensional tangent orientation by the two collar derivatives at \((t,0)\); one equals the negative of the other. This is the code's boundary-orientation reversal condition. It is not an additional assertion that \(m_i\) has a particular degree with respect to an independently chosen torus orientation.

The generic pairing record does not itself contain boundary exhaustion. In `RawGraphPresentation`, boundary exhaustion forces every paired port to lie in the actual boundary. It permits \(L_i\) and \(R_i\) to belong to the same connected component of \(C\), although the subsets themselves must be distinct and disjoint. Thus loop edges are permitted.

`QuotientSpace` is the literal quotient that identifies \(x\in L_i\) with \(a_i(x)\in R_i\), and identifies no other distinct points. It is not a guessed assembled manifold. Disjointness of all ports makes these pairwise identifications an equivalence relation. The inherited compact Hausdorff quotient theorem supplies its Hausdorff topology. `quotientMap` is the actual continuous quotient map \(q:C\to C/{\sim}\).

The inherited gluing relation and its assumptions are in [BoundaryGluing.lean:154](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/Attachment/BoundaryGluing.lean#L154). The exact orientation condition is in [SmoothTorusReconstruction.lean:13](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/Geometrization/SmoothTorusReconstruction.lean#L13).

## T4. What a raw graph presentation contains {#t4}

**Declaration:** `RawGraphPresentation W` (Presentation:129). This is a definition of data, not a theorem that a given \(W\) has such data.

It says that the actual compact oriented smooth carrier \(W\) is obtained by gluing finitely many actual regular circle-bundle blocks along actual paired torus boundaries, with all the following witnesses.

| Lean field(s) | Mathematical data or requirement |
|---|---|
| `cutCarrier`, `components` | A compact smooth oriented cut carrier \(C\), with a positive finite clopen decomposition \(C=\coprod_i C_i\) as in T0. |
| `fibration` | An ordinary circle-bundle structure on each entire compact component \(C_i\), as in T1. |
| `pairing` | Paired internal ports and their smooth matching maps and half-collars, as in T3. Write \(q:C\to Q=C/{\sim}\). |
| `externalCount`, `external`, `cutExternal` | A chosen finite label set for external boundary tori, and disjoint smooth half-collars on both \(W\) and \(C\), with those same labels. |
| `external_exhausted` | The actual boundary of \(W\) equals the union of its external zero-slice tori. |
| `cut_boundary_exhausted` | The actual boundary of \(C\) equals the union of all paired internal ports and all cut external zero-slice tori. |
| `external_disjoint` | The paired internal ports are disjoint from the cut external zero-slice tori. |
| `reconstruction` | An actual homeomorphism \(h:Q\to W\). |
| `quotient_smooth` | The map \(F=h\circ q:C\to W\) is smooth, including in the manifold-with-boundary sense at each boundary point. |
| `quotient_oriented` | At every \(x\in C\), \(dF_x\) is represented by a linear isomorphism carrying the chosen tangent orientation of \(C\) to that of \(W\). Thus the half-side maps have nonsingular orientation-preserving derivatives. |
| `interiorImage`, `interiorDiffeomorph`, `interior_map` | An open subset \(V\subset W\) and a smooth diffeomorphism \(C^\circ\to V\), whose underlying map is exactly \(F\vert_{C^\circ}\). The interior here removes **all** boundary of \(C\), paired and external. |
| `seam`, `seam_source`, `seam_zero` | For each pair, a smooth two-sided seam chart \(s_i:T^2\times(-1,1)\to W\), onto an open set, with \(s_i(t,0)=F(\ell_i(t))\). |
| `seam_positive` | For \(0\leq u<1\), \(s_i(t,u)=F(\text{rightCollar}_i(m_i(t),u))\). |
| `seam_negative` | For \(-1<u\leq0\), \(s_i(t,u)=F(\text{leftCollar}_i(t,-u))\). |
| `seam_interior`, `seam_disjoint` | Each seam chart has image in \(W^\circ\), and these images are pairwise disjoint. |
| `marked_collar` | On **every point of** \(T^2\times[0,1)\), reconstruction of the cut external collar is exactly the corresponding external collar of \(W\). This is equality of parametrized collar maps, not just equality of homology classes. |
| `external_seam_disjoint` | Every external collar image in \(W\) is disjoint from every internal seam image. |
| `leftPiece`, `rightPiece`, `left_owned`, `right_owned` | Each paired port is assigned to an actual connected cut component, and its subset is contained in that component. The assignments may be equal for the two sides of one pair. |
| `externalPiece`, `external_owned` | Each external zero-slice torus is assigned to its actual connected cut component. |

This definition has **no incompressibility hypothesis**. Its auxiliary seams may be compressible; they need not be the final essential tori. It supplies no irreducibility of a block and no geometric metric. It supplies no circle-fiber compatibility between opposite sides of an arbitrary torus pairing; all smooth orientation-compatible torus matchings are allowed. The number of paired or external tori can be zero. The blocks cannot form an empty list.

The external labels and collar parametrizations are genuinely retained **inside the supplied presentation**. But `RawGraphPresentation W` chooses them as part of its own data. A theorem merely concluding `Nonempty (RawGraphPresentation W)` does not by that fact preserve an independently prescribed set of external labels or parametrizations. A separate producer must state any such comparison.

The code uses regular bundles, even when a later Seifert description has exceptional fibers. To obtain a raw presentation from that later description, one must actually remove exceptional-fiber neighborhoods and use regular bundle pieces; an exceptional solid-torus carrier may itself be given a different ordinary bundle structure over a disk. That conversion is not a theorem in these five files.

## T5. A torus decomposition before geometry or incompressibility {#t5}

**Declaration:** `componentCarrier` (TorusDecomposition:10), a definition.

Given the data \(C=\coprod_i C_i\) of T0 and an index \(i\), this is the actual subset \(C_i\), equipped with its inherited smooth chart model and the restriction of \(C\)'s orientation. Compactness comes from \(C_i\) being closed in compact \(C\). No replacement by an abstract diffeomorphic manifold occurs.

**Declaration:** `TorusDecomposition M` (TorusDecomposition:17), a definition of data.

Here \(M\) is an actual connected, nonempty, closed, oriented smooth 3-manifold, **not assumed prime**. A torus decomposition supplies a compact oriented cut carrier with its positive finite components, pairs of torus ports exhausting its entire boundary, a smooth oriented assembly of their literal quotient, and an orientation-preserving diffeomorphism from the assembled quotient to \(M\). Every left and right port is assigned to its actual component. The inherited assembly includes the smooth quotient map, its orientation-preserving nonsingular derivatives, an interior diffeomorphism, matching half-collars, and two-sided seam charts with the exact positive/negative identities described in T4.

Unlike T4, all boundary ports in this record are paired: the reconstructed \(M\) is closed. Unlike `RawGraphPresentation`, this definition asks for no circle fibrations on the pieces. Crucially, **it also asks for neither incompressibility nor geometric metrics**. Those are subsequent premises. There may be zero tori, and there may be loop edges.

**Declaration:** `TorusDecomposition.component` (TorusDecomposition:30), a definition, is just the component carrier above for this particular decomposition.

**Declaration:** `TorusDecomposition.toGeometricDecomposition` (TorusDecomposition:34), an actual data assembly without an admission.

If this same torus decomposition is supplied with (i) injection of every reconstructed seam \(T^2\to M\) on \(\pi_1\), at every torus basepoint, and (ii) a complete model geometry on each actual cut interior, then it becomes a `GeometricDecomposition M` by retaining every carrier, pairing, reconstruction map, and piece assignment unchanged. This construction adds the supplied evidence; it proves no new geometry or incompressibility. It is valid without assuming \(M\) prime, because that assumption belongs to the surrounding prime-decomposition certificate.

## T6. The first admitted topology producer: closed graph carriers admit graph prime factors {#t6}

**Lean:** `GC.GraphManifold.exists_prime_decomposition_of_rawGraphPresentation`, [Refinement:23](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean#L23).

**Status: admitted with `sorry`.**

For **every** connected closed oriented smooth 3-manifold \(M\), and **every supplied** raw graph presentation of the actual \(M\), there exists a `PrimeDecomposition M` such that **each of its chosen factors** also has a raw graph presentation.

In symbols, with “graph” meaning existence of the full data in T4:

\[
\begin{gathered}
 \forall M\;\forall G\in\operatorname{RawGraphPresentation}(M),\\
 \exists\,(P_1,\ldots,P_m,\Phi),\quad
 m\geq1,\quad P_i\text{ prime and graph},\\
 \Phi:\#_iP_i\cong_+M.
\end{gathered}
\]

`NoCuts.carrier M` in the Lean signature means \(M\) itself regarded as a compact carrier with no boundary; it is not an extra topological assumption.

This is a **closed consequence** of the blueprint's relative graph-prime construction. The conclusion preserves the actual selected factor identities: it asserts graph presentations on precisely the \(P_i\) in its reconstruction. But it gives no relation between the original raw seams and the factor seams, no embedded sphere system in \(M\), no punctured factors or cap-ball assignments, and no relative boundary data. The theorem does not accept a preselected prime decomposition which it must use.

It does not assume irreducibility of \(M\), nonempty torus cuts, incompressibility of raw seams, or uniqueness of prime decomposition. It permits \(S^3\) identity factors and \(S^2\times S^1\) factors under the definition in T0.

## T7. The second admitted topology producer: a prime graph carrier admits the endpoint geometry {#t7}

**Lean:** `GC.GraphManifold.exists_geometric_decomposition_of_prime_rawGraphPresentation`, [Refinement:31](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean#L31).

**Status: admitted with `sorry`.**

For every connected closed oriented smooth 3-manifold \(P\), if \(P\) is prime and an actual raw graph presentation of \(P\) is supplied, then \(P\) has a `GeometricDecomposition` as defined in T0 and T5, including essential torus cuts and complete metrics on all the actual cut interiors.

The final torus family and geometric models are chosen by the conclusion. No statement identifies them with the raw auxiliary torus family. Their actual reconstructed inclusions into \(P\) must be injective on \(\pi_1\). The code imposes no minimality, canonical JSJ property, nonparallel condition, prescribed fiber slope, or prohibition on extra product cuts. A torus bundle that could support an uncut Sol metric may therefore instead be represented by retained essential product cuts with complete flat or Seifert-type interiors.

The output's model field may be any of the eight models. This theorem does **not** additionally assert that hyperbolic pieces cannot occur in its chosen output, even though a sharper graph-manifold classification would provide such a statement. Whatever model is chosen must have its actual model atlas and complete metric; a model tag alone is insufficient. Only hyperbolic outputs have the additional finite-volume requirement.

It also does not say that the complete metrics are restrictions of a metric on \(P\), agree across a torus, or retain a prescribed boundary metric. Completeness is required on the whole cut interior, and no complete restriction is claimed after sphere puncturing.

## T8. The actual closed graph assembly {#t8}

**Lean:** `GC.GraphManifold.geometrizes_of_rawGraphPresentation`, [Refinement:37](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean#L37).

**Status: actual proof, depending on the two admissions T6 and T7.**

Given a raw graph presentation of a connected closed oriented smooth \(M\), the proof obtains the selected prime decomposition from T6, obtains geometric decomposition data on each of those same factors from T7, and puts them into `GeometrizationCertificate M`. It uses choice to select the finitely indexed witnesses from existence statements. It does not prove the two producers.

This is a real, compiling connection between supplier and consumer: the graph presentation returned for \(P_i\) is applied to that exact \(P_i\), using the primality proof of that same factor. It does not substitute merely an isomorphic fundamental group or an unmarked list of prime types.

## T9. Hyperbolic-or-graph pieces and the mixed admitted topology producer {#t9}

**Declarations:** `isHyperbolicInteriorGeometry` (Refinement:11) and `HyperbolicOrGraph` (:17), both definitions.

`isHyperbolicInteriorGeometry g` means that the `InteriorGeometry` \(g\) of T0 has its model field equal to the fixed hyperbolic model. The rest of the mathematical force lies in the already supplied `InteriorGeometry`: completeness, an actual hyperbolic model atlas, and finite volume.

For an actual cut component \(C_i\subset C\), `HyperbolicOrGraph C components i` is data of **one of** the following kinds:

1. A complete finite-volume hyperbolic structure on the actual whole interior \(C_i\cap C^\circ\).
2. A full raw graph presentation of the actual compact carrier \(C_i\).

No metric is required in the graph alternative. The alternatives are constructors of a data type, not a theorem that every component has one of these forms. No relation to an ambient Ricci-flow metric is imposed by this particular type; those metric relations belong to the separate collapse/flow input layer.

**Lean:** `GC.GraphManifold.exists_prime_geometric_decomposition_of_hyperbolicOrGraph`, [Refinement:46](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean#L46).

**Status: admitted with `sorry`.**

For every connected closed oriented smooth 3-manifold \(M\), every supplied actual torus decomposition \(D\) of \(M\), and every choice of hyperbolic-or-graph data for each of its actual cut components, assume additionally that **each of the input seam maps into this actual \(M\)** induces an injection on fundamental groups, at every basepoint. Then there exists a prime decomposition of \(M\), together with a geometric decomposition of each of its selected prime factors.

The incompressibility assumption concerns the actual reconstructed seam \(T^2\to M\). Injection into just a hyperbolic model or a single cut piece is not a substitute. The theorem does not assume \(M\) already prime or irreducible, and does not assume that every raw internal graph seam is incompressible. It permits zero ambient seams, no hyperbolic components, and self-pairings between ports of one component.

The conclusion is a new existentially chosen prime decomposition and new geometric cut data. It contains **no comparison identifying the final seams with the input seams, no requirement to retain the supplied hyperbolic metric, and no requirement to preserve the input graph labels or external collars in those final data**. The new output nevertheless reconstructs the same actual \(M\) by the maps required in T0. These omissions make this an endpoint consequence of the fuller relative blueprint, not an implementation of all the relative data in AT13–AT18.

In particular, this admitted theorem has **not** been proved in Lean by combining T6 and T7. Those are statements for closed graph carriers; an argument for graph carriers with boundary, their relative prime/cap construction, and the hyperbolic reattachment is still inside this single mixed admission.

## T10. The actual mixed endpoint assembly {#t10}

**Lean:** `GC.GraphManifold.geometrizes_of_hyperbolicOrGraph`, [Refinement:54](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean#L54).

**Status: actual proof, depending on the admission T9.**

Under exactly the hypotheses of T9, \(M\) geometrizes in the existing certificate sense. The proof takes the prime decomposition and per-factor geometric decompositions supplied by T9 and packages them into the certificate. No further topological input is used in this packaging. It is a short conditional assembly, not a proof of relative graph refinement.

The two graph routes in these files are therefore:

\[
\begin{aligned}
  &\text{raw closed graph presentation}\\
  &\quad\xrightarrow{\text{T6, admitted}}\text{graph prime factors}\\
  &\quad\xrightarrow{\text{T7, admitted}}\text{factor geometries}\\
  &\quad\xrightarrow{\text{T8, proved assembly}}\text{certificate}.
\end{aligned}
\]

and separately

\[
\begin{aligned}
  &\text{actual mixed torus decomposition}\\
  &\qquad{}+\text{ ambient injection}\\
  &\quad\xrightarrow{\text{T9, admitted}}\text{prime factors + geometries}\\
  &\quad\xrightarrow{\text{T10, proved assembly}}\text{certificate}.
\end{aligned}
\]

## FR1. Finite-order compactness: the exact admitted local statement {#fr1}

**Lean:** `DifferentialGeometry.CheegerGromovCompactness.exists_bilinear_form_limit_subsequence_of_bounded_derivatives`, [Compactness:11](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Analysis/Calculus/Compactness/FiniteOrder.lean#L11).

**Status: admitted with `sorry`.**

Let \(E\) be a finite-dimensional complete real normed vector space, \(U\subset E\) an open set, and \(K\geq1\) an integer. Let \(g_i(x)\) be continuous bilinear forms on \(E\), with \(g_i\) defined as a function on all of \(E\) and of class \(C^K\) on \(U\). Symmetry and metric inequalities below are required only on \(U\).

Assume:

1. For **each** integer \(0\leq q\leq K\) and **each** compact set \(S\subset U\), there is a real number \(C_{q,S}\) such that, for all sufficiently large \(i\),
   \[
        \sup_{x\in S}\|D^q g_i(x)\|\leq C_{q,S}.
   \]
   Both \(C_{q,S}\) and the starting index may depend on \(q,S\). There is no single global derivative bound on \(U\), and finitely many early sequence terms need not satisfy a chosen bound.
2. There are two **fixed** real constants \(a,b\), with \(a>0\), such that for **every** index \(i\), every \(x\in U\), and every \(v,w\in E\),
   \[
     g_i(x)(v,w)=g_i(x)(w,v),\qquad
     a\|v\|^2\leq g_i(x)(v,v)\leq b\|v\|^2.
   \]
   The same \(a,b\) apply on all of \(U\) and to all terms, including the early ones. The code does not separately assume \(b>0\); if \(U\ne\varnothing\) and \(\dim E>0\), the displayed inequalities force \(b\geq a>0\).

Then there exist a **single strictly increasing** subsequence map \(\phi:\mathbb N\to\mathbb N\) and a bilinear-form-valued function \(g_\infty\), defined on all of \(E\), such that:

1. \(g_\infty\) is \(C^{K-1}\) on \(U\).
2. On **every** compact \(S\subset U\), \(g_{\phi(i)}\to g_\infty\) in \(C^{K-1}\).
3. On \(U\), \(g_\infty\) is symmetric and satisfies the same two-sided bounds with exactly the original \(a,b\).

For item 2, the code's precise convergence condition is

\[
 \forall\varepsilon>0\;\exists i_0\;\forall i\geq i_0\;
 \forall q\leq K-1\;\forall x\in S,
 \quad \|D^q(g_{\phi(i)}-g_\infty)(x)\|\leq\varepsilon.
\]

This unfolds `MapCPConvergenceOn` in [MapConvergence/Basic.lean:25](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Analysis/Calculus/MapConvergence/Basic.lean#L25). Its derivatives are ordinary ambient Fréchet derivatives; openness of \(U\) ensures that at its points these depend only on the local restrictions to \(U\). Values outside \(U\) are not constrained by the conclusion.

There is no assumption that \(U\) is bounded, connected, relatively compact, convex, or nonempty. At \(K=1\), the conclusion is only a continuous positive-definite limit and uniform convergence on compact subsets. At \(U=\varnothing\), the regularity, convergence and positivity-on-\(U\) assertions are vacuous; a subsequence and arbitrary globally defined bilinear forms still exist. Dimension zero is allowed. These cases do not give a counterexample to the statement.

This is a **local coefficient compactness statement on a fixed Euclidean domain**. It has no sequence of manifolds, basepoints, injectivity-radius hypothesis, volume lower bound, complete limit metric, global atlas, overlap transitions, pointed convergence, comparison embeddings, or sectional-curvature conclusion. Those are substantial additional obligations in the full LFR14/LC81 blueprint. Uniform coordinate derivative bounds are premises here; this theorem does not derive them from curvature derivative bounds.

## FR2. Pulling back a finite-regularity metric: the exact admitted statement {#fr2}

**Lean:** `DifferentialGeometry.Geometry.exists_pullback_metric_of_finite_diffeomorph`, [Pullback:16](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Metric/Pullback/FiniteRegularity.lean#L16).

**Status: admitted with `sorry`.**

Let \(M,N\) already be smooth manifolds, with general real finite-dimensional models with corners \(I,J\), respectively. The statement does not assume compactness, connectedness, nonemptiness, completeness, boundarylessness, Hausdorffness, or second countability. It uses the manifold structures and finite-dimensional normed tangent models needed for the derivative and metric definitions. The source and target model vector spaces need not be declared to have equal dimension in advance; existence of the diffeomorphism is the relevant premise.

Let \(K,s,r\in\mathbb N\) satisfy

\[
                 r\leq K,\qquad r+1\leq s.
\]

Let \(g\) be a \(C^K\) Riemannian metric on \(N\), and let \(f:M\to N\) be a \(C^s\) diffeomorphism, meaning an actual bijection whose forward **and inverse** maps are \(C^s\). Then there exists a \(C^r\) Riemannian metric \(h\) on \(M\) satisfying the **exact tensor identity**

\[
          h_x(v,w)=g_{f(x)}(df_xv,df_xw)
          \quad\text{for every }x\in M,\;v,w\in T_xM.
\]

Here a \(C^r\) Riemannian metric means a continuously varying symmetric positive-definite bilinear form of the asserted regularity on the tangent bundle, compatible with its existing fiber topology. It is not an arbitrary semidefinite tensor. The code's `Diffeomorph` definition explicitly contains \(C^s\) regularity of the inverse; since \(s\geq1\), the derivative has the isomorphism property needed for positivity.

The order bound is the familiar one-derivative cost in pulling back a metric:

\[
                h\in C^{\min(K,s-1)},
\]

or any weaker finite order \(r\) allowed by the inequalities. The code states existence at each such specified \(r\), rather than a maximum-order formula. Natural-number subtraction and the lower bound \(s\geq1\) therefore cause no exceptional \(s=0\) case.

The conclusion contains no explicit length, distance, completeness, volume, or curvature-preservation theorem. It contains the exact tensor formula from which appropriate preservation results can subsequently be proved. It asserts neither smoothing of \(g\) nor a curvature-preserving perturbation. It also does **not** construct a compatible smooth structure on a manifold initially given only a finite-regularity atlas: both carriers are already smooth at the start of this theorem.

## FR3. The two proved regularity-budget corollaries {#fr3}

**Lean:** `exists_pullback_metric_of_diffeomorph_one_order_higher`, [Pullback:26](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Metric/Pullback/FiniteRegularity.lean#L26).

**Status: actual proof by specialization of the admission FR2.** For any natural \(K\), a \(C^{K+1}\) diffeomorphism pulls a \(C^K\) metric back to a \(C^K\) metric with the exact displayed tensor identity. This includes \(K=0\): a \(C^1\) diffeomorphism pulls a continuous metric back to a continuous metric. The proof substitutes \(s=K+1\) and \(r=K\) into FR2.

**Lean:** `exists_pullback_metric_of_diffeomorph_three_orders_lower`, [Pullback:35](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Metric/Pullback/FiniteRegularity.lean#L35).

**Status: actual proof by specialization of the admission FR2.** For an integer \(m\geq4\), a \(C^{m-3}\) diffeomorphism pulls a \(C^m\) metric back to a \(C^{m-4}\) metric with exactly the same tensor formula. The hypothesis \(m\geq4\) controls truncated natural-number subtraction. At \(m=4\) the map is \(C^1\) and the output metric is \(C^0\). The proof supplies \(r=m-4\leq m\) and \(r+1\leq m-3\) to FR2.

For the blueprint's common substitution \(m=K-1\), this second statement gives order \(K-5\), provided \(K\geq5\). It does not claim that every model map in the blueprint is automatically \(C^{m-3}\); a consumer must supply such a map. It also gives no quantitative norm bound on the pullback or its difference from another metric.

## R1. What is and is not yet connected in Lean {#topology-r1}

The statement network in this part has two actual topology assemblies (T8 and T10), and two actual regularity specializations (FR3). The mixed topology producer T9 is one large admission rather than a proof assembled from the relative constructions of the blueprint.

The local compactness theorem FR1 and finite pullback theorem FR2 are separate prepared statements. At this commit, searches of the Lean sources show no mathematical application of FR1 beyond its own declaration, and no mathematical application of FR2 beyond its two FR3 corollaries. In particular, these files do not yet demonstrate that their outputs satisfy the hypotheses of the late-flow or static-collapse producers. Importing a file or listing it in the declaration audit does not establish such an application.

Similarly, the two closed graph admissions T6 and T7 do feed T8, but they are not called in the proof body of the mixed admission T9. A future relative-refinement proof needs additional intermediate statements to expose that connection.

## R2. Approval points and weaknesses identified by this rereading {#topology-r2}

I found **no specific counterexample or internal contradiction** in these five admitted statements during this rereading. That is a bounded review judgment, not a mathematical proof or a claim that all stronger blueprint arguments have been checked. The most consequential decisions for Bennett Chow and Peng Lu are these:

1. **Approve the regular-bundle meaning of raw graph presentation.** Its fibers are all ordinary circles; exceptional Seifert fibers must be removed or represented by further regular blocks before supplying it. The bases may be nonorientable. There is no global circle action in the definition.
2. **Approve the endpoint consequence rather than a full relative export.** T6, T7 and especially T9 omit the sphere/cap ledger and comparisons preserving the given decorations. This suffices for their chosen final certificate conclusion. It does not yet provide the finer relative interfaces needed to implement the blueprint proof in parallel without further design.
3. **Check the existential freedom in T9 deliberately.** The final chosen metrics and cuts need not retain the input hyperbolic metrics or seams. This is a weaker conclusion, not an inconsistency; any task expecting to reuse those exact markings cannot treat T9 as already exporting them.
4. **Keep nonempty components separate from possibly empty seam families.** The underlying `Components` record excludes an empty carrier. Empty late-flow slices must be handled elsewhere. No-cut geometric manifolds remain legal because the torus index may be empty.
5. **Do not call FR1 the global compactness theorem.** It is only the fixed-chart coefficient subsequence lemma. Producing the chart bounds, a global limit and actual comparison embeddings remains unrepresented here.
6. **Do not call FR2 a smooth-metric category bridge.** Its tensor remains only finitely regular. Choosing the initial compatible smooth carrier and deriving metric/curvature invariance are additional steps. FR2's actual content is the precise finite pullback regularity statement.

The existing complete-interior metric convention is also essential: only hyperbolic pieces require finite volume, and extra essential product cuts are permitted. Requiring all geometries to have finite volume or demanding an uncut model for every torus bundle would change these statements substantially.

## R3. Evidence, source comparison, and review limits {#topology-r3}

This review read all five actual Lean files, then expanded their dependencies for compact carriers and components, manifold-with-boundary interiors, finite torus gluing relations, smooth oriented reconstruction, prime decomposition, endpoint geometry, metric regularity, diffeomorphism regularity, and the exact \(C^p\)-convergence predicate. Source locations and authored-declaration coverage are recorded in `topology_finite_regularity_coverage.json` next to this report.

The corresponding natural-language blueprint bodies were reread at:

- `master207A.tex`, lines 8526–8588: G01–G05, especially ordinary circle bundles, nonorientable bases, raw versus essential cuts, and actual ambient injection.
- `master207A.tex`, lines 9467–9579: RG05–RG06, actual relative graph-prime/good-block output and its terminal block list.
- `master207A.tex`, lines 10378–10431: GM06, full marked graph refinement and complete E1 witnesses.
- `master207B.tex`, lines 11895–12036: AT13–AT18, relative prime/cap data, good-block refinement, actual capped ambient injection and prime reconstruction.
- `master207A.tex`, lines 24826–24860: LFR01, compatible smooth structures and the finite derivative ledger.
- `master207A.tex`, lines 25872–25908 and 25970–26030: LFR14, finite-model construction and actual comparison maps.
- `master207A.tex`, lines 26128–26144: the \(m=K-1\) consumer regularity distinction.

Those comparisons identify which conclusions are intentionally omitted; they do not silently import them into the Lean signatures. No new theorem contract or source classification was changed. Consequently this report does not claim a new primary-source literature or erratum audit; the previously recorded source checks for these unchanged mathematical routes retain their historical scope.

Proof status was cross-checked against the recorded elaborated declaration audit at this commit: the five admitted theorem names and four admission-dependent corollary/assembly theorem names have `sorryAx`; the three collar proofs do not. This report did not rebuild Lean or reprove any admission. The previously recorded build checks elaboration and dependencies; it does not establish the mathematical truth of a `sorry` statement.


# Suggested joint review and the limits of this report {#joint-review}

## A practical order for the mathematical review {#review-order}

Read E1–E2 first and decide whether that is the desired theorem. Then read
F3–F8 together: these show the exact hypotheses that supply the endpoint,
the order in which choices are made, and what the written assembly actually
uses. C2, C4–C10, HA-2–HA-4, and T9 contain the principal remaining
mathematical assertions. Finally, read the prepared branches, including
Mostow–Prasad, the two closed graph refinements, and FR1–FR3. They are useful
future work, but are not already proofs inside the main composite admissions.

The following questions can serve as a review worksheet. A request to change
one of these statements is a specification correction, not a request to
begin filling its proof immediately.

| Review question | Where to look |
| --- | --- |
| Is the smooth, connected, closed, oriented endpoint, with a noncanonical prime list and collared fundamental-group-injective cuts, exactly the desired public statement? | E1, T0, T5 |
| Are the eight fixed model metrics and the finite-volume requirement only for hyperbolic interiors correct? | E2, HA-1.3–HA-1.4 |
| Do the static hypotheses suffice with intrinsic balls, whole-ball derivative estimates, uncapped curvature radius, and arbitrary positive derivative function? | C2, C6, C8–C10 |
| Is the boundary statement correct with diameter measured in the carrier, no pairwise collar-disjointness field, and only boundary-image/index retention? | C4–C5, C8–C9 |
| Is the selected-flow assertion true with precisely its sequence-dependent derivative function and its fixed-flow-before-sequence quantifiers? | F4, F6–F8 |
| Is the stated disk class the one for which the intended existence and comparison arguments work, including smooth immersion at the boundary and exact parametrized boundary equality? | HA-3.1–HA-3.4 |
| Can the actual physical area have the stipulated continuity and strict upper barriers at every surgery time on the same future half-line? | F5, HA-2, HA-5 |
| Are the weaker existential outputs of mixed refinement sufficient, even though they do not retain prescribed incoming seams, metrics or markings? | T6–T10 |
| Are the finite-order statements correct at their lowest orders, and understood as local coefficient compactness and finite pullback rather than the full category bridge? | FR1–FR3 |
| Which of the large admitted producers must be subdivided before the team can safely assign independent proof tasks? | F7, C11, HA-4.4, T9 |

## What the rereading found {#review-findings}

The direct and independent rereadings found no concrete counterexample or
explicit contradiction in the new admitted statements. This is a bounded
review judgment, not a proof of those statements or certification that all
source-to-interface comparisons are complete. The mathematical obligations
are exactly the assertions marked admitted, together with any inherited
foundation obligations outside the scope of this review.

The most substantial finding concerns **how much mathematics remains inside
the largest admissions**. The selected-flow theorem contains the production
of the actual late geometric pieces and the incompressibility obstruction.
The mixed-refinement theorem contains the relative topology needed to reach
the endpoint. Their short consumers compile, but this does not make those
large producers small tasks.

There is also a distinction between **a faithful endpoint consequence and
a full translation of a blueprint node**. Several statements deliberately
export less data than the corresponding blueprint development: relative
marking comparisons, persistent families, global parameter coherence beyond
the common delta function, and the global finite-regularity construction
remain outside the displayed interfaces. These omissions have been listed
where they occur rather than supplied implicitly by the prose.

The observation that the area-obstruction premise is equivalent to injection
once the scalar contradiction is granted is a logical analysis in this
report. It is not an additional equivalence theorem claimed to exist in Lean.
Likewise, explanatory proof sketches for admitted elementary lemmas are
identified as intended arguments, not as completed proof bodies.

## Evidence and the meaning of complete coverage {#report-evidence}

The declaration register below accounts for **all 121 authored declarations
in the 22 new mathematical files**, including the private collar helper.
Generated constructors and projections are covered by their parent data
definitions and their field descriptions; they are not presented as hundreds
of separate mathematical claims. The recorded elaborated types and axiom
closures were used to distinguish direct admissions from actual proofs with
or without admitted dependencies.

For this report, four family translations were read against the actual Lean
files, and the endpoint/flow translation received independent cross-checks
from the other reviewers. That process corrected a prose overstatement:
the generic area-obstruction predicate does not itself tie its torus carrier
to a flow component; the surrounding late-sequence predicate makes that
identification. The report also makes explicit that the topological assembly
discards the supplied induced-metric equalities, although those equalities
constrain the geometric producer's input to that assembly.

Fresh mechanical checks for the report verify the frozen source hashes,
complete declaration coverage, the 17 direct admission names, the six
endpoint-reachable admissions, and the absence of Lean-source changes.
The PDF is rendered and inspected for legible equations and tables. These
are document and consistency checks. The earlier successful Lean build is
reported from its pinned verification receipt; it is not described as a new
build or as a proof of the admitted mathematics.

The companion files include the editable combined Markdown and standalone
LaTeX, the exact text of the 22 skeleton modules in `exact_sources.txt`,
coverage records, and a source-hash inventory. The source text is frozen at
the commit named on the cover. References to inherited definitions have
their own pinned source links and hashes; including a source in that
inventory does not assert that every theorem in it received a fresh proof
audit. Primary-source and blueprint passages actually reopened are listed
in the family sections. Older source and errata checks retain their stated
historical scope.

Your approval can therefore be recorded at two levels: whether the displayed
mathematical statements are correct and appropriate, and whether a particular
producer has been decomposed sufficiently for assignment. The present report
does not presume either approval and does not modify the Lean skeleton.


# Complete declaration register {#declaration-register}
This register is exhaustive for the 121 authored declarations. Each entry gives its status, a link to the mathematical explanation, and the exact source line at the frozen commit. All file paths are under `DifferentialGeometry/`. A proof without a skeleton admission still uses the inherited library; this label is not a new audit of that whole library.

```{=latex}
\Needspace{6\baselineskip}
```

## M01. FiniteOrder.lean

**File:** `Analysis/Calculus/Compactness/FiniteOrder.lean`

- `DifferentialGeometry.CheegerGromovCompactness.exists_bilinear_form_limit_subsequence_of_bounded_derivatives`\
  Admitted. [Explanation: FR1](#fr1); [source line 11](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Analysis/Calculus/Compactness/FiniteOrder.lean#L11).

```{=latex}
\Needspace{6\baselineskip}
```

## M02. AreaUpperBarrier.lean

**File:** `Analysis/ODE/AreaUpperBarrier.lean`

- `DifferentialGeometry.Analysis.hasLocalSmoothUpperBarrier`\
  Definition/construction. [Explanation: HA-2.1](#ha-2-1); [source line 13](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Analysis/ODE/AreaUpperBarrier.lean#L13).

- `DifferentialGeometry.Analysis.not_nonnegative_area_upper_barriers_shift`\
  Admitted. [Explanation: HA-2.2](#ha-2-2); [source line 18](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Analysis/ODE/AreaUpperBarrier.lean#L18).

- `DifferentialGeometry.Analysis.not_nonnegative_area_upper_barriers`\
  Written proof; admitted dependence. [Explanation: HA-2.3](#ha-2-3); [source line 28](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Analysis/ODE/AreaUpperBarrier.lean#L28).

- `DifferentialGeometry.Analysis.not_nonnegative_area_upper_barriers_pi_shift`\
  Written proof; admitted dependence. [Explanation: HA-2.3](#ha-2-3); [source line 39](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Analysis/ODE/AreaUpperBarrier.lean#L39).

- `DifferentialGeometry.Analysis.not_nonnegative_area_upper_barriers_pi`\
  Written proof; admitted dependence. [Explanation: HA-2.3](#ha-2-3); [source line 52](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Analysis/ODE/AreaUpperBarrier.lean#L52).

```{=latex}
\Needspace{6\baselineskip}
```

## M03. CurvatureScale.lean

**File:** `Geometry/Collapse/CurvatureScale.lean`

- `DifferentialGeometry.Geometry.Collapse.curvatureRadius`\
  Definition/construction. [Explanation: C2](#collapse-radius); [source line 23](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CurvatureScale.lean#L23).

- `DifferentialGeometry.Geometry.Collapse.ballVolume`\
  Definition/construction. [Explanation: C2](#collapse-radius); [source line 28](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CurvatureScale.lean#L28).

- `DifferentialGeometry.Geometry.Collapse.euclideanUnitBallVolume`\
  Definition/construction. [Explanation: C2](#collapse-radius); [source line 31](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CurvatureScale.lean#L31).

- `DifferentialGeometry.Geometry.Collapse.volumeCollapsedAtCurvatureScale`\
  Definition/construction. [Explanation: C2](#collapse-radius); [source line 33](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CurvatureScale.lean#L33).

- `DifferentialGeometry.Geometry.Collapse.curvatureDerivativesControlled`\
  Definition/construction. [Explanation: C2](#collapse-radius); [source line 38](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CurvatureScale.lean#L38).

- `DifferentialGeometry.Geometry.Collapse.curvatureRadius_pos`\
  Admitted. [Explanation: C2](#collapse-radius); [source line 46](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CurvatureScale.lean#L46).

- `DifferentialGeometry.Geometry.Collapse.curvatureRadius_eq_top_iff`\
  Admitted. [Explanation: C2](#collapse-radius); [source line 50](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CurvatureScale.lean#L50).

- `DifferentialGeometry.Geometry.Collapse.curvatureDerivativesControlled_mono_threshold`\
  Written proof; no skeleton admission. [Explanation: C2](#collapse-radius); [source line 55](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CurvatureScale.lean#L55).

```{=latex}
\Needspace{6\baselineskip}
```

## M04. CuspBoundary.lean

**File:** `Geometry/Collapse/CuspBoundary.lean`

- `DifferentialGeometry.Geometry.Collapse.cuspMetricError`\
  Definition/construction. [Explanation: C4](#collapse-cuspembedding); [source line 15](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CuspBoundary.lean#L15).

- `DifferentialGeometry.Geometry.Collapse.cuspMetricErrorBound`\
  Definition/construction. [Explanation: C4](#collapse-cuspembedding); [source line 22](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CuspBoundary.lean#L22).

- `DifferentialGeometry.Geometry.Collapse.CuspEmbedding`\
  Definition/construction. [Explanation: C4](#collapse-cuspembedding); [source line 29](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CuspBoundary.lean#L29).

- `DifferentialGeometry.Geometry.Collapse.NearlyCuspidalBoundary`\
  Definition/construction. [Explanation: C4](#collapse-cuspembedding); [source line 43](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CuspBoundary.lean#L43).

- `DifferentialGeometry.Geometry.Collapse.distanceToBoundary`\
  Definition/construction. [Explanation: C5](#collapse-boundarydistance); [source line 56](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CuspBoundary.lean#L56).

- `DifferentialGeometry.Geometry.Collapse.boundaryVolumeCollapsed`\
  Definition/construction. [Explanation: C5](#collapse-boundarydistance); [source line 60](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CuspBoundary.lean#L60).

- `DifferentialGeometry.Geometry.Collapse.CuspEmbedding.weaken`\
  Definition/construction. [Explanation: C4](#collapse-cuspembedding); [source line 64](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CuspBoundary.lean#L64).

- `DifferentialGeometry.Geometry.Collapse.NearlyCuspidalBoundary.weaken`\
  Definition/construction. [Explanation: C4](#collapse-cuspembedding); [source line 70](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/CuspBoundary.lean#L70).

```{=latex}
\Needspace{6\baselineskip}
```

## M05. GraphManifold.lean

**File:** `Geometry/Collapse/GraphManifold.lean`

- `DifferentialGeometry.Geometry.Collapse.closedCollapseHypotheses`\
  Definition/construction. [Explanation: C6](#collapse-hypotheses); [source line 11](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/GraphManifold.lean#L11).

- `DifferentialGeometry.Geometry.Collapse.boundaryCollapseHypotheses`\
  Definition/construction. [Explanation: C6](#collapse-hypotheses); [source line 17](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/GraphManifold.lean#L17).

- `DifferentialGeometry.Geometry.Collapse.staticCollapseHypotheses`\
  Definition/construction. [Explanation: C6](#collapse-hypotheses); [source line 22](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/GraphManifold.lean#L22).

- `DifferentialGeometry.Geometry.Collapse.volumeCollapsedAtCurvatureScale_mono`\
  Written proof; no skeleton admission. [Explanation: C6](#collapse-hypotheses); [source line 26](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/GraphManifold.lean#L26).

- `DifferentialGeometry.Geometry.Collapse.closedCollapseHypotheses_mono`\
  Written proof; no skeleton admission. [Explanation: C6](#collapse-hypotheses); [source line 35](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/GraphManifold.lean#L35).

- `DifferentialGeometry.Geometry.Collapse.boundaryCollapseHypotheses_mono`\
  Written proof; no skeleton admission. [Explanation: C6](#collapse-hypotheses); [source line 43](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/GraphManifold.lean#L43).

- `DifferentialGeometry.Geometry.Collapse.exists_rawGraphPresentation_of_nonnegative`\
  Admitted. [Explanation: C8](#collapse-admitted); [source line 52](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/GraphManifold.lean#L52).

- `DifferentialGeometry.Geometry.Collapse.exists_closed_graph_threshold`\
  Admitted. [Explanation: C8](#collapse-admitted); [source line 60](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/GraphManifold.lean#L60).

- `DifferentialGeometry.Geometry.Collapse.exists_boundary_graph_threshold`\
  Admitted. [Explanation: C8](#collapse-admitted); [source line 68](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/GraphManifold.lean#L68).

- `DifferentialGeometry.Geometry.Collapse.exists_graph_threshold`\
  Written proof; admitted dependence. [Explanation: C9](#collapse-composition); [source line 80](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/GraphManifold.lean#L80).

- `DifferentialGeometry.Geometry.Collapse.exists_componentwise_graph_threshold`\
  Written proof; admitted dependence. [Explanation: C9](#collapse-composition); [source line 97](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/GraphManifold.lean#L97).

```{=latex}
\Needspace{6\baselineskip}
```

## M06. TorusDecomposition.lean

**File:** `Geometry/Collapse/TorusDecomposition.lean`

- `DifferentialGeometry.Geometry.Collapse.cutPieceMap`\
  Definition/construction. [Explanation: F3](#f3-induced-cut-metric); [source line 11](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/TorusDecomposition.lean#L11).

- `DifferentialGeometry.Geometry.Collapse.isInducedCutMetric`\
  Definition/construction. [Explanation: F3](#f3-induced-cut-metric); [source line 16](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/TorusDecomposition.lean#L16).

- `DifferentialGeometry.Geometry.Collapse.HyperbolicOrCollapsed`\
  Definition/construction. [Explanation: F3](#f3-induced-cut-metric); [source line 25](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/TorusDecomposition.lean#L25).

- `DifferentialGeometry.Geometry.Collapse.geometrizes_of_hyperbolicOrCollapsed`\
  Written proof; admitted dependence. [Explanation: F3](#f3-induced-cut-metric); [source line 41](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/TorusDecomposition.lean#L41).

```{=latex}
\Needspace{6\baselineskip}
```

## M07. UniformDerivativeBounds.lean

**File:** `Geometry/Collapse/UniformDerivativeBounds.lean`

- `DifferentialGeometry.Geometry.Collapse.exists_common_curvature_derivative_bound`\
  Admitted. [Explanation: C10](#collapse-uniform); [source line 10](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Collapse/UniformDerivativeBounds.lean#L10).

```{=latex}
\Needspace{6\baselineskip}
```

## M08. Metric.lean

**File:** `Geometry/Connection/TensorNabla/Iterated/Metric.lean`

- `DifferentialGeometry.Geometry.Connection.metricCovariantDerivative`\
  Definition/construction. [Explanation: C1](#collapse-tensor); [source line 17](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Connection/TensorNabla/Iterated/Metric.lean#L17).

- `DifferentialGeometry.Geometry.Connection.iteratedMetricCovariantDerivative`\
  Definition/construction. [Explanation: C1](#collapse-tensor); [source line 30](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Connection/TensorNabla/Iterated/Metric.lean#L30).

```{=latex}
\Needspace{6\baselineskip}
```

## M09. DerivativeNorm.lean

**File:** `Geometry/Curvature/Metric/DerivativeNorm.lean`

- `DifferentialGeometry.Geometry.Curvature.curvatureDerivativeNorm`\
  Definition/construction. [Explanation: C1](#collapse-tensor); [source line 18](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Curvature/Metric/DerivativeNorm.lean#L18).

```{=latex}
\Needspace{6\baselineskip}
```

## M10. CuspIncompressibility.lean

**File:** `Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean`

- `DifferentialGeometry.Geometry.RicciFlow.cusp_injective_of_exterior_area_barriers`\
  Written proof; admitted dependence. [Explanation: HA-4.1](#ha-4-1); [source line 15](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean#L15).

- `DifferentialGeometry.Geometry.RicciFlow.cusp_slice_injective_iff`\
  Written proof; no skeleton admission. [Explanation: HA-4.2](#ha-4-2); [source line 43](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean#L43).

- `DifferentialGeometry.Geometry.RicciFlow.incompressible_of_area_barriers`\
  Written proof; admitted dependence. [Explanation: HA-4.3](#ha-4-3); [source line 51](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean#L51).

- `DifferentialGeometry.Geometry.RicciFlow.incompressible_of_shifted_area_barriers`\
  Written proof; admitted dependence. [Explanation: HA-4.3](#ha-4-3); [source line 67](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean#L67).

```{=latex}
\Needspace{6\baselineskip}
```

## M11. ExteriorDiskFlow.lean

**File:** `Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean`

- `GC.LongTime.postStage`\
  Definition/construction. [Explanation: HA-5.1](#ha-5-1); [source line 18](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean#L18).

- `GC.LongTime.postMetric`\
  Definition/construction. [Explanation: HA-5.2](#ha-5-2); [source line 22](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean#L22).

- `GC.LongTime.postStage_regularSlice`\
  Written proof; no skeleton admission. [Explanation: HA-5.3](#ha-5-3); [source line 26](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean#L26).

- `GC.LongTime.postMetric_regularSlice`\
  Written proof; no skeleton admission. [Explanation: HA-5.3](#ha-5-3); [source line 37](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean#L37).

- `GC.LongTime.exteriorDiskArea`\
  Definition/construction. [Explanation: HA-5.4](#ha-5-4); [source line 57](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean#L57).

- `GC.LongTime.exteriorDiskArea_nonneg`\
  Written proof; no skeleton admission. [Explanation: HA-5.4](#ha-5-4); [source line 62](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean#L62).

- `GC.LongTime.exteriorDiskArea_eq`\
  Written proof; no skeleton admission. [Explanation: HA-5.4](#ha-5-4); [source line 68](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean#L68).

```{=latex}
\Needspace{6\baselineskip}
```

## M12. LateDecomposition.lean

**File:** `Geometry/Flow/RicciFlow/LongTime/LateDecomposition.lean`

- `GC.LongTime.hasCommonNeckAccuracy`\
  Definition/construction. [Explanation: F4](#f4-common-accuracy); [source line 17](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/LateDecomposition.lean#L17).

- `GC.LongTime.RegularSlice.componentMetric`\
  Definition/construction. [Explanation: F2](#f2-slices); [source line 23](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/LateDecomposition.lean#L23).

- `GC.LongTime.hasExteriorAreaObstructionAfter`\
  Definition/construction. [Explanation: F5](#f5-area-obstruction); [source line 29](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/LateDecomposition.lean#L29).

- `GC.LongTime.hasLateSequenceTests`\
  Definition/construction. [Explanation: F6](#f6-sequence-tests); [source line 47](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/LateDecomposition.lean#L47).

- `GC.LongTime.exists_surgery_with_late_sequence_tests`\
  Admitted. [Explanation: F7](#f7-selected-flow); [source line 62](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/LateDecomposition.lean#L62).

- `GC.LongTime.components_geometrize_of_late_sequence_tests`\
  Written proof; admitted dependence. [Explanation: F8](#f8-bad-sequence-proof); [source line 71](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/LateDecomposition.lean#L71).

- `GC.LongTime.geometrizes_of_metric`\
  Written proof; admitted dependence. [Explanation: F9](#f9-capstone); [source line 99](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/LateDecomposition.lean#L99).

```{=latex}
\Needspace{6\baselineskip}
```

## M13. RegularSlice.lean

**File:** `Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean`

- `GC.LongTime.RegularSlice`\
  Definition/construction. [Explanation: F2](#f2-slices); [source line 13](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean#L13).

- `GC.LongTime.RegularSlice.history`\
  Definition/construction. [Explanation: F2](#f2-slices); [source line 24](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean#L24).

- `GC.LongTime.RegularSlice.stage`\
  Definition/construction. [Explanation: F2](#f2-slices); [source line 26](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean#L26).

- `GC.LongTime.RegularSlice.metric`\
  Definition/construction. [Explanation: F2](#f2-slices); [source line 29](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean#L29).

- `GC.LongTime.RegularSlice.normalizedMetric`\
  Definition/construction. [Explanation: F2](#f2-slices); [source line 32](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean#L32).

- `GC.LongTime.RegularSlice.curvatureOneMetric`\
  Definition/construction. [Explanation: F2](#f2-slices); [source line 35](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean#L35).

- `GC.LongTime.RegularSlice.initial`\
  Definition/construction. [Explanation: F2](#f2-slices); [source line 38](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean#L38).

- `GC.LongTime.hasArbitrarilyLateNonemptySlices`\
  Definition/construction. [Explanation: F2](#f2-slices); [source line 43](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean#L43).

- `GC.LongTime.exists_regular_slice_after`\
  Written proof; no skeleton admission. [Explanation: F2](#f2-slices); [source line 47](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean#L47).

- `GC.LongTime.empty_slice_or_arbitrarily_late`\
  Written proof; no skeleton admission. [Explanation: F2](#f2-slices); [source line 53](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean#L53).

- `GC.LongTime.exists_common_late_slice`\
  Written proof; no skeleton admission. [Explanation: F2](#f2-slices); [source line 67](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean#L67).

- `GC.LongTime.geometrizes_of_late_slice_supply`\
  Written proof; no skeleton admission. [Explanation: F2](#f2-slices); [source line 91](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/RegularSlice.lean#L91).

```{=latex}
\Needspace{6\baselineskip}
```

## M14. Cusp.lean

**File:** `Geometry/Hyperbolic/Cusp.lean`

- `DifferentialGeometry.Geometry.Hyperbolic.CuspHalfSpace`\
  Definition/construction. [Explanation: C3](#collapse-cuspmodel); [source line 10](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Hyperbolic/Cusp.lean#L10).

- `DifferentialGeometry.Geometry.Hyperbolic.cuspDomain`\
  Definition/construction. [Explanation: C3](#collapse-cuspmodel); [source line 12](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Hyperbolic/Cusp.lean#L12).

- `DifferentialGeometry.Geometry.Hyperbolic.HyperbolicCusp`\
  Definition/construction. [Explanation: C3](#collapse-cuspmodel); [source line 14](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Hyperbolic/Cusp.lean#L14).

- `DifferentialGeometry.Geometry.Hyperbolic.cusp_constant_sectional_curvature`\
  Admitted. [Explanation: C3](#collapse-cuspmodel); [source line 23](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Hyperbolic/Cusp.lean#L23).

```{=latex}
\Needspace{6\baselineskip}
```

## M15. ModelAtlas.lean

**File:** `Geometry/Hyperbolic/ModelAtlas.lean`

- `DifferentialGeometry.Geometry.Hyperbolic.has_hyperbolic_atlas_of_curvature_neg_one`\
  Admitted. [Explanation: HA-1.3](#ha-1-3); [source line 17](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Hyperbolic/ModelAtlas.lean#L17).

- `DifferentialGeometry.Geometry.Hyperbolic.finiteVolumeGeometricStructure`\
  Definition/construction; admitted dependence. [Explanation: HA-1.4](#ha-1-4); [source line 23](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Hyperbolic/ModelAtlas.lean#L23).

- `DifferentialGeometry.Geometry.Hyperbolic.finiteVolumeGeometricStructure_model`\
  Written proof; admitted dependence. [Explanation: HA-1.4](#ha-1-4); [source line 42](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Hyperbolic/ModelAtlas.lean#L42).

```{=latex}
\Needspace{6\baselineskip}
```

## M16. Rigidity.lean

**File:** `Geometry/Hyperbolic/Rigidity.lean`

- `DifferentialGeometry.Geometry.Hyperbolic.hasConstantSectionalCurvature`\
  Definition/construction. [Explanation: HA-1.1](#ha-1-1); [source line 20](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Hyperbolic/Rigidity.lean#L20).

- `DifferentialGeometry.Geometry.Hyperbolic.mostow_prasad`\
  Admitted. [Explanation: HA-1.2](#ha-1-2); [source line 24](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Hyperbolic/Rigidity.lean#L24).

```{=latex}
\Needspace{6\baselineskip}
```

## M17. FiniteRegularity.lean

**File:** `Geometry/Metric/Pullback/FiniteRegularity.lean`

- `DifferentialGeometry.Geometry.exists_pullback_metric_of_finite_diffeomorph`\
  Admitted. [Explanation: FR2](#fr2); [source line 16](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Metric/Pullback/FiniteRegularity.lean#L16).

- `DifferentialGeometry.Geometry.exists_pullback_metric_of_diffeomorph_one_order_higher`\
  Written proof; admitted dependence. [Explanation: FR3](#fr3); [source line 26](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Metric/Pullback/FiniteRegularity.lean#L26).

- `DifferentialGeometry.Geometry.exists_pullback_metric_of_diffeomorph_three_orders_lower`\
  Written proof; admitted dependence. [Explanation: FR3](#fr3); [source line 35](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/Metric/Pullback/FiniteRegularity.lean#L35).

```{=latex}
\Needspace{6\baselineskip}
```

## M18. ExteriorDiskArea.lean

**File:** `Geometry/MinimalSurface/ExteriorDiskArea.lean`

- `DifferentialGeometry.Geometry.MinimalSurface.isExteriorSpanningDisk`\
  Definition/construction. [Explanation: HA-3.1](#ha-3-1); [source line 15](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/MinimalSurface/ExteriorDiskArea.lean#L15).

- `DifferentialGeometry.Geometry.MinimalSurface.leastExteriorDiskArea`\
  Definition/construction. [Explanation: HA-3.2](#ha-3-2); [source line 22](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/MinimalSurface/ExteriorDiskArea.lean#L22).

- `DifferentialGeometry.Geometry.MinimalSurface.leastExteriorDiskArea_nonneg`\
  Written proof; no skeleton admission. [Explanation: HA-3.2](#ha-3-2); [source line 27](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/MinimalSurface/ExteriorDiskArea.lean#L27).

- `DifferentialGeometry.Geometry.MinimalSurface.leastExteriorDiskArea_le`\
  Written proof; no skeleton admission. [Explanation: HA-3.2](#ha-3-2); [source line 33](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/MinimalSurface/ExteriorDiskArea.lean#L33).

- `DifferentialGeometry.Geometry.MinimalSurface.exteriorDiskAreaOn`\
  Definition/construction. [Explanation: HA-3.3](#ha-3-3); [source line 43](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/MinimalSurface/ExteriorDiskArea.lean#L43).

- `DifferentialGeometry.Geometry.MinimalSurface.exteriorDiskAreaOn_nonneg`\
  Written proof; no skeleton admission. [Explanation: HA-3.3](#ha-3-3); [source line 52](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/MinimalSurface/ExteriorDiskArea.lean#L52).

- `DifferentialGeometry.Geometry.MinimalSurface.continuousOn_leastExteriorDiskArea_of_local_disk_comparisons`\
  Admitted. [Explanation: HA-3.4](#ha-3-4); [source line 65](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Geometry/MinimalSurface/ExteriorDiskArea.lean#L65).

```{=latex}
\Needspace{6\baselineskip}
```

## M19. Theorem.lean

**File:** `Topology/ThreeManifold/Geometrization/Theorem.lean`

- `GC.Endpoint.geometrization`\
  Written proof; admitted dependence. [Explanation: F9](#f9-capstone); [source line 10](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/Geometrization/Theorem.lean#L10).

- `GC.Endpoint.geometrization_conjecture`\
  Written proof; admitted dependence. [Explanation: F9](#f9-capstone); [source line 14](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/Geometrization/Theorem.lean#L14).

- `GC.Endpoint.smooth_geometrization_conjecture`\
  Written proof; admitted dependence. [Explanation: F9](#f9-capstone); [source line 16](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/Geometrization/Theorem.lean#L16).

```{=latex}
\Needspace{6\baselineskip}
```

## M20. Presentation.lean

**File:** `Topology/ThreeManifold/GraphManifold/Presentation.lean`

- `GC.GraphManifold.SurfaceModel`\
  Definition/construction. [Explanation: T1](#t1); [source line 10](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L10).

- `GC.GraphManifold.SurfaceModel.Space`\
  Definition/construction. [Explanation: T1](#t1); [source line 13](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L13).

- `GC.GraphManifold.SurfaceModel.model`\
  Definition/construction. [Explanation: T1](#t1); [source line 22](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L22).

- `GC.GraphManifold.CompactSurface`\
  Definition/construction. [Explanation: T1](#t1); [source line 28](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L28).

- `GC.GraphManifold.CircleFibration`\
  Definition/construction. [Explanation: T1](#t1); [source line 43](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L43).

- `GC.GraphManifold.BoundaryTori`\
  Definition/construction. [Explanation: T2](#t2); [source line 55](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L55).

- `GC.GraphManifold.BoundaryTori.torusMap`\
  Definition/construction. [Explanation: T2](#t2); [source line 64](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L64).

- `GC.GraphManifold.BoundaryTori.image`\
  Definition/construction. [Explanation: T2](#t2); [source line 67](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L67).

- `GC.GraphManifold.BoundaryTori.zero_mem_source`\
  Written proof; no skeleton admission. [Explanation: T2](#t2); [source line 70](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L70).

- `GC.GraphManifold.BoundaryTori.torusMap_smooth`\
  Written proof; no skeleton admission. [Explanation: T2](#t2); [source line 77](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L77).

- `GC.GraphManifold.BoundaryTori.boundaryMap`\
  Definition/construction. [Explanation: T2](#t2); [source line 82](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L82).

- `GC.GraphManifold.BoundaryTori.torusMap_isEmbedding`\
  Written proof; no skeleton admission. [Explanation: T2](#t2); [source line 86](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L86).

- `GC.GraphManifold.BoundaryTori.incompressible`\
  Definition/construction. [Explanation: T2](#t2); [source line 93](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L93).

- `GC.GraphManifold.TorusPairing`\
  Definition/construction. [Explanation: T3](#t3); [source line 98](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L98).

- `GC.GraphManifold.TorusPairing.QuotientSpace`\
  Definition/construction. [Explanation: T3](#t3); [source line 118](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L118).

- `GC.GraphManifold.TorusPairing.quotientMap`\
  Definition/construction. [Explanation: T3](#t3); [source line 124](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L124).

- `GC.GraphManifold.RawGraphPresentation`\
  Definition/construction. [Explanation: T4](#t4); [source line 129](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean#L129).

```{=latex}
\Needspace{6\baselineskip}
```

## M21. Refinement.lean

**File:** `Topology/ThreeManifold/GraphManifold/Refinement.lean`

- `GC.GraphManifold.isHyperbolicInteriorGeometry`\
  Definition/construction. [Explanation: T9](#t9); [source line 11](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean#L11).

- `GC.GraphManifold.HyperbolicOrGraph`\
  Definition/construction. [Explanation: T9](#t9); [source line 17](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean#L17).

- `GC.GraphManifold.exists_prime_decomposition_of_rawGraphPresentation`\
  Admitted. [Explanation: T6](#t6); [source line 23](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean#L23).

- `GC.GraphManifold.exists_geometric_decomposition_of_prime_rawGraphPresentation`\
  Admitted. [Explanation: T7](#t7); [source line 31](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean#L31).

- `GC.GraphManifold.geometrizes_of_rawGraphPresentation`\
  Written proof; admitted dependence. [Explanation: T8](#t8); [source line 37](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean#L37).

- `GC.GraphManifold.exists_prime_geometric_decomposition_of_hyperbolicOrGraph`\
  Admitted. [Explanation: T9](#t9); [source line 46](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean#L46).

- `GC.GraphManifold.geometrizes_of_hyperbolicOrGraph`\
  Written proof; admitted dependence. [Explanation: T10](#t10); [source line 54](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean#L54).

```{=latex}
\Needspace{6\baselineskip}
```

## M22. Decomposition.lean

**File:** `Topology/ThreeManifold/TorusCut/Decomposition.lean`

- `GC.GraphManifold.componentCarrier`\
  Definition/construction. [Explanation: T5](#t5); [source line 10](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/TorusCut/Decomposition.lean#L10).

- `GC.GraphManifold.TorusDecomposition`\
  Definition/construction. [Explanation: T5](#t5); [source line 17](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/TorusCut/Decomposition.lean#L17).

- `GC.GraphManifold.TorusDecomposition.component`\
  Definition/construction. [Explanation: T5](#t5); [source line 30](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/TorusCut/Decomposition.lean#L30).

- `GC.GraphManifold.TorusDecomposition.toGeometricDecomposition`\
  Definition/construction. [Explanation: T5](#t5); [source line 34](https://github.com/qinz1yang/differential-geometry-dev/blob/ea0fae60ee01ef8c8d9b57a51794c6538f679c5d/DifferentialGeometry/Topology/ThreeManifold/TorusCut/Decomposition.lean#L34).
