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
