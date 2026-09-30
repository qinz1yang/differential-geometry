# Geometrization skeleton: a mathematical reading for Bennett Chow and Peng Lu

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
