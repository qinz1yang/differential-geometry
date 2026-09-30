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
