# Section 34 source face order: review digest (answer to request BL)

Owner supplied the review on 2026-09-23 (request BL, mirror commit `51271364e4f`). The reviewer
read the full `Section34CompactCutFrame` (27 clauses) and the non-compact `Section34CutFrame`; no
Lean was compiled. Marks: **[V]** checked against the Lean source by the lead; **[P]** the
reviewer's paper argument; **[OPEN]** proof obligation.

## Verdicts

| Leaf | Review | Lead disposition |
|---|---|---|
| `compactSourceFace_iff_cutLe` | OK; the "short proof" label was wrong, the statement is not | Stays frozen; no frame clause added; proof route below; Codex reconnaissance first |
| `section34SourceFace_iff_cutLe` (non-compact twin) | OK, same argument; local finiteness keeps each cell's check finite | Stays frozen; Q's SUSPECT withdrawn (see [V] below) |

## Corrections to our records, verified

**[V] `IsPLCellOn` has an API now.** `PLCellOnBoundary.lean` provides `IsPLCellOn.dim_eq` (a set
is not a PL `d`-cell and a PL `d'`-cell for `d ≠ d'`), `IsPLCellOn.boundary_eq` (uniqueness of the
intrinsic boundary), `IsPLCellOn.boundary_eq_frontier` (codimension zero, `d = 3`) and
`IsPLCellOn.sdiff_boundary_eq_interior`. The gap named in `consult/Q-section34-terminal-due-diligence.md`
§4 is closed for these three items.

**[V] The non-compact frame has the tetrahedron clauses.** `Section34Frame.lean` lines 693–695:
`Section34Incident s t → src (.faceDisk s) ⊆ src (.tetraBall t)` and `∀ s, ∃ t, Section34Incident s t`.
Q's "silently needed" clause is a field.

## Why BL's degenerate position is not a counterexample

**[V] The intersection-formula step.** For an interior triangle `σ` with a boundary edge `e`, the
marked point `P = D_e ∩ D_σ` (clause `src (.markedPoint p) = src (.splitDisk) ∩ src (.faceDisk)`)
lies in `D_σ ⊆ Q_t` for each of the two tetrahedra `t` on `σ` (clause 342 of the compact frame),
hence `P ⊆ Q_t ∩ D_e = I_te` (clause 312); `I_te` is a proper set-face of `D_e` of lower dimension
(clause 10 with `dim_eq`), so `I_te ⊆ srcBd D_e` by clause 8. The two edge arcs `I_{t₋e}`, `I_{t₊e}`
are distinct cells.

**[P] Thinness.** Clauses 7–10 make the closed cells a regular cell complex, whose face poset is
thin: between two faces two dimensions apart there are exactly two intermediate faces (on the
circle `srcBd D_e` a vertex meets exactly two arcs; on the sphere `srcBd V_w` an edge meets
exactly two faces). Were `P ⊆ o_e` as well, the interval `[P, D_e]` would have three intermediate
one-cells. So "the marked point lies on the original edge" cannot coexist with the full cell
conditions; no "one point in `∂C` hence the whole triangle" inference is used. (The reviewer cites
the standard theory of regular cell complexes; not verified further by the lead.)

## Proof route (five steps, the reviewer's)

1. **End points first.** Restrict the subdivision to the boundary circle of a coarse triangle: each
   `(σ, w)` has exactly two end edges, each `(t, e)` exactly two triangle faces containing `e`; the
   intersection formulas give two distinct marked points of every `faceArc` / `edgeArc`, which
   exhaust its intrinsic boundary.
2. **Exclude foreign vertices and split disks.** The two-ball intersection formula and clause 26
   give disjointness of different `D_e`; with `Section34CompactSplitDiskIntersection` this fixes
   the vertex of every patch and face arc and excludes a face disk inside a vertex ball.
3. **Identify the outer adjacencies.** If `A_{σw} ⊆ Q_t` then its end point `P_{σe} ⊆ I_te` forces
   `σ < t` by step 1; an interior face arc already has two patches and cannot also border an outer
   face; a boundary face arc has one patch, and thinness forces the other side to be `O_w`.
   Likewise a boundary marked point's second arc is `o_e`; an outer arc has points outside `C`,
   so after excluding patches its other side is its end point's outer face.
4. **Classify the codimension-one containments.** Compact version: `D_σ ⊆ Q_t` with
   `Q_t ⊆ conv t` and the dimension test on simplex intersections. Non-compact version: `tetraBall`
   has only carrier support, so the third tetraBall must be excluded by local two-sidedness in
   dimension three, not by `Q_t ⊆ conv t`.
5. **Generate the order.** Each cell's sphere boundary is a pure-dimensional tiling, so any proper
   containment refines into a chain rising one dimension at a time; step 4 identifies each step
   as a `CutStep`, whence `CutLe`.

The expensive part is the uniform derivation of subdivision restriction, pure-dimensionality of
the sphere boundaries and two-sidedness, not any new position clause. The non-compact version
uses local finiteness to get a finite face family inside each compact cell; no global finiteness.

## Clause proposals: mandatory set empty; optional certificate not adopted

The reviewer's optional certificate, one predicate for both versions:

```lean
def Section34FacetTiling {Λ X : Type*}
    (step : Λ → Λ → Prop)
    (src srcBd : Λ → Set X) : Prop :=
  ∀ l, srcBd l = ⋃ m, ⋃ (_ : step m l), src m
```

with `Section34FacetTiling Section34CompactCutStep src srcBd` and
`Section34FacetTiling Section34CutStep src srcBd`. With it the bridge is short (pick a point of
`src m \ srcBd m`, choose the next face by the boundary tiling, then the common-face formula and
induction on dimension). **Lead decision:** not adopted now. Adding it to the frame moves the
obligation into the open producer `exists_compactCutAndGraph` (and, non-compact, into
`exists_section34CutFrame`), it does not remove it; the consumers would only gain a hypothesis
(conjunction splits and call sites would need mechanical edits). Revisit if the derivation stalls.
No relative-interior clause and no graph-edge-coverage clause is needed.

## Obligations and warnings

- **[OPEN]** Reusable lemmas, not statement changes: pure-dimensionality of the sphere boundary of
  a cell of a regular cell complex given by clauses 7–10; thinness; the codimension-one containment
  classification for the ten (compact) / eight (non-compact) label kinds; for the non-compact
  version, local two-sidedness of a `tetraBall`. Assigned as Codex reconnaissance (day queue item
  1b): a probe reducing `compactSourceFace_iff_cutLe` to these named lemmas, then the elementary ones.
- Non-degenerate model (reviewer, unverified): the standard tube cut of a single tetrahedron; on
  `∂Δ⁴` for the non-compact version. Source-side only; the joint witness of the compact chain is
  still UNTESTED in the ledger.
- Most likely surprise (reviewer): the non-compact `tetraBall` has only carrier support, so the
  compact simplex-position proof cannot be copied; local two-sidedness must be used there.
