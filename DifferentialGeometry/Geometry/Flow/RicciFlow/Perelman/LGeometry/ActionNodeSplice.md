# Two-piece node splices

## Goal

`lNode_c1_dense` is the shared-node competitor producer immediately below the
corner argument.  It starts from two adjacent chart `timeH1` pieces, requires
only a monotone three-node subdivision, target containment, and equality of
their inverse-chart values at the common node, and constructs the manifold
curve internally.  Repeated subdivision nodes are allowed.

## Native route

The two coordinate curves are clamped to their compact time intervals, lifted
by their respective inverse charts, and joined at the shared time.  The node
hypothesis is exactly what makes this lift continuous; no tangent or cotangent
transition object is introduced.  The existing `lAction_c1_dense` theorem then
handles cross-chart C1 gluing by endpoint-flat coordinate germs.  It supplies
global fixed-endpoint C1 curves, strong `timeH1` convergence on both pieces,
uniform manifold convergence, and convergence of the complete regularized
L-action.  The theorem now also exposes the constructed curve's two chart
containment and coordinate-representation facts.  These are the exact data
needed to identify its global action with the sum of the two chart actions;
the construction and assumptions are unchanged.

## Verification

The noncompact declaration-level generalization of `lNode_c1_dense` passed
focused verification without warnings. Its proof delegates the approximation
step to the compact-target finite-chart density producer, so no ambient
compactness hypothesis or new replacement assumption is added. The refreshed
export for `ActionNodeWindow` also passed.

Focused verification passes without warnings.  The theorem has no project
placeholders; its axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## 2026-08-24: finite joined realization

`exists_chartH1_join` is now verified without warnings.  It applies
`exists_chart_split` independently to two adjacent C1 pieces, concatenates the
two finite node families, and deliberately keeps two copies of the common node.
The resulting zero-length middle segment lets the left and right chart covers
remain independent.  The dependent `timeH1` lengths are transported with the
same local `toFun_cast` pattern already used by `ActionNodeRefine`; no new
foundational subdivision API was needed.  The theorem returns the joined curve,
the common node in the subdivision, chart containment, and the coordinate
representations for every segment.

## Project position

The final corner/momentum-matching theorem is not stated and remains 0%.
This producer closes the arbitrary finite joined-realization gate (100%).  With
the checked tent and C1-density modules, the generic node-variation machinery
is roughly 94%.  `ActionPrefix.lReg_prefix_min` and
`CutDomain.lMinDomain_down` now consume this producer, so prefix minimality and
downward closure are complete.  `CutStrict.lMinVec_unique_lt` also consumes it
to prove strict pre-cut uniqueness.  The next genuine frontier is the
nonconjugacy-before-cut theorem and the limiting cut alternative.  Dedicated
L-geometry machinery for the compact ordinary-flow route is roughly 90%,
while `redVolume_anti` remains 0% until its theorem is proved.  The generic
finite-chart density infrastructure reused here is complete for this purpose.
