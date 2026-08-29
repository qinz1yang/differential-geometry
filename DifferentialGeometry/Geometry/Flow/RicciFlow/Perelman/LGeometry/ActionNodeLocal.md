# Two-piece node minimality

## Goal

`lNodeAct_min` transfers the relaxed minimizer's global comparison against
fixed-endpoint `C¹` curves to an exact inequality for two adjacent chart
`timeH1` pieces.  A competitor must stay in the two chart targets, preserve
the outer manifold endpoints, and have one common inverse-chart node.

## Native route

`lNode_c1_dense` constructs the continuous two-piece curve and global
fixed-endpoint `C¹` recovery sequence.  The global comparison passes to the
limit, while the chart containment and representation data exposed by
`lNode_c1_dense` identify both global actions with their two chart-action
sums.  No momentum match, transition covector, or new minimizer predicate is
assumed.

## Verification

Focused verification passes without warnings.  The file contains no project
placeholders, and the public theorem keeps only assumptions used by the exact
comparison.

## Project position

The comparison theorem is the variational input immediately below the
Weierstrass--Erdmann node calculation.  The next exact step is to apply it to
same-chart endpoint ramps, differentiate both chart actions, and evaluate the
two momentum boundary terms.  `lNode_mom_match` and
`exists_lMinimizer` remain unstated (0%); `redVolume_anti` remains 0%.
The two-piece comparison gate itself is now 100%, while dedicated node-match
machinery is roughly 94--96%.
