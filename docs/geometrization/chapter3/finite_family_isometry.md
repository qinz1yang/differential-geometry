# AC59: one subsequence for a finite family of isometric limits

One theorem starts with actual maps g(n,j):D->Y, where D and Y are proper metric
spaces and j ranges over any finite type. All maps send a fixed p to a fixed q.
On each fixed D-ball, their distance distortion is eventually bounded by a
single epsilon(n) tending to zero, uniformly over j. No continuity of the maps,
coverage of the target, or global distortion bound is assumed.

The theorem constructs a family F(j):D->Y of actual isometries with F(j)(p)=q and
ONE strictly increasing subsequence phi. Along that same phi, the actual maps
converge to F uniformly over every fixed ball and every member j. This is an
embedding theorem: target surjectivity is neither assumed nor concluded. In the
line application D=R; the properness of the varying original source spaces is
not involved in this parameter-domain hypothesis.

The proof uses one ultrafilter refining atTop. Each image parameter lies eventually
in a compact target ball, giving simultaneous pointwise limits along that filter.
The actual vanishing distortion proves exact distances. Finite nets in the
parameter balls and finite intersection over j give uniform filter convergence.
A recursive choice from the same filter then yields an ordinary strictly increasing
subsequence on integer balls with reciprocal accuracies. Thus no independent
per-member subsequences or unrelated ball limits are substituted for one family.

Source body checked: blueprint207A AC59 full5089-5139, specifically the one-line,
finite-family and uniform-on-bounded-parameters requirements. BBI2.5.14 printed47-48,
PDF62-63 and its proof were reread through the retained targeted extraction;
July6,2024 errata PDF1-3 were freshly checked with the preceding AC58 milestone.
Our explicit ultrafilter/finite-net proof replaces the source's rational diagonal
argument and does not assume map continuity. Existing controlled_isometry proof
checks are reused for that proof pattern, without its coverage/surjectivity part.
The actual pinned compact ultrafilter criterion, finite filter intersection and
accepted compact finite-net theorem bodies were read. No current-remote errata
clearance is claimed.

This closes AC59's general finite-family extraction mechanism once the actual
prefix images have the required local distance bounds. The source-prefix maps,
proof of those bounds from absolute excess, and original-input application to
the SAME prescribed pointed target remain to be connected. AC59 is not yet
claimed in full. Earlier mathematical leaves, blueprint207 and migration
interfaces are unchanged.
