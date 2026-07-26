# BishopBall.lean

## 2026-07-18 local normal-ball comparison

The center-metric polar integration stage is complete and sorry-free.
`exists_framed_ratio` supplies one common source radius and the radial
parametrized-density ratio in every framed unit direction.  The private radial
lintegral bridge converts `volumeIoiPow` to the ordinary weighted interval
integral, and a localized cumulative-ratio lemma permits comparison at every
pair of radii strictly inside the common source.

The public outputs are:

- `hypRadVol` and its positivity theorem `hypRadVol_pos`;
- `normalBallVolume`, the Riemannian volume of the framed exponential image of
  the center-metric tangent ball;
- `normalBall_cross`, the cross-multiplied local Bishop inequality; and
- `normalBall_ratio`, the corresponding ENNReal quotient antitonicity.

Focused verification passed without warnings.  No cut-time or measurable
direction choice is used.

`normalBall_ratio` is complete (100%).  The next theorem `localBall_ratio`
remains 0% until the framed normal image is identified with the intrinsic
metric ball on the chosen radius.  Dedicated Route B machinery is now about
68--72%; the full V1--V3 volume-comparison/CGT theorem program is about
44--48%.  Global Bishop--Gromov and the unconditional HCG compactness endpoint
remain 0%.
