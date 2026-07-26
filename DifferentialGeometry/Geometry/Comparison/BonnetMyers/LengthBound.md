# LengthBound notes

## 2026-07-18 nonunit perpendicular trace

- Added `ricci_eq_sum_perp`, which expresses Ricci curvature along an arbitrary
  positive nonzero vector as the trace over a perpendicular orthonormal family,
  with the expected squared-speed factor.
- Focused verification and the exported module refresh passed.
- This is a proved local producer. Bishop--Gromov volume comparison remains an
  unstated and unproved endpoint (0%).

## 2026-07-24 one-dimensional Ricci lower bound

- Added `ricciLower_dim1`: when the model has real finrank one, the transverse
  family in `ricci_eq_sum_perp` is empty, so every diagonal Ricci value is zero
  and hence `RicciBoundedBelow g 0`.
- The proof adds no hypothesis and uses no curvature-radius or compactness
  input. Focused verification passed; the exported artifact refresh remains
  pending while another explicitly coordinated target owns the write window.
- This local theorem is complete. The evolving
  `scaledDist_calabiUpperSupport_of_sol` theorem remains 0%; its dedicated
  Route B-prime machinery is still incomplete, while whole HCG supporting
  machinery remains about 60%.
