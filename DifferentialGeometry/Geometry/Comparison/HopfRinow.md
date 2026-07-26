# HopfRinow.lean notes

## 2026-07-23 connectedness boundary audit

Removed the file-wide `ConnectedSpace M` assumption from the complete-geodesic
producer.  Explicit connectedness remains on exactly the two global theorems
which assert a realizing path or minimizing geodesic for every pair of points;
those statements are false across different connected components.  Focused and
exact verification passed, with the file's three pre-existing intentional
frontiers unchanged.

Accounting: the complete-geodesic no-connected migration is complete (100%);
the independent global minimizer proof frontiers remain incomplete.
