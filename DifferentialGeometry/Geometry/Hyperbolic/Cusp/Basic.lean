import DifferentialGeometry.Geometry.Hyperbolic.Cusp

/-!
# S-MIRRORS shim for `Cusp/Basic` (not a copy of the IMS03 file)

IMS03 split the monolith `Cusp` into an aggregator plus a `Basic` file.
Here the monolith (module below) still exists and already contains every
declaration of IMS03's `Basic`, so this shim only re-exports it.  Modules copied
verbatim from IMS03 that import `Cusp.Basic` then compile unchanged,
without duplicate declarations.  No declaration and no `set_option` here.

Monolith module: `DifferentialGeometry.Geometry.Hyperbolic.Cusp`.
-/
