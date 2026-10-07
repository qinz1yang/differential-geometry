import DifferentialGeometry.Geometry.Hyperbolic.TruncationGeometryPortHGI2

/-!
Shim (S-HG-INTAKE-2, suffix `_HGI2`): the donor file `Geometry/Hyperbolic/TruncationGeometry.lean`
uses `hyperbolicGeometricStructure`, whose atlas field rests on the unproved skeleton
`has_hyperbolic_atlas_of_curvature_neg_one` of the tracked `Hyperbolic/ModelAtlas.lean`.  The donor
text (one extra `import`, `hyperbolicGeometricStructure` renamed `…_HGI2`, see
`ModelAtlasProofHGI2`) lives in `TruncationGeometryPortHGI2.lean`; this file only re-exports it.
-/
