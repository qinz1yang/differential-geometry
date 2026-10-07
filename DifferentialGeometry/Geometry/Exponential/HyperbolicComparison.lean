import DifferentialGeometry.Geometry.Exponential.HyperbolicComparisonPortHGI

/-!
Shim (S-HG-INTAKE, suffix `_HGI`): the donor file `Geometry/Exponential/HyperbolicComparison.lean`
needs the generalised Cartan norm comparison (`Cartan/NormGeneralHGI`), which the tracked
`Cartan/Norm.lean` does not have; the verbatim donor text (plus that one `import` line) lives in
`HyperbolicComparisonPortHGI.lean`.  Delete this shim and the port when INT upgrades
`Cartan/Norm.lean` to the donor version.
-/
