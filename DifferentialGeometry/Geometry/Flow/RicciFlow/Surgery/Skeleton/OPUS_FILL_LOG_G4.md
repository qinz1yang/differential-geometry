# G4 fill log (interval index comparison)

- 2026-09-26: built on `lRegularizedIndex` (`Perelman/LGeometry/Index/Regularized.lean:115`,
  integrand `:31`), `IsLRegularizedJacobi` (`Jacobi/Regularized.lean:788`), bilinearity in
  `Index/Algebra.lean` (`lRegularizedIndex_add_smul_self` :459), boundary formula
  `lRegularizedIndex_eq_half_boundary_of_isLRegularizedJacobi` (Regularized.lean, pre-existing).
- New file `Perelman/LGeometry/Index/JacobiMinimality.lean` (200 lines, one private helper):
  `lRegularizedIndex_self_eq_add_boundary_add_sub_of_isLRegularizedJacobi` (free ends,
  boundary term `<∇J, V-J>|_a^b`), `lRegularizedIndex_self_eq_add_sub_of_isLRegularizedJacobi`
  (matched ends: I(V,V) = I(J,J) + I(V-J,V-J)), `lRegularizedIndex_le_of_isLRegularizedJacobi`.
- Admissible class: chart-differentiable on `uIcc a b` + integrable `I(W,W)` integrand. Tree's
  `lRegularizedIndex_nonneg` gives only C^8 fields; consumers holding only C^8 nonnegativity use
  the matched-ends identity directly.
- `lake env lean`: clean (0 errors/warnings). Axioms: propext, Classical.choice, Quot.sound.
  `#lint` (scratch copy): 0 findings. Not registered in DifferentialGeometry.lean (lead).
