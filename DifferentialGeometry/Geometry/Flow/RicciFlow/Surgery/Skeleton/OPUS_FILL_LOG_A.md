# Lane A log: lemma (A), axial minimizing arms in a neck region

- 2026-09-25: `Surgery/Topology/NeckRegionAxialArms.lean`. Only the single neck at x is needed when eps depends on D (`9 * D < eps⁻¹`), so the neck-ball hypothesis is not taken. Heights ±3D/2 in the neck chart; two-sided distance bounds from `crossModel_edist_transfer` + cylinder axial/height distances; arms by Hopf–Rinow on the component of x.
- Angle bound: `arccos ((3 eps - 1) / (1 + eps))` (tends to π; ≥ π/2 for eps ≤ 1/3).
- Combined with `exists_strongNeck_threshold_of_minimizing_arms`: `exists_strongNeck_threshold_of_spatialNeck` (spatial eps-neck, eps = (9D+11)⁻¹ ⇒ strong delta-neck).
- Compile: clean (HornNeckImprovement olean built into an E: scratch hardlink mirror, since removed). Axioms of all 4 public theorems: propext, Classical.choice, Quot.sound. `#lint` 0 errors. Not wired, not lake-built.
