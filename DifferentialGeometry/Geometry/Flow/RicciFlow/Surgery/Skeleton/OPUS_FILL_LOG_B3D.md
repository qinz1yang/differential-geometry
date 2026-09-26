# B3d — bounded-threshold version of bounded curvature at distance (2026-09-26)

File `Surgery/Topology/BoundedCurvatureAtDistanceBoundedThreshold.lean` (1060 lines, no sorry,
not registered, imports `BoundedCurvatureAtDistance` from a161fc07e). Compiles directly with
`LEAN_NUM_THREADS=2 lake env lean -Dweak.linter.mathlibStandardSet=true` (no output). On a scratch
copy: `#lint` 14 linters 0 errors; both headlines [propext, Classical.choice, Quot.sound].

## Where `q_i/Q_i → 0` was used (exactly two places) and what replaces it
1. Ray/neck step (Necks file, `exists_isometric_ray_with_spatialNecks_of_scalar_escape`): to put
   the segment points γ_n(τ) above the witness threshold. They have normalized scalar
   → R_P(g τ) > max(2, C2+1), so q ≤ Q (already an L1 hypothesis) gives q < R there.
2. Second level (Cone file, `…_at_final_slab_end`): to put the re-based points y_n = F(x_n)
   above the threshold. Their normalized scalar q_k(n) → ∞, so again q ≤ Q suffices.
Nowhere else: the neck/cap structure is only ever used at points of normalized scalar ≥ 2 (ray)
or → ∞ (second level). So the sequence version holds with (b) replaced by the ratio bound
q_i ≤ Q_i, which L1 already assumes; (b) is simply dropped.

## Why the ratio constant is 1 in the sequence version, and Cq enters by re-basing
L1 (and its suppliers: escape radius, traced convergence) require q_i ≤ Q_i = R(base). With
q ≤ Cq·R(y), Cq > 1, the headline re-bases: on the ball B(y, A/√R(y)) with the bad point z
(R(z) > (n+K+1)R(y), K = max Cq 1) it picks x with R(x) = max(q, R(y)) ∈ [R(y), K R(y)] and
d(x, z) < A/√R(y) (intermediate value on the path-connected ball B(z, A/√R(y))). Then
q ≤ R(x), normalized distance d(x,z)√R(x) < A√K, R(z)/R(x) > (n+1)/K → ∞, the window
Λ/R(y) ≥ 1/R(x), and ρ√R(x) ≥ ρ√R(y) ≥ Λ ≥ 1. No configuration obstruction.

## Statements
- `RetainedCoreHistory.exists_normalized_scalar_bound_of_bounded_threshold`: the B3c positive
  form with (b) removed (L1 hyps incl. q_i ≤ Q_i, Q_i → ∞, final-slice witnesses, small ε).
- `RetainedCoreHistory.exists_scalar_bound_at_distance_of_bounded_threshold` (κ C1 C2) (hκ)
  (Ctime Cgrad) (hphi): ∃ εcone > 0, ∀ ε ≤ εcone, ∀ A > 0, ∀ Cq, ∃ Q Λ ≥ 1, ∀ P₀ H hend t S hS y q ρ,
  0 < q → q ≤ Cq·R(y,t) → Λ ≤ R(y,t) → time last ≤ t − Λ/R(y,t) → final-slice witnesses above q →
  EventSlabsDerivative → S'.DerivativeBoundBefore → S'.GradientBoundBefore → EventSlabsPinched →
  PhiAlmostNonnegative → TerminalNoncollapsedBefore … κ ρ t → Λ ≤ ρ√R(y,t) →
  ∀ z ∈ B_t(y, A/√R(y,t)), R(z,t) ≤ Q·R(y,t).   (same εcone as before)
  `Λ ≤ R(y,t)` (large curvature at the base) is kept: the contradiction sequence needs
  R(y_n) → ∞ for Rm ≥ 0 on the first limit (vanishing rescaled pinching); with R(y) bounded the
  argument has no cone to exclude. Old `Λq < R` with q ≥ 1 implied it.
- helpers (new copies without the `q/Q → 0` hypothesis):
  `exists_isometric_ray_with_spatialNecks_of_bounded_threshold`,
  `RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_bounded_threshold`,
  `RetainedCoreHistory.final_slab_punctured_cone_end_exclusion_of_bounded_threshold`.

## Duplication (lead)
The four `_of_bounded_threshold` theorems are copies of committed ones minus the `hqlim`
hypothesis (strictly more general, since L1 already has q ≤ Q). Recommended: delete `hqlim`
from the committed Necks/Cone/B3c statements (same proofs with the two edits above) and drop
the copies here; the old headline then follows from the new one (Cq = 1, Λ q < R ⇒ Λ ≤ R).
