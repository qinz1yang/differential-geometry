# B3e — cone accuracy fixed before the constants (2026-09-26)

File `Surgery/Topology/BoundedCurvatureAtDistanceConstants.lean` (324 lines, no sorry, not
registered; imports `BoundedCurvatureAtDistance` and `BoundedCurvatureAtDistanceBoundedThreshold`).

- `def coneAccuracy : ℝ := min (neckModelTolerance (1/4000000/26000)) (1/4000000/26000/64) / (13000*13000)`
- `coneAccuracy_pos : 0 < coneAccuracy`
- `RetainedCoreHistory.exists_scalar_bound_at_distance_of_final_slab_window_of_le_coneAccuracy
   {ε} (hεle : ε ≤ coneAccuracy) (κ C1 C2) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0) {phi} (hphi) :
   ∀ A > 0, ∃ Q Λ, 1 ≤ Q ∧ 1 ≤ Λ ∧ ∀ P₀ H hend t S hS y q ρ, …` (body identical to
  `exists_scalar_bound_at_distance_of_final_slab_window` after the existential).
- `RetainedCoreHistory.exists_scalar_bound_at_distance_of_bounded_threshold_of_le_coneAccuracy
   {ε} (hεle : ε ≤ coneAccuracy) (κ C1 C2) (hκ) (Ctime Cgrad) {phi} (hphi) :
   ∀ A > 0, ∀ Cq, ∃ Q Λ, 1 ≤ Q ∧ 1 ≤ Λ ∧ ∀ … (as `…_of_bounded_threshold`)`.
Both re-proved (the old proofs pick exactly this constant independently of κ C1 C2 Ctime Cgrad
phi; the old ∃-statements cannot be instantiated, so the proofs were copied with the constant
exposed; the private path helper is copied too). Names: descriptive `_of_le_coneAccuracy`
instead of the requested primes (NAMING §5 disallows primes for restatements).
Compile: `LEAN_NUM_THREADS=2 lake env lean -Dweak.linter.mathlibStandardSet=true <file>`: no
output. Scratch: axioms [propext, Classical.choice, Quot.sound] for all three; `#lint` reports
only docBlame on `coneAccuracy` (docBlame is excluded by AGENTS.md).
Lead: the old ∃εcone headlines are now corollaries (could be re-derived in one line each).
