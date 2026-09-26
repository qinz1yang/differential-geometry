# OPUS fill log: T1 of DESIGN_B13 (terminal cap-side obstruction), 2026-09-26

## Delivery
- File: `Surgery/Topology/TerminalCapSideExclusion.lean` (new, 155 lines, uncommitted, not wired).
- Import: `Surgery/Topology/HornSeparationFrontierScalar` only (committed, shared olean).
- Compile: `lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`, LEAN_NUM_THREADS=2: zero output (no errors, warnings, lints).
- Axioms of `TerminalCorePresentation.false_of_terminal_capSide`: `[propext, Classical.choice, Quot.sound]`. Probe was a scratch copy outside the repo, deleted.
- `git diff --check` clean for the new file.

## Declarations (namespace `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation`)
- `positiveHornMap_injective`: `Function.Injective (P.positiveHornMap c e)`. New public name, grep-unique. It was inlined as `hinj` inside the private `horn_sides_of_complementPair` (`HornCentralSphereSeparation.lean:350`). Deferred merge: that proof could call this lemma.
- `false_of_frontier_eq_image_complementPair_sphere` (T1c): horn `e`, `p : ComplementPair S` in `positiveHornDomain` with `S` nonempty, the `hlo`/`hhi` end clauses, `W` open with `frontier W = positiveHornMap '' S`, `ℓ < cQ` and `cQ ≤ R ≤ U` on `closure W` ⇒ `False`. Proof: `W` is clopen in `Σᶜ`. The right side `V` is connected, so `V ⊆ W` or `V ∩ closure W = ∅`. In the first case `horn_scalar_diverges` breaks `R ≤ U`. In the second case, a point of `W` near the neck centre lies in the left image, so the left image is `⊆ W`. Then `horn(y, 0) ∈ closure W` (continuity of `horn` at `u = 0⁺`), and `horn_base_scalar` gives `R ≤ ℓ < cQ`.
- `false_of_terminal_capSide` (T1): the §2 statement VERBATIM. It was first elaborated with a `sorry` body; the only diagnostic was `declaration uses sorry`. `eta := min eta_sep (1/8646)`, where `eta_sep` comes from `exists_horn_neck_end_separation_tolerance`. The neck centre is `N.chart (mark, 0) ∈ frontier W ⊆ closure W`, so `cQ ≤ N.scale`, and then `2·R(frontier core) ≤ 2ℓ < cQ` gives the `(1 − 4323δ)` margin. The proof then applies `exists_neck_coordinates_in_horn_of_frontier_scalar_lt`, then the separation tolerance, then rewrites the central sphere into `positiveHornMap '' S`, then T1c.

## Deviations
- None in the statement.
- Unused by the proof: `IsConnected W` (it is a binder inside the `∃ … ∀` body, so the linter does not flag it). Only `IsOpen W` and the frontier equation are used.
- The hypotheses `hbd.2` (`R ≤ U`) are used only on the tip side. This matches §0 F3: T2's `IsCompact (closure W)` with `Cup·Qs` supplies `U := Cup·Qs` directly.
- T1a (`withEps`) and T1b are not needed. The centre-in-horn fact is a hypothesis of T1 as frozen (`N.center ∈ P.hornHalfRange c e`), so T4 must still supply it (design brick T1b), together with `P.withEps` if T4 needs the presentation's `ε ≤ eta`.
- Consumer check (T2 → T1): T2 outputs `SpatialNeck L.metric eps w` with `frontier W = range (y ↦ nk.map (y, 0))`. It needs `SpatialNeck.exists_normalizedNeck_of_two_mul_le` (chart = nk.map) to rewrite this into `N.chart '' {z.2 = 0}`, plus `2·ℓ < c·Qs` (F4) and `U := Cup·Qs`. These are T4 bookkeeping, not T1 changes.

## Deferred merges
- `HornCentralSphereSeparation.lean:350` (private `horn_sides_of_complementPair`): its inline injectivity could use `positiveHornMap_injective`. Committed file, not touched.
- Root aggregate `DifferentialGeometry.lean`: the new module is not registered (worker rule). The acceptance lane registers it.
