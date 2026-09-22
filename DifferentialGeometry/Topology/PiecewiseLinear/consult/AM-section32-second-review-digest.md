# Digest — second external review of `Skeleton/Section32PseudoCell.lean` (snapshot `c1d5ba63`)

**All five repaired leaves and the corrected `Moise267` OK — frozen.** The added hypotheses have
suppliers in the assembly; no new endpoint hypothesis.

| Item | Verdict | Reason |
|---|---|---|
| `separates_initialSurface` | OK | `havoid` follows from the tower's avoidance of `Bu ∪ Bv` and is passed |
| `exists_descentSequence` | OK | receives `havoid`; the corrected `Moise267` gets its non-empty common boundary from the two seam circles of Type 2; no new gap in the four-step package |
| `isOpenTopologicalCell_annularChain` | OK | the genuine tube gives a compact carrier, true boundary circles and two ends distinct from the centre; `hsepU` comes from the descent output and the limit leaf first — no circularity |
| `exists_generalPosition_ball_pseudoCell` | OK | `Dc ⊆ Metric.ball P δ` is chosen jointly with the small ball and general position; it is p. 229's pre-chosen controlled cell; no PL at the centre |
| `exists_reducedDisk_of_crossesPseudoCell` | OK | `Bl ⊆ Ω`, `Dc ⊆ Ω`, `IsOpen Ω` give the common support domain; `Δ ⊆ Ω` matches the book; `Ω` need not be simply connected |
| `Moise267` | OK | non-empty common boundary fills the implicit premise of p. 195 (the proof starts from a boundary edge); **do not** also require the common boundary connected — that would exclude Type 2's two-circle model |

Book checks: p. 227 obtains the closure equality after the separation property; p. 229's
replacement disk is controlled by the previously chosen cell, not confined to the original `Bl`.
**Owed:** unconditional proofs of the three named inputs (`Moise303`, `Moise286`, `Moise267`); a Lean
inhabitant of `IsTube`. **Fixture:** a one-edge derived neighbourhood after a non-affine PL bend
with a thin torus tower; on an even torus push a half annulus inward to get a three-annulus model
whose common boundary is two circles; near the centre a small polyhedral ball crossing the
pseudo-cell (mathematical model, not a compiled inhabitant). **Likely surprise:** the descent
schedule — on each compact set away from `P'` all four surgery stages must eventually be complete;
pointwise convergence does not replace the promised local eventual equality.
