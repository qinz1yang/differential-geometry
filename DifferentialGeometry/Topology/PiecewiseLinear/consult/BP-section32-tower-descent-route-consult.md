# BP — route consult for the Section 32 canonical tower and descent (for the owner's Codex)

Written by the lead on 2026-09-23. Codex may read the checkout directly and compile probes on its
own lease; the answer goes to `consult/BP-section32-tower-descent-codex-answer.md` (new file; no git
writes; no frozen statement edited). Use the six checks of `consult/REVIEW-TEMPLATE.md`,
concentrating on checks 4 and 6, and end with a reduction of each leaf into named sub-leaves
marked SMALL / MEDIUM / NEW_THEORY with the tree modules each would use. About 2000 words plus Lean.

Objects, in `Skeleton/Section32PseudoCell.lean` (read its module docstring first; Moise §32,
pages 224–229; the §31 canonical configuration is `Skeleton/Section31CanonicalConfiguration.lean`
with `moise311 (h307 : Moise307)`, and the nested-torus producer `moise308Nested` is unconditional):

1. `exists_canonicalTower` (line 236): from an `IsTube` (`ht : IsTube K N C D Dbd h N'`), a vertex
   `u`, an incident edge and the tube's splitting disk, a canonical tower `IsCanonicalTower` — a
   bi-infinite compatible family of revolved torus chains (`IsRevolvedTorusChain`) inside `W ∩ Zᶜ`
   with two exact tail closures (at the centre and at the rim), local finiteness away from the
   centre, and nested fitted PL solid tori in adjacent general position on every integer window.
   Codex's probe `Skeleton/CanonicalTowerReduction.lean` (with `Skeleton/CanonicalTowerReduction.md`;
   lead recheck 2 sorry, 0 errors) reduces it to two sub-leaves:
   `exists_splitDisk_cylinder_coordinates` (line 72; PARTIAL: `SplitDiskCenter` and
   `TubeCenteredPrismCoordinates` give the centred split disk extended to a PL prism over both dual
   balls; what is left is the round-cylinder-to-prism model map identifying the middle disk, rim
   and centre, then the composite through the tube embedding `h`) and
   `exists_controlled_revolved_tower` (line 81; the substantial producer: the joint radial
   exhaustion with the two tail closures, `W` containment, `Z` avoidance and local finiteness).
   Questions: (a) for the cylinder coordinates, the exact model map (`Skeleton/CanonicalTowerReduction.cylinder`
   vs the triangular prism) and whether `stdCenter 1` must be re-marked; (b) for the revolved
   tower, a construction: which canonical configurations (`moise311`/`Moise307`, or the nested tori
   of `moise308Nested`) supply each window, how the radial parameter is chosen so the tails close
   exactly at the centre and the rim, and where local finiteness comes from; is `Moise307`
   really needed per window (the log says `ControlledRevolvedTower.exists_canonicalTower` is a
   conditional consumer of `Moise307`), and if so is it available unconditionally in the tree
   (grep `Moise307`, `moise307`, `Section30Torus`, `Section30Separation`).
2. `exists_descentSequence` (line 250): the surgery stage on a compact set iterated along the
   tower — one canonical configuration from 30.7 inside `W ∩ Zᶜ` per step, one surgery stage per
   compact set — whose iteration gives the leaf. Question: the per-step producers (state them as
   sub-leaves), the induction measure, and which of the three neighbouring leaves
   (`isOpenTopologicalCell_annularChain` line 277, `exists_generalPosition_ball_pseudoCell` 296,
   `exists_reducedDisk_of_crossesPseudoCell` 303; their probes `Skeleton/Section32*Probe.lean` are
   assigned to a collaborator — do not prove those) the descent consumes and how.

Also check: the Q6 note in `Skeleton/FILL_LOG.md` ("Codex overnight remaining gates") says the finite
three-cell standard configuration of the §31 skeleton does not supply a bi-infinite tower; confirm
or refute, and say whether a genuine `IsCanonicalTower` inhabitant (a fixture) can be built from
`exists_isTube` and the standard configuration once `exists_controlled_revolved_tower` is proved.
What is the single most likely surprise? Verdicts are evidence, not rulings; the lead verifies
against Lean.
