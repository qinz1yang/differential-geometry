# BO — route consult for the first four CGN leaves (for the owner's Codex)

Written by the lead on 2026-09-23. Codex may read the checkout `D:\differential-geometry-moise-int`
directly and may compile probes on its own lease; the answer goes to
`consult/BO-cgn-first-four-leaves-codex-answer.md` (new file; no git writes; no frozen statement
edited). Use the six checks of `consult/REVIEW-TEMPLATE.md` but concentrate on checks 4 and 6
(dischargeability and the proof route), and end with a reduction of each leaf into named
sub-leaves, each marked SMALL / MEDIUM / NEW_THEORY with the tree modules it would use. Chinese or
English, about 2000 words plus Lean statements; a probe file per leaf (sorry only at the named
sub-leaves, compiled with only those warnings) is welcome but not required.

Objects, all in `Skeleton/ControlledGraphNeighborhood.lean` (the controlled 35.1; read its module
docstring first, especially the paragraphs at lines 136–200 on these four leaves and the assembly
`section34ControlledGraphNeighborhood` from line 590; the frame vocabulary is `Section34Frame.lean`:
`Section34CutFrame` 656, `Section34CutStep` 594, `Section34VertexPreparation` 926,
`Section34PiercingConditions` 1011; the reviews are digested in
`consult/AC-controlled351-seventh-review-digest.md` and `consult/AE-controlled351-eighth-review-digest.md`;
the previous worker's notes are `Skeleton/OPUS_FILL_LOG_D.md` lines 399–470):

1. `exists_section34CutFrame` (line 273, steps 1–5 of page 244, frozen): the joint construction of
   the cut — vertex balls around the vertices of a subdivision `𝒦'` of the locally finite piece,
   splitting disks, tetraBalls, faceDisks, patches, face arcs, edge arcs, marked points — with the
   24 clauses of `Section34CutFrame` and the outer torus data. Question: which existing producers
   supply which clauses (grep `TubeOfGraphDualCells`, `exists_isTube`, `Section33TubeFrame`,
   `PolyhedralTubeNeighborhoodExists`, `HandleDecompositionTubeFixture`, `DualCellDecomposition`,
   `derivedNeighborhood`, `SplitDiskCenter`, `TubeCenteredPrismCoordinates`,
   `Section34CompactSplitDiskIntersection`), and what is genuinely new (the regular-neighbourhood
   clause `hN`, local finiteness in the manifold, the closure formulas of face disks and
   tetraBalls, the two-sidedness the source-face order needs, cf. digest BM).
2. `exists_section34VertexPreparation` (line 303, FIX of reviews Z/AC, unreviewed as a proof
   route): per vertex the pierced/enlarged PL 3-cells `Cp`, cores `Cc`, `Kcore`, per edge the nested
   solid tori `Sn`, `Tn`, the annuli `Aa`, `Ab₀`, `Ab₁`, `Bb`, `Bb₀`, `Bb₁`, `Bc`, `Bc₀`, `Bc₁` with
   marked end circles, the tolerances `ε` with the one-sided and sum-distance clauses, the stability
   clause 999 and the overlap isolation (`section34CellThickening`). Question: a construction order
   that satisfies all 85 lines of the predicate at once (which clauses force which choices; where
   compactness gives a common `ε`), and which existing modules supply the tori and annuli
   (`InnerSolidTorusToroidalShell`, `IsTopologicalSolidTorus.exists_toroidalShell_of_isCompact_subset_interior`,
   `Section28Annuli`, `PrismLateralCircleSides`, `LateralAnnulusLevels`).
3. `exists_section34PiercingPackage` (line 371, changed after W/Z/AC): from `Moise341` (the
   approximation `Moise341.exists_section34VertexApproximation`, proved at line 322, gives `G w`
   `ε`-close to `h` on `Cc w`) produce `Sp`, `Tp`, `cnt`, `Pg`, `G'` with the 22 clauses of
   `Section34PiercingConditions` AND `∀ w, ∀ x ∈ Cc w, dist (G' w x) (h x) < ε w`. Question: how
   the piercing tori/annuli are placed in general position with the crossing charts (clause 1050),
   how `cnt`/`Pg` count the crossing polygons, and which clauses are consequences of the
   preparation rather than new choices.
4. `exists_section34ProtectedCircleRemovalStep` (line 389, frozen; the page 249–250 surgery): one
   modification that lowers `cnt e` by one while keeping all 22 piercing clauses, the closeness
   off the `Sp` interiors, and the marker agreement (its conclusion at lines 320–330). The full
   removal `exists_section34ProtectedCircleRemoval` is already proved from this step by descent
   (`Section34CircleRemovalDescent`); the deleted balls after removal are real
   (`Section34DeletedBalls`, with the single-cap lemma `IsPLCellOn.sdiff_interior_of_frontier_inter`).
   Question: the surgery in the tree's vocabulary — an innermost crossing polygon on the annulus
   `Aa e`, the disk it bounds in `Bb e`, the push of `G (ends e).1` across it — and which of the
   22 clauses each sub-step touches (list them by clause number), plus what happens to the
   closeness bound (the removal's conclusion does not return `dist (G' w x) (h x) < ε w`; say
   whether it could, cf. request BN).

For the file as a whole: is any obligation missing between these four leaves and the deleted
balls / edge matching that consume their outputs (check the assembly's `obtain` patterns for
dropped conjuncts, as happened with the closeness bound in BN)? What is the single most likely
surprise? External or Codex verdicts are evidence, not rulings; the lead verifies against Lean.
