# Opus fill log, lease d (token `claude-agent-d-20260919`), 2026-09-22

The coordinator stopped the lane before the first compile (lease d was in use by the Gemini
batch). No Lean module, `.wip` file or scratch probe was created. There were 0 compiles, so
nothing was verified and there is no axiom audit. Every leaf is STUCK at "design only". The
routes below come from reading `Skeleton/Section32PseudoCell.lean`, `PseudoCell.lean` and the
digests AK/AM/AD. None of them has been checked in Lean.

## exists_compact_connected_to_freeFace — STUCK (not started in Lean)
- File: none. Import line: none. New public names: none. Compiles: 0.
- Route: `Bv := h '' (f '' [q, s])`, where `f` is the `IsPLBall 3` model of `C v`,
  `q = f⁻¹ v` and `s = f⁻¹ p` for a point `p` of the free face `F_v` (non-empty by
  `freeFaceConnected`). `F_v ∩ D e = ∅` follows from `splitProper`. The half-open segment
  maps into `interior (C v)`, and `D e ∩ interior (C v) = ∅`.
- Needed: `f` (relative interior) = `interior (C v)` by invariance of domain, and "a splitting
  disk has empty interior in ℝ³" (or `D e ⊆ frontier (C v)`). Neither was searched for yet.

## exists_twoComponents_of_pseudoCell — STUCK (not started in Lean)
- File: none. Compiles: 0.
- Route: `U_i := connectedComponentIn ((h''C u ∪ h''C v) \ Ec) (h u / h v)`. "All or none" on
  `Eint \ {P'}` uses `hcell` and needs `DQ ⊆ closure (Q₁ \ DQ)`. A third component is excluded
  because `Y \ (Ebd ∪ {P'})` is connected. It lies between the connected `interior (C·)` and
  its closure.
- Two gaps were found that the frozen hypotheses do not obviously close:
  - (a) Disjointness of `U₁` and `U₂` needs the separation `hsep` inside
    `I = interior Y` to extend to frontier points of `Y`. That needs `Y` to be locally
    collared at `frontier Y \ Ec`, a model-side property of `C u ∪ C v`.
  - (b) Clause (6) at the rim circles `h '' Dbd f`, `f ∋ u`, needs
    `Dbd f ⊆ closure F_u`. The proof reduces to "a PL disk does not locally separate ℝ³ at
    its boundary points".
- Neither gap is a counterexample. Both are genuine regularity lemmas.

## exists_edgeCollarFamily — STUCK (not started in Lean)
- File: none. Compiles: 0.
- Route: build `W e := h '' (radial collar in the `f_u` model ∪ radial collar in the `f_v`
  model)` over `f⁻¹ (D e)`. The collar thickness is a continuous function tapering to 0 at
  `f⁻¹ (midpoint)`, bounded by the distance to `f⁻¹ K`, to the other disks, and to the `V`
  margins.
- `C v \ W e` is star-shaped in the model, so it is connected.
- Needed: uniqueness of the radial representation in the standard simplex (relative
  interior, not ambient), `∂C = f (∂Δ)`, and invariance of domain to transport interiors and
  frontiers through `h`.

## isHandleDecomposition_of_edgeCollars — STUCK (not started in Lean)
- File: none. Compiles: 0.
- Route: partition `G = N' \ ⋃ Ec` into `P_w` by owner (the side of `W e`, else the unique
  cell). Each `P_w` is clopen in `G`. (7), (10a) and (10b) then follow set-theoretically,
  with `closure U₁ ∩ closure U₂ ⊆ Ec e` because components are closed.
- Remaining gap: `P_w ⊆ closure (connectedComponentIn G (h w))`. This reduces to
  `h''C w \ ⋃_{e ∋ w} W e` being connected. The reduction from `Q_w ∪ R_e` is a clopen
  argument, done on paper.
- `IsEdgeCollarFamily` gives connectivity only per single edge. Deriving it for the union
  needs unicoherence of the ball `h''C w`. That means `separates_or_separates_of_union`
  (`Connected/PhragmenBrouwer.lean`, `[SimplyConnectedSpace X] [LocallyConnectedSpace X]`)
  applied to the subspace `h''C w`.
- Not refuted: a circle-type counterexample needs a non-unicoherent `h''C w`, and the tube's
  cells are balls.

# Batch 2 (lease d)

Worker: Claude (lease d, token `claude-agent-d-20260919`), 2026-09-22, output root
`C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d`.

## isEmbedding_derivedNeighborhoodRay — CLOSED
## range_derivedNeighborhoodRay — CLOSED

- File (both leaves): `DifferentialGeometry/Topology/PiecewiseLinear/DerivedNeighborhoodRayInterior.lean`
  (43 lines, SHA-256 `bc4a8618fc18df4661d416c784adcb930aa1477ba6296f42bbe2e331ca8e1e50`).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRayInterior`
  (the module imports only `DerivedNeighborhoodRayEmbedding`).
- New public names: the two leaves only (grepped tree-wide; the only other occurrences are the
  skeleton's `sorry` copies). Statements byte-identical to
  `Skeleton/DerivedNeighborhoodComplement.lean:66-79` (checked by script, text up to `:=`), with
  the same `local notation "E3"` and the same `private noncomputable local instance
  euclideanDecidableEq`; the instance in the `range` statement is definitionally the classical
  one of `range_derivedNeighborhoodRay_of_subset_interior`, `exact`-term accepted.
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\DerivedNeighborhoodRayInterior.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 15:41 local, -07:00).
- Axiom audit: `AuditOpusD1.lean` (lease d output root, `-Audit`) — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\AuditOpusD1.lean with no diagnostics;
  shared outputs unchanged.` (15:42): closure within `propext`, `Classical.choice`,
  `Quot.sound`; the thirteen environment linters pass.
- Route: each leaf is `…_of_subset_interior A K hKA` (lease b,
  `DerivedNeighborhoodRayEmbedding.lean`) applied to
  `derivedNeighborhood_space_subset_interior (n := 2) finrank_euclideanSpace_fin hA hKA hKint`.
  Every frozen hypothesis is used (`hA` only for `N ⊆ interior |A|`); no gap.
- Lead option: the skeleton could instead call the two lease-b theorems directly; the leaves
  are kept because their statements are frozen.
- Compiles: 1 module check (≈11 s) + 1 audit (≈46 s).
