# Package G: closing the last Section 34 sorry by a weaker final configuration

Two branches carry the same mathematics:

* `codex/package-g-final-configuration` (worktree `E:\differential-geometry-dev\.codex-scratch\package-g-final-configuration`):
  the work as first developed on `origin/codex/package-g-protected-circle` (`28a40080a`, rebased
  onto `a98d2dd77`).  No build on this host covers that branch's module cone, so nothing there was
  elaborated; it is kept only as the record of the package-g-based variant.
* `codex/moise-confined-tube` (worktree `D:\differential-geometry-confined-tube`), started from the
  lead's merge branch `codex/moise-pc-merge-20260924` @ `c2a18f12f` (moise-integration with the
  Poincaré development merged, controlled graph neighbourhood skeleton down to the single step
  `sorry`).  This is the branch to take.  From package-g it cherry-picks, as files, the 431 modules
  in the import closure of `exists_section34_single_trace_motion` and of the per-edge removal
  machinery that the merge branch lacks (none of them changed between `28a40080a` and `a98d2dd77`);
  the 654 shared base modules differ from package-g's copies only cosmetically except for 43, of
  which 10 are imported directly by the cherry-picked modules, and those 10 differ by dropped
  redundant instance binders or added ones on declarations the cherry-picked modules never use.
  All 2008 modules of the closure that exist on the merge branch reuse the lead's build artifacts
  (LF-identical sources); the 431 cherry-picked modules and the six new or modified ones are
  compiled from source.  Written 2026-09-24.

Status legend used below: **compiled and axiom-checked** means the module was elaborated on this
branch and `#print axioms` was run on the theorem; **argued on paper** means the statement and proof
text exist on the branch but have not yet been elaborated.  Section 5 says which is which.

## 1. Audit of the post-descent consumers (H1)

The post-descent configuration is `hpack₂` in `controlledGraphNeighborhood`
(`Skeleton/ControlledGraphNeighborhood.lean`, obtained on the branch from
`exists_section34ProtectedCircleRemoval`).  Every declaration that receives it, transitively, and
the clauses of `Section34PiercingConditions` (numbered 1–22 in definition order, clause 3 being
`(3a) G b '' Sn e ⊆ Q a ∧ (3b) G a '' Sn e ⊆ Q b`) it destructures:

| consumer | branch | how it takes the package | clauses read |
| --- | --- | --- | --- |
| `controlledGraphNeighborhood` (assembly) | both | `obtain ⟨-, hGQ₂, …, hGp₂, …, hCpdisj₂, …, hLdisj₂, -⟩ := id hpack₂` | 2, 11, 14, 21 |
| `section34Core_of_eqOn_off_support` | both | takes `hGp₁ hGp₂ hoff₂`, no package | none |
| `exists_section34DeletedBalls` (`Section34DeletedBalls.lean:82`) | both | `obtain ⟨-, -, -, -, -, -, hbd, hAb, -, -, hGCp, -, -, -, -, -, hcnt, hPg, -, -, hover, hbody⟩` | 7, 8, 11, 17, 18, 21, 22 |
| `exists_section34EdgeMatching` (skeleton leaf) | package-g | `sorry`; `hpack` passed wholesale to nothing | none (leaf) |
| `exists_section34EdgeMatching` (`ControlledGraphNeighborhoodReduction.lean`) | package-g | passes `hpack` to three `sorry` leaves `exists_joint_boundary_matching`, `face_rim_subset_interior_deleted_family`, `exists_nested_torus_of_deleted_family` | none (leaves) |
| `exists_section34EdgeMatching` (`Section34EdgeMatchingLeaf.lean`) | moise-integration | passes `hpack` to `exists_section34_joint_cell_matching`; the rim and nested-torus lemmas take no package | via joint matching |
| `exists_section34_joint_cell_matching` (`Section34JointCellMatching.lean:64`) | moise-integration | passes `hpack` to `exists_section34_positive_reference_maps`; `exists_section34_reference_ball_maps` takes `hprep` only | via reference maps |
| `exists_section34_positive_reference_maps` (`Section34PositiveReferenceMaps.lean:69`) | moise-integration | `obtain ⟨-, …, -, hsep⟩ := id hpack`; `hsep` is passed to `exists_section34_relative_edge_character`, whose hypothesis is the bare clause | 22 |

Union of clauses read after the descent: **{2, 7, 8, 11, 14, 17, 18, 21, 22}**.  No consumer reads
clause 3 at all, in either half.  H1 holds: nothing after the descent needs (3a), and the fact
those consumers use about the tubes is only what clause 4 and clause 2 give.  The audit was done
by reading every `obtain … := hpack` pattern in the files above (`grep -n ":= hpack\|:= id hpack"`
over the two checkouts); the moise-integration files were read from
`D:\differential-geometry-moise-int` at `21543f9d7`.

Where (3a) is consumed *inside* the descent: only by the step.  `section34_second_vertex_motion_properties`
uses `(hSn e₀).2` (3b) to see that `Sp e₀ ⊆ Q b`; `section34_second_motion_cross_carriers_of_mapsTo`
re-establishes (3a) for the modified family and is the only place `hforeign` is used; the
`section34Step_*` preservation lemmas destructure clauses 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 21, 22.

## 2. H2 checked against the actual single-trace motion

`exists_section34_single_trace_motion hprep hpack e` (`Section34SingleTraceMotion.lean`) gives, for
every edge `e` (no hypothesis `1 < cnt e`), `k : Fin (cnt e)`, `K`, `ψ : M₂ ≃ₜ M₂` with

1. `IsCompact K`, 2. `K ⊆ interior (Sp e)`, 3. `EqOn ψ id Kᶜ`,
4. `IsPLOn 3 3 ψ (interior (G a '' Cc a))`,
5. `Disjoint K (G a '' (Ab₀ e ∪ Ab₁ e))`, 6. `Disjoint K (G b '' (Bb₀ e ∪ Bb₁ e))`,
7. `Disjoint K (closure (G b '' CpBd b \ G b '' Bb e))`, 8. `Disjoint K (Pg e k)`,
9. `G a '' CpBd a ∩ ψ '' (G b '' CpBd b) = Pg e k`.

Everything is local to `Sp e` (clauses 2, 9 and the disk-motion consequences), and the moves are
chosen once, on `G⁰`.  With `Ψ_w := ∏_{e : (ends e).2 = w} ψ_e` (finite by
`section34_incident_edges_finite`) and `G'_w := Ψ_w ∘ G⁰_w`:

* `Ψ_w` is the identity off `⋃_{e→w} K_e` and equals `ψ_e` on `K_e`; since `K_d ⊆ Sp d` and the
  tubes are pairwise disjoint (clause 6), `Ψ_w = ψ_e` on all of `Sp e` when `w = b_e`, and
  `Ψ_w = id` on `Sp e` when `w ≠ b_e`.  So on `Sp e` the final family is the single-edge outcome
  `section34VertexModification G⁰ b_e ψ_e`, the first-end map is untouched on `Sp e`, and
  `Sp e = G'_a '' Sn e`, `Tp e = G'_a '' Tn e` (clause 4) survive.
* The confinement of the new intersections needs one fact beyond disjoint supports: for `e ≠ d`, the
  boundary sphere of an end `w` of `e` meets `Sp d` only if `w` is an end of `d` (clause 13).  Two
  distinct edges cannot share both ends in either order (`hends`: an edge is the union of its two
  vertex simplices; `section34_edge_eq_of_ends_eq`, `section34_edge_eq_of_ends_swap`), so the sphere
  of `a_e` misses every `Sp d` with `d → b_e`, `d ≠ e`, and the sphere of `b_e` misses every
  `Sp d` with `d → a_e`.  Hence `G'_a(CpBd a) ∩ G'_b(CpBd b) = G⁰_a(CpBd a) ∩ ψ_e(G⁰_b(CpBd b)) = Pg e k`.
* Clauses that must be re-proved for the final family and how: 1, 11 (iterated
  `postcomp_of_supported_isPLOn` along the finite composition); 2 (`K_e ⊆ Sp e ⊆ Q b` by 3b);
  4, 12, 13 (identity of `Ψ` on the relevant sets); 7, 9, 15, 16, 17, 18, 19, 20 (the single-edge
  outcome, transported by the coincidence on `Sp e`); 8 (side clause: the interior is transferred
  through the open set complementary to the other supports at `b`, which contains `Sp e`);
  14, 21, 22 (`Ψ_w '' A ⊆ A ∪ ⋃_{d→w} K_d`, then `section34_support_disjoint_other_cell`,
  `section34_support_disjoint_other_lens`, clause 10); 5, 6, 10 and the new clause 3 are
  `G`-independent.
* Quantifier extremes.  `cnt e = 1`: the motion still exists and is applied; the outcome has one
  circle, nothing is assumed about strict decrease, so the count-one edges need no case split.
  A vertex with many incoming edges: the composite is a finite product over disjoint supports; the
  order is immaterial, and only the finiteness of `{d | (ends d).2 = w}` is used (also for the
  closed finite union in clause 8).  Several edges sharing both endpoints: impossible for distinct
  edges (the two edge-identity lemmas), which is exactly what the sphere-confinement argument needs;
  edges sharing one endpoint are the generic case handled by clause 13.

H2 holds on paper, and it is what the Lean development below formalises.

## 3. Design

New predicate `Section34ConfinedTubePiercingConditions` (`Section34ConfinedTubePiercingConditions.lean`):
identical to `Section34PiercingConditions` except that clause 3 is
`∀ e, Sp e ⊆ Q (ends e).1 ∩ Q (ends e).2`.  `cnt` and `Pg` stay parameters, so the consumers keep
their signatures; `∀ e, cnt' e = 1` remains a separate conclusion as before.
`Section34PiercingConditions.confinedTube` proves the original conditions imply the new ones.

New theorem `exists_section34ConfinedTubePiercingConditions_count_eq_one`
(`Section34ConfinedTubeCircleRemoval.lean`): from `hprep` and a full `Section34PiercingConditions`
package it produces `G' cnt' Pg'` with the confined-tube conditions, `∀ e, cnt' e = 1`,
`∀ w, EqOn (G' w) (G w) {x ∈ Cc w | ∀ e, G w x ∉ interior (Sp e)}` and
`∀ w, EqOn (G' w) (G w) (simplexBody 𝒦' w.1)`, that is the same guarantees as
`exists_section34ProtectedCircleRemoval` without the compact envelopes `K`, and without the step
leaf.  Supporting declarations:

* `DisjointSupportedMotionComposition.lean`: `exists_homeomorph_of_finite_disjoint_supported_isPLOn`
  (finite composition of disjointly supported motions, each PL on an open set around its support,
  agreeing with each factor on its support, identity off the union, and carrying PL embeddings of
  cells to PL embeddings) and the namespace `SupportedHomeomorphFamily` (reading a target-indexed
  family of such composites support by support).
* `Section34CarrierSingleTraceRemoval.lean`: the per-edge outcome
  `section34_single_trace_carrier_motion_conditions` extracted from the existing removal step
  (which now calls it); statements of the existing theorems unchanged.
* `Section34ConfinedTubeCircleRemoval.lean`: `section34_edge_eq_of_ends_eq`,
  `section34_edge_eq_of_ends_swap`, `exists_section34_vertex_supported_motions`, the assembly
  `section34ConfinedTubePiercingConditions_of_single_trace_motions`, and the final theorem.

Consumers re-stated with the new predicate (proof bodies unchanged, the destructuring pattern is
the same 22-clause shape): `exists_section34DeletedBalls`; the `exists_section34EdgeMatching` leaf
in both skeletons and the three leaves of the reduction skeleton.  The assembly
`controlledGraphNeighborhood` now calls the new theorem; the compact-envelope hypothesis `hK` it
built for the descent is gone.  Kept unchanged and now unused on the assembly path: the step leaf
`exists_section34ProtectedCircleRemovalStep`, the descent `exists_section34ProtectedCircleRemoval`,
`Section34CircleRemovalDescent`, and the probe with its `sorry`.

Not on this branch: the moise-integration modules `Section34EdgeMatchingLeaf`,
`Section34JointCellMatching`, `Section34PositiveReferenceMaps` must take the new predicate when the
two branches meet; only their hypothesis type changes (`hsep` is clause 22 in both predicates).

## 4. Findings outside the task

* The collaborator's own `Section34ProtectedCircleRemovalReport.md` (at `a98d2dd77`) lists as the
  remaining admission that "the singleton second-endpoint motion has no theorem preserving every
  other incoming carrier `Q c` when its tube enters the active `Sp e`", which is exactly clause
  (3a); the route here never re-establishes that clause, so the admission does not arise.

* No build on this host contains oleans for the package-g modules.  `E:\differential-geometry-dev\.lake\build`
  has 4 Section 34 oleans, the lead's merge worktree (`codex/moise-pc-merge-20260924`, merge base
  with package-g `6d6815d99`) has none of the single-trace modules, and no other worktree has any.
  The import closure of the new modules is 1738 modules; 523 have LF-identical sources with an
  existing olean, 289 more will be covered when the lead's root build finishes, and 926 must be
  compiled from source on this branch.
* The lead's root build in `moise-pc-merge-20260924` failed at 13:25 PDT with `no space left on
  device` at module 20274 of 24972 (E: had 2.5 GB free at 12:50), and was restarted at 13:27 after
  space was freed; this branch keeps its whole `.lake` on D: through a junction for that reason.
* At 15:13–15:15 PDT a `lake build` of this branch's target modules was running inside this
  worktree that this session did not start (its outputs landed in this `.lake/build`); the session's
  guard that stops its own build when a root-scale build appears matched it by the target names and
  killed it at 15:15.  Whoever started it: the build driver here resumes the same targets whenever
  at most four foreign `lean.exe` are running and no other `lake` is building these targets.
* The package-g branch registers 67 of its 799 `Section34*` modules in `DifferentialGeometry.lean`;
  732 are unregistered (the whole single-trace development among them).  The three new modules
  are registered next to `Section34CircleRemovalDescent`.

## 5. Verification status

On `codex/moise-confined-tube` (worktree `D:\differential-geometry-confined-tube`, base `c2a18f12f`),
2026-09-24 16:35–16:45 PDT, `lake build` of the four targets `Section34ConfinedTubeCircleRemoval`,
`Section34DeletedBalls`, `Skeleton.ControlledGraphNeighborhood`,
`Skeleton.ControlledGraphNeighborhoodReduction`: **Build completed successfully (6439 jobs)**, zero
errors; the only warnings are the three pre-existing `sorry` leaves of the reduction skeleton.  The
431 cherry-picked modules, the four new or refactored modules and the five restated consumers all
elaborated from source on the merge-branch base (2008 base modules reused from the lead's build).

`#print axioms` through `lake env lean` on a probe outside the tree, all **compiled and axiom-checked**,
each `[propext, Classical.choice, Quot.sound]`:
`exists_section34ConfinedTubePiercingConditions_count_eq_one`,
`section34ConfinedTubePiercingConditions_of_single_trace_motions`,
`exists_section34_vertex_supported_motions`, `exists_homeomorph_of_finite_disjoint_supported_isPLOn`,
`Section34PiercingConditions.confinedTube`, `section34_single_trace_carrier_motion_conditions`,
`section34_removal_step_of_single_trace_carrier_motion`, `exists_section34DeletedBalls`,
`exists_section34_single_trace_motion`, and the endpoint **`controlledGraphNeighborhood`** — which no
longer depends on `sorryAx`.  The step leaf `exists_section34ProtectedCircleRemovalStep`, the count
descent and `exists_section34ProtectedCircleRemoval` were then deleted from the skeleton as dead
code; the skeleton rebuilt with no `sorry` and the endpoint's axiom set is unchanged.

Name reconciliation needed by the cherry-pick (both branches had re-proved the same facts): nine
package-g copies were dropped in favour of the merge-branch declarations (`IsAnnulusOn.symm`,
`IsAnnulusOn.locallyConnectedSpace`, `IsAnnulusOn.isCompact`, `IsAnnulusOn.isConnected`,
`IsPLAnnulusWithEnds.symm`, `IsTopologicalSolidTorus.fundamentalGroupEquivInt`,
`IsPLCellOn.closure_sdiff_boundary`, `IsPLCellOn.isConnected_interior`,
`IsCombinatorialManifold.subset_or_disjoint_disk`), and three package-g theorems whose statements
differ from the merge-branch namesakes were renamed: `section34_piercing_trace_nonempty_of_sides`,
`IsPLHomeomorphInto.carriesFundamentalGroupOnto_of_image_of_subset`,
`IsAnnulusOn.image_inter_frontier_nonempty_of_eqOn_ends`.  A declaration scan over the whole tree
finds no remaining duplicate full names.

The lead-style audit (axiom closure plus the thirteen Mathlib environment linters, excluding the two
documentation linters) over the 431 cherry-picked modules, the four new modules and the three
edge-matching consumers, run through `lake env lean` on a probe outside the tree: **1150 declarations
from 438 modules, 0 failures** (17:15 PDT).  Its first passes found four `unusedArguments` hits, all
redundant instance binders in cherry-picked modules (`annulus_product_arc`,
`signs_of_frontier_reading`, and the finite-dimensionality binders that
`IsAnnulusOn.eq_or_eq_product_bands` and `IsAnnulusOn.exists_product_arc_eq` inherited from the
first); the binders were removed and the affected modules rebuilt.  After the final rebuild
`controlledGraphNeighborhood` again depends on `[propext, Classical.choice, Quot.sound]` only.

## 6. Open items

* The reduction skeleton `ControlledGraphNeighborhoodReduction` keeps its three `sorry` leaves
  (`exists_joint_boundary_matching`, `face_rim_subset_interior_deleted_family`,
  `exists_nested_torus_of_deleted_family`); the endpoint does not go through them, since
  `exists_section34EdgeMatching` is the proved module `Section34EdgeMatchingLeaf`.
* The 431 cherry-picked modules and the three new ones are registered in `DifferentialGeometry.lean`;
  a root `lake build DifferentialGeometry` was not run (the owner's rule for this host).
