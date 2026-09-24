# Marked rim collar route: completed compact cut-and-graph proof

L2 `bu_markedPrism_of_bridge` is proved, together with its actual compatible collar
and cap-free whole-ball marked-prism producer. L3, L4, L5, and L6 are also proved.
The actual `exists_compactRimCoreBuffer`, finite target rim neighborhoods, and frozen
`exists_compactCutAndGraph` assembly are proved. The statement and variable block match
the Skeleton target byte-for-byte, and all 29 cut-frame and 11 graph-frame clauses hold.
No construction hypothesis has been added to any frozen target.

This checkpoint comprises 79 modules and 214 non-auto declarations, including private helpers.
Every module compiled under the collaborator strict flags. Independent checks ran all thirteen
standard environment linters and checked every declaration's transitive axioms:
only `propext`, `Classical.choice`, and `Quot.sound` occur.
Source scans and the 1488-local-module import closure exclude forbidden debt,
resource overrides, Skeleton imports, and `HurewiczLowDegrees`.
The requested flat aggregate and `FREE_INPUTS.md` are unchanged.
The unmodified aggregate build has pre-existing sorry and linter diagnostics outside this
import closure; no clean aggregate build is claimed. The aggregate build is still running.

- Cap correction: `IsPLHomeomorphOn.exists_prism_cap_images_preserving_stdCenter` preserves the entire parametrized axis while matching both cap sets. Shared radial prism and triangle-coordinate proofs replace duplicated arguments in the pointed pseudo-isotopy modules.

- Ambient deletion: one-edge and two-edge boundary traces are realized by protected triangle moves. `IsBridgeDisk.exists_isPLHomeomorphOn_map_arc_to_subdisk` maps the actual bridge arc onto that of a prescribed bridge subdisk, fixing the ball boundary and exterior. The intrinsic-boundary invariant is proved through the finite deletion chain.

- Bridge links: `IsBridgeDisk.exists_compatible_triangulation` and `IsBridgeDisk.geometricLink_traces` derive the actual source links. Disk crosscuts and one-ended disk arcs admit relative rectangle coordinates; conical comparison preserves the disk, its intrinsic boundary, the bridge arc, and its endpoint segments.

- Collar infrastructure: indexed transverse patterns and both end cuts survive finite arc-chart gluing. A prescribed boundary-disk collar extends over a spherical boundary. `IsPLBall.exists_isPLHomeomorphOn_collar_core` constructs the ball core by an explicit collar shift; `exists_isPLHomeomorphOn_eq_on_collars` matches whole collars and extends over the remaining cores.

- Compact adapters: actual dual cells have shared marked cap centers and bridge disks. Supplied single-vertex marked prisms glue into a marked product, with an outward buffer of the whole torus. These are downstream adapters; they do not supply L2.

- Standard model: the box axis has a genuine bridge disk and exact endpoint/interior affine charts. `exists_isBridgeDisk_prism_axis` produces a full Euclidean three-ball prism and its marked bridge without hypotheses.

- Actual compatible collar: `IsBridgeDisk.exists_boundary_collar` now derives a jointly PL collar on frontier C × [0,2] from the bridge certificate and the PL ball. It includes the collar-neighborhood property, exact bridge intersection, and endpoint fibers lying in the original arc. Local charts come from actual links; finite germ restrictions avoid false closed-star intersection identities.

- Ribbon geometry: a disk meeting the ambient boundary in a boundary arc is a bridge for the closure of its complementary intrinsic boundary. Positive collar ribbons specialize this producer.

- L2 DONE: `bu_markedPrism_of_bridge` gives the whole-ball PL prism, both prescribed cap sets, ordered marked centers, and the exact marked-axis image. The cap-free primary `IsBridgeDisk.exists_prism_axis` uses actual compatible collars, finite disk-deletion sweeps, boundary arc matching, and the whole-ball shell/core extension. Cap adjustment is applied last and preserves every axis point.

- Rim buffer DONE: `exists_compactRimCoreBuffer` derives each single-vertex marked prism from its actual bridge, glues the three prisms, untwists while preserving their centers, and thickens the entire torus. The exact simplex rim is the zero section of the buffered product. `exists_compactRimNeighborhoods` chooses all buffers and finite open target constraints before approximation. The marked-product sandwich then supplies graph clause 9 from the actual target torus.

- Final assembly DONE: `exists_compactCutAndGraph` chooses the small carriers, foreign-face avoidance neighborhoods, exterior buffers, and zero-marked rim buffers before the single delayed `Moise331OnTube` application. The actual cut frame is reused with `K' = K`. Finite foreign-cell avoidance gives graph clauses 5–8; the same marked product gives clause 9; existing exterior neighborhoods give clause 11. Independent review checked every clause and the unchanged hypotheses.
