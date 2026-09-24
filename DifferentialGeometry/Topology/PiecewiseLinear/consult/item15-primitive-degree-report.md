# Section 34 primitive longitudinal degree

Base: `c6c05ca9f69376ee2be77e9ac5403be95b551311`; branch `collab/item15-trace`.

The inherited expanded audit is complete: 46 modules, 129 nonautomatic declarations,
13 environment linters, zero diagnostics, and only the permitted foundational axioms.
All 46 owned modules were freshly compiled under the prescribed flags with private outputs.
This is macOS evidence, separate from the earlier Windows checker receipts.

The first part of sub-leaf 6 is complete:
`Section34CompactFaceBallInvariants.exists_primitive_marked_meridian_coordinates_of_no_operation`.
It constructs the actual marked boundary-torus coordinates from the compact frame.
The actual longitudinal projection induces a surjection on fundamental groups and has
integral homology degree +1 or -1, with no extra frame hypothesis.

The proof compares each nonseparating trace circle with the disjoint surjective member,
uses the disk-bounding meridian to kill the first product factor, and applies infinite
cyclicity to the longitudinal factor. It does not extend the boundary chart into the solid torus.

New layer audit: 8 modules, 27 nonautomatic declarations, all 13 environment linters pass.
Transitive axiom closure is contained in `propext`, `Classical.choice`, `Quot.sound`.
All eight fresh compilations and the audit have zero diagnostics; source hashes are stable.
Receipts: `item15-primitive-degree-receipts.json`.

The excess-crossing returning arc and full admissible bigon remain under construction.
Both frozen trace headlines remain open; no manifold-twin proof is claimed.
No frozen statement, P6 module, Skeleton import, or aggregate was changed.
