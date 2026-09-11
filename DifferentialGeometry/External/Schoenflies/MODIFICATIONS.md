# Local modifications

Upstream: <https://github.com/alonamaloh/schoenflies-lean>, commit
`05a43d29cde026618777db3d4e4316204ccca237`, licensed under Apache-2.0.

The complete 128-module transitive dependency closure of
`Schoenflies.jordan_schoenflies_of_homeomorph` is included together with the
upstream `Compose.lean` and `InitialReverseTransfer.lean` modules. Internal
imports were relocated from `Schoenflies.*` to
`DifferentialGeometry.External.Schoenflies.*`. Upstream mathematical
namespaces and declaration names are otherwise retained.

Every modified Lean source carries a local-modification notice while preserving
the original copyright and author lines. The original `LICENSE`, README content
(`UPSTREAM_README.md`), and `formalization.yaml` are retained. The sources use
this project's Lean and Mathlib 4.33.1 configuration.

## 2026-09-11: Lean 4.33.1 reconciliation

The compatibility work from Ayush Khaitan's commits `ed97bb87e`, `392dcfd56`,
and `54009db02` was reconciled with the existing vendor tree.

- Removed `set_option autoImplicit true` from the 128-module theorem closure
  and explicitly bound the parameters it formerly inferred. `Compose.lean` and
  `InitialReverseTransfer.lean` remain outside that closure and retain the
  upstream option.
- Replaced deprecated set and graph APIs with their Lean 4.33.1 names:
  `Set.mem_ofPred_eq`, `Graph.edgeSet_eq_setOfPred_exists_isLink`,
  `Set.ofPred_and`, `Set.domRestrict`, `Set.domRestrict_apply`,
  `Set.range_domRestrict`, and `continuousOn_iff_continuous_domRestrict`.
- Replaced proposition-valued proof-local `letI` and `haveI` declarations by
  ordinary `let` or `have` declarations where the current source linters
  require them.
- Removed the redundant simp attributes from `det_perp_perp`, `poly_pair`,
  `Graph.mem_vertexSet_induce_component`, and
  `Graph.IsCycleThrough.cycleGraph_vertexSet`; the declarations themselves are
  retained.
- Removed unnecessary graph-finiteness assumptions from
  `Graph.IsAcyclic.longest_path_source_is_leaf`,
  `Graph.IsAcyclic.longest_path_target_is_leaf`,
  `Graph.IsDrawing.edge_radial_unique`, and
  `Graph.IsDrawing.not_three_localDirs_on_edge`.
- Removed unused infinity assumptions from the finite-transfer ear-step
  predicates and from the assembly theorems that consume already constructed
  ear steps. Infinity assumptions remain on constructions that select fresh
  cell names.
- Explicitly bound the refined domain in `RefinementStars.lean`, the real
  coordinates in `Strip.lean`, the arbitrary parameter set in
  `Polygonal.lean`, the graph variables in `Graph/Relabel.lean`, the input type
  of `exists_injective_pinned_avoiding`, and the cell-name type in
  `FreshDenseSelection.lean`.
- Made the affine reparametrization and unit interval explicit in
  `Subarc.lean` before transporting the segment-image equality.
- Qualified the Schoenflies graph namespace openings in
  `SourceAttachment.lean`, `SourceJoining.lean`, and `OverlayExtension.lean`.
- Applied whitespace-only repairs required by `git diff --check`.
