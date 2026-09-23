# BT — consult: clauses 9 and 11 of the compact graph frame (leaf `exists_compactCutAndGraph`)

Written by the lead on 2026-09-23 after the lease-b worker's Batch 8 report
(`Skeleton/OPUS_FILL_LOG_B.md`, `# Batch 8 (compact cut and graph frames, leaf 1)`). For the owner's
Codex or an external reviewer; answer in `consult/BT-compact-cut-graph-clauses-nine-eleven-answer.md`
(new file; no git writes; no frozen statement edited). Chinese or English, about 1500 words plus
Lean; the six checks of `consult/REVIEW-TEMPLATE.md` apply, concentrating on checks 4 and 6.

Object: the frozen leaf `exists_compactCutAndGraph` in `Skeleton/Section34Compact.lean` (grep it;
it now takes `h331 : Moise331OnTube` from `Section33TubeApproximation.lean` by the owner's
decision), whose conclusion includes `Section34CompactGraphFrame V h ε K K' src H f₁`
(`Section34CompactVocabulary.lean` line 384). Six bricks are real (`Section34CompactLinkCondition`,
`Section34CompactGraphApproximation`, `Section34CompactResidualCells`, `Section34CompactCarriers`,
`Section34CompactCellSeparation`, `Section33TubeApproximation`). The worker reports that
graph-frame clauses 1–8 and 10 follow from the bricks and that two clauses have no producer:

**Clause 9** (nested solid tori with a spine): for every triangle `s` of `K`, topological solid
tori `S₁ ⊆ interior T_s`, `T_s ⊆ interior S₂` (where `T_s = section34CompactFaceTorus … s`, the
cyclic union of the three vertex-ball images, an `IsCombinatorialSolidTorus`), a toroidal shell
`closure (S₂ \ S₁)` between their frontiers, and `IsSpine S₁ (h '' section34CompactSimplexRim s.1)`
(`MoiseChain.lean` line 254: a product parametrisation `D² × S¹ ≃ₜ S₁` sending an interior point
times the circle to the spine). The worker says this needs regular-neighbourhood or annulus
theory "for a PL circle with arms", absent from the tree. Questions: (a) is that right — is the
spine here the image under the topological embedding `h` of the rim of `s` (a PL circle in the
2-skeleton), so that a PL solid-torus regular neighbourhood of the PL rim, taken inside a small
neighbourhood in `V` and pushed through `h`, gives `S₁` with the product structure, and a
slightly larger one gives `S₂`, with the shell from `InnerSolidTorusToroidalShell` /
`IsTopologicalSolidTorus.exists_toroidalShell_of_isCompact_subset_interior`? What do
`CircleSolidTorus`, `SolidTorusOpenNeighborhood`, `Section34FaceTorusCycle`, `CyclicBallUnion`,
`TubeOfGraphDualCells` (grep) already give, and what is the exact missing brick? (b) The
containments `S₁ ⊆ interior T_s ⊆ … ⊆ interior S₂` require `T_s` to be a regular neighbourhood
of the spine in the same sense; is that automatic from the cut (vertex balls are dual cells of a
fine subdivision) or a separate choice of scales?

**Clause 11** (`Section34CompactExterior K K' h (vertex-ball images) (fun s => h '' conv s)`,
`Section34CompactVocabulary.lean`; read its definition): the worker says it needs `ℝ³ \ h '' conv t`
connected for the tetrahedra `t`, i.e. the named proposition `TopologicalCellComplementConnected`
(`MoiseChain.lean` line 251: every topological 3-cell has connected complement), which the
ledger lists as off the goal path. Lead observation to check: `h` is a topological embedding of
the open set `V ⊇ C` (`hh : IsEmbedding (V.domRestrict h)`), `conv t` is a PL 3-ball whose
frontier sphere has a PL bicollar inside `V`, and `h` carries that bicollar to a bicollar of the
frontier of `h '' conv t`; the tree has
`isConnected_compl_of_homeomorphClosedBall_of_isBicollared` and
`isConnected_compl_of_isBicollared_frontier` (grep `SphereSeparation/`, `Bicollar.lean`,
`BicollarSeparationAssembly`, `JordanBrouwer.lean`), so the complement of `h '' conv t` is
connected without the general (possibly wild) cell theorem. Questions: (c) does clause 11 need
exactly complement connectedness of `h '' conv t`, or connectedness of a complement relative to
the union of several carriers (read `Section34CompactExterior`)? (d) is the bicollar route sound
as stated — which existing theorem applies, with what hypotheses (compactness, the bicollar as an
open embedding of `S² × (-1,1)`, `NoncompactSpace`), and which small brick is missing (the
transport of a PL bicollar of `∂(conv t)` through `h`)? (e) if the route works, confirm that
`TopologicalCellComplementConnected` stays off the goal path; if not, state the minimal
alternative (e.g. proving the general theorem through the tree's Alexander-duality certificates
`hasAlexanderDualityH0Certificate_of_relativeH1`, `ContractibleAmbient`, `SpecializedDuality`).

Also list, in five lines each, the remaining cut-frame obligations the worker names (clauses 7
for patches, arcs, marked points and the outer kinds; 8–11; 26; 28: the face-complex descriptions
of `C_w ∩ σ` and `D_e ∩ t` and the collar of `M` near `∂C`) with the tree modules that would
supply them. Verdicts are evidence, not rulings; the lead verifies against Lean.
