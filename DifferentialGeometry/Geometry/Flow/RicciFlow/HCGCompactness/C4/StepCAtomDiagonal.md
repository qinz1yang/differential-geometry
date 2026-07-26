# StepCAtomDiagonal status

Status: 2026-07-13, focused verification passed without warnings or `sorry`.

`HasAtomWeightLim.subseq`, `exists_atom_lim`, and `exists_atom_fin` implement
the finite source-slot diagonal for the fixed-source atom/weight package.  Each
new extraction preserves all earlier limits by the package's native `subseq`
operation; no parallel atom representation was introduced.

The finite atom diagonal sub-brick is 100%.  It does not yet construct the
stable interacting-pair transition family or feed the decoded composition into
the POU readout, so the concrete outer transition/readout theorem remains 0%.
Dedicated Step-B/B1 machinery is about 84%, Chapter 4 machinery about 80%, and
whole-HCG machinery about 53%; `StepB1RawInput`, textbook B1, and the conditional
compactness endpoint remain theorem-level 0%.

The diagonal now calls `existsAtomWeightH6` directly.  Its fixed source and
target-ball containments are reindexed through every finite induction step;
`exists_atom_lim`, `exists_atom_fin`, and the retained earlier packages are
focused-green.  A zero-consumer audit then allowed the S6 atom compatibility
entrypoint and the endpoint `ExpInverseDerivBoundInput` field to be removed.

The saved module currently has no external importer or theorem caller, so there
was no downstream `exists_atom_fin` call site to migrate.  Its `hmapsJ`
parameter is the fixed target-ball containment consumed by the H6 extractor;
the geometric producer of that containment calls
`StepBTransitionOverlap.normalTrans_mapsTo` directly in `StepCPairTail.lean`.
This keeps the diagonal abstract without adding a synonymous map wrapper.

`HasAtomWeightLim.binter_of_weight` is now focused-green.  It projects the
checked `C^infty` convergence of normalized weights to one point and one slot;
a nonzero limit weight is therefore eventually nonzero, and the existing
`seqAtom_mem_hat` plus `NetLimitData.binter_of_mem_hat` produce the eventual
source/target interaction.  This is the canonical bridge from support-local
limit data to the positive-pair H6 tail; it adds no geometric assumption and is
independent of the capstone API choice.

This completes the requested H6 migration of the existing finite source-slot
diagonal (100%).  It does not repair that diagonal's mathematically overstrong
all-live-target overlap interface.  The new `InterSlot` plus stable-disjoint
zero branch records the honest sparse route, and the limit-weight bridge now
connects actual support to that route.  Sparse active-support machinery is
about 85%; its capstone integration remains the current implementation
frontier.  Endpoint theorem percentages remain 0%.

`HasAtomWeightLim.weight_ne_tail` and `HasAtomWeightLim.weight_data` are now
focused-green. The latter reconstructs `WeightDataOn U (fun _ => univ)` from
the existing Pi-valued normalized-weight convergence, eventual stage
`seqWeights_zero_ev`, and the retained source-chart maps-to tail. No
denominator field was added to `HasAtomWeightLim`, and `StepCAtomPackage` was
not strengthened: normalization is a derived projection, not new producer
data.

The finite atom diagonal remains 100%; sparse active-support machinery is now
about 92% and pair-to-capstone integration about 78%. Dedicated Step-B/B1
machinery remains about 84%, Chapter 4 about 80%, and whole-HCG machinery about
53%. `StepB1RawInput`, textbook B1, and compactness endpoints remain 0%.

`HasAtomWeightLim.weight_data_of_innerCover` is now the primary normalized
weight projection for a chart mapping into the strict inner-ball union. It uses
the existing `seqWeights_data` directly on that union. The older `weight_data`
statement remains a corollary through `innerBall_cover`. Focused verification
passed, with no new field added to `HasAtomWeightLim`.

`HasAtomWeightLim.of_atoms` is now focused-green. It is the thin downstream
projection of `atomWeight_of_atoms`: prescribed per-slot atom limits and the
existing direct inner-cover premise are packaged into `HasAtomWeightLim`
without adding an assumption, field, alias, or second atom representation.
This local packaging brick is 100%; sparse active-support machinery remains
about 92%, pair-to-capstone integration about 78%, dedicated Step-B/B1
machinery about 84%, Chapter 4 about 80%, and whole-HCG machinery about 53%.
`StepB1RawInput`, textbook B1, and the compactness endpoints remain theorem-level
0%.

## 2026-07-18 framed normal-coordinate migration

The complete canonical atom-diagonal surface now uses the framed semantics.
`HasAtomWeightLim.of_atoms`, both normalized-weight projections,
`binter_of_weight`, `exists_atom_lim`, and `exists_atom_fin` map source domains
with `framedExpDiffeo`; the H6 target cages use `framedExpMap`; all source and
target radius premises use `expRadiusGp`.  The finite subsequence induction
passes these same framed premises without adding a field, wrapper, or
assumption.

Source review is clean, but focused verification is blocked by exactly two
stale `StepCAtomPackage` declarations: the exported `atomWeight_of_atoms` still
expects the raw source map, and `existsAtomWeightH6` still expects the old
`expMapC2Radius` premise.  No independent proof or type error was exposed.  The
ordered refresh/recheck chain is `StepCAtomConv`, `StepCAtomJoin`,
`StepCAtomPackage`, then a focused check of this module; refresh this module
only when its downstream consumer requires the artifact.

Accordingly, atom-diagonal framed source migration is 100%, but the migrated
theorems are 0% revalidated until that upstream refresh chain completes.  The
selected B/C capstone, `StepB1RawInput`, textbook Step B1, and unconditional
compactness endpoints remain theorem-level 0%; whole-HCG support machinery is
approximately 60%.
