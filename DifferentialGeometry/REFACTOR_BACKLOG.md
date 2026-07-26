# Refactor Backlog

Source: user cleanup/refactor backlog, recorded 2026-06-14.

## 4. Harden the tensor-component eval API

Theme: Tensor, hide internals, simp discipline.

66 Tensor files, 37 RicciFlow files, and 31 Curvature files carry
`set_option backward.isDefEq.respectTransparency false` because
`component0S` and `coordComponent...` proofs often unfold down to
`Fin.cons` and `basisTensor0S`. Add the missing `_apply`, `_eq`, and `_ext`
lemmas so downstream proofs match structurally, then delete the transparency
hacks. This is the "warning signs the abstraction is wrong" checklist made
concrete.

## 5. Replace standing frame-regularity black boxes

Theme: RicciFlow, do not carry frontier hypotheses; factor into packages.

There are 348 occurrences across 64 files of assumptions shaped like
`...InFrameOnLocal`, `hmetricFrame`, `hmix`, and `hswap`. Consolidate them into
one or two regularity packages with restriction and gluing lemmas, including
the still-missing `Tensor0SFamilyContinuousOnSet` union-glue lemma. Build
producers instead of threading assumptions.

## 6. Finish the generic StarSum2/genStar star-action algebra

Theme: Tensor/RicciFlow, reuse and avoid component brute-force.

Tasks 39-41 are in progress. Complete the j-bucketed class plus `.nabla` and
`.add` closures so per-k reaction bounds compose structurally instead of by
per-component enumeration. This follows the CLAUDE.md rule: structural lemmas
over `fin_cases` plus `ring`.

## 7. Weakest-typeclass and section-variable sweep

Theme: Geometry/Connection, weakest assumptions and inferable implicits.

Audit variable blocks, remove unused instances, and drop gratuitous
constraints such as the `NormedSpace` plus `InnerProductSpace` double
declaration in files like `Reconcile.lean`. Clean warnings instead of
suppressing them, including unused-section-variable warnings.

## 8. Drive down maxHeartbeats overrides

Theme: Connection/Curvature/Tensor, perf smell means wrong abstraction.

There are 39 Connection, 32 Curvature, and 12 Tensor `maxHeartbeats` overrides.
Most are downstream of items 4 and 6. Once those land, remove the overrides;
they mask real cost and silently rot.

## 9. Remove dead frontiers and stale code

Theme: RicciFlow transitions and removal.

After Stage 2, delete the now-dead `leviCivitaStitched` and its five lemmas.
Triage the 22 RicciFlow sorry-files into genuine frontiers versus removable
stubs, like the already-deleted `residualStarSum` stub. Leave only intentional,
documented `sorry`s.

## 10. Naming and docstring hygiene at the public boundary

Theme: all sides, naming and result-focused docstrings.

Many public names exceed the 20-letter budget and read like proof scripts.
Move endpoint names toward the conclusion-of-hypotheses dictionary and make
public docstrings result-focused. Route and failure detail belongs in same-name
Markdown notes. This is lowest priority and should be done opportunistically
alongside the other work.

## Sequencing

Items 1-3 are the high-leverage unblocks and ride the in-flight Levi-Civita
rebuild. Items 4-6 dissolve systemic friction: transparency hacks, black-box
hypotheses, and component brute-force. Items 7-10 are hygiene that gets cheaper
once items 1-6 reduce the surface.

Items 4 and 6 need deliberate design passes rather than mechanical sweeps.
