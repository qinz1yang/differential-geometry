# PR #30 Section 32 descent: Moise integration acceptance

PR #30 at `217ca3863` contributes 47 new Lean modules and four provenance
reports, all new paths relative to its base. The same source was checked first
in an isolated worktree and then under the actual Moise integration checkout.

- The `exists_descentSequence` frozen variable block and statement are LF-identical
  to the original Section 32 skeleton (1,772 characters). No new named input,
  source `sorry`, linter suppression or resource override was introduced.
- The 47 incoming files have source hashes matching the submitted LF-normalized
  receipts. Public-name comparison against the Smooth-merged integration tree
  found only the expected duplicate with the skeleton leaf; that duplicate was
  removed by the wiring step. The final changed-file census found zero collisions.
- Isolated host checks: 47/47 strict source modules, 3/3 axiom/linter audits,
  202 declarations (77 + 82 + 43). No imported main receipt was older than its
  last certified prerequisite.
- Main checkout: 48/48 strict modules, including the promoted, sorry-free
  `Section32PseudoCell`, and 3/3 source-bound audits of the 47 incoming modules.
  All 202 audited declarations use only `propext`, `Classical.choice`,
  `Quot.sound` and pass the thirteen applicable environment linters.
- A separate main-checkout axiom probe confirms foundational closure for
  `exists_descentSequence`, `moise322`, `moise321`, `moise323` and `moise324`.
  The first three assembly theorems still require their stated earlier Moise
  inputs. The completed descent leaf does not discharge those separate inputs.
- The 47 modules and promoted Section 32 file are registered in dependency order
  in the single flat aggregate. The frozen physical-sorry total is 3 -> 2.

The full repository aggregate build is a separate delivery gate. The preceding
Smooth acceptance report documents a broader all-PL replay with the inherited
unfinished `FourSpokeCap` source outside both present entry closures. It is not
currently imported by the flat root aggregate; no root-build result is inferred
from that broader replay.

`PR30-main-host-receipts.json` contains isolated and main-checkout source-bound
receipts, audit counts, and the direct axiom-closure probe.
