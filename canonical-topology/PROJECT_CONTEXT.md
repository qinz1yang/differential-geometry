# Poincare local-homology checkpoint

This directory is a separate portable `PoincareLean` project prepared for
additive publication within the shared DifferentialGeometry Git repository. Its Lean
library is `Poincare`; its sources retain the original mathematical namespaces.

The source baseline is the recovered Chapter 35 commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`. This checkpoint includes 100 modules:
the dependency closure of eleven roots covering local homology, derivatives,
determinant signs, oriented chart compatibility, closed-ball classes and
unique compact chart classes, plus the actual Euclidean3 consumer's dependencies.
The latest gate freshly compiled RelativeMayerVietoris and root
in Slurm 13781140, request
`1789257537165329093-topology_checkpoint-6a6afc66`. It passed in 133.73 seconds.
The same run checked all 40 added public exports and 86 signature/axiom pairs,
including all 77 previous pairs unchanged. All 99 previous source leaves remain
byte-identical and retain earlier compilation evidence. New relative
Mayer–Vietoris results construct compatible lifts and give uniqueness under
next-degree vanishing, with actual closed-support gluing corollaries.
The preceding results prove
H_n(X,X)=0 and local/convex-support homology vanishing above the dimension,
including empty sets, rank zero and arbitrary real norms. The prior public
complement-inclusion equivalence and relative restriction
isomorphism work for bounded star-convex sets about a member in arbitrary real
normed spaces and every natural degree. The closed-ball public statements and
entire proof bodies are preserved. Global oriented generators remain open.
[provenance/SNAPSHOT.json](provenance/SNAPSHOT.json) records exact source and
configuration identity and preserves the earlier validation records. It is not
the full recovered Chapter 35 project.

Preserve Lean `leanprover/lean4:v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and DifferentialGeometry `v0.1.2`
at `1b535dd102b94cc42b107cca27059687888f08b3`. Use DifferentialGeometry only
as a pinned upstream dependency; no included Lean module currently imports it.

The mathematical work belongs to the canonical-topology workstream described
in the enclosing Schoenflies controller's
[two-project prompt](../../plan/della_two_projects_prompt.md),
[topology brief](../../plan/CANONICAL_TOPOLOGY_SPINOFF_BRIEF.md), and
[active plan](../../plan/plan_smooth_schoenflies.md). Those controller records
are external to this portable package. The package README records its limited
delivered scope and checkpoint status independently.

The frozen topology handoff is still missing. Do not reconstruct its public
contract from this foundations checkpoint. Neither the full canonical topology
suite nor the combined Schoenflies/topology goal is complete.

The older project context and agent instructions are preserved under
`provenance/RECOVERED_*.md` as historical source records. Their old machine paths,
branch destinations and release claims are not current operating instructions.
