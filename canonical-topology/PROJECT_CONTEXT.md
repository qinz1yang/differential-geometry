# Poincare local-homology checkpoint

This directory is a separate portable `PoincareLean` project prepared for
additive publication within the shared DifferentialGeometry Git repository. Its Lean
library is `Poincare`; its sources retain the original mathematical namespaces.

The source baseline is the recovered Chapter 35 commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`. This checkpoint includes 101 modules:
the dependency closure of twelve roots covering local homology, derivatives,
determinant signs, oriented chart compatibility, compact chart classes,
Mayer–Vietoris and compact-support vanishing, plus the actual Euclidean3
consumer dependencies. The latest gate freshly compiled CompactSupport,
CompactVanishing and root in Slurm 13781140, request
`1789259440438453253-topology_checkpoint-e60efd1d`. It passed in 151.16 seconds.
The same run checked all 43 added public exports and 95 signature/axiom pairs,
including all 86 previous pairs unchanged. The other 99 prior source leaves
remain byte-identical and retain earlier compilation evidence.

The new results give a compact carrier for each actual finite singular chain,
extend any compact-support relative class to a compact neighborhood inside a
prescribed open set, and prove actual H_n(E,E\K)=0 for every compact K when
n exceeds the dimension. They allow arbitrary real norms, nonconvex compact
sets, empty sets and rank zero. Neighborhood extension works for all degrees
in locally compact Hausdorff spaces. The existing bounded star-convex/convex
results and compact-convex compatibility theorem remain unchanged.
The earlier actual Mayer–Vietoris lifts, conditional uniqueness and oriented
compact chart classes retain their public signatures. Global oriented
generators remain open.
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
