# Discharged tame-cell inputs and face-torus hypotheses

Accepted on the Windows integration host on 2026-09-24.

The two face-torus chart theorems now take `hf₁ : IsPLHomeomorphInto 3 f₁
(section34CutNeighborhood src)` instead of a complete graph frame. Their target only needs a
Hausdorff topology and the existing charted-space structure. The canonical cell restriction theorem
was generalized from a metric target to those same assumptions without changing its proof.
The four existing callers pass the PL-embedding field of their graph frame.

Fourteen application theorems in eight modules no longer take `h305 : Moise305Tame`.
They use the proved `moise305Tame` through `LoopTheorem.Moise304Producer`. The compact assembly
retains only `Moise331OnTube`; normal-family assembly retains its control and neighborhood inputs.
The lower-level implication `moise305_tame_of_moise304` remains a reusable conditional theorem:
it is used in the producer construction and is not an unresolved input of these applications.
Moving the producer import into that foundational file would create an import cycle.

Validation covers fourteen changed modules and all 261 affected tracked real-module consumers.
All compiled without diagnostics in private outputs. Two disjoint audits cover all seventy
non-automatic declarations in the changed modules (39 + 31): foundational axioms only and all
thirteen applicable environment linters. The affected ControlledGraphNeighborhood and
Section34Terminal skeletons each compile with zero errors and exactly their existing single
`sorry` warning. No new proof placeholder or warning exception was introduced. The frozen count
remains four. This checkpoint precedes the separate smooth-branch merge and its main-tree replay.
