# FiniteHornIntrinsicRays

Owner: Chapter25 continuation, claim 3e9f694e-5f46-4981-8fdc-832b1f005b21.
Verified 2026-09-09: focused2 EMPTY (25.63s), named build1 (52.23s),
fresh external audit1 (24.15s), all three public declarations standard-only.
Receipts: E:/lean-tools/chapter25-terminal-local-20260909/ambient-completion.json.
First check required an explicit NNReal Lipschitz constant and an explicit
constant in the limit subtraction; these were elaboration issues, not added
geometric assumptions. Proposition instances use ordinary local `let`.

Consumer of the checked InteriorSpheres, InteriorMinimizers and
CompactMetricSegment producers. For a deep point x, radii below r_E(x)
tend to that distance. The sphere endpoints tend to E, while their original
metric minimizers have a common Lipschitz bound and lie in the single compact
closure of tail 0. A limiting segment is in W except at E by the checked
annulus range lemma. Reverse and rescale it to the actual EndRay fields.

Three public declarations: a Lipschitz bridge reused by DeepMinimizers and
two actual ray-existence endpoints. The bundle Hausdorff instance is derived
locally from the C1 manifold structure, not added to the public signature.
The ray-existence theorems target only the intrinsic rays field. The raw ambient
distance and frontier-escape defect remains a separate geometric obligation.
