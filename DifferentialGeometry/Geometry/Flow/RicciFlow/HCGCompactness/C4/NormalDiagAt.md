# NormalDiagAt

## Role

`normalDiagAtFull` is the full fixed-source-radius assembly for the quantitative
normal diagonal branch. It separates branch construction at a supplied `q`
from the private small-radius selection used by `exists_normal_diag` and
`NormalRadiusProfile.exists_uniform_diag`.  The compatibility wrapper
`normalDiagAt` retains the established result shape.

## Producer chain

The theorem consumes the existing public bilateral-flow, quantitative-inverse,
inverse-smoothness, and intrinsic-endpoint-square producers. The source radius
must satisfy the bilateral fence, acceleration, and inverse-margin bounds. It
returns an explicit positive target radius with its formula, an `IsNormalDiag`
witness on the same branch, and `NormalDiagFence`.  The fence records that the
source and both image coordinates stay in the normal ball on the whole closed
source ball; it is the exact input needed for full source/target transport.

The fixed-radius theorem does not require a separate proof that the ambient
phase radius is positive. That fact belongs to the private radius-selection
step; at fixed `q`, the stronger bilateral fence is the operative hypothesis.

## Verification

Focused verification and the targeted module build passed without a local
warning, `sorry`, or `admit`.

## Project position

- `normalDiagAtFull` and its `normalDiagAt` projection: proved, 100%.
- Dedicated fixed-radius branch assembly: 100%.
- Quantitative normal-coordinate branch theorem: already proved independently.
- Explicit selected-branch architecture acceptance: 100%.
- Dedicated Step-B/B1 machinery: about 77%.
- Textbook B1 theorem: unstated/unproved, 0%.
- Whole HCG compactness infrastructure: about 51%.
# Normal diagonal branch at a fixed radius

`normalDiagAtFull` now calls the strong quantitative inverse producer and
retains its `ApproximatesLinearOn` witness for the exact partial
homeomorphism `e` used by `IsNormalDiag`.  The compatibility theorem
`normalDiagAt` keeps its public statement unchanged.  This is producer data,
not a new branch field or endpoint assumption.  Focused verification passed,
and the exact module object was refreshed for downstream consumers.

## 2026-07-16 lower-layer fence API

The canonical definition of `NormalDiagFence` moved to
`NormalPhaseEndpoint.lean`, where the endpoint construction first produces its
containment data.  `normalDiagAtFull` still returns that same predicate and all
existing consumers keep their names and statements; this file no longer owns
a duplicate definition.  Focused verification passed and downstream refreshes
confirmed the import boundary is stable.

This API placement change does not complete an endpoint.  `StepB1RawInput` and
textbook B1 remain theorem-level **0%**; dedicated Step-B/B1 machinery is about
**95%**, Chapter 4 about **87%**, and whole-HCG compactness machinery about
**57%**.

## 2026-07-18 framed-radius migration

`normalDiagAtFull` and `normalDiagAt` now take the canonical
`expRadiusGp / 4` quarter-ball fence.  The retained `NormalDiagFence` proof
uses the direct `normalBall = ball 0 expRadiusGp` containment.  Focused
verification and the module refresh passed.  No branch, radius assumption, or
moving-base exponential was replaced.
