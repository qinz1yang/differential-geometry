# GPT Pro ruling — TensorRS TotalSpace topology-instance diamond (received 2026-07-24)

Verbatim ruling from the "Lean Pro Consult Handoff" consult (prompt:
`UNIF_DIAMOND_PRO_PROMPT.md`; submitted manually by the user).  Planner
digest at the end.

---

## Ruling (verbatim)

The operational conclusion is right: **proof-local pins are dead, and the repair belongs at the bundle-definition layer.** But the D-round classification is not type-correct.
`Tensor0SBundle.tensorRSSpace_topologicalSpace r s x` is a topology on the **individual fiber**
`TensorRSSpace r s I x`; it is not a topology on `Bundle.TotalSpace`. Its explicit `x : M` argument confirms this.  Mathlib's `FiberBundle` carries two distinct topology inputs: one on the total space and a family of topologies on the individual fibers.
Consequently, the trace line `result tensorRSSpace_topologicalSpace 2 2` is almost certainly the eta-reduced solution of `∀ x, TopologicalSpace (TensorRSSpace 2 2 I x)`, not the total-space topology.

### 1. Classification and canonical choices

| Declaration | Actual carrier | Classification |
| --- | --- | --- |
| `Tensor0SBundle.tensorRSSpace_topologicalSpace r s x` | `TensorRSSpace r s I x` | Canonical **pointwise fiber topology**. Keep it. |
| `Tensor0SBundle.tensorRSBundle_topology r s` | `TotalSpace (TensorRSModel …) (fun x ↦ TensorRSSpace … x)` | Canonical **bundle total-space topology**. Keep as the sole global instance. |
| `TensorRSRiemannianBundleContinuous.tensorRSSpace_totalSpace_topologicalSpace r s` | Same total space, eta-contracted family | Redundant higher-layer alias. Demote it. |
| Topology carried by `tensorRSSpace_normedAddCommGroup` | `TensorRSSpace r s I x` | Separate pointwise bundle/norm topology diamond; propositionally equal, not defeq. Do NOT conflate with this dedup. |

`tensorRSBundle_topology` is constructed from `Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace`; `tensorRSBundle_fiber/vector/smooth` are built against it.  The higher Riemannian file's wrappers unfold to the same VALUES but are harmful as REGISTERED instances (different family spellings; downstream FiberBundle types freeze the selected topology).

### 2. Minimal safe dedup design

- **Edit A** (`Tensor/RSTensor/Defs.lean`): retain the five lower-layer instances (`tensorRSSpace_topologicalSpace`, `tensorRSBundle_topology`, `tensorRSBundle_fiber`, `tensorRSBundle_vector`, `tensorRSBundle_smooth`).  Do NOT demote the pointwise fiber topology.  HARDEN `tensorRSBundle_fiber`: replace the inferred topology-family `_` argument with the explicit canonical pointwise family `fun x : M => tensorRSSpace_topologicalSpace … r s x`.  No priority changes.
- **Edit B** (`Analysis/Spectral/Tensor/ChartTensor/Inner/TensorRSContRiemannianBundle.lean`): change exactly `tensorRSSpace_totalSpace_topologicalSpace`, `tensorRSSpace_fiberBundle`, `tensorRSSpace_vectorBundle` from `instance` to `def` (names/types/bodies unchanged).  Keep `tensorRS_isContinuousRiemannianBundle` registered.
- **Edit C** (audit by full target type): grep every declaration whose RESULT type is `TopologicalSpace (Bundle.TotalSpace (TensorRSModel …) (… TensorRSSpace …))`; demote any additional alias the same way.  (Precedent: the `(0,0)` bundle already removed a duplicate total-space topology for exactly this reason.)
- **What not to do**: no priority games, no scoping the canonical instances, no extra global aliases, no new FiberBundle paired with a winning topology, no `cast`/`Eq.ndrec` transports.

### 3. Blast radius and verification sequence

Source blast radius small (one hardening + three keyword demotions); REBUILD radius large.
- Phase 1 — two tiny probes (minimal-import `RSTensor/Defs`-only + rich-import `TensorRSContRiemannianBundle`): `#synth` TotalSpace `TopologicalSpace` / `FiberBundle` / `VectorBundle`, in BOTH eta spellings, + an `rfl` check that the inferred total-space topology is `tensorRSBundle_topology`.  Both contexts must agree; traces must no longer list the three wrappers.
- Phase 2 — force-rebuild the two defining layers (`Tensor.RSTensor.Defs`, `…TensorRSContRiemannianBundle`).
- Phase 3 — the minimal failing consumers: `LieCorr0Split.lean` then `LieCorr0LowJet.lean`.
- Phase 4 — import-lucky regression: `DeTurckLieKernelL2JetBound.lean` + representatives from its cone (`OperatorFieldFibreNormJet`, `IteratedCovGradFibreNormPermutationInvariance`, `TensorRSRiemannianBundle`).
- Phase 5 — `lake build DifferentialGeometry` (the library target, NOT the default target that regenerates DeclIndex).  No clean unless olean provenance becomes doubtful.

### 4. Per-site paired pins
Not an acceptable bridge (the letIs elaborate but the topology is frozen upstream in the `SmoothCcTensor`/`ContMDiffSection` types; file-level local instances recreate the import-sensitivity at larger granularity).  Diagnostic use only.

### 5. Stop signals (stop the dedup rather than patch consumers)
1. The minimal `RSTensor/Defs` probe cannot synthesize `FiberBundle` (canonical core inconsistent — inspect the explicit pointwise-topology argument of `tensorRSBundle_fiber`).
2. After demotion, traces still show multiple total-space topology instances (audit incomplete).
3. The inferred pointwise topology is the `tensorRSSpace_normedAddCommGroup`-projected one while `tensorRSBundle_fiber` carries `tensorRSSpace_topologicalSpace` (or vice versa) — the SEPARATE fiber norm-topology diamond is the real blocker; needs a focused pointwise-normed redesign, not another FiberBundle instance.
4. Eta-expanded probe succeeds but eta-contracted fails (or conversely) — normalize the family spelling; do not restore the wrapper.
5. `TensorRSContRiemannianBundle` needs its own topology/FiberBundle back to build — repair its coupling against the lower canonical instances instead.
6. Rich-import modules need casts/topology-equality transports — the aliases are not defeq in hidden arguments.
7. Dozens of downstream proof bodies need local instance changes — incomplete dedup or stale artifacts; the patch should change instance resolution, not proofs.

Target architecture: `RSTensor/Defs` = the five canonical instances; `TensorRSContRiemannianBundle` = the continuous RiemannianBundle instance only (wrappers as plain defs).

---

## Planner digest

- The D-round's "≥3 competing TotalSpace topologies" was type-miscounted:
  one pointwise fiber topology (canonical, keep), one canonical TotalSpace
  topology, one redundant TotalSpace wrapper alias (demote), plus a
  SEPARATE documented pointwise norm-topology diamond (out of scope unless
  stop-signal 3 fires).
- Repair = Edit A (harden `tensorRSBundle_fiber`'s explicit family) +
  Edit B (3× `instance`→`def`) + Edit C (type-based audit), verified by
  the 5-phase sequence with the 7 stop signals.
- This unblocks `LieCorr0Split`/`LieCorr0LowJet` → the lieCorr0
  constituent → the Ψ₀/threeArm assembly (ruling item 2).
