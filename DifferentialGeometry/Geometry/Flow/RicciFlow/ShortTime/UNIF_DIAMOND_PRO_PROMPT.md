# GPT Pro consult prompt — TensorRS TotalSpace topology-instance diamond (prepared 2026-07-24)

Send in a fresh chat of the ChatGPT project "Lean Pro Consult Handoff" IF the
band-aid track fails or the pin-count is large.  Attach
`Analysis/Sobolev/TensorHilbert/LieCorr0CoeffL2JetBound.md` (§"D-ROUND
RESULT") and the trace excerpt from `split_trace.txt` (:6078-6093), plus the
instance-defining files if Case-1 attachment is used.

---

I am working in a large Lean 4/mathlib project. Do not write code first. This is a TYPECLASS/INSTANCE DESIGN consult: diagnose the instance-diamond and rule on the minimal safe dedup.

Problem:
On `TotalSpace (TensorRSModel r s ℝ E) (TensorRSSpace r s I)` our codebase has ≥3 competing `TopologicalSpace` instances (`tensorRSSpace_topologicalSpace`, `tensorRSBundle_topology`, `…tensorRSSpace_totalSpace_topologicalSpace`). Depending on a file's import set, a different one wins instance search. `FiberBundle`'s type carries the `TopologicalSpace (TotalSpace …)` instance, so in minimal-import files the winning topology has NO paired `FiberBundle` instance and every `ContMDiffSection.ext` fails with:
  `failed to synthesize FiberBundle (TensorRSModel 2 2 ℝ E) fun x ↦ TensorRSSpace 2 2 I x`

synthInstance trace evidence (decisive lines):
- goal's TotalSpace topology resolves to `tensorRSSpace_topologicalSpace 2 2`
- candidates found: `#[tensorRSBundle_fiber, tensorRSSpace_fiberBundle]`
- `tensorRSSpace_fiberBundle` rejected: eta-contracted fiber (`TensorRSSpace ?r ?s ?I`) fails to unify with the goal's `fun x ↦ …`
- `tensorRSBundle_fiber` rejected: fiber unifies (eta-expanded) but it carries `tensorRSBundle_topology` ≠ the goal's baked-in `tensorRSSpace_topologicalSpace`

Files with `.ext` failures: `Analysis/Spectral/Intrinsic/DeTurckCoefficients/LieCorr0Split.lean` (186 lines, 2 sites) and `LieCorr0LowJet.lean` (1832 lines, pervasive). Rich-import files (e.g. `Analysis/Sobolev/TensorHilbert/DeTurckLieKernelL2JetBound.lean`) succeed only because their import set makes the paired topology win.

What was tried:
- import of the module declaring `tensorRSSpace_fiberBundle` — does not resolve (eta mismatch), and worsens the diamond (even plain defs start failing)
- bare `letI : FiberBundle … := tensorRSBundle_fiber` — elaborates, `.ext` still fails (topology mismatch)
- `letI : Bundle.RiemannianBundle … := tensorRS_riemannianBundle` — wrong class (equips inner product, does not provide FiberBundle)
- paired pin (`letI` topology := tensorRSBundle_topology, then `letI` FiberBundle, both eta-expanded, installed at the failing sites) — TESTED, DEAD: the letIs elaborate but all three sites still fail (`:79` def `toSection`, `:122`/`:179` `.ext`).  Two independent reasons: (1) the WINNING topology (`tensorRSSpace_topologicalSpace`) has no paired FiberBundle instance at all — the two candidates pair with the other two topologies; (2) the topology is baked in upstream at the `SmoothCcTensor`/`ContMDiffSection` definition sites, so a proof-local `letI` arrives too late.  Per-site pins CANNOT work; only the definition-layer dedup can.

GitHub reference:
- Branch: https://github.com/liao9yuan/differential-geometry/tree/codex/analytic-producers-e87b
- NOTE: local commits may be ahead; the attached files are current.
- Instance-defining layers to inspect: `DifferentialGeometry/Tensor/` bundle files declaring `tensorRSSpace_topologicalSpace` / `tensorRSBundle_topology` / `tensorRSSpace_fiberBundle` / `Tensor0SBundle.tensorRSBundle_fiber` (grep these names), and `ChartTensor/Inner/TensorRSContRiemannianBundle`.

Constraints:
- Preserve public APIs; thousands of downstream modules currently build against the import-lucky resolution.
- Prefer the minimal dedup that makes exactly ONE topology canonical with its paired FiberBundle instance; no broad refactor.
- Any instance priority/scoping change must not flip the winner in the currently-green rich-import files.

Tasks:
1. Classify: are the competing topologies defeq? Which should be canonical?
2. Give the minimal safe dedup design (delete/demote/scope/align — exactly what edits, in which files).
3. Blast-radius assessment: what could break, and what check sequence proves safety (which representative modules to rebuild first).
4. Say whether per-site paired-pin band-aids are acceptable as a bridge, and their risk.
5. Stop signals: what failure during the dedup means the design is wrong.
