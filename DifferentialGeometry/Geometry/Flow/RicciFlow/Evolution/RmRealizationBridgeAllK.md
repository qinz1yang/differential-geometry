# RmRealizationBridgeAllK

## 2026-06-13 Planner note -- local-frame all-k bridge

Current file status relevant to StarSum P3:

- `nablaKRm04Field_realizes` is the rank-uniform realization producer for
  `nablaKRm04Field S t (k+1)` as `∇(nablaKRm04Field S t k)`.
- `iteratedRmComp_eq_nablaKRm04Field` proves the all-`k` component tower bridge only for
  `coordinateFrameAt x0`, using `realizedChr` and `realizedRmBase`.
- `TimeRecursion.residualStarSumLF` uses an arbitrary smooth local frame and the concrete arrays
  `frameComp0S (S.base.rm04 s) frame` and
  `christoffelSymbolInFrame (S.family.connection s) frame hframe`.  P3 therefore needs the same
  all-`k` bridge in local-frame form.

Suggested theorem name: `iterRmLF_eq_nabla` (short enough).

Suggested statement shape:

```text
iteratedRmComp frame
  (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y)
  (fun s => frameComp0S (S.base.rm04 s) frame)
  k t x n
= nablaKRm04Field S t k x (frameTuple frame x n)
```

with hypotheses `{x : M}`, `{u : Set M}`, `hframe : IsLocalFrameOn I E 1 frame u`,
`hu : IsOpen u`, and `hx : x in u`.

Proof route should be a direct generalization of the existing coordinate-frame induction:

1. `k = 0`: unfold `iteratedRmComp_zero`, `nablaKRm04Field_zero`, and `frameComp0S`.
2. `succ k`: use the induction hypothesis as an eventual equality on a neighborhood of `x`,
   obtained from `hu.mem_nhds hx`, not from `coordinateFrameSet_open`.
3. Rewrite the `frameExtData` input using `extDerivFun_eventuallyEq_congr`.
4. Apply `covDerivStepComp_frameComp_eq` with the supplied `hframe`, `hu`, and `hx`.

Stop condition: if this proof fails because a theorem expects a coordinate frame rather than an
arbitrary `IsLocalFrameOn`, report the exact theorem and goal.  Do not move the bridge into
`TimeRecursion.lean` unless the obstacle is purely import-local.

## 2026-06-13 EXECUTOR — `iterRmLF_eq_nabla` GREEN (added here, `section Bridge`)

Added `iterRmLF_eq_nabla` in this file (NOT `TimeRecursion.lean`), per the planner preference.
Focused check + targeted build of this module both PASS, sorry-free.  No stop condition: the proof
is a **verbatim generalization** of `iteratedRmComp_eq_nablaKRm04Field` — every banked step is
already frame-general.  Exact substitutions from the coordinate proof:

- `coordinateFrameAt x₀` → the abstract `frame` (new `{Idx} [Fintype] [DecidableEq]` binders);
- `realizedChr S x₀` / `realizedRmBase S x₀` → the inlined
  `fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y` /
  `fun s => frameComp0S (S.base.rm04 s) frame` (these are exactly `TimeRecursion.lfChr`/`lfBase`
  by definition, so the bridge applies to the endpoint's tower by defeq);
- `coordinateFrameSet_open x₀ |>.mem_nhds hx` → `hu.mem_nhds hx`;
- `coordinateFrameAt_isLocalFrame_one x₀` → the supplied `hframe`;
- final `simpa [realizedChr, hframe_def] using hstep` → `simpa using hstep`.

Signature (Idx-general, `{x}`/`{u}` implicit, `∀ k`):

```text
iterRmLF_eq_nabla (S) (t) (frame) {u} (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) :
  ∀ (k) {x}, x ∈ u → ∀ n,
    iteratedRmComp frame
      (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y)
      (fun s => frameComp0S (S.base.rm04 s) frame) k t x n
    = nablaKRm04Field S t k x (frameTuple frame x n)
```
