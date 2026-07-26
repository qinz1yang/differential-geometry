# MovingImplicit

## 2026-07-16 compact-seed root tube

- `exists_rootTube` is focused-green. It extends a continuous compact family of
  nondegenerate seed roots to one smooth ambient root branch and then reuses
  `exists_compactRootTube` to obtain the uniform compact tube.
- The construction uses the existing pinned-map inverse-function API. Pointwise
  invertibility on the compact seed graph is sufficient; no quantitative
  inverse approximation or new endpoint assumption is required.
- The generic compact moving-root layer is now complete for the intended C4
  center application. The remaining work is downstream specialization to the
  limit inverse-velocity equation and its finite-slot subsequence alignment.

## Accounting

- `exists_rootTube`: theorem 100%, dedicated machinery 100%.
- Generic compact moving-root API: about 100%.
- Concrete `StepB1RawInput` producer and textbook Step B1 remain 0%; this file
  supplies infrastructure only.
