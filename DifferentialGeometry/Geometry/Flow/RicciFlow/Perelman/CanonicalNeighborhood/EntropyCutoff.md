# Book cutoff entropy constant

Current acceptance2026-09-10: saved check2 EMPTY, named build1 PASS,
fresh CutoffAxioms1 standard-only for both public producers. The exact original
cutoff_entropy_doubling body now consumes these producers and independently
audits standard-only. Frozen receipt: E:/lean-tools/chapter25-book-20260910/book-entropy-completion.json.
The source-only preparation records below are historical.

2026-09-10 Chapter25 source-only preparation while Chapter23 holds its
18:40--19:40 compiler window. Unchecked and unregistered; does not change
the original Chapter25Entropy endpoint or its proof accounting.
Claim4185c8f4-1d2e-430b-8008-f08d9f25fb14.

The existing distance tent with parameter4r/3 equals one on B(2r/3), is
supported in B(r), and has intrinsic Lipschitz constant3/r. Use the native
weak Lipschitz gradient theorem directly, now that the book admits weak W1,2
tests. At a zero of this nonnegative function, its gradient vanishes by the
local-minimum derivative theorem (and by the default derivative at points
without a derivative); no measure-zero sphere assumption is needed.

Normalize by the actual mass I. The inner half-ball gives V(r/2)<=I and
doubling gives V(r)<=D I, hence the normalized energy term is at most36D.
The scalar term uses only the upper bound on B(r). Reuse the existing
normalized entropy/Jensen inequality for -integral(w^2 log(w^2))<=log V(r).
Adding the nonnegative D/e gives exactly the book's advertised constant.
This does not import or change connectedness, curvature, or flow hypotheses.

Two public statements are source-written. The exact book constant is connected
to the original muSobolev definition in the external CutoffEntropyDraft.lean;
it adds only D/exp(1)>=0 and the elementary logarithmic scaling identity.
The normalization reuses HasWeakRiemannianGradLp.const_smul from Intrinsic/Lp,
without invoking a smooth product rule on the nonsmooth cutoff.

Next checks after the agreed handback: independent check of this saved file,
named module refresh, external CutoffAxioms and CutoffEntropyDraft checks.
All fixtures/receipts are under E:/lean-tools/chapter25-book-20260910.
