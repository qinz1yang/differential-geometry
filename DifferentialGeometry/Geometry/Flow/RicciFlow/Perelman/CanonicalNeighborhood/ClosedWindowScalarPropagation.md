# ClosedWindowScalarPropagation

Claim c4894463-ee08-4e82-b081-b2fc52dcf625. Source-only until explicit compiler
handback; initially UNVERIFIED. This extends the existing LocalPropagation
first-crossing argument to terminal closed time windows and actual derivative
bounds above the curvature threshold, independent of the old witness record.

Reuse the native first-crossing lemma, smooth curves with controlled total
length, inverse-square-root and inverse derivative estimates, and the three
thresholds 2Q, 3QL, 4QL. The spatial argument is adapted directly from the
checked scalar_le_of_good_locus proof. Keep that existing public API and
its shared import cone unchanged. The time leg uses HasDerivWithinAt on
[0,1], with the actual left derivative as value via ClosedCarrierDerivative.
The carrier must contain a left neighborhood at every controlled time; the
normalized sequence's doubled source depth supplies this, even at time zero.

No regularity of the terminal slice is added. No conversion to the old
IsGoodPoint/KappaModelWitness record is assumed. The raw derivative input
is supplied by the now verified WindowedGoodPointBounds in the consumer.

Accepted 2026-09-11: saved check2 EMPTY (38.1s), named build1 (47.0s), fresh public audit standard-only. The first check passed with only an unused SigmaCompactSpace condition; that unused hypothesis was removed. The actual closed-worldline proof passed without a mathematical repair. Receipt: E:/lean-tools/chapter25-book-20260910/book-local-propagation-completion.json.

Landed in c2c9b9dc1040a88ca041fbad0fa0028a1e04fd08; this batch's ordinary file claim was released after landing. Current compiler ownership is in WORKING_STATUS.md.
