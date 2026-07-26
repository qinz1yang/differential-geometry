# ApproxIsometryDefs notes

## 2026-07-09: separated partial-map carrier

Added the D1b-facing separated partial-map carriers:

- `PreApproxIsoSep`, separating the `C^0` pullback-metric error ledger from the
  higher covariant-derivative ledger;
- `BookApproxIsoSep`, the two-sided partial-diffeomorphism package;
- `toBook`, `toSep`, and `mono` bridges for moving between the separated and
  existing single-epsilon book carriers.

Verification passed.  These definitions are infrastructure only: no target
theorem was completed by adding them.
