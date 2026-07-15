# NablaReactionAllK Notes

## 2026-06-14 caller cleanup

Removed local `hcov`/`hmc` witnesses that were only being forwarded to the
spatial commutator split.  The split now derives those solution-connection facts
internally.

Verification passed for the edited file.

## 2026-06-14 manifold instance cleanup

Removed the redundant explicit `infty+1` manifold binder from the concrete
nabla-reaction context.  The proof remains under the standard smooth manifold
assumptions.

Verification passed for the edited file.
