# Compact-support flows

## API correction

The compact-support flow theorems are universe-polymorphic and now require an
ordinary smooth manifold, `IsManifold I ∞ M`, rather than the strictly stronger
analytic-manifold assumption. Their vector-field hypotheses and proofs use
only smooth regularity, so this is the honest native assumption.

## Verification

Focused verification and the targeted module export pass without warnings.
The corrected API supports the global compactly supported geodesic-spray flow
used by fixed-endpoint variation realization.
