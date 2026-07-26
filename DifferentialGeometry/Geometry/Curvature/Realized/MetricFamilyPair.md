# Smooth pairings for realized metric families

## Goal

Derive joint spacetime smoothness of a moving realized metric paired with two
globally smooth tangent sections, using only scalar local-frame components.

## 2026-07-10

- Added `MetricFamilySmoothOn.pairSmoothAt` as the generic producer underlying
  the older solution-specific `solnMetricJointAt` proof pattern.
- The proof expands the two sections in one actual local trivialization frame
  and never constructs a tensor-valued map across varying tangent fibres.
- Focused verification and the targeted module build both pass.
- The theorem is consumed by the fully applied covariant-derivative continuity
  route in `HCGCompactness/MetricC1Continuity.lean`.
