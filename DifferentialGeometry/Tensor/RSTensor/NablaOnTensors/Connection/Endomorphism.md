# Endomorphism.lean Notes

## Goal

Keep chart-level connection endomorphism facts near the tangent connection API.

## Result

Added `connectionEndomorphismInChartL`, the chart connection endomorphism as a
continuous linear map in the derivative vector direction.  It agrees with the
existing `connectionEndomorphismInChart` after feeding the model coordinate of a
vector field.

## Lessons

The linearity in the derivative vector is a connection-layer fact, not a
higher-order tensor fact.  Building it here keeps `totalNabla0SFun` from
manually re-proving linearity every time it constructs a leading derivative
slot.

## Verification

Verification passed.

## 2026-05-13: Centered Endomorphism Normalization

- Added `connectionEndomorphismInChartL_apply_center_modelVector`, the self-chart
  specialization of the model-vector comparison.
- Added `connectionEndomorphismInChartL_apply_center`, the ergonomic centered
  version where the derivative direction is written in the self-chart model
  coordinate.
- This closes the connection-layer normalization requested by the
  `totalNabla0SFun_apply_section` attempt.  The remaining obstruction is now in
  the tensor theorem's slot/input normalization, not in the connection
  endomorphism comparison.
- Verification passed.
