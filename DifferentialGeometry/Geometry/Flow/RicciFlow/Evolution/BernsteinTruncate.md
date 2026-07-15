# BernsteinTruncate

## 2026-07-14 finite-level heat input

`BernsteinTower.estimate_of_heat` is proved, focused-check green, and exported
by a targeted build.
For a fixed target order `m`, it keeps the original tower through `m`, sets all
higher levels and Laplacians to zero, raises the finitely many level constants
to one nonnegative constant, and applies `BernsteinTower.estimate_div`.

This resolves the apparent quantifier mismatch between a level-dependent Shi
producer and the existing all-level `BernsteinTower.hheat` field without
changing that public structure. It is reusable C2 infrastructure; it does not
prove `movingShi_of_soln` or any Hamilton endpoint by itself.
