# LowRegDenseSolve

## Role

This file extends the genuine smooth Ricci--DeTurck nonlinearity from
`smoothCore` to the complete lower `H2` state ball and specializes the tame
forcing fixed-point theorem.

## Source status

- `realizeOfLE` restricts an outer-radius realization witness.
- `lowRegN` is exactly `Dense.extend` of `coreN`.
- `coreN_outer` freezes the coefficient bounds at an outer radius `Q` while
  allowing the actual state radius to be any `R <= Q`.  This avoids the false
  circular requirement of choosing `R` from the value of `B1 R`.
- `lowRegN_outer` uses `tame_lip_balls`, `dense_cont_on_balls`, and
  `dense_tame_extend`.  It proves continuity and the full-state three-arm
  estimate for the genuine dense extension, with coefficients frozen at `Q`.
- `lowreg_partial_sol` first chooses an admissible outer radius `Q`, then a
  smaller actual state radius `R`.  It converts the frozen coefficients to the
  exact `A * R`, `B`, `C` shape of `partial_sol_tame` and exports its Duhamel,
  state-ball, forcing, trace, time-derivative PDE, and forcing-norm fields.
  Its interface also returns the concrete `δ`, realization witness, and fixes
  `Nfun` by a `let` to the genuine `lowRegN`; downstream geometric consumers
  therefore do not have to unfold an opaque existential proof to identify the
  forcing on the smooth core.  The same interface exports continuity of the
  underlying `coreN`, proved from the local tame bounds rather than assumed.
- The private `realize_at_thr` obtains its radius directly from
  `hs2_op_bound` and fixes the realization parameter at the positive
  `deTurckArmContractionThreshold''`.  It does not infer an unexported sign or
  equality for the second projection of `lowreg_realize_h2`'s witness.
- No continuity or monotonicity of `B1` is used.  In particular, the source
  does not make the circular choice `B1 R * R` before freezing a coefficient
  radius.

Lean verification is deferred while the shared named build occupies the sole
Lean slot.  No `sorry`, `admit`, axiom, new class, instance, or notation is
introduced.

## Remaining frontier

The exact public uniform-family Ricci-flow theorem is still unproved.  The
next abstraction boundary is to make the constants and horizon in this
fixed-background solver uniform under the stated family bounds, and then to
realize and smooth the solution on that same horizon.
