# PhaseFlowExistence status

## 2026-07-10

- Added anisotropic phase scaling with separate position and velocity radii.
- `scaledPhase_lip` and `scaledPhase_norm` transfer a box-local acceleration
  estimate to the unit normalized phase ball.
- `exists_fenced` applies Picard--Lindelof and exposes the range property of
  its chosen curves: every trajectory exists on `[0,1]`, solves the exact
  unscaled phase ODE, and remains in the original closed phase box.
- Factored the interval-independent unscaling argument into a private closed-
  interval helper; the public signature of `exists_fenced` is unchanged.
- `exists_fenced_sym` uses the same numerical fence to produce one common
  family on `[-1,1]`.  It retains the exact within derivative on the closed
  interval and also exposes the resulting ordinary derivative on `(-1,1)`.
- `exists_fenced_on` exposes the same Picard core on an arbitrary positive
  symmetric time window.  The normal-phase consumer uses this to make time one
  an interior point without changing the phase-box ledger.
- `scale_maps_ball` converts an ordinary initial phase ball into the inner
  normalized ball.
- Focused verification and the targeted module refresh passed without warnings
  or new `sorry`s.

Scope accounting: the requested bilateral phase-flow existence brick is
complete (100%), and this file's fenced existence layer is complete for the
current compactness consumer.  It is supporting machinery only; the unstated
moving inverse theorem itself remains 0% complete.

The remaining work is geometric and consumer-side, not ODE existence: transport
the checked quantitative branch into the HCG readout and finite-hat assembly.
