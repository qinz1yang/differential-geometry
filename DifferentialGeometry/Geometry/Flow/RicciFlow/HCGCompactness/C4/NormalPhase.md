# NormalPhase status

## 2026-07-10

- `normalAccel_eq` identifies the bump-extended normal metric acceleration
  with the raised Koszul expression on the quarter normal ball.
- `normalAccel_norm` and `normalAccel_lip` are uniform in the sequence index
  and base point once a common source radius is supplied.
- `normalAccel_zero` records the stationary zero phase needed to normalize the
  quantitative endpoint branch at the model origin.
- `normalDiag_approx` is the reusable conditional endpoint estimate.
- `exists_normalFlow` now discharges its former trajectory assumptions.  For
  a sufficiently small ordinary phase ball it constructs exact trajectories,
  fences them in the controlled normal phase box, and proves the retained
  endpoint map `ApproximatesLinearOn` the free diagonal map.
- Focused verification passed.

The normal acceleration and fenced-flow producer layer is complete for the
current quantitative branch.  Endpoint naturality is now handled downstream
by `NormalPhaseEndpoint`; the live frontier is transporting the resulting
uniform branch into the HCG readout consumer.

## 2026-07-18 framed-radius migration

- The quarter-ball hypotheses of the acceleration, Lipschitz, endpoint
  approximation, and flow producers now use the canonical `expRadiusGp`
  profile.
- Focused verification passed.  This is a consumer-interface migration; it
  does not prove the sequence-uniform H6 radius profile.
