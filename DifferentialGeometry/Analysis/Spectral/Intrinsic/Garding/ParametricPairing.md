# ParametricPairing

## Producers

- `iterL_pair_unif` combines a compact-slab operator-field jet window with the
  generic balanced pairing estimate.
- `iterL_smul_unif` combines `smul_jet_unif` with `iterL_window_pair`; its
  output is the adjacent `H^(n+1) * H^n` window needed for Young absorption.

Both constants are chosen before the parameter, input tensor, and support.

## Frontier

Both producers now pass focused verification without warnings.  The repair was
pure elaboration infrastructure: open the native `TensorSpectral` namespace,
install the finite-dimensional completeness instance, and scope the larger
heartbeat budget only to the Hom-bundle theorem.  No statement or estimate
changed.  The exact A1 square estimate is deliberately not a new frontier: the
adjacent-window estimate is the honest smooth-level input for the closure step.

`iterL_pair_unif`, `iterL_smul_unif`, and their dedicated compact-parameter
pairing machinery are 100% verified.  Uniform slot transport is likewise
focused-verified in `SlotTransportPairing.lean`.  The conjugate-heat and
Perelman endpoint theorems remain separate and are not proved here.
