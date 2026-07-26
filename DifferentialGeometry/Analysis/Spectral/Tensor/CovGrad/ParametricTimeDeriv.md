# ParametricTimeDeriv

## Verified producer

`exists_timeDerivCc` is focused-check green.  For a jointly smooth compactly
supported `(b,c)` coefficient family on an open time slab, it constructs a
compactly supported time-derivative family on the same slab, proves joint
smoothness, and identifies every fully applied scalar component with the
ordinary real derivative.

The implementation differentiates the fixed model coordinate
`TensorRSSpace.toModel` and returns through `TensorRSSpace.ofModel`.  This is the
cheap normal form: differentiating the dependent fibre object directly exposes
the norm-topology/bundle-topology diamond and is not definitionally stable.
No whole-Hom equality is used.

`set_option backward.isDefEq.respectTransparency false` is required by the
existing tensor-bundle instance path.  No heartbeat increase, locally constant
chart hypothesis, or new convergence assumption is needed.  `CompactSpace M`
is used only when packaging the pointwise derivative as `SmoothCcTensor`.

## Frontier

The next consumer is a pathwise derivative theorem for the completed action
`appHs`, specialized using `scalarTrace_joint` and `connTrace_joint`.  It should
remain fully applied to a Sobolev input and avoid equality of entire operator
objects.  After that, the remaining analytic step is the all-order Banach ODE
jet induction and compact-interior jet mass estimate.

Honest accounting at this checkpoint:

- `exists_timeDerivCc`: 100% verified;
- dedicated higher-time-jet machinery: about 45%;
- `galLimExt_smooth` theorem: not yet stated/proved, 0%;
- compact-interior jet mass theorem: 0%;
- scalar reconstruction and Perelman noncollapsing endpoints: 0%.
