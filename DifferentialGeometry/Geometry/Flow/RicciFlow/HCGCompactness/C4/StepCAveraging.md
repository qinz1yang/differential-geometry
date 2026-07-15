# StepCAveraging.lean

## 2026-06-30

Added the pointwise Step-C averaging wrapper.

Implemented:

- `centerAverage`, the center-of-mass average at a source point from supplied
  weights, target points, joining curves, and the pointwise `CenterInput`;
- `centerAverageOn`, the restricted-source version of the pointwise average:
  on the source set it chooses the same center of mass, and outside the set it
  uses a harmless default map so no off-set center input is needed;
- `centerAverage.on_eq`, the on-source reduction of `centerAverageOn` to the
  ordinary selected center of mass;
- `metricEnorm`, the tangent extended-norm formula in the exact shape needed by
  `CenterInput.enorm`;
- `centerAverage.mem`, the closed `2r` ball membership statement;
- `centerAverage.mem_on`, the restricted-source closed `2r` ball membership
  statement for `centerAverageOn`;
- `centerAverage.eq_of_all_eq`, the pointwise fact that the average of a
  constant finite family is that same point;
- `centerAverage.dist_le`, the pointwise `2 epsilon` stability statement;
- `centerAverage.dist_le_on`, the restricted-source pointwise stability
  statement for `centerAverageOn`;
- `centerAverage.unif_tendsto`, the uniform `C^0` stability statement:
  if every finite input point is uniformly close to the same target map on a
  set, then the center averages converge uniformly to that target map;
- `centerAverage.unif_tendsto_i`, the finite-index adapter from per-index
  uniform convergence of each input point family;
- `centerAverage.unif_tendsto_id`, the identity-target specialization for
  averaged self-maps;
- `centerAverage.unif_two_index`, the same uniform stability statement in the
  two-parameter `k,l >= N` shape needed by the Step-C/C4 average of local maps;
- `centerAverage.unif_two_index_i`, the finite-index adapter from per-index
  two-parameter convergence thresholds;
- `centerAverage.unif_two_index_id`, the two-parameter identity-target
  specialization for composed local inverse/forward maps;
- `centerAverage.activeFill`, the zero-weight-entry defaulting wrapper;
- `centerAverage.activeFill_close`, the pointwise fact that defaulted entries
  stay close when every active original entry is close;
- `centerAverage.inputOfFill`, the pointwise `CenterInput` constructor for a
  filled family: it discharges `pts_mem` from target-in-ball plus active
  original entries in the ball, discharges `enorm` through `metricEnorm`, and
  carries only the explicit completeness, weight, radius, and strict inputs;
- `centerAverage.unif_two_id_fill`, the two-parameter identity-target
  convergence wrapper where only nonzero-weight entries need convergence;
- `centerAverage.unif_two_id_fill_on`, the restricted-source version where the
  center input is required only for `x` in the source set;
- `centerAverage.unifTwoIdOfFill`, the same convergence wrapper with the
  pointwise filled-family `CenterInput` assembled from the routine active-map,
  weight, radius, completeness, and strict-convexity hypotheses, with no
  separate `enorm` hypothesis;
- `centerAverage.unifTwoIdOfFillOn`, the corresponding restricted-source
  wrapper: all radius, active-map, weight, and strict-convexity inputs are only
  required where the finite partition is valid;
- `centerAverage.unifTwoIdRegOn`, the active-region version of the restricted
  two-index identity convergence theorem.  It takes normalized POU-style
  weights, an active-support-to-region bridge, and convergence only on those
  active regions, then routes everything through `unifTwoIdOfFillOn`;
- `centerAverage.unifTwoIdDataOn`, the bundled-data version of the same
  restricted active-region convergence theorem.  Its pointwise data hypothesis
  matches the finite POU package from `NetLimitData.hatPOU_active_data`, so the
  later concrete layer can pass normalized weights and active support as one
  package;
- `centerAverage.eqn_local`, the local-radius exponential equation routed
  through `centerOfMass.expInv_eqn_local`.
- `centerAverage.eqn_local_on`, the restricted-source local-radius equation
  for `centerAverageOn`, reducing on `x ∈ s` to the ordinary selected center of
  mass.  This keeps later POU consumers from unfolding the off-source default.

The finite Step-C partition layer now supplies normalized weights and an
active-support bridge.  The new `activeFill` wrapper is the consumer-side piece
that lets later code define arbitrary local-map values outside the active
support while keeping the center average and convergence statement controlled by
only the nonzero weights.  `inputOfFill` and `unifTwoIdOfFill` now isolate the
remaining C3/C4 obligations in the expected shape: show the active local maps
land in the chosen small ball, show the target point itself lands there, import
the POU weight facts, and supply the strict-convexity input for the filled
finite family.  The tangent norm field is no longer a consumer obligation in
this layer.

The restricted-source wrappers are needed because the finite POU facts from the
good-cover layer are only meaningful on the covered source set.  They avoid an
artificial global `CenterInput`/positive-weight obligation outside that set,
while keeping the existing global wrappers available for situations where a
global family is already natural.

This is still not the full C3 partition-of-unity construction. The next
producer layer must combine the finite POU weights with concrete local
forward/inverse maps from the Step-A/Step-B geometry on the covered source set,
prove the pointwise active-map radius facts and strict-convexity hypotheses for
the filled family there, pass `NetLimitData.hatPOU_active_data` directly to
`centerAverage.unifTwoIdDataOn`, and prove the active local-map convergence on
the regions selected by the bundled support bridge.

Verification status: focused Lean check and targeted module build passed; axiom
checks for the new identity, active-fill, norm, and filled-input wrappers use
only the usual project axioms.  The restricted-source averaging wrappers also
passed focused check, targeted module build, and the same usual-axiom probe.
The restricted-source local equation wrapper passed the same checks and usual
axiom probe.  The restricted-source membership and pointwise stability wrappers
also passed focused check, targeted module build, and the usual axiom probe.
The active-region convergence wrapper passed focused check, targeted module
build, and the usual axiom probe.  The bundled active-region data wrapper also
passed focused check, targeted module build, and the usual axiom probe.

## 2026-07-01

Added `centerAverage.inputOfFillSelf`.

This is the self-centered specialization of `inputOfFill`: when the comparison
target is also the center of the radius ball, the target-in-ball hypothesis is
discharged from `dist_self` and the positive radius.  It is intended for the
concrete Step-C averaging layer, where the source point itself is the natural
center for the small ball around the local-map images.

Added `centerAverage.unifTwoIdDataSelf`.

This is the bundled-data self-centered version of `unifTwoIdDataOn`.  It removes
the separate two-index center family and target-in-ball hypothesis from the
generic averaging API: active map values only need to lie in the radius ball
around the source point itself.  The proof routes through the existing
active-fill convergence theorem and the new `inputOfFillSelf` constructor.

Verification status: the focused Lean check passed, and the downstream
`StepCAveragePOU` targeted module build passed after these helpers were added.

## 2026-07-09, explicit weight data

Added `centerAverage.WeightDataOn`, the generic pointwise package for normalized
finite weights on a source set together with their nonzero-weight active-region
bridge.  Added `WeightDataOn.data` to expose the package in the exact conjunction
shape already consumed by `unifTwoIdDataOn` and `unifTwoIdDataSelf`.

This package deliberately records no smoothness or convergence assumptions:
those remain separate producer obligations, while the center-average consumer
only needs nonnegativity, a positive entry, sum one, and active-region
membership.

Verification status: the focused Lean check passed.

## 2026-07-13, active-radius producer

Added `centerAverage.exists_active_radius`.  From two-index uniform convergence
of each nonzero-weight entry in a finite family, it constructs one
`radSeq : Nat -> Nat -> X -> Real` which is everywhere positive, strictly
dominates every active distance on the source set, and converges uniformly to
zero there as both indices tend to infinity.

The construction is the finite sum of the active distances plus the positive
tail `1 / (a + 1)`.  Thus no radius assumption is added: finiteness combines the
per-entry convergence, while the tail supplies strict positivity and strict
domination.  The theorem is metric-generic and does not depend on the
Riemannian center-of-mass implementation.

The public statement now asks only for `[Finite ι]`, installing
`Fintype.ofFinite ι` internally for the finite sum.  The surrounding file's
`[Fintype ι]` section instance is explicitly omitted from this theorem, so the
weaker reusable API does not carry an unused section variable.  The resulting
linter cleanup was included in the successful focused verification.

Verification status: the focused Lean check passed.

Accounting: `exists_active_radius` and the generic active-radius producer are
complete (100%).  Instantiating its convergence hypothesis for the concrete
finite-hat maps and proving the later cage/strict-convexity bounds remain
downstream work; no Chapter-4 endpoint theorem was completed (endpoint 0%).

## 2026-07-13, source-patch transport and finite tail

Added `centerAverage.WeightDataOn.comp`, which pulls normalized finite weight
data back along a source-set map without asserting compatibility between
different charts. Added `finite_cover_two_tail`, which takes the finite maximum
of the source-patch thresholds and produces one common two-index tail on every
patch. Both additions passed focused verification.

These are generic assembly tools only. The source-local B/C capstone and all
compactness endpoint theorems remain unproved (endpoint 0%).

## 2026-07-15, energy invariance under active filling

Added `centerAverage.energy_activeFill` and
`centerAverage.uniqueMin_activeFill`.  The first proves that replacing every
zero-weight point by the chosen filler leaves the original center energy
unchanged.  The second transports the checked `CenterInput` uniqueness theorem
back from the filled family to the actual finite-stage point family.  Both
passed focused verification.

These are pointwise energy and minimizer-identification lemmas.  They do not
assert that `activeFill` is smooth when the active set varies with the source
point.  The live all-pairs route still needs either a smooth support filler or a
support-aware moving-center theorem.  `StepB1RawInput`, textbook B1, and every
compactness endpoint remain theorem-level 0%.
