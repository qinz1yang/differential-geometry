# RicciIdentity split note

Goal: move the tensor Ricci-identity interface out of the realized folder.

What worked: `DifferentialGeometry/Tensor/RicciIdentity.lean` now owns the existing
one-form Ricci-identity statements and realization bridges. The old realized
file is only an import wrapper.

Current risk: this is not a proof cleanup. The existing bridges remain because
downstream Levi-Civita and scalar-Bochner files still consume them.

unfolding in the moved proof scripts.

## 2026-05-11: Smooth one-form realization interfaces

- Lowered `OneFormSection`, `TwoTensorSection`, `NablaOneFormRealizesAt`, `NablaOneFormSectionRealizes`, `Nabla2OneFormRealizesAt`, and `nabla2OneFormRealizesAt_of_totalNabla` to smooth inputs.
- The file now consumes the smooth `TotalNabla0SRealizes` predicates directly.
- Verification passed.

## 2026-05-13: Theorem 14.12 invariant interface

Worked:

- Added the real `(0,s)` Ricci-identity interface:
  `oneFormAtSlot0S` / `freezeSlot0SAt`, `curvatureAction0SAt`,
  `Tensor0SRicciIdentityAt`, and the torsion-corrected variant.
- Added general `(0,s)` first/second derivative realization predicates matching
  the existing one-form realization style.
- Proved the checked `s = 1` bridge:
  `tensor0S_ricciIdentity_one`, showing the new invariant statement is
  equivalent to `OneFormThirdCovDerivCommAt`.
- Proved the torsion-free corollary from the torsion-corrected statement by
  multilinearity in the first derivative slot.

Remaining frontier:

- `tensor0S_ricciIdentity_with_torsion` is the single intentional producer
  frontier. It should be proved by the invariant moving-slot expansion, scalar
  commutator, and slotwise one-form Ricci identity, not by adding coordinate
  Christoffel assumptions.

Verification passed with the expected single `sorry` warning at that frontier.

## 2026-05-13: Definition 14.5 wrappers for 14.12

Worked:

- Added `Nabla0SSectionRealizes.eval_smooth_slots`, exposing Definition 14.5
  from the section-level first-derivative realization predicate.
- Added `Nabla20SRealizesAt.eval_smooth_slots`, exposing the same moving-slot
  rule for the outer derivative in the second covariant derivative realization.
- These wrappers checked and avoid reopening the coordinate/model construction
  in future Ricci-identity proofs.

Failed:

- The full `tensor0S_ricciIdentity_with_torsion` proof is not closed in this
  pass. The obstruction is not mathematical; it is the missing reusable
  finite-sum derivation algebra for arbitrary covariant valence `s`.
- The existing single `sorry` frontier remains the right visible frontier. I
  did not replace it with a new coordinate-Christoffel hypothesis or an
  equivalent wrapper assumption.

Next step:

- Prove a pure algebra lemma for the commutator of the derivation-style
  `(0,s)` covariant derivative. It should handle the double finite sums and
  slot-update cancellations once, then instantiate it with vector fields and
  `nabla0SFun_eval_smooth_slots`.

## 2026-05-13: Public theorem reduced to section-level frontier

Worked:

- `tensor0S_ricciIdentity_with_torsion` now performs the pointwise-to-section
  setup itself: it chooses smooth extensions for `X`, `Y`, and every covariant
  slot, then delegates only the moving-slot expansion to a private helper.
- The remaining helper is named
  `tensor0S_commutator_expansion_from_realizes`.  Its statement is narrower
  than the public theorem because all pointwise extension choices have already
  been made.

Failed:

- The proof is not closed.  The real remaining calculation is the finite-sum
  section-level expansion: expand the two second covariant derivatives, apply
  the scalar bracket commutator, cancel off-diagonal double slot updates, and
  identify the diagonal terms with `connectionRiemannCurvatureField`.
- The generic theorem now explicitly requires `[T2Space M]`, because the
  pointwise-to-section setup uses `ContMDiffSection.exists_eq_at`.  The
  Levi-Civita consumer already has this hypothesis.
- Verification passed for the focused file check and the targeted
  `DifferentialGeometry.Tensor.RicciIdentity` build, with the expected single `sorry`
  warning at the private frontier.  The downstream Levi-Civita curvature
  focused check also passed; its longer targeted build outlived the tool
  timeout, so no final build result was captured.

Lesson:

- The useful frontier is not a pure pointwise algebra lemma over one tangent
  space.  Directional derivatives act on scalar functions built from moving
  slots, so the reusable calculation must live at the section/moving-slot
  level.

## 2026-05-13: Pure double-update cancellation

Worked:

- Added the pure finite-index/update algebra block before the section-level
  Ricci-identity frontier:
  `update_update_ne_comm`,
  `double_sum_sub_eq_diag_sub_diag_of_offdiag_swap`, and
  `double_update_sum_cancel_diag`.
- These lemmas contain no geometry.  They isolate the off-diagonal
  double-slot cancellation needed after expanding the two second covariant
  derivatives by Definition 14.5.
- Verification passed for the focused file check.

Remaining frontier:

- The private theorem `tensor0S_commutator_expansion_from_realizes` still has
  the single intentional `sorry`.  The next proof step is to use
  `double_update_sum_cancel_diag` at the exact off-diagonal cancellation point,
  then separately handle the diagonal curvature rewrite and first-slot torsion
  linearity.

## 2026-05-13: C1 regularity bridge and local algebra helpers

Worked:

- Added `Nabla0SSectionRealizes.eval_C1_slots`, backed by the new C1
  moving-slot theorem in the tensor/nabla regularity layer.
- Added private helpers for the two algebraic end pieces:
  `curvatureAction0SAt_eq_neg_sum_connectionRiemannCurvature` and
  `first_slot_torsionCorrection_eq`.
- Verification passed with the same single intentional frontier `sorry`.

Failed:

- `tensor0S_commutator_expansion_from_realizes` is still not closed.  The C1
  regularity obstruction is gone; the remaining proof is the large
  section-level expansion/cancellation itself.

Next step:

- Expand the two `Nabla20SRealizesAt.eval_smooth_slots` equalities, rewrite the
  resulting first-derivative scalar functions with
  `Nabla0SSectionRealizes.eval_C1_slots`, then apply
  `double_update_sum_cancel_diag`.

## 2026-05-14: Curvature action extraction

Worked:

- Moved the `(0,s)` curvature-action definitions and Ricci-identity predicates
  into `Tensor/RSTensor/CurvatureAction.lean`.
- Replaced the local private Rm13-to-connection-curvature bridge with the
  reusable bridge from the new action layer.
- Refactored the commutator proof to pass through
  `curvatureAction0SAtSlots` before converting back to the public Rm13 action.

Verification passed.

Lesson:

- `Tensor/RicciIdentity.lean` should own the commutator proof, but not the
  definition of curvature action.  The proof-safe curvature object is the
  slot-map replacement action; the Rm13 statement is the canonical public
  wrapper.

## 2026-05-13: Partial proof scaffold inside commutator frontier

Worked:

- Replaced the bare body of `tensor0S_commutator_expansion_from_realizes` by a
  checked partial proof scaffold.  The theorem now constructs named facts for
  both second-derivative expansions, both first-derivative expansions, the C1
  correction-slot expansions, the curvature-action rewrite, and the torsion
  first-slot rewrite.
- The remaining `sorry` is now at the final assembly point only.  The comments
  in the proof list the intended manual close order.
- Verification passed with the same single intentional `sorry` warning.

Remaining frontier:

- The final proof step still needs to normalize the `Fin.cons`/`Function.update`
  expressions into the exact shape of `double_update_sum_cancel_diag`, apply the
  scalar bracket commutator, and combine the resulting diagonal terms with the
  curvature and torsion bridge facts already named in the proof.

Lesson:

- For this theorem, the useful partial proof should expose named expansion
  facts rather than trying to compress the calculation into one large tactic
  block.  The C1-slot API and torsion/curvature bridge lemmas now check, so the
  only remaining work is finite-sum assembly.

## 2026-05-13: HExpanded cut and point-vector wrapper

Worked:

- Added `Nabla0SSectionRealizes.eval_point_vector_smooth_slots`.  It extends an
  arbitrary tangent vector to a smooth section and reuses
  `eval_smooth_slots`, so the scalar Lie-bracket derivative can be rewritten
  into a `nablaAlpha` first-slot term.
- Recut the final frontier at the intermediate equality `hExpanded`.  After
  that equality, the theorem now closes by `hcurvAction` and
  `htorsionFirstSlot`; this terminal curvature/torsion assembly checks.
- Verification passed with the same single intentional `sorry` warning.

Remaining frontier:

- The only remaining proof is the local expansion/cancellation inside
  `hExpanded`: normalize the two `Nabla20SRealizesAt` expansions, apply the
  scalar bracket commutator, use the new point-vector wrapper for the bracket
  derivative, cancel off-diagonal double updates, and combine the diagonal
  terms into `connectionRiemannCurvatureField`.

## 2026-05-13: HExpanded correction-sum split

Worked:

- Added scalar derivative linearity helpers for finite sums, negation, and
  subtraction of scalar functions.
- Added `update_finCons_zero`, `update_finCons_succ`,
  `sum_update_finCons`, and `sum_update_finCons_raw`.  The raw version is the
  useful one for this proof because the derivative values arrive as a function
  on `Fin (s + 1)`, not syntactically as a `Fin.cons`.
- Used those helpers inside `hExpanded` to split both second-derivative
  correction sums into the first-slot terms and the tail-slot sums.
- Removed an accidental unnecessary `[Zero V]` requirement from the
  `Fin.cons` update helper.

Failed:

- `hExpanded` is still not closed.  After the correction-sum split, the
  remaining blocker is derivative linearity for the two first-derivative
  scalar functions:
  `p ↦ nablaAlphaSec p (Fin.cons Ysec Vsec p)` and the swapped `Xsec` version.
- A local attempt to package the needed C1 tensor-evaluation differentiability
  helper hit the `Tensor0SModel` normed-space instance
  boundary in this file.  That helper was removed rather than adding a second
  frontier.

Next step:

- Put the C1 tensor-evaluation differentiability helper in the tensor/nabla
  regularity layer, where the tensor bundle topology and model-space instances
  are already local.  Then use it to justify `extDerivFun_sub_at` and
  `extDerivFun_finset_sum_at` for the two first-derivative scalar functions.

Verification passed for `RicciIdentity.lean` with the same single intentional
`sorry`.  The downstream Levi-Civita curvature check is blocked until the
`DifferentialGeometry.Tensor.RicciIdentity` olean is rebuilt.

## 2026-05-13: C1 helper consumed in hExpanded

Worked:

- Used the tensor/nabla C1 evaluation helper to prove the differentiability of
  the two scalar finite sums coming from the `hFY` and `hFX` rewrites.
- Differentiated those scalar equalities with `extDerivFun_sub_at` and
  `extDerivFun_finset_sum_at`.
- Added the scalar Lie-bracket commutator step and the point-vector
  `Nabla0SSectionRealizes` rewrite for the bracket derivative.
- Verification passed with the same single intentional `sorry` at `hExpanded`.

Failed:

- The final `hExpanded` proof is still not closed.  The remaining blocker is
  now only finite-index update normalization: Lean does not automatically
  identify `Fin.cons` tail-slot updates with the nested `Function.update`
  shape required by `double_update_sum_cancel_diag`.

Next step:

- Add a pure finite-index helper normalizing
  `Fin.cons head (Function.update tail q v)` to
  `Function.update (Fin.cons head tail) q.succ v`, then use it before
  applying `double_update_sum_cancel_diag`.

## 2026-05-13: Tensor0S Ricci identity closed

Worked:

- Closed the remaining `hExpanded` frontier in
  `tensor0S_commutator_expansion_from_realizes`.
- Added the symmetric `Fin.cons` tail-update normalizer and used it to cancel
  the first-slot tail correction sums.
- Normalized the two double-update sums into the exact shape of
  `double_update_sum_cancel_diag`, then combined the diagonal terms with
  `tensor0S_update_curvature_diag` and the definition of
  `connectionRiemannCurvatureField`.
- The public torsion, torsion-free, and Levi-Civita wrappers now consume the
  proved invariant `(0,s)` Ricci identity without a local frontier.

Verification passed:

- `RicciIdentity.lean` checks.
- The downstream Levi-Civita curvature file checks.
- The placeholder scan for `RicciIdentity.lean` is clean.

Lesson:

- The successful close was not another geometric bridge.  Once the C1 moving
  slot and scalar bracket pieces were available, the remaining work was purely
  finite-index normalization plus additive bookkeeping.

## 2026-05-13: Mixed component probe algebra

Worked:

- Added the pure finite-index algebra layer for deriving the mixed `(r,s)`
  Ricci-identity signs from the covariant `(0,n)` curvature action:
  `deltaMulti`, `contractUpper`, `covariantCurvAction`, and
  `contract_covariantCurvAction_deltaMulti_eq_mixedCurvAction`.
- The proof uses an elementary covariant probe in the upper slots.  The
  lower-slot term comes from the covariant identity for the contraction, and
  the upper-slot term appears with the opposite sign by subtracting the
  covariant identity for the probe.
- The key finite-sum step is a local involution on `(multiIndex, replacement)`
  pairs, sending `(A,m)` to `(A[p := m], A p)`.  This avoids metric lowering
  and avoids the false assumption that coordinate coframes are parallel.

Verification passed.

Next step:

- Add the geometric/component bridge that supplies the product rule for the
  upper-slot contraction, applies the already-proved `(0,s)` and `(0,r)`
  coordinate Ricci identities, and then invokes the pure probe algebra theorem.

## 2026-05-13: Mixed component contraction bridge

Worked:

- Added `mixedCurvAction` and `MixedRicciIdentityCoord`, the component-level
  statement of Remark 14.13 with positive upper-slot curvature terms and
  negative lower-slot curvature terms.
- Proved `mixedRicciIdentityCoord_of_contract_probe_identities`.  The theorem
  takes the contraction product rule as the only bridge hypothesis, then uses
  the covariant Ricci identities for the contracted tensor and the elementary
  probe to invoke the already-proved delta-probe algebra.
- The proof remains purely component-level; it does not import mixed tensor
  geometry, lower upper indices with the metric, or assume coordinate coframes
  are parallel.

Verification passed.

Next step:

- Prove the geometric contraction product rule that supplies the `hcontract`
  hypothesis from actual mixed tensor covariant derivatives.  That is the next
  genuine frontier before exposing a full coordinate `(r,s)` Ricci identity.

## 2026-05-13: Second-product contraction algebra

Worked:

- Added `contractUpper_commutator_of_second_product_rules`, a pure algebra
  theorem showing that the two second-product-rule expansions imply the
  commutator contraction rule
  `theta ⋅ commBeta = commContract - commTheta ⋅ beta`.
- Added `mixedRicciIdentityCoord_of_second_product_identities`, which packages
  that rule into the existing mixed Ricci bridge.  The covariant Ricci
  identities for the contracted tensor and the probe still supply the curvature
  signs through the delta-probe theorem.
- The theorem is still component-level.  It does not prove differentiability,
  Christoffel cancellation, or geometric contraction naturality.

Verification passed.

Next step:

- Prove the geometric second covariant derivative product rule for upper-slot
  contraction.  This is now the exposed frontier for turning the component
  bridge into a full coordinate `(r,s)` Ricci identity.

## 2026-05-14: Mixed component product-rule producer

Worked:

- Added `contractUpper_first_product_of_scalar_derivation`, the finite-sum
  Leibniz rule for an abstract scalar derivative acting on upper-slot
  contractions.
- Added `contractUpper_second_product_of_first_product_rules`, deriving the
  four-term second-product expansion from the two first-product pieces.
- Added `mixedRicciIdentityCoord_of_coordinate_second_product`, which feeds
  those first-product pieces into the existing mixed Ricci identity component
  algebra.

Verification passed.

Remaining frontier:

- The mixed `(r,s)` component identity now needs the geometric producer for the
  first-product pieces: evaluate a smooth `TensorRSField r s` on a moving
  smooth `Tensor0SField r`, then prove the coordinate derivative Leibniz rule
  for that contraction.
- The current search found tensoriality and contraction APIs, but not a
  bundled smooth field-level evaluation operation
  `TensorRSField r s × Tensor0SField r -> Tensor0SField s`.

Frontier assessment:

- This is a missing API/product-rule lemma, not a mathematical obstruction.  I
  expect it is solvable without user intervention, but it is a medium-sized
  tensor-bundle proof rather than a local ring/sum normalization.

## 2026-05-14: Mixed first-product local algebra and pointwise bridge

Worked:

- Added `contractUpper_components_eq_component_applyInput`, identifying the
  `contractUpper` notation with the pointwise component expansion of applying a
  mixed tensor to a covariant input.
- Added `contractUpper_first_product_of_local_rules`, the localized Leibniz
  algebra for one contraction component.  The older abstract derivation theorem
  now delegates to this smaller theorem, so future coordinate producers only
  need to supply the finite-sum and product rules for the specific scalar
  functions involved.
- Verification passed, including the targeted `RicciIdentity` build and the
  downstream Levi-Civita curvature check.

Remaining frontier:

- The geometric coordinate producer is still not closed.  The next lemma should
  prove that the scalar function underlying
  `coordDeriv0SAt X x0 (tensorRSField_applyInput T theta)` is locally the
  finite contraction of the local-frame components of `theta` and `T`, then
  differentiate that equality with the concrete coordinate derivative product
  rule.

Frontier assessment:

- This is missing coordinate/local-frame API, not a mathematical obstruction.
  Expected hardness is medium-high Lean plumbing.  I still expect it is solvable
  without user intervention, but it should be isolated in the coordinate
  component layer rather than pushed into the mixed Ricci algebra.

## 2026-05-14: Coordinate first-product bridge

Worked:

- Imported the coordinate mixed-component producer and added
  `coordDeriv_applyInput_eq_contractUpper`.
- This rewrites the raw coordinate derivative product rule for
  `tensorRSField_applyInput T theta` into the `contractUpper` shape used by the
  mixed Ricci identity component algebra.
- The targeted `RicciIdentity` build and downstream Levi-Civita curvature smoke
  check passed.

Remaining frontier:

- The full mixed `(r,s)` Ricci producer still needs the geometric setup for the
  elementary probe fields and second-product assembly.  The immediate proof
  frontier feeding this bridge is upstream in
  `Coordinates/NablaComponents/TensorRS.lean`:
  `constInChart_basisTensor0S_coordFrame`.

Frontier assessment:

- The remaining blocker is coordinate/local-frame normalization, not curvature
  signs, coframe parallelism, or mixed Ricci algebra.  I expect it is solvable
  without user intervention, but it belongs in the coordinate component layer
  before adding another mixed Ricci wrapper.

## 2026-05-14: Slot algebra extraction

Worked:

- Moved the private finite-slot update algebra into
  `DifferentialGeometry/Tensor/Auxiliary/SlotAlgebra.lean`.
- `RicciIdentity.lean` now imports the new auxiliary module and consumes the
  shared lemmas for double-update cancellation, `Fin.cons` update
  normalization, and `Fin (s+1)` sum splitting.
- Removed the duplicated private proofs from this file without changing the
  Ricci-identity theorem statements.

Verification passed.

Remaining:

- The next reusable layer should be a derivation-algebra theorem built on top
  of `SlotAlgebra`, not another local proof block in this file.

## 2026-05-14: Derivation algebra extraction

Worked:

- Moved the reusable upper-contraction product-rule algebra into
  `DifferentialGeometry/Tensor/Auxiliary/DerivationAlgebra.lean`.
- `RicciIdentity.lean` now keeps the curvature/probe algebra and coordinate
  producers, while importing the pure `contractUpper` layer.
- The extracted lemmas were generalized away from `Real` where the algebra
  allowed it.

Verification passed.

Remaining:

- The mixed coordinate producer is still blocked upstream by
  `constInChart_basisTensor0S_coordFrame`.

## 2026-05-14: Mixed component algebra split

Worked:

- Moved the whole `MixedComponentAlgebra` section into
  `Tensor/RicciIdentity/MixedComponents.lean`.
- `Tensor/RicciIdentity.lean` now imports that module and keeps the same public
  import surface for downstream files.
- This removed the component/probe mixed Ricci algebra from the main invariant
  Ricci-identity file without changing theorem endpoints.

Verification passed:

- The extracted mixed-component module checks.
- The old `Tensor/RicciIdentity.lean` import path checks and builds.
- Downstream focused checks for Levi-Civita curvature and curvature components
  passed.

Remaining:

- The main file is still long because it owns the one-form and invariant
  `(0,s)` Ricci identity interfaces and the section-level commutator proof.
  The next cleanup should extract scalar derivative helpers or the one-form
  interface only if that creates a genuinely reusable API.
