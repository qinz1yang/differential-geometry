# ParametricScalarSmulJet

## Route

The scalar multiplier is represented by the rank-zero mixed coefficient
obtained by scaling the canonical rank-zero identity. Its `appCc` action is
proved equal to `scalarSmul` after full application. This lets
`smul_jet_unif` reuse `param_app_jet`, avoiding a second iterated Leibniz
calculus.

The spacetime smoothness proof cannot use ordinary `smul_section`: the family
covers `Prod.fst : M × ℝ → M`, not the identity map.  The private
`joint_rs_smul` helper instead opens the total-space smoothness criterion and
performs scalar multiplication only in a local trivialization.  This is the
same established normal form used by existing joint tensor-family producers.

## Frontier

The source theorem is stated and proved without solution-specific assumptions.
The missing namespace opening for `iteratedCovGrad` was repaired, and the
private helpers now explicitly omit unused ambient instances.  The global
heartbeat overrides were unnecessary and have been removed.  Focused
verification passes without warnings.

`smul_jet_unif`: theorem and its dedicated scalar-multiplier machinery are
100% verified.  This is one producer in the larger A1/Galerkin chain; it does
not by itself prove the conjugate-heat or noncollapsing endpoints.

## 2026-07-16 public rank-zero bridge

`scalarCc`, `app_scalarCc`, and `scalarCc_joint` are now public producer
APIs. They expose the rank-zero coefficient and its jointly smooth family only
in the fully applied normal form needed by `ScalarPotentialTime`; no whole-Hom
model equality is introduced. Focused and targeted verification are green, so
this API and its dedicated machinery are **100%**.

`scalar0_smul_cc` now records the matching pointwise scalar readout for an
arbitrary smooth rank-zero input.  Its proof unfolds the multiplier only after
the goal is scalar-valued, so it needs no extra boundary, positive-dimension,
or chart assumption.  Focused verification passes.  This closes the final
scalar normalization used by the Galerkin pointwise PDE assembly; it is
machinery and does not by itself complete the classical heat-potential theorem.

## 2026-07-16 normalized positive initial tensor

`scalar0_scalarCc` identifies the scalar readout of `scalarCc` with its bundled
smooth scalar function.  The proof stays fully applied and reuses the existing
rank-zero evaluation lemma; it does not assert equality of whole Hom models.

`unit_init_or_empty` now constructs the constant positive rank-zero tensor
whose value is the inverse total Riemannian volume.  On a nonempty compact
manifold, open positivity and finiteness of the Riemannian volume give a
strictly positive finite normalization constant, and the constant-integral
formula gives mass exactly one.  The empty-manifold case remains an explicit
disjunct: an unconditional unit-mass existence theorem would be false there.
No `Nonempty`, boundaryless, or positive-dimension assumption was added.

Focused verification passes without warnings, and the targeted module refresh
passes.  Both new producer theorems and their dedicated initial-data machinery
are **100%**.  They do not prove moving-mass conservation or a normalized
conjugate-heat endpoint; any such unstated downstream theorem remains **0%**.
Perelman no-local-collapsing likewise remains theorem-level **0%**, and the
broader entropy/noncollapsing and HCG machinery estimates are unchanged.
