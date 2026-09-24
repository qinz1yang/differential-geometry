# Section 32: finite-window returning-annulus elimination

Base: `a8dda0594` (the registered 96-brick integration commit).
Status: this Type 2 stage is accepted; `exists_descentSequence` remains open.

Endpoints:
- `IsCanonicalAnnularWindow.exists_returning_component_deletion`
- `IsCanonicalAnnularWindow.exists_window_returning_reduction`

The single step constructs the actual component complement and both complementary
marked even-torus annuli. `IsReturningAnnulusDeletion` is the probe Type 2 certificate
with only its name changed. Deletion removes precisely the intrinsic annulus interior
from the full separator, retaining its end circles on the even torus.

The finite-window producer uses strict descent of `windowComponentRank` and returns
the real finite deletion history, source and target annular windows, literal unchanged
rows, exact surviving-component label embeddings, trace and boundary inclusions,
null-rank monotonicity, protected-set equality, and the absence of returning components.
All end labels, essentiality, generators and reference subsurface models survive.

Audit: 43 nonautomatic declarations in five new Lean modules; transitive axioms are
within `propext` / `Classical.choice` / `Quot.sound`; all thirteen environment linters pass.
All five modules were freshly elaborated with the brief's exact flags: zero diagnostics.
Receipts, source SHA-256 values, audit driver and axiom report:
`COLLABORATOR-section32-returning-receipts.json`.

Recursive source inspection found no Skeleton dependency. No named input was added.
The frozen Section 32 source, root aggregate and FREE_INPUTS are byte-identical to base.
Root registration is reserved for the integration lead, as required by the brief.

Remaining: a same-component mixed-end witness and its history transport; Type 3 and
half selection; guarded recursion, annular-chain fields and the frozen descent leaf.
Returning-free classification alone is not a bridge-nonemptiness theorem.
