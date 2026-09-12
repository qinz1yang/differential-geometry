# Positive linear homotopy

`positive_linear_homotopy` uses an actual `OrthonormalBasis (Fin 3) ℝ E`, an
actual continuous linear equivalence `L`, and `0 < LinearMap.det L.toLinearMap`.
Gram--Schmidt gives a positive triangular interpolation from `L` to its basis
isometry; orientation equality makes that isometry positive. Reflection
generation in dimension three reduces it to zero or two nonzero reflections,
whose normals are joined in the punctured vector space. Concatenation preserves
every nonzero vector.

The first focused check (17 seconds) accepted all helper proofs; the final
concatenation branch needed its time inferred from the actual zero equality.
That branch is repaired. The second check showed the public proof still needs
its original `FiniteDimensional` instance; restored it (the earlier unused-variable
warning came from an unsuccessful elaboration). Awaiting a third check. All helper declarations
are private; no explicit proof debts, axioms, or resource-limit overrides.
The saved candidates remain unchanged. The filter repair specifies the exact
Boolean predicate before rewriting, and the triangular basis bridge uses
`repr_self` after applying the actual inverse isometry. Final acceptance still
requires the saved-file focused check and endpoint axiom audit in an allocated
verification window. Claim token: `9499fb5d-29e4-42a9-99bb-d4f9c4e7bfd7`.

## Root handoff checkpoint — 2026-09-09

Exact source SHA256: `2B0C1C74D3F41EB094B5531DA5C0138A9B08E0CC20A2301BD01B1641481F70EB`.
The independent THIRD focused check passed in 16.1 seconds with empty Lean
diagnostics. The named lint/artifact build passed (2397 jobs, target 14 seconds),
without warnings. Receipts are preserved in `Handoff/Evidence/`.
This supersedes the pending-third-check wording above. The endpoint has NOT
received its separate `#print axioms` audit, and the new leaf is not registered
or committed. No original Homology proof debt has been removed by this result.
The user stopped proof work before the next candidate check; the ordinary file
claim was released. Continue only under the receiving collaborator's assignment.
