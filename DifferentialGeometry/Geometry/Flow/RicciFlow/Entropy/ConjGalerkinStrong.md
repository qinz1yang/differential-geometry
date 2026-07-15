# ConjGalerkinStrong

## Role

This file turns the all-order spectral subsequential limit from
`ConjGalerkinLimit.lean` into a genuine `H¹_t H⁰_x` object while retaining the
explicit `H² → H⁰` companion path.  It is the intrinsic strong-limit producer;
it does not yet assert joint spacetime smoothness or `IsHeatPotOn`.

## Route

The proof first extends each compact-interval Sobolev path continuously, defines
the limiting `H⁰` velocity from the frozen scalar Laplacian and the moving
perturbation, and passes each finite coordinate ODE to the limit by the
right-sided FTC and dominated convergence.  The mode identities are assembled
with `coeffCLM` into an `H⁰` Bochner integral identity, then packaged by
`timeH1.mk` with the exact initial trace and derivative representative.

No consumer hypothesis, convergence predicate, locally constant chart choice,
or tensor-representation unfolding is added.  Continuity of the perturbation is
producer data already obtained while constructing `scalar_gal_subseq`.

## Verification and frontier

The source implementation currently contains `galLim_mode_ftc`, `galLim_ftc`,
and `scalar_gal_limit`.  Focused verification is pending the refresh of the
exported upstream declarations used by this new file.  Static review finds no
`sorry`, and the modewise DCT, compact maximum, right-sided FTC, coefficient
integral commutation, and `timeH1` APIs all match their live signatures.  One
nested-filter tactic mismatch found during review has already been repaired.

Even after this theorem verifies, the classical moving conjugate-heat theorem
remains a separate theorem-level frontier: the all-order spectral strong path
must still be realized as a jointly spacetime-smooth pointwise heat potential.
Perelman no-local-collapsing and `ham3_noncollapse` also remain endpoint-level
frontiers rather than consequences of this packaging step alone.
