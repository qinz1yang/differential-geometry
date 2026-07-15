# Dirichlet spectral Bochner gap

## 2026-07-14 rank-generic producer

The existing coefficient-one gap was restricted to `(0,2)` tensors.  The live
lower layers are now rank-generic: the Green identity, curvature commutator
bounds, iterated rough-Laplacian bounds, `ccTensorToHs`, and `hsJet_le` all
accept an arbitrary covariant rank.  The source therefore now states
`cc_dirichlet_gap g₀ s n` with no new assumptions.  The old long rank-two
theorem is retained as a compatibility specialization.

The proof keeps the sharp coefficient one by the same genuine Bochner route as
the rank-two theorem.  It compares the top covariant derivative with the
spectral mode mass, controls only commutator terms by the lower spectral norm,
and finally uses `λ^(n+1) ≤ (1+λ)^(n+1)`.  A generic local coefficient recursion
through `rawLap_coeff` replaces the older exported coefficient lemma, which is
rank-two-specific despite the underlying resolvent API being generic.

The required upstream artifact was refreshed and the complete file now passes
focused verification without warnings.  Two elaboration-fragile inequalities
were normalized with explicit `lambda ≤ 1 + lambda`, coefficient rewrites, and
associativity instead of leaving metavariables to `linarith`/`positivity`.
There is no remaining mathematical assumption or generic Bochner API frontier
in this producer.

Honest accounting: `cc_dirichlet_gap` is complete (100%).  The consumer theorem
`scalar_crit_tame` remains unstated/unproved (0%); its dedicated machinery is
roughly 80%, with the finite spectral pairing and compact-slab coefficient
uniformization still being assembled.
Perelman no-local-collapsing and `ham3_noncollapse` remain theorem-level 0%;
their dedicated analytic machinery is roughly 40%.  Whole HCG machinery is
roughly 53%, while its endpoint theorems remain 0%.
