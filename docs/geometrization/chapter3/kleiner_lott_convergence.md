# The full eventual KL convergence criterion: MC11

The precise equivalence in `PointedGHConverges.iff_exists_kleinerLott_sequence`
requires a complete target and asserts:

- closed-ball pointed convergence, with every radius and error allowed;
- iff there is a real sequence δ(n) with 0<δ(n)<1 for every n, δ(n)→0,
  and KL δ(n)-approximations on a tail of source indices.

The maps themselves are required only eventually. No assertion about a
possibly bad finite prefix is introduced. The sequence δ is harmlessly
chosen positive and below1 on that prefix. Nonempty existence of the
approximation data is equivalent to selecting the maps by classical choice.

The forward proof first converts each fixed admissible δ, then uses
`Filter.exists_tendsto_atTop_eventually_diagonal` to allow the accuracy level
to grow slowly with n. This generic lemma proves, for predicates P(k,n) with
each fixed k eventually true, that some j(n)→∞ makes P(j(n),n) eventually
true. It uses finite greatest admissible indices, without assuming any
monotonicity of P. This differs from selecting a subsequence of source indices:
the final maps exist for every sufficiently large original index.

The reverse proof simultaneously ensures 3δ(n)<ε and R<1/δ(n), obtains
a radius-R approximation with error3δ(n), then enlarges its error toε.

Source/proof locator: master207A.tex, `prop:metric-conventions`, lines
1130–1192. Exact KL definitions and source/version/errata checks are in
kleiner_lott_approximations.md. The finite-greatest-index argument is the
blueprint's written diagonal proof, expressed using standard Filter and
Nat.findGreatest APIs. The compiled statements retain target completeness.
