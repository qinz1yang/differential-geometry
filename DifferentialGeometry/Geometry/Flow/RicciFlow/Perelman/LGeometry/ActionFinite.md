# ActionFinite

## Role

`lChartH1_fin` is the L-specific finite compactness brick. From one global
upper bound for the regularized L-action, it produces one common subsequence
for all local chart-`timeH1` representatives in a finite monotone subdivision.
The result gives weak convergence of every local derivative and uniform
convergence of every local continuous representative.

`lSegLen t i = t i.succ - t i.castSucc` is the shared dependent interval
length used by the theorem's local `timeH1` and `timeL2` types. Writing the
endpoint difference independently at every dependent occurrence caused
definitional-equality elaboration to exceed even an enlarged heartbeat budget;
the named length keeps the public mathematics unchanged and checks under the
default budget.

## Internal production

The theorem derives rather than requests the following data:

- almost-everywhere manifold differentiability on each shifted local interval,
  obtained from the global `ContMDiffOn` hypothesis away from the measure-zero
  interval endpoints;
- continuity and integrability of the scalar term and its compact-spacetime
  lower bound;
- global kinetic integrability and the exact action split;
- a global kinetic upper bound, followed by each local kinetic upper bound via
  nonnegativity and interval restriction;
- the exact fixed-chart quadratic identity from `lKinetic_local`.

The resulting finite family is passed to `chartH1_fin`. No local action bound,
local integrability, differentiability, scalar lower constant, norm bound,
coercivity constant, or measurability premise appears in the public API.

`exists_chartH1_fin` realizes the local data consumed by `lChartH1_fin` from a
uniformly convergent sequence of global `C¹` curves. Uniform convergence is
restricted to each closed subdivision piece; `mapsTo_eventually` and finite
`eventually_all` produce one tail index valid for every chart. The coordinate
compacta are the images `extChartAt I (p i) '' Kman i`, and the local paths are
the canonical shifted `chartTimeH1` representatives, so their source, toFun,
and compact-containment properties match `lChartH1_fin` exactly.

The realization theorem uses the standard boundaryless-model instance. This
is necessary for the stated input `Kman i ⊆ chart source` to imply that its
coordinate image lies in the ambient interior of the extended-chart target.
For a general manifold-with-boundary model that implication is false; the
alternative honest API would have to assume coordinate-interior containment
directly.

## Verification and progress

Focused verification passed without warnings. The file contains no `sorry`,
`admit`, or axiomatic placeholder.

These theorems provide the finite-subdivision realization and compactness
producers. The
minimizer endpoint `exists_lMinimizer` remains unstated and therefore 0%, and
`redVolume_anti` remains 0%. The dedicated direct-method machinery is now about
85% complete; the generic compactness and moving-Gram infrastructure consumed
here is complete for this stage.
