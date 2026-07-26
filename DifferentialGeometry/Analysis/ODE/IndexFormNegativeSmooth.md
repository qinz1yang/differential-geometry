# IndexFormNegativeSmooth

## 2026-07-24 arbitrary terminal time

The source now has the canonical arbitrary-terminal-time facade
`IsJacobiSolOn.exists_smooth_neg_on`. It consumes the endpoint-aware split
producer on `[0, L]`; the previous `exists_smooth_neg` theorem is retained as
the literal `L = 1` compatibility wrapper.

The quantitative smoothing argument is not duplicated. A private positive
time-dilation identity transports the split index form to the already checked
unit-interval smoothing capstone, and the resulting smooth field is pulled
back to `[0, L]`. Positivity of the dilation preserves strict negativity.

The new dilation and smoothing helpers and the final
`IsJacobiSolOn.exists_smooth_neg_on` assembly pass focused verification without
diagnostics after refreshing the direct `IndexFormNegative` dependency.  The
arbitrary-length theorem and its dedicated smoothing machinery are both 100%;
only the module artifact refresh remains before downstream consumers can use
the export.

Project accounting: the minimizing-geodesic no-conjugacy endpoint remains 0%
until its own focused verification, and the Calabi support theorem remains a
separate 0% downstream theorem.

## 2026-07-23

Architecture ruling: use an explicit quantitative `H¹`-type smoothing in the
fixed Hilbert space of the abstract Jacobi ODE.  Do not add derivative
matching, global smoothness of the input half-fields, or abstract index-form
continuity assumptions.

The construction is complete.  Its first hard gate, `exists_deriv_bound`,
expands the derivative of the `CutoffProfile.value` splice.  Value matching at
the junction makes the `1 / δ` transition derivative multiply an `O(δ)` field
difference, so the resulting derivative bound is independent of `δ`.

The private `exists_splice_error` then splits the index form into left,
central, and right intervals.  The tails agree almost everywhere with the
input half-fields, and the three central terms have lengths `2 * δ`, `δ`, and
`δ`.  This gives an explicit `C * δ` error bound without an abstract
index-form continuity assumption.

The public theorem `exists_smooth_indexForm_neg_of_split` is proved.  It first
uses a compact plateau to extend each locally smooth half-field globally
without changing its value or derivative on `[0, 1]`, and then chooses `δ`
small enough that the smoothed field still has negative index.  Its statement
has no derivative-matching, `CompleteSpace`, self-adjointness, Jacobi, or
global input-smoothness hypothesis.

Focused verification and the targeted module build passed; the file is
warning-free and contains no `sorry`.

The umbrella import was added to `DifferentialGeometry.lean`.  Its focused
root check could not reach the new import because the unrelated
`Evolution/BBSLimitProducer.olean` artifact is currently absent.  A broad
refresh was not started while other shared lanes are active.

One reusable lesson is that the older `intInt_indexIntegrand` declaration
carries an unnecessary `CompleteSpace F` parameter from its source section.
This module avoids propagating that assumption by proving scalar integrability
directly from continuity of the index integrand.

This finishes the abstract fixed-Hilbert smoothing bridge, not the geometric
N-d endpoint.  The remaining frontier is to lift the smooth coefficient field
through the parallel orthonormal frame, prove perpendicularity and equality
with the geometric index form, and feed it to the minimizing-geodesic
nonnegativity theorem.

## 2026-07-24 closed-interval facade

The public theorem `IsJacobiSolOn.exists_smooth_neg` now composes the negative
split and quantitative smoothing results for the geometric use case where the
Jacobi ODE is available only on `[0, 1]`, but the position coefficient field is
globally smooth.  It takes the closed-interval solution, continuity and
self-adjointness of the coefficient operator, global smoothness of `y`, and
the exact identity `deriv y = v` on `[0, 1]`; it returns one globally smooth
endpoint-vanishing field with strictly negative index.

This avoids the mathematically false strengthening that a cut-off parallel
frame remain parallel on an open interval beyond both endpoints.  Focused
verification passes without warnings.  The theorem is an abstract ODE
composition result, not the geometric no-conjugate endpoint.
