# Full AC59 and AC60: original pointed limits and calibrated coordinates

Two public theorems finish the original-input AC59 line construction and the
AC60 single-coordinate consumer of its actual outputs.

PointedGHConverges.exists_calibrated_lines_of_opposite_endpoints starts with the
specified proper pointed limit, the original short-curve characterization in
finite metric sources, and any finite family of opposite endpoint pairs. Positive
endpoint lengths may differ by family member; each tends to infinity. Each
actual ABSOLUTE excess 2L-d(aPlus,aMinus) tends to zero. Any positive curve-length
error sequence tending to zero may be supplied. No source completeness,
properness, minimizing geodesics or curvature is required.

The theorem selects actual closed-ball approximations from the convergence
hypothesis, constructs the actual signed almost-shortest prefixes, and composes
the approximation-selection and line-extraction subsequences. It returns ONE
strict source subsequence, convergence to the SAME original target on that
subsequence, actual radii/errors with their limits, actual approximation maps,
actual signed prefixes and their exact calibrations, and one whole isometric
line for each member. Every line passes through the original basepoint. Uniform
control on each bounded signed parameter interval is simultaneous over the
finite family and uses exactly those returned maps and prefixes. No varying
target, replacement endpoint, separate ball limit or per-member subsequence is
substituted. The empty indexing type is allowed; no line is then asserted.

The AC60 theorem consumes a supplied onto product isometry aligned with ONE of
these lines. It uses the actual 1-Lipschitz prefixes, their two relevant signed
calibrations and their actual same-map convergence to PRODUCE the calibration
witnesses required by the earlier two-sided squeeze. It yields, for every fixed
source radius and positive accuracy, eventual control at EVERY source point:

    |d(o_i,a_i)-d(x,a_i)-firstCoordinate(e(f_i(x)))| < accuracy.

The source domain contains the whole fixed ball eventually. The endpoint may
lie outside the approximation domain. This theorem needs no properness or
curvature beyond whatever produced its inputs. Its target basepoint may be
supplied separately from gamma(0), with their equality retained. Combined with
the existing quantitative product Busemann theorem, the first coordinate is
minus the positive-ray Busemann function, with the original endpoint orientation.
The aligned product is the stated AC60 assumption, not a hidden line-production
hypothesis or a claim of multi-axis orthogonality.

Source bodies checked: blueprint207A MC06 full1015-1033 and nearby restriction
proof, AC58 full5033-5085, AC59 full5089-5139, AC60 full5148-5205. Existing BBI
natural-parametrization, finite-family extraction and KL4.15 negative-Busemann
source/retained-errata checks are reused unchanged. The actual PointedGHConverges
15-33 body and Mathlib AtTopBot/Basic109-140 strict diagonal selection were read.
Source and subtype hypotheses are preserved through both selections. No fresh
remote errata clearance is claimed.

AC59 and AC60 are complete in their written finite-metric scopes, including
finite-family AC59 and the supplied aligned splitting in AC60. The compiled
integration checks the returned maps and lines in an actual incomplete-source
example, then obtains an actual geometric line splitting and applies AC60 to
those very objects. AC53 multi-axis alignment, AC57 absolute-excess production,
AC54/55 long-strainer splitting and AC62-80 orthogonality/compatibility work remain.
Earlier mathematical leaves, blueprint207 and migration interfaces are unchanged.
