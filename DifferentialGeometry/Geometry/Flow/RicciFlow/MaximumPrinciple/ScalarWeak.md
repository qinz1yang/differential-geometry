# Scalar weak maximum principle notes

## 2026-07-09: linear reaction nonnegativity

- `linear_react_nonneg` now closes the negative-region calculation from the
  genuine equation `P u = beta * u` and a uniform upper bound `beta <= C`.
  The earlier book-facing wrapper still accepts that calculation as an input.
- The proof uses the existing exponential rescaling identity.  On the negative
  set, `(beta - C) * u` is nonnegative because both factors are nonpositive.
- The zero-length interval is discharged directly from the initial condition;
  the positive-length case uses uniqueness of derivatives on the closed time
  interval.
- Focused verification passed without `sorry` or warnings.

This completes the generic linear-reaction WMP calculation needed by the
time-reversed conjugate heat equation.  It does not construct a heat solution.
Perelman no-local-collapsing remains 0%; its dedicated analytic machinery is
about 15%, while the whole HCG machinery remains about 45% and its endpoint
theorems remain 0%.

## 2026-07-22: parabolic product rule

- Added `parabolic_mul` for the drifted operator
  `partial_t - Delta - <X, grad>`.  It reuses the realized heat product rule
  and the one-variable `derivWithin` product rule.
- The conclusion retains the negative gradient cross term with the sign needed
  by cutoff localization.
- Focused verification passed without new warnings.

This closes only the generic calculus seam used by localized Bernstein
arguments.  It does not supply the compactly supported parabolic cutoffs or
the localized maximum argument.  The corrected complete-Bernstein theorem is
still theorem-level 0%; its dedicated localization machinery is about
35--40%.  The unconditional HCG compactness theorem remains theorem-level 0%,
with whole-project support machinery about 60%.

## 2026-07-22: compact-support maximum principle

- Added `strict_barrier_cpt`, the positive-time strict-barrier weak maximum
  principle when the possible negative region is contained in one fixed
  compact spatial set across the whole closed time slab.
- The proof minimizes only on `Set.Icc 0 T ×ˢ K`.  At a spatial point outside
  `K`, the exterior hypothesis makes the function nonnegative, so a negative
  compact minimizer is still a genuine global spatial minimum.
- The theorem removes `[CompactSpace M]`; it does not replace it with a
  slicewise compactness hypothesis.  The same compact `K` must contain every
  negative point at every time, which is the form required by the corrected
  affine-barrier cutoff architecture.
- Focused verification passed without warnings or new `sorry`s.

This closes the maximum-principle consumer for a supplied localization whose
negative region is uniformly compact.  It does not construct the quantitative complete-flow
cutoff family.  The complete noncompact Bernstein theorem itself remains 0%;
its dedicated localization machinery is now about 40--45%.  The public trusted
complete Shi theorem and unconditional HCG endpoint remain theorem-level 0%.

## 2026-07-22: additive and finite-sum parabolic rules

- Added `parabolic_add` and `parabolic_smul` for addition and multiplication by
  a fixed real scalar.
- Added `parabolic_sum`, which commutes the drifted parabolic operator through
  a finite family under explicit per-summand time, spatial, and gradient-section
  regularity.
- The finite-sum proof derives the regularity of the summed gradient section;
  it does not hide that obligation in a Bernstein-specific assumption.
- Focused verification passed without local warnings.

This finite-sum calculus brick is complete (100%) and is ready for the graded
cutoff Bernstein sum with its fixed coefficients.  The complete noncompact
Bernstein theorem itself remains theorem-level 0%; its dedicated localization
machinery is about 45--50%.  The unconditional HCG endpoint remains
theorem-level 0%, with whole-project support machinery about 60%.

## 2026-07-23: parabolic chain rule

Added `parabolic_comp` for `P = ∂t - Δ - <X, ∇·>`:

`P (φ ∘ u) = φ'(u) P u - φ''(u) |∇u|²`.

The time term uses Mathlib's `derivWithin_comp`; this already handles a
non-unique closed time domain, so no artificial `UniqueDiffWithinAt` hypothesis
is required.  The spatial term is the checked `heatDrift_comp`.

Focused verification passed with no diagnostics.  The named theorem is complete
(100%).  Together with the lower scalar cutoff profile it closes the
route-neutral composition calculus, but it does not construct a smooth
parabolic exhaustion or a Calabi barrier.  Consequently the solution-generated
`ShiCutoffData` and corrected complete-noncompact Shi theorem remain
theorem-level 0%.

## 2026-07-23: local upper-support compact maximum principle

- Added `ParabolicUpperSupportAt`, carrying one smooth spacetime upper support
  and the parabolic inequality only at the selected contact point.
- Added `strict_barrier_cpt_of_upperSupport`.  Its compact-cylinder minimizer
  is global because the function is nonnegative outside the supplied compact
  set, but differentiability is requested only from the local upper support at
  a possible negative minimizer.
- The consultation displayed the support structure as `Prop`.  Lean correctly
  rejects that form because the structure contains the data field `v`; the
  checked interface is therefore a data structure in `Type`.  The redundant
  pointwise spatial differentiability field was also omitted, since it follows
  from the neighborhood field.
- The private one-sided time derivative helper was weakened from a global
  `IsMinOn` hypothesis to the exact `IsLocalMinOn` hypothesis used by both the
  old smooth theorem and the new support theorem.
- Focused and exact targeted verification passed with no local diagnostics.

This theorem is complete (100%).  It closes only the maximum-principle brick of
the selected Route B-prime complete-Bernstein architecture; the
solution-generated barrier cutoff and the complete Shi theorem are still
unstated/unproved (0%).  Dedicated Route B-prime machinery is about 10--15%,
the unconditional HCG endpoint remains theorem-level 0%, and whole-project HCG
supporting machinery remains about 60%.

## 2026-07-24: neighborhood parabolic composition

Added `parabolic_comp_nhds`, the local chain rule for the parabolic operator at
one spacetime point.  Its spatial hypotheses are neighborhood-local and its
time hypothesis is relative to the closed slab, matching the selected Calabi
support rather than assuming a globally smooth exhaustion.

Focused and exact verification are current with no local diagnostics.  This
composition theorem and its dedicated machinery are 100%.  The concrete
barrier cutoff and complete-Shi assembly remain separate producer endpoints.
