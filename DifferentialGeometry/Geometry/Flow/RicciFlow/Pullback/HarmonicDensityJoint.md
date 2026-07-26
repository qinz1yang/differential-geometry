# HarmonicDensityJoint

## Purpose

This file develops the finite-spectral joint regularity needed by the
harmonic-map gauge construction.  The coefficient ball is uniform in the
spatial point.  The local-addition coordinate is nonlinear, so its faithful
mass pairs coefficient velocities only after applying the state derivative of
the exponential chart.

## Source-written declarations

- `hmfSpecDens_cd` states joint `C²` regularity of the finite-spectral
  Dirichlet density on a positive coefficient ball.  Its proof freezes a
  smooth orthonormal frame at the point under consideration and uses
  basis-independence of the bilinear trace to recover the moving-centre
  density.
- `hmfSpecCoeff_cd` states joint bundled `C²` regularity of the derivative in
  one fixed finite coefficient direction on a positive coefficient ball.  It
  differentiates the genuinely joint `C³` local-addition map in the
  coefficient slot, rather than treating the derivative as independent data.
- `hmfStateVar` and `hmfStateMass` record the corrected nonlinear state
  variation and mass.  The older `hmfMass` omits the state-dependent
  differential and is only the zero-state form.
- `hmfStateVar_zero` identifies the state derivative at the zero section with
  `hmfUnknown`.
- `hmfStateMass_zero_eq` identifies the corrected mass at the zero section
  with the older fixed-coordinate mass.

`HarmonicStateMass.lean` imports this file.  Its finite coefficient derivative
and finite faithful mass definitions are intended to consume
`hmfSpecCoeff_cd`, `hmfStateVar`, and the zero-state bridge.

## Mathematical route

The density proof first obtains the parameterised spatial manifold derivative
from `ContMDiffWithinAt.mfderivWithin`.  The moving-centre frame cannot be used
as a smooth field, so the proof replaces it locally by a frozen smooth frame
and applies the orthonormal-basis trace identity.

The coefficient-direction proof regards the local addition as a family of
maps from the finite Euclidean coefficient space.  At every point of the open
coefficient ball, ordinary `ContMDiffAt.mfderiv` supplies the jointly regular
coefficient differential, and the vector-bundle coordinate application API
packages its value on a fixed direction as a tangent-bundle section.

At zero state, `mfderiv_expMapIntrinsic_at_zero` gives the identity derivative
of the fibre exponential.  A one-dimensional chain rule then gives
`hmfStateVar_zero`.  The mass identity uses the canonical rank-zero lift,
`inner_toRS0`, and the coordinate formula for the cotangent metric.  A direct
claim that the old mass remains faithful away from zero was rejected because
it is mathematically false: the exponential-chart differential depends on the
state.

## Verification state

This is currently source-written and statically reviewed only.  No Lean check
or build was started because the shared workspace has a sole active Edge build
owned by another lane.  Consequently none of the declarations in this file is
yet claimed as verified.

The main elaboration risks to check once the shared build lane is released are:

- the coordinate conversion around the parameterised spatial derivative in
  `hmfSpecPush_cd`;
- the frozen-frame local eventual-equality rewrite in `hmfSpecDens_cd`;
- reducible model-space identifications and the final bundle-function
  conversion in `hmfSpecCoeff_cd`;
- definitional alignment between the local metric instances used by
  `hmfDiagExp` and those needed by `mfderiv_expMapIntrinsic_at_zero`;
- the rank-zero `TensorRSSpace` extensionality and the rank-one cotangent
  coordinate calculation in the zero-mass bridge.

Static review found no placeholder declaration in the Lean source, and the
file remains below the 3000-line hand-maintained-file limit.  The exact endpoint
theorems `ricci_flow_unif_existence` and `ricci_flow_forward_unique` remain at
theorem-level 0% until their existing statements are proved and verified; this
file is only Phase B machinery.  The next step for this file is a focused
lock-aware check after the active shared build finishes, followed by repair of
the first concrete elaboration error rather than a broad build.
