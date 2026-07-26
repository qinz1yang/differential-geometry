# LowRegBootstrapOne status

## Endpoint accounting

- `ricci_flow_unif_existence`: 0%. Its exact Lean theorem is not yet proved.
- Low-regularity Phase N machinery: about 70%. The mixed `H3 -> H1`
  nonlinearity and forcing-space solver are assembled; this file supplies the
  first same-horizon trace bootstrap, but the spatial parabolic bootstrap to a
  smooth solution is still missing.
- `extends_of_rmBounded`: still depends directly on the unproved endpoint.

## Source added here

`LowRegBootstrapOne.lean` packages an affine maximal-regularity Duhamel solution
as a `CrossScaleField`.  Its intended exported facts are:

- `crossRepr_toFun`: the Lions--Magenes `H^(a+1)` representative includes to
  the `H^a` carrier for every `t` in the original `Icc 0 T`;
- `crossRepr_hi_ae`: it equals the `H^(a+1)` inclusion of the `L2_t H^(a+2)`
  companion almost everywhere;
- `crossRepr_ball`: an a.e. `H^(a+1)` ball bound becomes an every-time bound,
  using continuity of the squared intermediate norm;
- `duhRepr_toFun`, `duhRepr_field_ae`, and `duhRepr_ball`: direct Duhamel and
  order-one Ricci--DeTurck specializations.

All conclusions retain the solver's original `T`; no `d <= T` is introduced.
At the time of this note these declarations are source-complete but have not
yet had a focused Lean check because the shared workspace's named Lean build is
still reserved by another lane.

## Three audited bootstrap routes

### 1. Re-run maximal regularity at `a = 2`

The order-two affine map requires initial data in `H4` and forcing in
`timeL2 H2`.  The zero initial perturbation is available in every order, but
the current fixed point only supplies

`gforce : timeL2 H1`

and `lowRegN` is a static map `H3 -> H1`.  A generic static `H3 -> H2` estimate
is false for the quasilinear second-order arm.  The exact missing input for
this route is an `H2` forcing lift obtained from the equation's parabolic
structure, not from a stronger restatement of `lowRegN`.

### 2. Pure spectral Duhamel smoothing

`duhamel_into_all_tensorHs` assumes, for every `c >= 0`, summability of

`weight(c) * integral_0^t |forcing_mode|^2`.

The order-one solver provides this mass only at `c = 1`.  The homogeneous heat
theorem `heat_semigroup_into_all_tensorHs` smooths the initial term, but the
initial perturbation here is already zero and it does not improve the
inhomogeneous forcing.  Generic `L2_t H1` forcing gives the sharp
`L2_t H3` maximal-regularity field; it does not give `L2_t H4`.  Thus this route
cannot produce the required next spatial order without new nonlinear input.

### 3. Differentiate/bootstrap the geometric PDE

The existing finite-order and all-order forcing regularity ladders start from
high base order.  In dimension three their visible hypotheses are
`2 * dim + 10 <= a` (hence `16 <= a`) and, for the later all-order ladder,
`4 * dim + 10 <= a` (hence `22 <= a`).  They also return an existential
positive `d <= T`.  They therefore neither accept the live `a = 1` solution nor
preserve its already fixed uniform horizon.

The smallest faithful next producer is a low-base, same-horizon parabolic
regularity step for the concrete Ricci--DeTurck equation: from the order-one
Duhamel identity, the continuous `H2` representative supplied here, and the
`L2_t H3` field, construct an `H2` lift of the nonlinear forcing (equivalently
an order-two maximal-regularity solution) on the same preselected `T`.  This
must use the variable-coefficient/quasilinear equation; a generic semigroup or
Nemytskii lemma cannot supply it.

