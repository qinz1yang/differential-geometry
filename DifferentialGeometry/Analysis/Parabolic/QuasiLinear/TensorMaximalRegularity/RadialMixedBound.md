# RadialMixedBound

## 2026-07-19

`norm_map_ball_le` records that a continuous linear lower-order view cannot
grow under radial retraction.  `radial_mixed` packages the full two-scale
algebra for composing a mixed nonlinear estimate with a high/low bounded
symmetry map and radial retraction.

For high and low symmetry constants `cH,cL`, radius `R`, and original mixed
constants `A,B`, the transferred constants are

- high: `A*cL*cH + B*(1/R)*cL*cH`;
- low: `B*cL`.

The `R⁻¹` term is exactly the derivative of the radial scaling factor.  This
lemma removes a long duplicated algebraic block from the intended
dimension-three Ricci--DeTurck dense extension.  Focused verification is
pending until the shared long-path `.olean` rebuild finishes; no analytic
endpoint is claimed here.

**2026-07-25 REAL BUILD VERDICT: GREEN.** Authoritative
`lake build +…RadialMixedBound` passed (olean produced); `norm_map_ball_le`
and `radial_mixed` are verified and consumable.
