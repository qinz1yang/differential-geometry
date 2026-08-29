# RayGlobalize

## Status

Focused verification passed without warnings or placeholders.

## API

- `lRegCurve_isReg` packages the totalized maximal ray as an
  `IsLRegCurveOn` object on every positive compact segment contained in its
  domain.  It uses chosen-solution germ equality rather than unfolding the
  bundle-valued ODE data.
- `exists_lReg_clamp` starts from `0 < b` and
  `b ∈ lRegDomain S T x Z`.  It uses compactness of `[0,b]` inside the open
  maximal domain to choose one positive two-sided buffer, then returns a global
  `C∞` scalar clamp.  The clamp is the identity, with derivative one, on
  `[0,b]`, and its whole range stays in `lRegDomain S T x Z`.
- `exists_lRay_smooth` composes that clamp with `lRegJacobi_smooth`.  It returns
  a globally `C∞` tangent-bundle section whose base is the clamped
  `lRegCurve` and whose fiber is the clamped canonical `lRegJacobiField`; the
  total section agrees exactly with the unclamped ray and Jacobi field on
  `[0,b]`.
- `exists_lReg_germ` strengthens the scalar clamp by making it the identity on
  a strictly larger interval `[a,d]`, where `a < 0` and `b < d`, while keeping
  its entire range in the maximal domain.
- `exists_lReg_germ_in` additionally keeps the clamp inside any supplied open
  neighborhood of `[0,b]`.  The original theorem is now its `univ` wrapper.
- `exists_lRay_germ` globalizes the curve/Jacobi pair using that stronger
  clamp.  The global total-space section therefore agrees with the original
  pair on a neighborhood of every point of `[0,b]`, including both endpoints.
- `exists_lRay_germ_in` is the corresponding curve/Jacobi producer with the
  extra open-neighborhood range control; it is the interface needed to
  globalize locally smooth comparison fields without asking them to be smooth
  on the nonsmooth totalization outside the maximal ray domain.

## Design notes

The proof uses the existing maximal-domain openness and segment theorem,
`exists_smooth_time_clamp`, and the joint total-space Jacobi smoothness theorem.
It does not unfold tangent bundles, introduce a new path or flow object, or add
completeness assumptions.  This globalization producer is consumed by the now
complete `lIndex_neg_conj` and `lMinVec_nconj_lt`; it is not itself either
endpoint.

The neighborhood form is needed for stable germ transport of velocities,
covariant derivatives, and index densities at the two endpoints; equality only
on the closed segment is not enough for those two-sided derivatives.

Project accounting remains separate: `redVolume_anti` is 0%; the dedicated
compact ordinary-flow L-geometry machinery is about 92%; generic reused
smooth-clamp and joint-smoothness infrastructure is complete for this producer.
