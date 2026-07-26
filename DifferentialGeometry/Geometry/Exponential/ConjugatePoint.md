# ConjugatePoint.lean

## 2026-07-19 created (option-1 lane, brick N-a + N-b; interface RULED by user)

The conjugate-point interface, in the form the user ruled ("differential def
+ bridge"): definition = differential-singularity of the intrinsic
exponential; Jacobi phrasing = bridge theorem.  All green, build-verified,
no `sorry`:

- `IsConjVec g hEnorm p x` — the vector-slot differential of
  `expMapIntrinsic g hEnorm p` at `x` is not injective.
- `isConjVec_iff` — ⟺ a nonzero kernel vector.  (Manual injectivity/kernel
  equivalence; `map_sub` as a `rw` pattern FAILS here — the goal's `a - b`
  and `map_sub`'s elaborate through different-but-defeq `Sub` instance paths
  (`TangentSpace 𝓘(ℝ,E) x` vs `E`); term-mode `calc … := map_sub f a b`
  unifies fine.  Also: `push_neg` is deprecated in this pin — use
  `push Not`.)
- `isConjVec_iff_jacobi` — ⟺ some variation Jacobi field with `w ≠ 0`
  vanishes at `t = 1` (bridge through `intrinsic_jacobi_one`; the `rw` needs
  a trailing explicit `rfl`).
- `jacobiVar_zero` — the variation field vanishes at `t = 0`
  (`intrinsicGeodesic_zero` + `mfderiv_const`), giving the classical
  "nontrivial Jacobi field vanishing at both ends" phrasing.

No smallness/injectivity-radius hypothesis anywhere — meaningful at every
scale via `intrinsicExp_smooth`.

## 2026-07-24 component-local signature cleanup

The stale `ConnectedSpace M` binder was removed from `IsConjVec`,
`isConjVec_iff`, `isConjVec_iff_jacobi`, `jacobiVar_zero`, and
`conjVec_jacobi_at`.  These declarations only inspect the complete intrinsic
geodesic and its vector-slot differential inside the component of the selected
basepoint.  Their public names and proof content are unchanged.

## Remaining N frontier (next planning pass)

- N-c: the endpoint covariant-derivative identity `D_t J_w(0) = w` (check
  first whether the intrinsic lane's endpoint identities already provide it —
  `intrinsicGeodesic_mfderiv_zero` is the t-velocity version; the s-field
  version needs the `∂ₛ∂ₜ` commutation at `0`).
- N-d: the index-form argument (minimizing ⟹ no INTERIOR conjugate vector)
  — the genuinely hard brick: broken-variation second-variation comparison
  from a Jacobi field vanishing at an interior time.  Assets:
  `Variation/SecondVariation{,Minimiser}.lean`, `jacobi_unique`,
  `exists_intrFrame`, Wronskian layer.  Reference route:
  frenzymath `IndexForm*` + `NoConjugateOfMinimizing` +
  `MinimalGeodesicNoConjugate` (five files — plan before implementing).

## 2026-07-24 rescaling bridge

N-c is complete in `JacobiVariation.lean` via `intrinsic_jacobi_d0`.
This file now also proves:

- `jacobiVar_smul`: differentiating the launch variation at time `c` along
  `u` agrees with differentiating the corresponding launch variation at time
  one along `c • u`; and
- `conjVec_jacobi_at`: a conjugate vector `c • u`, with `c ≠ 0`, produces a
  nonzero direction whose intrinsic Jacobi variation along the original
  geodesic launched by `u` vanishes at time `c`.

Focused verification passes without warnings.  This closes the scaling
interface needed by N-d; it does not itself prove that a minimizing geodesic
has no interior conjugate vector.

## 2026-07-24 conjugate-vector reversal

The fixed-time intrinsic reversal brick is complete and exact-current:

- `intrinsicGeodesic_reverse` identifies the reversed intrinsic geodesic with
  the intrinsic geodesic launched from the endpoint with negative terminal
  velocity.
- The private `exp_pair_reverse` proves the endpoint Wronskian pairing between
  the forward exponential differential at `u` and the reversed exponential
  differential at the negative terminal velocity.
- The public `conjVec_reverse` uses that pairing, positive definiteness, and
  finite-dimensional injective/surjective duality to prove conjugacy is
  invariant under geodesic reversal.

The source is placeholder-free; focused verification and the targeted module
refresh pass.  The
`conjVec_reverse` theorem and its dedicated reversal machinery are both 100%;
the minimizing-tail theorems remain unstated here and therefore remain 0%.
