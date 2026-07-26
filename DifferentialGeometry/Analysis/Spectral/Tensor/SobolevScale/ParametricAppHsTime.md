# ParametricAppHsTime

## Purpose

This module is the pathwise time-regularity producer for the completed tensor
action `appHs`. It deliberately proves derivatives only after application to
a fixed Sobolev input. This is the cheapest normal form and avoids asking Lean
to normalize equality or convergence in an entire reducible Hom/CLM object.

## Verified result

Focused verification passes without `sorry`.

`exists_appHsDeriv` is complete. From a jointly smooth coefficient family it
chooses one jointly smooth coefficient derivative `dΦ` and proves, for every
time in the open parameter set, every Sobolev order, and every fixed input `U`,

```text
HasDerivAt (τ ↦ appHs (Φ τ) U) (appHs (dΦ t) U) t.
```

The proof is a real producer rather than a consumer wrapper:

1. `coeff_secant` proves the coefficient FTC remainder identity by evaluating
   a fixed fibre input and all output slots before rewriting.
2. `joint_jet_small` makes finitely many jets of `dΦ(t)-dΦ(a)` uniformly
   small on the compact manifold.
3. `icg_path_comm` and the pointwise fibre-norm path-integral bound transfer
   that estimate to the averaged coefficient remainder.
4. `appHs_unif` turns the pointwise finite-jet envelope into a completed
   operator-norm estimate with a coefficient-independent constant.
5. The final slope proof is again fully applied to `U`; no operator-valued
   derivative equality is introduced.

The attempted whole-operator `Tendsto` statement exposed the documented CLM
topology diamond. It was removed rather than hidden behind a transparency or
heartbeat change. The applied theorem is both sufficient and cheaper.

`appHs_path_cd` is also complete. Finite-order induction repeatedly applies the
same all-order derivative producer and proves that

```text
t ↦ appHs (Φ t) U
```

is `C∞` on the open parameter set for each fixed completed input. This remains
a strong, applied statement; it does not assert smoothness of a whole
operator-valued path.

## Consult ruling

The completed Pro consult selected the weaker pathwise route:

- do not first prove joint smoothness or differentiability of
  `(t,U) ↦ appHs (Φ t) U`;
- obtain a single coefficient derivative valid for all Sobolev orders;
- prove fully applied finite-order derivatives, specialize them to the scalar
  loss-two Laplacian path, and then run the Banach-space ODE induction;
- only after all-scale time smoothness, derive compact-interior jet masses;
- do not import or repackage the full DeTurck forcing-jet machinery, because it
  consumes the very jet bounds still to be proved.

This matches the public GitHub reference requested for consultation:
`liao9yuan/differential-geometry`, branch `short-time-existence`.

## Exact frontier

The generic completed-action time derivative is now **100%**. Its dedicated
remainder machinery is **100%** and focused-green.

The next missing producer is the scalar loss-two specialization combining this
path theorem with the fixed-background covariant-derivative maps. After that,
the Galerkin limit ODE must be normalized to its explicit velocity and
differentiated at every spatial Sobolev order.

Honest project accounting at this point:

- original minimal `A2` finite-support estimate: **100%**;
- all-scale `A2` bounds and strong first derivative packaging: **100%**;
- generic pathwise `appHs` derivative and fixed-input `C∞` path: **100%**;
- scalar loss-two coefficient path theorem: implementation complete, downstream
  verification pending its producer `.olean` refresh;
- `galLimExt_smooth`: theorem **0%**, dedicated higher-time machinery about
  **60%**;
- compact-interior Galerkin jet mass: theorem **0%**;
- classical conjugate-heat reconstruction: **0%**;
- Perelman noncollapsing endpoint: **0%**;
- broader HCG machinery remains approximately **57%**, while its endpoint
  theorems remain **0%**.

## 2026-07-16 dynamic-input completion

The completed-action product rule is now closed for a moving Sobolev input.
`exists_appHsDyn` supplies the fully applied derivative, while
`appHs_dyn_cont`, `appHs_dyn_fin`, and `appHs_dyn_cd` propagate continuity,
finite `ContDiffOn`, and `C^infinity` regularity. The private
`coeffRem0_move` estimate controls the coefficient remainder using only scalar
operator-norm smallness and local boundedness of the moving input; it never
forms a CLM-valued derivative or whole-operator equality.

Focused verification and the targeted export refresh are green. The generic
fixed-input and dynamic-input time-regularity APIs are both **100%**. Their
first scalar consumers are now also complete, so the live frontier has moved
past `galLimExt_smooth` to compact-interior Galerkin jet majorants.

## 2026-07-19 common derivative export

`exists_appHsFull` has been added as the common-derivative version of the
fixed-input theorem.  It chooses one jointly smooth coefficient derivative
`dPhi` and records, for that same `dPhi`, both:

- the componentwise scalar `HasDerivAt` statement obtained by evaluating every
  fibre input and every output slot; and
- the strong `HasDerivAt` statement for `appHs (Phi t) U` at every integer
  Sobolev order and every fixed completed input `U`.

This is the bridge needed to identify a geometrically specified tensor PDE
with the derivative used by the spectral strong-solution package: uniqueness
of the scalar derivative identifies the smooth tensor first, after which the
all-order Sobolev derivative is already attached to that exact tensor.

The new theorem is source-complete and contains no `sorry`.  Its focused Lean
verification is still pending because a shared named Lean build is active;
the earlier verified results above are unchanged.
