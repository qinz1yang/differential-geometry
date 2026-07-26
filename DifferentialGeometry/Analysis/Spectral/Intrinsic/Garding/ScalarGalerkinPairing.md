# Scalar Galerkin pairing

## 2026-07-14 A2-only closure

The moving-minus-frozen scalar Laplacian now has a support-independent finite
Galerkin dissipation estimate.  `cc_finite_diss` combines `cc_lap_pair`, the
coefficient-one `cc_dirichlet_gap`, the two spectral-to-jet bounds, and
`finite_cc_pair`.  With the internal choice `delta = 1/4`, its top coefficient
is exactly `5/3 < 2`; Young's inequality puts every remaining term into one
nonnegative lower-energy constant.

`cc_a2_closure` is the minimal live-consumer adapter.  It chooses `Cmid` before
quantifying the arbitrary finite mode set `S` and finite spectral element `T`.
Its conclusion is the A2 part of the `GalerkinParabolicEnergy.hclosure` normal
form on `S`.  Taking the order to be `n = a + k` gives a family `Cmid k` which
depends on the order and fixed metric pair, but not on the Galerkin cutoff `N`,
the support, or its cardinality.  The single top coefficient remains `5/3` for
all orders.

This is deliberately not presented as the full closure: the source/potential
arm and its seed term have not been joined here.  Also, this fixed-metric-pair
theorem does not itself provide one `Cmid k` uniform over a varying time-family
of metrics; that parametric coefficient producer is a separate live lane.  Both
new theorems are complete (100%) and focused verification passed without a new
`sorry`.

Honest project accounting: the eventual full scalar critical-tame theorem is
still unstated/unproved (0%); its dedicated reusable machinery is about 82%.
`heatpot_of_maxreg` remains 0% with about 35% dedicated machinery, the classical
moving conjugate-heat theorem remains 0% with about 77% dedicated machinery,
and Perelman no-local-collapsing / `ham3_noncollapse` remain 0% with about 40%
dedicated analytic machinery.  Whole HCG machinery remains about 53%, with its
endpoint theorems at 0%.

## 2026-07-14 A1 exact design

The potential endpoint `cc_a1_closure` is not yet stated or proved (0%).  Its
dedicated reusable machinery is about 70%: finite spectral pairing, the
balanced iterated-Laplacian pairing, scalar potential realization, and the
final Young inequality are available, while the uniform high-order scalar
multiplier producer is missing.  This percentage is separate from the 0%
theorem-level status.

The minimal theorem should fix a solution `S`, its proof `hS`, a regular
terminal time `T`, and a compact set `K` of reversed-time offsets satisfying
`(T : ℝ) - t ∈ D.regular` for `t ∈ K`.  With
`q = S.family.metric (T : ℝ)`, it should produce

```text
∃ Cmid : ℕ → ℝ, (∀ n, 0 ≤ Cmid n) ∧
  ∀ n t ∈ K, ∀ F v hv, hv.toFinset ⊆ F →
    2 * a1Pair q S T t n F v hv
      ≤ (1 / 4) * spectralEnergy q (n + 1) F v
        + Cmid n * spectralEnergy q n F v.
```

The live-facing left side may use the coefficients of `conjA1 S T t` applied
to the finite-support `H¹` realization.  The lower-layer proof should instead use
the equivalent smooth tensor
`scalarSmul q 0 0 (conjCoeff S ((T : ℝ) - t))
  (tensorHsSmoothRepr v hv)`, then cross the existing
`scalarPotOp_core` / `scalarPotH0_apply` bridge.  The quantifier order is
essential: `Cmid` is chosen before the time, finite mode set, support, and its
cardinality.

For the pairing estimate, instantiate `iterL_window_pair` with
`s₀ = σ = 0`, `a = n`, `r = n / 2`, `dX = dY = 0`, `NA = n + 1`,
`NB = n`, `X = U`, and `Y = ζₜ • U`.  Its two index obligations are
`2 * (n - n / 2) ≤ n + 1` and `2 * (n / 2) ≤ n`.  A uniform scalar
multiplier jet estimate then gives

```text
|Q| ≤ Pₙ * H_(n+1) * H_n,
```

where `Pₙ` depends on the order, the fixed terminal metric, and the compact
time slab, but not on time, support, cutoff, or cardinality.  The two
`hsJet_le` estimates absorb the high and low jet windows into `H_(n+1)` and
`H_n`.  The exact Young allocation is

```text
2 * Q ≤ 2 * Pₙ * H_(n+1) * H_n
      ≤ (1 / 4) * H_(n+1)^2 + 4 * Pₙ^2 * H_n^2,
```

because `(H_(n+1) / 2 - 2 * Pₙ * H_n)^2 ≥ 0`.  Thus the A1 top
coefficient is exactly `1/4 < 1/3`, and its lower constant is `4 * Pₙ^2`.
Together with `cc_a2_closure`, the top coefficient is
`5/3 + 1/4 = 23/12 < 2`, and the lower constants add.  If a stronger uniform
`Hⁿ → Hⁿ` zeroth-multiplier bound is later available, A1 can instead be
entirely lower order and contribute top coefficient zero.

The precise missing producer is a compact-family iterated scalar-multiplier
jet bound, suggested name `smul_jet_unif`.  A solution-specific
`conjCoeff_joint` should derive its joint coefficient regularity from `hS` and
the regular time slab.  Existing `conjA1_short` supplies only a uniform
zeroth-order coefficient bound and an `H¹ → H⁰` operator norm, so it does not
close arbitrary spectral order.  The compact-slab and regular-time inputs are
geometric domain data, not new coefficient-bound assumptions.  This is a
missing reusable API, not a mathematical obstruction, and should be solvable
without user intervention.  No Lean source was changed during this A1 audit.
