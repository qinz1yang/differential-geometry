# SecondOrderLinearExistence.lean

## 2026-07-19 created (option-1 lane, brick J-b)

`forward_ode2_of_bound`: global forward solutions of `y'' = A(t) y` on
`[0, T]` for an operator family `A : ℝ → F →L[ℝ] F` that is pointwise
continuous in time and uniformly bounded (`‖A t‖ ≤ M`), on any inner-product
`F` with `[CompleteSpace F]`.  Returns the pair `(y, v)` with `y 0`, `v 0`
prescribed, both `ContinuousOn [0,T]`, and `y' = v`, `v' = A t y` as
`HasDerivWithinAt … (Ici 0)` at every `t ∈ [0, T)`.  Sign-neutral: pass `-A`
for the Jacobi system.

Focused check PASSED, no `sorry`.

Route: phase space `WithLp 2 (F × F)` (plain `F × F` has no inner-product
instance; the first-order engine `forward_solution_of_lipschitzWith_affineBound`
genuinely needs Hilbert — its `ballRetraction` 1-Lipschitz constant is
Hilbert-only, verified by a weaken-and-revert experiment).  Field
`f t z = toLp 2 (z.snd, A t z.fst)`; Lipschitz constant `max 1 M` via
`prod_norm_sq_eq_of_L2`; affine constant `0`; components extracted through
`ContinuousLinearMap.{fst,snd} ∘L (prodContinuousLinearEquiv 2 ℝ F F)`.

Elaboration lessons: `(f t z - f t w).fst` etc. handled by `simp [hf_def]`
(ProdLp `sub_fst/sub_snd` simp set); the `(fun t => (γ t).fst) 0` goals need a
`show (γ 0).fst = _` beta step before `rw`; `(toLp 2 (a, b)).fst = a` is
`rfl`.

Consumer (next, brick J-e): the frame-coordinate Jacobi system along the
intrinsic radial geodesic, with `A t` the curvature operator matrix in the
`exists_intrFrame` frame (`Volume/IntrRadialFrame.lean`).

## 2026-07-19 addition: `ode2_pi_zero` (J-remaining sub-brick d1)

Zero-solution Grönwall corollary for componentwise second-order systems:
scalar coordinates `y · i` continuous on `[0,b]`, forward derivatives
`y' = v`, `v' = w` on `[0,b)`, domination `|w t i| ≤ C ∑ⱼ |y t j|`, zero
initial data ⟹ `y ≡ 0` on `[0,b]`.  Green.  Route: package into
`EuclideanSpace ℝ ι` via `(PiLp.continuousLinearEquiv 2 ℝ _).symm`
(componentwise-to-joint derivatives via `hasDerivWithinAt_pi`), entry bound →
`‖W‖ ≤ (C·card)‖Y‖` via `sq_sum_le_card_mul_sum_sq` (root namespace, import
`Mathlib.Algebra.Order.Chebyshev`), close with `norm_le_gronwall_secondOrder`
at `δ = eps = 0` and `gronwallBound_zero_mul_eps (a := 0)`.
Elaboration lessons: `pow_le_pow_left₀` (₀-suffixed in this pin);
`set`-bound lambdas need `show`-beta before `rw`; EuclideanSpace application
surfaces as `.ofLp i` and `(L u).ofLp i = u i` is `rfl`.
