# JacobiCoord.lean

## 2026-07-19 created (option-1 lane, J-remaining sub-bricks a+b)

Scalar derivative identities for the frame coordinates of a Jacobi field.
Both green on first focused check, no `sorry`:

- `parInner_deriv`: for parallel `Fi`, `d/dt g(Fi, Y) = g(Fi, D_t Y)`
  (via `inner_deriv_at` metric compatibility; parallelism kills the other
  term).
- `parInner_d2`: additionally `Y` Jacobi at `t` ⟹
  `d/dt g(Fi, D_t Y) = -g(Fi, R(Y, γ̇)γ̇)` (via `jacobi_d2_eq`).

- (c) `parInner_curv_expand` (DONE 2026-07-19, green): the curvature pairing
  expands to the `(A t) y` linear-combination form via `gON_expand` +
  `riemannOp` slot-1 CLM linearity.  Elaboration lessons: needs the
  `attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup/…` +
  `set_option synthInstance.maxHeartbeats 400000 in` prefix (iterated-CLM
  instance search over `TangentSpace` times out otherwise), and the
  `simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum',
  Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
  smul_eq_mul]` chain closes the goal COMPLETELY (no `mul_sum`/`ring` tail —
  they error with "no goals").

- (d2) `jacobi_unique` (DONE 2026-07-19, green): **uniqueness of Jacobi
  fields with given initial data** along any curve carrying a parallel g-ON
  frame of full card on `[0,b]`, under an explicit curvature-entry bound
  `|g(Fᵢ, R(Fⱼ,γ̇)γ̇)| ≤ C`.  Route: scalar coordinate differences (no
  dependent-type subtraction), (a)+(b) supply the derivative facts, (c) the
  `-∑ aᵢⱼ yⱼ` form and hence `|w| ≤ C ∑|y|`, and `ode2_pi_zero`
  (`Analysis/ODE/SecondOrderLinearExistence.lean`) closes; values recovered
  by `gON_expand` on both sides.  Elaboration lesson: goals of the shape
  `(fun t i => …) t i` (from passing explicit lambdas to `ode2_pi_zero`)
  block `rw` — a bare `simp only []` beta-reduces first.

**J-remaining is COMPLETE** (a+b+c+d1+d2 all green).  With the intrinsic
lane's `intrinsic_jacobi` (existence via variations, `JacobiVariation.lean`)
and `exists_intrFrame` (frames at every scale), the Jacobi layer along
intrinsic geodesics at arbitrary scale now has: existence, uniqueness,
frames, and coordinate calculus.  Next brick (N, minimizing ⟹ no interior
conjugate point) requires FIRST a design decision: the conjugate-point
interface should be built on `intrinsic_jacobi_one` (Jacobi field at `t=1` =
vector-slot `mfderiv` of `expMapIntrinsic`), i.e. "differential singular ⟺
nontrivial Jacobi field vanishing at both ends", and must be coordinated
with the intrinsic lane's in-flight diagExp/branch interface — do not pick
the interface unilaterally.
