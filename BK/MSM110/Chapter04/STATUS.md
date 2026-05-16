# MSM110 Chapter 4 Status

Source: `C:/Users/liao9/Downloads/MSM110_clean01.tex`, Chapter 4,
"Maximum principles".

## Scalar First Pass

| LaTeX label | BK alias | Canonical RicciFlower theorem | Status |
| --- | --- | --- | --- |
| `prop:scalar_maximum_principle_pointwise` | `BK.MSM110.Chapter04.Scalar.prop_scalar_maximum_principle_pointwise` | `RicciFlower.Realized.msm110_ch4_scalar_pointwise_bounds` | Proved wrapper. The book's pointwise lower/upper statement is split into lower and upper strict-barrier applications. |
| `thm:scalar_maximum_principle_supersolutions` | `BK.MSM110.Chapter04.Scalar.thm_scalar_maximum_principle_supersolutions` | `RicciFlower.Realized.msm110_ch4_scalar_supersolutions` | Proved wrapper around `strict_barrier_nonnegative`; the parabolic inequality is supplied on the negative set. |
| `prop:scalar_maximum_principle_linear_reaction` | `BK.MSM110.Chapter04.Scalar.prop_scalar_maximum_principle_linear_reaction` | `RicciFlower.Realized.msm110_ch4_scalar_linear_reaction` | Proved wrapper using the rescaled function `exp (-C*t) * u(t,x)`. The rescaled negative-set calculation remains an explicit hypothesis. |
| `thm:scalar_maximum_principle_ode` | `BK.MSM110.Chapter04.Scalar.thm_scalar_maximum_principle_ode` | `RicciFlower.Realized.msm110_ch4_scalar_ode_lower` | Proved lower-bound wrapper using the uniform compact-value Lipschitz route. Monotonicity is retained as a book-facing hypothesis, although the core proof consumes the uniform Lipschitz estimate. |

## Deferred Chapter 4 Frontiers

- Tensor nonnegativity maximum principle.
- Systems maximum principle.
- Time-dependent subset maximum principle.
- Avoidance maximum principle.
- Strong maximum principles.

These are intentionally not implemented in the scalar first pass.
