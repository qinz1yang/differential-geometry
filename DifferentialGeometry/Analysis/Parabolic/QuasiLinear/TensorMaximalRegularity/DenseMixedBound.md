# DenseMixedBound

## Proved

- `dense_lipschitz` shows that the canonical `Dense.extend` of a Lipschitz
  map has the same Lipschitz constant.
- `mixed_of_dense` transfers a continuous two-scale estimate

  `A * max ||J x|| ||J y|| * ||x-y|| + B * ||J (x-y)||`

  from a dense subset to the completed normed space.

Both proofs are purely topological.  The second proof closes the sublevel set
of the continuous left- and right-hand sides in the product space.

## Role in the Ricci-DeTurck route

The low-regularity nonlinear estimate is first available for smooth compact
tensors.  These lemmas package the two repeated completion steps needed to
turn it into the global Sobolev nonlinearity consumed by
`quasilinear_maxreg_solution_of_nemytskii`, without repeating the long
closed-set argument in the concrete Ricci-DeTurck file.

## Verification

The focused source check passed with no warnings or `sorry`s.  The named
exported target was refreshed after that check.

This is supporting machinery only.  Neither exact analytic endpoint theorem
is proved here; both endpoint percentages remain 0%.
