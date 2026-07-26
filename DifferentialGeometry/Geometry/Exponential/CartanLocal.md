# CartanLocal

## Role

This module assembles the invariant local Cartan metric calculation from the
already verified Jacobi transfer and a smooth fixed-first diagonal-exponential
inverse branch.

## Route

- `cartanMap` is `exp_{p'} ∘ i ∘ exp_p⁻¹`, using a selected
  `DiagInvBranch` for the inverse.
- `cartanMap_smooth` proves smoothness only on the honest fixed-first branch
  domain.
- `cartanMap_sq` differentiates the composite, invokes `expDiff_sq_xfer`, and
  cancels the source exponential differential with
  `DiagInvBranch.exp_inv_mfderiv`.
- `cartanMap_inner` polarizes the square identity.
- `cartanPD` composes the source fixed inverse, the tangent linear isometry,
  and the target fixed exponential into a genuine `C∞`
  `PartialDiffeomorph`.
- `cartanPD_center` places the source center in its domain, and
  `cartanPD_inner` transfers the metric identity to the realized partial
  diffeomorphism.

No global frame, analytic-continuation assumption, or local-isometry wrapper
hypothesis is introduced.

## Verification and progress

Focused verification passes without warnings, and exact module verification is
GREEN (`3866/3866`); the file is sorry-free.

`ham3_space_box` remains unproved and therefore 0%.  Its dedicated positive
Killing--Hopf machinery is approximately 55% complete.  The local Cartan
partial-isometry phase is now implemented; the remaining substantive frontier
is the explicit punctured-sphere extension and global two-chart gluing.

## 2026-07-24 branch compatibility update

The sole direct `exp_inv_mfderiv` call now projects the diagonal branch through
`DiagInvBranch.fixed` and supplies the fixed target-domain membership. The
Cartan API itself remains diagonal and unchanged; it consumes the canonical
fixed-first calculus rather than maintaining an independent inverse proof.

The source is focused green and placeholder-free. This compatibility edit does
not change the existing `ham3_space_box` accounting: theorem-level 0%, with
its dedicated positive Killing--Hopf machinery still approximately 55%.
