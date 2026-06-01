import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Coordinate Realization Notes

This lightweight module anchors the future coordinate bridge. Mathlib supplies
charts, tangent coordinate changes, local frames, tangent trivializations, and
`CovariantDerivative.difference`; the synthetic Ricci-flow core should use this
folder only for realization lemmas, not for primary tensor identities.
-/
