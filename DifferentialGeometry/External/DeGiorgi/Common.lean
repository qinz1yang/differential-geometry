-- Modified 2026-04-28: updated internal import paths for project namespace
import Mathlib

/-!
# Common Prelude

This module is the shared prelude for the De Giorgi development.

Policy:

- imports come directly from `Mathlib`;
- declarations in this directory live under `DeGiorgi`;
- shared opens and scoped notations live here so the theorem files stay small.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace DeGiorgi

end DeGiorgi
