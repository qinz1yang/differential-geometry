# Naming conventions

Follow Mathlib naming conventions and the established names in this project.

- Lean source files and concept directories use `UpperCamelCase` mathematical
  names.
- Theorems and lemmas use `snake_case` names describing their conclusions.
- Definitions, structures, classes, and abbreviations use `camelCase` names.
- Public declarations live under the `Poincare` namespace, followed by the
  natural mathematical namespace; namespaces need not mirror every path
  component.
- Name classical results by their accepted mathematical names. Otherwise name
  the conclusion and only the hypotheses needed to disambiguate it.
- Do not encode task history, implementation steps, arbitrary numbering, or
  proof status in public declaration names.
- Use qualified names when they avoid ambiguous or overly broad namespace
  openings.

Before introducing a public name, search Mathlib, `DifferentialGeometry`, and
this repository for the same mathematical content and nearby name variants.
Prefer reusing or extending a canonical declaration over creating a parallel
API.

Working names in blueprint or status documents remain proposals until the
corresponding declaration is implemented, compiled in the pinned environment,
and checked for its transitive axioms.
