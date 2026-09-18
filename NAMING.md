# NAMING.md — public declaration names

This file is the authority for declaration names in `DifferentialGeometry`. `STRUCTURE.md` governs
file and folder placement. `AGENTS.md` governs workflow, soundness, source discipline, and delivery.
The exact elaborated declaration remains the final authority for what a name denotes.

## 1. Search before naming

Before adding or renaming public mathematics:

1. Search Mathlib and this library by mathematical content, type shape, and several standard names.
2. Read every plausible signature and inspect its axiom closure.
3. Reuse, generalize, or re-export the canonical declaration when possible.
4. Check the proposed fully qualified name for collisions.

Do not create a second vocabulary for an object that already has a standard mathematical or Mathlib
name.

## 2. Casing by declaration kind

- Theorems and lemmas use lower snake case.
- `def` and `abbrev` names use lower camel case, with one exception: type-valued abbreviations
  (abbreviations whose return type is a `Type`) use Upper camel case.
- `structure`, `class`, and `inductive` names use Upper camel case.
- Namespaces use Upper camel case and name mathematical objects or subjects, not directory history.
- Preserve an established Mathlib identifier token such as `ContMDiff`, `mfderiv`, or an existing
  camel-case definition root when it occurs inside a theorem name.

The exception for type-valued abbreviations reflects the established library convention: `ClosedCell`,
`CellBoundary`, `MorseModel`, `StandardHandle`, `AttachingRegion`, `BeltRegion`, and `Corner` are all
type-valued abbreviations or definitions written Upper camel case, matching the Upper camel case of
the type-level objects they denote. Function- and value-valued definitions and abbreviations remain
lower camel case (`cellBoundaryInclusion`, `handleSet`, `adjunctionHomeomorphUnionImage`).

Local implementation lemmas follow the same rules. A private declaration may have a concise technical
name, but making it public requires a mathematical name and a library-wide collision check.

## 3. Name the mathematical result

Use standard, widely recognized vocabulary. Name a classical theorem by its accepted name only when
the public signature expresses the accepted theorem with natural hypotheses.

Examples include `morse_lemma`, `no_critical_values`, `cell_attachment`, `bonnet_myers_*`,
`hopf_rinow_*`, `gauss_bonnet`, `lichnerowicz_*`, `hamilton_*`, and `perelman_*`.

If a result is only a conditional core, name the condition or supplied object that drives it. A lemma
which assumes a preconstructed unit-speed flow belongs under `UnitSpeedFlow` and should describe its
conclusion, for example `UnitSpeedFlow.image_sublevel`; it is not itself the classical
`no_critical_values` theorem. A theorem may not acquire a classical name by accepting a structure,
modified function, existence package, or proposition-valued hypothesis that already contains the hard
part of the classical conclusion.

For results without an accepted eponym, describe the conclusion and only the essential disambiguating
hypotheses:

```text
subject_conclusion_of_essential_hypotheses
```

Prefer names such as `sublevel_diffeomorphic_of_no_critical_value`,
`chartHessian_nondegenerate_iff`, or `cellAdjunctionSpace_homeomorphic_union` over names describing a
proof route.

## 4. Hypotheses and variants

- Use an `of_...` suffix only for load-bearing mathematical hypotheses needed to distinguish the
  result, such as `_of_compact`, `_of_closed`, or `_of_ricci_lower_bound`.
- Do not list routine typeclass assumptions or implementation devices in the name.
- Different conclusions are coequal sibling theorems with names describing those conclusions.
- The same conclusion under stronger assumptions is a corollary of the natural primary theorem.
- Local, global, boundary, relative, pointwise, integrated, scalar, tensor, and time-dependent variants
  receive qualifiers only when the distinction is mathematically real.
- Use conclusion-specific words such as `homeomorph`, `diffeomorph`, `homotopyEquiv`, `isometry`,
  `continuous`, or `contMDiff`; do not blur these strengths under one generic name.

## 5. Definition and structure names

A public definition names a genuine mathematical object. A public structure names data with a stable,
reusable mathematical meaning and laws intrinsic to that object.

Avoid public names ending in `Data`, `Package`, `Context`, `Bundle`, or `Witness` when the object exists
only to shorten binders or carry hypotheses for one proof. Do not use a structure to package a theorem's
conclusion. Prefer ordinary variable blocks, explicit hypotheses, or a canonical existing structure.

Place operations and laws in the namespace of their main object when this makes names shorter and
discoverable, for example `UnitSpeedFlow.image_sublevel` or `AdjunctionSpace.lift`.

A primed public name is allowed only for a genuinely standard near-variant when a more descriptive name
would be misleading. A prime must not stand for "new", "fixed", "manifold version", or an implementation
stage.

## 6. Forbidden public-name patterns

Do not expose:

- task history, node identifiers, milestone numbers, or agent terminology;
- effort or status words such as `final`, `complete`, `closure`, `unconditional`, `strong`, `clean`,
  `assembly`, `v2`, or `new`;
- proof mechanisms such as `_via_schur_complement` when they are not part of the statement;
- invented abbreviations that are not standard in mathematics or Mathlib;
- misleading classical theorem names for conditional transport or assembly lemmas.

## 7. Source text

Non-vendored Lean source contains no inline comments or declaration docstrings. Required copyright
headers and module docstrings are allowed. Names and signatures must remain honest and searchable.
On-disk identifiers are English.

## 8. Review checklist

Before accepting a public name, verify:

- the declaration is in its canonical namespace and topic home;
- the name matches the exact conclusion and strength;
- every named hypothesis is essential;
- no stronger or more canonical existing declaration was missed;
- special cases are corollaries of the natural theorem;
- the name contains no task history or implementation route;
- a classical name is used only for the actual classical statement.
