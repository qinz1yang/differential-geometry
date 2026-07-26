# FineTensorProject

## Status

Source-written only. The shared named build still owns the Lean verification
lane, so no Lean or Lake process was started here. Every declaration below
still requires focused elaboration verification.

## Mathematical role

The parabolic fixed point cannot live on arbitrary scalar arrays from several
charts: independent arrays generally violate the tensor transition law on
overlaps. This file factors the chart operation through a genuine dependent
tensor section.

- `modelRepack` reconstructs a mixed tensor in the canonical model-fibre
  basis, and `modelRepack_proj` / `modelRepack_eq` prove the two exact
  component identities.
- `chartExtract` and `chartRepack` pass between one chart-component family and
  a genuine fibrewise tensor section.
- `chartRepack_extract` proves that extracting every raw component of a genuine
  section and repacking it recovers the section on the chart source.
- `chartRepack_fine` proves the sharper identity needed by the parametrix: a
  fine-localized canonical component repacks to `φ · ρ_α · S` pointwise.
- `finePouRepack` performs the nested finite sum over canonical active charts
  and their fine refinements; `finePou_retract` proves this actual extraction
  and reassembly satisfy `RF ∘ E = id` whenever the fine weights sum to one on
  `tsupport ρ_α`.
- `canonFineData`, `CanonFineIdx`, and the three `canonFine...` cutoff maps
  choose those refinements from `existsFineChart` for every canonical chart;
  `canonFine_retract` discharges the partition hypothesis and exports the
  unconditional exact retraction for any prescribed positive radius family.
- `CanonFineFlat` flattens the finite active atlas and all its dependent fine
  refinements into the one index type consumed by the finite Sobolev product.
  `canonFineQMap` is the actual quotient-level extraction map into that
  product, with coordinatewise addition and scalar identities.
- `canonFineRaw` exposes the corresponding raw representatives, while
  `canonCutRepack` multiplies arbitrary local outputs by the middle strict
  cutoff before pulling them back. `canonCut_retract` proves that this
  heat-compatible reassembly still satisfies the exact identity `R E = id`:
  the middle cutoff is one on the inner partition support, so no projection
  error is introduced.
- `fineRepack` forms the finite POU sum in the genuine dependent fibres, while
  `fineExtract` reads its chart components.
- `fineRepack_extract` proves the POU retraction identity under exactly the two
  geometric hypotheses needed: subordination of nonzero weights and sum one.
- `fineProject := fineExtract ∘ fineRepack` is consequently idempotent, by
  `fineProject_idem`. Its image is made of component families of genuine
  global tensor sections, not free incompatible arrays.

No smoothness, Sobolev boundedness, closed-range assertion, Banach instance,
new foundational class, axiom, opaque producer, `sorry`, or `admit` is used.

## Exact remaining analytic bridge

`FineTensorWkp.lean` now supplies the quotient localizations and finite
extraction function, and this file specializes it to the canonical flattened
fine family and supplies exact middle-cutoff reassembly. The next producer
must package the coordinatewise bounds as a continuous linear extraction map
and prove bounded Sobolev reassembly on the same finite product. It can then
combine that bound with `canonCut_retract` and use the theorem-valued
completeness API directly:

1. show projected Cauchy component families have a quotient limit;
2. use the exact idempotence above and continuity of the projection to show
   the limit remains in the projected image;
3. retain the genuine-section representative supplied by `fineRepack`;
4. run Picard convergence with `qCauchy_limit` / `qdist_limit`, without
   installing a new global `CompleteSpace` instance.

For the Ricci--DeTurck metric state the `(0,2)` symmetry condition must also be
preserved. The clean next layer is an intrinsic fibrewise symmetrization (or a
proof that the geometric heat/nonlinear map preserves symmetric input) before
restricting the projected image; this file intentionally does not encode
symmetry as a new class.

## Honest progress

- Algebraic finite-chart genuine-tensor projection, canonical quotient
  extraction, and exact middle-cutoff retraction: 100% source-written, 0%
  Lean verified.
- Bounded quotient-level projection and closed-image limit theorem: 0% exact
  theorem.
- Complete projected Picard construction: 0% exact theorem.
- Exact `ricci_flow_unif_existence`: 0%.
