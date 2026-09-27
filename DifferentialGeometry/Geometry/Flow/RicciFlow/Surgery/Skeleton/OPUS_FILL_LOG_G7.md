# G7 fill log (area inequality with density)

- 2026-09-26: new file `Analysis/Integration/Measure/Parametric/AreaInequality.lean`.
  Public: `lintegral_image_le_lintegral_paramDensity_mul` (weight `φ (f x)`, no injectivity,
  no measurability of `φ`), `lintegral_image_le_lintegral_paramDensity_mul_of_le` (DESIGN_22 §5
  majorant form; `hh : Measurable h` dropped, it is unused). Equality under injectivity already
  exists: `lintegral_image_eq_lintegral_paramDensity_mul` (Parametric/Integration.lean).
- Proof: critical set `{J = 0}` has null image via `riemannianVolumeMeasure_image_le_of_isCompact`
  on a compact covering of `U`; regular part is locally injective (IFT in a chart),
  `exists_partition_injOn`, and on each piece `map_withDensity_paramDensity` + `lintegral_map_le`
  + `lintegral_withDensity_le_lintegral_mul`.
- Compile: in-tree compile blocked (Parametric/Integration and LocallyInjective oleans missing);
  scratch copy with those two inlined compiles clean under `linter.mathlibStandardSet`,
  `#lint` clean, axioms propext/Classical.choice/Quot.sound.
