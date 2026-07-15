# Rank-zero mixed-field embedding

## Status (2026-07-09)

`Tensor0SField.toTensorRSField` now has a complete, self-contained smoothness
proof.  It no longer contains a `sorry` and does not import the higher-level
`Tensor.Mixed.Field` module.  The proof works directly in the tangent tensor
bundle trivializations already owned by this layer.

The accompanying API consists of scalar evaluation at rank zero, the forward
fiber map `Tensor0SSpace.toRS0`, its application theorem, and the pointwise
agreement theorem `Tensor0SField.toRS0_eq`.  This keeps `toRS0` as the forward
application map and does not expose tensor representation internals downstream.

Focused verification passed, and the explicitly named module refresh also
passed.  The pre-existing local unused-section-variable warnings on the two
function-smultiplication application lemmas were silenced locally.

## Project position

- rank-zero smooth-field embedding producer: 100% checked;
- first-order connection compatibility using this producer: 100% checked
  before the later upstream object-file loss;
- raw rank-zero connection-Laplacian theorem: theorem completion 0% until its
  source check can run against a rebuilt `Derivation` module;
- Perelman no-local-collapsing and `ham3_noncollapse`: theorem completion 0%;
  their dedicated entropy/conjugate-heat machinery remains roughly 20%;
- whole HCG compactness machinery remains roughly 45%, while its endpoint
  theorems remain 0%.

