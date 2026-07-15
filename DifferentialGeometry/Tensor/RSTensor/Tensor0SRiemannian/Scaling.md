# Scaling.lean — constant metric scaling of covariant tensor norms

## 2026-07-09

The reusable scaling layer now proves:

- `normSq0S_smul`: the squared norm is quadratic in the tensor argument;
- `normSq0S_scale`: under `g ↦ c g`, the squared norm of a covariant
  `s`-tensor gains the factor `(c⁻¹)^s`.

These are the tensor-level producers used by the parabolic curvature norm
identity `paraRmNormSq`; they do not themselves prove noncollapsing or an HCG
endpoint.  Focused verification and the targeted module build both passed.

Local scaling lemmas: **100% checked**.  Whole-HCG accounting remains
approximately **45% machinery** and **0% endpoint theorems**.
