# Maximal-regularity solution-field links

## Purpose

`SolutionFieldLink.lean` is the low dependency layer relating the two spatial
companion fields of `maxRegDuhamelMap` to its canonical `timeH1.toFun`
representative.  It imports only `SolutionSpace`; in particular it does not pull
the local-Lipschitz existence or cross-scale energy layers into
`Nonautonomous`.

## Route

The structural per-mode FTC results previously located in
`LocallyLipschitzExistence.lean` were moved here.  For each eigenindex, those
identities identify the companion-field coefficient with the coefficient of
`maxRegDuhamelMap.toFun`.  Resolvent compactness supplies countability of the
eigenindex, so the per-mode almost-everywhere identities can be assembled on
one common full-measure set and closed by `tensorHs.ext`.

The public endpoints are:

- `solField_toFun_ae` for the `H^{a+2}` companion field;
- `solFieldHa1_toFun_ae` for the `H^{a+1}` companion field.

Both conclude equality only after the canonical Sobolev inclusion into `H^a`.
They add no consumer hypothesis: the compact-resolvent witness is already an
input of the non-autonomous maximal-regularity theorem.

## Verification

Focused verification passed for the new link module, the importing
`LocallyLipschitzExistence` module, and `Nonautonomous`.

The first local proof used `coeffCLM`, but that functional belongs to the
higher cross-scale trace layer.  Replacing it with the canonical low-level
`tensorHsCoeffL` from the Plancherel layer preserved the proof and kept this
module's only import at `SolutionSpace`.
