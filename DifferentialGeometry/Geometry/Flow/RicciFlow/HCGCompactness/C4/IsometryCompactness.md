# IsometryCompactness.lean — F8 / MSM135 Cor `lbl374` (2026-06-11)

"Compactness of a sequence of isometries." Verification passed; **zero `sorry` in this
file** — the whole corollary (incl. the diffeomorphism) is assembled sorry-free on top
of the one engine `sorry` in `MapConvergence.lean` (`exists_cInf_subseq`) and one
honest-input predicate.

## Honest-input boundary

`IsometryDerivBounds Φ` = "all iterated Euclidean derivatives `∇ʳΦₖ` are uniformly
bounded (over `k`) on each compact set." The book *derives* this from the isometry
relation `(gₖ)_{ab}=∂Φₖ^α∂Φₖ^β(hₖ)_{αβ}` (`lbl375`) by a polynomial recursion it
attributes to §5 of [H6]; we take that conclusion as input (matches the repo's
honest-input convention, e.g. `GeometricInputs.lean`). This is the genuine geometric
content the book itself externalizes — NOT a frontier-hiding wrapper.

## What's proved (sorry-free here)

- `isometry_seq_cInf` — F8 convergence core: `IsometryDerivBounds` + smoothness ⇒
  a subsequence `C^∞`-converges on compacts to a smooth limit. (Direct
  `exists_cInf_subseq` application — the book-facing `lbl374` endpoint for Step D.)
- `comp_eq_id_of_cInf` — the "by symmetry" invertibility step, FULLY proved: from
  `Φₖ→Φ_∞`, `Ψₖ→Ψ_∞` (`C^∞`-on-compacts), `Φ_∞` continuous, `Φₖ∘Ψₖ=id`, conclude
  `Φ_∞∘Ψ_∞=id`. Route: `tendsto_of_cInf` (pointwise `Ψₖx→Ψ_∞x`) + a compact nbhd of
  `Ψ_∞x` (`exists_mem_nhds_isCompact_isClosed`, needs finite-dim ⇒ proper) +
  `tendstoUniformlyOn_of_cPConv` + `TendstoUniformlyOn.tendsto_comp` + `tendsto_nhds_unique`.
- `isometry_seq_diffeo` — full `lbl374`, FULLY proved (modulo the engine): two engine
  extractions (Φ, then Ψ along the Φ-subsequence; bounds restrict via
  `IsometryDerivBounds.comp_subseq`), composed subsequence `φ1∘φ2`, both convergences
  via `comp_subseq`, both inverse identities via `comp_eq_id_of_cInf`.

## Status / what remains

F8 (the corollary) is **complete at the proof level**: it reduces `lbl374` to exactly
ONE genuine analytic frontier — the AA-for-maps engine (`MapConvergence.exists_cInf_subseq`)
— plus the [H6] §5 honest-input. The plan's "F8 = apply F8tool" understated it: the
scalar `ArzelaAscoli.lean` tool is not directly enough; the engine (vector AA + diagonal
over orders + derivative-of-uniform-limit) is the real tool, now isolated as the sole
remaining `sorry`.

## Lean gotchas
- `omit [FiniteDimensional ℝ E] in` must precede the *docstring* (not sit between
  docstring and `theorem`).
- finite-dim ⇒ `ProperSpace` ⇒ locally compact needs
  `import Mathlib.Analysis.Normed.Module.FiniteDimension` (else
  `WeaklyLocallyCompactSpace` fails to synthesize for the compact-nbhd lemma).
