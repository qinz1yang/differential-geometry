# BoundaryDerivLimit.lean — derivative-limit theorem at a closed endpoint

Verified, sorry-free, banked (`lake build`, 2033 jobs). The foundational 1-D analytic step of the
parabolic boundary-regularity leverage ("corollary (b)") in the Ricci-flow `hglue` route.

## Theorem

`hasDerivWithinAt_Ici_of_tendsto_nhdsGT` : for `f : ℝ → F` (`F` a real normed space), `a < b`,
`f` continuous on `[a,b]`, differentiable on `(a,b)` with derivative `f'`, and `f' → L` as `t → a⁺`
(`Tendsto f' (𝓝[>] a) (𝓝 L)`), then `HasDerivWithinAt f L (Ici a) a` (right-derivative `L` at `a`).

This is the classical derivative-limit theorem. **Mathlib has only the uniform-limit-of-sequences
forms** (`hasFDerivAt_of_tendstoUniformlyOn` etc.), NOT this single-function form, so it had to be
built. No direct `ContDiffOn`-closure/extension lemma exists in Mathlib either.

## Proof route (what worked)

For `a < s < t < b`, apply the mean-value inequality `norm_image_sub_le_of_norm_deriv_right_le_segment`
(MeanValue.lean:308 — continuity on `[s,t]` + right-derivative on the interior `Ico s t`) to
`g = fun x => f x - x•L`, giving `‖f t − f s − (t−s)•L‖ ≤ ε·(t−s)` when `‖f'−L‖ ≤ ε` on `(a,a+η)`.
Let `s → a⁺` via `le_of_tendsto_of_tendsto` (continuity of `f` at `a` from the right). Convert to the
slope limit via `hasDerivWithinAt_iff_tendsto_slope` + `Metric.tendsto_nhdsWithin_nhds` (use `ε/2` to
beat the strict `<`).

## Lean lessons (3 iterations to green)

- `𝓝[>] a ≤ 𝓝[Icc a b] a` is NOT `nhdsWithin_mono` (`Ioi a ⊄ Icc a b`). Use `nhdsWithin_le_of_mem`
  with `Icc a b ∈ 𝓝[>] a`, proved from `Ioo a b ∈ 𝓝[>] a` =
  `inter_mem_nhdsWithin (Ioi a) (Iio_mem_nhds hab)` rewritten by `Set.Ioi_inter_Iio`.
- `Ici a \ {a} = Ioi a` is `Set.Ici_diff_left` (NOT `omega` — these are reals).
- `le_of_tendsto_of_tendsto'` wants a GLOBAL `∀x` bound; use the unprimed `le_of_tendsto_of_tendsto`
  for an `≤ᶠ` (eventual) bound + `filter_upwards`.
- The slope `smul` identity `(t−a)⁻¹•(f t−f a) − L = (t−a)⁻¹•(f t−f a−(t−a)•L)`: prove it stated with
  the COMPOUND side on the left (`rw [smul_sub, smul_smul, inv_mul_cancel₀, one_smul]`), then use `←`,
  so `smul_sub` matches the intended subterm first.
- `(continuous_id.tendsto a).mono_left nhdsWithin_le_nhds` for `Tendsto (·) (𝓝[>] a) (𝓝 a)`.

## Remaining for corollary (b) (the full leverage)

This primitive is the time-direction `C¹` core. The full "spatial-`C∞`-convergence + the evolution
`∂ₜG = Φ(jet²ₓG)` ⇒ `G` is `C∞` up to the closed endpoint" still needs: (1) the `Cⁿ`-up-to-endpoint
upgrade (iterate this primitive over orders, via `HasFTaylorSeriesUpToOn` on the closed slab);
(2) the joint `(t,x)` version; (3) the convergence-from-evolution argument (the evolution makes the
time-derivatives spatial-expressible, so spatial convergence ⇒ all derivatives converge). These reduce
Gate-L and the endpoint time-regularity to plain spatial `C∞` convergence (what Shi/Arzelà–Ascoli give).
See `hglue-splice-and-gates.md`.
