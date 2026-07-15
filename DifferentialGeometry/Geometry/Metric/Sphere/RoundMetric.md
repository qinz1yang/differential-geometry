# RoundMetric.lean — notes

Plan: `plan-on-taking-a-spicy-kitten.md`, step 2. Role: the round metric on `Sⁿ`,
foundation for the constant-curvature (homogeneity) and quotient-descent steps.

## State: COMPLETE (sorry-free)

`roundMetric` is fully proven and VERIFIED GREEN (`lake env lean`, exit 0, no
`sorry`/warnings/errors). The `contMDiff` field is closed. See
"`contMDiff` — how it was closed" below.

Done & checked:
- `dIncl x : T_x(Sⁿ) →L[ℝ] E` — the inclusion differential with codomain
  **ascribed to `E`** (crucial: `TangentSpace 𝓘(ℝ,E) y` is a type synonym for `E`
  that does NOT inherit `Inner`/`InnerProductSpace`; ascribing to `E` gives the
  inner-product instances).
- `roundInner x v w = ⟪dIncl x v, dIncl x w⟫` (`roundInner_apply`), `roundInner_symm`,
  `dIncl_ne_zero` (from `mfderiv_coe_sphere_injective`), `roundInner_pos`.
- `roundMetric` with `inner/symm/pos/isVonNBounded` fields (isVonNBounded via
  `posDef_isVonNBounded`), `roundMetric_inner`.

## `contMDiff` — how it was closed

Closed via three `private` helpers placed immediately above `roundMetric`
(`flatInner_comp_incl_contMDiff`, `dIncl_apply_section_contMDiff`) plus the field
proof. Two deviations from the originally planned route mattered:

- **Reused Mathlib's `riemannianMetricVectorSpace E` instead of hand-rolling the
  flat-metric trivialization `simp`.** The hand-rolled `flatInner_contMDiff`
  (mirroring VectorBundle/Riemannian.lean:101–106) got stuck: after
  `convert contMDiffAt_const`, the leftover trivialization goal carried a
  star-vs-non-star coercion side goal (`e_18 : (E →L[ℝ] E →L[ℝ] ℝ) = (E →L⋆[ℝ] …)`,
  because `innerSL ℝ : E →L⋆[ℝ] E →L[ℝ] ℝ`), and the suggested `simp` lemmas
  (`hom_trivializationAt_apply`, `inCoordinates`, `linearMapAt_apply`) were
  reported *unused* — the tangent-bundle Hom trivialization needs a different
  normal form. The clean fix: `Mathlib.Geometry.Manifold.Riemannian.Basic`
  already provides `riemannianMetricVectorSpace F` (fiber inner = `innerSL ℝ`), so
  `(riemannianMetricVectorSpace E).contMDiff.of_le le_top |>.comp contMDiff_coe_sphere`
  gives the pulled-back flat section directly. **This required adding one import:
  `Mathlib.Geometry.Manifold.Riemannian.Basic`** (it imports VectorBundle.Riemannian,
  not vice-versa, so it was not transitively available). Carry `ψ` and the scalar
  bridge as `(riemannianMetricVectorSpace E).inner (↑x)` (defeq `innerSL ℝ`) so the
  `clm_bundle_apply₂` and `rfl` bridges fire.
- **`clm_bundle_apply₂` produces a section over the TARGET bundle's base `E`, not
  the sphere.** The target bundle `E₃ = fun _ : E => ℝ` lives over `E`, so the
  result is `ContMDiff (𝓡 n) (𝓘(ℝ,E).prod 𝓘(ℝ,ℝ)) ∞ (fun x => ⟨↑x, scalar⟩)` with
  base map `ι` and `Bundle.Trivial E ℝ` — NOT `(𝓡 n).prod` / `Trivial (sphere) ℝ`.
  Declaring `h_total` with the sphere base gave a type mismatch. Scalar extraction
  via `contMDiffAt_totalSpace … |>.2` still works (trivial-bundle fiber = scalar).

Other instance needs: `haveI : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n`
and `haveI : CompactSpace (sphere (0:E) 1) := Metric.sphere.compactSpace _ _` at the
top of the field proof — `cotangentCov_clmSection_smooth_aux` requires
`[SigmaCompactSpace M] [T2Space M]`, both derived from `CompactSpace`+metric, and
`ProperSpace E` (for `CompactSpace`) needs the explicit `FiniteDimensional`.
Also: `convert contMDiffAt_const` needs its model spaces / `n` / `M` / `x` pinned
explicitly when used standalone (otherwise `convert` falls back to an `↔` between
two `ContMDiffAt` props and `ext` fails).

## Original frontier plan (kept for reference)

Mathematically trivial (pullback of the flat ambient metric along the smooth
embedding `ι`), but delicate in Lean's bundle framework. Route (mirror
`Geometry/Metric/Pullback.lean` `Diffeomorph.pullbackMetric.contMDiff`, lines
175–230, and `mfderiv_apply_section_smooth_along_diffeo`, 149–163), adapted
cross-model (`M = sphere`/`𝓡 n`, `N = E`/`𝓘(ℝ,E)`), with `ι = contMDiff_coe_sphere`:

1. `cotangentCov_clmSection_smooth_aux` (Bundle/ClmSectionSmooth.lean:44) twice ⇒
   reduce to: for global smooth tangent sections `Y W`, smoothness of
   `x ↦ roundInner x (Y x) (W x)`.
2. Pushforward sections `x ↦ ⟨ι x, mfderiv ι x (Y x)⟩` of `T(E)` along ι, smooth
   via `(contMDiff_coe_sphere).contMDiff_tangentMap (le_refl _) |>.comp Y.contMDiff`.
3. Combine with the ambient inner product. PROBED FACT: the flat Riemannian
   instance `IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E))` is
   **NOT inferrable**, so `ContMDiff.inner_bundle` does not apply out of the box.
   Use `ContMDiff.clm_bundle_apply₂` with an explicit flat metric section
   `hg : x ↦ ⟨ι x, innerSL ℝ⟩` — proven by mirroring Mathlib's trivial-bundle
   Riemannian instance proof (VectorBundle/Riemannian.lean:101–106) adapted to the
   tangent bundle of `E`. (Alternative: extract the `E`-valued pushforward
   `x ↦ mfderiv ι x (Y x)` and use `innerSL`/`ContMDiff.clm_apply` — but extracting
   from the `T(E)` section needs the model-space tangent-bundle trivialization,
   also fiddly.)
4. Extract the scalar (`contMDiffAt_totalSpace`, `.2`) and lift to the trivial
   `ℝ`-bundle section (`contMDiffAt_section` + `congr_of_eventuallyEq`).

`roundMetric` now typechecks as a complete, sorry-free `SmoothRiemannianMetric`
object, so downstream files (O(n) action, curvature) can be built on it.
