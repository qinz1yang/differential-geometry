# DiagExpDerivative.lean — notes

Step C center-of-mass, **target 2**: the zero-section derivative of `diagExp`.
Plan: `plan-on-taking-a-spicy-kitten.md` ("SEPARATE TASK — diagExp ... target 2").

## State: COMPLETE (sorry-free)

Verified by a real `lake build` (3764 jobs, **no sorry, axiom-clean, no warnings**;
final focused `lake env lean` also clean).

Main results:
- `diagExp_hasFDerivAt_zero` — in the tangent-bundle chart at `⟨p,0⟩` and the
  product chart at `diagExp ⟨p,0⟩ = (p,p)`, the chart-pushed `diagExp`
  (`chartedDiagExp`) has Fréchet derivative `(fst ℝ E E).prod (fst + snd)` at the
  zero-section chart point, i.e. `(δz₁, δz₂) ↦ (δz₁, δz₁ + δz₂)`.
- `unipotentCLE : (E×E) ≃L[ℝ] (E×E)` (`(z₁,z₂)↦(z₁,z₁+z₂)`, inverse `(w₁,w₂)↦(w₁,w₂-w₁)`).
- `diagExp_hasFDerivAt_zero_unipotent` — the same derivative packaged through
  `unipotentCLE` (the exact Banach-IFT input: a `ContinuousLinearEquiv`).

With target 1 (`diagExp_contMDiffAt_zero`, regularity) the Banach IFT now applies
near the zero section → the moving-base inverse section `q ↦ exp_q⁻¹(pt)` (NEXT task).

## Route (sum of two `id` partials — NOT a flow linearisation)

`chartedDiagExp := extChartAt (I.prod I) (diagExp ⟨p,0⟩) ∘ diagExp ∘ (extChartAt I.tangent ⟨p,0⟩).symm`.
- `chartedDiagExp_contDiffAt` from target 1 via `contMDiffAt_iff` + boundaryless
  `range (I.tangent) = univ` + `contDiffWithinAt_univ`.
- chart-inverse identifications: `extChartAt_tangent_zero_symm_zero_fiber`
  (`z.2 = 0` ⟹ inverse lands on the zero section over `(extChartAt I p).symm z.1`)
  and `extChartAt_tangent_zero_symm_at_base` (`z.1 = extChartAt I p p` ⟹ inverse =
  `⟨p, z.2⟩`, fibre = `z.2` via `chartFiberCoord_mk_self`).
- base partial: `chartedDiagExp (z₁, 0) = (z₁, z₁)` near `c = extChartAt I p p` (via
  `exp_q 0 = q` + chart cancellation) ⟹ `D.comp ((id).prod 0) = (id).prod (id)`.
- fibre partial: `chartedDiagExp (c, z₂) = (c, chartedExpIntrinsic z₂)` ⟹
  `D.comp ((0).prod id) = (0).prod (id)`, where `chartedExpIntrinsic` is the
  fixed-base intrinsic charted exp (`chartedExpIntrinsic_hasFDerivAt_zero` mirrors
  `LocalDiffeomorphism.chartedExpAt_hasFDerivAt_zero` with `mfderiv_expMapIntrinsic_at_zero`).
- assemble: `(a,b) = ((id).prod 0) a + ((0).prod id) b`, `D` linear ⟹ `D = fst.prod (fst+snd)`.

## 2026-06-26 — Banach IFT assembly LANDED (moving-base inverse section)

The IFT assembly (next task after target 2) is DONE, build-verified (`lake build`,
3764 jobs, **this file sorry-free**, `✔`; remaining sorries are pre-existing in
HopfRinow / ChainedFlowContinuity / Field — the project's existing frontiers, not
introduced here). New public API in this file:

- `diagExpInv g hEnorm p : M × M → TangentBundle I M` — the local inverse of
  `diagExp` near the zero section, `inner.symm ∘ (diagExpIFT).symm ∘ outer` with
  `inner = extChartAt I.tangent ⟨p,0⟩`, `outer = extChartAt (I.prod I) (p,p)`.
- `diagExpInv_center` — `diagExpInv g hEnorm p (p,p) = ⟨p,0⟩`.
- `diagExpInv_contMDiffAt` — `ContMDiffAt (I.prod I) I.tangent 1 (diagExpInv …) (p,p)`.
- `diagExp_diagExpInv` — `∀ᶠ y in 𝓝 (p,p), diagExp (diagExpInv … y) = y` (right inverse).
- `diagExpInv_proj` — `∀ᶠ y in 𝓝 (p,p), (diagExpInv … y).proj = y.1`.
- `expIntr_diagExpInv` — `∀ᶠ y in 𝓝 (p,p), exp_{(diagExpInv y).proj} (diagExpInv y).snd = y.2`.

So for `y = (q, pt)` near the diagonal, `(diagExpInv (q,pt)).snd ∈ T_q M` is the
inverse exponential `exp_q⁻¹(pt)` (`proj = q`, `exp_q (·) = pt`), smooth in `(q,pt)`.

### Route (germ/`eventually`, NOT the full `PartialDiffeomorph` mirror)

Deliberately avoided mirroring `LocalDiffeomorphism.lean`'s ~450-line explicit
`exists_nice_open_nhds` + `PartialDiffeomorph` construction. The germ-level route
(IFT `OpenPartialHomeomorph.eventually_right_inverse` + `ContMDiffAt`) is ~150 lines
and is exactly what the gradient consumer (`lbl411`, a pointwise/neighborhood
gradient identity) needs.
- `diagExpIFT := ContDiffAt.toOpenPartialHomeomorph chartedDiagExp_cdaOne
  diagExp_hasFDerivAt_zero_unipotent one_ne_zero` (C¹; level 1 like the template).
- `outer_center : extChartAt (I.prod I) (p,p) (p,p) = chartedDiagExp z₀` (the bridge:
  `inner.symm z₀ = ⟨p,0⟩` + `diagExp_zero_eq`); used in all three core lemmas.
- right inverse: `Φ.eventually_right_inverse` (in 𝓝 (chartedDiagExp z₀)) pulled back
  along `outer` (continuous, `outer (p,p) = chartedDiagExp z₀`) via
  `Tendsto.eventually`; then `chartedDiagExp (Φ.symm (outer y)) = outer y` is converted
  to a chart equation (`⇑Φ = chartedDiagExp` by `diagExpIFT_coe := rfl`; chartedDiagExp
  def-unfold `e2 := rfl`; `diagExp_zero_eq`) and the chart is cancelled by
  `(extChartAt …).injOn` (both points in source eventually:
  `extChartAt_source_mem_nhds` for `y`, `ContinuousAt.eventually_mem` for
  `diagExp (diagExpInv y)`).
- smoothness: 3-fold `ContMDiffAt.comp` — `contMDiffAt_extChartAt` (outer),
  `Φ.symm` via `to_localInverse` + `diagExpIFT_symm = localInverse` (`rfl`) +
  `contMDiffAt_iff_contDiffAt`, `inner.symm` via
  `contMDiffWithinAt_extChartAt_symm_range_self` + boundaryless `range I.tangent = univ`.

### Lean gotchas (IFT assembly)

- State the inverse facts at `(p,p)` (the user-facing point); the chart center inside
  `diagExpInv`'s def is `extChartAt (I.prod I) (p,p)` (matching, since
  `diagExp ⟨p,0⟩ = (p,p)`). The ONE place chartedDiagExp's center
  `extChartAt (I.prod I) (diagExp⟨p,0⟩)` meets it is `outer_center`/`e2`, bridged by a
  single `rw [diagExp_zero_eq]` (rewrites the bound `diagExp⟨p,0⟩`, NOT the opaque
  `diagExpInv`/`chartedDiagExp` constants — safe).
- `chartedDiagExp_cdaOne`: `chartedDiagExp_contDiffAt … 1 le_rfl` is at level `((1:ℕ):ℕ∞)`;
  `simpa using` normalises it to `ContDiffAt ℝ 1`. Reuse the SAME named lemma in
  `diagExpIFT` and the `localInverse`/`to_localInverse` calls so
  `Φ.symm = localInverse` holds by `rfl` (CompleteSpace is a `Prop` class ⇒ proof-irrelevant,
  so even differing instance paths stay defeq).
- `CompleteSpace E`/`CompleteSpace (E×E)` are inferred automatically (over ℝ,
  `FiniteDimensional.proper` is a registered instance ⇒ proper ⇒ complete); no `haveI`.
- `ContinuousAt.eventually_mem hf (hs : s ∈ 𝓝 (f x))`; `continuousAt_extChartAt x`;
  `Φ.eventually_right_inverse (hx : x ∈ Φ.target)` live in `OpenPartialHomeomorph`.
- `change`, not goal-changing `show` (style linter) — applies to the def-unfold goals in
  `outer_center` / `diagExpInv_center`.

## Lean gotchas

- The first background agent on this DIED mid-proof (process exit, not a proof wall);
  it had landed the helpers + the two chart-inverse identifications + the `ContDiffAt`
  (the hardest infra). The assembly was finished by hand.
- `MinimizingGeodesic.lean`/`expMapIntrinsic_zero` and `extChartAt_tangent_zero_apply_chartFiber`
  carry `[T2Space (TangentBundle I M)]` as a section var ⟹ put the full instance set on
  every decl; `chartFiberCoord*` lemmas live in `…Riemannian.Geodesic` (must `open`).
- `ContDiffAt.differentiableAt` wants the smoothness `≠ 0` (`↑↑n ≠ 0`), via
  `Nat.one_le_iff_ne_zero.mp hn`.
- In the partials, `rw [diagExp_apply]` would hit the chart-CENTRE `diagExp ⟨p,0⟩`
  first — compute the inner `diagExp` value in a separate `have`, then `rw [hinner,
  diagExp_zero_eq, extChartAt_prod]`.
- `HasFDerivAt.comp` higher-order-unifies `f x` with the point and leaves the OUTER
  function a metavar if you ASCRIBE the result type — use `have hc1 := hD.comp c haff`
  (no ascription; `hD`'s concrete type pins the outer function), then
  `congr_of_eventuallyEq … |>.unique`.
- `ContinuousLinearMap.id_ne_zero` does NOT exist — derive `id ≠ 0` via `DFunLike.congr_fun`
  on a nonzero vector (`Nontrivial E` from `Module.nontrivial_of_finrank_pos`).
- `change`, not goal-changing `show` (style linter); `simp` (not `simp [Prod.ext_iff]`,
  flagged unused) closes the prod equalities.

## `diagExpInv_contMDiffAt_order` (order `n`, `lbl430`(ii)) DONE 2026-07-05 — sorry-free, in `lake build`
The order-`n` companion of `diagExpInv_contMDiffAt`. Statement: `(n : ℕ) (hn : 1 ≤ n) ⟹ ContMDiffAt
(I.prod I) I.tangent (n:ℕ∞) (diagExpInv g hEnorm p) (p,p)`. Proof is a verbatim order-bump of the
order-1 proof; the ONLY changes are the ContDiffAt order on the inner symm and the outer extChartAt.
- **KEY (why order is free):** `ContDiffAt.localInverse`/`to_localInverse` are defined from the
  *proof-irrelevant* `HasStrictFDerivAt`, so `(diagExpIFT g hEnorm p).symm =
  (chartedDiagExp_contDiffAt g hEnorm p n hn).localInverse (diagExp_hasFDerivAt_zero_unipotent … 1
  le_rfl) hn0 := rfl` holds at ANY order `n` (the order-1 `diagExpIFT` and the order-`n` localInverse
  are the same PartialHomeomorph up to proof irrelevance). Then
  `(chartedDiagExp_contDiffAt … n hn).to_localInverse … hn0` gives the `C^n` symm.
- `hn0 : ((n:ℕ∞):WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)` — the ContDiff order is
  `WithTop ℕ∞`, so `(n:ℕ∞)` is the DOUBLE coercion `↑↑n`; a single-coe `Nat.cast_ne_zero` mismatches.
- Import graph checked FIRST (planner instruction): the C∞/order-`n` forward `chartedDiagExp` facts
  (`chartedDiagExp_contDiffAt` already stated at general `n`) are NOT downstream of DiagExpDerivative
  (no Step-B LocalDiffeomorphism↔OffZero cycle), so the bump is IN-PLACE, no downstream-file needed.

## 2026-07-10 — finite-order off-diagonal branch domain

- Added `exists_diagInvDom`. For every finite `n ≥ 1` it exposes an open
  neighborhood of `(p,p)` on which the fixed, totalized `diagExpInv` branch is
  genuinely `C^n`, is a right inverse of `diagExp`, projects to the moving base,
  and satisfies the intrinsic exponential identity pointwise.
- This closes the former API problem that all IFT branch data were private: an
  off-diagonal consumer can now ask for membership in a real branch domain.
- The domain may depend on `n`. Mathlib's `ContMDiffAt ∞` convention gives
  order-dependent neighborhoods, so this does not claim one common open
  `C^∞` region.
- Focused verification and the targeted module build passed. The next analytic
  frontier is a common `C^∞` branch domain, requiring either a fixed-box `∞`
  geodesic-flow theorem or a deliberate Step-C scale shrink.

## 2026-07-10 — one common C-infinity branch domain

- Added the private fixed-neighborhood producers `exists_chartDiagInf` and
  `exists_chartInvInf`.  On the rescaled preimage of the fixed chart-flow ball,
  `chartedDiagExp` agrees with the explicit map `z ↦ (z.1, G (R z))`, hence is
  genuinely `C^∞` on one open set.
- The inverse proof keeps the existing `diagExpIFT` branch.  Continuity of
  `fderiv` and openness of the continuous-linear-equivalence locus provide a
  smaller source on which every derivative is invertible; no second inverse or
  branch-uniqueness theorem is introduced.
- Added public `exists_diagInvDom_inf`: one open neighborhood of `(p,p)` carries
  `ContMDiffOn ∞` for `diagExpInv`, its right-inverse identity, base projection,
  and intrinsic exponential identity.
- Focused verification and the targeted module build passed.  The common
  all-order inverse domain is no longer a frontier; the next Step-C issue is
  uniform finite-hat/configuration containment in this domain and in the named
  realized-exponential radii.

## 2026-07-10 - shared unipotent linearization

- `unipotentCLE` is now a compatibility alias for
  `PhaseFlow.freeDiagCLE`.  Existing derivative and IFT proofs continue to check,
  while the quantitative phase endpoint and the qualitative `diagExpIFT` branch
  now refer to the same continuous linear equivalence.
- This alias does not yet identify the two inverse branches.  That still requires
  the cross-model normal-coordinate endpoint theorem and branch compatibility.

## 2026-07-10 - zero-section left inverse germ

- `diagExpInv_diagExp` now exposes the missing source-side inverse identity:
  near `⟨p, 0⟩`, applying `diagExp` and then the existing `diagExpInv` recovers
  the original tangent vector.
- The proof pulls `diagExpIFT.eventually_left_inverse` back through the
  tangent-bundle chart.  Unlike the target-side right-inverse proof, it needs
  only the tangent chart source germ; no product-chart injectivity argument is
  required.
- Focused verification passed without warnings or placeholders.
- This is a pointwise germ, not a sequence-uniform quantitative radius.  It
  identifies any transported quantitative branch with `diagExpInv` on their
  common neighborhood, but a uniform `StepB1RawInput` domain still requires an
  explicit uniform containment/refactoring argument.

## 2026-07-11 - explicit standard selected branch

- `stdBranch` now packages the existing qualitative `diagExpInv` construction
  as a `DiagInvBranch`.  Its manifold-level open partial homeomorphism is the
  chart transport of the private Banach-IFT branch, with its target restricted
  to the already checked common `C^infinity` domain.
- The restriction is on the target side, so the inverse total function remains
  exactly `diagExpInv`; `std_inv_eq` exports that compatibility globally.
- The branch forward equality with intrinsic `diagExp` is derived from the
  partial-homeomorphism left inverse and the existing right-inverse theorem on
  the restricted target.  No radius is extracted from the qualitative branch.
- Focused verification passed without warnings or local `sorry`s.  The generic
  standard-branch instance is 100% complete; it is compatibility machinery and
  does not complete the still-unstated quantitative HCG branch/readout theorem
  or the `StepB1RawInput` producer.

## 2026-07-23 - component-local standard branch

- Removed the accidental file-wide `ConnectedSpace M` assumption.  The complete
  source, including `exists_stdBranch`, `stdBranch`, and `std_inv_eq`, passes
  focused verification without it.
- This is an assumption cleanup only: the selected branch remains qualitative
  and component-local.  It supplies no Calabi radius, no quantitative support
  estimate, and no new HCG endpoint theorem.
