# MapConvergenceDeriv.lean — derivative-closure for `MapCInfConvOnCompacts` (P3 C-II-final-B2)

**Status (2026-06-13): DONE + verified** — focused check + targeted build green
(2323 jobs); both endpoints `#print axioms` clean = `[propext, Classical.choice,
Quot.sound]`.

## What landed

- `MapCInfConvOnCompacts.congr_eventually`: the tail-stable locality bridge;
  eventual equality on an open convergence set preserves full
  `C^∞`-on-compacts convergence.  This is the canonical analytic producer for
  finite slots whose live/dead status stabilizes only eventually.

This is the **Gap A producer (1)** the covariant-tower bridge `a ≥ 1` needs (see
`MetricPreconvDiag.md`, "Gap B remaining"): the analytic derivative-closure of the
Euclidean `C^∞`-on-compacts convergence notion.

The stop condition (definition does not retain derivative data) is **NOT**
triggered: `MapCInfConvOnCompacts U Φ Φinf` is `∀ K compact ⊆ U, ∀ p, MapCPConvOn
K p Φ Φinf`, and `MapCPConvOn K p` controls `mapDerivNorm r = ‖iteratedFDeriv ℝ r
(Φₖ - Φ_∞)‖` uniformly on `K` for every `r ≤ p` — i.e. the FULL Fréchet-derivative
tower is retained.  So the closure lemma is provable.

- `mapDerivNorm_fderivApply_le (r) (v) (hk hinf : ContDiff ℝ ∞ ·) : mapDerivNorm r
  (fun z => fderiv ℝ Φk z v) (fun z => fderiv ℝ Φinf z v) x ≤ ‖v‖ * mapDerivNorm
  (r+1) Φk Φinf x`.  Proof: `fderiv` is linear ⇒ `fderiv Φk z v − fderiv Φinf z v =
  fderiv (Φk − Φinf) z v` (`fderiv_sub`, pointwise, via a lambda-ascribed `have`
  since `rw [fderiv_sub]` won't unify the `fun y => …` with the `HSub` form); then
  `norm_iteratedFDeriv_clm_apply_const` peels off `· v` (`≤ ‖v‖ · ‖∇ʳ(fderiv g)‖`)
  and `norm_iteratedFDeriv_fderiv` raises the order (`‖∇ʳ(fderiv g)‖ =
  ‖∇ʳ⁺¹ g‖`).
- `MapCInfConvOnCompacts.fderivApply (h) (hΦ : ∀ k, ContDiff ℝ ∞ (Φ k))
  (hΦinf : ContDiff ℝ ∞ Φinf) (v) : MapCInfConvOnCompacts U (fun k z => fderiv ℝ
  (Φ k) z v) (fun z => fderiv ℝ Φinf z v)`.  At order `p`/`K` it consumes the
  order-`(p+1)` content of `h` with the threshold `ε/(‖v‖+1)`, then the pointwise
  bound closes `mapDerivNorm r (∂…) ≤ ‖v‖·mapDerivNorm (r+1) … ≤ ε`.

`ContDiff ℝ (∞ : WithTop ℕ∞)` matches the Brick-B engine output
(`exists_engine_frameCInfConv`'s `Φinf`/`Φ k` are `ContDiff ∞`), so the lemma is
directly applicable to the order-0 chart-component convergence.

## Lean gotchas
- `ContDiff.differentiable` takes `(hn : n ≠ 0)`, NOT `1 ≤ n` — at `∞` discharge
  with `by simp`.
- `norm_iteratedFDeriv_clm_apply_const` / `norm_iteratedFDeriv_fderiv` live in
  `Mathlib.Analysis.Calculus.ContDiff.Bounds` / `…/FTaylorSeries`; needed an
  explicit `import …ContDiff.Bounds` (not transitive through `MapConvergence`).
- `ContDiff.fderiv_right (hmn : m + 1 ≤ n)`: `(↑r) + 1 ≤ ∞` closes with
  `by exact_mod_cast le_top`.
- `‖v‖ * (ε/(‖v‖+1)) ≤ ε`: `← mul_div_assoc` (the goal is already `a*(b/c)`), then
  `div_le_iff₀` + `nlinarith`.

## Placement note (layering)
This is generic Euclidean analysis with NO manifold content; it belongs IN
`MapConvergence.lean` (the Euclidean AA layer).  It is in this adjacent file only
because `MapConvergence.lean` is currently owned/dirty in another session
(off-limits per P3_PLAN §3).  Candidate to fold back into `MapConvergence.lean`
when that file is free.

## Producer (3) — scalar convergence-algebra closures (2026-06-13, added)

The covariant-tower convergence induction also needs the algebra of `C^∞`-on-
compacts convergence (sum of terms, Christoffel-weighted terms).  Added (both
axiom-clean):

- `MapCInfConvOnCompacts.add (hΦ hΨ) (ContDiff hyps) : MapCInfConvOnCompacts U
  (fun k z => Φ k z + Ψ k z) (fun z => Φinf z + Ψinf z)`.  `mapDerivNorm r` of the
  sum-difference splits by `iteratedFDeriv_add_apply` + `norm_add_le`; threshold
  `ε/2 + ε/2`.  (Codomain `F` is an additive group ⇒ the rearrangement is `abel`,
  not `ring`.)
- `MapCInfConvOnCompacts.mulLeft (h) (hg : ContDiff ∞ g) (ContDiff hyps) :
  MapCInfConvOnCompacts U (fun k z => g z * Φ k z) (fun z => g z * Φlim z)` (scalar
  `ℝ`).  Leibniz `norm_iteratedFDeriv_mul_le` bounds `mapDerivNorm r (g·Φₖ)(g·Φlim)`
  by `∑_{i≤r} C(r,i)‖∇ⁱg‖·mapDerivNorm (r-i)`; `‖∇ⁱg‖ ≤ Bg` uniformly on the
  compact (`IsCompact.bddAbove_image` of `(continuous_iteratedFDeriv).norm`, summed
  over `i ≤ p`), `∑ C(r,i) = 2ʳ`; threshold `ε/(2ᵖ·Bg+1)`.  This is the closure for
  the fixed `gRef`-Christoffel correction terms.
- `MapCInfConvOnCompacts.sum (s : Finset ι) (∀ i, MapCInfConvOnCompacts U (Φ i)
  (Φinf i)) (ContDiff hyps) : MapCInfConvOnCompacts U (fun k z => ∑ i ∈ s, Φ i k z)
  (fun z => ∑ i ∈ s, Φinf i z)` — `Finset.induction` fold of `.add` (`ContDiff.sum`
  for partial-sum smoothness); the form the Christoffel/slot sums take.

## Gap B `a ≥ 1` — route now fully scoped (the remaining work is assembly)
Producers (1)=B2 fderiv-closure and (3)=add/mulLeft are DONE.  Producer (2) — the
rank-general covariant-step component formula — is **already provided by A2**:
`fderiv_chartRep_eq_towerStep` (MetricPreconv.lean) + the `towerStep` def give, for
any level `p`, that the chart-`fderiv` of the `p`-tower scalar `s_p^V` equals the
chart-rep of `towerStep = (next-order on cons-slots) + Σ Christoffel-corrected
lower-order scalars`.  Rearranged, the `(p+1)`-order component on cons-slots =
chart-`fderiv` of the `p`-scalar − Σ (lower-order scalars on Christoffel-modified
slots).

Induction for `componentConv_covDeriv_of_chartCInf` (IH at `C^∞`-on-compacts level,
over ALL slot tuples `V`):
- base `a = 0`: B0 (`exists_engine_frameCInfConv`) gives `MapCInfConvOnCompacts` of
  the order-0 chart components.
- step `a → a+1`: the directional term is the chart-`fderiv` of the `a`-scalar ⇒
  converges by **B2**; each Christoffel term is a fixed `gRef`-Christoffel times a
  lower-order scalar (after expanding the modified slot in the frame, using tensor
  multilinearity) ⇒ converges by **mulLeft** + **add** + IH.

**KEY de-risking insight (2026-06-13): the induction runs along the SINGLE
subsequence `φ` from B0 — NO new diagonal is needed.**  The reason: a covariant
component `s_p^V` is a FIXED (gRef-Christoffel) differential operator of order ≤ p
applied to the order-0 metric components.  Concretely:
- **All slot tuples from one frame.**  For arbitrary smooth `V`, expand each slot
  in the frame `V_c = Σ_i (cᵢ_c) frameVecᵢ` (smooth coefficient functions `cᵢ_c`);
  then `s_0^V = g.inner(V_0)(V_1) = Σ_{ij} cᵢ_0 cⱼ_1 · (g.inner(frameVecᵢ)(frameVecⱼ))
  = Σ (fixed smooth coeff) · (B0 frame component)`.  So `s_0^V` converges `C^∞`
  ALONG THE SAME `φ` as B0, via **mulLeft + add** — no extra engine run / diagonal.
- **Levels propagate along the same `φ`.**  A2's `towerStep` recursion takes
  `fderiv` (B2) + Christoffel multiplication (mulLeft) + sums (add) of the SAME
  converging sequence; so `s_{p+1}^V` converges `C^∞` along `φ` given `s_p^{·}`
  does (IH over all `V`).  The modified slots `leviCivita(Vₐ)(X)` are smooth fields
  ⇒ still covered by the (all-`V`) IH.

So C1b's `metricPreconv_gInf` (pointwise CLM only) is NOT the bottleneck — B0's
re-exposed `C^∞` engine output + the fixed-operator propagation give the whole
tower along one `φ`.  **ALL remaining sub-frontiers are pure assembly of CONFIRMED-PRESENT lemmas — no
missing API, no new producer, no new diagonal.**  (i) frame match — ALREADY DONE:
`frameVec x₀ i = tangentConstInChart x₀ (finBasis i)` (rfl, B0) and
`tangentConstInChart_eq_coordinateFrame_eventually`
(ConnectionCoefficients.lean:36) gives `frameVec x₀ i =ᶠ[𝓝 x₀] coordinateFrameAt
x₀ i`.  So B0's `frameVec` output IS the `coordinateFrameAt` data near `x₀`, and
the existing coordinate-frame covariant formulas (`nabla0SFun_two_eval_coordFrame`,
`nabla0SFun_eval_coordFrame_moving_raw`, `tensor0S_two_eval_coordFrame_sum`) apply
directly — NO frame-conversion lemma to prove.
(ii) the multilinear slot-expansion
(`leviCivita(frameₐ)(frame₀) = Σ Γᵏ frameₖ` + tensor linearity); (iii) the A2 germ
(`=ᶠ[𝓝 y]`) → neighbourhood-of-compact upgrade (local equality on each `y∈K`
patches to an open set ⊇ chart image of `K`, since `C^∞`-on-compacts convergence is
local); (iv) discharge of A2's per-point regularity hypotheses along the sequence.
After the bridge: finite-cover `hnorm` (via `metricDerivNorm_le_compSq_uniform`,
B-final-A) → `metricPreconvInf`.
