# QuotientDescent.lean — round-metric descent to a finite quotient

## Status: COMPLETE, sorry-free (2026-07-07). Both frontiers discharged + Hamilton assembled.

Step D of the spherical-space-form quotient descent (plan `plan-on-taking-a-spicy-kitten.md`,
"Steps 6–7"). `QuotientDescent.lean` is sorry-free & axiom-clean (`[propext, Classical.choice,
Quot.sound]`, real `lake-locked build`). Brick 4 (Hamilton assembly) landed:
`spaceForm_const_metric` is proved (sorry-free); `ham3_space_box` is the lone remaining sorry of
that pair (the hard topological direction). Both Hamilton consumers (`HamiltonPositiveRicciAdapter`,
root) build green.

## Brick 3 + 4 execution notes (2026-07-07)

**Brick 3 (`gQuot_constPosSec`, c=1).** Added a general metric-ext helper
`SmoothRiemannianMetric.ext'` (one data field `inner`; `symm`/`pos`/`isVonNBounded`/`contMDiff`
are Props → `obtain ⟨i,…⟩; obtain ⟨i',…⟩; subst (funext …); rfl`, Prop fields closed by
definitional proof irrelevance). Canonical home is `Geometry/Metric/Basic.lean`; kept LOCAL in
this file to avoid a full-tree rebuild (noted for later promotion). Calc:
`metricRm04StdAt gQuot x = (Step B restrictOpen, symm) = (rw hmetric: gQuot.restrictOpen W = h via
ext') = (Step C pullback_localDiffeo) metricRm04StdAt round (toSphere lift) = (roundMetric_sec_value)
Gram`, then `hbridge` transports each Gram entry back through `pullback_inner_eval`. KEY LESSONS:
(i) `roundMetric.inner q = roundInner q` and the base-point `↑(S.s ⟨x⟩) = S.toSphere ⟨x⟩` are
DEFEQ but rw's trailing rfl uses *reducible* transparency and won't close them → append an explicit
`rfl` (default transparency) after each such rw block (in `hC` and `hbridge`). (ii) `metricRm04StdAt`
needs only `[IsManifold ∞]` (+ SigmaCompact/T2/Boundaryless, all global for the sphere) on its
manifold — the `IsManifold 1/(∞+1)` come only from the restrictOpen/pullback lemmas via the
`SectionWitness` instance fields; but the curvature value still needs
`haveI : NeZero (finrank (EuclideanSpace ℝ (Fin n)))` (via `finrank_euclideanSpace_fin`).
(iii) import `Curvature.Sphere.ConstCurvature` for `roundMetric_sec_value`.

**Brick 4 (Hamilton, `HamiltonPositiveRicci.lean`).** Replaced the old metric-space model
(`RoundSphere3`/`SphereOrbitQuotient`/`action_isometric`/`quotientHomeomorph`) with the minimal
consumer form `structure SphericalSpaceFormQuotientModel … where data : Geometry.RoundQuotientData
(EuclideanSpace ℝ (Fin 4)) 3 ; equiv : N ≃ₘ⟮I,𝓡 3⟯ data.Q`, plus a local
`instance : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1)`. `spaceForm_const_metric` gains
`(hM : Closed3Manifold)`; witness = `Diffeomorph.pullbackMetricCross data.gQuot equiv`, per point
`rw [metricRm04Std_pullbackCross, gQuot_constPosSec, ← pullbackMetricCross_inner ×3]`. KEY LESSONS:
(i) `RoundQuotientData` bundles `Q : Type*` existentially → its use as a field type leaves
UNINFERABLE universe metavars ("failed to infer universe levels") → pin with
`Geometry.RoundQuotientData.{0,0,0} …`. (ii) `IsManifold I 1 M` is a GLOBAL instance from
`[IsManifold I ∞ M] + LEInfty 1` (Basic.lean:852) — do NOT write `IsManifold.of_le le_top`, which
targets `⊤ = ω` (analytic) not `∞` and fails. `BoundarylessManifold I M` auto-derives from
`[I.Boundaryless]` (just `haveI : I.Boundaryless := hM.2.2.1`). (iii) `metricRm04Std_pullbackCross`
needs the F-side `haveI : NeZero (finrank (EuclideanSpace ℝ (Fin 3)))`. (iv) accepted ripple:
`ham3_space_box` (still `sorry`) must now PRODUCE the stronger witness (RoundQuotientData +
cross-model equiv) — statement-type change only.

## What is REAL (compiles, no sorry)

- `SectionWitness E n Q proj x` — a covering local section through `x`: open `W ⊆ Q`, open
  `V ⊆ S`, a diffeo `s : W ≃ₘ⟮𝓡n,𝓡n⟯ V` right-inverse to `π`, BUNDLING the manifold
  instances on `W`,`V` (`SigmaCompact`/`T2`/`Boundaryless`/`IsManifold 1`/`IsManifold (∞+1)`)
  as instance fields — these are NOT auto for open subsets of a compact manifold, so they are
  genuine witness data.
- `RoundQuotientData E n` — the descent inputs: quotient `Q` (𝓡n-manifold, T2, σ-compact,
  boundaryless), finite `Γ`, orthogonal rep `ρ : Γ →* (E ≃ₗᵢ E)`, `proj : S → Q` smooth +
  Γ-invariant (`proj_smul`) + orbit-injective (`proj_eq_imp`), and `section_at : ∀ x, SectionWitness … x`.
- `gm x := (pullbackMetric (round.restrictOpen (section_at x).V) (section_at x).s).inner ⟨x, mem⟩`
  — the descended fiberwise form, via the chosen section. `gm_symm`, `gm_pos` proved from the
  pullback metric's symm/pos.
- `gQuot : SmoothRiemannianMetric (𝓡n) Q` via `smoothMetric_of_localCoeff` (+ `gQuot_inner`).

## The 2 remaining sorries (the genuine math)

1. `gm_coeff` — local-frame components of `gm` are `ContMDiffOn` each trivialization base set.
   Route (DESIGNED, de-risked): near `x₀`, `gm =ᶠ (pullbackMetric round (section_at x₀).s).inner`
   (a `SmoothRiemannianMetric`, hence smooth frame components). Agreement at `x` (using its own
   section) is round's Γ-invariance via the POINTWISE relation `mfderiv s' = dγ ∘ mfderiv s`
   between the two section differentials — from `s'(x)=γ·s(x)` (orbit, `proj_eq_imp`) +
   differentiating `proj∘(γ·)=proj` (`proj_smul`, `mfderiv_comp`), with `mfderiv s = (dπ)⁻¹`
   from `proj∘s=id`. NO covering-space unique-lifting needed. Then `roundInner_sphereDiffeo`.
2. `gQuot_constPosSec` — constant curvature `c=1`. Route: at `x`, `gQuot =ᶠ pullbackMetric round s`
   (from 1's local agreement + `gQuot_inner`), so germ-locality (`metricRm04StdAt_restrictOpen`,
   Step B) + `metricRm04StdAt_pullback_localDiffeo` (Step C) reach `roundMetric` at the lift, then
   `roundMetric_sec_value` (c=1); transport the Gram shape through `pullbackMetric_inner`.

## Gotchas (fixed while building the skeleton)

- `q̄` (q + U+0304 combining macron) is NOT a valid Lean identifier char → "expected token"
  parse errors. Use `x` for quotient points.
- `gm` returns DATA, so `section_at` must be DATA (`SectionWitness`/`Σ'`), not a `Prop` `∃`
  (`Exists.casesOn` can only eliminate into `Prop`).
- Parenthesize `(round.restrictOpen V)` as one unit inside `pullbackMetric (…) s`, else the
  application groups `restrictOpen`'s arg as `pullbackMetric`'s.
- `SigmaCompactSpace ↥V` / `↥W` for open submanifolds are NOT synthesizable (bumping heartbeats
  → whnf timeout) — bundle them as `SectionWitness` instance fields.

## EXECUTION PLAN — finish the 2 sorries + Hamilton assembly (Fable, 2026-07-06)

Self-contained brick plan for executor sessions. Verified context: Steps A/B/C all
build-verified sorry-free (`PullbackCross.lean` + `PullbackNaturalityCross.lean`
= cross-model `pullbackMetricCross`/`metricRm04Std_pullbackCross`;
`RestrictOpenRm04.lean` = `metricRm04StdAt_restrictOpen`;
`PullbackNaturalityLocal.lean` = `metricRm04StdAt_pullback_localDiffeo`); this file's
skeleton compiles with exactly 2 sorries (`gm_coeff`, `gQuot_constPosSec`).
Feasibility: every step below reduces to verified lemmas + one bounded new argument
(the pointwise section-differential intertwining); no open mathematical question.

### Brick 1a — Opens ContMDiffAt transfer lemma (independent; search FIRST)

Statement (name ≤20 chars, e.g. `contMDiffAt_of_opens`):
`(U : Opens M) (x : U) : ContMDiffAt I I' k (fun r : U => f ↑r) x → ContMDiffAt I I' k f ↑x`.
SEARCH Mathlib first: `rg -n "subtypeRestr|Opens.*contMDiff|contMDiff.*Opens|IsOpenEmbedding.*contMDiff" .lake/packages/mathlib/Mathlib/Geometry/Manifold` — a form of this may exist
(also try `IsLocalDiffeomorph`, `contMDiffAt_subtype_iff`). If absent, prove by chart germs:
`Opens.instChartedSpace` makes `chartAt H (x:U)` the `subtypeRestr` of `chartAt H (↑x:M)`, so
both sides' `contMDiffAt_iff` chart-composites have the same germ at the image point (U open).
Home: `Geometry/Metric/OpenSubtype.lean` or a small new file next to it. ~40–70 ln. Fallback
is bounded; if 3 routes fail, STOP and report (this gates Brick 2 only).

### Brick 1b — section calculus + `gm_locallyEq` (the R2 core, in THIS file)

All statements in scalar/applied form (avoid CLM-equality coercion traps). Tangent fibers of
`Opens` subtypes are model fibers (defeq) — reuse the OpenSubtypeNaturality idioms
(`mfderiv_subtype_val`, `restrictOpenTangentField_apply`) for every identification.

1. `SectionWitness.toSphere (S) : S.W → sphere (0:E) 1 := fun r => ((S.s r : S.V) : _)`;
   `toSphere_contMDiff` (comp of `S.s.contMDiff` with `contMDiff_subtype_val`);
   `toSphere_proj : proj (S.toSphere r) = ↑r` (= `S.isSec`).
2. `pullback_inner_eval (S) (hx : x ∈ S.W) (v w)`:
   `(pullbackMetric ((roundMetric).restrictOpen S.V) S.s).inner ⟨x,hx⟩ v w
     = roundInner (S.toSphere ⟨x,hx⟩) (mfderiv _ _ S.toSphere _ v) (mfderiv _ _ S.toSphere _ w)`.
   Route: `pullbackMetric_inner` + `restrictOpen_inner` + `mfderiv (val ∘ s) = mfderiv s`
   (`mfderiv_comp` + `mfderiv_subtype_val` on `Opens (sphere)`).
3. `dproj_sec (S) (r)` : `mfderiv proj (S.toSphere r) ∘L mfderiv S.toSphere r = .id` —
   differentiate `proj ∘ S.toSphere = Subtype.val` (funext `toSphere_proj`; `mfderiv_comp`,
   `proj_smooth`, `mfderiv_subtype_val` on `Opens Q`).
4. `dproj_inj (S) (r) : Function.Injective (mfderiv proj (S.toSphere r))` — right inverse (3)
   ⟹ surjective; both fibers are defeq the SAME model space `EuclideanSpace ℝ (Fin n)`
   (`show` to the endo form), so `LinearMap.injective_iff_surjective` closes it.
5. `sections_agree (D) {x₁ x} (hx : x ∈ (D.section_at x₁).W)`: with `S₁ := D.section_at x₁`,
   `Sₓ := D.section_at x`, `q := Sₓ.toSphere ⟨x,Sₓ.mem⟩`, `q₁ := S₁.toSphere ⟨x,hx⟩`:
   `∃ γ, q₁ = sphereDiffeo (D.ρ γ) q ∧ ∀ v, mfderiv _ _ S₁.toSphere ⟨x,hx⟩ v
     = mfderiv _ _ (sphereDiffeo (D.ρ γ)) q (mfderiv _ _ Sₓ.toSphere ⟨x,Sₓ.mem⟩ v)`.
   γ from `proj_eq_imp q q₁` (both proj to `x` by `toSphere_proj`). Differentials: apply (3)
   to S₁, and to `sphereDiffeo (ρ γ) ∘ Sₓ.toSphere` (whose proj-composite is also `val`, via
   `proj_smul`); both are right-inverses of the SAME `mfderiv proj q₁`; conclude by
   `dproj_inj` applied vectorwise. POINTWISE — γ may depend on x; no unique lifting,
   no local constancy, no connectedness.
6. **`gm_locallyEq (D) {x₁ x} (hx) (v w)`:
   `D.gm x v w = (pullbackMetric ((roundMetric).restrictOpen S₁.V) S₁.s).inner ⟨x,hx⟩ v w`.**
   = `gm`-def (own section, `rfl`-unfold) + (2) on both sections + (5) + `roundInner_sphereDiffeo`.

Fiddly but designed; ~120–200 ln. Failure signal: if the (4)/(5) defeq wrangling on
`T_{⟨x⟩}↥W` vs `T_x Q` resists after `show`-to-model-fiber normalization, report the exact
stuck goal (do NOT introduce transport `▸`-chains).

### Brick 2 — `gm_coeff` (discharges sorry 1; needs 1a + 1b)

`baseSet` is open ⟹ reduce `ContMDiffOn` to `ContMDiffAt` at each `x₁ ∈ baseSet`.
Take `S₁ := D.section_at x₁`, `h₁ := pullbackMetric ((round).restrictOpen S₁.V) S₁.s`
(a genuine `SmoothRiemannianMetric (𝓡 n) ↥S₁.W`). By Brick 1a it suffices to show
ContMDiffAt on `↥S₁.W` at `⟨x₁, S₁.mem⟩` of `r ↦ D.gm ↑r (frameVec x₀ i ↑r) (frameVec x₀ j ↑r)`,
which by `gm_locallyEq` (funext on all of `↥S₁.W` — no filter needed) equals
`r ↦ h₁.inner r (frameVec x₀ i ↑r) (frameVec x₀ j ↑r)`. Close with
`CovariantDerivative.metric_inner_contMDiffAt h₁ hf hf` (pattern: OpenSubtypeNaturality:206),
where `hf : ContMDiffAt` of `T% (fun r : ↥S₁.W => frameVec x₀ i ↑r)` at `⟨x₁⟩` comes from:
ambient localFrame smoothness on `baseSet` (`isLocalFrameOn_localFrame_baseSet` — its
`IsLocalFrameOn` carries the ContMDiffOn; `frameVec = e.localFrame b i` on baseSet via
`localFrame_apply_of_mem_baseSet` + `basisAt`/`symmL_apply`, the Sections.lean:43 rewrite)
composed with `contMDiff_subtype_val`. ~60–100 ln.

### Brick 3 — `gQuot_constPosSec` (discharges sorry 2; needs 1b, NOT 1a/2)

Helper first: `SmoothRiemannianMetric` extensionality (`ext'` : equal `inner` ⟹ equal) —
grep `Geometry/Metric/Basic.lean` for an existing ext lemma; else add there (all non-`inner`
fields are Props; the `pullbackMetric_round_eq` proof's `congr 1` pattern shows the shape).
Then at `x`, `S := D.section_at x`, `h := pullbackMetric ((round).restrictOpen S.V) S.s`:
- `hrestr : D.gQuot.restrictOpen S.W = h` — `ext'` + `restrictOpen_inner` + `gQuot_inner` +
  `gm_locallyEq` (at every `r : S.W`).
- calc: `metricRm04StdAt gQuot x X Y Y X
    = metricRm04StdAt (gQuot.restrictOpen S.W) ⟨x,S.mem⟩ …` (Step B, symm)
  `= metricRm04StdAt h ⟨x⟩ …` (rw `hrestr`)
  `= metricRm04StdAt round (S.toSphere ⟨x⟩) (ds X)(ds Y)(ds Y)(ds X)`
    (`metricRm04StdAt_pullback_localDiffeo round S.V S.W S.s` — the exact Step C shape;
    W/V instances are the `SectionWitness` fields, sphere instances by the
    ConstCurvature.lean:48–53 `haveI` pattern: `NeZero (finrank …)` via
    `finrank_euclideanSpace_fin`, `IsManifold 1`/`(∞+1)` via `instIsManifoldSphere.of_le le_top`)
  `= Gram of roundInner at the lift` (`roundMetric_sec_value`)
  `= 1 * (gQuot-Gram at x)` — transport back: `roundInner (S.toSphere ⟨x⟩)(ds X)(ds Y)
    = h.inner ⟨x⟩ X Y` (`pullback_inner_eval`, backwards) `= D.gm x X Y` (gm-def, `rfl`-ish,
    SAME section) `= D.gQuot.inner x X Y` (`gQuot_inner`); `ring`. ~80–140 ln.

### Brick 4 — Hamilton model rewrite + `spaceForm_const_metric` (needs 2+3)

GREP FIRST (stop and report if extra consumers appear):
`rg -n "RoundSphere3|SphereOrbitQuotient|SphericalSpaceFormQuotientModel|quotientHomeomorph|action_isometric" DifferentialGeometry/`.
Then in `HamiltonPositiveRicci.lean` (surgical; file ~2900 ln):
1. REPLACE the model (HPR:99–112) by the minimal consumer form —
   `structure SphericalSpaceFormQuotientModel (I) (N) … where
      data : Geometry.RoundQuotientData (EuclideanSpace ℝ (Fin 4)) 3
      equiv : N ≃ₘ⟮I, 𝓡 3⟯ data.Q`
   with a local `instance : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1)` (`Fact.mk`,
   `finrank_euclideanSpace_fin`). `IsSphericalSpaceFormQuotient`/`SphericalSpaceForm` stay
   `Nonempty`-wrappers (downstream statement shapes unchanged). Freeness/isometry fields are
   NOT consumed by this direction — they move to the producer obligation of `ham3_space_box`
   (separate sorry, accepted ripple; note it in-file). Delete `RoundSphere3`/
   `SphereOrbitQuotient` only if the grep shows no other consumer.
2. `spaceForm_const_metric` — new signature `(hM : Closed3Manifold) (model : …)`
   (boundarylessness is genuinely consumed; `ham3_const_box` already holds `hM`, its call
   becomes `… hM hsph`). Proof: `obtain ⟨S⟩ := model`;
   `haveI : I.Boundaryless := hM.2.2.1` (+ the derived `BoundarylessManifold I M` instance;
   `haveI : IsManifold I 1 M := .of_le …`); F-side instances for `𝓡 3` as in Brick 3;
   witness `⟨Diffeomorph.pullbackMetricCross S.data.gQuot S.equiv, c, hc, …⟩` from
   `S.data.gQuot_constPosSec`; per-point: `metricRm04Std_pullbackCross` +
   `pullbackMetricCross_inner` land exactly on the `hsec (S.equiv x) (dX) (dY)` shape.
   Imports to add: `…Metric.Sphere.QuotientDescent`, `…Curvature.PullbackNaturalityCross`
   (both below the Flow layer — no cycle). ~100–150 ln incl. plumbing.

### Ordering, verification, acceptance

1a ∥ 1b first (1a is independent and small); then 2; 3 after 1b (parallel to 2); 4 last.
Per brick: focused `lake env lean` while iterating (false-green caveat), then targeted
`./scripts/lake-locked.ps1 build +Module`; after Brick 4 a FULL `lake-locked build`
(HPR is a root-level consumer). Accept when: QuotientDescent.lean sorry-free in a real build;
`spaceForm_const_metric` proved (no sorry) with `ham3_const_box`/`ham3_equiv`/`ham3_main`
elaborating; `ham3_space_box` remains the lone sorry of the pair; same-name `.md`s updated.
Sizing (honest): ~400–660 ln total, 1 substantial session (1b) + 1–2 short ones.
Only after Brick 4 does the target theorem itself go 0% → done.
