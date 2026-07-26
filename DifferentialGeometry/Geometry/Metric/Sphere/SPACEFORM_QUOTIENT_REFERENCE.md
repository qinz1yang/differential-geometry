# SPACEFORM_QUOTIENT_REFERENCE — Petersen `quotientMetric` vs our round-quotient descent

## 2026-07-24 update

The reference-guided quotient design has now been consumed by the native
positive-space-form producer and the `ham3_space_box` source proof.  The
universal-cover countability repair and the complete downstream exact replay
now pass; the final axiom audit has no `sorryAx`.  Thus the trusted
`ham3_space_box` endpoint is closed.  The historical audit below describes the
earlier producer frontier.

The public `main` branch was rechecked at
`27d799cc3710fed4e0c56d26e397f121d27b3346` (2026-07-23).  Its additional
useful reference chain is:

- Petersen `Ch01/SpaceForms.lean` for the explicit constant-curvature model;
- Do Carmo `Jacobi/CartanLocalIsometry.lean` and the surrounding
  constant-curvature Jacobi files for the local exponential-map isometry;
- Do Carmo `Manifold/CoveringMapConclusion.lean` and
  `CoveringDiffeomorph.lean` for globalization from a complete source;
- Petersen `Ch05/LocalIsometryCovering.lean` and
  `Ch06/MyersFundamentalGroup.lean` for related covering and finiteness
  consequences.

Those files are sorry-free at that remote revision, but they are reference
infrastructure rather than a ready `ham3_space_box` theorem.  The local
`RoundIntrinsic`/Cartan/Killing--Hopf, deck-isometry, quotient-descent, and
Bonnet--Myers modules already adapt the needed parts to RicciFlower
conventions.  LeeSmooth
`Ch01/Sec01_05/Proposition_1_40.lean` does contain a sorry-free
`countable_fundamentalGroup` polygon-code proof for its
`TopologicalManifoldWithBoundary` interface.  It is a useful independent
check, but not a drop-in producer for this project's more general
`ModelWithCorners` universal-cover API; the local refined-basis proof closes
that obligation natively.  No remote theorem was found that directly packages
the Killing--Hopf round quotient.

Reference study (2026-07-19) of `frenzymath/Poincare-Conjecture` (Apache-2.0), files
`Petersen/PetersenLib/Ch01/{MetricConstructions,CoveringMetrics,AveragedMetric,AveragedMetricCompact}.lean`.
STRICT POLICY: reference-only — statement shapes and design lessons; no proof bodies copied,
no imports, clone untracked.

## 0. Where our lane stands (verified in-tree, 2026-07-19)

- `QuotientDescent.lean` (this directory): COMPLETE, sorry-free. `RoundQuotientData`,
  `SectionWitness`, `gm`, `gQuot`, `gQuot_inner`, `gQuot_constPosSec` all proved.
- Endpoint served: `spaceForm_const_metric`
  (`Geometry/Flow/RicciFlow/DimensionThree/HamiltonPositiveRicci.lean:3212`) — PROVED,
  sorry-free (HAM3 frontier #8 closed). It descends `roundMetric` through
  `RoundQuotientData` and pulls back along the model equivalence.
- Remaining sorry of the pair: `ham3_space_box` (same file, :3199) — the Killing–Hopf
  direction; its obligation is to PRODUCE a `RoundQuotientData` witness + cross-model equiv.

So the reference is NOT needed to close the descent (done); it matters as (i) a design
check on `RoundQuotientData`, (ii) the missing uniqueness/local-isometry clause our lane
never states, (iii) a producer-side pattern for `ham3_space_box`.

## 1. `quotientMetric` statement shape (MetricConstructions.lean:418)

Petersen §1.3.3. Signature (their `RiemannianMetric` ≈ our `SmoothRiemannianMetric`;
their field is `metricInner`, ours is `inner`):

```lean
theorem quotientMetric [FiniteDimensional ℝ E'] [I.Boundaryless] [I'.Boundaryless]
    (g : RiemannianMetric I M) (q : M → M')
    (hq_cont : ContMDiff I I' ∞ q)
    (hq_cov  : IsCoveringMap q)
    (hq_surj : Function.Surjective q)
    (hq_bij  : ∀ p : M, Function.Bijective (mfderiv I I' q p))
    (hinv : ∀ (p p' : M), q p = q p' →
      ∀ (u v : TangentSpace I p) (u' v' : TangentSpace I p'),
        mfderiv I I' q p u = mfderiv I I' q p' u' →
        mfderiv I I' q p v = mfderiv I I' q p' v' →
        g.metricInner p u v = g.metricInner p' u' v') :
    ∃! gN : RiemannianMetric I' M', PreservesMetric g gN q
```

where `PreservesMetric g gN q := ∀ p u v, g p u v = gN (q p) (Dq u) (Dq v)` — the
local-isometry clause (`q^* gN = g`). Fully proved, sorry-free, both halves:

- Uniqueness: surjectivity of `q` and of each `Dq_p` forces `gN` on every tangent plane
  (plus a `RiemannianMetric.ext_inner` — inner determines the metric, rest is Props;
  our analogue is the `SmoothRiemannianMetric.ext'` currently LOCAL in
  `QuotientDescent.lean`, canonical home `Geometry/Metric/Basic.lean`).
- Existence: define `gN` at `y` by transporting `g` through `(Dq_p)⁻¹` at ANY chosen
  `p ∈ q⁻¹(y)` (`Classical.choice` over `hq_surj`); well-defined across the fibre by
  exactly `hinv`; SMOOTH because near `y₀` a smooth local section `s` of `q` exists
  (IFT-style `exists_localSection_of_mfderiv_surjective`, needs only `ContMDiffAt` +
  surjective differential + boundaryless), `Ds_y = (Dq_{s y})⁻¹`, so the candidate
  coincides with the pullback `s^* g` near `y₀`.
- Notable: `hq_cov : IsCoveringMap` is carried for faithfulness to Petersen but is not
  consumed by the proof route — the constructive content is
  smooth + surjective + bijective differentials + `hinv` + IFT sections. (Same spirit as
  our lane, where `section_at` replaces the covering hypothesis outright.)

## 2. The invariance hypothesis and how deck isometries discharge it

`hinv` is the Γ-invariance of `g` phrased WITHOUT a group: fibrewise on the deck relation
`q p = q p'`, comparing vectors through their `Dq`-images. For a normal covering with deck
group Γ this is literally "Γ acts by isometries", since `u' = Dγ(u) ↔ Dq_{p'}(u') = Dq_p(u)`.

Discharge pattern (CoveringMetrics.lean), two layers:

- General deck lemma (`coveringInducedMetric_deck_preservesMetric`, :75): ANY smooth
  `τ : M → M` over `F` (`F ∘ τ = F`) preserves the pullback metric `F^* g_N` — pure chain
  rule `DF_{τ p} ∘ Dτ_p = DF_p`. No covering theory, no unique lifting.
- Example ℝPⁿ (`realProjectiveSpaceCovering`, :200): fibre hypothesis
  `hq_fib : q x = q y ↔ y = x ∨ y = -x` case-splits the relation `q p = q p'`;
  identity case: injectivity of `Dq` forces `u = u'`, `rfl`; antipodal case: chain rule
  through `q ∘ (-I) = q` identifies `u' = D(-I) u`, then the deck ISOMETRY
  (`antipodal_isRiemannianIsometry`: `Dι ∘ D(-I) = -Dι` + `⟪-a,-b⟫ = ⟪a,b⟫`) closes it.

Our lane's `sections_agree`/`gm_locallyEq` in `QuotientDescent.lean` is the SAME pointwise
argument (γ from `proj_eq_imp`, differential intertwining from differentiating
`proj ∘ (γ·) = proj`, then `roundInner_sphereDiffeo` = our deck isometry, proved in
`OrthogonalAction.lean:105`) — independent convergence on the identical route: pointwise
chain rule + injective `Dproj`, no covering-space unique lifting.

## 3. Design lesson: represent the quotient by hypotheses

Mathlib (at both pins) has NO quotient-manifold construction and no smooth structure on
`Projectivization`. The reference therefore never constructs `ℝPⁿ`: it takes as
HYPOTHESES a smooth manifold `P`, a smooth surjective `q : Sⁿ → P` with `IsCoveringMap`
and bijective differentials, and a fibre condition identifying fibres with deck orbits
(`hq_fib`), and proves `∃! gP, PreservesMetric (sphereMetricUnit E) gP q`. Whoever later
builds a concrete `ℝPⁿ` instantiates the hypotheses; the metric theory is already done.

Our `RoundQuotientData` (QuotientDescent.lean:72) made the same choice, with these deltas:

| aspect | Petersen ref | our lane |
| --- | --- | --- |
| quotient | hypothesized `P` + instances | bundled field `Q` + instance fields |
| deck group | implicit (fibre iff) | explicit finite `Γ`, `ρ : Γ →* (E ≃ₗᵢ E)` |
| fibre condition | iff (`hq_fib`) | split: `proj_smul` (⊇) + `proj_eq_imp` (⊆) |
| covering hyp | `IsCoveringMap` (unused by proof) | none — replaced by section data |
| local sections | EXISTENCE via IFT from `hq_bij` | DATA `section_at : ∀ x, SectionWitness` (diffeo `s : W ≃ₘ V` + bundled instances on `W`,`V`) |
| conclusion | ∃! metric, `q` local isometry | metric `gQuot` CONSTRUCTED + `gQuot_constPosSec`; no uniqueness, no `proj`-isometry clause |

Lesson to keep: hypothesized-quotient statements stay usable when the concrete quotient
arrives; and the reference shows section EXISTENCE is derivable from bijective
differentials (IFT) — if `ham3_space_box`'s producer finds `SectionWitness` data heavy to
build, an `exists_localSection`-style bridge could construct it (bounded new API, our
`Foundations`-analogue would live near `Geometry/Metric/`).

Averaging (AveragedMetric[-Compact].lean, Petersen Ex. 1.6.24/26): when the upstairs
metric is NOT already invariant, average it over a finite group (sum) or compact group
(Haar) to force `hinv`. Irrelevant for round S³ (`roundInner_sphereDiffeo` gives
invariance for free) but the right tool if a future space-form lane starts from an
arbitrary metric.

## 4. What this serves in our lane

- Served (already closed by our own descent): `spaceForm_const_metric`
  (HamiltonPositiveRicci.lean:3212), via `gQuot_constPosSec`.
- Genuinely missing, and what the proposal below adds: the Petersen-shape
  CHARACTERIZATION of `gQuot` — `proj` is a local isometry and is the UNIQUE such metric.
  Our lane defines `gQuot` through sections (`gm`, `gQuot_inner`); it never states
  `proj^* gQuot = roundMetric`. That clause is what any later consumer (volume of the
  quotient, geodesics, `ham3_space_box` compatibility checks) will actually want.
- For `ham3_space_box` (the live frontier): the reference confirms the witness design —
  produce the hypothesized-quotient package (our `RoundQuotientData`), do not wait for a
  Mathlib quotient-manifold construction.

## 5. PROPOSED statement skeleton (proposal only — NOT implemented, no proof)

In our conventions (`SmoothRiemannianMetric I M` = alias of Mathlib's
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`, `Geometry/Metric/Basic.lean`;
field `.inner`). Lane-specific form, home: this directory, `QuotientDescent.lean` (or a
small `QuotientUnique.lean` beside it). Existence witness would be `D.gQuot`; the
invariance input is `sections_agree`/`roundInner_sphereDiffeo`, both banked.

```lean
-- PROPOSAL (statement only).  Petersen §1.3.3 quotient-metric clause for the
-- round descent: `proj` is a local isometry onto `(Q, gQuot)`, uniquely.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]
  (D : Geometry.RoundQuotientData E n)

/-- `gQuot` makes `proj` metric-preserving: `proj^* gQuot = roundMetric`. -/
theorem gQuot_proj_isom (p : sphere (0 : E) 1) (u v : TangentSpace (𝓡 n) p) :
    (roundMetric (E := E) (n := n)).inner p u v
      = D.gQuot.inner (D.proj p)
          (mfderiv (𝓡 n) (𝓡 n) D.proj p u)
          (mfderiv (𝓡 n) (𝓡 n) D.proj p v) := sorry -- proposal

/-- Uniqueness: any smooth metric on `Q` making `proj` metric-preserving is `gQuot`. -/
theorem gQuot_unique (h : SmoothRiemannianMetric (𝓡 n) D.Q)
    (hh : ∀ (p : sphere (0 : E) 1) (u v : TangentSpace (𝓡 n) p),
      (roundMetric (E := E) (n := n)).inner p u v
        = h.inner (D.proj p)
            (mfderiv (𝓡 n) (𝓡 n) D.proj p u)
            (mfderiv (𝓡 n) (𝓡 n) D.proj p v)) :
    h = D.gQuot := sorry -- proposal
```

Expected inputs if implemented (all existing): `proj` surjectivity — NOT currently a
`RoundQuotientData` field; recover it pointwise from `section_at` (`isSec` at `x` gives
`proj (s x) = x`), so no statement change needed. Bijectivity of `Dproj` at the section
image = `dproj_sec`/`dproj_inj` (in `QuotientDescent.lean`); uniqueness route =
`SmoothRiemannianMetric.ext'` (promote from LOCAL to `Geometry/Metric/Basic.lean` when
touched) + surjectivity of `proj` and `Dproj` exactly as in the reference. A fully
general two-model `quotientMetric` (arbitrary `g`, `q`, `hinv`) is the reference's shape;
if ever needed, its canonical home is `Geometry/Metric/` next to `Pullback.lean` — do not
build it speculatively (Simplicity first; the lane consumer is the specialized form).
