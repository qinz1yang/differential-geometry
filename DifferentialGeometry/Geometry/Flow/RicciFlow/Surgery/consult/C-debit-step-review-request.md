# Third external review request: the debit step S and the age-restricted witness clause

Target: mirror `liao9yuan/differential-geometry-dev`, branch `codex/pc-target-c-psf`
(= collaborator's `codex/pc-sorry-free` @ 286e17a8c plus our skeleton). Read
`DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/FREE_INPUTS.md`,
`…/Surgery/Topology/CanonicalNeighborhoodsThroughSurgery.lean` (defs `CanonicalNeighborhoodsThroughSurgery`,
`UniformDebitSurgeryStep`, the assembly `exists_poincare_controlled_extinction_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods`),
`…/Surgery/Skeleton/HANDOFF_S.md`, and the factory
`…/Surgery/Contract/PoincareHornCutoffRecord.lean:461`
(`exists_horn_cutoff_record_with_uniform_volume_debit_and_poincareStandardDiscarded_of_canonical_neighborhoods`),
`…/Surgery/Contract/PreparedHistoryCutoff.lean:237,381-383`,
`…/Surgery/Contract/TerminalCorePresentationExistence.lean:466-474`,
`…/Surgery/Topology/ProspectiveNeckSurvival.lean:3194,3322,3448`.

## Findings to check (from the lead's read-only analysis of 2026-09-26)

F1. Precision direction. The factory's cutting accuracy is `εcan = min epsGeometry epsTop` with
`epsGeometry = δ'/4`, `26000·δ' ≤ ε₀`, `ε₀ = min εfactory (min (ηstar/2) ((mstar+1)⁻¹))`, and
`ε₀ ≤ ηstar ≤ δ ≤ ηrecord ≤ δbound ≤ δmax(ε)`. So the factory consumes canonical neighbourhoods at
accuracy `≤ δ/208000`, FINER than the record precision δ; while C (and Perelman) require the record
precision far below the canonical accuracy `ε` (fresh caps are ε-canonical only when glued at finer
precision). With S's order (`∀ B, ∃ ε, ∀ C's constants at ε, ∃ p₀ δbound …`), no fixed point exists
unless `δmax(ε) ≥ 2·10⁵·ε`. Neither S as stated nor the joint-tuple alternative of HANDOFF_S is
obtainable from this factory by reordering binders.

F2. The missing brick is Perelman II Lemma 4.3 (Kleiner–Lott Lemma 71): in an ε̄₀-horn, points of
curvature ≥ Q(δ) are centres of strong δ-necks; proof by blow-up to an ancient κ-solution that is a
neck at every point, hence the round cylinder. This needs κ-noncollapsing, so S must receive κ
(the C2 predicate) and C's interface is unchanged; ε becomes a fixed coarse ε̄₀ and the improvement
threshold goes into the cutting scale Q, hence into the debit v.

F3. Input dependence table for εcan: q0 — deferrable (every inner use is through q0/scale → 0; the
subsequence lemma must take a sequence q0ₙ with q0ₙ/scaleₙ → 0; output Qmin = Λ·max q0 1);
Ctime — dimensionless, must precede ε (S restated as `∀ B Ctime, ∃ ε, …`; the assembly gets Ctime
from `hcn B (1/22)` first); m, accuracy, ηrecord (and Dcap) — genuine, tied to the cut precision.

F4. Uses of the canonical-neighbourhood hypothesis inside the factory closure: (i) terminal
chains (`TerminalCutoffScale:111`, `TerminalSphericalRegion*`, `TerminalCapCore:313`,
`DiscardedComponentClassification:106`, …) at points with terminal `R > L`, `L ∈ {C·qcan, (δρ)⁻², B}`,
at times near the singular time s: normalized age ≈ `L·(s − a)`, NOT bounded below when the slab is
short; (ii) five sites that only read `W.time_derivative` at every time (replaceable by the
unrestricted derivative clause); the `.gradient` uses are outside the closure.

F5. The lead's earlier "FIX 3" repair (cut at `h' = h/√(C·Ctime·τmin)`) does not close: caps at
scale h' have curvature ≈ h'⁻² ≫ C h⁻², so no post-surgery bound is preserved; the ratio is
scale-invariant. Young high-curvature points on short slabs need the scathed alternative (they lie in
evolved cap regions, which are discarded / Poincaré-standard by the standard-solution comparison).

F6 (design, not yet decided). The age restriction `τmin ≤ R (t − a)` on slab witnesses is an artifact
of the tree's witness type (`CanonicalWitness G.flow`, both alternatives built on `StrongNeck`, whose
backward window must lie in the slab). Perelman's canonical neighbourhoods are unrestricted because
strong necks run through the pre-surgery flow on retained regions, and ε-caps are spatial. A faithful
witness would carry spatial data at time t on the stage and strong necks on the backward-survivor
flow (`ObservedHistory.exists_backwardSurvivor_isSolutionOn`, `HistoryParabolicBall.lean:790`, a
`SolutionOn` on the survivor domain through retained cores); fresh cap tips would still be excluded
from the survivor domain, so the cap alternative's tube (retained δ-neck region) would carry the
strong necks while the tip only needs spatial data.

## Questions (answer in Chinese; ~1500 characters; a table of verdicts OK / FALSE / FIX with the
clause checked; counterexamples checked clause by clause against the Lean statements)

1. Is F1 real as stated — does the factory need canonical neighbourhoods finer than the cut
   precision, and is Lemma 4.3 the only way to decouple them? Where exactly in Perelman/KL does
   `δ ≪ ε` enter, and does Perelman's fixed ε (universal) plus 4.3 give a consistent parameter
   order for OUR interface (C is `∀ ε`; would S only ever call C at a fixed ε̄₀)?
2. Restated S: `∀ B Ctime, ∃ ε, ∀ C1 C2 qcan τmin Cgrad δmax ρmax εcap Dcap mcap κ, ∃ p₀ δbound
   ρbound v, …, ∀ H in the class, κ-noncollapsed up to s (history-wide parabolic balls of radius ≤ ε),
   derivative clause above qcan, canonical witnesses at age ≥ τmin → next event …`. Is it provable in
   principle from the factory plus 4.3? Does the assembly with C2 (κ before qcan; the interface's
   derivative clause from a first call `hcn B (1/22)`) thread without circularity?
3. F4(i): with the age restriction, terminal-time classification at threshold L fails on slabs
   shorter than `2τmin/L`. Options: (a) raise the threshold on short slabs (non-uniform v?);
   (b) young-point alternative via the standard-solution comparison (which points are "young" at the
   singular time: ONLY evolved cap regions? what about untouched components made young by a cut
   elsewhere — their moderate-curvature points near s?); (c) drop the age restriction by F6. Which is
   sound and cheapest? Give the counterexample if (b) is false as stated.
4. F6: is the survivor-flow witness (spatial tip data + strong necks on the backward-survivor flow)
   the right object? Does the factory's consumption (terminal topology from spatial data, time
   derivative from the field) go through with it? What does the blow-up produce at a crossing point
   (a witness on which flow)?
5. The Crossing leaf's read-only analysis says no complete ancient limit can be built from the
   collaborator's local tools (`IncompleteLocal` fixed radius ρ, `TracedTerminalCompactness`
   bounded depth, its own derivative constant), and estimates a "history model theorem" layer at
   5–9k lines (compactness with ρ = ∞ on incomplete sources, backward extension, scathed dichotomy
   at each backward step, localizing `NormalizedSequence`'s `complete`/`source_bound`). Is there a
   cheaper faithful route for points of age in `[τmin, θ(κ))` (e.g. blow-up in the PREVIOUS slab at
   the traced point when that slab is long, forward propagation otherwise), or is local compactness
   unavoidable?
6. Anything false or vacuous in the current skeleton statements on this branch that you can refute
   with a concrete configuration (the S, C2, C3a/b/c leaves, `CapWindowPoint`,
   `GradientBoundBefore`).
