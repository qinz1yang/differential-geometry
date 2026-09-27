# OPUS_FILL_LOG_C4B2 (DESIGN_C4B bricks M1a, M1b, M4, M4★; review H11 binding)

## 2026-09-26 entry 1 (start)

Read: AGENTS.md, DESIGN_C4B.md, consult/H11-c4b-m4star-review-digest.md, the 27c producer
(`StandardSliceSpatialCanonical.lean`, `StandardInitialSpatialCanonical.lean`), the witness-first
transport lemmas. C4B1 log not yet present.

Compile method: new uncommitted modules are copied to the scratchpad as `C4B2.<Base>` (imports of
the other new modules rewritten), compiled with `lean --root=<scratch src> -o <scratch olean>`,
`LEAN_PATH = scratch olean ; lake env LEAN_PATH`, lakefile options passed by `-D`
(`maxSynthPendingDepth=3`, `weak.linter.mathlibStandardSet=true`, `linter.style.longLine=false`,
`linter.style.header=false`), `LEAN_NUM_THREADS=2`. Nothing written under `.lake` / E:.

## M1a (done, compiles clean)

- `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessMargins.lean`: `HasMargins` (§2 verbatim)
  and `HasMargins.enlarge_constants`.
- `Perelman/StandardSolution/StandardSpatialCanonicalMargins.lean`:
  `FiniteHorn.exists_uniform_spatialNeck_canonicalWitness_with_margins` (neck, radius `9/√Q`,
  `9.45 ≤ 10·√(1−ε)` via `√(1−ε) ≥ 189/200`, `16·√(1+ε) < 17.55` by nlinarith from `ε < 1/11`),
  private tip producer with radius `20ρ/21` (inner ball `(21/20)(20ρ/21) = ρ`, outer
  `K1 ⊆ B(13ρ/7)` from `α ≥ 9/10`, `β ≤ 11/10`, `r ≥ 4√ΛD + 4D₁ + 11200`; depth
  `≥ 0.9·11200 − 1 ≥ 10000 + 1/20`), and the headline
  `StandardSolution.exists_spatialCanonicalWitness_with_margins` (§2 verbatim).
- Deferred merge: the neck/tip bodies duplicate `exists_uniform_spatialNeck_canonicalWitness`
  and the private `exists_tip_spatialCanonicalWitness` with the margin clauses added; the old
  producers can later be derived from these. The private helpers `distance_lower_of_radial`,
  `distance_upper_of_radial`, `radial_neck_image_eq` are used through
  `open private … from …StandardSliceSpatialCanonical` (existing tree pattern), not copied.

## M1b (done, compiles clean)

- `Perelman/StandardSolution/StandardWindowBallPlacement.lean` (150 lines):
  `StandardSolution.exists_ball_placement` and `StandardSolution.exists_window_ball_placement`,
  both §2 verbatim. Output `Λ := 2Λ₀` (ℝ³) and `4Λ₀` (window), `Λ₀` from
  `uniformStandardLifetime_metricComparison`; `‖y‖ = d_cap(0,y)` (`StandardCap.edist_zero`),
  triangle, `edistOf_le_of_quad` (cap ≤ Λ₀·Q, and `Q|_W ≤ 2g`), `riemannianEDistOf_le_restrictOpen`.
  Compactness: closed subset of the Euclidean closed ball (window: of its preimage, compact since
  it lies in the window by the room hypothesis).

## M4 (done, compiles clean)

- `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessUniformTransport.lean` (909 lines).
  Headline `SpatialCanonicalWitness.exists_uniform_comparison_transport_tolerance`, §2 verbatim.
  Public supporting lemmas (all new names, unique library-wide):
  - `MetricComparisonOn.abs_metricScalarAt_sub_le_of_rm_bound`: `|R'(Fy) − R(y)| ≤ 243(δ + 3Kδ)`
    from `|Rm(y)| ≤ K` (explicit form of `scalarComparisonC_le`).
  - `MetricComparisonOn.rmNormSq_image_le_of_mem_opens`: the `324K²` bound on an open comparison
    set (complete auxiliary metric + a small closed ball, then the existing closed-ball lemma).
  - `SpatialNeck.exists_scale_invariant_transport_tolerance`: neck transport whose tolerance
    depends only on `(α, Λ, order)` with `q⁻¹ ≤ Λ` and RELATIVE scalar closeness `≤ η₀·q` (no upper
    bound on `q`). NOTE: the name `SpatialNeck.exists_uniform_transport_tolerance` is taken by
    `Surgery/Topology/AncientPointedFlowLimitTransfer.lean:515` (absolute scalar window `[r₀,r₁]`,
    `Nonempty` output), which does not fit (no upper bound on `q` here).
- Tolerance: `δ = min(dN, 1/10, Rlow/40, m/10⁵, θ₀/A)`, `A = 243(Rlow⁻¹ + 3C2)`,
  `θ₀ = min(m/10⁵, 1/(2C2), ηN/C2)`, `(dN, ηN)` from the neck lemma at `Λ = max 1 (C2/Rlow)`.
  Depends only on `(α, m, C1, C2, Rlow)` (C1 only through nothing; C2 the SOURCE constant).
  The target constant `C2' ≥ 1000·C2` is quantified after `δ`.
- Fields: scalar via `A·δ·q` relative error on the domain (`Rm ≤ C2·q`, `q ≥ Rlow`); radius kept
  `r' = r` (`(1+m)/√q ≤ r` gives `1/√q' ≤ r`; `q' ≤ 2q` gives `r ≤ 2C1/√q'`); inner ball via
  `ball_subset_image_of_metric_lower_crossModel` at `R₀ = (1+m/2)r`; outer ball and cap depth via
  `crossModel_edist_transfer_of_comparison` with `ρ = 2r`, `R = Rb` (`8r < Rb`); `Rm` via
  `18·C2·q ≤ C2'·q'`; volume via `volume_image_ge` (`√((1−δ)³) ≥ 1/2`, `q'√q' ≥ q√q/4`);
  gradient from the hypothesis.
- Hidden gap (H11): the cap is rebuilt with the `[0,1]` SINGLE-neck chain of the
  `capTubeHasNeckChart` neck (private `SpatialLocalCap.singleNeckChain`); its centre
  `nk.map (center,0) = tubeMap (center,0)` lies in the tube, hence in the domain, which gives
  `q_v ≥ q/C2` and `|R'(Fv) − q_v| ≤ ηN·q_v`; its `α⁻¹` window lies in `B(x, 2r + (α⁻¹+6)(3/2)√C2/√q)
  ⊆ B(x, Rb)`. The original chain is not preserved (allowed by H11). `capTubeHasNeckChart (2α)` of
  the output: its tube map is `tubeMap.trans F = nk.map.trans F = nk'.map`.
- The witness-first lemmas of `SpatialCanonicalWitnessComparisonTransport.lean` are not used.

Axioms (probe outside the tree, removed) of every public declaration of M1a, M1b, M4:
`[propext, Classical.choice, Quot.sound]`.

Lead message (M2 changed by C4B1): noted. M4 is stated for an arbitrary `U : Opens`, so it is
unaffected; M4★ will use `exists_window_metricComparisonOn_of_lt` with `D' := D − 1`.

## M4★ (done, compiles clean)

- `Perelman/StandardSolution/StandardWindowSpatialCanonical.lean` (202 lines):
  `exists_window_spatialCanonicalWitness_of_standard_close`, §2 verbatim.
- Constants before `Θ` (H11 item 1): B8 at `(α, H) = (ε, 1)` gives `(C_old, δ₀)`; L6e at `δ₀` gives
  `τQ`; `c₀` from `exists_standard_scalar_lower_bound`; `τ' = max τQ δ₀⁻¹`,
  `Θ₃ = 2τ'/(c₀ + 2τ')`; M1a at `(neckModelTolerance(ε/2), Θ₃)` gives `C_std`; M4 at
  `(α, m, C1, C2, Rlow) = (ε/2, 1/20, C_std, C_std, 1)` gives `δ₄`; M1b (ℝ³ form) at `Θ₃` gives `Λ`;
  M2 (`_of_lt`) at `(Θ₃, order = max 2 ⌈ε⁻¹⌉₊, η = min δ₄ (1/2))` gives `e₂`.
  `Cw = max C_old (1000·C_std)`.
- After `(Θ, r)`: `eta` from `exists_uniform_standard_metric_scalar_lower_comparison (max Θ 0)`;
  `L = 8C_std + 3((ε/2)⁻¹ + 7)√C_std`; ONE `D` from L6e at `r' = r + Λ(L+1) + 1` (never replaced);
  `N = max N_L6 (max 2 order)`, `e = min e_L6 (min eta e₂)`; `e` is uniform in `(Q, T, z, C2)`.
- Split on `Θ₃ ≤ T`:
  - old: `R_S ≥ R_Q/2` (the folded scalar comparison) and `R_Q ≥ c₀/(1−T)` give `τ' ≤ T·R_S`
    (private copy of `le_mul_of_half_standard_scalar_lower`); L6e gives the oriented witness on
    `S` itself (orientation: the standard orientation of ℝ³ restricted to the window, private copy
    of `CanonicalWitnessPositiveAge.nonempty_positiveAge_tangentOrientation` + `restrictOpen`);
    `δ₀⁻¹ ≤ T·R_S` puts the window `Ioo (T − (δ₀R)⁻¹) T` in `(closed 0 T).regular = Ioo 0 T`;
    B8 → `canonicalWitness_mono` → `enlarge_constants` → `toSpatial`. No transport.
  - young (`T < Θ₃`): M1a witness for `Q.val.metric T` at `z.val` (margins `1/20`),
    `R_Q ≥ 1` (`Rlow = 1`), the M4 ball radius `≤ L` (since `√R_Q ≥ 1`), compact and inside
    `standardCapWindow (D − 1)` by M1b; comparison from M2 `_of_lt` with `D' = D − 1`; M4 along
    `F = (subtypeVal (standardCapWindow D)).symm` with `C2' := C2 ≥ 1000·C_std`; `F z.val = z`;
    output tolerance `2·(ε/2) = ε`; `enlargeConstants (2C_std ≤ Cw)`.
- Deviation from the lead's M2 note: none needed; `D − 1` as advised, no new hypothesis.
- Deferred merges (private copies): `nonempty_window_tangentOrientation` (from
  `CanonicalWitnessPositiveAge.lean`), `le_mul_of_half_scalar_lower` (from
  `Surgery/Topology/CapWindowContinuationAssembly.lean:142`, not imported to keep
  `Perelman/StandardSolution` free of a `Surgery/Topology` assembly import).
- Axioms: `[propext, Classical.choice, Quot.sound]`.

## Summary

| Brick | File | Lines | Status | Deviation |
|---|---|---|---|---|
| M1a | `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessMargins.lean` + `Perelman/StandardSolution/StandardSpatialCanonicalMargins.lean` | 61 + 551 | proved, clean | none (producer bodies duplicated from 27c; deferred merge) |
| M1b | `Perelman/StandardSolution/StandardWindowBallPlacement.lean` | 150 | proved, clean | none |
| M4 | `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessUniformTransport.lean` | 909 | proved, clean | none in the headline; supporting neck lemma named `…scale_invariant…` (name clash) |
| M4★ | `Perelman/StandardSolution/StandardWindowSpatialCanonical.lean` | 202 | proved, clean | none |

All compiled with the lakefile options (standard linter set on) as scratch modules `C4B2.*`
(imports rewritten), zero output. No `sorry`, no comments, no linter suppression, no heartbeat
option. No committed file touched, no `DifferentialGeometry.lean` change, no lake build, no git
write. Import order for wiring: Margins → StandardSpatialCanonicalMargins; UniformTransport (needs
Margins); StandardWindowSpatialCanonical (needs all four + C4B1's `StandardWindowComparison`).
