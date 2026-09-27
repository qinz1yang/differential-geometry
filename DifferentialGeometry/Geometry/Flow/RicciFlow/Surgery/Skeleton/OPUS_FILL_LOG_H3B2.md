# Lane H3b' log: public window family, general truncation, unconditional H7a window theorems

- 2026-09-26 start (~06:35). Coordinator follow-up to H3b plus owner directive: export the jointly
  smooth window family at every parameter `s₀ ∈ (0, v)` (seams included) and the non-minimizing
  truncation identity, then restate H7a's window theorems without their family hypothesis.
  `ExponentialSmooth.lean` is not edited (acceptance build); its private declarations are reached
  with `open private … from`. Read: `OPUS_FILL_LOG_H7A.md`, `HistoryLGeometry/Jacobian.lean`
  (hypothesis block `hV hZ₀V hVdom hK hKW hβ hgeo hrep`, :254–267 and :450–463), H5
  `Truncation.lean` (`HasHistoryLInitialVector.truncate`; its `isHistoryLGeodesicOn_truncate`
  needs minimality).
- Final (~07:20). Two new files, LF, no sorry/admit/axiom, no nolint/heartbeat/synth options, no
  comments/docstrings, only `set_option autoImplicit false`, lines ≤ 100 chars (imports excepted).
  No other repo edits, no git writes, root aggregate not touched (register `ExponentialFamily`
  after `ExponentialSmooth` and `Truncation`, `JacobianUnconditional` after `Jacobian`).
  - `Surgery/Topology/HistoryLGeometry/ExponentialFamily.lean` (654 lines). Imports
    `HistoryLGeometry.ExponentialSmooth`, `HistoryLGeometry.Truncation`.
  - `Surgery/Topology/HistoryLGeometry/JacobianUnconditional.lean` (129 lines). Imports
    `HistoryLGeometry.Jacobian`, `HistoryLGeometry.ExponentialFamily`.
- Compile: scratch `h3a/src/H3aPre/{ExponentialFamily,Jacobian}.lean` (repo files, imports and the
  two `open private … from` module names renamed to `H3aPre.*`; `diff` otherwise identical),
  built with `h3a/mk.sh` (`lean --root=. -o`, `LEAN_NUM_THREADS=2`): clean, 56 s / 40 s.
  `h3b2/JU.lean` (= `JacobianUnconditional.lean`, imports renamed) via `h3b2/chk.sh`: no errors,
  warnings or infos. `linter.mathlibStandardSet` + `#lint`: all passed on both files (9 and 2
  declarations). Axioms of all 7 public theorems: propext, Classical.choice, Quot.sound. Public
  names grep-unique library-wide.
- Public API, `ExponentialFamily` (namespace `ObservedHistory`):
  - `IsHistoryLGeodesicOn.truncate (hfk : first ≤ k) (hkl : k ≤ last) (hv₁ : 0 < v₁) (h12 : v₁ ≤ v₂)
    (hk : T - v₁ ^ 2 ∈ stageDomain k) (hgeo : IsHistoryLGeodesicOn hle T v₂ α) :
    IsHistoryLGeodesicOn hkl T v₁ (fun j : StageInterval k last => α ⟨j, _, _⟩)` — no minimality,
    `T − v₁²` may be an event time (windows restricted to `b ≤ v₁`; continuity at `v₁` from the
    window at `v₁` when `v₁ < v₂`).
  - `mem_historyLExpDomain_of_le … : Z ∈ historyLExpDomain hle T v₂ p → Z ∈ historyLExpDomain
    hkl T v₁ p` and `historyLExp_eq_historyLCurve_of_mem_historyLExpDomain hfk hkl hv₁ h12 hk
    (Z : historyLExpDomain hle T v₂ p) : historyLExp hkl T v₁ p ⟨Z.1, _⟩ = historyLCurve hle T v₂ p
    Z ⟨k, hfk, hkl⟩ v₁` (H7a item 4; for every `Z` in the domain, not only minimizers).
  - `exists_contMDiffOn_window_family_historyLCurve (hv : 0 < v) (hZ₀ : Z₀ ∈
    historyLExpOpenDomain hle T v p) (hs₀ : s₀ ∈ Ioo 0 v) : ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧
    V ⊆ historyLExpOpenDomain hle T v p ∧ ∃ hVdom : (∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈
    historyLExpDomain hle T v p), ∃ lo hi (hlo : first ≤ lo) (hhi : hi ≤ last) (W : LWindow lo hi T)
    (K : Set ℝ), IsOpen K ∧ s₀ ∈ K ∧ K ⊆ Ioo W.a W.b ∧ ∃ β, ContMDiffOn (𝓘(ℝ,ThreeSpace).prod
    𝓘(ℝ,ℝ)) ThreeModel ∞ β (V ×ˢ K) ∧ (∀ Z ∈ V, IsLRegularizedGeodesicOn W.S T (β (Z, ·)) K) ∧
    ∀ Z (hZ : Z ∈ V) (j : StageInterval lo hi), ∀ r ∈ K ∩ Ioo (regStart T W.a j) (regEnd T W.b j),
    historyLCurve hle T v p ⟨Z, hVdom Z hZ⟩ ⟨j, hlo.trans _, _.trans hhi⟩ r = W.f j (β (Z, r))` —
    exactly H7a's `hV hZ₀V hVdom hK hKW hβ hgeo hrep` (with `Z₀.1`), at every `s₀`, seams included.
  - `exists_contMDiffOn_seam_window_family_historyLCurve hv hZ₀ (i) (hlo : first ≤ i.castSucc)
    (hhi : i.succ ≤ last) (hw : √(T - time i.succ) ∈ Ioo 0 v)`: the same with
    `W : LWindow i.castSucc i.succ T` and `√(T − time i.succ) ∈ K` (H7a's Seam section shape).
- Proof route. At `s₀` take the witness window `W` of the reference geodesic (it contains `s₀`, seam
  or not). Non-event `c₁ ∈ (W.a, s₀)`, `c' ∈ (s₀, W.b)`. `HasPrefixFamily … c₁` by a sup argument
  aimed at `c₁` (`hasPrefixFamily_of_window`; needs a base point below `c₁`, hence
  `exists_hasPrefixFamily_base_lt`, a bounded copy of the private base lemma). One exposed step
  through `W` (`exists_window_family_step` = the private step with the family `β₂` on an open
  preconnected `K ⊇ [c₁, c']` and `A' Z = W.f ∘ β₂(Z, ·)` beyond `c₁` in the conclusion). The
  prefix `A' Z` up to the non-event `c'` becomes a full history geodesic for the stages
  `k' .. last` (`isHistoryLGeodesicOn_of_prefix`), so H3a's uniqueness against the truncation
  (`IsHistoryLGeodesicOn.truncate`, H5's `HasHistoryLInitialVector.truncate`) of `historyLCurve Z`
  gives `hrep` on `K ∩ (c₁, c')`. `V` is intersected with H3b's neighbourhood inside the open
  domain. Seam version: restrict that window to `[i.castSucc, i.succ]` and `[w − ε/2, w + ε/2]`.
- Public API, `JacobianUnconditional` (hypothesis-free forms of H7a's window theorems; the family
  comes from the export above; `Z₀ : historyLExpDomain hle T v p`, `hZ₀ : Z₀.1 ∈
  historyLExpOpenDomain hle T v p`):
  - `exists_window_historyLJacobianDensity_eq_lJacobianDensity (hv) (hZ₀) (hs₀ : s₀ ∈ Ioo 0 v) : ∃ lo
    hi hlo hhi (W : LWindow lo hi T) K β, IsOpen K ∧ s₀ ∈ K ∧ K ⊆ Ioo W.a W.b ∧
    IsLRegularizedGeodesicOn W.S T (β (Z₀.1, ·)) K ∧ [Jacobi field: conclusion of
    `isLRegularizedJacobi_historyLJacobiField`] ∧ [∀ j τ, √τ ∈ K ∩ piece → `historyLGram … = lGram
    W.S T …`] ∧ [same for `historyLJacobianDensity = lJacobianDensity`] ∧ [∀ j τ, … → 0 < det lGram
    → `HasDerivAt` of `hasDerivAt_historyLJacobianDensity`] ∧ [∀ j s₁ ∈ K, ∀ l ≤ 𝓝 s₁, piece
    eventually → `Tendsto` of `tendsto_historyLJacobianDensity`]`, all for one `β`.
  - `exists_seam_window_tendsto_historyLJacobianDensity (hv) (hZ₀) (i) (hlo) (hhi) (hw) : ∃ (W :
    LWindow i.castSucc i.succ T) K β, IsOpen K ∧ √(T − time i.succ) ∈ K ∧ K ⊆ Ioo W.a W.b ∧ geodesic
    ∧ [density = lJacobianDensity on K ∩ piece] ∧ [the two one-sided limits of
    `tendsto_historyLJacobianDensity_seam`]`.
- Honest limits: everything needs `Z₀ ∈ historyLExpOpenDomain` (geodesic continues past `v`), which
  holds for `historyMinDomain` when `T − v²` is not an event time (H3b); the event-time case (H3b
  item 4) is unchanged. Seam value at `s = w` itself is not added (H7a's (b)).
- Duplicates (unavoidable without editing `ExponentialSmooth`): `exists_hasPrefixFamily_base_lt`
  (bounded copy of the private base lemma) and `exists_window_family_step` (the private step with
  an exposed conclusion). On integration, fold them into `ExponentialSmooth` by strengthening the
  private statements.
