# Lane H2b log: seam C¹ matching (DESIGN_22 §2, brick H2b)

- 2026-09-26: new file `Surgery/Topology/HistoryLGeometry/Seam.lean`, 786 lines. No sorry,
  nolint, or heartbeat/synth options. No comments or docstrings. Lines ≤ 100. No other edits and no
  git writes. The root aggregate is not touched; the lead must register it after `Regularity`.
- Imports:
  - `HistoryLGeometry.Regularity` (H2a)
  - `Perelman/LGeometry/Jacobian/Naturality` (G2)
  - `SurvivorChartMetric`, `ClosedSlabEndpoints`, `Geodesic/Congruence`
  - Mathlib `FDeriv.Extend`
- Compile:
  - The four uncommitted suppliers were compiled as separate scratch modules outside the repo, each
    with its own original import list: G2's `PartialDiffeomorph` and `Naturality`, and H1/H2a's
    `Window` and `Regularity`. Compiling them as one flat concatenation breaks: G2's
    `open scoped Topology` inside a namespace resolves to `DifferentialGeometry.Topology` once
    Window's imports are present.
  - Each module was built with `LEAN_NUM_THREADS=2 lake env lean --root=<scratch> -o`, and
    `LEAN_PATH` was extended to the scratch output directory.
  - Seam was then compiled against those modules. Result: clean, with no errors, warnings or info.
  - `#lint` with `linter.mathlibStandardSet` on the scratch copy: 0 errors in 29 declarations.
  - Transient "failed to read …olean.private" errors appeared when two lean processes started
    together. A retry fixed them.
- Axioms, checked for all 23 public declarations: propext, Classical.choice, Quot.sound. No sorryAx.
- Delivered, generic single-flow (namespace `…Perelman`; they could be promoted later):
  - `IsLRegularizedGeodesicOn.union_Ioo_of_continuousAt`. Suppose `γ` is an L-geodesic on
    `Ioo c w` and on `Ioo w d`, `T - w^2 ∈ D.regular`, and the tangent lift `r ↦ ⟨γ r, γ' r⟩` is
    continuous at `w`. Then `γ` is an L-geodesic on `Ioo c d`.
    - Proof: the chart phase satisfies the ODE on both sides by `lRegularizedCurve_phase`.
      `lPhaseField_smoothAt` and `hasDerivWithinAt_Ici/Iic_of_tendsto_deriv` give the ODE at `w`.
      The committed `lPhase_*` lemmas then give the geodesic at `w`.
    - This is the converse the brief asked for (the removable seam point).
  - `mfderivWithin_Ici_eq_of_eqOn_comp` / `mfderivWithin_Iic_eq_of_eqOn_comp`: if `f ∘ γ = α` on
    `Icc s c` (resp. `Icc c s`), then `α` has the one-sided velocity `mfderiv f (γ s) (γ' s)`.
- Delivered, windows (namespace `ObservedHistory.LWindow`):
  - Transition across a seam, for any window and any `ψ` with
    `∀ᶠ p in 𝓝 (W.f old z), RegularCrossing p (ψ p)`:
    - `eventuallyEq_comp_of_regularCrossing`
    - `mdifferentiableAt_of_regularCrossing`
    - `mfderiv_apply_mfderiv_eq_of_regularCrossing`: `dψ (d f_old V) = d f_new V` for every
      `V : T_z W.X`.
    - `mfderiv_partialDiffeomorph_apply_eq_of_regularCrossing`: the same for the survivor
      `F : PartialDiffeomorph terminalRegularOpen → stage i.succ`, i.e. the `F` of
      `RegularCrossing.exists_survivor_partialDiffeomorph`.
    - `eventually_regularCrossing_invFun`: `ψ := f_new ∘ invFun f_old` satisfies the hypothesis,
      so it is not vacuous.
  - Seam-window pieces, for `W : H.LWindow i.castSucc i.succ T`:
    - old piece `= Icc w W.b`, new piece `= Icc W.a w`
      (`regularizedStage{Start,End}_{castSucc,succ}_eq`)
    - `W.a ≤ w < W.b` (`a_le_sqrt`, `sqrt_lt_b`)
  - `isLRegularizedGeodesicOn_of_comp`, the history-form converse. Suppose `f_old ∘ γ` is an
    L-geodesic of a stage flow `So` on `Ioo w W.b`, `f_new ∘ γ` is one of `Sn` on `Ioo W.a w`
    (with `So`/`Sn` metrics equal to `stageMetric` there), and the tangent lift of `γ` is
    continuous at `w`. Then `γ` is an L-geodesic of the glued flow `W.S` on `Ioo W.a W.b`.
  - `isLRegularizedGeodesicOn_comp` / `isLRegularizedJacobi_comp`: window geodesics and Jacobi
    fields push to stage-flow geodesics and Jacobi fields on open `K ⊆` piece interior.
  - `ObservedHistory.exists_incomingSlab_stageMetric`: for `time j < stageEndTime j`, there is an
    `IncomingSlab (time j) (stageEndTime j)` whose metric at `time j` is `initialMetric j` and
    which agrees with `stageMetric j` on the open stage. For `last` it is
    `finalSlab.restrictIncoming`, which closes H1's "no ClosedSlab → IncomingSlab" gap.
  - `exists_seam_isLRegularizedGeodesicOn_of_regularizedCost_eq` (the H2b headline):
    - Hypotheses: H2a's (`hle hu hupper hlower hfloor α hα hmin hfin`), plus `huv : u ≤ v`,
      `RegularCrossing` for all events (`hcross`), the event `i` with `first ≤ i.castSucc` and
      `i.succ ≤ last`, and `hw : u < w`.
    - Conclusion: `∃ W : H.LWindow i.castSucc i.succ T, u ≤ W.a < w < W.b ≤ v ∧ ∃ γ,` continuous,
      AC, `EqOn (W.f j ∘ γ) (α j)` on the pieces, and `IsLRegularizedGeodesicOn W.S T γ
      (Ioo W.a W.b)`.
    - Proof: window from `exists_seam`, with `W = F.source` of the survivor map. `a` and `b` come
      from the continuity of `α_new`/`α_old` at `w` into `F.target` and `val '' F.source`. Then H2a.
  - `mfderiv_mfderivWithin_Ici_eq_mfderivWithin_Iic_of_regularizedCost_eq` (matching):
    - Hypotheses: the same, plus `ψ` with eventual `RegularCrossing p (ψ p)` near `α_old w`.
    - Conclusion: `α_old` is differentiable within `Ici w`, `α_new` is differentiable within
      `Iic w`, and `mfderiv ψ (α_old w) (mfderivWithin α_old (Ici w) w 1) =
      mfderivWithin α_new (Iic w) w 1`.
  - `mfderiv_partialDiffeomorph_mfderivWithin_Ici_eq_of_regularizedCost_eq`: the same statement
    with the survivor `F` at `x`, `x.val = α_old w`.
- Deviations and limits:
  - Hypothesis `hw : u < w` excludes a seam exactly at the base (`T = time i.succ`, `u = w`). That
    case needs a glued base window with `W.a = 0` (G1/§4 item 4) and is not covered here.
  - `huv : u ≤ v` is added. It is needed for `w < v`; H2a does not carry it.
  - Jacobi data across the seam: values and velocities transport by
    `mfderiv_apply_mfderiv_eq_of_regularCrossing` (take `V := Y w`). Covariant derivatives are not
    stated on the old side at `w`, because `stageMetric i.castSucc (time i.succ)` is junk (F5). Use
    the glued `W.S` Jacobi field and push it with `isLRegularizedJacobi_comp` on open pieces.
  - The converse takes C¹-ness as continuity of the window tangent lift at `w`. That is the
    matching expressed in window coordinates. Deriving it from one-sided stage velocities plus
    `dψ`-matching was not done.
- §7 rows these must match:
  - "H2b | Seam C¹ matching `mfderiv F (α_old' w) = α_new' w` | `…/Seam` | history | 1000 | H1, H2a"
  - "H3a | `IsHistoryLGeodesicOn`, `historyLExpDomain`, `historyLExp`, uniqueness | `…/Exponential` |
    history | 900 | H1, G3"
  - "H7a | `historyReducedJacobian`; seam continuity | `…/Jacobian` | history | 900 | H3b, G2"
- How H3a uses this:
  - Its seam clause of `IsHistoryLGeodesicOn` is `exists_seam_isLRegularizedGeodesicOn_of_regularizedCost_eq`.
  - To construct `historyLExp` across a seam: solve in the glued `W.S`, or glue stage pieces with
    `isLRegularizedGeodesicOn_of_comp`.
  - Uniqueness: the old-side data at `w` is fixed by `regularCrossing_left_unique` and `dψ`
    invertibility.
- How H7a uses this: `isLRegularizedJacobi_comp` plus the transition identity.
