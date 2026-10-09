import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5Gauge

/-!
# The gradient gauge of the potential on a terminal interval

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (potential gauge, design D18 (iv)).

* `surfaceFlow_exists_gradient_flow_window_open`: for `0 < t₀ < t₁ < T` the flow of
  `∇_{g(t)} f(t)` with `Φ t₀ = id` on an open interval `(lo, hi) ∋ t₀, t₁` inside `(0, T)`, with
  velocity at every time of `(lo, hi)` (also at `t₀`) and diffeomorphic slices on `[t₀, hi)`: the
  field is cut off past `[t₀ / 2, t₁]` (`interior_field_global_cutoff_extension`) and integrated by
  `global_flow_with_reverse_on_closed_interval_of_closed_manifold` after a time shift.
* `gradient_flow_window_eq`: two such flows agree on the intersection of their intervals, by
  `integral_curves_eqOn_of_jointC1` from the interior time `t₀`.
* `surfaceFlow_exists_gradient_flow`: gluing the windows `[t₀, T - (T - t₀) / (n + 2)]` gives one
  family of diffeomorphisms `ψ` on `[t₀, T)` with `ψ t₀ = id`, jointly smooth on `(t₀, T) × M`, with
  velocity `∇_{g(t)} f(t)` on `(t₀, T)` and a one-sided derivative at `t₀`.
* `surfaceFlow_exists_potential_gauge`: design D18 (iv), the statement frozen in the design, adding
  `surfaceFlow_pullback_normalized_hasDerivAt` for `T* = A₀ / C₀`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Bundle Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]
  {T : ℝ} {hT : 0 < T}

private local instance gaugeMeasurable : MeasurableSpace M := borel M
private local instance gaugeBorel : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
theorem hasMFDerivAt_add_const_one (t₀ r : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + t₀) r (1 : ℝ →L[ℝ] ℝ) := by
  have h' := ((hasDerivAt_id r).add_const t₀).hasFDerivAt.hasMFDerivAt
  have hone : (1 : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.toSpanSingleton ℝ 1 := by
    ext
    simp
  rw [hone]
  exact h'

theorem surfaceFlow_exists_gradient_flow_window_open
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) :
    ∃ (Φ : ℝ → M → M) (lo hi : ℝ), 0 < lo ∧ lo < t₀ ∧ t₁ < hi ∧ hi < T ∧ (∀ x, Φ t₀ x = x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) (Ioo lo hi ×ˢ univ) ∧
      (∀ t ∈ Ioo lo hi, ∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (gradFun (S.family.metric t) (f t) (Φ t x)))) ∧
      (∀ t ∈ Ico t₀ hi, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x, d x = Φ t x) := by
  have hint := surfaceFlow_gradient_field_contMDiffOn S hS f hf
  obtain ⟨Xt, δ, hδ, hXeq, hXsm, -⟩ := interior_field_global_cutoff_extension
    (fun s y => gradFun (S.family.metric s) (f s) y) T hint (a := t₀ / 2) (b := t₁)
    (by positivity) h1
  let Y : ℝ → ∀ x : M, TangentSpace I x := fun s y => Xt (s + t₀) y
  have hshift : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M => (q.1 + t₀, q.2)) :=
    ContMDiff.prodMk (contMDiff_fst.add contMDiff_const) contMDiff_snd
  have hY : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y q.1 q.2) : TangentBundle I M)) :=
    hXsm.comp hshift
  obtain ⟨Φ₀, Ψ₀, lo₀, hi₀, hlo₀, hhi₀, hΦ0, hΦsm, hvel, hΨsm, hΨΦ, hΦΨ⟩ :=
    global_flow_with_reverse_on_closed_interval_of_closed_manifold Y hY (t₁ - t₀)
      (sub_pos.mpr h01)
  set lo := max (t₀ + lo₀) (t₀ / 2) with hlodef
  set hi := min (t₀ + hi₀) (min (t₁ + δ) ((t₁ + T) / 2)) with hhidef
  have hlo_pos : 0 < lo := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hlo_t₀ : lo < t₀ := max_lt (by linarith) (by linarith)
  have hhi_t₁ : t₁ < hi := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hhi_T : hi < T := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  have hmem : ∀ t ∈ Ioo lo hi, t - t₀ ∈ Ioo lo₀ hi₀ := fun t ht =>
    ⟨by linarith [le_max_left (t₀ + lo₀) (t₀ / 2), ht.1],
      by linarith [min_le_left (t₀ + hi₀) (min (t₁ + δ) ((t₁ + T) / 2)), ht.2]⟩
  have hXt : ∀ t ∈ Ioo lo hi, ∀ y, Xt t y = gradFun (S.family.metric t) (f t) y := by
    intro t ht y
    refine hXeq t ⟨?_, ?_⟩ y
    · linarith [le_max_right (t₀ + lo₀) (t₀ / 2), ht.1]
    · linarith [(min_le_right (t₀ + hi₀) _).trans (min_le_left (t₁ + δ) ((t₁ + T) / 2)), ht.2]
  have hback : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M => (q.1 - t₀, q.2)) :=
    ContMDiff.prodMk (contMDiff_fst.sub contMDiff_const) contMDiff_snd
  have hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ₀ (q.1 - t₀) q.2)
      (Ioo lo hi ×ˢ univ) :=
    hΦsm.comp hback.contMDiffOn (fun q hq => ⟨hmem q.1 hq.1, mem_univ _⟩)
  refine ⟨fun s x => Φ₀ (s - t₀) x, lo, hi, hlo_pos, hlo_t₀, hhi_t₁, hhi_T,
    fun x => by simpa using hΦ0 x, hjoint, fun t ht x => ?_, fun t ht => ?_⟩
  · have hat := hvel (t - t₀) (hmem t ht) x
    have htrans : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s - t₀) t (1 : ℝ →L[ℝ] ℝ) := by
      have h := hasMFDerivAt_add_const_one (-t₀) t
      have hfun : (fun s : ℝ => s + -t₀) = fun s => s - t₀ := by
        funext s
        ring
      rwa [hfun] at h
    have hcomp := hat.comp t htrans
    have hYt : Y (t - t₀) (Φ₀ (t - t₀) x) =
        gradFun (S.family.metric t) (f t) (Φ₀ (t - t₀) x) := by
      simp only [Y, sub_add_cancel]
      exact hXt t ht _
    rw [hYt] at hcomp
    exact hcomp.congr_mfderiv (by ext; rfl)
  · rcases ht.1.eq_or_lt with h | hlt
    · refine ⟨Diffeomorph.refl I M ∞, fun x => ?_⟩
      rw [← h]
      simpa using (hΦ0 x).symm
    · have hτ : t - t₀ ∈ Ico (0 : ℝ) hi₀ :=
        ⟨by linarith, by linarith [min_le_left (t₀ + hi₀) (min (t₁ + δ) ((t₁ + T) / 2)), ht.2]⟩
      have hslice : ContMDiff I I ∞ (Φ₀ (t - t₀)) := by
        intro y
        have hm : ((t - t₀, y) : ℝ × M) ∈ Ioo lo₀ hi₀ ×ˢ (univ : Set M) :=
          ⟨⟨by linarith, hτ.2⟩, mem_univ _⟩
        have hat := hΦsm.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hm)
        exact hat.comp y (contMDiffAt_const.prodMk contMDiffAt_id)
      obtain ⟨d, hd, -⟩ := time_dependent_vf_diffeomorph_slice_of_smooth_bijective
        (Φ₀ (t - t₀)) (Ψ₀ (t - t₀)) hslice (hΨsm (t - t₀) (by linarith) hτ.2)
        (fun x => hΨΦ (t - t₀) hτ x) (fun x => hΦΨ (t - t₀) hτ x)
      exact ⟨d, hd⟩

omit [CompactSpace M] in
theorem gradient_flow_window_eq
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    {t₀ c d : ℝ} (hc : 0 < c) (hct : c < t₀) (htd : t₀ < d) (hdT : d < T)
    (Φ Φ' : ℝ → M → M) (h0 : ∀ x, Φ t₀ x = x) (h0' : ∀ x, Φ' t₀ x = x)
    (hv : ∀ t ∈ Ioo c d, ∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (gradFun (S.family.metric t) (f t) (Φ t x))))
    (hv' : ∀ t ∈ Ioo c d, ∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ' s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (gradFun (S.family.metric t) (f t) (Φ' t x)))) :
    ∀ t ∈ Ioo c d, ∀ x, Φ t x = Φ' t x := by
  have hint := surfaceFlow_gradient_field_contMDiffOn S hS f hf
  obtain ⟨Xt, δ, hδ, hXeq, -, hXC1⟩ := interior_field_global_cutoff_extension
    (fun s y => gradFun (S.family.metric s) (f s) y) T hint (a := c) (b := d) hc hdT
  have hXt : ∀ t ∈ Ioo c d, ∀ y, Xt t y = gradFun (S.family.metric t) (f t) y := fun t ht y =>
    hXeq t ⟨by linarith [ht.1], by linarith [ht.2]⟩ y
  intro t ht x
  refine integral_curves_eqOn_of_jointC1 Xt hXC1 Φ Φ' x x ⟨hct, htd⟩ (fun s hs => ?_)
    (fun s hs => ?_) (by rw [h0, h0']) t ht
  · rw [hXt s hs]
    exact (hv s hs x).hasMFDerivWithinAt
  · rw [hXt s hs]
    exact (hv' s hs x).hasMFDerivWithinAt

omit [CompactSpace M] in
theorem exists_lt_seq_of_lt {t₀ t : ℝ} (ht : t < T) :
    ∃ n : ℕ, t < T - (T - t₀) / ((n : ℝ) + 2) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|T - t₀| / (T - t))
  refine ⟨n, ?_⟩
  have hgap : 0 < T - t := sub_pos.mpr ht
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h1 : (T - t₀) / ((n : ℝ) + 2) < T - t := by
    rw [div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hgap] at hn
    nlinarith [le_abs_self (T - t₀), abs_nonneg (T - t₀)]
  linarith

theorem surfaceFlow_exists_gradient_flow
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) :
    ∃ ψ : ℝ → (M ≃ₘ⟮I, I⟯ M), (∀ x, ψ t₀ x = x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ψ q.1 q.2) (Ioo t₀ T ×ˢ univ) ∧
      (∀ x, ContinuousWithinAt (fun s => ψ s x) (Ici t₀) t₀) ∧
      (∀ t ∈ Ioo t₀ T, ∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => ψ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (gradFun (S.family.metric t) (f t) (ψ t x)))) ∧
      (∀ x, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s => ψ s x) (Ici t₀) t₀
        ((1 : ℝ →L[ℝ] ℝ).smulRight (gradFun (S.family.metric t₀) (f t₀) x))) := by
  classical
  let tseq : ℕ → ℝ := fun n => T - (T - t₀) / ((n : ℝ) + 2)
  have hseq0 : ∀ n, t₀ < tseq n := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h : (T - t₀) / ((n : ℝ) + 2) < T - t₀ := by
      rw [div_lt_iff₀ hpos]
      nlinarith [ht₀.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [tseq]
    linarith
  have hseqT : ∀ n, tseq n < T := by
    intro n
    have : 0 < (T - t₀) / ((n : ℝ) + 2) := div_pos (by linarith [ht₀.2]) (by positivity)
    simp only [tseq]
    linarith
  have hwin : ∀ n : ℕ, ∃ (Φ : ℝ → M → M) (lo hi : ℝ), 0 < lo ∧ lo < t₀ ∧ tseq n < hi ∧ hi < T ∧
      (∀ x, Φ t₀ x = x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) (Ioo lo hi ×ˢ univ) ∧
      (∀ t ∈ Ioo lo hi, ∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (gradFun (S.family.metric t) (f t) (Φ t x)))) ∧
      (∀ t ∈ Ico t₀ hi, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x, d x = Φ t x) := fun n =>
    surfaceFlow_exists_gradient_flow_window_open S hS f hf ht₀.1 (hseq0 n) (hseqT n)
  choose W lo hi hlo hlot hhit hhiT hW0 hWsm hWv hWd using hwin
  have hagree : ∀ n m : ℕ, ∀ t ∈ Ico t₀ (min (hi n) (hi m)), ∀ x, W n t x = W m t x := by
    intro n m t ht x
    rcases ht.1.eq_or_lt with h | h
    · rw [← h, hW0, hW0]
    exact gradient_flow_window_eq S hS f hf (c := max (lo n) (lo m)) (d := min (hi n) (hi m))
      (lt_max_of_lt_left (hlo n)) (max_lt (hlot n) (hlot m))
      (lt_min (hseq0 n |>.trans (hhit n)) (hseq0 m |>.trans (hhit m)))
      ((min_le_left _ _).trans_lt (hhiT n)) (W n) (W m) (hW0 n) (hW0 m)
      (fun s hs y => hWv n s ⟨(le_max_left _ _).trans_lt hs.1, hs.2.trans_le (min_le_left _ _)⟩ y)
      (fun s hs y => hWv m s ⟨(le_max_right _ _).trans_lt hs.1, hs.2.trans_le (min_le_right _ _)⟩ y)
      t ⟨(max_lt (hlot n) (hlot m)).trans h, ht.2⟩ x
  have hex : ∀ t, t < T → ∃ n, t < tseq n := fun t ht => exists_lt_seq_of_lt ht
  let idx : ℝ → ℕ := fun t => if h : ∃ n, t < tseq n then Nat.find h else 0
  have hidx : ∀ t, t < T → t < tseq (idx t) := by
    intro t ht
    have h := hex t ht
    simp only [idx, dite_eq_left h]
    exact Nat.find_spec h
  have hidx_le : ∀ t n, t < tseq n → idx t ≤ n := by
    intro t n htn
    have h : ∃ n, t < tseq n := ⟨n, htn⟩
    simp only [idx, dite_eq_left h]
    exact Nat.find_min' h htn
  have hloc : ∀ n, ∀ s ∈ Ico t₀ (tseq n), ∀ x, W (idx s) s x = W n s x := by
    intro n s hs x
    have hsT : s < T := hs.2.trans (hseqT n)
    exact hagree (idx s) n s ⟨hs.1, lt_min ((hidx s hsT).trans (hhit _))
      (hs.2.trans (hhit n))⟩ x
  have hdiff : ∀ t ∈ Ico t₀ T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x, d x = W (idx t) t x := fun t ht =>
    hWd (idx t) t ⟨ht.1, (hidx t ht.2).trans (hhit _)⟩
  let ψ : ℝ → (M ≃ₘ⟮I, I⟯ M) := fun t =>
    if h : t ∈ Ico t₀ T then Classical.choose (hdiff t h) else Diffeomorph.refl I M ∞
  have hψ : ∀ t ∈ Ico t₀ T, ∀ x, ψ t x = W (idx t) t x := by
    intro t ht x
    simp only [ψ, dite_eq_left ht]
    exact Classical.choose_spec (hdiff t ht) x
  have hψn : ∀ n, ∀ s ∈ Ico t₀ (tseq n), ∀ x, ψ s x = W n s x := fun n s hs x => by
    rw [hψ s ⟨hs.1, hs.2.trans (hseqT n)⟩, hloc n s hs]
  have hmemW : ∀ n, Ico t₀ (tseq n) ⊆ Ioo (lo n) (hi n) := fun n s hs =>
    ⟨(hlot n).trans_le hs.1, hs.2.trans (hhit n)⟩
  have hnhds0 : ∀ x, (fun s => ψ s x) =ᶠ[𝓝[Ici t₀] t₀] fun s => W 0 s x := by
    intro x
    have hmem : Ico t₀ (tseq 0) ∈ 𝓝[Ici t₀] t₀ := Ico_mem_nhdsGE (hseq0 0)
    filter_upwards [hmem] with s hs
    exact hψn 0 s hs x
  have hW0at : ∀ x, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun s => W 0 s x) t₀ := by
    intro x
    have hm : ((t₀, x) : ℝ × M) ∈ Ioo (lo 0) (hi 0) ×ˢ (univ : Set M) :=
      ⟨⟨hlot 0, (hseq0 0).trans (hhit 0)⟩, mem_univ _⟩
    have hat := (hWsm 0).contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hm)
    exact hat.comp t₀ (contMDiffAt_id.prodMk contMDiffAt_const)
  refine ⟨ψ, fun x => ?_, ?_, fun x => ?_, fun t ht x => ?_, fun x => ?_⟩
  · rw [hψ t₀ ⟨le_rfl, ht₀.2⟩, hW0]
  · intro q hq
    obtain ⟨n, hn⟩ := hex q.1 hq.1.2
    have hU : Ioo t₀ (tseq n) ×ˢ (univ : Set M) ∈ 𝓝 q :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hq.1.1, hn⟩, mem_univ _⟩
    have hWq : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => W n q.1 q.2) q :=
      (hWsm n).contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        ⟨hmemW n ⟨hq.1.1.le, hn⟩, mem_univ _⟩)
    refine (hWq.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hU] with p hp
    exact hψn n p.1 ⟨hp.1.1.le, hp.1.2⟩ p.2
  · exact ((hW0at x).continuousAt.continuousWithinAt).congr_of_eventuallyEq (hnhds0 x)
      (by rw [hψn 0 t₀ ⟨le_rfl, hseq0 0⟩])
  · obtain ⟨n, hn⟩ := hex t ht.2
    have hev : (fun s => ψ s x) =ᶠ[𝓝 t] fun s => W n s x := by
      filter_upwards [isOpen_Ioo.mem_nhds (⟨ht.1, hn⟩ : t ∈ Ioo t₀ (tseq n))] with s hs
      exact hψn n s ⟨hs.1.le, hs.2⟩ x
    have hv := hWv n t (hmemW n ⟨ht.1.le, hn⟩) x
    rw [← hψn n t ⟨ht.1.le, hn⟩ x] at hv
    exact hv.congr_of_eventuallyEq hev
  · have hv := (hWv 0 t₀ (hmemW 0 ⟨le_rfl, hseq0 0⟩) x).hasMFDerivWithinAt (s := Ici t₀)
    rw [hW0] at hv
    exact hv.congr_of_eventuallyEq (hnhds0 x) (by rw [hψn 0 t₀ ⟨le_rfl, hseq0 0⟩])

def flowExtinctionTime
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) : ℝ :=
  surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0)

theorem surfaceFlow_exists_potential_gauge [NeZero (Module.finrank ℝ E)] [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    (hfeq : ∀ t ∈ Ioo 0 T, ∀ x,
      ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) :
    ∃ ψ : ℝ → (M ≃ₘ⟮I, I⟯ M), (∀ x, ψ t₀ x = x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ψ q.1 q.2) (Ioo t₀ T ×ˢ univ) ∧
      (∀ x, ContinuousWithinAt (fun s => ψ s x) (Ici t₀) t₀) ∧
      (∀ t ∈ Ioo t₀ T, ∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => ψ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (gradFun (S.family.metric t) (f t) (ψ t x)))) ∧
      ∀ t ∈ Ioo t₀ T, ∀ x (v w : TangentSpace I x),
        HasDerivAt (fun s => 1 / (2 * (flowExtinctionTime S - s)) *
            (Diffeomorph.pullbackMetric (S.family.metric s) (ψ s)).inner x v w)
          (1 / (flowExtinctionTime S - t) *
            tracelessHessAt (S.family.metric t) (f t) (ψ t x)
              (vec2 (mfderiv I I (ψ t) x v) (mfderiv I I (ψ t) x w))) t := by
  obtain ⟨ψ, hψ0, hψsm, hψc, hψv, -⟩ := surfaceFlow_exists_gradient_flow S hS f hf ht₀
  have hTT : T ≤ flowExtinctionTime S := surfaceFlow_le_extinctionTime hT S hS hdim hscal
  exact ⟨ψ, hψ0, hψsm, hψc, hψv, surfaceFlow_pullback_normalized_hasDerivAt hdim S hS f hTT hfeq
    ht₀.1 le_rfl ψ hψsm hψv⟩

end GC.Geometry
