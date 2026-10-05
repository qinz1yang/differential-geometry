import DifferentialGeometry.Geometry.Comparison.FiniteSoul.BandProduct

/-!
# Distance to the soul along a soul-outward flow (lane CMS3-FLOW2, G2)

Blueprint LFR46 (A:28948–28958): "Distance composed with the flow is locally Lipschitz, and its
almost-everywhere derivative is at least `c_B` while in that annulus. Integration proves strict
increase, finite-time crossing of each higher level, and a unique backward crossing of
`{d_S = ℓ}` from any point with `d_S ≥ ℓ`."

Data: a continuous field `X`, a jointly continuous flow `φ` of `X` (`φ 0 = id`, group law,
`∂ₜ φ = X ∘ φ`), and strict soul-outwardness `g(X, u) < 0` against all minimizing directions to the
compact `S` on `{d_S ≥ a}`, `a > 0`.

* `strictMono_of_local_two_sided`: a real lemma (local two-sided strict increase on `{f ≥ a}` gives
  global strict increase from any time where `f ≥ a`).
* `exists_rate_of_isCompact_outward`: a uniform rate `κ > 0` on an open neighbourhood of a compact
  subset of `{d_S ≥ a}` (S-PATCH margins + CM-D first variation).
* `infDist_flow_lt_of_le`: strict increase of `d_S ∘ φ_t` after any time where `d_S ≥ a`.
* `exists_flow_infDist_eq_of_le`: backward crossing of every level `c ∈ [a, d_S q]`.
* `existsUnique_flow_infDist_eq`: the crossing time of a level `c ≥ a` is unique; it is the S-HIT
  `hittingTime` (`hittingTime_eq_of_infDist_eq`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

/-- **Strict increase from local two-sided increase.** -/
theorem strictMono_of_local_two_sided {f : ℝ → ℝ} (hf : Continuous f) {a : ℝ}
    (hloc : ∀ t, a ≤ f t → ∃ η > 0, (∀ s ∈ Ioo t (t + η), f t < f s) ∧
      ∀ s ∈ Ioo (t - η) t, f s < f t)
    {t₀ t : ℝ} (ht₀ : a ≤ f t₀) (ht : t₀ < t) : f t₀ < f t := by
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨η, hη, hηr, -⟩ := hloc t₀ ht₀
  set A : Set ℝ := {s | t₀ + η / 2 ≤ s ∧ f s ≤ f t₀} with hAdef
  have hAsub : ∀ s, t₀ < s → f s ≤ f t₀ → s ∈ A := by
    intro s hs hfs
    refine ⟨?_, hfs⟩
    by_contra hlt
    rw [not_le] at hlt
    have := hηr s ⟨hs, by linarith⟩
    linarith
  have htA : t ∈ A := hAsub t ht hcon
  have hAc : IsClosed A :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_le hf continuous_const)
  have hAbdd : BddBelow A := ⟨t₀ + η / 2, fun s hs => hs.1⟩
  set T := sInf A with hT
  have hTA : T ∈ A := hAc.csInf_mem ⟨t, htA⟩ hAbdd
  have hT₀ : t₀ < T := by linarith [hTA.1]
  have hbefore : ∀ s, t₀ < s → s < T → f t₀ < f s := by
    intro s hs hsT
    by_contra hle
    rw [not_lt] at hle
    have := csInf_le hAbdd (hAsub s hs hle)
    linarith
  -- `f T = f t₀` by continuity from the left
  have hge : f t₀ ≤ f T := by
    have hlim : Tendsto f (𝓝[<] T) (𝓝 (f T)) := hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hT₀] with s hs
    exact (hbefore s hs.1 hs.2).le
  have hTeq : f T = f t₀ := le_antisymm hTA.2 hge
  obtain ⟨η', hη', -, hηl⟩ := hloc T (by rw [hTeq]; exact ht₀)
  set s := max (T - η' / 2) ((t₀ + T) / 2) with hs
  have hs1 : t₀ < s := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hs2 : s < T := max_lt (by linarith) (by linarith)
  have h1 := hηl s ⟨lt_of_lt_of_le (by linarith) (le_max_left _ _), hs2⟩
  have h2 := hbefore s hs1 hs2
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **A uniform rate near a compact set of the outward region.** -/
theorem exists_rate_of_isCompact_outward
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) (X : (x : M) → TangentSpace I x)
    (hXc : Continuous (fun x => (⟨x, X x⟩ : TangentBundle I M)))
    {φ : ℝ → M → M} (hφc : Continuous (fun p : ℝ × M => φ p.1 p.2)) (hφ0 : ∀ x, φ 0 x = x)
    (hder : ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (φ t x))))
    {K : Set M} (hK : IsCompact K) (hKS : ∀ x ∈ K, x ∉ S)
    (hout : ∀ x ∈ K, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (X x) u < 0) :
    ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧ ∃ κ > 0, ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, φ s x ∈ U) →
      infDist x S + κ * t ≤ infDist (φ t x) S := by
  have hDbdd : ∀ x, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x u u ≤ 1 :=
    fun _ _ hu => hu.1.le
  have hDclosed : ∀ (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M),
      (∀ k, (p k).snd ∈ g.finiteMinimizingDirectionsTo S (p k).proj) →
        Tendsto p atTop (𝓝 pInf) → pInf.snd ∈ g.finiteMinimizingDirectionsTo S pInf.proj :=
    fun _ _ hp hlim => g.mem_finiteMinimizingDirectionsTo_of_tendsto hr hnorm hSc.isClosed hp hlim
  obtain ⟨κ, hκ, hκK⟩ := exists_margin_of_isCompact g (fun x => g.finiteMinimizingDirectionsTo S x)
    hDbdd hDclosed X hXc hK (c := 0) (fun x hx u hu => by rw [neg_zero]; exact hout x hx u hu)
  set U : Set M := interior {y | ∀ u ∈ g.finiteMinimizingDirectionsTo S y,
    g.inner y (X y) u < -(κ / 2)} ∩ Sᶜ with hUdef
  refine ⟨U, isOpen_interior.inter hSc.isClosed.isOpen_compl, fun x hx => ⟨?_, hKS x hx⟩, κ / 2,
    half_pos hκ, infDist_add_mul_le_flow g hr hnorm hSc.isClosed hSne hφc hφ0 X hder
      (fun x hx => hx.2) (fun x hx u hu => (interior_subset hx.1 u hu).le)⟩
  rw [mem_interior_iff_mem_nhds]
  exact eventually_forall_inner_lt g (fun x => g.finiteMinimizingDirectionsTo S x) hDbdd
    hDclosed X isOpen_univ hXc.continuousOn (mem_univ x) (fun u hu => by
      have := hκK x hx u hu
      linarith)

/-- **Strict increase of `d_S` along the flow** after any time where `d_S ≥ a`. -/
theorem infDist_flow_lt_of_le
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) (X : (x : M) → TangentSpace I x)
    (hXc : Continuous (fun x => (⟨x, X x⟩ : TangentBundle I M)))
    {φ : ℝ → M → M} (hφc : Continuous (fun p : ℝ × M => φ p.1 p.2)) (hφ0 : ∀ x, φ 0 x = x)
    (hφadd : ∀ s t x, φ (s + t) x = φ s (φ t x))
    (hder : ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (φ t x))))
    {a : ℝ} (ha : 0 < a)
    (hout : ∀ q, a ≤ infDist q S → ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q (X q) u < 0)
    (x : M) {t₀ t : ℝ} (ht₀ : a ≤ infDist (φ t₀ x) S) (ht : t₀ < t) :
    infDist (φ t₀ x) S < infDist (φ t x) S := by
  have hcurve : Continuous (fun s : ℝ => φ s x) := hφc.comp (continuous_id.prodMk continuous_const)
  refine strictMono_of_local_two_sided (f := fun s => infDist (φ s x) S)
    ((continuous_infDist_pt S).comp hcurve) (a := a) (fun τ hτ => ?_) ht₀ ht
  set y := φ τ x with hy
  have hyS : y ∉ S := fun hyS => by
    have : infDist y S = 0 := infDist_zero_of_mem hyS
    change a ≤ infDist y S at hτ
    linarith
  obtain ⟨U, hU, hyU, κ, hκ, hrate⟩ := exists_rate_of_isCompact_outward g hr hnorm hSc hSne X hXc
    hφc hφ0 hder (K := {y}) isCompact_singleton (fun z hz => by rw [mem_singleton_iff.mp hz]; exact hyS)
    (fun z hz => (mem_singleton_iff.mp hz) ▸ hout y hτ)
  have hev : ∀ᶠ s in 𝓝 τ, φ s x ∈ U :=
    hcurve.continuousAt.preimage_mem_nhds (hU.mem_nhds (hyU (mem_singleton y)))
  obtain ⟨η, hη, hηU⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨η, hη, fun s hs => ?_, fun s hs => ?_⟩
  · have h := hrate y (s - τ) (by linarith [hs.1]) (fun σ hσ => by
      rw [hy, ← hφadd]
      apply hηU
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hσ.1, hσ.2, hs.2])
    rw [hy, ← hφadd, sub_add_cancel] at h
    change infDist (φ τ x) S < infDist (φ s x) S
    nlinarith [hs.1]
  · have h := hrate (φ s x) (τ - s) (by linarith [hs.2]) (fun σ hσ => by
      rw [← hφadd]
      apply hηU
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hσ.1, hσ.2, hs.1, hs.2])
    rw [← hφadd, sub_add_cancel] at h
    change infDist (φ s x) S < infDist (φ τ x) S
    nlinarith [hs.2]

/-- **Backward crossing** of every level `c ∈ [a, d_S q]`. -/
theorem exists_flow_infDist_eq_of_le
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) (X : (x : M) → TangentSpace I x)
    (hXc : Continuous (fun x => (⟨x, X x⟩ : TangentBundle I M)))
    {φ : ℝ → M → M} (hφc : Continuous (fun p : ℝ × M => φ p.1 p.2)) (hφ0 : ∀ x, φ 0 x = x)
    (hφadd : ∀ s t x, φ (s + t) x = φ s (φ t x))
    (hder : ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (φ t x))))
    {a : ℝ} (ha : 0 < a)
    (hout : ∀ q, a ≤ infDist q S → ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q (X q) u < 0)
    {q : M} {c : ℝ} (hac : a ≤ c) (hcq : c ≤ infDist q S) :
    ∃ t ≤ 0, infDist (φ t q) S = c := by
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have hcurve : Continuous (fun s : ℝ => φ s q) := hφc.comp (continuous_id.prodMk continuous_const)
  have hfc : Continuous (fun s : ℝ => infDist (φ s q) S) := (continuous_infDist_pt S).comp hcurve
  by_cases hex : ∃ t ≤ 0, infDist (φ t q) S ≤ c
  · obtain ⟨t, ht, htc⟩ := hex
    obtain ⟨s, hs, hsc⟩ := intermediate_value_Icc ht hfc.continuousOn
      (show c ∈ Icc (infDist (φ t q) S) (infDist (φ 0 q) S) by rw [hφ0]; exact ⟨htc, hcq⟩)
    exact ⟨s, hs.2, hsc⟩
  · simp only [not_exists, not_and, not_le] at hex
    exfalso
    set K : Set M := (fun x => infDist x S) ⁻¹' Icc c (infDist q S) with hKdef
    have hK : IsCompact K := isCompact_infDist_band hSc hSne c (infDist q S)
    have hKS : ∀ x ∈ K, x ∉ S := fun x hx hxS => by
      have h0 : infDist x S = 0 := infDist_zero_of_mem hxS
      have : c ≤ infDist x S := hx.1
      linarith
    obtain ⟨U, -, hKU, κ, hκ, hrate⟩ := exists_rate_of_isCompact_outward g hr hnorm hSc hSne X
      hXc hφc hφ0 hder hK hKS (fun x hx u hu => hout x (hac.trans hx.1) u hu)
    have hmem : ∀ t ≤ 0, φ t q ∈ K := by
      intro t ht
      refine ⟨(hex t ht).le, ?_⟩
      rcases eq_or_lt_of_le ht with h | h
      · rw [h, hφ0]
      · have := infDist_flow_lt_of_le g hr hnorm hSc hSne X hXc hφc hφ0 hφadd hder ha hout q
          (t₀ := t) (t := 0) (hac.trans (hex t ht).le) h
        rw [hφ0] at this
        exact this.le
    set T : ℝ := (infDist q S - c) / κ + 1 with hT
    have hTpos : 0 < T := by
      have : 0 ≤ (infDist q S - c) / κ := div_nonneg (by linarith) hκ.le
      linarith
    have h := hrate (φ (-T) q) T hTpos.le (fun s hs => by
      rw [← hφadd]
      exact hKU (hmem _ (by linarith [hs.2])))
    rw [← hφadd, add_neg_cancel, hφ0] at h
    have hc := hex (-T) (by linarith)
    have hκT : κ * T = infDist q S - c + κ := by
      rw [hT, mul_add, mul_div_cancel₀ _ hκ.ne', mul_one]
    linarith

/-- **Unique crossing** of a level `c ≥ a` from a point with `d_S ≥ c`. -/
theorem existsUnique_flow_infDist_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) (X : (x : M) → TangentSpace I x)
    (hXc : Continuous (fun x => (⟨x, X x⟩ : TangentBundle I M)))
    {φ : ℝ → M → M} (hφc : Continuous (fun p : ℝ × M => φ p.1 p.2)) (hφ0 : ∀ x, φ 0 x = x)
    (hφadd : ∀ s t x, φ (s + t) x = φ s (φ t x))
    (hder : ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (φ t x))))
    {a : ℝ} (ha : 0 < a)
    (hout : ∀ q, a ≤ infDist q S → ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q (X q) u < 0)
    {q : M} {c : ℝ} (hac : a ≤ c) (hcq : c ≤ infDist q S) :
    ∃! t : ℝ, infDist (φ t q) S = c := by
  obtain ⟨t, -, ht⟩ := exists_flow_infDist_eq_of_le g hr hnorm hSc hSne X hXc hφc hφ0 hφadd hder ha
    hout hac hcq
  refine ⟨t, ht, fun t' ht' => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := infDist_flow_lt_of_le g hr hnorm hSc hSne X hXc hφc hφ0 hφadd hder ha hout q
      (by rw [ht']; exact hac) hlt
    rw [ht, ht'] at this
    exact lt_irrefl _ this
  · have := infDist_flow_lt_of_le g hr hnorm hSc hSne X hXc hφc hφ0 hφadd hder ha hout q
      (by rw [ht]; exact hac) hlt
    rw [ht, ht'] at this
    exact lt_irrefl _ this

/-- **The crossing time is the S-HIT hitting time.** -/
theorem hittingTime_eq_of_infDist_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) (X : (x : M) → TangentSpace I x)
    (hXc : Continuous (fun x => (⟨x, X x⟩ : TangentBundle I M)))
    {φ : ℝ → M → M} (hφc : Continuous (fun p : ℝ × M => φ p.1 p.2)) (hφ0 : ∀ x, φ 0 x = x)
    (hφadd : ∀ s t x, φ (s + t) x = φ s (φ t x))
    (hder : ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (φ t x))))
    {a : ℝ} (ha : 0 < a)
    (hout : ∀ q, a ≤ infDist q S → ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q (X q) u < 0)
    {q : M} {c : ℝ} (hac : a ≤ c) (hcq : c ≤ infDist q S) {t : ℝ}
    (ht : infDist (φ t q) S = c) :
    hittingTime φ (fun x => infDist x S) q c = t := by
  obtain ⟨t₀, ht₀, hc₀⟩ := exists_flow_infDist_eq_of_le g hr hnorm hSc hSne X hXc hφc hφ0 hφadd
    hder ha hout hac hcq
  have huniq := existsUnique_flow_infDist_eq g hr hnorm hSc hSne X hXc hφc hφ0 hφadd hder ha hout
    hac hcq
  have hspec : ∃ t : ℝ, infDist (φ t q) S = c ∧
      ∀ u ∈ uIcc 0 t, infDist (φ u q) S ∈ uIcc (infDist q S) c := by
    refine ⟨t₀, hc₀, fun u hu => ?_⟩
    rw [uIcc_of_ge ht₀] at hu
    rw [uIcc_of_ge hcq]
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hu.1 with h | h
      · rw [← h, hc₀]
      · have := infDist_flow_lt_of_le g hr hnorm hSc hSne X hXc hφc hφ0 hφadd hder ha hout q
          (by rw [hc₀]; exact hac) h
        rw [hc₀] at this
        exact this.le
    · rcases eq_or_lt_of_le hu.2 with h | h
      · rw [h, hφ0]
      · have hu1 : c ≤ infDist (φ u q) S := by
          rcases eq_or_lt_of_le hu.1 with h' | h'
          · rw [← h', hc₀]
          · have := infDist_flow_lt_of_le g hr hnorm hSc hSne X hXc hφc hφ0 hφadd hder ha hout q
              (by rw [hc₀]; exact hac) h'
            rw [hc₀] at this
            exact this.le
        have := infDist_flow_lt_of_le g hr hnorm hSc hSne X hXc hφc hφ0 hφadd hder ha hout q
          (hac.trans hu1) h
        rw [hφ0] at this
        exact this.le
  unfold hittingTime
  rw [dite_eq_left hspec]
  exact huniq.unique hspec.choose_spec.1 ht

end DifferentialGeometry.Geometry.FiniteSoul
