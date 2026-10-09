import DifferentialGeometry.Geometry.Comparison.FiniteSoul.BandProduct
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.RadialLength

/-!
# Quantitative S-PATCH and the SAME outward field for LFR23 → LFR24 (disposition D4)

Package CM-S (finite soul), lane CMS-T; thin corollaries of lane CMS-H's accepted modules
`FiniteSoul/{OutwardPatch, HittingTime, BandProduct}.lean`. Blueprint master207A LFR23
(A:26745–26806: "the negative of any inward direction has pairing less than `−7/8` with all the
others … a smooth outward field on a neighborhood of this closed band, with norm less than two and
pairing less than `−3/4` with EVERY inward direction") and LFR24 (A:26900–26905:
`dF(V) > 3/4 − 2ε > 1/2` for LFR23's SAME field).

* `exists_outward_field_seven_eighths`: unit vectors with pairing `< −7/8` against every minimizing
  direction on a closed set `A` ⇒ ONE smooth field, `|V| < 2` everywhere, pairing `< −3/4`
  against every minimizing direction on an open `O ⊇ A`.
* `exists_outward_field_margin_of_isCompact`: the general compact-band version, strict pairing
  `< 0` ⇒ a uniform positive margin on an open neighbourhood.
* `exists_endpoint_band_field`: the LFR23 package for the SAME field: `V`, its complete flow,
  the rate `3/4` of `d_S` along it, the continuous and UNIQUE hitting time, the projection to a
  level, the band product `{d_S = c} × [a, b] ≃ₜ {a ≤ d_S ≤ b}` and its coordinate identities.
* `lt_inner_of_outward_field`, `one_half_lt_inner_of_outward_field`: LFR24's
  `dh(V) > 3/4 − 2ε > 1/2` from `|V| < 2`, `g(V, u) < −3/4`, `|∇h + u| < ε`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- **LFR24's derivative bound** at one point: if `|V| < 2`, `g(V, u) < −3/4` and
`|w + u| < ε`, then `g(w, V) > 3/4 − 2ε` (`w = ∇h`, `u` a minimizing direction). -/
theorem lt_inner_of_outward_field {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M) {V u w : E}
    {ε : ℝ} (hε : 0 ≤ ε) (hV : g.inner x V V < 2 ^ 2) (hVu : g.inner x V u < -(3 / 4))
    (hwu : g.inner x (w + u) (w + u) < ε ^ 2) : 3 / 4 - 2 * ε < g.inner x w V := by
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner x with hB
  have hsym : ∀ a b, B a b = B b a := fun a b => g.symm x a b
  have hnn : ∀ a, 0 ≤ B a a := fun a => by
    by_cases ha : a = 0
    · rw [ha, map_zero]
    · exact (g.pos x a ha).le
  change B V V < 2 ^ 2 at hV
  change B V u < -(3 / 4) at hVu
  change B (w + u) (w + u) < ε ^ 2 at hwu
  change 3 / 4 - 2 * ε < B w V
  have hcs := Bundle.ContMDiffRiemannianMetric.le_sqrt_mul_sqrt_of_psd B hsym hnn (-(w + u)) V
  have hneg : B (-(w + u)) (-(w + u)) = B (w + u) (w + u) := by
    simp only [map_neg, neg_apply, neg_neg]
  rw [hneg] at hcs
  have hs1 : Real.sqrt (B (w + u) (w + u)) < ε := by
    rw [Real.sqrt_lt' (by nlinarith [hnn (w + u)])]
    exact hwu
  have hs2 : Real.sqrt (B V V) < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    exact hV
  have hprod : Real.sqrt (B (w + u) (w + u)) * Real.sqrt (B V V) ≤ ε * 2 :=
    mul_le_mul hs1.le hs2.le (Real.sqrt_nonneg _) hε
  have hsplit : B w V = B (w + u) V - B u V := by
    simp only [map_add, add_apply]
    ring
  have hlin : B (-(w + u)) V = -B (w + u) V := by simp only [map_neg, neg_apply]
  rw [hlin] at hcs
  rw [hsplit, hsym u V]
  have hε' : 0 < ε := by
    rcases eq_or_lt_of_le hε with h | h
    · rw [← h] at hwu; nlinarith [hnn (w + u)]
    · exact h
  nlinarith

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- **LFR24, `dh(V) > 1/2`**: for `ε ≤ 1/8`. -/
theorem one_half_lt_inner_of_outward_field {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M) {V u w : E}
    {ε : ℝ} (hε : 0 ≤ ε) (hε8 : ε ≤ 1 / 8) (hV : g.inner x V V < 2 ^ 2)
    (hVu : g.inner x V u < -(3 / 4)) (hwu : g.inner x (w + u) (w + u) < ε ^ 2) :
    1 / 2 < g.inner x w V := by
  have h := lt_inner_of_outward_field g x hε hV hVu hwu
  linarith

section Binding

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

/-- **Quantitative S-PATCH (D4)**: unit vectors with pairing `< −7/8` against every minimizing
direction to `S` on a closed set `A` give ONE smooth field with `|V| < 2` everywhere and pairing
`< −3/4` against EVERY minimizing direction on an open neighbourhood of `A`. -/
theorem exists_outward_field_seven_eighths [SigmaCompactSpace M] [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S A : Set M} (hS : IsClosed S) (hA : IsClosed A) (w : (x : M) → TangentSpace I x)
    (hwunit : ∀ x ∈ A, g.inner x (w x) (w x) = 1)
    (hwout : ∀ x ∈ A, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (w x) u < -(7 / 8)) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      (∀ x, g.inner x (V x) (V x) < 2 ^ 2) ∧
      ∃ O : Set M, IsOpen O ∧ A ⊆ O ∧
        ∀ x ∈ O, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (V x) u < -(3 / 4) :=
  exists_contMDiff_outward_field_minimizingDirections g hr hnorm hS hA two_pos w
    (fun x hx => by rw [hwunit x hx]; norm_num)
    (fun x hx u hu => (hwout x hx u hu).trans (by norm_num))

/-- **S-PATCH with a uniform margin on a compact band**: unit vectors with strict pairing `< 0`
against every minimizing direction on a compact `K` give one smooth field with `|V| < 2` and a
uniform pairing `< −c`, `c > 0`, on an open neighbourhood of `K`. -/
theorem exists_outward_field_margin_of_isCompact [SigmaCompactSpace M] [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S K : Set M} (hS : IsClosed S) (hK : IsCompact K) (w : (x : M) → TangentSpace I x)
    (hwunit : ∀ x ∈ K, g.inner x (w x) (w x) = 1)
    (hwout : ∀ x ∈ K, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (w x) u < 0) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      (∀ x, g.inner x (V x) (V x) < 2 ^ 2) ∧
      ∃ c > 0, ∃ O : Set M, IsOpen O ∧ K ⊆ O ∧
        ∀ x ∈ O, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (V x) u < -c := by
  have hDbdd : ∀ x, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x u u ≤ 1 :=
    fun _ _ hu => hu.1.le
  have hDclosed : ∀ (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M),
      (∀ k, (p k).snd ∈ g.finiteMinimizingDirectionsTo S (p k).proj) →
        Tendsto p atTop (𝓝 pInf) → pInf.snd ∈ g.finiteMinimizingDirectionsTo S pInf.proj :=
    fun _ _ hp hlim => g.mem_finiteMinimizingDirectionsTo_of_tendsto hr hnorm hS hp hlim
  obtain ⟨V, hV, hVR, O₁, -, hKO₁, hO₁⟩ := exists_contMDiff_outward_field_minimizingDirections g hr
    hnorm hS hK.isClosed two_pos w (c := 0) (fun x hx => by rw [hwunit x hx]; norm_num)
    (fun x hx u hu => by rw [neg_zero]; exact hwout x hx u hu)
  obtain ⟨c', hc', hc'K⟩ := exists_margin_of_isCompact g (fun x => g.finiteMinimizingDirectionsTo S x)
    hDbdd hDclosed V hV.continuous hK (c := 0) (fun x hx u hu => hO₁ x (hKO₁ hx) u hu)
  refine ⟨V, hV, hVR, c' / 2, half_pos hc',
    interior {y | ∀ u ∈ g.finiteMinimizingDirectionsTo S y, g.inner y (V y) u < -(c' / 2)},
    isOpen_interior, fun x hx => ?_, fun x hx => interior_subset hx⟩
  rw [mem_interior_iff_mem_nhds]
  exact eventually_forall_inner_lt g (fun x => g.finiteMinimizingDirectionsTo S x) hDbdd hDclosed V
    isOpen_univ hV.continuous.continuousOn (mem_univ x) (fun u hu => by
      have := hc'K x hx u hu
      linarith)

/-- **The SAME outward field for LFR23 → LFR24 (D4).** From unit vectors with pairing `< −7/8`
against every minimizing direction to `S` on a closed `A ⊇ {a ≤ d_S ≤ b}`, `a > 0`: one smooth
field `V`, `|V| < 2`, pairing `< −3/4` on an open `O ⊇ A`; its complete flow `Φ`; the rate `3/4`
of `d_S` along orbit segments in `O ∖ S`; the continuous hitting time of every level of the band,
UNIQUE among crossing times whose orbit segment stays in `O ∖ S`; the projection
`y ↦ Φ_{τ(y, c)} y` to the level `c`; and `{d_S = c} × [a, b] ≃ₜ {a ≤ d_S ≤ b}` with both maps and
the coordinate identities. -/
theorem exists_endpoint_band_field [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S A : Set M} (hS : IsClosed S) (hSne : S.Nonempty) (hA : IsClosed A) {a b c : ℝ}
    (ha : 0 < a) (hc : c ∈ Icc a b) (hbandA : (fun x => infDist x S) ⁻¹' Icc a b ⊆ A)
    (w : (x : M) → TangentSpace I x) (hwunit : ∀ x ∈ A, g.inner x (w x) (w x) = 1)
    (hwout : ∀ x ∈ A, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (w x) u < -(7 / 8)) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      (∀ x, g.inner x (V x) (V x) < 2 ^ 2) ∧
      ∃ O : Set M, IsOpen O ∧ A ⊆ O ∧
        (∀ x ∈ O, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (V x) u < -(3 / 4)) ∧
      ∃ Φ : ℝ → M → M,
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) ∧ (∀ x, Φ 0 x = x) ∧
        (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
        (∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x)))) ∧
        (∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ O ∩ Sᶜ) →
          infDist x S + 3 / 4 * t ≤ infDist (Φ t x) S) ∧
        ContinuousOn (fun p : M × ℝ => hittingTime Φ (fun x => infDist x S) p.1 p.2)
          (((fun x => infDist x S) ⁻¹' Icc a b) ×ˢ Icc a b) ∧
        (∀ x, infDist x S ∈ Icc a b → ∀ s ∈ Icc a b,
          infDist (Φ (hittingTime Φ (fun x => infDist x S) x s) x) S = s ∧
          (∀ u ∈ uIcc 0 (hittingTime Φ (fun x => infDist x S) x s),
            infDist (Φ u x) S ∈ uIcc (infDist x S) s) ∧
          3 / 4 * |hittingTime Φ (fun x => infDist x S) x s| ≤ |s - infDist x S| ∧
          ∀ t, (∀ u ∈ uIcc 0 t, Φ u x ∈ O ∩ Sᶜ) → infDist (Φ t x) S = s →
            hittingTime Φ (fun x => infDist x S) x s = t) ∧
        ∃ e : ({x : M // infDist x S = c} × Icc a b) ≃ₜ {x : M // infDist x S ∈ Icc a b},
          (∀ p, (e p : M) = Φ (hittingTime Φ (fun x => infDist x S) p.1 p.2) p.1) ∧
          (∀ y, ((e.symm y).1 : M) = Φ (hittingTime Φ (fun x => infDist x S) y c) y) ∧
          (∀ y, ((e.symm y).2 : ℝ) = infDist (y : M) S) ∧
          (∀ p, infDist (e p : M) S = p.2) ∧
          ∀ x : {x : M // infDist x S = c}, (e (x, ⟨c, hc⟩) : M) = x := by
  obtain ⟨V, hV, hVR, O, hO, hAO, hOout⟩ :=
    exists_outward_field_seven_eighths g hr hnorm hS hA w hwunit hwout
  obtain ⟨Φ, hΦ, hΦ0, hΦadd, hder, -, -⟩ := exists_complete_flow_of_bounded_ENat g hnorm
    (n := ⊤) le_top V hV (B := 2) (fun x => (hVR x).le)
  have hUo : IsOpen (O ∩ Sᶜ) := hO.inter hS.isOpen_compl
  have hbandU : (fun x => infDist x S) ⁻¹' Icc a b ⊆ O ∩ Sᶜ := fun x hx =>
    ⟨hAO (hbandA hx), fun hxS => by
      have h0 : infDist x S = 0 := infDist_zero_of_mem hxS
      have : a ≤ infDist x S := hx.1
      linarith⟩
  have hκ : (0 : ℝ) < 3 / 4 := by norm_num
  have hrate := infDist_add_mul_le_flow g hr hnorm hS hSne hΦ.continuous hΦ0 V hder
    (U := O ∩ Sᶜ) (fun x hx => hx.2) (κ := 3 / 4) (fun x hx u hu => (hOout x hx.1 u hu).le)
  obtain ⟨hcont, hspec, e, he1, he2, he3, he4, he5⟩ := exists_hittingTime_band_product
    hΦ.continuous hΦ0 hΦadd (continuous_infDist_pt S) hUo hκ hc hbandU hrate
  refine ⟨V, hV, hVR, O, hO, hAO, hOout, Φ, hΦ, hΦ0, hΦadd, hder, hrate, hcont,
    fun x hx s hs => ⟨(hspec x hx s hs).1, (hspec x hx s hs).2.1, (hspec x hx s hs).2.2,
      fun t htU hts => hittingTime_eq_of_forall_mem hΦ.continuous hΦ0 hΦadd
        (continuous_infDist_pt S) hUo hκ hbandU hrate hx hs htU hts⟩,
    e, he1, he2, he3, he4, he5⟩

/-- **Consumer (LFR23 → LFR24).** The field of `exists_endpoint_band_field` satisfies LFR24's
`dh(V) > 1/2` on `O` for every vector `w` (a gradient) within `ε ≤ 1/8` of minus a minimizing
direction. -/
theorem exists_endpoint_band_field_dh [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S A : Set M} (hS : IsClosed S) (hSne : S.Nonempty) (hA : IsClosed A) {a b c : ℝ}
    (ha : 0 < a) (hc : c ∈ Icc a b) (hbandA : (fun x => infDist x S) ⁻¹' Icc a b ⊆ A)
    (w : (x : M) → TangentSpace I x) (hwunit : ∀ x ∈ A, g.inner x (w x) (w x) = 1)
    (hwout : ∀ x ∈ A, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (w x) u < -(7 / 8)) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      ∃ O : Set M, IsOpen O ∧ A ⊆ O ∧
        (∀ x ∈ O, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, ∀ (y : TangentSpace I x) (ε : ℝ), 0 ≤ ε →
          ε ≤ 1 / 8 → g.inner x (y + u) (y + u) < ε ^ 2 → 1 / 2 < g.inner x y (V x)) ∧
        ∃ e : ({x : M // infDist x S = c} × Icc a b) ≃ₜ {x : M // infDist x S ∈ Icc a b},
          ∀ y, ((e.symm y).2 : ℝ) = infDist (y : M) S := by
  obtain ⟨V, hV, hVR, O, hO, hAO, hOout, -, -, -, -, -, -, -, -, e, -, -, he3, -⟩ :=
    exists_endpoint_band_field g hr hnorm hS hSne hA ha hc hbandA w hwunit hwout
  exact ⟨V, hV, O, hO, hAO, fun x hx u hu y ε hε hε8 hyu =>
    one_half_lt_inner_of_outward_field g x hε hε8 (hVR x) (hOout x hx u hu) hyu, e, he3⟩

end Binding

end DifferentialGeometry.Geometry.FiniteSoul
