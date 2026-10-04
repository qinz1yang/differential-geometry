import DifferentialGeometry.Geometry.Comparison.FiniteSoul.BoundedFlow
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.HittingTime
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.OutwardPatch
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FirstVariation

/-!
# Distance bands as products along an outward flow (S-HIT binding for LFR23, S6, LFR46)

Package CM-S (finite soul), lane CMS-H. The flow mechanism of LFR23 (master207A:26787–26806) and of
LFR46 (A:28944–28958) on a complete finite-order manifold, for the distance `d_S` to a closed set:

* `infDist_add_mul_le_flow`: along the flow of a field pairing `≤ -κ` with every minimizing
  direction to `S` on an open set `U` disjoint from `S`, `d_S` grows at rate `κ` on every orbit
  segment inside `U` (CM-D first variation, `le_infDist_sub_of_forall_finite`).
* `exists_flow_infDist_band_product` (LFR23 form): S-FLOW's complete flow and the band product
  `{d_S = c} × [a, b] ≃ₜ {a ≤ d_S ≤ b}` of S-HIT for the SAME flow.
* `exists_flow_infDist_halfBand_product` (S6 / LFR46 form): a compact `S`, a strict pairing `< 0` on
  an open set containing `{d_S ≥ a}`, compact margins (S-PATCH), and
  `{d_S = c} × [a, ∞) ≃ₜ {d_S ≥ a}`.
* Consumers: pointwise outward vectors ⇒ S-PATCH ⇒ S-FLOW ⇒ the products
  (`exists_outward_flow_infDist_band_product`, `exists_outward_flow_infDist_halfBand_product`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **Rate of the distance along an outward flow.** -/
theorem infDist_add_mul_le_flow [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) {Φ : ℝ → M → M}
    (hΦc : Continuous (fun p : ℝ × M => Φ p.1 p.2)) (hΦ0 : ∀ x, Φ 0 x = x)
    (V : (x : M) → TangentSpace I x)
    (hder : ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x))))
    {U : Set M} (hUS : ∀ x ∈ U, x ∉ S) {κ : ℝ}
    (hout : ∀ x ∈ U, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (V x) u ≤ -κ) :
    ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → infDist x S + κ * t ≤ infDist (Φ t x) S := by
  intro x t ht hU
  have h := g.le_infDist_sub_of_forall_finite hr hnorm hS hSne (γ := fun s => Φ s x)
    (X := fun s => V (Φ s x)) (a := 0) (b := t) ht
    (hΦc.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun s _ => hder s x) (fun s hs => hUS _ (hU s ⟨hs.1, hs.2.le⟩))
    (fun s hs u hu => by
      have h1 := hout _ (hU s ⟨hs.1, hs.2.le⟩) u hu
      rw [g.symm]
      linarith)
  rw [hΦ0, sub_zero] at h
  linarith

/-- **S-HIT binding, LFR23 form.** A bounded `C^n` field pairing `≤ -κ` with every minimizing
direction to `S` on an open set containing the band `{a ≤ d_S ≤ b}`, `a > 0`: its complete flow
(S-FLOW), the continuous hitting time of every level of the band, and the band product
`{d_S = c} × [a, b] ≃ₜ {a ≤ d_S ≤ b}` along the SAME flow. -/
theorem exists_flow_infDist_band_product [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) {n : ℕ∞} (hn : 1 ≤ n)
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent n (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    {B : ℝ} (hB : ∀ x, g.inner x (V x) (V x) ≤ B ^ 2) {U : Set M} (hU : IsOpen U)
    {a b c κ : ℝ} (ha : 0 < a) (hκ : 0 < κ) (hc : c ∈ Icc a b)
    (hbandU : (fun x => infDist x S) ⁻¹' Icc a b ⊆ U)
    (hout : ∀ x ∈ U, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (V x) u ≤ -κ) :
    ∃ Φ : ℝ → M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I n (fun q : ℝ × M => Φ q.1 q.2) ∧ (∀ x, Φ 0 x = x) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      (∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x)))) ∧
      ContinuousOn (fun p : M × ℝ => hittingTime Φ (fun x => infDist x S) p.1 p.2)
        (((fun x => infDist x S) ⁻¹' Icc a b) ×ˢ Icc a b) ∧
      (∀ x, infDist x S ∈ Icc a b → ∀ s ∈ Icc a b,
        infDist (Φ (hittingTime Φ (fun x => infDist x S) x s) x) S = s ∧
          (∀ u ∈ uIcc 0 (hittingTime Φ (fun x => infDist x S) x s),
            infDist (Φ u x) S ∈ uIcc (infDist x S) s) ∧
          κ * |hittingTime Φ (fun x => infDist x S) x s| ≤ |s - infDist x S|) ∧
      ∃ e : ({x : M // infDist x S = c} × Icc a b) ≃ₜ {x : M // infDist x S ∈ Icc a b},
        (∀ p, (e p : M) = Φ (hittingTime Φ (fun x => infDist x S) p.1 p.2) p.1) ∧
        (∀ y, ((e.symm y).1 : M) = Φ (hittingTime Φ (fun x => infDist x S) y c) y) ∧
        (∀ y, ((e.symm y).2 : ℝ) = infDist (y : M) S) ∧
        (∀ p, infDist (e p : M) S = p.2) ∧
        ∀ x : {x : M // infDist x S = c}, (e (x, ⟨c, hc⟩) : M) = x := by
  obtain ⟨Φ, hΦ, hΦ0, hΦadd, hder, -, -⟩ := exists_complete_flow_of_bounded_ENat g hnorm hn V hV hB
  have hUS : ∀ x ∈ U ∩ Sᶜ, x ∉ S := fun x hx => hx.2
  have hband' : (fun x => infDist x S) ⁻¹' Icc a b ⊆ U ∩ Sᶜ := fun x hx =>
    ⟨hbandU hx, fun hxS => by
      have h0 : infDist x S = 0 := infDist_zero_of_mem hxS
      have : a ≤ infDist x S := hx.1
      linarith⟩
  have hrate := infDist_add_mul_le_flow g hr hnorm hS hSne hΦ.continuous hΦ0 V hder hUS
    (fun x hx u hu => hout x hx.1 u hu)
  obtain ⟨hcont, hspec, e, he1, he2, he3, he4, he5⟩ := exists_hittingTime_band_product
    hΦ.continuous hΦ0 hΦadd (continuous_infDist_pt S) (hU.inter hS.isOpen_compl) hκ hc hband' hrate
  exact ⟨Φ, hΦ, hΦ0, hΦadd, hder, hcont, hspec, e, he1, he2, he3, he4, he5⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] in
/-- The closed distance band to a compact set is compact (proper `M`). -/
theorem isCompact_infDist_band [ProperSpace M] {S : Set M} (hS : IsCompact S)
    (hSne : S.Nonempty) (a b : ℝ) : IsCompact ((fun x => infDist x S) ⁻¹' Icc a b) := by
  obtain ⟨s₀, hs₀⟩ := hSne
  obtain ⟨D, hD⟩ := (isBounded_iff_subset_closedBall s₀).mp hS.isBounded
  refine (isCompact_closedBall s₀ (b + D)).of_isClosed_subset
    (isClosed_Icc.preimage (continuous_infDist_pt S)) fun x hx => ?_
  obtain ⟨y, hy, hxy⟩ := hS.exists_infDist_eq_dist ⟨s₀, hs₀⟩ x
  have h1 : dist x y ≤ b := hxy ▸ hx.2
  have h2 : dist y s₀ ≤ D := hD hy
  rw [mem_closedBall]
  linarith [dist_triangle x y s₀]

/-- **S-HIT binding, S6 / LFR46 form.** A compact `S`, a bounded `C^n` field strictly outward
(pairing `< 0`) against every minimizing direction to `S` at every point with `d_S ≥ a`, `a > 0`
(compact margins and their open neighbourhoods come from S-PATCH): its complete flow, the
continuous hitting time, and the exterior product `{d_S = c} × [a, ∞) ≃ₜ {d_S ≥ a}` along that
flow. -/
theorem exists_flow_infDist_halfBand_product [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty) {n : ℕ∞} (hn : 1 ≤ n)
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent n (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    {B : ℝ} (hB : ∀ x, g.inner x (V x) (V x) ≤ B ^ 2) {a c : ℝ} (ha : 0 < a) (hc : c ∈ Ici a)
    (hout : ∀ x, a ≤ infDist x S →
      ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (V x) u < 0) :
    ∃ Φ : ℝ → M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I n (fun q : ℝ × M => Φ q.1 q.2) ∧ (∀ x, Φ 0 x = x) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      (∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x)))) ∧
      ContinuousOn (fun p : M × ℝ => hittingTime Φ (fun x => infDist x S) p.1 p.2)
        (((fun x => infDist x S) ⁻¹' Ici a) ×ˢ Ici a) ∧
      (∀ x, infDist x S ∈ Ici a → ∀ s ∈ Ici a,
        infDist (Φ (hittingTime Φ (fun x => infDist x S) x s) x) S = s ∧
          ∀ u ∈ uIcc 0 (hittingTime Φ (fun x => infDist x S) x s),
            infDist (Φ u x) S ∈ uIcc (infDist x S) s) ∧
      ∃ e : ({x : M // infDist x S = c} × Ici a) ≃ₜ {x : M // infDist x S ∈ Ici a},
        (∀ p, (e p : M) = Φ (hittingTime Φ (fun x => infDist x S) p.1 p.2) p.1) ∧
        (∀ y, ((e.symm y).1 : M) = Φ (hittingTime Φ (fun x => infDist x S) y c) y) ∧
        (∀ y, ((e.symm y).2 : ℝ) = infDist (y : M) S) ∧
        (∀ p, infDist (e p : M) S = p.2) ∧
        ∀ x : {x : M // infDist x S = c}, (e (x, ⟨c, hc⟩) : M) = x := by
  obtain ⟨Φ, hΦ, hΦ0, hΦadd, hder, -, -⟩ := exists_complete_flow_of_bounded_ENat g hnorm hn V hV hB
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have hVc : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M)) := hV.continuous
  have hDbdd : ∀ x, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x u u ≤ 1 :=
    fun _ _ hu => hu.1.le
  have hDclosed : ∀ (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M),
      (∀ k, (p k).snd ∈ g.finiteMinimizingDirectionsTo S (p k).proj) →
        Tendsto p atTop (𝓝 pInf) → pInf.snd ∈ g.finiteMinimizingDirectionsTo S pInf.proj :=
    fun _ _ hp hlim => g.mem_finiteMinimizingDirectionsTo_of_tendsto hr hnorm hS.isClosed hp hlim
  have hrate : ∀ b, ∃ U : Set M, IsOpen U ∧ (fun x => infDist x S) ⁻¹' Icc a b ⊆ U ∧
      ∃ κ > 0, ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) →
        infDist x S + κ * t ≤ infDist (Φ t x) S := by
    intro b
    have hK := isCompact_infDist_band hS hSne a b
    obtain ⟨κ, hκ, hκK⟩ := exists_margin_of_isCompact g (fun x => g.finiteMinimizingDirectionsTo S x)
      hDbdd hDclosed V hVc hK (c := 0) (fun x hx u hu => by
        rw [neg_zero]; exact hout x hx.1 u hu)
    set U : Set M := interior {y | ∀ u ∈ g.finiteMinimizingDirectionsTo S y,
      g.inner y (V y) u < -(κ / 2)} ∩ Sᶜ with hUdef
    refine ⟨U, isOpen_interior.inter hS.isClosed.isOpen_compl, fun x hx => ⟨?_, ?_⟩, κ / 2,
      half_pos hκ, infDist_add_mul_le_flow g hr hnorm hS.isClosed hSne hΦ.continuous hΦ0 V hder
        (fun x hx => hx.2) (fun x hx u hu => (interior_subset hx.1 u hu).le)⟩
    · rw [mem_interior_iff_mem_nhds]
      exact eventually_forall_inner_lt g (fun x => g.finiteMinimizingDirectionsTo S x) hDbdd
        hDclosed V isOpen_univ hVc.continuousOn (mem_univ x) (fun u hu => by
          have := hκK x hx u hu
          linarith)
    · intro hxS
      have h0 : infDist x S = 0 := infDist_zero_of_mem hxS
      have : a ≤ infDist x S := hx.1
      linarith
  obtain ⟨hcont, hspec, e, he1, he2, he3, he4, he5⟩ := exists_hittingTime_halfBand_product
    hΦ.continuous hΦ0 hΦadd (continuous_infDist_pt S) hc hrate
  exact ⟨Φ, hΦ, hΦ0, hΦadd, hder, hcont, hspec, e, he1, he2, he3, he4, he5⟩

/-- **Consumer (LFR23 mechanism).** Pointwise vectors on a closed set `A ⊇ {a ≤ d_S ≤ b}`,
`a > 0`, of `g`-length `< 2` and pairing `< -κ` with every minimizing direction: ONE smooth field
of norm `< 2` (S-PATCH), its complete flow (S-FLOW), and the band product along it (S-HIT). -/
theorem exists_outward_flow_infDist_band_product [SigmaCompactSpace M] [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) {A : Set M} (hA : IsClosed A)
    {a b c κ : ℝ} (ha : 0 < a) (hκ : 0 < κ) (hc : c ∈ Icc a b)
    (hbandA : (fun x => infDist x S) ⁻¹' Icc a b ⊆ A) (v : (x : M) → TangentSpace I x)
    (hvR : ∀ x ∈ A, g.inner x (v x) (v x) < 2 ^ 2)
    (hvout : ∀ x ∈ A, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (v x) u < -κ) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      (∀ x, g.inner x (V x) (V x) < 2 ^ 2) ∧
      ∃ Φ : ℝ → M → M, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) ∧
        (∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x)))) ∧
        ∃ e : ({x : M // infDist x S = c} × Icc a b) ≃ₜ {x : M // infDist x S ∈ Icc a b},
          ∀ p, (e p : M) = Φ (hittingTime Φ (fun x => infDist x S) p.1 p.2) p.1 := by
  obtain ⟨V, hV, hVR, O, hO, hAO, hOout⟩ :=
    exists_contMDiff_outward_field_minimizingDirections g hr hnorm hS hA two_pos v hvR hvout
  obtain ⟨Φ, hΦ, -, -, hder, -, -, e, he1, -⟩ := exists_flow_infDist_band_product g hr hnorm hS hSne
    (n := ⊤) le_top V hV (B := 2) (fun x => (hVR x).le) hO ha hκ hc (hbandA.trans hAO)
    (fun x hx u hu => (hOout x hx u hu).le)
  exact ⟨V, hV, hVR, Φ, hΦ, hder, e, he1⟩

/-- **Consumer (S6 / LFR46 mechanism).** LFR45.1-type data — at every point with `d_S ≥ a` a unit
vector strictly outward against ALL minimizing directions to the compact `S` — gives ONE smooth
field of norm `< 2`, its complete flow, and the exterior product
`{d_S = c} × [a, ∞) ≃ₜ {d_S ≥ a}` along it. -/
theorem exists_outward_flow_infDist_halfBand_product [SigmaCompactSpace M] [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty) {a c : ℝ} (ha : 0 < a) (hc : c ∈ Ici a)
    (v : (x : M) → TangentSpace I x)
    (hvunit : ∀ x, a ≤ infDist x S → g.inner x (v x) (v x) = 1)
    (hvout : ∀ x, a ≤ infDist x S →
      ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (v x) u < 0) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      (∀ x, g.inner x (V x) (V x) < 2 ^ 2) ∧
      ∃ Φ : ℝ → M → M, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) ∧
        (∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x)))) ∧
        ∃ e : ({x : M // infDist x S = c} × Ici a) ≃ₜ {x : M // infDist x S ∈ Ici a},
          ∀ p, (e p : M) = Φ (hittingTime Φ (fun x => infDist x S) p.1 p.2) p.1 := by
  have hA : IsClosed {x : M | a ≤ infDist x S} := isClosed_le continuous_const (continuous_infDist_pt S)
  obtain ⟨V, hV, hVR, O, -, hAO, hOout⟩ :=
    exists_contMDiff_outward_field_minimizingDirections g hr hnorm hS.isClosed hA two_pos v
      (c := 0) (fun x hx => by rw [hvunit x hx]; norm_num)
      (fun x hx u hu => by rw [neg_zero]; exact hvout x hx u hu)
  obtain ⟨Φ, hΦ, -, -, hder, -, -, e, he1, -⟩ := exists_flow_infDist_halfBand_product g hr hnorm hS
    hSne (n := ⊤) le_top V hV (B := 2) (fun x => (hVR x).le) ha hc
    (fun x hx u hu => by have := hOout x (hAO hx) u hu; rwa [neg_zero] at this)
  exact ⟨V, hV, hVR, Φ, hΦ, hder, e, he1⟩

end DifferentialGeometry.Geometry.FiniteSoul
