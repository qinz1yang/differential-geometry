import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBarrier_O27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterThinStatic_S35

set_option autoImplicit false

/-! CH12-O27 G3a — **HPI07 thick-radius transfer** (R4 radius clause).  For one model datum with the S4
fields there are `w0 > 0` and `T` such that for `t ≥ T` and `0 < w' ≤ w0`, a point `y` of the advertised
ball whose image is `w'`-thick in the normalized flow lies in the model ball of radius `w'⁻¹`.
Proof: `hTrans_of_curv_O27` (radius in `[c₀, √8]`, `vol ≤ 2 vol_H(y, 4)`) + `hpi07_log_bound_gen_S35`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

/-- **HPI07 transfer (G3a).**  Uniform in `w'`: one `T` serves every `w' ∈ (0, w0]`. -/
theorem hpi07_thick_transfer_O27 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (H : FiniteVolumeHyperbolicModel.{u}) (Tr : HyperbolicTruncation H) (start : ℝ)
    (hstart : 0 < start) (α : ℝ → ℝ) (Ω : TopologicalSpace.Opens (ℝ × H.Carrier))
    (map : (t : ℝ) → start ≤ t → H.Carrier → (postStage F.observation t).Carrier)
    (hpos : ∀ t, start ≤ t → 0 < α t) (hdecay : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε)
    (hemb : ∀ t (ht : start ≤ t),
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => map t ht x))
    (hsmooth : ∀ t (ht : start ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map t ht) (sourceSlice_CX5 Ω t))
    (hball : ∀ t, start ≤ t →
      riemannianBallOf H.metric H.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t)
    (hck : ∀ t (ht : start ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (α t)⁻¹),
        ckErr_O21 H (postMetric F.observation t) t⁻¹ (map t ht) k p < α t) :
    ∃ w0 : ℝ, 0 < w0 ∧ ∃ T : ℝ, ∀ t (ht : start ≤ t), T ≤ t → ∀ w' : ℝ, 0 < w' → w' ≤ w0 →
      ∀ y ∈ riemannianBallOf H.metric H.basepoint (α t)⁻¹, ∀ r : ℝ, 0 < r →
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hstart.trans_le ht))
          (postMetric F.observation t)) (map t ht y) = ENNReal.ofReal r →
        ENNReal.ofReal (w' * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (hstart.trans_le ht))
          (postMetric F.observation t)) (map t ht y) r →
        y ∈ riemannianBallOf H.metric H.basepoint w'⁻¹ := by
  have hD : ((∀ t (ht : start ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map t ht) (sourceSlice_CX5 Ω t)) ∧
      (∀ t (ht : start ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => map t ht x)) ∧
      (∀ t, start ≤ t → riemannianBallOf H.metric H.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t) ∧
      (∀ t (ht : start ≤ t),
        let h := H.metric; let error := fun p : H.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (map t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h H.basepoint (2 * (α t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < α t) ∧
      (∀ t, start ≤ t → 0 < α t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε)) :=
    ⟨hsmooth, hemb, hball, fun t ht => by intro h error k hk p hp; exact hck t ht k hk p hp,
      hpos, hdecay⟩
  obtain ⟨c₀, hc₀, T₁, hT⟩ := hTrans_of_curv_O27 hstart hD (hUp_O27 hstart hD)
    (hLow_O27 hstart hD (hC0_O27 hstart hD))
  obtain ⟨C₀, C₁, hC₀, hC₁, hlog⟩ := hpi07_log_bound_gen_S35 Tr H.basepoint (ρ := 4) (by norm_num)
  set Kc : ℝ := 2 * C₁ + 2 with hKc
  have hKc0 : 0 < Kc := by positivity
  set C' : ℝ := C₀ + C₁ * |Real.log (2 / c₀ ^ 3)| + C₁ * |Real.log Kc| with hC'
  have hC'0 : 0 ≤ C' := by positivity
  refine ⟨min (2 / c₀ ^ 3) (1 / (2 * C' + 1)), lt_min (by positivity) (by positivity), T₁,
    fun t ht hTt w' hw' hw'le y hy r hr hcr hth => ?_⟩
  obtain ⟨hlow, hup, hvol⟩ := hT t ht hTt y hy
  obtain ⟨hr1, hr8⟩ := curvatureRadius_bounds_S35 _ _ hc₀ hlow hup hr hcr
  have hc3 : c₀ ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hc₀.le hr1 3
  -- model volume lower bound at radius 4
  have h2 : ENNReal.ofReal (w' * c₀ ^ 3) ≤ ENNReal.ofReal 2 * ballVolume H.metric y 4 :=
    ((ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hc3 hw'.le)).trans hth).trans
      (hvol r hr hr8)
  set wm : ℝ := w' * c₀ ^ 3 / 2 with hwm
  have hwm0 : 0 < wm := by positivity
  have hwm1 : wm ≤ 1 := by
    have h1 : w' ≤ 2 / c₀ ^ 3 := hw'le.trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    rw [hwm]; linarith
  have hBV : ENNReal.ofReal wm ≤ ballVolume H.metric y 4 := by
    rw [hwm, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact ENNReal.div_le_of_le_mul' h2
  have hd := hlog wm hwm0 hwm1 y hBV
  -- arithmetic: C₀ + C₁ log (1 / wm) < w'⁻¹
  set u : ℝ := w'⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have hu2 : 2 * C' + 1 ≤ u := by
    have h1 : w' ≤ 1 / (2 * C' + 1) := hw'le.trans (min_le_right _ _)
    rw [hu, ← one_div, le_div_iff₀ hw']
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hsplit : 1 / wm = (2 / c₀ ^ 3) * (u / Kc) * Kc := by
    rw [hwm, hu]; field_simp
  have hlogsplit : Real.log (1 / wm) =
      Real.log (2 / c₀ ^ 3) + Real.log (u / Kc) + Real.log Kc := by
    rw [hsplit, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have hlu : Real.log (u / Kc) ≤ u / Kc - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hCu : C₁ * (u / Kc) ≤ u / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ hKc0 (by norm_num)]
    nlinarith
  have hfin : C₀ + C₁ * Real.log (1 / wm) < u := by
    rw [hlogsplit]
    have e1 : C₁ * Real.log (2 / c₀ ^ 3) ≤ C₁ * |Real.log (2 / c₀ ^ 3)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hC₁
    have e2 : C₁ * Real.log Kc ≤ C₁ * |Real.log Kc| := mul_le_mul_of_nonneg_left (le_abs_self _) hC₁
    have e3 : C₁ * Real.log (u / Kc) ≤ C₁ * (u / Kc) := by
      nlinarith [mul_le_mul_of_nonneg_left hlu hC₁]
    nlinarith
  change riemannianEDistOf H.metric H.basepoint y < ENNReal.ofReal u
  exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hu0).2 hfin)

end GC.LongTime.Ch12
