import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBarrierTransferB_O27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CuspThickDistanceMain_S26
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoresAssembly_O21

set_option autoImplicit false

/-! CH12-O27 G1 — **HPI04 thin cusp band** (`[FROZEN] CH12-O27` R1 v2 = `[FROZEN] CH12-O21 R1` + `hsmooth`).
For one model datum with the S4 fields, cusp points of height in `[s0, s0 + L]` are eventually
mapped to `w`-thin points of the normalized flow.  Proof: count-free S35/S40/S41 transfer
(`hTrans_of_curv_O27`: curvature radius in `[c₀, √8]`, `vol ≤ 2 vol_H(y, 4)`) + S26 cusp window volume. -/

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

/-- **HPI04 (R1 v2).**  Thin cusp band: for every `w > 0` there is a height `s0` such that for every
band length `L ≥ 0`, eventually every cusp point of height in `[s0, s0 + L]` is mapped to a point
whose normalized ball at its curvature radius `r` has volume `< w r³`. -/
theorem hpi04_thin_barrier_O27 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    ∀ w : ℝ, 0 < w → ∃ s0 : ℝ, ∀ L : ℝ, 0 ≤ L → ∃ T : ℝ, ∀ t (ht : start ≤ t), T ≤ t →
      ∀ (q : Fin Tr.count) (p : CuspHalfSpace), s0 ≤ p.2.val 0 → p.2.val 0 ≤ s0 + L →
        ∀ r : ℝ, 0 < r →
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hstart.trans_le ht))
            (postMetric F.observation t)) (map t ht (Tr.cuspMap q p)) = ENNReal.ofReal r →
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (hstart.trans_le ht))
            (postMetric F.observation t)) (map t ht (Tr.cuspMap q p)) r <
            ENNReal.ofReal (w * r ^ 3) := by
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
  choose A hA0 hA using fun q : Fin Tr.count => cusp_window_volume_le_S26 Tr q
  choose D hD0 hDd using fun q : Fin Tr.count => exists_edist_cusp_le_S26 Tr H.basepoint q
  set As : ℝ := 1 + ∑ q, A q with hAs
  set Ds : ℝ := ∑ q, D q with hDs
  have hAs0 : 0 ≤ ∑ q, A q := Finset.sum_nonneg fun q _ => hA0 q
  have hDs0 : 0 ≤ Ds := Finset.sum_nonneg fun q _ => hD0 q
  have hAsp : 0 < As := by linarith
  intro w hw
  have hε : 0 < w * c₀ ^ 3 / (16 * As) := by positivity
  obtain ⟨N, hN⟩ := (Real.tendsto_exp_neg_atTop_nhds_zero.eventually
    (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨max 5 (N + 4), fun L hL => ?_⟩
  set s0 := max 5 (N + 4) with hs0def
  have hs05 : (5 : ℝ) ≤ s0 := le_max_left _ _
  have hs0N : N + 4 ≤ s0 := le_max_right _ _
  set R : ℝ := Ds + s0 + L with hR
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨T₂, hT₂⟩ := hdecay (1 / (R + 1)) (by positivity)
  refine ⟨max T₁ T₂, fun t ht hTt q p hsl hsu r hr hcr => ?_⟩
  have hαt := hpos t ht
  have hRlt : R < (α t)⁻¹ := by
    have h1 : α t < 1 / (R + 1) := hT₂ t ((le_max_right _ _).trans hTt)
    have h2 : R + 1 < (α t)⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) hαt]
      simpa [one_div] using h1
    linarith
  have hDq : D q ≤ Ds :=
    Finset.single_le_sum (f := D) (fun j _ => hD0 j) (Finset.mem_univ q)
  have hAq : A q ≤ ∑ j, A j :=
    Finset.single_le_sum (f := A) (fun j _ => hA0 j) (Finset.mem_univ q)
  have hy : Tr.cuspMap q p ∈ riemannianBallOf H.metric H.basepoint (α t)⁻¹ := by
    change riemannianEDistOf H.metric H.basepoint (Tr.cuspMap q p) < ENNReal.ofReal (α t)⁻¹
    refine (hDd q p).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
    linarith
  obtain ⟨hlow, hup, hvol⟩ := hT t ht ((le_max_left _ _).trans hTt) _ hy
  obtain ⟨hr1, hr8⟩ := curvatureRadius_bounds_S35 _ _ hc₀ hlow hup hr hcr
  have hv := hvol r hr hr8
  have hs4 : (4 : ℝ) < p.2.val 0 := by linarith
  have hmodel : ballVolume H.metric (Tr.cuspMap q p) 4 ≤
      ENNReal.ofReal (A q * Real.exp (-(p.2.val 0 - 4)) * (p.2.val 0 + 4 - (p.2.val 0 - 4))) := by
    unfold ballVolume
    refine (MeasureTheory.measure_mono ((ball_subset_window_S26 Tr q p (by norm_num) hs4).trans ?_)).trans
      (hA q _ _ (by linarith) (by linarith))
    refine image_mono fun z hz => ?_
    have hz' := abs_lt.mp (show |z.2.val 0 - p.2.val 0| < 4 from hz)
    exact ⟨by linarith [hz'.1], by linarith [hz'.2]⟩
  have hexp : Real.exp (-(p.2.val 0 - 4)) < w * c₀ ^ 3 / (16 * As) := hN _ (by linarith)
  have hexp0 : 0 < Real.exp (-(p.2.val 0 - 4)) := Real.exp_pos _
  have hnum : 2 * (A q * Real.exp (-(p.2.val 0 - 4)) * (p.2.val 0 + 4 - (p.2.val 0 - 4))) <
      w * r ^ 3 := by
    have hc3 : c₀ ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hc₀.le hr1 3
    have h16 : 16 * As * Real.exp (-(p.2.val 0 - 4)) < w * c₀ ^ 3 := by
      rw [lt_div_iff₀ (by positivity)] at hexp; linarith
    have hAqs : A q * Real.exp (-(p.2.val 0 - 4)) ≤ As * Real.exp (-(p.2.val 0 - 4)) :=
      mul_le_mul_of_nonneg_right (by linarith) hexp0.le
    nlinarith
  calc ballVolume _ (map t ht (Tr.cuspMap q p)) r
      ≤ ENNReal.ofReal 2 * ballVolume H.metric (Tr.cuspMap q p) 4 := hv
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal
          (A q * Real.exp (-(p.2.val 0 - 4)) * (p.2.val 0 + 4 - (p.2.val 0 - 4))) := by
        gcongr
    _ = ENNReal.ofReal
          (2 * (A q * Real.exp (-(p.2.val 0 - 4)) * (p.2.val 0 + 4 - (p.2.val 0 - 4)))) :=
        (ENNReal.ofReal_mul (by norm_num)).symm
    _ < ENNReal.ofReal (w * r ^ 3) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hnum

end GC.LongTime.Ch12
