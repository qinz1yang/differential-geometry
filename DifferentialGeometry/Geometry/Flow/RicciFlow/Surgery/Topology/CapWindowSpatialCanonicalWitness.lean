import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowContinuationAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowStandardComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalPullScalarGradient
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessUniverseTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardWindowSpatialCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardWindowBallPlacement
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardActionComparison

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private local instance capWindowSpatialSigmaCompact (D : ℝ) :
    SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

namespace RetainedCoreHistory

theorem exists_capWindowPoint_spatialCanonicalWitness (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧
    ∀ (Ctime Cgrad : ℝ≥0) (Dw θcap : ℝ), 0 < Dw → θcap < 1 →
    ∃ (Rcap : ℝ) (mcap : ℕ), Dw + 1 < Rcap ∧
    ∀ qcan : ℝ, 0 < qcan →
    ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Rcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ H : RetainedCoreHistory.{u}, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
      p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative Ctime qcan k →
    ∀ t : ℝ, H.time k < t → t < s → Gk.DerivativeBoundBefore Ctime qcan t →
    ∀ y : (H.stage k).Carrier, H.CapWindowPoint records k y t Dw θcap →
      qcan < Gk.flow.scalar t y →
      (∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t y v| ≤
          Cgrad * Gk.flow.scalar t y * Real.sqrt (Gk.flow.scalar t y) *
            Real.sqrt ((Gk.flow.base.metric t).inner y v v)) →
      ∃ W : SpatialCanonicalWitness (Gk.flow.base.metric t) ε Cs (max Cs (Cgrad : ℝ)) y,
        W.capTubeHasNeckChart ε := by
  obtain ⟨a₀, ha₀, hHI⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  obtain ⟨Cw, hCw, hM4⟩ := exists_window_spatialCanonicalWitness_of_standard_close hε hε'
  refine ⟨Cw, hCw, ?_⟩
  intro Ctime Cgrad Dw θcap hDw hθcap
  set Θ := max θcap (1 / 2) with hΘdef
  have hΘ1 : Θ < 1 := max_lt hθcap (by norm_num)
  have hΘ0 : 0 < Θ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨eta, heta, hlower⟩ :=
    exists_uniform_standard_metric_scalar_lower_comparison Θ hΘ0.le hΘ1
  obtain ⟨Λ, hΛ, hplace⟩ := StandardSolution.exists_window_ball_placement hΘ1
  set L := 4 * Cw + 1 with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hΛL : 0 ≤ Λ * (L + 1) := by positivity
  obtain ⟨D, N, e, hrD, he, hwin⟩ := hM4 Θ (Dw + 1 + Λ * (L + 1)) hΘ1
  have hD : 0 < D := by linarith
  obtain ⟨Pb, Creset, Cb, -, -, hCb, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace.{u} Θ Ctime hΘ0 hΘ1
  obtain ⟨R, hR, m, -, ζ, δ₀, hζ, -, hδ₀, hbr⟩ := hbridge D e eta hD he heta N
  refine ⟨R, m, by linarith, ?_⟩
  intro qcan hqcan
  set ρmax := min (Real.sqrt (Cb / (4 * qcan))) (Real.sqrt (a₀ / 2)) with hρdef
  have hρmax : 0 < ρmax := lt_min (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_pos.mpr (by positivity))
  have hρ₁ : ρmax ^ 2 ≤ Cb / (4 * qcan) := by
    have h := pow_le_pow_left₀ hρmax.le (min_le_left _ _) 2
    rwa [Real.sq_sqrt (by positivity)] at h
  have hρ₂ : ρmax ^ 2 ≤ a₀ / 2 := by
    have h := pow_le_pow_left₀ hρmax.le (min_le_right _ _) 2
    rwa [Real.sq_sqrt (by positivity)] at h
  refine ⟨δ₀, ρmax, ζ, hδ₀, hρmax, hζ, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec k s Gk hGk hderiv t hkt
    hts hcur y hcap hRy hgrad
  obtain ⟨j, hl, A, b, x, hanchor, hxD, hage⟩ := hcap
  obtain ⟨hHI1, hHI2⟩ := hHI H.toHistory hId.some
  set q := ((records j).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j).static b).neck.scale_pos
  obtain ⟨hbirth, haq⟩ := hrec.birth_scale_bounds hΛδ j b hqcan hCb ha₀ hρb hρ₁ hρ₂
  have hbirth1 : qcan ≤ Cb * q := by linarith
  have hba : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hl
  have hθΘ : θcap ≤ Θ := le_max_left _ _
  have hxD' : ‖x.val‖ < D + 1 := by linarith
  obtain ⟨G, L', hG, -, hL, -, -, -, -, -, -, -, z, hzx, hy, Ξ, hΞs, -, hΞmark, hΞ, gflow, S,
      -, hS2, hS3, -, hS5, -, -, Q, -, hclose⟩ :=
    hbr H p₀ δbound ρbound records hrec hδb hrad hord hacc qcan a₀ θcap hqcan hθΘ hHI1 hHI2 k s
      Gk hGk hderiv t hkt hts hcur j hl y A b x hanchor hage hxD' hbirth1 haq
  have hyz : (Ξ z).val.val = y := congrArg Subtype.val hΞmark
  set T := q * (t - H.time j.succ) with hTdef
  have hT0 : 0 ≤ T := mul_nonneg hq.le (by linarith)
  have hTθ : T ≤ θcap := by
    have h1 := mul_le_mul_of_nonneg_left hage hq.le
    rwa [mul_comm θcap, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
  have hTΘ : T ∈ Icc 0 Θ := ⟨hT0, hTθ.trans hθΘ⟩
  have hTmem : T ∈ Icc 0 T := ⟨hT0, le_rfl⟩
  have htT : H.time j.succ + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hST := H.capWindow_flow_metric_eq Gk hl hΞ hq hG hL hS2 hS5 T hTmem
    (by rw [htT]; linarith)
  rw [htT] at hST
  have hΦ := H.toHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val j.succ k hl G hΞ
  have hinj := H.toHistory.injective_backwardSurvivorIncomingDomain_val_val j.succ k hl G
    hΞs.isEmbedding.injective
  subst hyz
  set C2 := max Cw (Cgrad : ℝ) with hC2def
  have hgradY : ∀ w : TangentSpace I3 (Ξ z).val.val,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (Gk.flow.base.metric t))
        (Ξ z).val.val w)| ≤
        C2 * metricScalarAt (Gk.flow.base.metric t) (Ξ z).val.val *
          Real.sqrt (metricScalarAt (Gk.flow.base.metric t) (Ξ z).val.val) *
          Real.sqrt ((Gk.flow.base.metric t).inner (Ξ z).val.val w w) := by
    intro w
    refine (hgrad w).trans ?_
    have hRpos : 0 ≤ Gk.flow.scalar t (Ξ z).val.val := (hqcan.trans hRy).le
    gcongr
    all_goals first | exact le_max_right _ _ | exact le_rfl
  have hgS := abs_mfderiv_metricScalarAt_localPullMetric_scaleMetric_le
    (Gk.flow.base.metric t) (fun w => (Ξ w).val.val) hΦ hq z hgradY
  have hinner : ∀ (v : standardCapWindow D) (w : TangentSpace I3 v),
      (1 / 2) * ((Q.val.metric T).restrictOpen (standardCapWindow D)).inner v w w ≤
        (S.base.metric T).inner v w w := fun v w =>
    (hlower Q (standardCapWindow D) (S.base.metric T) T hTΘ v
      (fun i hi => ((hclose T hTmem).2 i hi v).le)).1 w
  have hlow := (hlower Q (standardCapWindow D) (S.base.metric T) T hTΘ z
    (fun i hi => ((hclose T hTmem).2 i hi z).le)).2
  rw [metricScalarAt_restrictOpen] at hlow
  have hQ1 : 1 ≤ metricScalarAt (Q.val.metric T) z.val :=
    Q.val.one_le_scalar T (Q.mem_domain_of_mem_Icc hΘ1 hTΘ) z.val
  have hzr : ‖(z : EuclideanSpace ℝ (Fin 3))‖ + Λ * (L + 1) < D + 1 := by
    rw [hzx]
    linarith only [hxD, hrD]
  obtain ⟨hcpt, -⟩ := hplace D L z hL0 hzr Q T hTΘ (S.base.metric T) hinner
  have key : ∃ W : SpatialCanonicalWitness (localPullMetric (scaleMetric q hq
      (Gk.flow.base.metric t)) (fun w => (Ξ w).val.val) hΦ) ε Cw C2 z,
      W.capTubeHasNeckChart ε ∧ 2 * W.radius < L := by
    rw [← hST]
    have hgS' : ∀ v : TangentSpace I3 z,
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (S.base.metric T)) z v)| ≤
          C2 * S.scalar T z * Real.sqrt (S.scalar T z) *
            Real.sqrt ((S.base.metric T).inner z v v) := by
      change ∀ v : TangentSpace I3 z,
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (S.base.metric T)) z v)| ≤
          C2 * metricScalarAt (S.base.metric T) z *
            Real.sqrt (metricScalarAt (S.base.metric T) z) *
            Real.sqrt ((S.base.metric T).inner z v v)
      rw [hST]
      exact hgS
    obtain ⟨W, hW⟩ := hwin Q T hT0 (hTθ.trans hθΘ) S hS3
      (fun τ hτ i hi v => (hclose τ hτ).1 i hi v) z (by rw [hzx]; linarith only [hxD, hΛL]) C2
      (le_max_left _ _) hgS'
    refine ⟨W, hW, ?_⟩
    have hRS : 1 / 2 ≤ metricScalarAt (S.base.metric T) z := by linarith only [hlow, hQ1]
    have hs : 1 / 2 ≤ Real.sqrt (metricScalarAt (S.base.metric T) z) := by
      have h := Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ^ 2 ≤ metricScalarAt (S.base.metric T) z by
        linarith only [hRS])
      rwa [Real.sqrt_sq (by norm_num)] at h
    have hr0 : 0 ≤ W.radius :=
      (inv_nonneg.mpr (Real.sqrt_nonneg _)).trans W.radius_lower
    have hup := W.radius_upper
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by linarith only [hRS]))] at hup
    linarith only [mul_le_mul_of_nonneg_left hs hr0, hup, hLdef]
  obtain ⟨W, hW, hWr⟩ := key
  rw [hST] at hcpt
  have hscale : scaleMetric q⁻¹ (inv_pos.mpr hq) (scaleMetric q hq (Gk.flow.base.metric t)) =
      Gk.flow.base.metric t :=
    SmoothRiemannianMetric.ext_inner fun v w₁ w₂ => by
      simp only [scaleMetric_inner]
      field_simp
  rw [← hscale]
  exact ⟨((W.pushforwardOfInjectiveULift hΦ hinj hWr hcpt).scaleMetric q⁻¹ (inv_pos.mpr hq)),
    SpatialCanonicalWitness.capTubeHasNeckChart.scaleMetric q⁻¹ (inv_pos.mpr hq)
      (hW.pushforwardOfInjectiveULift hΦ hinj hWr hcpt)⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
