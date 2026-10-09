import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowContinuationAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosenessEndpointWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DerivativeBoundExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabStartDerivativeBounds

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance capWindowLeafSigmaCompact (D : ℝ) :
    SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

namespace RetainedCoreHistory

theorem exists_capWindowPoint_bounds (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (C₀ τ₀ : ℝ) (Ctime₀ : ℝ≥0), 1 ≤ C₀ ∧ 0 < τ₀ ∧
    ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), C₀ ≤ C1 → C₀ ≤ C2 → τ₀ ≤ τmin →
      Ctime₀ ≤ Ctime → Ctime₀ ≤ Cgrad →
    ∀ (Dcap θcap : ℝ), 0 < Dcap → θcap < 1 →
    ∃ (Rcap : ℝ) (mcap : ℕ), Dcap + 1 < Rcap ∧
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
    ∀ t : ℝ, H.time k < t → t < s → Gk.DerivativeBoundBefore (2 * Ctime) (2 * qcan) t →
    ∀ y : (H.stage k).Carrier, H.CapWindowPoint records k y t Dcap θcap →
      qcan < Gk.flow.scalar t y →
      (τmin ≤ Gk.flow.scalar t y * (t - H.time k) →
        ∃ W : CanonicalWitness Gk.flow ε C1 C2 y t, W.capTubeHasNeckChart ε) ∧
      |derivWithin (fun v => Gk.flow.scalar v y) (Iic t) t| ≤ Ctime * Gk.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t y v| ≤
          Cgrad * Gk.flow.scalar t y * Real.sqrt (Gk.flow.scalar t y) *
            Real.sqrt ((Gk.flow.base.metric t).inner y v v) := by
  obtain ⟨a₀, ha₀, hHI⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  obtain ⟨Cε, δ0, hCε, hδ0, hδ01, hpipe⟩ :=
    OrientedThreeStage.IncomingSlab.exists_canonicalWitness_of_orientedWitness.{u} hε hε'
  set δ := min δ0 (1 / 4) with hδdef
  have hδ : 0 < δ := lt_min hδ0 (by norm_num)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hδ1 : δ < 1 := hδ4.trans_lt (by norm_num)
  obtain ⟨τQ, hτQ, hL6⟩ := exists_uniform_orientedWitness_of_standard_close_endpoint hδ hδ1
  obtain ⟨CA, hCA, hA⟩ :=
    OrientedThreeStage.IncomingSlab.exists_scalar_derivative_bounds_of_window_orientedWitness.{u}
  obtain ⟨c₀, hc₀, hQlow⟩ := exists_standard_scalar_lower_bound
  set Θ₃ := 2 * τQ / (c₀ + 2 * τQ) with hΘ₃def
  have hΘ₃ : 0 < Θ₃ := by positivity
  have hΘ₃1 : Θ₃ < 1 := by rw [hΘ₃def, div_lt_one (by positivity)]; linarith
  obtain ⟨cB, CB, -, hCB, hyoung⟩ :=
    exists_uniform_derivative_gradient_bounds_of_cap_window_trace.{u} Θ₃ hΘ₃ hΘ₃1
  refine ⟨Cε, max τQ δ⁻¹ + 1, ⟨max CA CB, le_max_of_le_left hCA.le⟩, hCε, by positivity, ?_⟩
  intro C1 C2 τmin Ctime Cgrad hC1 hC2 hτmin hCt hCg Dcap θcap hDcap hθcap
  have hCt' : max CA CB ≤ (Ctime : ℝ) := hCt
  have hCg' : max CA CB ≤ (Cgrad : ℝ) := hCg
  set Θ := max θcap (1 / 2) with hΘdef
  have hΘ1 : Θ < 1 := max_lt hθcap (by norm_num)
  have hΘ0 : 0 < Θ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨eta, heta, hlower⟩ :=
    exists_uniform_standard_metric_scalar_lower_comparison Θ hΘ0.le hΘ1
  obtain ⟨DW, NW, eW, hDW, heW, hwit⟩ := hL6 Θ (Dcap + 1) hΘ1
  obtain ⟨Pb, Creset, Cb1, -, -, hCb1, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace.{u} Θ (2 * Ctime) hΘ0 hΘ1
  obtain ⟨R1, hR1, m1, -, ζ1, δ1, hζ1, -, hδ1', hbr⟩ :=
    hbridge DW eW eta (by linarith) heW heta NW
  obtain ⟨Cb2, hCb2, hy2⟩ := hyoung (2 * Ctime)
  obtain ⟨R2, hR2, m2, -, ζ2, δ2, hζ2, -, hδ2, hyc⟩ := hy2 Dcap hDcap
  refine ⟨max R1 R2, max m1 m2, hR2.trans_le (le_max_right _ _), ?_⟩
  intro qcan hqcan
  set Cb := min Cb1 Cb2 with hCbdef
  have hCb : 0 < Cb := lt_min hCb1 hCb2
  set ρmax := min (Real.sqrt (Cb / (4 * qcan))) (Real.sqrt (a₀ / 2)) with hρdef
  have hρmax : 0 < ρmax := lt_min (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_pos.mpr (by positivity))
  have hρ₁ : ρmax ^ 2 ≤ Cb / (4 * qcan) := by
    have h := pow_le_pow_left₀ hρmax.le (min_le_left _ _) 2
    rwa [Real.sq_sqrt (by positivity)] at h
  have hρ₂ : ρmax ^ 2 ≤ a₀ / 2 := by
    have h := pow_le_pow_left₀ hρmax.le (min_le_right _ _) 2
    rwa [Real.sq_sqrt (by positivity)] at h
  refine ⟨min δ1 δ2, ρmax, min ζ1 ζ2, lt_min hδ1' hδ2, hρmax, lt_min hζ1 hζ2, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec k s Gk hGk hderiv t hkt
    hts hcur y hcap hR
  obtain ⟨j, hl, A, b, x, hanchor, hxD, hage⟩ := hcap
  obtain ⟨hHI1, hHI2⟩ := hHI H.toHistory hId.some
  set q := ((records j).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j).static b).neck.scale_pos
  obtain ⟨hbirth, haq⟩ := hrec.birth_scale_bounds hΛδ j b hqcan hCb ha₀ hρb hρ₁ hρ₂
  have hba : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hl
  have hderiv2 := eventSlabsDerivative_two_mul hqcan hderiv
  have hθΘ : θcap ≤ Θ := le_max_left _ _
  have hxD' : ‖x.val‖ < DW + 1 := by linarith
  have hbirth1 : 2 * qcan ≤ Cb1 * q :=
    hbirth.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le)
  have hbirth2 : 2 * qcan ≤ Cb2 * q :=
    hbirth.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hq.le)
  obtain ⟨G, L, hG, -, hL, -, -, -, -, -, -, -, z, hzx, hy, Ξ, hΞs, -, hΞmark, hΞ, gflow, S,
      -, hS2, hS3, -, hS5, -, -, Q, -, hclose⟩ :=
    hbr H p₀ δbound ρbound records hrec (hδb.trans (min_le_left _ _))
      ((le_max_left _ _).trans hrad) ((le_max_left _ _).trans hord) (hacc.trans (min_le_left _ _))
      (2 * qcan) a₀ θcap (by positivity) hθΘ hHI1 hHI2 k s Gk hGk hderiv2 t hkt hts hcur
      j hl y A b x hanchor hage hxD' hbirth1 haq
  have hyz : (Ξ z).val.val = y := congrArg Subtype.val hΞmark
  set T := q * (t - H.time j.succ) with hTdef
  have hjt : H.time j.succ < t := hba.trans_lt hkt
  have hT0 : 0 ≤ T := mul_nonneg hq.le (by linarith)
  have hTθ : T ≤ θcap := by
    have h1 := mul_le_mul_of_nonneg_left hage hq.le
    rwa [mul_comm θcap, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
  have hTmem : T ∈ Icc 0 T := ⟨hT0, le_rfl⟩
  have htT : H.time j.succ + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hST := H.capWindow_flow_metric_eq Gk hl hΞ hq hG hL hS2 hS5 T hTmem
    (by rw [htT]; linarith)
  rw [htT] at hST
  have hRS : S.scalar T z = q⁻¹ * Gk.flow.scalar t y := by
    change metricScalarAt (S.base.metric T) z = _
    rw [hST, metricScalarAt_localPullMetric_scaleMetric, hyz]
    rfl
  have hRpos : 0 < Gk.flow.scalar t y := hqcan.trans hR
  have hTRS : T * S.scalar T z = Gk.flow.scalar t y * (t - H.time j.succ) := by
    rw [hRS, hTdef]
    field_simp
  have hwit' : τQ ≤ T * S.scalar T z →
      ∀ o, OrientedWitness S o δ standardModelKappa z T := by
    intro hτ o
    exact hwit Q T hT0 (hTθ.trans hθΘ) S hS3 (fun τ hτ' => (hclose τ hτ').1) o z
      (by rw [hzx]; linarith) hτ
  have hΦ := H.toHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val j.succ k hl G hΞ
  have hderivClause : |derivWithin (fun v => Gk.flow.scalar v y) (Iic t) t| ≤
        Ctime * Gk.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t y v| ≤
          Cgrad * Gk.flow.scalar t y * Real.sqrt (Gk.flow.scalar t y) *
            Real.sqrt ((Gk.flow.base.metric t).inner y v v) := by
    by_cases hyng : t - H.time j.succ ≤ Θ₃ * q⁻¹
    · obtain ⟨-, hd, hg⟩ := hyc H p₀ δbound ρbound records hrec (hδb.trans (min_le_right _ _))
        ((le_max_right _ _).trans hrad) ((le_max_right _ _).trans hord)
        (hacc.trans (min_le_right _ _)) (2 * qcan) a₀ Θ₃ (by positivity) le_rfl hHI1 hHI2 k s Gk
        hGk hderiv2 t hkt hts hcur j hl y A b x hanchor hyng hxD hbirth2 haq
      have hCBt : CB ≤ (Ctime : ℝ) := (le_max_right _ _).trans hCt'
      have hCBg : CB ≤ (Cgrad : ℝ) := (le_max_right _ _).trans hCg'
      refine ⟨hd.trans (mul_le_mul_of_nonneg_right hCBt (sq_nonneg _)), fun v => (hg v).trans ?_⟩
      gcongr
    · have hTΘ₃ : Θ₃ ≤ T := by
        have h1 := mul_le_mul_of_nonneg_left (not_le.mp hyng).le hq.le
        rwa [mul_comm Θ₃, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
      have hT1 : T < 1 := by linarith only [hTθ, hθcap]
      have hlow := (hlower Q (standardCapWindow DW) (S.base.metric T) T
        ⟨hT0, hTθ.trans hθΘ⟩ z (fun i hi => ((hclose T hTmem).2 i hi z).le)).2
      rw [metricScalarAt_restrictOpen] at hlow
      have hτ := le_mul_of_half_standard_scalar_lower hτQ.le hc₀ hT1
        (hQlow Q z.val T ⟨hT0, hT1⟩) hlow hTΘ₃
      have h := hA Gk S hS3 hΦ hq hkt hts le_rfl hST (hwit' hτ) hδ4
        Ctime Cgrad ((le_max_left _ _).trans hCt') ((le_max_left _ _).trans hCg')
      subst hyz
      exact h
  refine ⟨fun hageC => ?_, hderivClause⟩
  have hτmin' : max τQ δ⁻¹ + 1 ≤ τmin := hτmin
  have hmono : Gk.flow.scalar t y * (t - H.time k) ≤
      Gk.flow.scalar t y * (t - H.time j.succ) :=
    mul_le_mul_of_nonneg_left (by linarith) hRpos.le
  have hτ : τQ ≤ T * S.scalar T z := by
    rw [hTRS]
    linarith only [hmono, hageC, hτmin', le_max_left τQ δ⁻¹]
  have hage2 : (δ * Gk.flow.scalar t y)⁻¹ ≤ t - H.time k := by
    have h1 : δ⁻¹ ≤ Gk.flow.scalar t y * (t - H.time k) := by
      linarith only [hageC, hτmin', le_max_right τQ δ⁻¹]
    rw [inv_le_iff_one_le_mul₀ (mul_pos hδ hRpos)]
    have h2 := mul_le_mul_of_nonneg_left h1 hδ.le
    rw [mul_inv_cancel₀ hδ.ne'] at h2
    have h3 : (t - H.time k) * (δ * Gk.flow.scalar t y) =
        δ * (Gk.flow.scalar t y * (t - H.time k)) := by ring
    rw [h3]
    exact h2
  have hOW := H.orientedWitness_of_capWindow_flow Gk hl hΞ hq hkt le_rfl hts hG hL hS2 hS5 hΞs
    hyz (hwit' hτ) hage2
  refine hpipe Gk (H.stage k).orientation (min_le_left _ _) ?_ hOW C1 C2 hC1 hC2
  intro σ hσ
  exact ⟨by linarith [hσ.1], hσ.2.trans hts⟩

theorem exists_capWindow_canonicalBoundsOn (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (C₀ τ₀ : ℝ) (Ctime₀ : ℝ≥0), 1 ≤ C₀ ∧ 0 < τ₀ ∧
    ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), C₀ ≤ C1 → C₀ ≤ C2 → τ₀ ≤ τmin →
      Ctime₀ ≤ Ctime → Ctime₀ ≤ Cgrad →
    ∀ (Dcap θcap : ℝ), 0 < Dcap → θcap < 1 →
    ∃ (Rcap : ℝ) (mcap : ℕ), Dcap + 1 < Rcap ∧
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
    ∀ t₀ η : ℝ, Gk.DerivativeBoundBefore (2 * Ctime) (2 * qcan) (t₀ + η) →
      Gk.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
        fun y t => H.CapWindowPoint records k y t Dcap θcap := by
  obtain ⟨C₀, τ₀, Ct₀, hC₀, hτ₀, h⟩ := exists_capWindowPoint_bounds P₀ g₀ hε hε'
  refine ⟨C₀, τ₀, Ct₀, hC₀, hτ₀, ?_⟩
  intro C1 C2 τmin Ctime Cgrad hC1 hC2 hτ hCt hCg Dcap θcap hDcap hθcap
  obtain ⟨Rcap, mcap, hRcap, h⟩ := h C1 C2 τmin Ctime Cgrad hC1 hC2 hτ hCt hCg Dcap θcap hDcap
    hθcap
  refine ⟨Rcap, mcap, hRcap, fun qcan hq => ?_⟩
  obtain ⟨δmax, ρmax, εcap, hδ, hρ, hεc, h⟩ := h qcan hq
  refine ⟨δmax, ρmax, εcap, hδ, hρ, hεc, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec k s Gk hGk hder t₀ η
    hcur y t hat _ htη hts hR hcap
  exact h p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec k s Gk hGk hder t hat
    hts (Gk.derivativeBoundBefore_mono htη.le hcur) y hcap hR

end RetainedCoreHistory

theorem capWindowContinuation_of_slab_interior (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∀ (B ε : ℝ), 0 < B → 0 < ε → ε < 1 / 11 →
    ∃ (C1₀ C2₀ τ₀ : ℝ) (Ctime₀ Cgrad₀ : ℝ≥0), 1 ≤ C1₀ ∧ 1 ≤ C2₀ ∧ 0 < τ₀ ∧
    ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0),
      C1₀ ≤ C1 → C2₀ ≤ C2 → τ₀ ≤ τmin → Ctime₀ ≤ Ctime → Cgrad₀ ≤ Cgrad →
    ∀ (κ : ℝ) (phi : ℝ → ℝ) (θ Dcap θcap : ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi →
      0 < θ → 0 < Dcap → θcap < 1 →
    ∃ (Rcap q₀ : ℝ) (mcap : ℕ), Dcap + 1 < Rcap ∧ 0 < q₀ ∧
    ∀ qcan : ℝ, q₀ ≤ qcan →
    ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Rcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax →
      ∀ (H : RetainedCoreHistory.{u}) (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
        H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        H.EventSlabsPinched phi →
        (∀ j : Fin H.eventCount,
          H.EventSlabsCanonical ε C1 C2 qcan τmin j.castSucc →
          H.EventSlabsDerivative Ctime qcan j.castSucc →
          H.EventSlabsGradient Cgrad qcan j.castSucc →
          ∀ t₀ : ℝ, t₀ ∈ Ioo (H.time j.castSucc) (H.time j.succ) →
            (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin t₀ →
            (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀ →
            (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan t₀ →
            H.NoncollapsedBefore κ ε t₀ →
            ∃ η : ℝ, 0 < η ∧
              (H.toHistory.event j).incoming.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
                fun y t => H.CapWindowPoint records j.castSucc y t Dcap θcap) ∧
        ∀ (s : ℝ)
          (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
          (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
          Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
          H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
          H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
          H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
          H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
          ∀ t₀ : ℝ, t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s →
            G.CanonicalBefore ε C1 C2 qcan τmin t₀ → G.DerivativeBoundBefore Ctime qcan t₀ →
            G.GradientBoundBefore Cgrad qcan t₀ →
            H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀ →
            ∃ η : ℝ, 0 < η ∧ G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
              fun y t => H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap := by
  intro B ε hB hε hε'
  obtain ⟨C₀, τ₀, Ct₀, hC₀, hτ₀, h⟩ :=
    RetainedCoreHistory.exists_capWindow_canonicalBoundsOn P₀ g₀ hε hε'
  refine ⟨C₀, C₀, τ₀, max Ct₀ 1, max Ct₀ 1, hC₀, hC₀, hτ₀, ?_⟩
  intro C1 C2 τmin Ctime Cgrad hC1 hC2 hτ hCt hCg κ phi θ Dcap θcap _ _ _ hDcap hθcap
  have hCtpos : 0 < Ctime := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hCt)
  obtain ⟨Rcap, mcap, hRcap, h⟩ := h C1 C2 τmin Ctime Cgrad hC1 hC2 hτ
    ((le_max_left _ _).trans hCt) ((le_max_left _ _).trans hCg) Dcap θcap hDcap hθcap
  refine ⟨Rcap, 1, mcap, hRcap, one_pos, fun qcan hqcan => ?_⟩
  have hq : 0 < qcan := one_pos.trans_le hqcan
  obtain ⟨δmax, ρmax, εcap, hδ, hρ, hεc, h⟩ := h qcan hq
  refine ⟨δmax, ρmax, εcap, hδ, hρ, hεc, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hH p records hrec _
  have hS := h p₀ δbound ρbound hacc hrad hord hδb hρb H hH.1 hH.2.2.2.2 p records hrec
  refine ⟨fun j _ hder _ t₀ ht₀ _ hdb _ _ => ?_, fun s G hG _ _ hder _ _ t₀ ht₀ _ hdb _ _ => ?_⟩
  · obtain ⟨η, hη, -, hext⟩ :=
      (H.toHistory.event j).incoming.exists_derivativeBoundBefore_extend hCtpos hq ht₀ hdb
    exact ⟨η, hη, hS j.castSucc _ (H.toHistory.event j).incoming
      (H.isContinuationSlab_event hH.2.2.1 j).2 hder t₀ η hext⟩
  · obtain ⟨η, hη, -, hext⟩ := G.exists_derivativeBoundBefore_extend hCtpos hq ht₀ hdb
    exact ⟨η, hη, hS _ s G hG.2 hder t₀ η hext⟩

theorem capWindowContinuation_of_slab_start_bounds (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric)
    (hslice : ∃ Cs : ℝ≥0, ∀ Ctime : ℝ≥0, Cs ≤ Ctime →
      ∃ (Rs qs : ℝ) (ms : ℕ), 0 < qs ∧ ∀ qcan : ℝ, qs ≤ qcan →
      ∃ (δs ρs εs : ℝ), 0 < δs ∧ 0 < ρs ∧ 0 < εs ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εs → Rs ≤ p₀.modelRadius → ms ≤ p₀.modelOrder →
        δbound ≤ δs → ρbound ≤ ρs →
      ∀ H : RetainedCoreHistory.{u}, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
        p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
        H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
        Gk.flow.base.metric (H.time k) = H.initialMetric k →
        H.EventSlabsDerivative Ctime qcan k →
        (∀ y : (H.stage k).Carrier, ContinuousWithinAt (fun z : ℝ × (H.stage k).Carrier =>
          derivWithin (fun v => Gk.flow.scalar v z.2) (Ici z.1) z.1)
            (Ici (H.time k) ×ˢ univ) (H.time k, y)) ∧
        ∀ y : (H.stage k).Carrier, qcan < Gk.flow.scalar (H.time k) y →
          |derivWithin (fun v => Gk.flow.scalar v y) (Ici (H.time k)) (H.time k)| ≤
            Ctime * Gk.flow.scalar (H.time k) y ^ 2) :
    CapWindowContinuation P₀ g₀ := by
  intro B ε hB hε hε'
  obtain ⟨Cs, hCs⟩ := hslice
  obtain ⟨C₀, τ₀, Ct₀, hC₀, hτ₀, h⟩ :=
    RetainedCoreHistory.exists_capWindow_canonicalBoundsOn P₀ g₀ hε hε'
  refine ⟨C₀, C₀, τ₀, max (max Ct₀ 1) Cs, max (max Ct₀ 1) Cs, hC₀, hC₀, hτ₀, ?_⟩
  intro C1 C2 τmin Ctime Cgrad hC1 hC2 hτ hCt hCg κ phi θ Dcap θcap _ _ _ hDcap hθcap
  have hCt1 : max Ct₀ 1 ≤ Ctime := (le_max_left _ _).trans hCt
  have hCg1 : max Ct₀ 1 ≤ Cgrad := (le_max_left _ _).trans hCg
  have hCtpos : 0 < Ctime := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hCt1)
  obtain ⟨Rs, qs, ms, hqs, hCs⟩ := hCs Ctime ((le_max_right _ _).trans hCt)
  obtain ⟨Rcap, mcap, hRcap, h⟩ := h C1 C2 τmin Ctime Cgrad hC1 hC2 hτ
    ((le_max_left _ _).trans hCt1) ((le_max_left _ _).trans hCg1) Dcap θcap hDcap hθcap
  refine ⟨max Rcap Rs, max 1 qs, max mcap ms, hRcap.trans_le (le_max_left _ _),
    one_pos.trans_le (le_max_left _ _), fun qcan hqcan => ?_⟩
  have hq : 0 < qcan := one_pos.trans_le ((le_max_left _ _).trans hqcan)
  obtain ⟨δmax, ρmax, εcap, hδ, hρ, hεc, h⟩ := h qcan hq
  obtain ⟨δs, ρs, εs, hδs, hρs, hεs, hCs⟩ := hCs qcan ((le_max_right _ _).trans hqcan)
  refine ⟨min δmax δs, min ρmax ρs, min εcap εs, lt_min hδ hδs, lt_min hρ hρs, lt_min hεc hεs, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hH p records hrec _
  have hS := h p₀ δbound ρbound (hacc.trans (min_le_left _ _)) ((le_max_left _ _).trans hrad)
    ((le_max_left _ _).trans hord) (hδb.trans (min_le_left _ _)) (hρb.trans (min_le_left _ _)) H
    hH.1 hH.2.2.2.2 p records hrec
  have hT := hCs p₀ δbound ρbound (hacc.trans (min_le_right _ _)) ((le_max_right _ _).trans hrad)
    ((le_max_right _ _).trans hord) (hδb.trans (min_le_right _ _)) (hρb.trans (min_le_right _ _))
    H hH.1 hH.2.2.2.2 p records hrec
  refine ⟨fun j _ hder _ t₀ ht₀ _ hdb _ _ => ?_, fun s G hG _ _ hder _ _ t₀ ht₀ _ hdb _ _ => ?_⟩
  · have hGk := (H.isContinuationSlab_event hH.2.2.1 j).2
    obtain ⟨hreg, hstart⟩ := hT j.castSucc _ (H.toHistory.event j).incoming hGk hder
    obtain ⟨η, hη, -, hext⟩ :=
      (H.toHistory.event j).incoming.exists_derivativeBoundBefore_extend_of_slice hCtpos hq ht₀
        (fun _ => hreg) (fun _ => hstart) hdb
    exact ⟨η, hη, hS j.castSucc _ (H.toHistory.event j).incoming hGk hder t₀ η hext⟩
  · obtain ⟨hreg, hstart⟩ := hT _ s G hG.2 hder
    obtain ⟨η, hη, -, hext⟩ := G.exists_derivativeBoundBefore_extend_of_slice hCtpos hq ht₀
      (fun _ => hreg) (fun _ => hstart) hdb
    exact ⟨η, hη, hS _ s G hG.2 hder t₀ η hext⟩

theorem capWindowContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    CapWindowContinuation P₀ g₀ :=
  capWindowContinuation_of_slab_start_bounds P₀ g₀
    (RetainedCoreHistory.exists_slice_bounds_at_slab_start P₀ g₀)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
