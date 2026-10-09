import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapWindowZC_S58

/-!
# CH12-S64, group 1 (main): `hZC_S64` = `hZC_S48_shape` of `[FROZEN v2] CH12-S48`, verbatim.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

private local instance sigmaCompactWindow_S64 (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

private theorem window_inclusion_isSmoothEmbedding_S64 {D D' : ℝ} (hDD : D ≤ D') :
    IsSmoothEmbedding ThreeModel ThreeModel ∞
      (TopologicalSpace.Opens.inclusion
        (show standardCapWindow D ≤ standardCapWindow D' from by
          intro x hx
          change ‖x‖ < D' + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hDD])) := by
  let inc := TopologicalSpace.Opens.inclusion
    (show standardCapWindow D ≤ standardCapWindow D' from
      by
          intro x hx
          change ‖x‖ < D' + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hDD])
  have hc : ContMDiff ThreeModel ThreeModel ∞ inc := contMDiff_inclusion _
  have hl := DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
    inc hc (fun x => by rw [mfderiv_opens_incl]; exact fun v w h => h) rfl
  apply Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective hl
  intro x y h
  exact Subtype.ext (congrArg (fun z : standardCapWindow D' => z.val) h)

theorem hZC_S64 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hP3 : P3_O2 Hp) (hcompat : CompatibleUpgradedCapRecords_S58 Hp) :
    ∀ Ctime : ℝ≥0, P2_O2 Hp Ctime → ∃ θ : ℝ, 0 < θ ∧
    ∀ Dcap C0 : ℝ, StandardCap.transitionEnd < Dcap → 0 < C0 → ∀ K : ℕ, ∃ (B : ℕ → ℝ) (T : ℝ),
    ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ T₀ : ℝ, T ≤ T₀ → T₀ ≤ s.time →
    ∀ (p : CutoffParameters)
      (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
        T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
        GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i p),
      (p.delta = Hp.parameters.delta ∧ p.neckRadius = Hp.parameters.neckRadius ∧
        p.fixed = Hp.parameters.fixed ∧ p.recenterConstant = Hp.parameters.recenterConstant ∧
        32 * (Dcap + 1) + 2 ≤ p.modelRadius ∧
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b))) →
      ∀ (y : s.stage.Carrier) (ρ : ℝ), 0 < ρ → metricScalarAt s.metric y ≤ C0 / ρ ^ 2 →
      (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
          (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
          (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
          (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
            (Fin.last (sliceHistoryR_O3 F s).eventCount) hl y)
          (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
          (x : standardCapWindow p.modelRadius),
          B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            s.time - (sliceHistoryR_O3 F s).time j.succ ≤
              θ * (((records j hj).static b).neck.scale)⁻¹) →
      ∀ k ≤ K, curvatureDerivativeNorm s.metric k y ≤ B k * (ρ ^ (k + 2))⁻¹ := by
  intro Ctime hP2
  obtain ⟨C₀, hC₀, -, η, ε₀, hη, hε₀, hεhalf, hker⟩ :=
    exists_uniform_prepared_incoming_cap_window_flow_with_curvature_derivative_bounds_uniform_S54.{u, 0, 0, u}
      Ctime
  obtain ⟨c, hc, hlap⟩ := lapR_le_jet_S52
  obtain ⟨B₂, hB₂, hker2⟩ := hker 2
  obtain ⟨ε₁, hε₁, hinit⟩ := window_init_scalar_S53
  obtain ⟨a₀, ha₀, ha₀h⟩ := exists_a0_slice_S53 g F
  obtain ⟨Ccmp, hCc, hscale⟩ := capScale_facts_S58 Hp hcompat
  have hr0 := Hp.parameters.neckRadius_pos 0 le_rfl
  set E : ℝ := min (C₀ / Ccmp) (a₀ / (Ccmp * Hp.parameters.neckRadius 0 ^ 2)) with hE
  have hE0 : 0 < E := lt_min (by positivity) (by positivity)
  obtain ⟨Tcap, hTcap⟩ := hscale (Real.sqrt E) (Real.sqrt_pos.mpr hE0)
  have hsqE : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE0.le
  have hsB₂ : 0 < Real.sqrt B₂ := Real.sqrt_pos.mpr (by linarith only [hB₂])
  set θ : ℝ := min (min η (1 / (4 * c * Real.sqrt B₂))) (1 / Ccmp) with hθdef
  have hθ : 0 < θ := lt_min (lt_min hη (by positivity)) (by positivity)
  have hθ1 : θ ≤ η := (min_le_left _ _).trans (min_le_left _ _)
  have hθ2 : θ ≤ 1 / (4 * c * Real.sqrt B₂) := (min_le_left _ _).trans (min_le_right _ _)
  have hθC : θ * Ccmp ≤ 1 := by
    have h := (min_le_right _ _ : θ ≤ 1 / Ccmp)
    rw [le_div_iff₀ hCc] at h; exact h
  refine ⟨θ, hθ, fun Dcap C0 hDcap hC0 K => ?_⟩
  have hDcap1 : 1 ≤ Dcap := (one_le_transitionEnd_S58).trans hDcap.le
  obtain ⟨B_K, hBK, hkerK⟩ := hker (max 2 K)
  obtain ⟨δ₂, hδ₂, hk2⟩ := hker2 (32 * (Dcap + 1) + 1) (Dcap + 1) (by linarith only [hDcap1])
    (by linarith only [hDcap1]) (by linarith only [hDcap1])
  obtain ⟨δK, hδK, hkK⟩ := hkerK (32 * (Dcap + 1) + 1) (Dcap + 1) (by linarith only [hDcap1])
    (by linarith only [hDcap1]) (by linarith only [hDcap1])
  obtain ⟨T₁, hT₁⟩ := late_linked_witness_S48 Hp hdec hP3 (32 * (Dcap + 1) + 1 + 1) (by linarith only [hDcap1])
    (max 2 K + 2) (min ε₀ ε₁) (lt_min hε₀ hε₁)
  obtain ⟨T₂, hT₂⟩ := hdec (min δ₂ δK) (lt_min hδ₂ hδK)
  refine ⟨fun k => Real.sqrt B_K * (2 * Real.sqrt C0) ^ (k + 2),
    max (max T₁ T₂) Tcap + θ + 1, ?_⟩
  intro s hTs T₀ hT₀ hT₀s p records hrec_ y ρ hρ hZ0 hcap k hk
  obtain ⟨hpd, hpn, hpf, hpc, hrad, hlink⟩ := hrec_
  obtain ⟨j, hj, hl, B, b, x, hxB, hxr, hage⟩ := hcap
  set R := records j hj with hR
  set q : ℝ := (R.static b).neck.scale with hqdef
  have hq : 0 < q := (R.static b).neck.scale_pos
  have hTs' : max (max T₁ T₂) Tcap + θ + 1 ≤ T₀ := hT₀
  have htj : max (max T₁ T₂) Tcap + 1 ≤ (sliceHistoryR_O3 F s).time j.succ := by
    linarith only [hj, hTs']
  have hts : (sliceHistoryR_O3 F s).time j.succ ≤ s.time :=
    (((sliceHistoryR_O3 F s).time_strictMono.monotone hl).trans (sliceSlabR_O3 F s).lt.le)
  have hTcap' : Tcap ≤ s.time := by
    have : Tcap ≤ (sliceHistoryR_O3 F s).time j.succ := by linarith only [htj, le_max_right (max T₁ T₂) Tcap]
    exact this.trans hts
  obtain ⟨hL1, hL2⟩ := hTcap s p j R b hpd hpn hpf hpc (hlink j hj b) hTcap' θ hθ hθC hage hts
  rw [hsqE, ← hpn] at hL1
  rw [hsqE] at hL2
  -- scale facts: q₀ := C₀ q
  have hq₀ : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ C₀ * q := by
    rw [← hpn]
    refine hL1.trans ?_
    have h1 : E * Ccmp ≤ C₀ := by
      have := (min_le_left (C₀ / Ccmp) (a₀ / (Ccmp * Hp.parameters.neckRadius 0 ^ 2)))
      rw [le_div_iff₀ hCc] at this; exact this
    exact mul_le_mul_of_nonneg_right h1 hq.le
  have h1a : 1 ≤ a₀ * q := by
    have hle : Ccmp * (E * Hp.parameters.neckRadius 0 ^ 2) ≤ a₀ := by
      have := min_le_right (C₀ / Ccmp) (a₀ / (Ccmp * Hp.parameters.neckRadius 0 ^ 2))
      rw [le_div_iff₀ (by positivity)] at this
      calc Ccmp * (E * Hp.parameters.neckRadius 0 ^ 2)
          = E * (Ccmp * Hp.parameters.neckRadius 0 ^ 2) := by ring
        _ ≤ a₀ := this
    have hpos : 0 < Ccmp * (E * Hp.parameters.neckRadius 0 ^ 2) := by positivity
    have h3 : a₀⁻¹ ≤ q := (inv_anti₀ hpos hle).trans hL2
    have := mul_le_mul_of_nonneg_left h3 ha₀.le
    rwa [mul_inv_cancel₀ ha₀.ne'] at this
  have hqT : q * (s.time - (sliceHistoryR_O3 F s).time j.succ) ≤ θ := by
    have := mul_le_mul_of_nonneg_left hage hq.le
    have e : q * (θ * q⁻¹) = θ := by field_simp
    linarith only [this, e]
  have hT0 : 0 ≤ q * (s.time - (sliceHistoryR_O3 F s).time j.succ) :=
    mul_nonneg hq.le (sub_nonneg.2 hts)
  let recsTot : ∀ j' : Fin (sliceHistoryR_O3 F s).eventCount,
      GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory j' Hp.parameters :=
    fun j' => (F.tower.history (sliceIndexR_O3 F s)).geometricCutoffRecordOfPrefix
      (sliceStageR_O3 F s)
      (Hp.records (sliceIndexR_O3 F s)
        (Fin.castLE (Nat.le_of_lt_succ (sliceStageR_O3 F s).isLt) j'))
  have hrecδ : ∀ j' : Fin (sliceHistoryR_O3 F s).eventCount, j.succ ≤ j'.castSucc →
      ∀ b', (recsTot j').delta b' ≤ min δ₂ δK := by
    intro j' hj' b'
    have hle' := (recsTot j').delta_le b'
    rw [Hp.accuracy_eq] at hle'
    have htj' : (sliceHistoryR_O3 F s).time j.succ < (sliceHistoryR_O3 F s).time j'.succ :=
      (sliceHistoryR_O3 F s).time_strictMono (lt_of_le_of_lt hj' Fin.castSucc_lt_succ)
    exact hle'.trans (hT₂ _ (by linarith only [htj, htj', le_max_left (max T₁ T₂) Tcap, le_max_right T₁ T₂])).le
  have hD : 32 * (Dcap + 1) + 1 + 1 ≤ p.modelRadius := by linarith only [hrad]
  obtain ⟨x₀, δ', d, w, -, hmetric⟩ := hT₁ (sliceHistoryR_O3 F s) j p R b hpd hpc hpf hD
    (hlink j hj b) (by linarith only [htj, le_max_left (max T₁ T₂) Tcap, le_max_left T₁ T₂])
  let G := (sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl
  let L := (sliceSlabR_O3 F s).endpointTerminalLimitMetric
    ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount))
  have hyG : y ∈ G.terminalRegularRegion := by
    change y ∈ ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl).terminalRegularRegion
    rw [(sliceSlabR_O3 F s).terminalRegularRegion_eq_univ _]; exact mem_univ _
  let x' : G.terminalRegularOpen := ⟨y, hyG⟩
  have hLm : L.metric = s.metric.restrictOpen G.terminalRegularOpen := by
    change ((sliceSlabR_O3 F s).flow.base.metric s.time).restrictOpen _ = _
    rw [sliceSlabR_metric_time_O3 F s]
    rfl
  let z : standardCapWindow (32 * (Dcap + 1) + 1) := ⟨x.val, by
    change ‖x.val‖ < 32 * (Dcap + 1) + 1 + 1; linarith only [hxr, hDcap1]⟩
  have hDD : 32 * (Dcap + 1) + 1 ≤ 32 * (Dcap + 1) + 1 + 1 := le_add_of_nonneg_right zero_le_one
  have hsub : standardCapWindow (32 * (Dcap + 1) + 1 + 1) ≤ standardCapWindow p.modelRadius := by
    intro y hy
    change ‖y‖ < p.modelRadius + 1
    change ‖y‖ < 32 * (Dcap + 1) + 1 + 1 + 1 at hy
    linarith only [hy, hD]
  let Jbig := (R.static b).window ∘ TopologicalSpace.Opens.inclusion hsub
  have hJbig : IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig :=
    (R.static b).window_smooth.comp (window_inclusion_isSmoothEmbedding_S64 hD) (by simp)
  have hA : B.point j.succ le_rfl hl = Jbig (TopologicalSpace.Opens.inclusion
      (show standardCapWindow (32 * (Dcap + 1) + 1) ≤ standardCapWindow (32 * (Dcap + 1) + 1 + 1) from
        fun y hy => by
          change ‖y‖ < 32 * (Dcap + 1) + 1 + 1 + 1
          change ‖y‖ < 32 * (Dcap + 1) + 1 + 1 at hy
          linarith only [hy]) z) :=
    hxB.trans (congrArg (R.static b).window (Subtype.ext rfl))
  have hslab := sliceHistory_eventSlabsDerivative_O3 Hp s Ctime (C₀ * q) hP2 hq₀
  have hfin := slice_hfinal_S53 Hp s Ctime (C₀ * q) hP2 hq₀
  have hmarg : 32 * (Dcap + 1) + 1 + 1 ≤ 32 * (Dcap + 1) + 1 + 1 := le_rfl
  -- call N = 2
  obtain ⟨Ξ, hΞs, -, hΞx, hΞ, gflow, S, -, -, hS, hS0, -, -, h10, h11, -, -⟩ :=
    hk2 w le_rfl (by omega) (min_le_left _ _) (sliceHistoryR_O3 F s).toHistory j.succ
      (Fin.last _) hl s.time G L (sliceSlabR_initial_O3 F s) Jbig hJbig q (C₀ * q) a₀ hq
      (mul_pos hC₀ hq) le_rfl h1a hmetric Hp.parameters recsTot (ha₀h s).1 (ha₀h s).2
      (fun j' hj' _ b' => (hrecδ j' hj' b').trans (min_le_left _ _))
      (fun j' _ hjl => hslab j' hjl) hfin (hqT.trans hθ1) z x' B hA
  have hΞloc := incoming_comp_isLocalDiffeo_S53 (sliceHistoryR_O3 F s).toHistory j.succ
    (Fin.last _) hl G Ξ hΞs hΞ
  have hzr : ‖z.val‖ ≤ Dcap + 1 := hxr.le
  have hzD : ‖z.val‖ < 32 * (Dcap + 1) + 1 := by
    change ‖x.val‖ < _; linarith only [hxr, hDcap1]
  have hpos4 : 0 < 4 * c * Real.sqrt B₂ := by positivity
  have hθ2' : θ * (4 * c * Real.sqrt B₂) ≤ 1 := by rwa [le_div_iff₀ hpos4] at hθ2
  have hsmall : c * Real.sqrt B₂ * (q * (s.time - (sliceHistoryR_O3 F s).time j.succ)) ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hqT (mul_pos hc hsB₂).le
    nlinarith only [this, hθ2']
  have hlow0 := cap_scalar_lower_S58 c hc hlap B₂ _ q hT0 hq S hS z
    (by
      change 1 / 2 ≤ metricScalarAt (S.base.metric 0) z
      rw [hS0]
      exact hinit w _ hDD (min_le_right _ _) (by omega) z hzD)
    (fun t ht => h10 2 le_rfl t ht z hzr) L.metric _ hΞloc.1 hΞloc.2
    (fun y' v w' => by
      have := h11 y' v w'
      rwa [scaleMetric_inner] at this) hsmall
  have hlow : q / 4 ≤ metricScalarAt s.metric y := by
    let U : TopologicalSpace.Opens s.stage.Carrier := G.terminalRegularOpen
    let x'' : U := ⟨y, hyG⟩
    have e0 : metricScalarAt (I := ThreeModel) (s.metric.restrictOpen U) x'' =
        metricScalarAt (I := ThreeModel) s.metric y := by
      have : IsManifold ThreeModel 1 U := IsManifold.of_le (I := ThreeModel) (n := ∞) (by decide)
      exact metricScalarAt_restrictOpen (I := ThreeModel) s.metric U x''
    rw [Function.comp_apply, hΞx, hLm] at hlow0
    exact hlow0.trans_eq e0
  -- call N = max 2 K (same z, x', trace, witness)
  obtain ⟨Ξ', -, -, hΞx', -, -, -, -, -, -, -, -, -, -, -, -, h13⟩ :=
    hkK w le_rfl (by omega) (min_le_left _ _) (sliceHistoryR_O3 F s).toHistory j.succ
      (Fin.last _) hl s.time G L (sliceSlabR_initial_O3 F s) Jbig hJbig q (C₀ * q) a₀ hq
      (mul_pos hC₀ hq) le_rfl h1a hmetric Hp.parameters recsTot (ha₀h s).1 (ha₀h s).2
      (fun j' hj' _ b' => (hrecδ j' hj' b').trans (min_le_right _ _))
      (fun j' _ hjl => hslab j' hjl) hfin (hqT.trans hθ1) z x' B hA
  have hjet := h13 k (le_max_of_le_right hk) z hzr
  rw [hΞx', hLm] at hjet
  let U : TopologicalSpace.Opens s.stage.Carrier := G.terminalRegularOpen
  have e1 := curvDerivNormSq_restrictOpen_S53 (M := s.stage.Carrier) s.metric U k ⟨y, hyG⟩
  have hjet' : CheegerGromovCompactness.curvDerivNormSq k s.metric y ≤ q ^ (k + 2) * B_K :=
    e1.symm.le.trans hjet
  exact curvatureDerivativeNorm_le_of_capJets_S44 s.metric y k q ρ C0 B_K hq hρ hC0
    (by linarith only [hBK]) hjet' (capScale_le_of_scalar_S44 hlow hZ0)

end GC.LongTime.Ch12
