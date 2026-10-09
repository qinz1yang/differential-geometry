import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortion

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private ObservedHistory.activeStage_eq_of_time_mem
  ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc
  ObservedHistory.backwardSurvivorInitialMetric_inner_le_exp
  BackwardPointTrace.apply_point_eq_of_stage_eq
  RetainedCoreHistory.exists_window_point_of_edist_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortion

namespace ObservedHistory

variable (K : ObservedHistory.{u})

private theorem initialMetric_inner_le_exp_of_normSq_le_of_eq_last {k : Fin (K.eventCount + 1)}
    (hk : k = Fin.last K.eventCount) (h : K.time (Fin.last K.eventCount) < K.horizon)
    (x : (K.stage k).Carrier) {t C : ℝ} (htk : K.time k ≤ t) (htb : t ≤ K.horizon)
    (hbound : ∀ r ∈ Icc (K.time k) t,
      normSq0S (K.stageMetric k r) x 4 (metricRm04At (K.stageMetric k r) x) ≤ C)
    (w : TangentSpace ThreeModel x) :
    (K.initialMetric k).inner x w w ≤
      Real.exp (18 * Real.sqrt C * (t - K.time k)) * (K.stageMetric k t).inner x w w := by
  subst hk
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [← K.stageMetric_initial]
  simp only [ObservedHistory.stageMetric_last_of_lt (h := h)] at hbound ⊢
  have hc := (metric_inner_exp_bounds_of_curvature_bound (K.finalSlab h).flow
    (K.finalSlab h).equation (a := K.time (Fin.last K.eventCount)) (b := t)
    (fun r hr => ⟨hr.1, hr.2.trans htb⟩) (fun r hr => ⟨hr.1, hr.2.trans_le htb⟩) x hbound
    (s := K.time (Fin.last K.eventCount)) (t := t) ⟨le_rfl, htk⟩ ⟨htk, le_rfl⟩ w).2
  rw [hdim, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htk)] at hc
  convert hc using 3
  push_cast
  ring

theorem activeStage_eq_last_of_time_last_le (t : Icc (0 : ℝ) K.horizon)
    (ht : K.time (Fin.last K.eventCount) ≤ t) : K.activeStage t = Fin.last K.eventCount :=
  le_antisymm (Fin.le_last _) (K.le_activeStage t _ ht)

end ObservedHistory

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

private theorem normSq_stageMetric_le_of_backwardPointTrace_of_final
    {Ctime : ℝ≥0} {qcan M : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) p)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u ≤ v) (hvt : v ≤ t) :
    normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
          (H.toHistory.activeStage_mono hvt)) 4
        (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt))) ≤
      (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by
  have hC : 0 ≤ 4 * Real.sqrt 3 * (1 + phi 1 + phi 0) := by
    have := hphi.pos 0
    have := hphi.pos 1
    positivity
  have hscal := H.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds hut A hslabs
    hcurrent hfinal (by linarith) hqcan hscalar htime v huv hvt
  have hs := H.sqrt_rmNormSq_stageMetric_le_of_pinched hphi hpinch v
    (fun h => hlast (le_antisymm (Fin.le_last _) (h ▸ H.toHistory.activeStage_mono hvt)))
    (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
      (H.toHistory.activeStage_mono hvt))
  have hmax : max (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
      (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
        (H.toHistory.activeStage_mono hvt))) 1 ≤ 2 * M := max_le hscal (by linarith)
  have h1 := hs.trans (mul_le_mul_of_nonneg_left hmax hC)
  have hN := normSq0S_nonneg (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
    (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
      (H.toHistory.activeStage_mono hvt)) 4
    (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
      (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
        (H.toHistory.activeStage_mono hvt)))
  rw [← Real.sq_sqrt hN]
  calc _ ≤ (4 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (2 * M)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    _ = (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by ring

private theorem exists_cap_capture_of_ball_point_without_trace_of_comparison
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M r Dcap Dstar : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (hcmp : ∀ (q : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (C : ℝ),
      (∀ s ∈ Icc (H.toHistory.time (H.toHistory.activeStage t)) (t : ℝ),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q) ≤ C) →
      ∀ w : TangentSpace ThreeModel q,
        (H.toHistory.initialMetric (H.toHistory.activeStage t)).inner q w w ≤
          Real.exp (18 * Real.sqrt C * ((t : ℝ) - H.toHistory.time (H.toHistory.activeStage t))) *
            (H.toHistory.stageMetric (H.toHistory.activeStage t) t).inner q w w)
    (y z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r)
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcur : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        y r,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * r < Dcap) :
    ∃ (j : Fin H.eventCount) (hl : j.succ ≤ H.toHistory.activeStage t)
      (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (zs : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
      (Az : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl zs)
      (x xc : standardCapWindow p.modelRadius),
      zs ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r ∧
      (∀ p' : (H.toHistory.stage j.castSucc).Carrier,
        ¬ (H.toHistory.event j).RegularCrossing p' (Az.point j.succ le_rfl hl)) ∧
      Az.point j.succ le_rfl hl = ((records j).static b).window xc ∧
      ‖xc.val‖ ≤ StandardCap.transitionEnd ∧
      A.point j.succ le_rfl hl = ((records j).static b).window x ∧ ‖x.val‖ < Dcap ∧
      riemannianEDistOf (H.toHistory.initialMetric j.succ) (((records j).static b).window xc)
          (A.point j.succ le_rfl hl) ≤
        ENNReal.ofReal
          (Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * r) ∧
      ((records j).static b).neck.scale ≤ 4 * M ∧
      ((records j).static b).neck.scale * ((t : ℝ) - H.time j.succ) ≤
        4 * M * ((t : ℝ) - u) := by
  classical
  let good : Fin H.eventCount → Prop := fun j =>
    H.toHistory.activeStage u ≤ j.castSucc ∧ ∃ (hl : j.succ ≤ H.toHistory.activeStage t)
      (w : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier),
      w ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r ∧
      ∃ A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl w,
        ∀ p' : (H.toHistory.stage j.castSucc).Carrier,
          ¬ (H.toHistory.event j).RegularCrossing p' (A.point j.succ le_rfl hl)
  obtain ⟨j₀, hf₀, hl₀, A₀, hno₀⟩ :=
    H.toHistory.exists_latest_event_without_regularCrossing _ z hzt
  let S := Finset.univ.filter good
  have hSne : S.Nonempty :=
    ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf₀, hl₀, z, hz, A₀, hno₀⟩⟩
  obtain ⟨j, hjS, hjmax⟩ : ∃ j ∈ S, ∀ j' ∈ S, j' ≤ j :=
    ⟨S.max' hSne, S.max'_mem hSne, fun j' h => S.le_max' j' h⟩
  obtain ⟨-, hfj, hlj, zs, hzs, As, hnos⟩ := Finset.mem_filter.mp hjS
  have htr : ∀ w ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r,
      Nonempty (BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hlj w) := by
    intro w hw
    by_contra hn
    obtain ⟨j', hf', hl', A', hno'⟩ :=
      H.toHistory.exists_latest_event_without_regularCrossing hlj w (not_nonempty_iff.mp hn)
    have hmem : j' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hfj.trans ((Fin.castSucc_lt_succ (i := j)).le.trans hf'), hl', w, hw, A', hno'⟩
    have h1 : j'.val ≤ j.val := hjmax j' hmem
    have h2 : j.val + 1 ≤ j'.val := hf'
    omega
  have hr : 0 < r := by
    have h : riemannianEDistOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y z <
        ENNReal.ofReal r := hz
    exact ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le h)
  have hyB :
      y ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r := by
    change riemannianEDistOf _ y y < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  let u' : Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨H.toHistory.time j.succ, H.toHistory.time_nonneg _, H.toHistory.time_le_horizon_at _⟩
  have hau' : H.toHistory.activeStage u' = j.succ := H.toHistory.activeStage_at_time j.succ
  have hu'u : u ≤ u' := by
    change (u : ℝ) ≤ H.toHistory.time j.succ
    by_contra hle
    have h := H.toHistory.le_activeStage u j.succ (not_le.mp hle).le
    exact absurd (h.trans hfj) (not_le_of_gt (Fin.castSucc_lt_succ (i := j)))
  have hu't : u' ≤ t := by
    change H.toHistory.time j.succ ≤ (t : ℝ)
    exact (H.toHistory.time_strictMono.monotone hlj).trans (H.toHistory.activeStage_time_le t)
  have htime' : Ctime * M * ((t : ℝ) - u') ≤ 1 / 2 := by
    have hu : (u : ℝ) ≤ u' := hu'u
    have hC : 0 ≤ (Ctime : ℝ) * M := mul_nonneg Ctime.coe_nonneg (by linarith)
    nlinarith
  have hRm : ∀ q ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r,
      ∀ Aq : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hlj q,
      ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvt : v ≤ t),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            ((Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)).point
              (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
              (H.toHistory.activeStage_mono hvt)) 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            ((Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)).point
              (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
              (H.toHistory.activeStage_mono hvt))) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := fun q hq Aq v huv hvt =>
    H.normSq_stageMetric_le_of_backwardPointTrace_of_final hphi hpinch hu't hlast
      (Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)) hslabs hcur
      hfinal hM hqcan (hspace q hq) htime' v huv hvt
  obtain ⟨b, zc, hzc⟩ := (records j).exists_cap_of_not_regularCrossing_target hnos
  obtain ⟨-, -, -, -, -, -, -, hcap⟩ := hcan j b
  obtain ⟨xz, hxzn, hxz⟩ := hcap zc
  have hspos : 0 < ((records j).static b).neck.scale := ((records j).static b).neck.scale_pos
  have hsM : ((records j).static b).neck.scale ≤ 4 * M := by
    have hb := H.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds hu't
      (As.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)) hslabs hcur
      hfinal (by linarith) hqcan (hspace zs hzs) htime' u' le_rfl hu't
    have heq := BackwardPointTrace.apply_point_eq_of_stage_eq As
      (fun m q => metricScalarAt (H.toHistory.stageMetric m (H.toHistory.time j.succ)) q)
      hau' ((le_of_eq hau'.symm).trans (H.toHistory.activeStage_mono (le_refl u')))
      (H.toHistory.activeStage_mono hu't) le_rfl hlj
    have h2 : metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap zc) ≤ 2 * M := by
      rw [((records j).static b).scalar_eq, ← hzc, H.toHistory.event_output j,
        ← H.toHistory.stageMetric_initial]
      exact heq.symm.le.trans hb
    linarith [hscale j b zc]
  have hage : ((records j).static b).neck.scale * ((t : ℝ) - H.time j.succ) ≤
      4 * M * ((t : ℝ) - u) := by
    have hu : (u : ℝ) ≤ H.time j.succ := hu'u
    have hT : H.time j.succ ≤ (t : ℝ) := hu't
    nlinarith [mul_le_mul_of_nonneg_left hsM (sub_nonneg.mpr hT)]
  have hΛ0 : 0 ≤ 8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M := by
    have := hphi.pos 0
    have := hphi.pos 1
    have : 0 ≤ M := by linarith
    positivity
  have hlocal : ∀ q : H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj,
      q.val ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r →
      ∀ v : TangentSpace ThreeModel q,
        (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
          le_rfl hlj).inner q v v ≤
        Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
          ((t : ℝ) - H.toHistory.time j.succ)) *
          ((H.toHistory.stageMetric (H.toHistory.activeStage t) t).restrictOpen
            (H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj)).inner
            q v v := by
    intro q hq v
    have hb1 : ∀ v : Icc (0 : ℝ) H.toHistory.horizon, H.toHistory.time j.succ ≤ v →
        (v : ℝ) ≤ H.toHistory.time (H.toHistory.activeStage t) →
        ∀ (hf : j.succ ≤ H.toHistory.activeStage v)
          (hl : H.toHistory.activeStage v ≤ H.toHistory.activeStage t),
          normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
              ((Classical.choice q.property).point (H.toHistory.activeStage v) hf hl) 4
            (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
              ((Classical.choice q.property).point (H.toHistory.activeStage v) hf hl)) ≤
            (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := fun v hv1 hv2 _ _ =>
      hRm q.val hq (Classical.choice q.property) v hv1
        (hv2.trans (H.toHistory.activeStage_time_le t))
    have hb2 : ∀ s ∈ Icc (H.toHistory.time (H.toHistory.activeStage t)) (t : ℝ),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q.val 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q.val) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by
      intro s hs
      let v : Icc (0 : ℝ) H.toHistory.horizon :=
        ⟨s, (H.toHistory.time_nonneg _).trans hs.1, hs.2.trans t.2.2⟩
      have hav : H.toHistory.activeStage v = H.toHistory.activeStage t :=
        ObservedHistory.activeStage_eq_of_time_mem H.toHistory v _ hs.1 (fun i' h =>
          hs.2.trans_lt
            (ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc H.toHistory t i' h))
      have huv : u' ≤ v := by
        change H.toHistory.time j.succ ≤ s
        exact (H.toHistory.time_strictMono.monotone hlj).trans hs.1
      have hb := hRm q.val hq (Classical.choice q.property) v huv hs.2
      have heq := BackwardPointTrace.apply_point_eq_of_stage_eq
        ((Classical.choice q.property).restrictFirst (le_of_eq hau'.symm)
          (H.toHistory.activeStage_mono hu't))
        (fun m x => normSq0S (H.toHistory.stageMetric m s) x 4
          (metricRm04At (H.toHistory.stageMetric m s) x))
        hav (H.toHistory.activeStage_mono huv) (H.toHistory.activeStage_mono hs.2)
        (H.toHistory.activeStage_mono hu't) le_rfl
      rw [BackwardPointTrace.endpoint_eq] at heq
      exact heq.symm.le.trans hb
    have h1 := ObservedHistory.backwardSurvivorInitialMetric_inner_le_exp H.toHistory hlj q hb1 v
    have h2 := hcmp q.val _ hb2 v
    rw [Real.sqrt_sq hΛ0] at h1 h2
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    calc _ ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hyz : riemannianEDistOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y zs <
      ENNReal.ofReal r := hzs
  let y' : H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj :=
    ⟨y, htr y hyB⟩
  let z' : H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj :=
    ⟨zs, htr zs hzs⟩
  have hyzU := Geometry.Metric.riemannianEDistOf_restrictOpen_lt_of_riemannianBallOf_subset
    (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
    (H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj) y' z'
    (fun w hw => htr w hw) hyz
  have hsub := riemannianBallOf_subset_of_inner_le_mul
    ((H.toHistory.stageMetric (H.toHistory.activeStage t) t).restrictOpen
      (H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj))
    (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
      le_rfl hlj) y' (r := r) (Real.exp_pos _) (fun q hq v => hlocal q (by
        have h1 : riemannianEDistOf
            ((H.toHistory.stageMetric (H.toHistory.activeStage t) t).restrictOpen
              (H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj)) y' q <
            ENNReal.ofReal r := hq
        exact lt_of_le_of_lt (riemannianEDistOf_le_restrictOpen _ _ y' q) h1) v)
  have hz'' := hsub hyzU
  have hmap := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
    (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
      le_rfl hlj)
    (H.toHistory.initialMetric j.succ)
    (H.toHistory.backwardSurvivorMap j.succ (H.toHistory.activeStage t) hlj j.succ le_rfl hlj)
    (H.toHistory.backwardSurvivorMap_isLocalDiffeomorph _ _ hlj j.succ le_rfl hlj) one_pos
    (fun x v => by
      rw [one_mul, ObservedHistory.backwardSurvivorInitialMetric, localPullMetric_inner])
    y' z'
  have hΦz : H.toHistory.backwardSurvivorMap j.succ (H.toHistory.activeStage t) hlj j.succ le_rfl
      hlj z' = As.point j.succ le_rfl hlj :=
    H.toHistory.backwardSurvivorMap_eq_point _ _ hlj j.succ le_rfl hlj z' As
  have hexp : Real.sqrt (Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - H.toHistory.time j.succ))) =
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
        ((t : ℝ) - H.toHistory.time j.succ)) := by
    rw [show 18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
        ((t : ℝ) - H.toHistory.time j.succ) =
        9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - H.toHistory.time j.succ) +
        9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - H.toHistory.time j.succ)
        by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  set dd := Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - H.toHistory.time j.succ)) * r with hdd
  have hnear : riemannianEDistOf (H.toHistory.initialMetric j.succ)
      (((records j).static b).window xz)
      ((Classical.choice (htr y hyB)).point j.succ le_rfl hlj) ≤ ENNReal.ofReal dd := by
    rw [hxz, ← hzc, ← hΦz, riemannianEDistOf_comm]
    have h3 : riemannianEDistOf (H.toHistory.backwardSurvivorInitialMetric j.succ
        (H.toHistory.activeStage t) hlj j.succ le_rfl hlj) y' z' <
        ENNReal.ofReal (Real.sqrt (Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
          ((t : ℝ) - H.toHistory.time j.succ))) * r) := hz''
    rw [hexp] at h3
    refine hmap.trans ?_
    rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul]
    exact h3.le
  have hwin' : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      (Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * r) <
        Dcap := by
    rw [← mul_assoc]
    exact hwin
  have hdd' : dd ≤ Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - u)) * r := by
    have hu : (u : ℝ) ≤ H.toHistory.time j.succ := hu'u
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hr.le
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  obtain ⟨x, hxn', hxeq⟩ := RetainedCoreHistory.exists_window_point_of_edist_le H records hcan
    hacc j b hsM hDstar hDmodel xz hxzn _ (hnear.trans (ENNReal.ofReal_le_ofReal hdd'))
    (mul_nonneg (Real.exp_pos _).le hr.le) hwin'
  have hzxc : As.point j.succ le_rfl hlj = ((records j).static b).window xz := hzc.trans hxz.symm
  exact ⟨j, hlj, Classical.choice (htr y hyB), b, zs, As, x, xz, hzs, hnos, hzxc, hxzn,
    hxeq.symm, hxn', hnear.trans (ENNReal.ofReal_le_ofReal hdd'), hsM, hage⟩

theorem exists_cap_capture_of_ball_point_without_trace_of_activeStage_eq_last
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M r Dcap Dstar : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hfinalPinch : Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
      (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (y z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r)
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hfinal : ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime
      qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        y r,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * r < Dcap) :
    ∃ (j : Fin H.eventCount) (hl : j.succ ≤ H.toHistory.activeStage t)
      (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (zs : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
      (Az : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl zs)
      (x xc : standardCapWindow p.modelRadius),
      zs ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r ∧
      (∀ p' : (H.toHistory.stage j.castSucc).Carrier,
        ¬ (H.toHistory.event j).RegularCrossing p' (Az.point j.succ le_rfl hl)) ∧
      Az.point j.succ le_rfl hl = ((records j).static b).window xc ∧
      ‖xc.val‖ ≤ StandardCap.transitionEnd ∧
      A.point j.succ le_rfl hl = ((records j).static b).window x ∧ ‖x.val‖ < Dcap ∧
      riemannianEDistOf (H.toHistory.initialMetric j.succ) (((records j).static b).window xc)
          (A.point j.succ le_rfl hl) ≤
        ENNReal.ofReal
          (Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * r) ∧
      ((records j).static b).neck.scale ≤ 4 * M ∧
      ((records j).static b).neck.scale * ((t : ℝ) - H.time j.succ) ≤
        4 * M * ((t : ℝ) - u) :=
  H.exists_cap_capture_of_ball_point_without_trace_of_comparison records hcan hscale hacc hphi
    hpinch hut (fun _ => ⟨h, hfinalPinch⟩)
    (fun q _ hb w => H.toHistory.initialMetric_inner_le_exp_of_normSq_le_of_eq_last hlastA h q
      (H.toHistory.activeStage_time_le t) t.2.2 hb w)
    y z hz hzt hslabs (fun j hj => absurd (hj.trans hlastA) (Fin.castSucc_ne_last j))
    (fun _ _ => hfinal) hM hqcan hspace htime hDstar hDmodel hwin

theorem capWindowPoint_of_ball_point_without_trace_of_activeStage_eq_last
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M r Dcap Dstar θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hfinalPinch : Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
      (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (y z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r)
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hfinal : ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime
      qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        y r,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 4 * M * ((t : ℝ) - u) ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * r < Dcap) :
    H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap := by
  obtain ⟨j, hl, A, b, -, -, x, -, -, -, -, -, hx, hxn, -, -, hage⟩ :=
    H.exists_cap_capture_of_ball_point_without_trace_of_activeStage_eq_last records hcan hscale
      hacc hphi hpinch hut h hlastA hfinalPinch y z hz hzt hslabs hfinal hM hqcan hspace htime
      hDstar hDmodel hwin
  refine ⟨j, hl, A, b, x, hx, by linarith, ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ ((records j).static b).neck.scale_pos]
  linarith

private theorem scalar_le_four_mul_max_on_ball_of_gradient_bound_of_activeStage_eq_last
    (t : Icc (0 : ℝ) H.toHistory.horizon) (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    {Cgrad : ℝ≥0} {qcan r : ℝ}
    (hgrad : ∀ w, qcan < (H.finalSlab h).flow.scalar t w →
      ∀ v : TangentSpace I3 w,
        |Perelman.CanonicalNeighborhood.scalarDifferential (H.finalSlab h).flow t w v| ≤
          Cgrad * (H.finalSlab h).flow.scalar t w *
            Real.sqrt ((H.finalSlab h).flow.scalar t w) *
            Real.sqrt (((H.finalSlab h).flow.base.metric t).inner w v v))
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hy : 0 < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
    (hr : (Cgrad : ℝ) * r *
      Real.sqrt (max (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
        qcan) ≤ 1 / 4) :
    ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤
        4 * max (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
          qcan := by
  revert y
  rw [hlastA]
  intro y hy hr x hx
  rw [ObservedHistory.stageMetric_last_of_lt (h := h)] at hy hr hx ⊢
  have hx' : x ∈ riemannianClosedBallOf ((H.finalSlab h).flow.base.metric t) y r :=
    le_of_lt (α := ENNReal) hx
  have : IsManifold I3 1 (H.stage (Fin.last H.eventCount)).Carrier :=
    IsManifold.of_le (n := ∞) (by decide)
  exact Perelman.CanonicalNeighborhood.scalar_le_four_mul_max_of_gradient_bound
    (H.finalSlab h).flow hgrad hy hr hx'

theorem exists_parabolicallyRmControlledBall_or_capWindowPoint_of_activeStage_eq_last
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime Cgrad : ℝ≥0} {qcan c Dcap θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hfinalPinch : Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
      (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hqR : qcan ≤ metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
    (hR : 1 ≤ 4 * metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
    (hc : 0 < c) (hcgrad : (Cgrad : ℝ) * c ≤ 1 / 4) (hctime : 8 * Ctime * c ^ 2 ≤ 1)
    (hcpinch : 3072 * (1 + phi 1 + phi 0) ^ 2 * c ^ 4 ≤ 1)
    {u : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hu : (u : ℝ) = t - c ^ 2 /
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hfinal : ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime
      qcan t)
    (hgrad : ∀ w, qcan < (H.finalSlab h).flow.scalar t w →
      ∀ v : TangentSpace I3 w,
        |Perelman.CanonicalNeighborhood.scalarDifferential (H.finalSlab h).flow t w v| ≤
          Cgrad * (H.finalSlab h).flow.scalar t w *
            Real.sqrt ((H.finalSlab h).flow.scalar t w) *
            Real.sqrt (((H.finalSlab h).flow.base.metric t).inner w v v))
    {Dstar : ℝ} (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 16 * c ^ 2 ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd +
      Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) < Dcap) :
    H.toHistory.isParabolicallyRmControlledBall t y
        (c / Real.sqrt
          (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)) ∨
      H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap := by
  by_cases hcw : H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap
  · exact Or.inr hcw
  refine Or.inl ?_
  set R := metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y with hRdef
  have hRpos : 0 < R := by linarith
  have hsq : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRpos
  have hsqsq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hRpos.le
  have hmax : max R qcan = R := max_eq_left hqR
  have hC : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
  have htu : (t : ℝ) - u = c ^ 2 / R := by rw [hu]; ring
  have hr2 : (c / Real.sqrt R) ^ 2 = c ^ 2 / R := by rw [div_pow, hsqsq]
  have hr4 : (c / Real.sqrt R) ^ 4 = c ^ 4 / R ^ 2 := by
    rw [show (c / Real.sqrt R) ^ 4 = ((c / Real.sqrt R) ^ 2) ^ 2 by ring, hr2, div_pow]
    ring
  have hspace : ∀ w ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
      y (c / Real.sqrt R),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) w ≤ 4 * R := by
    intro w hw
    have hs := H.scalar_le_four_mul_max_on_ball_of_gradient_bound_of_activeStage_eq_last t h
      hlastA hgrad y hRpos
      (by rw [← hRdef, hmax, mul_assoc, div_mul_cancel₀ c hsq.ne']; exact hcgrad) w hw
    rwa [← hRdef, hmax] at hs
  have hcur : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t := fun j hj =>
    absurd (hj.trans hlastA) (Fin.castSucc_ne_last j)
  apply H.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace hphi hpinch
    (M := 4 * R) hut (by positivity) (by rw [hu, hr2]) (fun _ => ⟨h, hfinalPinch⟩) y hslabs
    hcur (fun _ _ => hfinal) hR (by linarith [le_max_right R qcan]) hspace
  · rw [hr2]
    field_simp
    nlinarith
  · rw [hr4]
    have hK : (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * R)) ^ 2 =
        3072 * (1 + phi 1 + phi 0) ^ 2 * R ^ 2 := by
      have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      ring_nf
      rw [h3]
      ring
    rw [hK]
    field_simp
    nlinarith
  intro x hx
  by_contra hn
  apply hcw
  apply H.capWindowPoint_of_ball_point_without_trace_of_activeStage_eq_last records hcan hscale
    hacc hphi hpinch hut h hlastA hfinalPinch y x hx (not_nonempty_iff.mp hn) hslabs hfinal hR
    (by linarith) hspace (hDstar := hDstar) (hDmodel := hDmodel)
  · rw [htu]
    field_simp
    nlinarith
  · rw [htu]
    field_simp
    nlinarith
  · have h32 : Real.sqrt (8 * (4 * R)) = Real.sqrt 32 * Real.sqrt R := by
      rw [show 8 * (4 * R) = 32 * R by ring, Real.sqrt_mul (by norm_num)]
    have harg : 9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * R)) * ((t : ℝ) - u) =
        288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2 := by
      rw [htu]
      field_simp
      ring
    rw [h32, harg]
    have he : Real.sqrt 32 * Real.sqrt R *
        Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) * (c / Real.sqrt R) =
        Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) := by
      field_simp
    rw [he]
    exact hwin

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
