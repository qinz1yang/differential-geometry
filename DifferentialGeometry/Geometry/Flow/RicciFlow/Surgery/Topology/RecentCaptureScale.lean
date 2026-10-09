import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingRoom

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

theorem exists_recent_cap_capture_scale_of_isEmpty_backwardPointTrace
    (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    {Ctime : ℝ≥0} {qcan M : ℝ} {u t : Icc (0 : ℝ) H.toHistory.horizon}
    (hut : u ≤ t)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hy : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) y))
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 0 < M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2) :
    ∃ (j : Fin H.eventCount) (_ : H.toHistory.activeStage u ≤ j.castSucc)
      (hl : j.succ ≤ H.toHistory.activeStage t)
      (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall)
      (x : standardCapWindow p.modelRadius),
      (∀ p' : (H.toHistory.stage j.castSucc).Carrier,
        ¬ (H.toHistory.event j).RegularCrossing p' (A.point j.succ le_rfl hl)) ∧
      A.point j.succ le_rfl hl =
        ((records j).static b).inclusion (((records j).static b).witness.cap z) ∧
      ‖x.val‖ ≤ StandardCap.transitionEnd ∧
      A.point j.succ le_rfl hl = ((records j).static b).window x ∧
      H.time j.succ ∈ Ioc (u : ℝ) (t : ℝ) ∧
      ((records j).static b).neck.scale ≤ 4 * M := by
  obtain ⟨j, hf, hl, A, b, z, x, hno, hz, hxn, hx⟩ :=
    H.toHistory.exists_cap_capture records hcan (H.toHistory.activeStage_mono hut) y hy
  have hju : (u : ℝ) < H.time j.succ := by
    by_contra hle
    have h := H.toHistory.le_activeStage u j.succ (not_lt.mp hle)
    exact absurd (h.trans hf) (not_le_of_gt (Fin.castSucc_lt_succ (i := j)))
  have hjt : H.time j.succ ≤ t :=
    (H.time_strictMono.monotone hl).trans (H.toHistory.activeStage_time_le t)
  have hnext (i : Fin H.eventCount) (hi : H.toHistory.activeStage t = i.castSucc) :
      (t : ℝ) < H.time i.succ := by
    have hval : (H.toHistory.activeStage t).val < H.toHistory.eventCount := by
      rw [hi]
      exact i.isLt
    have h := H.toHistory.activeStage_before_next t hval
    have he : (⟨(H.toHistory.activeStage t).val + 1, Nat.succ_lt_succ hval⟩ :
        Fin (H.toHistory.eventCount + 1)) = i.succ := by
      ext
      simp [hi]
    rw [he] at h
    exact h
  have hrec := A.inv_max_stageMetric_scalar_sub_le_of_derivativeBoundBefore hM hqcan
    (H.toHistory.activeStage_time_le t) hnext
    t.2.2 hslabs hcurrent hfinal j.succ le_rfl hl le_rfl
    (fun i hi => hi ▸ H.time_strictMono (Fin.castSucc_lt_succ (i := i))) hjt
  rw [max_eq_left hscalar, H.toHistory.stageMetric_initial, ← H.toHistory.event_output j, hz,
    ← ((records j).static b).scalar_eq] at hrec
  set S := ((records j).static b).neck.scale with hSdef
  have hlow := hscale j b z
  set R := metricScalarAt ((records j).static b).witness.metric
    (((records j).static b).witness.cap z) with hRdef
  have hgap : M⁻¹ - (max M R)⁻¹ ≤ Ctime * ((t : ℝ) - H.time j.succ) := by
    have := (abs_le.mp hrec).1
    linarith
  have hC : 0 ≤ (Ctime : ℝ) := Ctime.coe_nonneg
  have htu : (t : ℝ) - H.time j.succ ≤ (t : ℝ) - u := by linarith
  have hnn : 0 ≤ (t : ℝ) - H.time j.succ := by linarith
  have hCt : (Ctime : ℝ) * ((t : ℝ) - H.time j.succ) ≤ (2 * M)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hmax : max M R ≤ 2 * M := by
    have hinv : (2 * M)⁻¹ ≤ (max M R)⁻¹ := by
      have htwo : M⁻¹ = 2 * (2 * M)⁻¹ := by field_simp
      linarith
    exact (inv_le_inv₀ (by positivity) (hM.trans_le (le_max_left M R))).mp hinv
  have hS : S ≤ 4 * M := by linarith [le_max_right M R]
  exact ⟨j, hf, hl, A, b, z, x, hno, hz, hxn, hx, ⟨hju, hjt⟩, hS⟩

theorem isParabolicallyRmControlledBall_of_recent_cap_scale_separation
    (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    {Ctime : ℝ≥0} {qcan M r : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hr : 0 < r)
    (hu : (u : ℝ) = t - r ^ 2)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 1 ≤ 4 * M) (hqcan : qcan ≤ M)
    (hspace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        y r,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ 4 * M)
    (htime : Ctime * (4 * M) * r ^ 2 ≤ 1 / 2)
    (hrM : r ^ 4 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * M)) ^ 2 ≤ 1)
    (hlarge : ∀ j : Fin H.eventCount,
      H.time j.succ ∈ Ioc (u : ℝ) (t : ℝ) →
      ∀ b : (H.toHistory.event j).RetainedBoundaryIndex,
        16 * M < ((records j).static b).neck.scale) :
    H.toHistory.isParabolicallyRmControlledBall t y r := by
  have hMpos : 0 < M := by linarith
  have hqfour : qcan ≤ 4 * M := hqcan.trans (by linarith)
  have htime' : Ctime * (4 * M) * ((t : ℝ) - u) ≤ 1 / 2 := by
    rw [hu, sub_sub_cancel]
    exact htime
  have htrace : ∀ x ∈ riemannianBallOf
      (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r,
      Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) x) := by
    intro x hx
    by_contra h
    obtain ⟨j, _, _, _, b, _, _, _, _, _, _, hbirth, hcaptured⟩ :=
      H.exists_recent_cap_capture_scale_of_isEmpty_backwardPointTrace records hcan hscale
        hut x (not_nonempty_iff.mp h) hslabs hcurrent hfinal
        (by positivity : 0 < 4 * M) hqfour (hspace x hx) htime'
    have hsmall : ((records j).static b).neck.scale ≤ 16 * M := by
      nlinarith [hcaptured]
    exact (not_le_of_gt (hlarge j hbirth b)) hsmall
  exact H.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace
    hphi hpinch hut hr hu hlast y hslabs hcurrent hfinal hM hqfour hspace htime hrM htrace

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
