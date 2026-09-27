import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitWitnesses

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace ObservedHistory

theorem abs_derivWithin_scalar_le_of_survivor_maps_of_lt (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) {R θ t₀ q qD C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hqD : q ≤ R * qD) {W : TopologicalSpace.Opens (H.stageAt t).Carrier}
    {h : ℝ → SmoothRiemannianMetric ThreeModel W}
    (a : Icc (0 : ℝ) H.horizon) (ha : (a : ℝ) = t - θ / R)
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W →
      (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hp : ∀ s ∈ Icc (-θ) 0, ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
      (t : ℝ) + s / R ∈ H.stageDomain j.val →
        h s = scaleMetric R hR
          (localPullMetric (H.stageMetric j.val ((t : ℝ) + s / R)) (f j) (hf j)))
    (hstage : ∀ v : Icc (0 : ℝ) H.horizon, (v : ℝ) < t₀ → H.time (H.activeStage v) < v →
      ∀ p : (H.stageAt v).Carrier, q < metricScalarAt (H.stageMetric (H.activeStage v) v) p →
        |derivWithin (fun v' => metricScalarAt (H.stageMetric (H.activeStage v) v') p)
          (Iic (v : ℝ)) v| ≤ C * metricScalarAt (H.stageMetric (H.activeStage v) v) p ^ 2)
    {s : ℝ} (hs : s ∈ Ioc (-θ) 0) (hst₀ : (t : ℝ) + s / R < t₀)
    (hreg : ∀ hv : (t : ℝ) + s / R ∈ Icc (0 : ℝ) H.horizon,
      H.time (H.activeStage ⟨_, hv⟩) < (t : ℝ) + s / R)
    (z : W) (hz : qD < metricScalarAt (h s) z) :
    |derivWithin (fun s' => metricScalarAt (h s') z) (Iic s) s| ≤
      C * metricScalarAt (h s) z ^ 2 := by
  have hvI : (t : ℝ) + s / R ∈ Icc (a : ℝ) t := by
    have h1 : -θ / R ≤ s / R := div_le_div_of_nonneg_right hs.1.le hR.le
    have h2 : s / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hR.le
    rw [neg_div] at h1
    constructor <;> linarith
  let v : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) + s / R, a.2.1.trans hvI.1, hvI.2.trans t.2.2⟩
  have hav : a ≤ v := hvI.1
  have hvt : v ≤ t := hvI.2
  have hreg' := hreg v.2
  let j : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩
  have hlow : H.time (H.activeStage v) - t < s / R := by
    change H.time (H.activeStage v) < (t : ℝ) + s / R at hreg'
    linarith
  have hlowR : (H.time (H.activeStage v) - t) * R < s := by
    rwa [lt_div_iff₀ hR] at hlow
  have hev : ∀ᶠ s' in 𝓝[Iic s] s, h s' = scaleMetric R hR
      (localPullMetric (H.stageMetric j.val ((t : ℝ) + s' / R)) (f j) (hf j)) := by
    filter_upwards [Ioc_mem_nhdsLE (max_lt hs.1 hlowR)] with s' hs'
    have h1 : -θ < s' := (le_max_left _ _).trans_lt hs'.1
    have h2 : (H.time (H.activeStage v) - t) * R < s' := (le_max_right _ _).trans_lt hs'.1
    refine hp s' ⟨h1.le, hs'.2.trans hs.2⟩ j
      (H.mem_stageDomain_activeStage_of_le v ?_ ?_)
    · have : H.time (H.activeStage v) - t < s' / R := by rwa [lt_div_iff₀ hR]
      linarith
    · change (t : ℝ) + s' / R ≤ (t : ℝ) + s / R
      have := div_le_div_of_nonneg_right hs'.2 hR.le
      linarith
  have hs0 := hp s ⟨hs.1.le, hs.2⟩ j (H.activeStage_mem v)
  have hRz : metricScalarAt (h s) z =
      R⁻¹ * metricScalarAt (H.stageMetric j.val ((t : ℝ) + s / R)) (f j z) := by
    rw [hs0, metricScalarAt_scaleMetric, metricScalarAt_localPull]
  have hqz : q < metricScalarAt (H.stageMetric (H.activeStage v) v) (f j z) := by
    have h1 : R * qD < R * metricScalarAt (h s) z := mul_lt_mul_of_pos_left hz hR
    rw [hRz, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] at h1
    exact hqD.trans_lt h1
  exact abs_derivWithin_scalar_le_of_scaleMetric_localPullMetric (hf j) hR hC hev hs0 z
    (hstage v hst₀ hreg' (f j z) hqz)

end ObservedHistory

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀)

theorem abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt {Ctime : NNReal}
    {qcan t₀ : ℝ} {t : Icc (0 : ℝ) H.toHistory.horizon} (ht₀ : t₀ ≤ t)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t₀)
    (v : Icc (0 : ℝ) H.toHistory.horizon) (hvt : (v : ℝ) < t₀)
    (hv : H.toHistory.time (H.toHistory.activeStage v) < v)
    (p : (H.toHistory.stageAt v).Carrier)
    (hq : qcan < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p) :
    |derivWithin (fun v' => metricScalarAt
        (H.toHistory.stageMetric (H.toHistory.activeStage v) v') p) (Iic (v : ℝ)) v| ≤
      Ctime * metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p ^ 2 := by
  have hmono : H.toHistory.activeStage v ≤ H.toHistory.activeStage t :=
    H.toHistory.activeStage_mono (show (v : ℝ) ≤ t from (hvt.trans_le ht₀).le)
  have hmem := H.toHistory.activeStage_mem v
  change (H.toHistory.stage (H.toHistory.activeStage v)).Carrier at p
  generalize H.toHistory.activeStage v = k at hmono hv hmem p hq ⊢
  cases k using Fin.lastCases with
  | last =>
    have hlt : H.time (Fin.last H.eventCount) < H.horizon := hv.trans_le v.2.2
    have hkt : H.toHistory.activeStage t = Fin.last H.eventCount :=
      le_antisymm (Fin.le_last _) hmono
    have hval : ∀ v' : ℝ, metricScalarAt (H.toHistory.stageMetric (Fin.last H.eventCount) v') p =
        ((H.finalSlab hlt).restrictIncoming le_rfl hlt le_rfl).flow.scalar v' p := by
      intro v'
      rw [ObservedHistory.stageMetric_last_of_lt (h := hlt)]
      rfl
    simp only [hval] at hq ⊢
    exact hfinal hlt hkt p v ⟨hv, hvt⟩ hq
  | cast i =>
    have hnext : (v : ℝ) < H.time i.succ := by
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at hmem
      exact hmem.2
    have hval : ∀ v' : ℝ, metricScalarAt (H.toHistory.stageMetric i.castSucc v') p =
        (H.toHistory.event i).incoming.flow.scalar v' p := by
      intro v'
      rw [ObservedHistory.stageMetric_castSucc_apply]
      rfl
    simp only [hval] at hq ⊢
    rcases hmono.lt_or_eq with hlt | heq
    · exact hslabs i hlt p v ⟨hv, hnext⟩ hq
    · exact hcurrent i heq p v ⟨hv, hvt⟩ hq

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
