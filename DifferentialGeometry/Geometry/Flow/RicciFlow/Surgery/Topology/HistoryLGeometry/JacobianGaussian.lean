import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.JacobianComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.SeamBaseJacobian

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature (metricScalarAt)

universe u

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {T B v : ℝ}
  {p : (H.stage last).Carrier}

private theorem exists_lt_historyReducedJacobian_le_gaussian {hle : first ≤ last}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hv : 0 < v) {Z₀ : TangentSpace ThreeModel p} (hZ₀ : Z₀ ∈ H.historyMinDomain hle T B v p) :
    ∃ (k : Fin (H.eventCount + 1)) (hkl : k ≤ last) (v' : ℝ), 0 < v' ∧ v' ≤ v ∧
      T - v' ^ 2 ∈ H.stageDomain k ∧ ∀ hZ : Z₀ ∈ H.historyLExpDomain hkl T v' p,
        H.historyReducedJacobian hkl T v' p ⟨Z₀, hZ⟩ ≤
          (Real.pi ^ ((3 : ℝ) / 2))⁻¹ * Real.exp (-(H.stageMetric last T).inner p Z₀ Z₀) := by
  have hZd := historyMinDomain_subset_historyLExpDomain hZ₀
  have hTl := stageDomain_last_of_historyLExpDomain (⟨Z₀, hZd⟩ : H.historyLExpDomain hle T v p)
  rcases (H.time_le_of_mem_stageDomain hTl).eq_or_lt with heq | hlt
  · obtain ⟨k, hkl, δ, hδ, hδv, hG⟩ :=
      exists_pos_historyReducedJacobian_le_gaussian_of_time_eq heq hfloor hv hZ₀
    obtain ⟨hk, hle'⟩ := hG (δ / 2) ⟨half_pos hδ, half_lt_self hδ⟩
    exact ⟨k, hkl, δ / 2, half_pos hδ, (half_lt_self hδ).le.trans hδv, hk, hle'⟩
  · have hm : 0 < min v (Real.sqrt (T - H.time last)) :=
      lt_min hv (Real.sqrt_pos.2 (by linarith))
    set v₀ := min v (Real.sqrt (T - H.time last)) / 2 with hv₀def
    have hv₀ : 0 < v₀ := half_pos hm
    have hv₀m : v₀ < min v (Real.sqrt (T - H.time last)) := half_lt_self hm
    have hv₀v : v₀ ≤ v := (hv₀m.trans_le (min_le_left _ _)).le
    have hdom : ∀ w, 0 < w → w ≤ v₀ → T - w ^ 2 ∈ H.stageDomain last := by
      intro w hw hwv
      have h1 : w ^ 2 < T - H.time last :=
        (Real.lt_sqrt hw.le).1 (hwv.trans_lt (hv₀m.trans_le (min_le_right _ _)))
      exact H.mem_stageDomain_of_mem_Ioo ⟨by linarith, lt_of_lt_of_le (by linarith [pow_pos hw 2])
        (H.le_stageEndTime_of_mem_stageDomain hTl)⟩
    have hZ₀' : Z₀ ∈ H.historyMinDomain (le_refl last) T B v₀ p :=
      mem_historyMinDomain_of_le hfloor (le_refl last) hv₀ hv₀v (hdom v₀ hv₀ le_rfl) hZ₀
    obtain ⟨δ, hδ, hG⟩ := exists_pos_historyReducedJacobian_le_gaussian hlt hfloor hv₀ hZ₀'
    have hm' : 0 < min δ v₀ := lt_min hδ hv₀
    set v' := min δ v₀ / 2 with hv'def
    have hv' : 0 < v' := half_pos hm'
    have hv'm : v' < min δ v₀ := half_lt_self hm'
    have hv'δ : v' < δ := hv'm.trans_le (min_le_left _ _)
    have hv'v₀ : v' ≤ v₀ := (hv'm.trans_le (min_le_right _ _)).le
    exact ⟨last, le_rfl, v', hv', hv'v₀.trans hv₀v, hdom v' hv' hv'v₀,
      fun hZ => hG v' ⟨hv', hv'δ⟩ hZ⟩

theorem historyReducedJacobian_le_gaussian {hle : first ≤ last}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hv : 0 < v) (Z : H.historyLExpDomain hle T v p) (hZ : Z.1 ∈ H.historyMinDomain hle T B v p) :
    H.historyReducedJacobian hle T v p Z ≤
      (Real.pi ^ ((3 : ℝ) / 2))⁻¹ * Real.exp (-(H.stageMetric last T).inner p Z.1 Z.1) := by
  obtain ⟨k, hkl, v', hv', hv'v, hk, hG⟩ :=
    exists_lt_historyReducedJacobian_le_gaussian hfloor hv hZ
  have hfk : first ≤ k :=
    first_le_of_mem_stageDomain hv'.le hv'v (isHistoryLGeodesicOn_historyLCurve Z).1 hk
  exact (historyReducedJacobian_le_of_le hfloor hfk hkl hv' hv'v hk Z hZ).trans (hG _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
