import DifferentialGeometry.Geometry.Metric.EuclideanCone
import DifferentialGeometry.Geometry.Metric.ConeDirectionControl

set_option autoImplicit false

open Set Filter Topology
open scoped NNReal

namespace Metric.EuclideanCone

instance completeSpace {Y : Type*} [MetricSpace Y] [CompleteSpace Y] :
    CompleteSpace (Metric.EuclideanCone Y) := by
  classical
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hrC : CauchySeq (fun n => radius (u n)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    exact (abs_radius_sub_le_dist _ _).trans_lt (hN m hm n hn)
  obtain ⟨r, hrlim⟩ := cauchySeq_tendsto_of_complete hrC
  have hr : 0 ≤ r := le_of_tendsto_of_tendsto tendsto_const_nhds hrlim
    (Eventually.of_forall (fun n => radius_nonneg (u n)))
  rcases eq_or_lt_of_le hr with hzero | hpos
  · refine ⟨tip, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
    simpa only [dist_tip, ← hzero] using hrlim
  · have hrad : ∀ᶠ n in atTop, r / 2 ≤ radius (u n) :=
      (hrlim.eventually (lt_mem_nhds (half_lt_self hpos))).mono (fun _ hn => hn.le)
    obtain ⟨n, hn⟩ := hrad.exists
    have hY : Nonempty Y := by
      cases he : u n with
      | none =>
        have hz : radius (u n) = 0 := by rw [he]; rfl
        rw [hz] at hn
        linarith
      | some x => exact ⟨x.2⟩
    let d : ℕ → Y := fun n => match u n with
      | none => Classical.choice hY
      | some x => x.2
    let rs : ℕ → ℝ≥0 := fun n => ⟨radius (u n), radius_nonneg (u n)⟩
    have hrepr (n : ℕ) : mk (rs n) (d n) = u n := by
      cases he : u n with
      | none =>
        have hz : rs n = 0 := by apply Subtype.ext; change radius (u n) = 0; rw [he]; rfl
        rw [hz, mk_zero]
        rfl
      | some x =>
        dsimp only [rs, d]
        rw [he]
        exact mk_pos (r := (⟨x.1, x.1.property.le⟩ : ℝ≥0)) x.1.property x.2
    have hdcone (m n : ℕ) :
        coneDistance (radius (u m), d m) (radius (u n), d n) = dist (u m) (u n) := by
      have h := (dist_mk (rs m) (rs n) (d m) (d n)).symm
      rw [hrepr m, hrepr n] at h
      exact h
    have hdC : CauchySeq d := by
      apply cauchySeq_directions_of_coneDistance_cauchy (half_pos hpos) hrad
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
      exact ⟨N, fun m hm n hn => by rw [hdcone]; exact hN m hm n hn⟩
    obtain ⟨v, hvlim⟩ := cauchySeq_tendsto_of_complete hdC
    refine ⟨mk (⟨r, hr⟩ : ℝ≥0) v, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
    have hpairs : Tendsto (fun n => ((radius (u n), d n), (r, v))) atTop
        (𝓝 ((r, v), (r, v))) :=
      (hrlim.prodMk_nhds hvlim).prodMk_nhds tendsto_const_nhds
    have hdist := continuous_coneDistance.continuousAt.tendsto.comp hpairs
    have heq : (fun n => dist (u n) (mk (⟨r, hr⟩ : ℝ≥0) v)) =
        (fun n => coneDistance (radius (u n), d n) (r, v)) := by
      funext n
      have h := dist_mk (rs n) (⟨r, hr⟩ : ℝ≥0) (d n) v
      rw [hrepr n] at h
      exact h
    rw [heq]
    simpa only [Function.comp_def, coneDistance_self] using hdist

end Metric.EuclideanCone
