import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Piecewise
import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk

section

noncomputable section

open Set Filter Metric
open scoped Topology

namespace Complex

theorem tendsto_norm_at_frontier_of_unit_disk_homeomorph
    (e : OpenPartialHomeomorph ℂ ℂ) (htarget : e.target = ball (0 : ℂ) 1)
    {p : ℂ} (hp : p ∈ frontier e.source) :
    Tendsto (fun z => ‖e z‖) (𝓝[e.source] p) (𝓝 (1 : ℝ)) := by
  have hps : p ∉ e.source := by
    rw [e.open_source.frontier_eq] at hp
    exact hp.2
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hsub : closedBall (0 : ℂ) a ⊆ e.target := by
      rw [htarget]
      exact closedBall_subset_ball ha
    have hK : IsCompact (e.symm '' closedBall (0 : ℂ) a) :=
      (isCompact_closedBall (0 : ℂ) a).image_of_continuousOn
        (e.continuousOn_invFun.mono hsub)
    have hpK : p ∉ e.symm '' closedBall (0 : ℂ) a := by
      rintro ⟨w, hw, hpw⟩
      exact hps (hpw ▸ e.map_target (hsub hw))
    have hnear : (e.symm '' closedBall (0 : ℂ) a)ᶜ ∈ 𝓝 p :=
      hK.isClosed.isOpen_compl.mem_nhds hpK
    filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with z hz hzs
    apply lt_of_not_ge
    intro hza
    have hez : e z ∈ closedBall (0 : ℂ) a := by
      simpa only [mem_closedBall, dist_zero_right] using hza
    exact hz ⟨e z, hez, e.left_inv hzs⟩
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hez := e.map_source hz
    rw [htarget] at hez
    exact (mem_ball_zero_iff.mp hez).trans ha

theorem tendsto_log_norm_at_frontier_of_unit_disk_homeomorph
    (e : OpenPartialHomeomorph ℂ ℂ) (htarget : e.target = ball (0 : ℂ) 1)
    {p : ℂ} (hp : p ∈ frontier e.source) :
    Tendsto (fun z => Real.log ‖e z‖) (𝓝[e.source] p) (𝓝 (0 : ℝ)) := by
  simpa only [Function.comp_def, Real.log_one] using
    (Real.continuousAt_log one_ne_zero).tendsto.comp
      (tendsto_norm_at_frontier_of_unit_disk_homeomorph e htarget hp)

open scoped Classical in
theorem continuousAt_piecewise_log_norm_of_unit_disk_homeomorph
    (e : OpenPartialHomeomorph ℂ ℂ) (htarget : e.target = ball (0 : ℂ) 1)
    {p : ℂ} (hp : p ∈ frontier e.source) :
    ContinuousAt (e.source.piecewise (fun z => Real.log ‖e z‖) (fun _ => 0)) p := by
  classical
  have hps : p ∉ e.source := by
    rw [e.open_source.frontier_eq] at hp
    exact hp.2
  have ht := (tendsto_log_norm_at_frontier_of_unit_disk_homeomorph e htarget hp).piecewise
    (s := e.source)
    (tendsto_const_nhds : Tendsto (fun _ : ℂ => (0 : ℝ)) (𝓝 p ⊓ 𝓟 e.sourceᶜ) (𝓝 0))
  simpa only [ContinuousAt, Set.piecewise, ite_eq_right hps] using ht

end Complex

end

end

section

noncomputable section

open Set Filter Metric
open DifferentialGeometry.Geometry
open scoped Topology

namespace Complex

theorem norm_extension_eq_one_on_sphere
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball (0 : ℂ) 1) (het : e.target = ball (0 : ℂ) 1)
    (G : C(closedBall (0 : ℂ) 1, closedBall (0 : ℂ) 1))
    (hG : ∀ z (hz : z ∈ ball (0 : ℂ) 1),
      (G ⟨z, ball_subset_closedBall hz⟩ : ℂ) = e z)
    {p : ℂ} (hp : p ∈ sphere (0 : ℂ) 1) :
    ‖(G ⟨p, sphere_subset_closedBall hp⟩ : ℂ)‖ = 1 := by
  let v : ℂ → ℂ := fun z => (G (diskRetraction z) : ℂ)
  have hvc : Continuous v := continuous_subtype_val.comp
    (G.continuous.comp diskRetraction_lipschitz.continuous)
  have hpcl : p ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact sphere_subset_closedBall hp
  let _ : (𝓝[ball (0 : ℂ) 1] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hpcl
  have hlim : Tendsto (fun z => ‖e z‖) (𝓝[ball (0 : ℂ) 1] p) (𝓝 1) := by
    have hpf : p ∈ frontier e.source := by rw [hes, frontier_ball (0 : ℂ) one_ne_zero]; exact hp
    simpa only [hes] using tendsto_norm_at_frontier_of_unit_disk_homeomorph e het hpf
  have heq : (fun z => ‖e z‖) =ᶠ[𝓝[ball (0 : ℂ) 1] p] fun z => ‖v z‖ := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [show v z = (G ⟨z, ball_subset_closedBall hz⟩ : ℂ) by
      dsimp only [v]; rw [diskRetraction_coe ⟨z, ball_subset_closedBall hz⟩], hG z hz]
  have hlimv := hlim.congr' heq
  have hnorm : ‖v p‖ = 1 := tendsto_nhds_unique
    (hvc.norm.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlimv
  simpa only [v, diskRetraction_coe ⟨p, sphere_subset_closedBall hp⟩] using hnorm

end Complex

end

end
