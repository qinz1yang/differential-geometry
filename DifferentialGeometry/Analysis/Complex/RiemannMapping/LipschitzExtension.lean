import DifferentialGeometry.Analysis.Complex.RiemannMapping.BoundaryGrowth
import DifferentialGeometry.Analysis.Complex.LogarithmicGradient
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.HarmonicGradient
import DifferentialGeometry.Topology.MetricSpace.FrontierBall
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

section

noncomputable section

open Set Filter Metric InnerProductSpace
open DifferentialGeometry.Analysis
open scoped Topology ContDiff

namespace Complex

theorem exists_deriv_bound_of_buffered_disk
    (W f : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hWsource : W.source = ball (0 : ℂ) r)
    (hW : ContDiffOn ℝ ∞ W W.source) (hWi : ContDiffOn ℝ ∞ W.symm W.target)
    (hfsource : f.source = W '' ball (0 : ℂ) 1)
    (hftarget : f.target = ball (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f f.source) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ f.source, ‖deriv f z‖ ≤ B := by
  let U := f.source
  let K := frontier U
  obtain ⟨hUopen, hcompact, hclosure, hfrontier, hKt, hKft, _⟩ :=
    buffered_disk_image_geometry W hr hWsource
  have hKcompact : IsCompact K := by
    apply hcompact.of_isClosed_subset isClosed_frontier
    rw [← hclosure]
    simpa only [K, U, hfsource] using (frontier_subset_closure (s := W '' ball (0 : ℂ) 1))
  have hKne : K.Nonempty := by
    rw [show K = frontier (W '' ball (0 : ℂ) 1) by simp only [K, U, hfsource], hfrontier]
    exact ⟨W 1, mem_image_of_mem W (by simp : (1 : ℂ) ∈ sphere (0 : ℂ) 1)⟩
  obtain ⟨ε, C, hε, hC, hgrowth⟩ := exists_log_norm_boundary_growth_of_buffered_disk
    W f hr hWsource hW hWi hfsource hftarget hf
  obtain ⟨δ, hδ, hnorm⟩ := exists_norm_gt_on_cthickening_frontier_of_unit_disk_homeomorph
    f hftarget hKcompact (show (1 / 2 : ℝ) < 1 by norm_num)
  let η := min ε δ / 2
  have hη : 0 < η := half_pos (lt_min hε hδ)
  have hηε : 2 * η ≤ ε := by dsimp only [η]; linarith [min_le_left ε δ]
  have hηδ : 2 * η ≤ δ := by dsimp only [η]; linarith [min_le_right ε δ]
  have hnear (z : ℂ) (hz : z ∈ U) (hzη : infDist z K < η) : ‖deriv f z‖ ≤ 32 * C := by
    let d := infDist z K
    have hzK : z ∉ K := by
      change z ∉ frontier f.source
      rw [f.open_source.frontier_eq]
      exact fun h => h.2 hz
    have hd : 0 < d := (isClosed_frontier.notMem_iff_infDist_pos hKne).mp hzK
    obtain ⟨p, hp, hdp⟩ := hKcompact.exists_infDist_eq_dist hKne z
    have hballU : ball z (d / 2) ⊆ U :=
      (ball_subset_ball (by linarith : d / 2 ≤ d)).trans
        (ball_infDist_frontier_subset_of_isOpen f.open_source hz hKne)
    have hynear (y : ℂ) (hy : y ∈ ball z (d / 2)) : dist y p < 2 * d := by
      have h := dist_triangle y z p
      change d = dist z p at hdp
      rw [← hdp] at h
      have hdist := mem_ball.mp hy
      linarith
    have hyδ (y : ℂ) (hy : y ∈ ball z (d / 2)) : y ∈ cthickening δ K := by
      apply mem_cthickening_of_dist_le y p δ K hp
      exact (hynear y hy).le.trans (by change 2 * d ≤ δ; linarith)
    have hne (y : ℂ) (hy : y ∈ ball z (d / 2)) : f y ≠ 0 :=
      norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans
        (hnorm y (hyδ y hy) (hballU hy)))
    have hu : HarmonicOnNhd (fun y => Real.log ‖f y‖) (ball z (d / 2)) := fun y hy =>
      (hf.analyticOnNhd f.open_source y (hballU hy)).harmonicAt_log_norm (hne y hy)
    have huBound : ∀ y ∈ ball z (d / 2), |Real.log ‖f y‖| ≤ 2 * C * d := by
      intro y hy
      have h := hgrowth p hp y ⟨hballU hy, mem_ball.mpr ((hynear y hy).trans_le (by linarith))⟩
      exact h.trans ((mul_le_mul_of_nonneg_left (hynear y hy).le hC).trans_eq (by ring))
    have hgrad := norm_gradient_le_of_harmonicOnNhd_ball (half_pos hd) hu huBound
    have hgrad' : ‖gradient (fun y => Real.log ‖f y‖) z‖ ≤ 32 * C := by
      convert hgrad using 1
      field_simp
      ring
    rw [norm_deriv_eq_norm_mul_norm_gradient_log_norm
      ((hf z hz).differentiableAt (f.open_source.mem_nhds hz))
      (hne z (mem_ball_self (half_pos hd)))]
    have hn : ‖f z‖ ≤ 1 := (mem_ball_zero_iff.mp (hftarget ▸ f.map_source hz)).le
    exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans (by simpa
      only [one_mul] using hgrad')
  let L := closure U ∩ {z : ℂ | η ≤ infDist z K}
  have hLcompact : IsCompact L := by
    have hclosed : IsClosed {z : ℂ | η ≤ infDist z K} :=
      isClosed_le continuous_const (continuous_infDist_pt K)
    apply hcompact.of_isClosed_subset (isClosed_closure.inter hclosed)
    intro z hz
    rw [← hclosure]
    simpa only [U, hfsource] using hz.1
  have hLU : L ⊆ U := by
    intro z hz
    by_contra hzu
    have hzK : z ∈ K := by
      change z ∈ frontier f.source
      rw [f.open_source.frontier_eq]
      exact ⟨hz.1, hzu⟩
    have hi : infDist z K = 0 := infDist_zero_of_mem hzK
    have hh : η ≤ infDist z K := hz.2
    rw [hi] at hh
    exact (not_le_of_gt hη) hh
  have hcont : ContinuousOn (deriv f) L :=
    (hf.analyticOnNhd f.open_source).deriv.continuousOn.mono hLU
  obtain ⟨B, hB⟩ := hLcompact.exists_bound_of_continuousOn hcont
  refine ⟨max (32 * C) B, (by positivity), ?_⟩
  intro z hz
  by_cases hn : infDist z K < η
  · exact (hnear z hz hn).trans (le_max_left _ _)
  · exact (hB z ⟨subset_closure hz, le_of_not_gt hn⟩).trans (le_max_right _ _)

end Complex

end

end

section

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace Complex

theorem exists_lipschitzOnWith_riemann_map_comp_of_buffered_disk
    (W f : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hWsource : W.source = ball (0 : ℂ) r)
    (hW : ContDiffOn ℝ ∞ W W.source) (hWi : ContDiffOn ℝ ∞ W.symm W.target)
    (hfsource : f.source = W '' ball (0 : ℂ) 1)
    (hftarget : f.target = ball (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f f.source) :
    ∃ C : ℝ≥0, LipschitzOnWith C (f ∘ W) (ball (0 : ℂ) 1) := by
  obtain ⟨B, hB, hfB⟩ := exists_deriv_bound_of_buffered_disk W f hr hWsource hW hWi
    hfsource hftarget hf
  have hball : closedBall (0 : ℂ) 1 ⊆ W.source := by
    rw [hWsource]
    exact closedBall_subset_ball hr
  have hcont : ContinuousOn (fderiv ℝ W) (closedBall (0 : ℂ) 1) :=
    (hW.continuousOn_fderiv_of_isOpen W.open_source (by simp)).mono hball
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont
  let C : ℝ≥0 := Real.toNNReal (B * max L 0)
  have hC : (C : ℝ) = B * max L 0 := Real.coe_toNNReal _ (by positivity)
  have hdiff (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : DifferentiableAt ℝ (f ∘ W) z := by
    have hzW : W z ∈ f.source := hfsource ▸ mem_image_of_mem W hz
    have hdW := (hW.contDiffAt (W.open_source.mem_nhds (hball
      (ball_subset_closedBall hz)))).differentiableAt (by simp)
    exact (((hf _ hzW).differentiableAt (f.open_source.mem_nhds hzW)).restrictScalars ℝ).comp z hdW
  refine ⟨C, (convex_ball (0 : ℂ) 1).lipschitzOnWith_of_nnnorm_fderiv_le hdiff ?_⟩
  intro z hz
  apply NNReal.coe_le_coe.mp
  rw [coe_nnnorm, hC]
  have hzW : W z ∈ f.source := hfsource ▸ mem_image_of_mem W hz
  have hdf := (hf _ hzW).differentiableAt (f.open_source.mem_nhds hzW)
  have hdW := (hW.contDiffAt (W.open_source.mem_nhds (hball
    (ball_subset_closedBall hz)))).differentiableAt (by simp)
  rw [fderiv_comp z (hdf.restrictScalars ℝ) hdW]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hreal : ‖fderiv ℝ f (W z)‖ = ‖deriv f (W z)‖ := by
    rw [hdf.hasDerivAt.complexToReal_fderiv.fderiv, norm_smul]
    simp
  rw [hreal]
  exact mul_le_mul (hfB _ hzW) ((hL z (ball_subset_closedBall hz)).trans (le_max_left _ _))
    (norm_nonneg _) hB

theorem exists_continuous_closed_unit_disk_extension
    {g : ℂ → ℂ} (hg : UniformContinuousOn g (ball (0 : ℂ) 1))
    (hmap : MapsTo g (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1)) :
    ∃ G : C(closedBall (0 : ℂ) 1, closedBall (0 : ℂ) 1),
      ∀ z (hz : z ∈ ball (0 : ℂ) 1),
        (G ⟨z, ball_subset_closedBall hz⟩ : ℂ) = g z := by
  let i : ball (0 : ℂ) 1 → closedBall (0 : ℂ) 1 := Set.inclusion ball_subset_closedBall
  have hi : Isometry i := fun _ _ => rfl
  have hd : DenseRange i := (denseRange_inclusion_iff ball_subset_closedBall).mpr (by
    rw [closure_ball (0 : ℂ) one_ne_zero])
  let g₀ : ball (0 : ℂ) 1 → ℂ := fun z => g z
  let G₀ := (hi.isUniformInducing.isDenseInducing hd).extend g₀
  have hGc : UniformContinuous G₀ :=
    uniformContinuous_uniformly_extend hi.isUniformInducing hd hg.restrict
  have heq (z : ball (0 : ℂ) 1) : G₀ (i z) = g z :=
    uniformly_extend_of_ind hi.isUniformInducing hd hg.restrict z
  have hGmap (z : closedBall (0 : ℂ) 1) : G₀ z ∈ closedBall (0 : ℂ) 1 := by
    refine hd.induction_on z (isClosed_closedBall.preimage hGc.continuous) ?_
    intro x
    rw [heq]
    exact hmap x.property
  refine ⟨⟨fun z => ⟨G₀ z, hGmap z⟩, hGc.continuous.subtype_mk _⟩, ?_⟩
  intro z hz
  exact heq ⟨z, hz⟩

theorem lipschitzWith_of_eq_on_open_unit_disk
    {g : ℂ → ℂ} {C : ℝ≥0} (hg : LipschitzOnWith C g (ball (0 : ℂ) 1))
    (G : C(closedBall (0 : ℂ) 1, closedBall (0 : ℂ) 1))
    (heq : ∀ z (hz : z ∈ ball (0 : ℂ) 1),
      (G ⟨z, ball_subset_closedBall hz⟩ : ℂ) = g z) : LipschitzWith C G := by
  let i : ball (0 : ℂ) 1 → closedBall (0 : ℂ) 1 := Set.inclusion ball_subset_closedBall
  have hd : DenseRange i := (denseRange_inclusion_iff ball_subset_closedBall).mpr (by
    rw [closure_ball (0 : ℂ) one_ne_zero])
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply hd.induction_on₂ (p := fun x y => dist (G x) (G y) ≤ (C : ℝ) * dist x y) ?_ ?_ x y
  · exact isClosed_le
      ((G.continuous.comp continuous_fst).dist (G.continuous.comp continuous_snd))
      (continuous_const.mul (continuous_fst.dist continuous_snd))
  · intro z w
    change dist (G (i z) : ℂ) (G (i w) : ℂ) ≤ (C : ℝ) * dist (z : ℂ) (w : ℂ)
    rw [heq z z.property, heq w w.property]
    exact hg.dist_le_mul z z.property w w.property

theorem exists_lipschitz_riemann_map_comp_extension_of_buffered_disk
    (W f : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hWsource : W.source = ball (0 : ℂ) r)
    (hW : ContDiffOn ℝ ∞ W W.source) (hWi : ContDiffOn ℝ ∞ W.symm W.target)
    (hfsource : f.source = W '' ball (0 : ℂ) 1)
    (hftarget : f.target = ball (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f f.source) :
    ∃ (C : ℝ≥0) (G : C(closedBall (0 : ℂ) 1, closedBall (0 : ℂ) 1)),
      LipschitzWith C G ∧ ∀ z (hz : z ∈ ball (0 : ℂ) 1),
        (G ⟨z, ball_subset_closedBall hz⟩ : ℂ) = f (W z) := by
  obtain ⟨C, hC⟩ := exists_lipschitzOnWith_riemann_map_comp_of_buffered_disk
    W f hr hWsource hW hWi hfsource hftarget hf
  obtain ⟨G, hG⟩ := exists_continuous_closed_unit_disk_extension hC.uniformContinuousOn (fun z hz =>
    ball_subset_closedBall (hftarget ▸ f.map_source (hfsource ▸ mem_image_of_mem W hz)))
  exact ⟨C, G, lipschitzWith_of_eq_on_open_unit_disk hC G hG, hG⟩

end Complex

end

end
