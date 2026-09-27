import DifferentialGeometry.Analysis.Calculus.Inverse.Univalent
import DifferentialGeometry.Analysis.Complex.RiemannMapping.Onto
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.OpenPartialHomeomorph.Composition

section

noncomputable section
open Set Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

theorem exists_smooth_univalent_disk_image
    {R r : ℝ} (hR : 0 < R) (hr : R < r) {W : ℂ → ℂ} (hW : ContDiffOn ℝ ∞ W (Metric.ball (0 : ℂ) r))
    (hi : InjOn W (Metric.ball (0 : ℂ) r))
    (hd : ∀ z ∈ Metric.ball (0 : ℂ) r, (fderiv ℝ W z).toLinearMap.det ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      e.source = Metric.ball (0 : ℂ) R ∧ e.target = W '' Metric.ball (0 : ℂ) R ∧
      (e : ℂ → ℂ) = W ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      Bornology.IsBounded e.target ∧ IsSimplyConnected e.target ∧ e.target ≠ univ := by
  have hsub : Metric.ball (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) r := Metric.ball_subset_ball hr.le
  obtain ⟨e, hes, het, heW, he, hei⟩ := exists_smooth_openPartialHomeomorph_of_injOn_det_ne_zero
    Metric.isOpen_ball (hW.mono hsub) (hi.mono hsub) (fun z hz => hd z (hsub hz))
  have hclsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) r :=
    Metric.closedBall_subset_ball hr
  have hbounded : Bornology.IsBounded e.target := by
    rw [het]
    exact ((isCompact_closedBall (0 : ℂ) R).image_of_continuousOn
      (hW.continuousOn.mono hclsub)).isBounded.subset (image_mono Metric.ball_subset_closedBall)
  have hsc : IsSimplyConnected e.target := by
    let : ContractibleSpace e.source := by
      rw [hes]
      exact (convex_ball (0 : ℂ) R).contractibleSpace ⟨0, Metric.mem_ball_self hR⟩
    let : SimplyConnectedSpace e.source := inferInstance
    exact e.toHomeomorphSourceTarget.toHomotopyEquiv.symm.simplyConnectedSpace
  have hproper : e.target ≠ univ := by
    intro h
    obtain ⟨C, hC, hbound⟩ := hbounded.exists_pos_norm_le
    have hh := hbound ((C + 1 : ℝ) : ℂ) (h.symm ▸ mem_univ _)
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ C + 1)] at hh
    linarith
  exact ⟨e, hes, het, heW, he, hei, hbounded, hsc, hproper⟩

theorem exists_riemann_map_on_univalent_disk_image
    {r : ℝ} (hr : 1 < r) {W : ℂ → ℂ} (hW : ContDiffOn ℝ ∞ W (Metric.ball (0 : ℂ) r))
    (hi : InjOn W (Metric.ball (0 : ℂ) r))
    (hd : ∀ z ∈ Metric.ball (0 : ℂ) r, (fderiv ℝ W z).toLinearMap.det ≠ 0) :
    ∃ (e f : OpenPartialHomeomorph ℂ ℂ),
      e.source = Metric.ball (0 : ℂ) 1 ∧ e.target = W '' Metric.ball (0 : ℂ) 1 ∧
      (e : ℂ → ℂ) = W ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      f.source = e.target ∧ f.target = Metric.ball (0 : ℂ) 1 ∧ f (W 0) = 0 ∧
      DifferentiableOn ℂ f e.target ∧ DifferentiableOn ℂ f.symm (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ e.target, deriv f z ≠ 0) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, deriv f.symm z ≠ 0 := by
  obtain ⟨e, hes, het, heW, he, hei, _, hsc, hproper⟩ :=
    exists_smooth_univalent_disk_image zero_lt_one hr hW hi hd
  have hp : W 0 ∈ e.target := by
    rw [het]
    exact mem_image_of_mem W (Metric.mem_ball_self zero_lt_one)
  obtain ⟨f, hfs, hft, hfp, hf, hfi, hfd, hfid⟩ :=
    Complex.riemann_mapping e.open_target hsc hproper hp
  exact ⟨e, f, hes, het, heW, he, hei, hfs, hft, hfp, hf, hfi, hfd, hfid⟩


theorem exists_buffered_univalent_disk_riemann_map
    {r : ℝ} (hr : 1 < r) {W : ℂ → ℂ} (hW : ContDiffOn ℝ ∞ W (Metric.ball (0 : ℂ) r))
    (hi : InjOn W (Metric.ball (0 : ℂ) r))
    (hd : ∀ z ∈ Metric.ball (0 : ℂ) r, (fderiv ℝ W z).toLinearMap.det ≠ 0) :
    ∃ (e f : OpenPartialHomeomorph ℂ ℂ),
      e.source = Metric.ball (0 : ℂ) r ∧ e.target = W '' Metric.ball (0 : ℂ) r ∧
      (e : ℂ → ℂ) = W ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      f.source = W '' Metric.ball (0 : ℂ) 1 ∧ f.target = Metric.ball (0 : ℂ) 1 ∧ f (W 0) = 0 ∧
      DifferentiableOn ℂ f (W '' Metric.ball (0 : ℂ) 1) ∧
      DifferentiableOn ℂ f.symm (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ W '' Metric.ball (0 : ℂ) 1, deriv f z ≠ 0) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, deriv f.symm z ≠ 0 := by
  obtain ⟨e, hes, het, heW, he, hei⟩ :=
    exists_smooth_openPartialHomeomorph_of_injOn_det_ne_zero Metric.isOpen_ball hW hi hd
  obtain ⟨e₁, f, _, hU, _, _, _, hfs, hft, hf0, hf, hfi, hfd, hfid⟩ :=
    exists_riemann_map_on_univalent_disk_image hr hW hi hd
  rw [hU] at hfs hf hfd
  exact ⟨e, f, hes, het, heW, he, hei, hfs, hft, hf0, hf, hfi, hfd, hfid⟩

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

theorem exists_normalized_smooth_disk_coordinate
    {r : ℝ} (hr : 1 < r) {W : ℂ → ℂ} (hW : ContDiffOn ℝ ∞ W (Metric.ball (0 : ℂ) r))
    (hi : InjOn W (Metric.ball (0 : ℂ) r))
    (hd : ∀ z ∈ Metric.ball (0 : ℂ) r, (fderiv ℝ W z).toLinearMap.det ≠ 0) :
    ∃ (e f ψ : OpenPartialHomeomorph ℂ ℂ),
      e.source = Metric.ball (0 : ℂ) r ∧ e.target = W '' Metric.ball (0 : ℂ) r ∧
      (e : ℂ → ℂ) = W ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      f.source = W '' Metric.ball (0 : ℂ) 1 ∧ f.target = Metric.ball (0 : ℂ) 1 ∧ f (W 0) = 0 ∧
      DifferentiableOn ℂ f f.source ∧ DifferentiableOn ℂ f.symm f.target ∧
      (∀ z ∈ f.source, deriv f z ≠ 0) ∧
      ψ.source = Metric.ball (0 : ℂ) 1 ∧ ψ.target = Metric.ball (0 : ℂ) 1 ∧
      ψ 0 = 0 ∧ ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      (∀ z, ψ z = f (W z)) ∧ ∀ z, ψ.symm z = e.symm (f.symm z) := by
  obtain ⟨e, f, hes, het, heW, he, hei, hfs, hft, hf0, hf, hfi, hfd, _⟩ :=
    exists_buffered_univalent_disk_riemann_map hr hW hi hd
  let e₁ := e.restrOpen (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball
  have he₁s : e₁.source = Metric.ball (0 : ℂ) 1 := by
    change e.source ∩ Metric.ball (0 : ℂ) 1 = _
    rw [hes, inter_eq_right.mpr (Metric.ball_subset_ball hr.le)]
  have he₁t : e₁.target = W '' Metric.ball (0 : ℂ) 1 := by
    rw [← e₁.image_source_eq_target, he₁s]
    exact congrArg (fun k : ℂ → ℂ => k '' Metric.ball (0 : ℂ) 1) heW
  let ψ := e₁.trans' f (he₁t.trans hfs.symm)
  have hψs : ψ.source = Metric.ball (0 : ℂ) 1 := he₁s
  have hψt : ψ.target = Metric.ball (0 : ℂ) 1 := hft
  have hfR : ContDiffOn ℝ ∞ f f.source :=
    (hf.contDiffOn (hfs ▸ f.open_source)).restrict_scalars ℝ |>.mono (by rw [hfs])
  have hfiR : ContDiffOn ℝ ∞ f.symm f.target :=
    (hfi.contDiffOn Metric.isOpen_ball).restrict_scalars ℝ |>.mono (by rw [hft])
  have he₁ : ContDiffOn ℝ ∞ e₁ e₁.source := he.mono (fun z hz => hz.1)
  have he₁i : ContDiffOn ℝ ∞ e₁.symm e₁.target := hei.mono (fun z hz => hz.1)
  have hψ : ContDiffOn ℝ ∞ ψ ψ.source :=
    hfR.comp he₁ (fun z hz => (he₁t.trans hfs.symm) ▸ e₁.map_source hz)
  have hψi : ContDiffOn ℝ ∞ ψ.symm ψ.target :=
    he₁i.comp hfiR (fun z hz => (hfs.trans he₁t.symm) ▸ f.map_target hz)
  have hψ0 : ψ 0 = 0 := by change f (e 0) = 0; rw [heW]; exact hf0
  exact ⟨e, f, ψ, hes, het, heW, he, hei, hfs, hft, hf0,
    hfs.symm ▸ hf, hft.symm ▸ hfi, hfs.symm ▸ hfd, hψs, hψt, hψ0, hψ, hψi,
    fun z => by change f (e z) = _; rw [heW], fun _ => rfl⟩

end DifferentialGeometry.Analysis

end

end
