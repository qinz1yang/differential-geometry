import DifferentialGeometry.Analysis.Schauder.Holder.Interpolation
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.MetricSpace.Cauchy

noncomputable section

open Set Filter
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.Schauder

private theorem derivative_uniform_cauchy_on_ball
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} {f : ι → E → F} {u : E → F} {C α : ℝ≥0}
    {center : E} {r R : ℝ} (hrR : r < R)
    (hα : 0 < α)
    (hf : ∀ i, ∀ x ∈ Metric.ball center R, DifferentiableAt ℝ (f i) x)
    (hD : ∀ i, HolderOnWith C α (fderiv ℝ (f i)) (Metric.ball center R))
    (hu : TendstoUniformlyOn f u l (Metric.ball center R)) :
    UniformCauchySeqOn (fun i => fderiv ℝ (f i)) l (Metric.ball center r) := by
  intro s hs
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_uniformity_dist.mp hs
  have hlim : Tendsto (fun δ : ℝ => (C + C : ℝ≥0) * δ ^ (α : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using tendsto_const_nhds.mul
      ((tendsto_id.mono_left nhdsWithin_le_nhds).rpow_const_nhds_zero
        (show 0 < (α : ℝ) from hα))
  have hbuffer : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < R - r :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const (sub_pos.mpr hrR)
  obtain ⟨δ, hδ, hδsmall, hδbuffer⟩ :=
    (eventually_mem_nhdsWithin.and
      ((hlim.eventually (gt_mem_nhds (half_pos hε))).and hbuffer)).exists
  change 0 < δ at hδ
  have hsmall := (Metric.tendstoUniformlyOn_iff.mp hu) (ε * δ / 16) (by positivity)
  filter_upwards [hsmall.prod_mk hsmall] with p hp
  intro x hx
  apply hεs
  have hsub : ∀ z ∈ Metric.ball center R, ‖(f p.1 - f p.2) z‖ ≤ ε * δ / 8 := by
    intro z hz
    have hh := dist_triangle (f p.1 z) (u z) (f p.2 z)
    have h1 := hp.1 z hz
    have h2 := hp.2 z hz
    rw [dist_comm] at h1
    change ‖f p.1 z - f p.2 z‖ ≤ _
    rw [← dist_eq_norm]
    linarith
  have hhold : HolderOnWith (C + C) α (fderiv ℝ (f p.1 - f p.2))
      (Metric.ball center R) := by
    have hh := holderWith_sub (hD p.1).holderWith (hD p.2).holderWith
    intro z hz w hw
    rw [fderiv_sub (hf p.1 z hz) (hf p.2 z hz),
      fderiv_sub (hf p.1 w hw) (hf p.2 w hw)]
    exact hh ⟨z, hz⟩ ⟨w, hw⟩
  have hxR : x ∈ Metric.ball center R :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hx).trans hrR)
  have hstep : ∀ v : E, ‖v‖ = 1 → x + δ • v ∈ Metric.ball center R := by
    intro v hv
    rw [Metric.mem_ball]
    calc
      dist (x + δ • v) center ≤ dist (x + δ • v) x + dist x center :=
        dist_triangle _ _ _
      _ = δ + dist x center := by
        congr 1
        rw [dist_eq_norm]
        simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.le,
          hv, mul_one]
      _ < δ + r := by linarith [Metric.mem_ball.mp hx]
      _ < R := by linarith
  have hest := norm_fderiv_le_at_scale_on
    (M := ⟨ε * δ / 8, by positivity⟩) (convex_ball center R)
    (fun z hz => (hf p.1 z hz).sub (hf p.2 z hz)) hhold hsub hδ hxR hstep
  rw [fderiv_sub (hf p.1 x hxR) (hf p.2 x hxR)] at hest
  rw [dist_eq_norm]
  have heq : 2 * (ε * δ / 8) / δ = ε / 4 := by
    field_simp [hδ.ne']
    ring
  change ‖fderiv ℝ (f p.1) x - fderiv ℝ (f p.2) x‖ ≤
    2 * (ε * δ / 8) / δ + (C + C : ℝ≥0) * δ ^ (α : ℝ) at hest
  rw [heq] at hest
  linarith

private theorem differentiable_and_derivative_convergence_on_ball
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {l : Filter ι} [NeBot l] {f : ι → E → F} {u : E → F} {C α : ℝ≥0}
    {center : E} {r R : ℝ} (hrR : r < R)
    (hα : 0 < α)
    (hf : ∀ i, ∀ x ∈ Metric.ball center R, DifferentiableAt ℝ (f i) x)
    (hD : ∀ i, HolderOnWith C α (fderiv ℝ (f i)) (Metric.ball center R))
    (hu : TendstoUniformlyOn f u l (Metric.ball center R)) :
    (∀ x ∈ Metric.ball center r, DifferentiableAt ℝ u x) ∧
      TendstoUniformlyOn (fun i => fderiv ℝ (f i)) (fderiv ℝ u) l
        (Metric.ball center r) := by
  have hc := derivative_uniform_cauchy_on_ball hrR hα hf hD hu
  let q : E → E →L[ℝ] F := fun x => limUnder l (fun i => fderiv ℝ (f i) x)
  have hq (x : E) (hx : x ∈ Metric.ball center r) :
      Tendsto (fun i => fderiv ℝ (f i) x) l (𝓝 (q x)) :=
    (hc.cauchy_map hx).le_nhds_lim
  have hconv := hc.tendstoUniformlyOn_of_tendsto hq
  have hinner : Metric.ball center r ⊆ Metric.ball center R := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_ball.mp hx).trans hrR)
  have hactual : ∀ x ∈ Metric.ball center r, HasFDerivAt u (q x) x := by
    intro x hx
    exact hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hconv
      (fun i y hy => (hf i y (hinner hy)).hasFDerivAt)
      (fun y hy => hu.tendsto_at (hinner hy)) hx
  exact ⟨fun x hx => (hactual x hx).differentiableAt,
    hconv.congr_right (fun x hx => (hactual x hx).fderiv.symm)⟩

theorem tendstoUniformlyOn_fderiv_ball_of_holderOnWith
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {l : Filter ι} [NeBot l] {f : ι → E → F} {u : E → F} {C α : ℝ≥0}
    {center : E} {r R : ℝ} (hrR : r < R)
    (hα : 0 < α)
    (hf : ∀ i, ∀ x ∈ Metric.ball center R, DifferentiableAt ℝ (f i) x)
    (hD : ∀ i, HolderOnWith C α (fderiv ℝ (f i)) (Metric.ball center R))
    (hu : TendstoUniformlyOn f u l (Metric.ball center R)) :
    TendstoUniformlyOn (fun i => fderiv ℝ (f i)) (fderiv ℝ u) l
      (Metric.ball center r) :=
  (differentiable_and_derivative_convergence_on_ball hrR hα hf hD hu).2

theorem differentiableOn_ball_of_tendstoUniformlyOn_of_holder_fderiv
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {l : Filter ι} [NeBot l] {f : ι → E → F} {u : E → F} {C α : ℝ≥0}
    {center : E} {R : ℝ} (hα : 0 < α)
    (hf : ∀ i, ∀ x ∈ Metric.ball center R, DifferentiableAt ℝ (f i) x)
    (hD : ∀ i, HolderOnWith C α (fderiv ℝ (f i)) (Metric.ball center R))
    (hu : TendstoUniformlyOn f u l (Metric.ball center R)) :
    DifferentiableOn ℝ u (Metric.ball center R) := by
  intro x hx
  let r := (dist x center + R) / 2
  have hrR : r < R := by
    dsimp only [r]
    linarith [Metric.mem_ball.mp hx]
  have hxr : x ∈ Metric.ball center r := by
    rw [Metric.mem_ball]
    dsimp only [r]
    linarith [Metric.mem_ball.mp hx]
  exact ((differentiable_and_derivative_convergence_on_ball hrR hα hf hD hu).1
    x hxr).differentiableWithinAt

end DifferentialGeometry.Analysis.Schauder
