import DifferentialGeometry.Analysis.Schauder.Holder.Interpolation
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.MetricSpace.Cauchy

noncomputable section
open Set Filter
open scoped Topology NNReal
namespace DifferentialGeometry.Analysis.Schauder

private theorem derivative_uniform_cauchy
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} {f : ι → E → F} {u : E → F} {C α : ℝ≥0}
    (hα : 0 < α) (hf : ∀ i, Differentiable ℝ (f i))
    (hD : ∀ i, HolderWith C α (fderiv ℝ (f i)))
    (hu : TendstoUniformly f u l) :
    UniformCauchySeqOn (fun i => fderiv ℝ (f i)) l univ := by
  intro s hs
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_uniformity_dist.mp hs
  have hlim : Tendsto (fun δ : ℝ => (C + C : ℝ≥0) * δ ^ (α : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using tendsto_const_nhds.mul
      ((tendsto_id.mono_left nhdsWithin_le_nhds).rpow_const_nhds_zero
        (show 0 < (α : ℝ) from hα))
  obtain ⟨δ, hδ, hδsmall⟩ := (eventually_mem_nhdsWithin.and
    (hlim.eventually (gt_mem_nhds (half_pos hε)))).exists
  change 0 < δ at hδ
  have hsmall := (Metric.tendstoUniformly_iff.mp hu) (ε * δ / 16) (by positivity)
  filter_upwards [hsmall.prod_mk hsmall] with p hp
  intro x _
  apply hεs
  change dist (fderiv ℝ (f p.1) x) (fderiv ℝ (f p.2) x) < ε
  have hsub : ∀ z, ‖(f p.1 - f p.2) z‖ ≤ ε * δ / 8 := by
    intro z
    have hh := dist_triangle (f p.1 z) (u z) (f p.2 z)
    have h1 := hp.1 z
    have h2 := hp.2 z
    rw [dist_comm] at h1
    change ‖f p.1 z - f p.2 z‖ ≤ _
    rw [← dist_eq_norm]
    linarith
  have hder : fderiv ℝ (f p.1 - f p.2) =
      fderiv ℝ (f p.1) - fderiv ℝ (f p.2) := by
    funext z
    exact fderiv_sub (hf p.1 z) (hf p.2 z)
  have hhold : HolderWith (C + C) α (fderiv ℝ (f p.1 - f p.2)) := by
    rw [hder]
    exact holderWith_sub (hD p.1) (hD p.2)
  have hest := norm_fderiv_le_at_scale (M := ⟨ε * δ / 8, by positivity⟩)
    ((hf p.1).sub (hf p.2)) hhold hsub hδ x
  rw [hder] at hest
  simp only [Pi.sub_apply] at hest
  rw [dist_eq_norm]
  have heq : 2 * (ε * δ / 8) / δ = ε / 4 := by field_simp [hδ.ne']; ring
  change ‖fderiv ℝ (f p.1) x - fderiv ℝ (f p.2) x‖ ≤
    2 * (ε * δ / 8) / δ + (C + C : ℝ≥0) * δ ^ (α : ℝ) at hest
  rw [heq] at hest
  linarith

private theorem differentiable_holder_of_tendstoUniformly
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {l : Filter ι} [NeBot l] {f : ι → E → F} {u : E → F} {C α : ℝ≥0}
    (hα : 0 < α) (hf : ∀ i, Differentiable ℝ (f i))
    (hD : ∀ i, HolderWith C α (fderiv ℝ (f i)))
    (hu : TendstoUniformly f u l) :
    Differentiable ℝ u ∧ HolderWith C α (fderiv ℝ u) ∧
      TendstoUniformly (fun i => fderiv ℝ (f i)) (fderiv ℝ u) l := by
  have hc := derivative_uniform_cauchy hα hf hD hu
  have hpt : ∀ x : E, ∃ v : E →L[ℝ] F,
      Tendsto (fun i => fderiv ℝ (f i) x) l (𝓝 v) :=
    fun x => cauchy_map_iff_exists_tendsto.mp (hc.cauchy_map (mem_univ x))
  choose v hv using hpt
  have hun : TendstoUniformly (fun i => fderiv ℝ (f i)) v l := by
    rw [← tendstoUniformlyOn_univ]
    exact hc.tendstoUniformlyOn_of_tendsto (fun x _ => hv x)
  have hd (x : E) : HasFDerivAt u (v x) x :=
    hasFDerivAt_of_tendstoUniformly hun (fun i x => (hf i x).hasFDerivAt) (fun x => hu.tendsto_at x) x
  have he : fderiv ℝ u = v := funext (fun x => (hd x).fderiv)
  refine ⟨fun x => (hd x).differentiableAt, ?_, ?_⟩
  · rw [he, ← holderOnWith_univ]
    exact holderOnWith_of_tendsto (Eventually.of_forall fun i => (hD i).holderOnWith univ)
      (fun x _ => hv x)
  · rwa [he]

theorem differentiable_of_tendstoUniformly_of_holder_fderiv
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {l : Filter ι} [NeBot l] {f : ι → E → F} {u : E → F} {C α : ℝ≥0}
    (hα : 0 < α) (hf : ∀ i, Differentiable ℝ (f i))
    (hD : ∀ i, HolderWith C α (fderiv ℝ (f i)))
    (hu : TendstoUniformly f u l) :
    Differentiable ℝ u :=
  (differentiable_holder_of_tendstoUniformly hα hf hD hu).1

theorem holder_fderiv_of_tendstoUniformly
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {l : Filter ι} [NeBot l] {f : ι → E → F} {u : E → F} {C α : ℝ≥0}
    (hα : 0 < α) (hf : ∀ i, Differentiable ℝ (f i))
    (hD : ∀ i, HolderWith C α (fderiv ℝ (f i)))
    (hu : TendstoUniformly f u l) :
    HolderWith C α (fderiv ℝ u) :=
  (differentiable_holder_of_tendstoUniformly hα hf hD hu).2.1

theorem tendstoUniformly_fderiv_of_holder
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {l : Filter ι} [NeBot l] {f : ι → E → F} {u : E → F} {C α : ℝ≥0}
    (hα : 0 < α) (hf : ∀ i, Differentiable ℝ (f i))
    (hD : ∀ i, HolderWith C α (fderiv ℝ (f i)))
    (hu : TendstoUniformly f u l) :
    TendstoUniformly (fun i => fderiv ℝ (f i)) (fderiv ℝ u) l :=
  (differentiable_holder_of_tendstoUniformly hα hf hD hu).2.2

end DifferentialGeometry.Analysis.Schauder
