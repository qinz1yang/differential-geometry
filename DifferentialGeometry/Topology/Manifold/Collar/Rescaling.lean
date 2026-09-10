import DifferentialGeometry.Topology.Collar.Rescaling
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc

open Set Function Filter Manifold Topology TopologicalSpace
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.Collar

theorem contMDiff_rescale
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace G M] [T2Space M]
    {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F G}
    {ε : ℝ} [Fact ((0 : ℝ) < ε)]
    (c : B × Icc (0 : ℝ) ε → M) (hc : IsEmbedding c)
    (hcs : ContMDiff (J.prod (𝓡∂ 1)) I ∞ c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε))
    (hσs : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ σ)
    {Ω : Opens (B × Icc (0 : ℝ) ε)} {Y : Opens M}
    (e : Diffeomorph (J.prod (𝓡∂ 1)) I Ω Y ∞)
    (he : ∀ q : Ω, (e q : M) = c q.val)
    {k : ℝ} (hcore : {q : B × Icc (0 : ℝ) ε | q.2.val ≤ k} ⊆ Ω)
    (hfix : ∀ t : Icc (0 : ℝ) ε, k ≤ t.val → σ t = t) :
    ContMDiff I I ∞ (Poincare.Topology.Collar.rescale c hc σ) := by
  let R := Poincare.Topology.Collar.rescale c hc σ
  have hR (q : B × Icc (0 : ℝ) ε) : R (c q) = c (q.1, σ q.2) :=
    Poincare.Topology.Collar.rescale_apply c hc σ q
  let K := c '' {q : B × Icc (0 : ℝ) ε | q.2.val ≤ k}
  have hK : IsCompact K :=
    ((isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact).image
      hc.continuous
  have hKY : K ⊆ Y := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← he ⟨q, hcore hq⟩]
    exact (e ⟨q, hcore hq⟩).property
  have hRY : ContMDiff I I ∞ (fun y : Y => R y.val) := by
    let g : Y → B × Icc (0 : ℝ) ε := fun y => (e.symm y).val
    have hg : ContMDiff I (J.prod (𝓡∂ 1)) ∞ g :=
      contMDiff_subtype_val.comp e.symm.contMDiff
    have hh : ContMDiff I I ∞ (fun y : Y => c ((g y).1, σ (g y).2)) :=
      hcs.comp (contMDiff_id.prodMap hσs |>.comp hg)
    apply hh.congr
    intro y
    have heq : c (g y) = y.val := by
      rw [← he (e.symm y), e.apply_symm_apply]
    rw [← heq, hR]
  intro x
  by_cases hxY : x ∈ Y
  · exact (contMDiffAt_subtype_iff (x := (⟨x, hxY⟩ : Y))).mp hRY.contMDiffAt
  · have hxK : x ∉ K := fun h => hxY (hKY h)
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    change R y = y
    by_cases hyc : y ∈ range c
    · obtain ⟨q, rfl⟩ := hyc
      have ht : k ≤ q.2.val := le_of_lt (lt_of_not_ge (fun h => hy ⟨q, h, rfl⟩))
      rw [hR, hfix q.2 ht]
    · exact Poincare.Topology.Collar.rescale_of_not_mem c hc σ hyc

end Poincare.Manifold.Collar
