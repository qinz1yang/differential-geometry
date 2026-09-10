import DifferentialGeometry.Topology.Covering.SmoothLift
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology

variable {E F C H H' W M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace W] [ChartedSpace H W]
  [TopologicalSpace M] [ChartedSpace H' M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}

theorem isImmersionOfComplement_of_lift_through_localDiffeomorphOn
    [IsManifold J ∞ N] {p : N → M} {g : W → N}
    (hp : IsLocalDiffeomorphOn J J ∞ p (range g))
    {f : W → M} (hf : IsImmersionOfComplement C I J ∞ f)
    (hg : Continuous g) (hpg : ∀ x, p (g x) = f x) :
    IsImmersionOfComplement C I J ∞ g := by
  intro x
  let h := hf x
  obtain ⟨χ, hxχ, hχ⟩ := hp ⟨g x, mem_range_self x⟩
  let U := g ⁻¹' χ.source
  have hU : IsOpen U := χ.open_source.preimage hg
  let φ := h.domChart.restr U
  let ψ := χ.toOpenPartialHomeomorph.trans h.codChart
  have hψ : ψ ∈ IsManifold.maximalAtlas J ∞ N := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        (χ.contMDiffOn_toFun.mono (fun _ hz ↦ hz.1)) (fun _ hz ↦ hz.2)
    · exact χ.contMDiffOn_invFun.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mono
          (fun _ hz ↦ hz.1)) (fun _ hz ↦ hz.2)
  have hφ : φ ∈ IsManifold.maximalAtlas I ∞ W :=
    restr_mem_maximalAtlas _ h.domChart_mem_maximalAtlas hU
  have hfx : g x ∈ ψ.source := by
    refine ⟨hxχ, ?_⟩
    change χ.toPartialEquiv (g x) ∈ h.codChart.source
    rw [← hχ hxχ, hpg]
    exact h.mem_codChart_source
  apply IsImmersionAtOfComplement.mk_of_continuousAt hg.continuousAt h.equiv φ ψ
    (by change x ∈ h.domChart.source ∩ interior U
        rw [hU.interior_eq]
        exact ⟨h.mem_domChart_source, hxχ⟩) hfx hφ hψ
  intro z hz
  have hm : (h.domChart.extend I).symm z ∈ h.domChart.source ∩ U := by
    simpa only [OpenPartialHomeomorph.extend_source, φ,
      OpenPartialHomeomorph.restr_source, hU.interior_eq,
      OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply,
      OpenPartialHomeomorph.restr_symm_apply] using (φ.extend I).map_target hz
  have hz' : z ∈ (h.domChart.extend I).target := by
    have hz₁ := hz
    simp only [φ, OpenPartialHomeomorph.extend_target,
      OpenPartialHomeomorph.restr_target, hU.interior_eq] at hz₁ ⊢
    exact ⟨hz₁.1.1, hz₁.2⟩
  have heq : χ.toPartialEquiv (g ((h.domChart.extend I).symm z)) =
      f ((h.domChart.extend I).symm z) := (hχ hm.2).symm.trans (hpg _)
  change J (h.codChart (χ.toPartialEquiv (g ((h.domChart.extend I).symm z)))) = _
  rw [heq]
  exact h.writtenInCharts hz'

theorem isImmersionOfComplement_of_lift_through_localDiffeomorph
    [IsManifold J ∞ N] {p : N → M} (hp : IsLocalDiffeomorph J J ∞ p)
    {f : W → M} (hf : IsImmersionOfComplement C I J ∞ f)
    {g : W → N} (hg : Continuous g) (hpg : ∀ x, p (g x) = f x) :
    IsImmersionOfComplement C I J ∞ g :=
  isImmersionOfComplement_of_lift_through_localDiffeomorphOn (fun y ↦ hp y) hf hg hpg

theorem isSmoothEmbedding_of_lift_through_localDiffeomorph
    [IsManifold J ∞ N] {p : N → M} (hp : IsLocalDiffeomorph J J ∞ p)
    {f : W → M} (hf : IsSmoothEmbedding I J ∞ f)
    {g : W → N} (hg : Continuous g) (hpg : ∀ x, p (g x) = f x) :
    IsSmoothEmbedding I J ∞ g := by
  refine ⟨?_, ?_⟩
  · exact (isImmersionOfComplement_of_lift_through_localDiffeomorph hp
      hf.isImmersion.isImmersionOfComplement_complement hg hpg).isImmersion
  · have hcomp : p ∘ g = f := funext hpg
    exact IsEmbedding.of_comp hg hp.contMDiff.continuous (hcomp ▸ hf.isEmbedding)

theorem injective_mfderiv_of_smooth_lift
    {p : N → M} (hp : ContMDiff J J ∞ p) {f : W → M}
    (hf : ∀ x, Function.Injective (mfderiv I J f x))
    {g : W → N} (hg : ContMDiff I J ∞ g) (hpg : ∀ x, p (g x) = f x) (x : W) :
    Function.Injective (mfderiv I J g x) := by
  have heq : p ∘ g = f := funext hpg
  have hc := mfderiv_comp x (hp.mdifferentiable (by decide) (g x))
    (hg.mdifferentiable (by decide) x)
  intro v w hvw
  apply hf x
  rw [← heq, hc]
  exact congrArg (mfderiv J J p (g x)) hvw

end DifferentialGeometry.Topology
