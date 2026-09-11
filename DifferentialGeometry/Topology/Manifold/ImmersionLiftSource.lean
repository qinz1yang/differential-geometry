import DifferentialGeometry.Topology.Manifold.SmoothLiftedCharts
import Mathlib.Geometry.Manifold.Immersion

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold IsManifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E F C H H' S T N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup C] [NormedSpace ℝ C]
variable [TopologicalSpace H] [TopologicalSpace H'] [Nonempty H]
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
variable [TopologicalSpace S] [ChartedSpace H S]
variable [TopologicalSpace T] [ChartedSpace H T] [IsManifold I ∞ T]
variable [TopologicalSpace N] [ChartedSpace H' N]

theorem isImmersionAtOfComplement_lift_source (f : S → T)
    (hf : _root_.Topology.IsOpenEmbedding f) (hs : IsLocalDiffeomorph I I ∞ f)
    (g : T → N) (x : S) (h : IsImmersionAtOfComplement C I J ∞ (g ∘ f) x) :
    IsImmersionAtOfComplement C I J ∞ g (f x) := by
  let c := h.domChart.lift_openEmbedding hf
  have hc : c ∈ maximalAtlas I ∞ T :=
    c.mem_maximalAtlas_of_contMDiffOn
      (contMDiffOn_lift_openEmbedding I I I f hf hs h.domChart
        (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas))
      (contMDiffOn_lift_openEmbedding_symm I I I f hf hs.contMDiff h.domChart
        (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas))
  have hinv : (hs x).localInverse (f x) = x :=
    (hs x).localInverse_left_inv (hs x).localInverse_mem_target
  have hg : ContinuousAt g (f x) := by
    have hgf : ContinuousAt (g ∘ f) ((hs x).localInverse (f x)) := hinv.symm ▸ h.continuousAt
    have hcomp := hgf.comp (hs x).localInverse_contMDiffAt.continuousAt
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [(hs x).localInverse_open_source.mem_nhds (hs x).localInverse_mem_source] with y hy
    exact congrArg g ((hs x).localInverse_right_inv hy).symm
  apply IsImmersionAtOfComplement.mk_of_continuousAt hg h.equiv c h.codChart
    ⟨x, h.mem_domChart_source, rfl⟩ h.mem_codChart_source hc h.codChart_mem_maximalAtlas
  intro z hz
  exact h.writtenInCharts hz
end DifferentialGeometry.Topology.Manifold
