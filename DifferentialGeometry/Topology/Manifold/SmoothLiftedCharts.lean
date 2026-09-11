import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
noncomputable section
open Set Function Manifold IsManifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E F G H H' H'' S T Z : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H') (K : ModelWithCorners ℝ G H'')
variable [TopologicalSpace S] [ChartedSpace H S]
variable [TopologicalSpace T] [ChartedSpace H' T]
variable [TopologicalSpace Z] [ChartedSpace H'' Z] [Nonempty Z]

theorem contMDiffOn_lift_openEmbedding (f : S → T)
    (hf : _root_.Topology.IsOpenEmbedding f) (hs : IsLocalDiffeomorph I J ∞ f)
    (e : OpenPartialHomeomorph S Z) (he : ContMDiffOn I K ∞ e e.source) :
    ContMDiffOn J K ∞ (e.lift_openEmbedding hf) (e.lift_openEmbedding hf).source := by
  rintro y ⟨x, hx, rfl⟩
  have hi := (hs x).localInverse_contMDiffAt
  have hix : (hs x).localInverse (f x) = x :=
    (hs x).localInverse_left_inv (hs x).localInverse_mem_target
  have hc : ContMDiffAt I K ∞ e ((hs x).localInverse (f x)) := by
    rw [hix]
    exact he.contMDiffAt (e.open_source.mem_nhds hx)
  have hcomp := hc.comp (f x) hi
  apply (hcomp.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(hs x).localInverse_open_source.mem_nhds (hs x).localInverse_mem_source] with z hz
  change (e.lift_openEmbedding hf) z = e ((hs x).localInverse z)
  exact (congrArg (e.lift_openEmbedding hf) ((hs x).localInverse_right_inv hz).symm).trans
    (e.lift_openEmbedding_apply hf)

theorem contMDiffOn_lift_openEmbedding_symm (f : S → T)
    (hf : _root_.Topology.IsOpenEmbedding f) (hs : ContMDiff I J ∞ f)
    (e : OpenPartialHomeomorph S Z) (he : ContMDiffOn K I ∞ e.symm e.target) :
    ContMDiffOn K J ∞ (e.lift_openEmbedding hf).symm (e.lift_openEmbedding hf).target :=
  hs.comp_contMDiffOn he
end DifferentialGeometry.Topology.Manifold
