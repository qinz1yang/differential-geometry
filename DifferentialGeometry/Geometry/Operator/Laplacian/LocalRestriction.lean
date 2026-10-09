import DifferentialGeometry.Geometry.Operator.Restriction
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Bundle.SmoothScalarGerm


noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem laplacian_restrictOpen_of_contMDiffOn
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    {f : M → ℝ} {V : Set M} (hV : IsOpen V)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V) (x : U) (hxV : (x : M) ∈ V) :
    laplacian (Connection.LeviCivita (g.restrictOpen U)) (g.restrictOpen U)
      (fun y : U => f (y : M)) x =
        laplacian (Connection.LeviCivita g) g f (x : M) := by
  obtain ⟨F, hF, heq⟩ := exists_smooth_germ hV hxV hf
  have hinc : ContMDiffAt I I ∞ (Subtype.val : U → M) x :=
    (contMDiff_subtype_val (I := I) (U := U)).contMDiffAt
  have hfU : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y : U => f (y : M)) x :=
    (hf.contMDiffAt (hV.mem_nhds hxV)).comp x hinc
  have hFU : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : U => F (y : M)) :=
    hF.comp (contMDiff_subtype_val (I := I) (U := U))
  calc
    laplacian (Connection.LeviCivita (g.restrictOpen U)) (g.restrictOpen U)
        (fun y : U => f (y : M)) x =
      laplacian (Connection.LeviCivita (g.restrictOpen U)) (g.restrictOpen U)
        (fun y : U => F (y : M)) x :=
      laplacian_congr_of_eventuallyEq _ _ hfU hFU.contMDiffAt
        (heq.symm.comp_tendsto hinc.continuousAt.tendsto)
    _ = laplacian (Connection.LeviCivita g) g F (x : M) :=
      laplacian_restrictOpen g U F hF x
    _ = laplacian (Connection.LeviCivita g) g f (x : M) :=
      laplacian_congr_of_eventuallyEq _ _ hF.contMDiffAt
        (hf.contMDiffAt (hV.mem_nhds hxV)) heq

end DifferentialGeometry.Geometry.Operator
