import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.GlobalImageLineFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureNullity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_global_parallel_unit_section_of_curvatureOperatorImage_rank_eq_one
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {U : Set ℝ} (hU : IsOpen U) (hreg : U ⊆ D.regular)
    {J : Set ℝ} (hJ : J.OrdConnected) (hJsub : J ⊆ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hR : ∀ t ∈ U, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1) :
    ∃ s : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ t ∈ J, ∀ x, s x ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ∧
      (∀ t ∈ J, ∀ x, (S.family.metric t).inner x (s x) (s x) = 1) ∧
      (∀ t ∈ J, ∀ x, ∀ v : TangentSpace I x,
        (LeviCivita (S.family.metric t)) s x v = 0) ∧
      ∀ t ∈ J, ∀ x, ∀ v : TangentSpace I x,
        (S.family.metric t).inner x (s x) v = (S.family.metric t₀).inner x (s x) v := by
  have hregJ : J ⊆ D.regular := hJsub.trans hreg
  have hRJ r (hr : r ∈ J) := hR r (hJsub hr)
  have hkernel r (hr : r ∈ J) :
      IsParallelContinuousAlternatingSubmoduleFamily (S.family.metric r)
        (fun x => curvatureOperatorKernelAt (S.family.metric r) x
          ⟨metricRm04At (S.family.metric r) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩) := by
    obtain ⟨a, b, hrange, hab⟩ :=
      (mem_nhds_iff_exists_Ioo_subset).mp (hU.mem_nhds (hJsub hr))
    obtain ⟨c, hac, hcr⟩ := exists_between hrange.1
    have hrb : r < b := hrange.2
    have hsub : Icc c r ⊆ U := fun q hq =>
      hab ⟨hac.trans_le hq.1, hq.2.trans_lt hrb⟩
    exact curvatureOperatorKernelAt_parallel_at_later_time S hS hdim hcr
      (hsub.trans hreg) (fun q hq => hR q (hsub hq))
  obtain ⟨s, hmem, hunit, hparallel, hdual⟩ :=
    exists_common_global_parallel_unit_section_of_curvatureOperatorImageAnnihilator_eq
      (fun r : J => S.family.metric r.1) ⟨t₀, ht₀⟩ hdim
      (fun r => hrank r.1 r.2) (fun r => hkernel r.1 r.2)
      (fun r x => (curvatureOperatorImageAnnihilatorAt_eq_and_inner_eq_of_rank_one_on_interval
        S hS hdim hJ hregJ hRJ hrank r.2 ht₀ x).1)
      (fun r x v hv w => (curvatureOperatorImageAnnihilatorAt_eq_and_inner_eq_of_rank_one_on_interval
        S hS hdim hJ hregJ hRJ hrank ht₀ r.2 x).2 v hv w |>.symm)
  exact ⟨s, (fun t ht => hmem ⟨t, ht⟩), (fun t ht => hunit ⟨t, ht⟩),
    (fun t ht => hparallel ⟨t, ht⟩), (fun t ht => hdual ⟨t, ht⟩)⟩

theorem exists_global_parallel_unit_section_on_interval_of_curvatureOperatorImage_rank_eq_one
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {α β : ℝ} (hreg : Ioo α β ⊆ D.regular)
    {J : Set ℝ} (hJ : J.OrdConnected) (hJsub : J ⊆ Ioo α β)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hR : ∀ t ∈ Ioo α β, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1) :
    ∃ s : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ t ∈ J, ∀ x, s x ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ∧
      (∀ t ∈ J, ∀ x, (S.family.metric t).inner x (s x) (s x) = 1) ∧
      (∀ t ∈ J, ∀ x, ∀ v : TangentSpace I x,
        (LeviCivita (S.family.metric t)) s x v = 0) ∧
      ∀ t ∈ J, ∀ x, ∀ v : TangentSpace I x,
        (S.family.metric t).inner x (s x) v = (S.family.metric t₀).inner x (s x) v := by
  exact exists_global_parallel_unit_section_of_curvatureOperatorImage_rank_eq_one
    S hS hdim isOpen_Ioo hreg hJ hJsub ht₀ hR hrank

end DifferentialGeometry.PDE.RicciFlow
