import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.ChartPulledCovApplyExplicitFormula
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartKernel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SmoothParametricCoeffIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import Mathlib.Analysis.Calculus.ParametricIntegral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Interval

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (covGrad covGrad_toSection_apply
  pathIntegralCoeffField pathIntegralFib pathIntegralCoeffField_toSection
  pathIntegralCoeffField_toModel pathIntegralFib_toModel tensorCovDerivAt tensorCovDerivAt_def)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (contMDiffOn_clm_section_of_pointwise_joint_manifold_time
  jointContMDiff_toModel_continuous_slice)
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.TensorRSNabla

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance tensorRSModelNormedAddCommGroup_local (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup r s

private local instance tensorRSModelNormedSpace_local (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace r s

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private theorem chartRepr_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
          (I := I) r s α (fun z : M => (F p.2).toSection z) p.1)
      (((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S) := by
  have hrepr :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
        (fun p : M × ℝ =>
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α)
            ⟨p.1, (F p.2).toSection p.1⟩).2)
        (((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S) := by
    intro p hp
    obtain ⟨hx, hs⟩ := hp
    have hsub : (((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S) ⊆
        ((Set.univ : Set M) ×ˢ S) := by
      intro q hq; exact ⟨Set.mem_univ _, hq.2⟩
    have hFwithin : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun p : M × ℝ => (⟨p.1, (F p.2).toSection p.1⟩ :
          TotalSpace (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z)))
        (((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S) p :=
      (hF p (hsub ⟨hx, hs⟩)).mono hsub
    have hsource : (⟨p.1, (F p.2).toSection p.1⟩ :
        TotalSpace (TensorRSModel r s ℝ E)
          (fun z : M => TensorRSSpace r s I z)) ∈
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).source := by
      rw [Bundle.Trivialization.mem_source]
      exact hx
    exact ((Bundle.Trivialization.contMDiffWithinAt_iff
      (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
      (f := fun p : M × ℝ => (⟨p.1, (F p.2).toSection p.1⟩ :
        TotalSpace (TensorRSModel r s ℝ E)
          (fun z : M => TensorRSSpace r s I z)))
      (s := ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S)
      (x₀ := p)
      (e := trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α) hsource).mp hFwithin).2
  refine hrepr.congr ?_
  intro p hp
  obtain ⟨hx, _hs⟩ := hp
  rw [DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply]
  change (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ p.1
      ((F p.2).toSection p.1) = _
  rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hx]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
theorem chartRepr_euclid_jointContDiffWithinAt
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    {t₀ : ℝ} {y₀ : E} (ht₀ : t₀ ∈ S)
    (hy₀ : y₀ ∈ (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (F q.1).toSection z) ((extChartAt I α).symm q.2))
      (S ×ˢ (extChartAt I α).target) (t₀, y₀) := by
  classical
  have hbase := chartRepr_jointContMDiffOn (I := I) g₀ r s F S α hF
  have hbaseSet_eq :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet =
        (chartAt H α).source := by
    change ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) α).baseSet) =
          (chartAt H α).source
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self]
    rfl
  rw [hbaseSet_eq] at hbase
  set φ := extChartAt I α with hφ
  have hx0src : φ.symm y₀ ∈ (chartAt H α).source := by
    have := φ.map_target hy₀
    rwa [extChartAt_source] at this
  have hsymm_on : ContMDiffOn 𝓘(ℝ, E) I ∞ φ.symm φ.target :=
    contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
  have hmove : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × E => ((φ.symm q.2 : M), q.1))
      (S ×ˢ φ.target) (t₀, y₀) := by
    refine ContMDiffWithinAt.prodMk ?_ ?_
    · have hsymm_w : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm φ.target y₀ := hsymm_on y₀ hy₀
      exact hsymm_w.comp (t₀, y₀) contMDiffWithinAt_snd (fun q hq => hq.2)
    · exact contMDiffWithinAt_fst
  have hbase_w : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (F p.2).toSection z) p.1)
      ((chartAt H α).source ×ˢ S) ((φ.symm y₀ : M), t₀) :=
    hbase ((φ.symm y₀ : M), t₀) ⟨hx0src, ht₀⟩
  have hmaps : Set.MapsTo (fun q : ℝ × E => ((φ.symm q.2 : M), q.1))
      (S ×ˢ φ.target) ((chartAt H α).source ×ˢ S) := by
    intro q hq
    obtain ⟨hqS, hqtgt⟩ := hq
    refine ⟨?_, hqS⟩
    have := φ.map_target hqtgt
    rwa [extChartAt_source] at this
  have hcomp : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun q : ℝ × E => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (F q.1).toSection z) (φ.symm q.2))
      (S ×ˢ φ.target) (t₀, y₀) :=
    hbase_w.comp (t₀, y₀) hmove hmaps
  have hself : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun q : ℝ × E => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (F q.1).toSection z) (φ.symm q.2))
      (S ×ˢ φ.target) (t₀, y₀) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hcomp
    exact hcomp
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hself
  exact hself


end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

