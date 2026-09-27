import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.ExponentialCoverage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.FinitePoleSpacetimeRegularity


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

theorem redLength_joint_contMDiffOn_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau : ℝ} (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : M × ℝ => redLength S T x q.1 q.2) (univ ×ˢ Ioo 0 tau) := by
  apply (redLength_joint_contMDiffOn_of_rm S hS T hg x hRm).mono
  rintro ⟨y, s⟩ ⟨_hy, hs, hstau⟩
  refine ⟨hs, ?_⟩
  have hcoverage := lExp_inj_image_eq_univ_of_redVolume_eq_one S hS T hg x hRm
    hs hstau hslab hvol
  have hy : y ∈ (fun Z : E => lExp S T x Z s) '' lInjDomain S T x s := by
    rw [hcoverage]
    exact mem_univ y
  exact hy

end DifferentialGeometry.PDE.RicciFlow.Perelman
