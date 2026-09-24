import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.NoCutLocus
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InjGeometryComplete


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

theorem lExp_inj_image_eq_univ_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau s : ℝ} (hs : 0 < s) (hstau : s < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    (fun Z : E => lExp S T x Z s) '' lInjDomain S T x s = univ := by
  have hslabs : Icc (T - s) T ⊆ D.regular :=
    (Icc_subset_Icc (sub_le_sub_left hstau.le T) le_rfl).trans hslab
  obtain ⟨K, hK⟩ := hRm s hs hslabs
  have hinj := lInjDomain_eq_univ_of_redVolume_eq_one S hS T hg x hRm
    (hs.trans hstau) hstau hslab hvol
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨Z, _hmin, hend⟩ := exists_lMin_slab_of_rm S hS K T hg x y s hs hslabs hK
  refine ⟨(Z : E), ?_, hend⟩
  rw [hinj]
  exact mem_univ Z

end DifferentialGeometry.PDE.RicciFlow.Perelman
