import DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem contMDiffOn_expMapIntrinsic_trivialization
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e] :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) I ∞
      (fun z : M × E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 z.2)) e.target := by
  have hcomp := (intrinsicExp_smooth g hEnorm).comp_contMDiffOn e.contMDiffOn_symm
  apply hcomp.congr
  intro z hz
  have hzbase : z.1 ∈ e.baseSet := e.mem_target.mp hz
  change expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 z.2) =
    expMapIntrinsic g hEnorm (e.toOpenPartialHomeomorph.symm (z.1, z.2)).proj
      (e.toOpenPartialHomeomorph.symm (z.1, z.2)).snd
  rw [← e.mk_symm hzbase, ← e.symmL_apply (R := ℝ) hzbase]

end DifferentialGeometry.Geometry.Riemannian.Exponential
