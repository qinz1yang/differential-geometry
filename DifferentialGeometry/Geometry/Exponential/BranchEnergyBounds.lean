import DifferentialGeometry.Geometry.Comparison.Volume.RadialTransport

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem branchEnergy_pos_of_ne
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {q : M} (hq : q ∈ B.dom) (hne : q ≠ p) :
    0 < branchEnergy g B q := by
  change 0 < (1 / 2 : ℝ) * g.inner p
    ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (B.inv q))
    ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (B.inv q))
  apply mul_pos (by norm_num) (g.pos p _ ?_)
  intro hv
  have he := B.right_inv hq
  rw [hv, expMapIntrinsic_zero] at he
  exact hne he.symm

theorem exists_pos_le_branchEnergy_of_isCompact
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {K : Set M} (hK : IsCompact K)
    (hKB : K ⊆ B.dom) (hp : p ∉ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ q ∈ K, c ≤ branchEnergy g B q := by
  apply hK.exists_forall_le' ((contMDiffOn_branchEnergy B).continuousOn.mono hKB)
  intro q hq
  apply branchEnergy_pos_of_ne B (hKB hq)
  intro hqp
  exact hp (hqp ▸ hq)

end DifferentialGeometry.Geometry.Riemannian.Exponential
