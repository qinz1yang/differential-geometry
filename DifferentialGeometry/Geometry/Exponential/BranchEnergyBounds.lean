import DifferentialGeometry.Geometry.Comparison.Volume.RadialTransport
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.InverseBranch

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
    (B : ExponentialInverseBranch g hEnorm p) {q : M} (hq : q ∈ B.dom) (hne : q ≠ p) :
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
    (B : ExponentialInverseBranch g hEnorm p) {K : Set M} (hK : IsCompact K)
    (hKB : K ⊆ B.dom) (hp : p ∉ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ q ∈ K, c ≤ branchEnergy g B q := by
  apply hK.exists_forall_le' ((contMDiffOn_branchEnergy B).continuousOn.mono hKB)
  intro q hq
  apply branchEnergy_pos_of_ne B (hKB hq)
  intro hqp
  exact hp (hqp ▸ hq)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem contMDiff_tangentEnergy (g : SmoothRiemannianMetric I M) :
    ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞
      (fun v : TangentBundle I M => (1 / 2 : ℝ) * g.inner v.proj v.snd v.snd) := by
  have hproj : ContMDiff I.tangent I ∞ (π E (TangentSpace I : M → Type _)) :=
    Bundle.contMDiff_proj (TangentSpace I)
  have hg := g.contMDiff.comp hproj
  have hv : ContMDiff I.tangent I.tangent ∞
      (fun v : TangentBundle I M => (⟨v.proj, v.snd⟩ : TangentBundle I M)) :=
    contMDiff_id
  have hi : ContMDiff I.tangent (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun v : TangentBundle I M => (⟨v.proj, g.inner v.proj v.snd v.snd⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := fun v : TangentBundle I M => v.proj) hg hv hv
  have hs : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞
      (fun v : TangentBundle I M => g.inner v.proj v.snd v.snd) := by
    intro v
    have h := hi v
    rw [Bundle.contMDiffAt_totalSpace] at h
    exact h.2
  exact contMDiff_const.mul hs

theorem DiagonalInverseBranch.contMDiffOn_branchEnergy_fixed
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c) :
    ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : M × M => branchEnergy g (B.fixed z.1) z.2) B.dom := by
  have he := (contMDiff_tangentEnergy g).comp_contMDiffOn B.inv_contMDiffOn
  apply he.congr
  intro z hz
  change (1 / 2 : ℝ) * g.inner z.1
      ((tangentSpaceModelContinuousLinearEquiv (I := I) z.1).symm ((B.fixed z.1).inv z.2))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) z.1).symm ((B.fixed z.1).inv z.2)) =
    (1 / 2 : ℝ) * g.inner (B.inv z).proj (B.inv z).snd (B.inv z).snd
  rw [B.proj_eq hz]
  rfl

theorem DiagonalInverseBranch.exists_pos_le_branchEnergy_fixed_of_isCompact
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c) {K : Set (M × M)} (hK : IsCompact K)
    (hKB : K ⊆ B.dom) (hne : ∀ z ∈ K, z.1 ≠ z.2) :
    ∃ b : ℝ, 0 < b ∧ ∀ z ∈ K, b ≤ branchEnergy g (B.fixed z.1) z.2 := by
  apply hK.exists_forall_le' (B.contMDiffOn_branchEnergy_fixed.continuousOn.mono hKB)
  intro z hz
  exact branchEnergy_pos_of_ne (B.fixed z.1) (hKB hz) (hne z hz).symm

end DifferentialGeometry.Geometry.Riemannian.Exponential
