import DifferentialGeometry.Analysis.Heat.Parametrix.CoordinateCoefficient
import DifferentialGeometry.Geometry.Comparison.Volume.ExponentialDensity
import DifferentialGeometry.Geometry.Exponential.BranchTrivialization

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.DiagonalInverseBranch

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection

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

def heatParametrixCoefficientInTrivialization
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e] (k : ℕ) (p q : M) : ℝ :=
  heatParametrixCoefficientInCoordinates g
    (fun v => expMapIntrinsic g hEnorm p (e.symmL ℝ p v))
    (fun y => (e (B.inv (p, y))).2)
    (fun v => paramDensity g (fun w => expMapIntrinsic g hEnorm p (e.symmL ℝ p w)) v /
      paramDensity g (fun w => expMapIntrinsic g hEnorm p (e.symmL ℝ p w)) 0) k q

theorem exists_contMDiffOn_heatParametrixCoefficientInTrivialization_prod
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e]
    (hc : c ∈ e.baseSet) :
    ∃ V : Set (M × M), IsOpen V ∧ (c, c) ∈ V ∧ V ⊆ B.dom ∧
      ∀ k : ℕ, ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : M × M => B.heatParametrixCoefficientInTrivialization e k z.1 z.2) V := by
  let Φ : M → E → M := fun p v => expMapIntrinsic g hEnorm p (e.symmL ℝ p v)
  let Ψ : M → M → E := fun p q => (e (B.inv (p, q))).2
  let J : M → E → ℝ := fun p v => paramDensity g (Φ p) v / paramDensity g (Φ p) 0
  obtain ⟨W, hW, _, hWzero, hJpos, hJ⟩ :=
    exists_contMDiffOn_paramDensity_ratio_expMapIntrinsic_trivialization g hEnorm e
  obtain ⟨S, hS, hcS, r, hr, V, hV, hcV, hVB, hT, hTB, hRe,
      hF, hR, hFV, hRT, hleft, hright⟩ :=
    B.exists_ball_trivialization_domain e hc hW (hWzero c hc)
  refine ⟨V, hV, hcV, hVB, ?_⟩
  intro k
  have hΦ : ContMDiffOn (I.prod 𝓘(ℝ, E)) I ∞ (Function.uncurry Φ)
      (S ×ˢ Metric.ball (0 : E) r) := contMDiff_snd.comp_contMDiffOn hF
  have hΨ : ContMDiffOn (I.prod I) 𝓘(ℝ, E) ∞ (Function.uncurry Ψ) V := by
    have hRs := contMDiff_snd.comp_contMDiffOn hR
    exact hRs
  have hJW : ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry J)
      (S ×ˢ Metric.ball (0 : E) r) := hJ.mono (fun z hz => (hT hz).1)
  exact contMDiffOn_heatParametrixCoefficientInCoordinates_prod (IP := I) g
    hV hS Metric.isOpen_ball ((convex_ball (0 : E) r).starConvex (Metric.mem_ball_self hr))
    hΦ hΨ hJW (fun z hz => hJpos z (hT hz).1) hFV hRT k

theorem exists_contMDiffOn_laplacian_heatParametrixCoefficientInTrivialization_prod
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e]
    (hc : c ∈ e.baseSet) :
    ∃ V : Set (M × M), IsOpen V ∧ (c, c) ∈ V ∧ V ⊆ B.dom ∧
      ∀ k : ℕ, ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : M × M => laplacian (LeviCivita g) g
          (B.heatParametrixCoefficientInTrivialization e k z.1) z.2) V := by
  obtain ⟨V, hV, hcV, hVB, ha⟩ :=
    B.exists_contMDiffOn_heatParametrixCoefficientInTrivialization_prod e hc
  refine ⟨V, hV, hcV, hVB, ?_⟩
  intro k
  exact contMDiffOn_laplacian_leviCivita_prod_of_isOpen (IP := I) g hV (ha k)

theorem exists_heatParametrixCoefficientInTrivialization_compact_bound
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e]
    (hc : c ∈ e.baseSet) :
    ∃ V : Set (M × M), IsOpen V ∧ (c, c) ∈ V ∧ V ⊆ B.dom ∧
      ∀ k : ℕ, ∀ K : Set (M × M), IsCompact K → K ⊆ V →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K,
          |B.heatParametrixCoefficientInTrivialization e k z.1 z.2| ≤ C ∧
          |laplacian (LeviCivita g) g
            (B.heatParametrixCoefficientInTrivialization e k z.1) z.2| ≤ C := by
  obtain ⟨V, hV, hcV, hVB, ha⟩ :=
    B.exists_contMDiffOn_heatParametrixCoefficientInTrivialization_prod e hc
  refine ⟨V, hV, hcV, hVB, ?_⟩
  intro k K hK hKV
  have hΔ := contMDiffOn_laplacian_leviCivita_prod_of_isOpen (IP := I)
    (f := B.heatParametrixCoefficientInTrivialization e k) g hV (ha k)
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn ((ha k).continuousOn.mono hKV)
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn (hΔ.continuousOn.mono hKV)
  refine ⟨max 0 (max C₀ C₁), le_max_left _ _, ?_⟩
  intro z hz
  constructor
  · exact (show |B.heatParametrixCoefficientInTrivialization e k z.1 z.2| ≤ C₀ by
      simpa only [Real.norm_eq_abs] using hC₀ z hz).trans
        ((le_max_left C₀ C₁).trans (le_max_right 0 (max C₀ C₁)))
  · exact (show |laplacian (LeviCivita g) g
        (B.heatParametrixCoefficientInTrivialization e k z.1) z.2| ≤ C₁ by
      simpa only [Real.norm_eq_abs] using hC₁ z hz).trans
        ((le_max_right C₀ C₁).trans (le_max_right 0 (max C₀ C₁)))

end DifferentialGeometry.Geometry.Riemannian.Exponential.DiagonalInverseBranch
