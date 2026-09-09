import DifferentialGeometry.Analysis.Heat.Parametrix.ParameterCoefficientCompatibility
import DifferentialGeometry.Geometry.Exponential.BranchEnergyBounds
import DifferentialGeometry.Geometry.Operator.GradientPairingRegularity

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.DiagInvBranch

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

theorem exists_heatParametrixCoefficientInCoordinates_fixed_compact_bound
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagInvBranch g hEnorm c) :
    ∃ V : Set (M × M), IsOpen V ∧ (c, c) ∈ V ∧ V ⊆ B.dom ∧
      ∀ (χ : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) ∞ χ →
      ∀ k : ℕ, ∀ K : Set (M × M), IsCompact K → K ⊆ V →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K,
          |heatParametrixCoefficientInCoordinates g (B.fixed z.1).hom (B.fixed z.1).inv
            (fun v => paramDensity g (B.fixed z.1).hom v /
              paramDensity g (B.fixed z.1).hom 0) k z.2| ≤ C ∧
          |laplacian (LeviCivita g) g
            (heatParametrixCoefficientInCoordinates g (B.fixed z.1).hom (B.fixed z.1).inv
              (fun v => paramDensity g (B.fixed z.1).hom v /
                paramDensity g (B.fixed z.1).hom 0) k) z.2| ≤ C ∧
          |g.inner z.2 (gradientFun g χ z.2)
            (gradientFun g (heatParametrixCoefficientInCoordinates g
              (B.fixed z.1).hom (B.fixed z.1).inv
              (fun v => paramDensity g (B.fixed z.1).hom v /
                paramDensity g (B.fixed z.1).hom 0) k) z.2)| ≤ C ∧
          |g.inner z.2 (gradientFun g χ z.2)
            (gradientFun g (branchEnergy g (B.fixed z.1)) z.2)| ≤ C := by
  obtain ⟨V, hV, hcV, hVB, ha⟩ :=
    B.exists_contMDiffOn_heatParametrixCoefficientInCoordinates_fixed_prod
  refine ⟨V, hV, hcV, hVB, ?_⟩
  intro χ hχ k K hK hKV
  let a : M → M → ℝ := fun p q => heatParametrixCoefficientInCoordinates g
    (B.fixed p).hom (B.fixed p).inv
    (fun v => paramDensity g (B.fixed p).hom v / paramDensity g (B.fixed p).hom 0) k q
  let l : M × M → ℝ := fun z => laplacian (LeviCivita g) g (a z.1) z.2
  let b : M × M → ℝ := fun z =>
    g.inner z.2 (gradientFun g χ z.2) (gradientFun g (a z.1) z.2)
  let d : M × M → ℝ := fun z =>
    g.inner z.2 (gradientFun g χ z.2) (gradientFun g (branchEnergy g (B.fixed z.1)) z.2)
  have has : ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞ (Function.uncurry a) V := ha k
  have hls : ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞ l V :=
    contMDiffOn_laplacian_leviCivita_prod_of_isOpen (IP := I) (f := a) g hV has
  have hχs : ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞ (fun z : M × M => χ z.2) V :=
    hχ.comp_contMDiffOn contMDiffOn_snd
  have hbs : ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞ b V :=
    contMDiffOn_inner_gradient_prod_of_isOpen (IP := I) (f := fun _ => χ) (h := a)
      g hV hχs has
  have hds : ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞ d V :=
    contMDiffOn_inner_gradient_prod_of_isOpen (IP := I) (f := fun _ => χ)
      (h := fun p => branchEnergy g (B.fixed p)) g hV hχs
      (B.contMDiffOn_branchEnergy_fixed.mono hVB)
  let F : M × M → ℝ := fun z => |a z.1 z.2| + |l z| + |b z| + |d z|
  have hF : ContinuousOn F K :=
    (((has.continuousOn.abs.add hls.continuousOn.abs).add hbs.continuousOn.abs).add
      hds.continuousOn.abs).mono hKV
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  have hCF : |F z| ≤ C := by simpa only [Real.norm_eq_abs] using hC z hz
  have hb : F z ≤ max C 0 := (le_abs_self (F z)).trans
    (hCF.trans (le_max_left C 0))
  change |a z.1 z.2| ≤ _ ∧ |l z| ≤ _ ∧ |b z| ≤ _ ∧ |d z| ≤ _
  dsimp only [F] at hb
  have h0 := abs_nonneg (a z.1 z.2)
  have h1 := abs_nonneg (l z)
  have h2 := abs_nonneg (b z)
  have h3 := abs_nonneg (d z)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end DifferentialGeometry.Geometry.Riemannian.Exponential.DiagInvBranch
