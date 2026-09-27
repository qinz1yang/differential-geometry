import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannSmooth
import DifferentialGeometry.Geometry.Comparison.Splitting.AffineFunctionSplitting

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open scoped _root_.Topology NNReal ContDiff Manifold

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem timeZero_isometric_product_of_nonnegative_ricci_line
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ x : M, ∀ v : TangentSpace I x, 0 ≤ ricciTensor (I := I) g x v v)
    {gamma : ℝ → M} (hgamma : Isometry gamma) :
    let b := busemann (fun t : ℝ≥0 => gamma t)
    ∃ hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b,
      ∃ hunit : ∀ p, g.inner p (gradientFun (I := I) g b p)
          (gradientFun (I := I) g b p) = 1,
        ∃ hH : ∀ p, hessFun (I := I) g b p = 0,
          ∃ p₀ : {q : M // b q = 0},
            let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
            let _ := affineZeroLevel_isManifold (I := I) g hEnorm hb hunit hH p₀
            let _ : SigmaCompactSpace {q : M // b q = 0} :=
              (isClosed_eq hb.continuous continuous_const).sigmaCompactSpace
            ConnectedSpace {q : M // b q = 0} ∧
            DifferentialGeometry.Geometry.IsEmbeddedSlice I (Module.finrank ℝ E - 1)
              {q : M | b q = 0} ∧
            Module.finrank ℝ (affineFunctionKernel (I := I) b p₀.1) + 1 =
              Module.finrank ℝ E ∧
            RiemannianMetricComplete
              (I := 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1))
              (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀) ∧
            ∃ F : ({q : M // b q = 0} × ℝ) ≃ₘ⟮
                𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ), I⟯ M,
              (∀ (p : {q : M // b q = 0}) (t : ℝ),
                F (p, t) = affineGradientFlow (I := I) g hEnorm b p.1 t) ∧
              (∀ x : M, F.symm x =
                (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH x, b x)) ∧
              (∀ (p : {q : M // b q = 0})
                (v w : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p)
                (t a c : ℝ),
                g.inner (F (p, t))
                  (mfderiv (𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ)) I
                    F (p, t) (v, a))
                  (mfderiv (𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ)) I
                    F (p, t) (w, c)) =
                  (affineZeroLevelMetric (I := I) g hEnorm hb hunit hH p₀).inner p v w +
                    a * c) := by
  let b := busemann (fun t : ℝ≥0 => gamma t)
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b := busemann_contMDiff g hEnorm hRic hgamma
  have hunit (p : M) :
      g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1 :=
    (opposite_busemann_gradient_unit g hEnorm hRic hgamma p).1
  have hH (p : M) : hessFun (I := I) g b p = 0 :=
    busemann_hessian_eq_zero g hEnorm hRic hgamma p
  exact ⟨hb, hunit, hH, affineFunction_splitting g hEnorm hb hunit hH⟩

theorem timeZero_busemann_factor_finrank_two
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ x : M, ∀ v : TangentSpace I x, 0 ≤ ricciTensor (I := I) g x v v)
    (hdim : Module.finrank ℝ E = 3) {gamma : ℝ → M} (hgamma : Isometry gamma)
    (p : M) :
    Module.finrank ℝ (affineFunctionKernel (I := I)
      (busemann (fun t : ℝ≥0 => gamma t)) p) = 2 := by
  let b := busemann (fun t : ℝ≥0 => gamma t)
  have hunit (q : M) :
      g.inner q (gradientFun (I := I) g b q) (gradientFun (I := I) g b q) = 1 :=
    (opposite_busemann_gradient_unit g hEnorm hRic hgamma q).1
  have h := affineFunction_kernel_finrank (I := I) g b hunit p
  change Module.finrank ℝ (affineFunctionKernel (I := I) b p) + 1 =
    Module.finrank ℝ E at h
  rw [hdim] at h
  exact Nat.add_right_cancel h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
