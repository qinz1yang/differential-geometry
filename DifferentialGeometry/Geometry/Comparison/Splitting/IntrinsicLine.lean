import DifferentialGeometry.Geometry.Comparison.Splitting.Busemann

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.HopfRinow
open scoped Topology NNReal ContDiff Manifold ENNReal

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH uM
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem cheeger_gromoll_splitting
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace I x, 0 ≤ ricciTensor g x v v)
    {gamma : ℝ → M}
    (hline : ∀ s t : ℝ, riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|) :
    ∃ V : Submodule ℝ E, Module.finrank ℝ V + 1 = Module.finrank ℝ E ∧
      ∃ N : Type uM, ∃ top : TopologicalSpace N, letI := top
        ∃ charts : ChartedSpace V N, letI := charts
          ∃ smooth : IsManifold 𝓘(ℝ, V) ∞ N, letI := smooth
            ∃ hausdorff : T2Space N, letI := hausdorff
              ∃ sigma : SigmaCompactSpace N, letI := sigma
                ∃ connected : ConnectedSpace N, letI := connected
                  ∃ h : SmoothRiemannianMetric 𝓘(ℝ, V) N, RiemannianMetricComplete h ∧
                    ∃ Phi : (N × ℝ) ≃ₘ⟮𝓘(ℝ, V).prod 𝓘(ℝ, ℝ), I⟯ M,
                      (∀ (p : N) (v w : TangentSpace 𝓘(ℝ, V) p) (t a c : ℝ),
                        g.inner (Phi (p,t))
                          (mfderiv (𝓘(ℝ, V).prod 𝓘(ℝ, ℝ)) I Phi (p,t) (v,a))
                          (mfderiv (𝓘(ℝ, V).prod 𝓘(ℝ, ℝ)) I Phi (p,t) (w,c)) =
                            h.inner p v w + a*c) ∧
                      ∀ y : M, (Phi.symm y).2 =
                        ⨆ s : ℝ≥0, (s : ℝ) - (riemannianEDistOf g y (gamma s)).toReal := by
  classical
  have hdim : Module.finrank ℝ E ≠ 0 := by
    intro hz
    let _ : Subsingleton E := Module.finrank_zero_iff.mp hz
    let _ : Subsingleton H := I.injective.subsingleton
    let _ : DiscreteTopology H := inferInstance
    let _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let _ : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
    have hh := hline 0 1
    rw [Subsingleton.elim (gamma 0) (gamma 1), riemannianEDistOf_self] at hh
    norm_num at hh
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : CompleteSpace M := hg.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := fun x v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  let _ : MetricSpace M := riemMetricSpace (I := I) (M := M)
  let _ : ProperSpace M := properSpace_riemMetric hg.complete g hEnorm
  have hgamma : Isometry gamma := by
    apply Isometry.of_dist_eq
    intro s t
    rw [riemMetric_dist_eq (I := I),
      ← riemannianEDistOf_eq_riemannianEDist g hEnorm,hline,
      ENNReal.toReal_ofReal (abs_nonneg _),Real.dist_eq]
  obtain ⟨hb,hunit,hH,p0,hconn,hslice,hfactor,hcomplete,Phi,hPhi,hPhiInv,hmetric⟩ :=
    PDE.RicciFlow.Perelman.KappaSolutions.timeZero_isometric_product_of_nonnegative_ricci_line
      g hEnorm hRic hgamma
  let b := busemann (fun t : ℝ≥0 => gamma t)
  let _ := affineZeroLevelChartedSpace g hEnorm hb hunit hH p0
  let _ := affineZeroLevel_isManifold g hEnorm hb hunit hH p0
  let _ : SigmaCompactSpace {x : M // b x = 0} :=
    (isClosed_eq hb.continuous continuous_const).sigmaCompactSpace
  refine ⟨affineFunctionKernel b p0.val,hfactor,{x : M // b x = 0},inferInstance,
    inferInstance,inferInstance,inferInstance,inferInstance,hconn,
    affineZeroLevelMetric g hEnorm hb hunit hH p0,hcomplete,Phi,hmetric,?_⟩
  intro y
  rw [hPhiInv]
  change b y = _
  unfold b busemann busemannApprox
  congr 1

end DifferentialGeometry.Geometry.Topology
