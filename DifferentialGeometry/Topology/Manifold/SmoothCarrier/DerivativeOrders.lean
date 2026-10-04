import DifferentialGeometry.Topology.Manifold.SmoothCarrier.OriginalManifold
import DifferentialGeometry.Geometry.Metric.FiniteLedger.Chart
import DifferentialGeometry.Geometry.Exponential.FiniteMetric

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Topology.Manifold

private theorem finite_geodesic_regularities
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {n : ℕ∞ω} (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (r : ℕ∞) (hn : n = (r : ℕ∞ω) + 1) (hr : 1 ≤ r) :
    IsOpen g.geodesicFlowDomain ∧
      ContMDiffOn (𝓘(ℝ, E).tangent.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E).tangent r
        (fun p : TangentBundle 𝓘(ℝ, E) M × ℝ => g.geodesicFlow p.1 p.2)
        g.geodesicFlowDomain ∧
      (∀ p : TangentBundle 𝓘(ℝ, E) M, (p, 0) ∈ g.geodesicFlowDomain ∧
        g.geodesicFlow p 0 = p) ∧
      IsOpen g.expDomain ∧
      ContMDiffOn 𝓘(ℝ, E).tangent 𝓘(ℝ, E) r g.expMap g.expDomain ∧
      ∀ x : M, (⟨x, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ g.expDomain ∧
        g.expMap (⟨x, 0⟩ : TangentBundle 𝓘(ℝ, E) M) = x := by
  subst n
  exact ⟨g.isOpen_geodesicFlowDomain hr, g.contMDiffOn_geodesicFlow hr,
    fun p => ⟨g.mem_geodesicFlowDomain_zero hr p, g.geodesicFlow_zero hr p⟩,
    g.isOpen_expDomain hr, g.contMDiffOn_expMap hr,
    fun x => ⟨g.zero_mem_expDomain x, g.expMap_zero hr x⟩⟩

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_smoothCarrier_metric_with_derivative_orders
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ChartedSpace E X]
    {K : ℕ} [IsManifold 𝓘(ℝ, E) ((K + 1 : ℕ) : ℕ∞ω) X] (hK : 3 ≤ K) :
    letI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
    letI : TopologicalSpace.MetrizableSpace X :=
      TopologicalSpace.metrizableSpace_of_t3_secondCountable X
    letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
    letI : IsManifold 𝓘(ℝ, E) 1 X :=
      IsManifold.of_le (n := ((K + 1 : ℕ) : ℕ∞ω)) (by exact_mod_cast Nat.succ_pos K)
    ∀ G : ContMDiffRiemannianMetric 𝓘(ℝ, E) (K : ℕ∞ω) E
        (TangentSpace 𝓘(ℝ, E) : X → Type _),
      ∃ (s : Set X) (A : SmoothCompatibleAtlas E X s),
        s.Countable ∧
        A.IsCompatible (chartAt E : X → OpenPartialHomeomorph X E) (K + 1) ∧
        (∃ f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier A) X (K + 1),
          ⇑f = SmoothCarrier.toBase A ∧ ⇑f.symm = SmoothCarrier.ofBase A) ∧
        ∃ G' : ContMDiffRiemannianMetric 𝓘(ℝ, E) (K : ℕ∞ω) E
            (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _),
          (∀ (x : SmoothCarrier A) (v w : E),
            G'.inner x v w = G.inner (SmoothCarrier.toBase A x)
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w)) ∧
          (letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) :=
             ⟨G.toRiemannianMetric⟩
           letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _) :=
             ⟨G'.toRiemannianMetric⟩
           (∀ (x : SmoothCarrier A) (v : TangentSpace 𝓘(ℝ, E) x),
              ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v‖ₑ = ‖v‖ₑ) ∧
           (∀ (y : X) (w : TangentSpace 𝓘(ℝ, E) y),
              ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y w‖ₑ = ‖w‖ₑ) ∧
           (∀ (γ : ℝ → SmoothCarrier A) (a b : ℝ),
              (∀ᵐ t ∂volume.restrict (Ioo a b),
                MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) →
              pathELength 𝓘(ℝ, E) (SmoothCarrier.toBase A ∘ γ) a b =
                pathELength 𝓘(ℝ, E) γ a b) ∧
           (∀ (γ : ℝ → X) (a b : ℝ),
              (∀ᵐ t ∂volume.restrict (Ioo a b),
                MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) →
              pathELength 𝓘(ℝ, E) (SmoothCarrier.ofBase A ∘ γ) a b =
                pathELength 𝓘(ℝ, E) γ a b) ∧
           (∀ x y : SmoothCarrier A, riemannianEDist 𝓘(ℝ, E) x y =
              riemannianEDist 𝓘(ℝ, E) (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y)) ∧
           (letI : IsContinuousRiemannianBundle E
                (TangentSpace 𝓘(ℝ, E) : X → Type _) :=
              ⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩
            letI : IsContinuousRiemannianBundle E
                (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _) :=
              ⟨G'.inner, G'.contMDiff.continuous, fun _ _ _ => rfl⟩
            @CompleteSpace (SmoothCarrier A)
                (PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) (SmoothCarrier A)).toUniformSpace ↔
              @CompleteSpace X
                (PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) X).toUniformSpace)) ∧
          (∀ (x : SmoothCarrier A) (v w : TangentSpace 𝓘(ℝ, E) x),
            G'.sectionalCurvature x v w =
              G.sectionalCurvature (SmoothCarrier.toBase A x)
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w)) ∧
          (∀ e : OpenPartialHomeomorph (SmoothCarrier A) E,
            e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ((K + 1 : ℕ) : ℕ∞ω) (SmoothCarrier A) →
            let _ : AddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
            let _ : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
            let b : E → E →L[ℝ] E →L[ℝ] ℝ := fun y =>
              (G'.inner (e.symm y) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
                (E := E) (F := E) (E' := E) (F' := E)
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y : E →L[ℝ] E)
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y : E →L[ℝ] E)
            ContDiffOn ℝ K b e.target ∧
              ContDiffOn ℝ ((K - 1 : ℕ) : ℕ∞ω)
                (fun y => MetricKoszul.raisedKoszulOp (E := E)
                  (b y) (fderiv ℝ b y)) e.target ∧
              ∀ v w z u : E, ContDiffOn ℝ ((K - 2 : ℕ) : ℕ∞ω)
                (fun y => DifferentialGeometry.Analysis.coefficientRm04 b y v w z u) e.target) ∧
          IsOpen G'.geodesicFlowDomain ∧
          ContMDiffOn (𝓘(ℝ, E).tangent.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E).tangent
            ((K - 1 : ℕ) : ℕ∞ω)
            (fun p : TangentBundle 𝓘(ℝ, E) (SmoothCarrier A) × ℝ =>
              G'.geodesicFlow p.1 p.2) G'.geodesicFlowDomain ∧
          (∀ p : TangentBundle 𝓘(ℝ, E) (SmoothCarrier A),
            (p, 0) ∈ G'.geodesicFlowDomain ∧ G'.geodesicFlow p 0 = p) ∧
          IsOpen G'.expDomain ∧
          ContMDiffOn 𝓘(ℝ, E).tangent 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω)
            G'.expMap G'.expDomain ∧
          ∀ x : SmoothCarrier A,
            (⟨x, 0⟩ : TangentBundle 𝓘(ℝ, E) (SmoothCarrier A)) ∈ G'.expDomain ∧
            G'.expMap (⟨x, 0⟩ : TangentBundle 𝓘(ℝ, E) (SmoothCarrier A)) = x := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
  let : TopologicalSpace.MetrizableSpace X :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let : IsManifold 𝓘(ℝ, E) 1 X :=
    IsManifold.of_le (n := ((K + 1 : ℕ) : ℕ∞ω)) (by exact_mod_cast Nat.succ_pos K)
  intro G
  obtain ⟨s, A, hs, hA, hf, G', hpull, hmetric, hsec⟩ :=
    exists_smoothCarrier_metric_of_secondCountable (E := E) (X := X) (K := K)
      (by omega) G
  refine ⟨s, A, hs, hA, hf, G', hpull, hmetric, hsec, ?_, ?_⟩
  · intro e he
    exact G'.contDiffOn_chart_inner_derivatives le_rfl (by omega) e he
  · have horder : (K : ℕ∞ω) = (((K - 1 : ℕ) : ℕ∞) : ℕ∞ω) + 1 := by
      rw [WithTop.coe_natCast]
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ K)).symm
    simpa only [WithTop.coe_natCast] using
      finite_geodesic_regularities G' ((K - 1 : ℕ) : ℕ∞) horder
        (by exact_mod_cast (show 1 ≤ K - 1 by omega))

end DifferentialGeometry.Topology.Manifold
