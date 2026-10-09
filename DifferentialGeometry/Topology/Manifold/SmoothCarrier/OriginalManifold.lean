import DifferentialGeometry.Topology.Manifold.SmoothCompatibleAtlas.Lindelof
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.IntrinsicSectional
import Mathlib.Topology.Metrizable.Urysohn

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Topology.Manifold

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_smoothCarrier_metric_of_secondCountable
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ChartedSpace E X]
    {K : ℕ} [IsManifold 𝓘(ℝ, E) ((K + 1 : ℕ) : ℕ∞ω) X] (hK : 2 ≤ K) :
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
          ∀ (x : SmoothCarrier A) (v w : TangentSpace 𝓘(ℝ, E) x),
            G'.sectionalCurvature x v w =
              G.sectionalCurvature (SmoothCarrier.toBase A x)
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w) := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
  let : TopologicalSpace.MetrizableSpace X :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let : IsManifold 𝓘(ℝ, E) 1 X :=
    IsManifold.of_le (n := ((K + 1 : ℕ) : ℕ∞ω)) (by exact_mod_cast Nat.succ_pos K)
  intro G
  let : IsManifold 𝓘(ℝ, E) 3 X :=
    IsManifold.of_le (n := ((K + 1 : ℕ) : ℕ∞ω))
      (by exact_mod_cast Nat.succ_le_succ hK)
  obtain ⟨s, hs, _, A, _, _, _, _, _, _, hA⟩ :=
    exists_smoothCompatibleAtlas_of_lindelof (E := E) (X := X) (r := K + 1)
      (Nat.succ_pos K)
  have hto : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) (K + 1) (SmoothCarrier.toBase A) :=
    SmoothCarrier.contMDiff_toBase_of_chartAt A (chartAt E) (fun y => mem_range_self y) hA
  have hfrom : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) (K + 1) (SmoothCarrier.ofBase A) :=
    SmoothCarrier.contMDiff_ofBase_of_chartAt A (chartAt E) (fun y => mem_range_self y) hA
  let f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier A) X (K + 1) :=
    ⟨SmoothCarrier.equivBase A,
      by simpa only [SmoothCarrier.coe_equivBase] using hto,
      by simpa only [SmoothCarrier.coe_equivBase_symm] using hfrom⟩
  obtain ⟨G', hpull, hrest, hsec⟩ :=
    SmoothCarrier.exists_pullback_metric_with_sectional_curvature_of_chartAt
      A K (K + 1) K le_rfl le_rfl hK hA G
  refine ⟨s, A, hs, hA, ⟨f, rfl, rfl⟩, G', hpull, ?_, hsec⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) :=
    ⟨G.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _) :=
    ⟨G'.toRiemannianMetric⟩
  obtain ⟨hnorm, hnorm', hpath, hpath', hedist, _, _⟩ := hrest
  refine ⟨hnorm, hnorm', hpath, hpath', hedist, ?_⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : X → Type _) :=
    ⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : IsContinuousRiemannianBundle E
      (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _) :=
    ⟨G'.inner, G'.contMDiff.continuous, fun _ _ _ => rfl⟩
  let mX : PseudoEMetricSpace X := .ofRiemannianMetric 𝓘(ℝ, E) X
  let mA : PseudoEMetricSpace (SmoothCarrier A) :=
    .ofRiemannianMetric 𝓘(ℝ, E) (SmoothCarrier A)
  let e : @IsometryEquiv (SmoothCarrier A) X mA mX :=
    { toEquiv := SmoothCarrier.equivBase A
      isometry_toFun := fun x y => (hedist x y).symm }
  exact e.completeSpace_iff

end DifferentialGeometry.Topology.Manifold
