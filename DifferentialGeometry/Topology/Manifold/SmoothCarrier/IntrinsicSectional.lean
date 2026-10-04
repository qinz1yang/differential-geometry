import DifferentialGeometry.Topology.Manifold.SmoothCarrier.OriginalMetric
import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Topology.Manifold

theorem SmoothCarrier.sectionalCurvature_toBase_of_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [MetricSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) 3 X]
    {ι : Type*} (A : SmoothCompatibleAtlas E X ι)
    (hA : A.IsCompatible (chartAt E : X → OpenPartialHomeomorph X E) 3)
    {n m : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E
      (TangentSpace 𝓘(ℝ, E) : X → Type _))
    (G' : ContMDiffRiemannianMetric 𝓘(ℝ, E) m E
      (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _))
    (hn : (2 : ℕ∞ω) ≤ n) (hm : (2 : ℕ∞ω) ≤ m)
    (hG' : ∀ (x : SmoothCarrier A) (v w : E),
      G'.inner x v w = G.inner (SmoothCarrier.toBase A x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w))
    (x : SmoothCarrier A) (v w : TangentSpace 𝓘(ℝ, E) x) :
    G'.sectionalCurvature x v w =
      G.sectionalCurvature (SmoothCarrier.toBase A x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w) := by
  have hCs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 (SmoothCarrier.toBase A) :=
    SmoothCarrier.contMDiff_toBase_of_chartAt A (chartAt E) (fun y => mem_range_self y) hA
  have hCs' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 (SmoothCarrier.ofBase A) :=
    SmoothCarrier.contMDiff_ofBase_of_chartAt A (chartAt E) (fun y => mem_range_self y) hA
  let f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier A) X 3 :=
    ⟨SmoothCarrier.equivBase A,
      by simpa only [SmoothCarrier.coe_equivBase] using hCs,
      by simpa only [SmoothCarrier.coe_equivBase_symm] using hCs'⟩
  exact ContMDiffRiemannianMetric.sectionalCurvature_eq_of_pullback G' G hm hn f
    (fun q a b => hG' q a b) x v w

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem SmoothCarrier.exists_pullback_metric_with_sectional_curvature_of_chartAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [MetricSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) 3 X]
    {ι : Type*} (A : SmoothCompatibleAtlas E X ι) (K s r : ℕ)
    (hrK : r ≤ K) (hrs : r + 1 ≤ s) (hr : 2 ≤ r)
    (hA : A.IsCompatible (chartAt E : X → OpenPartialHomeomorph X E) s)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) (K : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : X → Type _)) :
    ∃ G' : ContMDiffRiemannianMetric 𝓘(ℝ, E) (r : ℕ∞ω) E
        (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _),
      (∀ (x : SmoothCarrier A) (v w : E),
        G'.inner x v w = G.inner (SmoothCarrier.toBase A x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w)) ∧
      (letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) := ⟨G.toRiemannianMetric⟩
       letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _) :=
         ⟨G'.toRiemannianMetric⟩
       (∀ (x : SmoothCarrier A) (v : TangentSpace 𝓘(ℝ, E) x),
          ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v‖ₑ = ‖v‖ₑ) ∧
       (∀ (y : X) (w : TangentSpace 𝓘(ℝ, E) y),
          ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) y w‖ₑ = ‖w‖ₑ) ∧
       (∀ (γ : ℝ → SmoothCarrier A) (a b : ℝ),
          (∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) →
          pathELength 𝓘(ℝ, E) (SmoothCarrier.toBase A ∘ γ) a b =
            pathELength 𝓘(ℝ, E) γ a b) ∧
       (∀ (γ : ℝ → X) (a b : ℝ),
          (∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) →
          pathELength 𝓘(ℝ, E) (SmoothCarrier.ofBase A ∘ γ) a b =
            pathELength 𝓘(ℝ, E) γ a b) ∧
       (∀ x y : SmoothCarrier A, riemannianEDist 𝓘(ℝ, E) x y =
          riemannianEDist 𝓘(ℝ, E) (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y)) ∧
       (∀ x y : SmoothCarrier A,
          dist x y = dist (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y)) ∧
       (IsRiemannianManifold 𝓘(ℝ, E) X → IsRiemannianManifold 𝓘(ℝ, E) (SmoothCarrier A))) ∧
      ∀ (x : SmoothCarrier A) (v w : TangentSpace 𝓘(ℝ, E) x),
        G'.sectionalCurvature x v w =
          G.sectionalCurvature (SmoothCarrier.toBase A x)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w) := by
  obtain ⟨G', hG', hrest⟩ :=
    SmoothCarrier.exists_pullback_metric_of_chartAt A K s r hrK hrs hA G
  have hs : (3 : ℕ∞ω) ≤ (s : ℕ∞ω) := by
    exact_mod_cast (Nat.succ_le_succ hr).trans hrs
  have hA3 : A.IsCompatible (chartAt E : X → OpenPartialHomeomorph X E) 3 := by
    intro i j
    exact ⟨(hA i j).1.of_le hs, (hA i j).2.of_le hs⟩
  refine ⟨G', hG', hrest, ?_⟩
  exact SmoothCarrier.sectionalCurvature_toBase_of_pullback A hA3 G G'
    (by exact_mod_cast hr.trans hrK) (by exact_mod_cast hr) hG'

end DifferentialGeometry.Topology.Manifold

end

set_option autoImplicit false

noncomputable section

open Set Bundle Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

open DifferentialGeometry.Analysis

theorem SmoothCarrier.sectionalCurvature_nonneg_of_chart_coefficients
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [MetricSpace X] {ι : Type*} (A : SmoothCompatibleAtlas E X ι)
    {m : ℕ∞ω}
    (G' : ContMDiffRiemannianMetric 𝓘(ℝ, E) m E
      (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _))
    (hm : (2 : ℕ∞ω) ≤ m) (c : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hreal : ∀ j, ∀ y ∈ (A.chart j).target, ∀ v w : E,
      G'.inner ((SmoothCarrier.chart A j).symm y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j).symm y v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j).symm y w) = c j y v w)
    (hsign : ∀ j, ∀ y ∈ (A.chart j).target, ∀ v w : E,
      0 ≤ coefficientSectional (c j) y v w)
    (x : SmoothCarrier A) (v w : TangentSpace 𝓘(ℝ, E) x) :
    0 ≤ G'.sectionalCurvature x v w := by
  obtain ⟨j, hj⟩ := A.mem_source (SmoothCarrier.toBase A x)
  have hx : x ∈ (SmoothCarrier.chart A j).source :=
    (SmoothCarrier.mem_chart_source_iff A j x).mpr hj
  have hθ : SmoothCarrier.chart A j ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 3
      (SmoothCarrier A) :=
    IsManifold.subset_maximalAtlas (⟨j, rfl⟩ : SmoothCarrier.chart A j ∈ atlas E (SmoothCarrier A))
  let e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier A) E 3 :=
    { toPartialEquiv := (SmoothCarrier.chart A j).toPartialEquiv
      open_source := (SmoothCarrier.chart A j).open_source
      open_target := (SmoothCarrier.chart A j).open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hθ
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hθ }
  let B : E → E →L[ℝ] E →L[ℝ] ℝ := fun y =>
    (G'.inner (e.symm y) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y : E →L[ℝ] E)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y : E →L[ℝ] E)
  have hB : B =ᶠ[𝓝 (e x)] c j := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    ext a b
    exact hreal j y hy a b
  have hGram : coefficientGram B =ᶠ[𝓝 (e x)] coefficientGram (c j) :=
    hB.mono fun y hy => congrArg (coefficientGramCLM E) hy
  rw [G'.sectionalCurvature_eq_coefficientSectional hm e hx]
  change 0 ≤ coefficientSectional B (e x)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x w)
  have heq : ∀ a b : E, coefficientSectional B (e x) a b =
      coefficientSectional (c j) (e x) a b := by
    intro a b
    unfold coefficientSectional coefficientRm04
    rw [jet2_congr_of_eventuallyEq hGram, hB.eq_of_nhds]
  let a : E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v
  let b : E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x w
  change 0 ≤ coefficientSectional B (e x) a b
  exact (heq a b).symm ▸ hsign j (e x) (e.map_source hx) a b

end DifferentialGeometry.Topology.Manifold

end
