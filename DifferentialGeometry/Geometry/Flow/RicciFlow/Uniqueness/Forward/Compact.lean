import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.SmoothSolutions
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Convergence.PullbackCross
import DifferentialGeometry.Geometry.Metric.ModelChange

noncomputable section

open Bundle Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

section InnerProductModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

private theorem compact_ricci_flow_unique_inner_product
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1pde : ∀ t ∈ Set.Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Set.Ici a) t)
    (h2pde : ∀ t ∈ Set.Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Set.Ici a) t)
    (h0 : g₁ a = g₂ a) :
    ∀ t ∈ Set.Ico a b, g₁ t = g₂ t := by
  exact forward_unique_of_gram (I := I) g₁ g₂ hab
    h1smooth h2smooth h1pde h2pde h0
    (fuSlab_of_gram (I := I) g₁ g₂ h1smooth h2smooth h1pde h2pde)
    (energyEdgeCont (I := I) g₁ g₂ hab h1smooth h2smooth)

end InnerProductModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

theorem ricci_flow_forward_unique_of_joint_contMDiffOn
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (h1smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g₁ p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a b ×ˢ (Set.univ : Set M)))
    (h2smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g₂ p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a b ×ˢ (Set.univ : Set M)))
    (h1pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g₁ s).inner x v w)
        (-2 * ricciTensor (g₁ t) x v w) (Ici a) t)
    (h2pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g₂ s).inner x v w)
        (-2 * ricciTensor (g₂ t) x v w) (Ici a) t)
    (hinit : g₁ a = g₂ a) : ∀ t ∈ Ico a b, g₁ t = g₂ t := by
  by_cases hE : Module.finrank ℝ E = 0
  · let _ : Subsingleton E := Module.finrank_zero_iff.mp hE
    intro t ht
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    let _ : Subsingleton (TangentSpace I x) := by unfold TangentSpace; infer_instance
    have hv : v = 0 := Subsingleton.elim _ _
    rw [hv]
    simp
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hE⟩
    let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
      (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
        (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
    let J := I.transContinuousLinearEquiv e
    let Φ := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
    let k₁ : ℝ → SmoothRiemannianMetric J M := fun t => (g₁ t).transContinuousLinearEquiv e
    let k₂ : ℝ → SmoothRiemannianMetric J M := fun t => (g₂ t).transContinuousLinearEquiv e
    let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
      ⟨by simpa using (NeZero.ne (Module.finrank ℝ E))⟩
    have hk₁ := chartGramMatrix_joint_contMDiffOn_of_pullback g₁ (Ico a b) h1smooth k₁
      Φ.symm Φ.symm.contMDiff (fun t _ x v w =>
        Diffeomorph.pullbackMetricCross_inner (g₁ t) Φ.symm x v w)
    have hk₂ := chartGramMatrix_joint_contMDiffOn_of_pullback g₂ (Ico a b) h2smooth k₂
      Φ.symm Φ.symm.contMDiff (fun t _ x v w =>
        Diffeomorph.pullbackMetricCross_inner (g₂ t) Φ.symm x v w)
    have hp₁ : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace J x,
        HasDerivWithinAt (fun s : ℝ => (k₁ s).inner x v w)
          (-2 * ricciTensor (k₁ t) x v w) (Ici a) t := by
      intro t ht x v w
      change HasDerivWithinAt
        (fun s => (Diffeomorph.pullbackMetricCross (g₁ s) Φ.symm).inner x v w)
        (-2 * ricciTensor (Diffeomorph.pullbackMetricCross (g₁ t) Φ.symm) x v w) (Ici a) t
      simpa only [Diffeomorph.pullbackMetricCross_inner,
        DifferentialGeometry.HCGCompactness.ricciTensor_cross] using
        h1pde t ht (Φ.symm x) (mfderiv J I Φ.symm x v) (mfderiv J I Φ.symm x w)
    have hp₂ : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace J x,
        HasDerivWithinAt (fun s : ℝ => (k₂ s).inner x v w)
          (-2 * ricciTensor (k₂ t) x v w) (Ici a) t := by
      intro t ht x v w
      change HasDerivWithinAt
        (fun s => (Diffeomorph.pullbackMetricCross (g₂ s) Φ.symm).inner x v w)
        (-2 * ricciTensor (Diffeomorph.pullbackMetricCross (g₂ t) Φ.symm) x v w) (Ici a) t
      simpa only [Diffeomorph.pullbackMetricCross_inner,
        DifferentialGeometry.HCGCompactness.ricciTensor_cross] using
        h2pde t ht (Φ.symm x) (mfderiv J I Φ.symm x v) (mfderiv J I Φ.symm x w)
    have hkinit : k₁ a = k₂ a := congrArg (fun g => g.transContinuousLinearEquiv e) hinit
    have hunique := compact_ricci_flow_unique_inner_product k₁ k₂ hab hk₁ hk₂ hp₁ hp₂ hkinit
    intro t ht
    have h := congrArg (fun g => Diffeomorph.pullbackMetricCross g Φ) (hunique t ht)
    simpa only [k₁, k₂, Φ, SmoothRiemannianMetric.pullback_transContinuousLinearEquiv] using h

end DifferentialGeometry.PDE.RicciFlow
