import DifferentialGeometry.Geometry.Metric.Convergence.OpenCover
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.SourceConvergence

section

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
variable {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, PseudoEMetricSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem IntrinsicBallChart.exists_metricCInfConvergenceOnCompacts_of_chart_convergence
    {ι : Type*} (U : ι → TopologicalSpace.Opens E) {ρ : ℝ}
    (hUρ : ∀ i, (U i : Set E) ⊆ Metric.ball (0 : E) ρ)
    (j : ∀ i, U i → Q) (hj : ∀ i, IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (j i))
    (hinj : ∀ i, Function.Injective (j i))
    (V : TopologicalSpace.Opens Q) [T2Space V]
    (hcover : ∀ x : V, ∃ i z, j i z = (x : Q))
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (gQ : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (p : ι → ∀ k, M k)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p i k) ρ)
    (F : ∀ k, Q → M k)
    (B : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) ρ)
      (fun k => intrinsicFrameMetric (g k) (hEnorm k) (p i k)) (B i))
    (hBC : ∀ i, ContDiffOn ℝ ∞ (B i) (Metric.ball (0 : E) ρ))
    (hmetric : ∀ i (z : U i) (v w : E),
      gQ.inner (j i z) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (j i) z v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (j i) z w) = B i z v w)
    (hcapture : ∀ i K, IsCompact K → K ⊆ Subtype.val '' ((j i) ⁻¹' (V : Set Q)) →
      ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U i), z ∈ K →
        F k (j i ⟨z, hz⟩) ∈ (c i k).hom.target)
    (hcoord : ∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Subtype.val '' ((j i) ⁻¹' (V : Set Q)))
      (fun k z => @dite E (z ∈ U i) (Classical.propDecidable _)
        (fun hz => (c i k).hom.symm (F k (j i ⟨z, hz⟩))) (fun _ => 0)) id)
    (hpartial : ∀ᶠ k in atTop, ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I Q (M k) ∞,
      (V : Set Q) ⊆ Φ.source ∧ Set.EqOn (Φ : Q → M k) (F k) Φ.source) :
    ∃ G : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) V,
      (∀ᶠ k in atTop, ContMDiff 𝓘(ℝ, E) I ∞ (fun x : V => F k x) ∧
        ∀ (x : V) (v w : TangentSpace 𝓘(ℝ, E) x),
          (G k).inner x v w = (g k).inner (F k x)
            (mfderiv 𝓘(ℝ, E) I (F k) (x : Q) v)
            (mfderiv 𝓘(ℝ, E) I (F k) (x : Q) w)) ∧
      CheegerGromovCompactness.MetricCInfConvergenceOnCompacts
        G (gQ.restrictOpen V) (gQ.restrictOpen V) := by
  classical
  by_cases hV : Nonempty V
  · let p₀ : V := Classical.choice hV
    let jbar : ι → E → Q := fun i z => if hz : z ∈ U i then j i ⟨z, hz⟩ else p₀
    have hjbar (i : ι) (z : U i) : jbar i z = j i z := dif_pos z.property
    apply CheegerGromovCompactness.exists_metricCInfConvergenceOnCompacts_restrict_open_of_local_coefficients
      U j hj hinj jbar hjbar V hcover g F gQ hpartial
    have hF : ∀ᶠ k in atTop, ContMDiffOn 𝓘(ℝ, E) I ∞ (F k) V :=
      hpartial.mono fun k ⟨Φ, hVΦ, hΦF⟩ => (Φ.contMDiffOn.congr hΦF.symm).mono hVΦ
    let F' : ∀ k, Q → M k := fun k =>
      if ContMDiffOn 𝓘(ℝ, E) I ∞ (F k) V then F k else fun _ => F k p₀
    have hF' : ∀ k, ContMDiffOn 𝓘(ℝ, E) I ∞ (F' k) V := by
      intro k
      dsimp only [F']
      split_ifs with h
      · exact h
      · exact contMDiffOn_const
    have hF'eq : ∀ᶠ k in atTop, F' k = F k := hF.mono fun k hk => if_pos hk
    intro i
    have hdom : IsOpen (Subtype.val '' ((j i) ⁻¹' (V : Set Q))) :=
      (U i).isOpen.isOpenMap_subtype_val _ (V.isOpen.preimage (hj i).contMDiff.continuous)
    have hcapture' : ∀ K, IsCompact K → K ⊆ Subtype.val '' ((j i) ⁻¹' (V : Set Q)) →
        ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U i), z ∈ K →
          F' k (j i ⟨z, hz⟩) ∈ (c i k).hom.target := by
      intro K hK hKV
      filter_upwards [hcapture i K hK hKV, hF'eq] with k hk heq
      simpa only [heq] using hk
    have hcoord' : CheegerGromovCompactness.MapCInfConvergenceOnCompacts
        (Subtype.val '' ((j i) ⁻¹' (V : Set Q)))
        (fun k z => @dite E (z ∈ U i) (Classical.propDecidable _)
          (fun hz => (c i k).hom.symm (F' k (j i ⟨z, hz⟩))) (fun _ => 0)) id :=
      (hcoord i).congr_eventually hdom
        (hF'eq.mono fun k hk z hz => by rw [hk]) (fun _ _ => rfl)
    have hcoef := IntrinsicBallChart.pullbackMetricCoefficients_convergence_of_local_inclusion
      (U i) (hUρ i) (j i) (hj i).contMDiff (jbar i) (hjbar i) V g gQ hEnorm
      (p i) (c i) F' hF' (hB i) (hBC i) (hmetric i) hcapture' hcoord'
    exact hcoef.congr_eventually hdom
      (hF'eq.mono fun k hk z hz => by rw [hk]) (fun _ _ => rfl)
  · obtain ⟨G, hG⟩ :=
      exists_eventually_pullback_metric_restrict_open V (gQ.restrictOpen V) g F hpartial
    refine ⟨G, hG, ?_⟩
    intro K hK p ε hε
    refine ⟨0, fun k hk => ?_⟩
    have hKempty : K = (∅ : Set V) := by
      ext x
      exact (hV ⟨x⟩).elim
    subst K
    simpa [CheegerGromovCompactness.metricDerivNormSupOn] using hε

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end
