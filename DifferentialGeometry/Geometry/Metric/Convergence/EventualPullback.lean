import DifferentialGeometry.Geometry.Metric.Convergence.CoefficientBridge
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

section

open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E F H G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M]

theorem PartialDiffeomorph.isLocalDiffeomorph_restrict_open_of_eqOn
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    (Φ : PartialDiffeomorph I J M N ∞) {W : TopologicalSpace.Opens M}
    (hW : (W : Set M) ⊆ Φ.source) {f : M → N}
    (hf : Set.EqOn (Φ : M → N) f Φ.source) :
    IsLocalDiffeomorph I J ∞ (fun x : W => f x) := by
  apply isLocalDiffeomorph_restrict_open W
  intro x
  exact ⟨Φ, hW x.property, hf.symm⟩

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  {ι : Type*} {N : ι → Type*} [∀ k, TopologicalSpace (N k)]
  [∀ k, ChartedSpace G (N k)] [∀ k, IsManifold J ∞ (N k)]

theorem exists_eventually_pullback_metric_restrict_open
    (W : TopologicalSpace.Opens M) [T2Space W]
    (g₀ : SmoothRiemannianMetric I W) (g : ∀ k, SmoothRiemannianMetric J (N k))
    (f : ∀ k, M → N k) {l : Filter ι}
    (hf : ∀ᶠ k in l, ∃ Φ : PartialDiffeomorph I J M (N k) ∞,
      (W : Set M) ⊆ Φ.source ∧ Set.EqOn (Φ : M → N k) (f k) Φ.source) :
    ∃ Gseq : ι → SmoothRiemannianMetric I W, ∀ᶠ k in l,
      ContMDiff I J ∞ (fun x : W => f k x) ∧
      ∀ (x : W) (v w : TangentSpace I x),
        (Gseq k).inner x v w =
          (g k).inner (f k x) (mfderiv I J (f k) (x : M) v)
            (mfderiv I J (f k) (x : M) w) := by
  classical
  let Gseq : ι → SmoothRiemannianMetric I W := fun k =>
    if h : IsLocalDiffeomorph I J ∞ (fun x : W => f k x) then
      (g k).pullback (fun x : W => f k x) h.contMDiff (fun x => by
        rw [← h.mfderivToContinuousLinearEquiv_coe (by decide)]
        exact (h.mfderivToContinuousLinearEquiv (by decide) x).injective)
    else g₀
  refine ⟨Gseq, hf.mono ?_⟩
  rintro k ⟨Φ, hW, hΦ⟩
  have hk := PartialDiffeomorph.isLocalDiffeomorph_restrict_open_of_eqOn Φ hW hΦ
  refine ⟨hk.contMDiff, ?_⟩
  intro x v w
  simp only [Gseq, dif_pos hk, SmoothRiemannianMetric.pullback_inner,
    mfderiv_restrict_open]
  rfl

end DifferentialGeometry

end

section

set_option autoImplicit false
noncomputable section
open Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F H}
  {N : ℕ → Type*} [∀ k, TopologicalSpace (N k)] [∀ k, ChartedSpace H (N k)]
  [∀ k, IsManifold J ∞ (N k)]

theorem metricCInfConvergenceOnCompacts_of_eventual_pullback_coefficients
    {ι : Type*} (U : ι → TopologicalSpace.Opens E)
    (j : ∀ i, U i → M) (hj : ∀ i, IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (j i))
    (hinj : ∀ i, Function.Injective (j i)) (hcover : ∀ x : M, ∃ i z, j i z = x)
    (jbar : ι → E → M) (hjbar : ∀ i (z : U i), jbar i (z : E) = j i z)
    (g : ∀ k, SmoothRiemannianMetric J (N k)) (P : ∀ k, M → N k)
    (G : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (gInf : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hP : ∀ᶠ k in atTop, ContMDiff 𝓘(ℝ, E) J ∞ (P k))
    (hG : ∀ᶠ k in atTop, ∀ (x : M) (v w : TangentSpace 𝓘(ℝ, E) x),
      (G k).inner x v w = (g k).inner (P k x)
        (mfderiv 𝓘(ℝ, E) J (P k) x v) (mfderiv 𝓘(ℝ, E) J (P k) x w))
    (hconv : ∀ i, MapCInfConvergenceOnCompacts (U i : Set E)
      (fun k => Geometry.pullbackMetricCoefficients (g k) (P k ∘ jbar i))
      (Geometry.pullbackMetricCoefficients gInf (jbar i))) :
    MetricCInfConvergenceOnCompacts G gInf gInf := by
  apply metricCInfConvergenceOnCompacts_of_pullback_coefficients U j hj hinj hcover jbar hjbar G gInf
  intro i
  apply (hconv i).congr_eventually (U i).isOpen
  · filter_upwards [hP, hG] with k hk hGk
    intro z hz
    have hjbar' : (fun z : U i => jbar i z) = j i := funext (hjbar i)
    have hdj : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (jbar i) z := by
      have h := (hj i).contMDiff.contMDiffAt (x := (⟨z, hz⟩ : U i))
      rw [← hjbar'] at h
      exact contMDiffAt_subtype_iff.mp h
    have hc := mfderiv_comp z (hk.mdifferentiableAt (by simp))
      (hdj.mdifferentiableAt (by simp))
    ext v w
    rw [Geometry.pullbackMetricCoefficients_apply, Geometry.pullbackMetricCoefficients_apply]
    rw [hGk (jbar i z) _ _]
    rw [hc]
    rfl
  · exact fun _ _ => rfl

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false
noncomputable section
open Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F H}
  {N : ℕ → Type*} [∀ k, TopologicalSpace (N k)] [∀ k, ChartedSpace H (N k)]
  [∀ k, IsManifold J ∞ (N k)]

theorem exists_metricCInfConvergenceOnCompacts_of_eventual_partial_pullback_coefficients
    (W : TopologicalSpace.Opens M) [T2Space W]
    {ι : Type*} (U : ι → TopologicalSpace.Opens E)
    (j : ∀ i, U i → W) (hj : ∀ i, IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (j i))
    (hinj : ∀ i, Function.Injective (j i)) (hcover : ∀ x : W, ∃ i z, j i z = x)
    (jbar : ι → E → W) (hjbar : ∀ i (z : U i), jbar i (z : E) = j i z)
    (g : ∀ k, SmoothRiemannianMetric J (N k)) (f : ∀ k, M → N k)
    (gInf : SmoothRiemannianMetric 𝓘(ℝ, E) W)
    (hpartial : ∀ᶠ k in atTop, ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) J M (N k) ∞,
      (W : Set M) ⊆ Φ.source ∧ Set.EqOn (Φ : M → N k) (f k) Φ.source)
    (hconv : ∀ i, MapCInfConvergenceOnCompacts (U i : Set E)
      (fun k => Geometry.pullbackMetricCoefficients (g k) (fun z => f k (jbar i z)))
      (Geometry.pullbackMetricCoefficients gInf (jbar i))) :
    ∃ G : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) W,
      (∀ᶠ k in atTop, ContMDiff 𝓘(ℝ, E) J ∞ (fun x : W => f k x) ∧
        ∀ (x : W) (v w : TangentSpace 𝓘(ℝ, E) x),
          (G k).inner x v w = (g k).inner (f k x)
            (mfderiv 𝓘(ℝ, E) J (f k) (x : M) v)
            (mfderiv 𝓘(ℝ, E) J (f k) (x : M) w)) ∧
      MetricCInfConvergenceOnCompacts G gInf gInf := by
  obtain ⟨G, hG⟩ := exists_eventually_pullback_metric_restrict_open W gInf g f hpartial
  refine ⟨G, hG, ?_⟩
  apply metricCInfConvergenceOnCompacts_of_eventual_pullback_coefficients U j hj hinj hcover
    jbar hjbar g (fun k (x : W) => f k x) G gInf (hG.mono fun _ h => h.1)
    (hconv := hconv)
  filter_upwards [hG] with k hk
  intro x v w
  rw [mfderiv_restrict_open]
  exact hk.2 x v w

end DifferentialGeometry.CheegerGromovCompactness

end

end
