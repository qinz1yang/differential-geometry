import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.IntrinsicOverlap
import DifferentialGeometry.Geometry.Exponential.NormalBall.Recenter
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Configuration

noncomputable section
open Set Filter Bundle
open scoped ContDiff Manifold Topology ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, PseudoEMetricSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem IntrinsicBallChart.eventually_mapsTo_target_of_near
    {ι : Type*} [Finite ι]
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ s : ℝ} (hρ : 0 < ρ) (hs : s ≤ 3 * ρ / 4)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool) (j : ι)
    (hnear : ∀ i, ∀ᶠ k in atTop,
      near j i = true → edist (x j k) (x i k) < ENNReal.ofReal (ρ / 4)) :
    ∀ᶠ k in atTop, ∀ i, near j i = true →
      MapsTo (c i k).hom (Metric.ball (0 : E) s) (c j k).hom.target := by
  filter_upwards [(Filter.eventually_all).2 hnear] with k hk i hi
  have hdist : edist (x i k) (x j k) + ENNReal.ofReal s ≤ ENNReal.ofReal ρ := by
    by_cases hs0 : 0 ≤ s
    · rw [edist_comm]
      calc
        edist (x j k) (x i k) + ENNReal.ofReal s ≤
            ENNReal.ofReal (ρ / 4) + ENNReal.ofReal s := add_le_add (hk i hi).le le_rfl
        _ = ENNReal.ofReal (ρ / 4 + s) :=
          (ENNReal.ofReal_add (by positivity) hs0).symm
        _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal (by linarith)
    · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hs0), add_zero, edist_comm]
      exact (hk i hi).le.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hov := (c i k).overlap_on_ball_of_edist_add_le
    (g k) (hEnorm k) (x i k) (x j k) (c j k) hρ hρ (by linarith) hdist
  intro z hz
  obtain ⟨w, hw, heq⟩ := (hov z hz).2
  change (c j k).hom w = (c i k).hom z at heq
  change w ∈ Metric.ball (0 : E) ρ at hw
  rw [← heq]
  exact (c j k).hom.map_source (by rw [(c j k).source_eq]; exact hw)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end

noncomputable section
open Set Filter
open scoped ContDiff Manifold Topology
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open DifferentialGeometry.CheegerGromovCompactness

variable {E P H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]

theorem eventually_recenter_apply_eq_of_configuration_convergence
    {p : ∀ k, M k} (c : ∀ k, NormalBallChart (I := I) (p k))
    (a : E) {r : ℝ} (hr : 0 < r)
    (hball : ∀ k, Metric.ball a r ⊆ Metric.ball (0 : E) (c k).radius)
    {ι : Type*} [Fintype ι] {S K : Set P}
    {configuration : ℕ → P → (ι → ℝ) × (ι → E)}
    {mu : P → ι → ℝ} {center : P → E}
    (hcfg : MapCInfConvergenceOnCompacts S configuration
      (fun q => (mu q, fun _ => center q)))
    (hK : IsCompact K) (hKS : K ⊆ S) (hcenter : ContinuousOn center K)
    (hcenterBall : MapsTo center K (Metric.ball (0 : E) r))
    (atoms : ∀ k, P → ι → M k)
    (htarget : ∀ᶠ k in atTop, ∀ q ∈ K, ∀ i, mu q i ≠ 0 →
      atoms k q i ∈ (c k).hom.target)
    (hcoords : ∀ᶠ k in atTop, ∀ q ∈ K, ∀ i, mu q i ≠ 0 →
      (configuration k q).2 i = -a + (c k).inv (atoms k q i)) :
    ∀ᶠ k in atTop, ∀ q ∈ K, ∀ i, mu q i ≠ 0 →
      ((c k).recenter a hr (hball k)).hom ((configuration k q).2 i) = atoms k q i ∧
      ((c k).recenter a hr (hball k)).inv (atoms k q i) = (configuration k q).2 i ∧
      atoms k q i ∈ ((c k).recenter a hr (hball k)).restrictBall.target := by
  let L : Set (P × E) := (fun q : P => (q, (0 : E))) '' K
  have hL : IsCompact L := hK.image_of_continuousOn
    (continuous_id.prodMk continuous_const).continuousOn
  have hLK : Prod.fst '' L = K := by
    ext q
    constructor
    · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      exact hz
    · intro hq
      exact ⟨(q, 0), ⟨q, hq, rfl⟩, rfl⟩
  have hfst : MapsTo Prod.fst L S := by
    rintro _ ⟨q, hq, rfl⟩
    exact hKS hq
  have hpair := hcfg.eventually_configuration_pairs_mem hL hfst
    (hLK ▸ hcenter) (isOpen_univ.prod Metric.isOpen_ball)
    (show MapsTo (fun q : P × E => (q.2, center q.1)) L
      (Set.univ ×ˢ Metric.ball (0 : E) r) from by
        rintro _ ⟨q, hq, rfl⟩
        exact ⟨Set.mem_univ _, hcenterBall hq⟩)
  filter_upwards [hpair, htarget, hcoords] with k hk ht hc q hq i hi
  exact (c k).recenter_apply_inv_of_mem_target a hr (hball k) (ht q hq i hi)
    (hk (q, 0) ⟨q, hq, rfl⟩ i).2 (hc q hq i hi)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
end
