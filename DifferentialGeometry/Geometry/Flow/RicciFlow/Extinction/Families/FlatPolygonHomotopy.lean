import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlatPolygonApproximation

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [T2Space Q] [CompactSpace Q] [ConnectedSpace Q] [I.Boundaryless]

theorem exists_uniform_flatPolygon_embedding_error {K : Type*} [TopologicalSpace K]
    [CompactSpace K] (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) K) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ k z,
      dist (e.map (flatPolygon g P n (Γ k).1 z)) (e.map ((Γ k).1 z)) < epsilon := by
  obtain ⟨L, hL, _⟩ := regularFamily_uniform_bounds g Γ
  obtain ⟨C, _, hC⟩ := Geometry.exists_riemannian_lipschitz_of_contMDiff g
    (e.smooth.of_le (by simp))
  obtain ⟨radius, hradius, hshort, _, _⟩ := shortSegment_neighborhood g
  obtain ⟨N₀, hN₀, hedge⟩ := exists_uniform_short_polygon_edges g Γ hradius
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 * (C : ℝ) * L / epsilon)
  refine ⟨max N₀ N₁, hN₀.trans (le_max_left _ _), ?_⟩
  intro n hn k z
  have hn₀ : N₀ ≤ n := (le_max_left N₀ N₁).trans hn
  have hn₁ : N₁ ≤ n := (le_max_right N₀ N₁).trans hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hseg : ∀ i : ℤ, 0 ≤ i → i < n → IsShortSegment g (polygonVertex (Γ k).1 n i)
      (polygonVertex (Γ k).1 n (i + 1))
      (shortSegment g (polygonVertex (Γ k).1 n i) (polygonVertex (Γ k).1 n (i + 1))) :=
    fun i _ _ => (hshort _ _ (hedge n hn₀ k i)).1
  have hbound := (hC (flatPolygon g P n (Γ k).1 z) ((Γ k).1 z)).trans
    (mul_le_mul' le_rfl (flatPolygon_edist_le_of_lipschitz g P (Γ k).1 L (hL k) hnpos hseg z))
  have hlt : (C : ℝ) * (2 * (L : ℝ) / n) < epsilon := by
    have h := (div_lt_iff₀ hepsilon).mp
      (hN₁.trans_le (by exact_mod_cast hn₁ : (N₁ : ℝ) ≤ n))
    calc
      (C : ℝ) * (2 * (L : ℝ) / n) = (2 * (C : ℝ) * L) / n := by ring
      _ < epsilon := (div_lt_iff₀ hnR).mpr (by nlinarith)
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg] at hbound
  exact (edist_lt_ofReal).mp (hbound.trans_lt (ENNReal.ofReal_lt_ofReal_iff hepsilon |>.mpr hlt))

theorem exists_uniform_flatPolygon_family_homotopy {K : Type*} [TopologicalSpace K]
    [CompactSpace K] (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) K) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ prepared : RegularFamily (I := I) (Q := Q) K,
        (∀ k z, (prepared k).1 z = flatPolygon g P n (Γ k).1 z) →
        ContinuousMap.Homotopic prepared Γ := by
  obtain ⟨epsilon, hepsilon, hhom⟩ := exists_regular_contractible_nearby_homotopy_radius
    (K := K) e
  obtain ⟨N, hN, hclose⟩ := exists_uniform_flatPolygon_embedding_error g P e Γ hepsilon
  refine ⟨N, hN, fun n hn prepared heq => ?_⟩
  obtain ⟨H, _⟩ := hhom Γ prepared (fun k z => by
    change dist (e.map ((prepared k).1 z)) (e.map ((Γ k).1 z)) < epsilon
    rw [heq]
    exact hclose n hn k z)
  exact (show ContinuousMap.Homotopic Γ prepared from ⟨H⟩).symm


theorem exists_uniform_flatPolygon_loop_homotopy {K : Type*} [TopologicalSpace K]
    [CompactSpace K] (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) K) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ k, ∀ c : RegularLoop I Q,
      (∀ z, c z = flatPolygon g P n (Γ k).1 z) →
      ContinuousMap.Homotopic c.toContinuousLoop (Γ k).1.toContinuousLoop := by
  obtain ⟨epsilon, hepsilon, hhom⟩ := exists_regular_nearby_homotopy_radius e
  obtain ⟨N, hN, hclose⟩ := exists_uniform_flatPolygon_embedding_error g P e Γ hepsilon
  refine ⟨N, hN, fun n hn k c heq => ?_⟩
  obtain ⟨R, hR, hz, ho, _⟩ := hhom Unit (fun _ => (Γ k).1) (fun _ => c)
    continuous_const continuous_const (fun _ z => by
      rw [heq]
      exact hclose n hn k z)
  have hp : Joined (Γ k).1.toContinuousLoop c.toContinuousLoop := by
    refine ⟨⟨⟨fun t => (R (t, ())).toContinuousLoop, ?_⟩, ?_, ?_⟩⟩
    · exact regularLoopInclusion.continuous.comp
        (hR.comp (continuous_id.prodMk continuous_const))
    · exact congrArg RegularLoop.toContinuousLoop (hz ())
    · exact congrArg RegularLoop.toContinuousLoop (ho ())
  exact ((DifferentialGeometry.Topology.homotopic_iff_joined _ _).mpr hp).symm

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
