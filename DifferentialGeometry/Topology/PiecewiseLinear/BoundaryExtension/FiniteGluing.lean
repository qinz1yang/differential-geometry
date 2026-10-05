import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.FiniteGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_isPLHomeomorphOn_finite_ball_union_of_boundary_maps
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Finite ι]
    {n : ℕ} {P : ι → Set E} {Q : ι → Set F}
    {r : ι → (Fin (n + 2) → ℝ) → E} {s : ι → (Fin (n + 2) → ℝ) → F}
    (hr : ∀ i, IsPLHomeomorphOn (r i) (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) (P i))
    (hs : ∀ i, IsPLHomeomorphOn (s i) (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) (Q i))
    (hPinter : ∀ i j, i ≠ j → P i ∩ P j ⊆ r i '' stdSimplexBoundary (n + 1))
    (hQinter : ∀ i j, i ≠ j → Q i ∩ Q j ⊆ s i '' stdSimplexBoundary (n + 1))
    {φ : E → F}
    (hφ : IsPLHomeomorphOn φ (⋃ i, r i '' stdSimplexBoundary (n + 1))
      (⋃ i, s i '' stdSimplexBoundary (n + 1)))
    (hφrim : ∀ i, φ '' (r i '' stdSimplexBoundary (n + 1)) =
      s i '' stdSimplexBoundary (n + 1)) :
    ∃ H : E → F, IsPLHomeomorphOn H (⋃ i, P i) (⋃ i, Q i) ∧
      EqOn H φ (⋃ i, r i '' stdSimplexBoundary (n + 1)) ∧
      ∀ i, H '' P i = Q i := by
  let J : ι → Set E := fun i => r i '' stdSimplexBoundary (n + 1)
  let L : ι → Set F := fun i => s i '' stdSimplexBoundary (n + 1)
  have hJpoly (i : ι) : IsPolyhedron (J i) :=
    (hr i).isPLSphere_image_stdSimplexBoundary.isPolyhedron
  have hJP (i : ι) : J i ⊆ P i := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hr i).bijOn.mapsTo hx.1
  have hLQ (i : ι) : L i ⊆ Q i := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hs i).bijOn.mapsTo hx.1
  have hφi (i : ι) : IsPLHomeomorphOn φ (J i) (L i) := by
    have h := hφ.restrict (hJpoly i) (subset_iUnion J i)
    rwa [hφrim i] at h
  choose f hf hfix using fun i =>
    exists_isPLHomeomorphOn_of_stdSimplexBoundary (hr i) (hs i) (hφi i)
  have hcompat (i j : ι) : EqOn (f i) (f j) (P i ∩ P j) := by
    intro x hx
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · exact (hfix i (hPinter i j hij hx)).trans
        (hfix j (hPinter j i hij.symm ⟨hx.2, hx.1⟩)).symm
  have hmeet (i j : ι) : f i '' (P i ∩ P j) = Q i ∩ Q j := by
    rcases eq_or_ne i j with rfl | hij
    · rw [inter_self, inter_self, (hf i).image_eq]
    have hsource : P i ∩ P j = J i ∩ J j := by
      apply Subset.antisymm
      · exact fun x hx => ⟨hPinter i j hij hx, hPinter j i hij.symm ⟨hx.2, hx.1⟩⟩
      · exact inter_subset_inter (hJP i) (hJP j)
    have htarget : Q i ∩ Q j = L i ∩ L j := by
      apply Subset.antisymm
      · exact fun x hx => ⟨hQinter i j hij hx, hQinter j i hij.symm ⟨hx.2, hx.1⟩⟩
      · exact inter_subset_inter (hLQ i) (hLQ j)
    rw [(show EqOn (f i) φ (P i ∩ P j) from
      (hfix i).mono (hPinter i j hij)).image_eq, hsource, htarget,
      hφ.bijOn.injOn.image_inter (subset_iUnion J i) (subset_iUnion J j), hφrim i, hφrim j]
  obtain ⟨H, hH, hHi⟩ := exists_isPLHomeomorphOn_iUnion
    (fun i => (show IsPLBall (n + 1) (P i) from ⟨r i, hr i⟩).isPolyhedron)
    hf hcompat hmeet
  refine ⟨H, hH, ?_, fun i => (hHi i).image_eq.trans (hf i).image_eq⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact (hHi i (hJP i hi)).trans (hfix i hi)

end DifferentialGeometry.Topology.PiecewiseLinear
