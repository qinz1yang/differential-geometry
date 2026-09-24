import DifferentialGeometry.Topology.PlanarJordan.SmoothSchoenflies

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

theorem exists_innermost_smooth_disk
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (e : ι → AddCircle (1 : ℝ) → Schoenflies.Plane)
    (he : ∀ i ∈ s, Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ (e i))
    (hdisjoint : (s : Set ι).Pairwise fun i j => Disjoint (range (e i)) (range (e j))) :
    ∃ i ∈ s, ∃ Φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane,
      Φ '' sphere (0 : Schoenflies.Plane) 1 = range (e i) ∧
      Φ '' ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (range (e i)) ∧
      Φ '' closedBall (0 : Schoenflies.Plane) 1 =
        closure (Schoenflies.inside (range (e i))) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ j ∈ s, j ≠ i →
        Disjoint (cthickening δ (Φ '' closedBall (0 : Schoenflies.Plane) 1))
          (range (e j)) := by
  let r := Complex.orthonormalBasisOneI.repr
  let a : Circle ≃ₜ sphere (0 : Schoenflies.Plane) 1 :=
    r.toHomeomorph.subtype (fun z => by
      change z ∈ sphere (0 : ℂ) 1 ↔ r z ∈ sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm, r.norm_map])
  let q : sphere (0 : Schoenflies.Plane) 1 ≃ₜ AddCircle (1 : ℝ) :=
    a.symm.trans (AddCircle.homeomorphCircle one_ne_zero).symm
  let f := fun i => e i ∘ q
  have hfe (i : ι) (hi : i ∈ s) : Topology.IsEmbedding (f i) :=
    (he i hi).isEmbedding.comp q.isEmbedding
  have hrange (i : ι) : range (f i) = range (e i) := by
    dsimp only [f]
    rw [range_comp, q.surjective.range_eq, image_univ]
  have hfd : (s : Set ι).Pairwise fun i j => Disjoint (range (f i)) (range (f j)) := by
    intro i hi j hj hij
    rw [hrange, hrange]
    exact hdisjoint hi hj hij
  obtain ⟨i, hi, F, _, _, hclosed, δ, hδ, hclear⟩ :=
    exists_innermost_circle_disk s hs f hfe hfd
  obtain ⟨Φ, hΦ, hball, hΦclosed⟩ := smooth_schoenflies (he i hi)
  have hdisk : Φ '' closedBall (0 : Schoenflies.Plane) 1 =
      F '' closedBall (0 : Schoenflies.Plane) 1 := by
    rw [hΦclosed, hclosed, hrange]
  refine ⟨i, hi, Φ, hΦ, hball, hΦclosed, δ, hδ, ?_⟩
  intro j hj hji
  rw [hdisk, ← hrange j]
  exact hclear j hj hji

end DifferentialGeometry.Topology.PlanarJordan
