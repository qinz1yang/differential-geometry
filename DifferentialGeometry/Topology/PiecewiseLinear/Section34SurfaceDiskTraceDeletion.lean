import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskSeparation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.exists_strict_trace_subfamily_after_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {ι : Type*} [Finite ι] {D : Set E} {J : ι → Set E}
    (i : ι) {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hbd : r '' stdSimplexBoundary 2 = J i) (hDK : D ⊆ K.space)
    (hJ : ∀ j, IsPLSphere 1 (J j)) (hJK : ∀ j, J j ⊆ K.space)
    (hdis : Pairwise fun j k => Disjoint (J j) (J k)) :
    ∃ I : Set ι, Nat.card I < Nat.card ι ∧
      ((⋃ j, J j) \ D) = ⋃ j : I, J j.1 ∧
      (∀ j : I, Disjoint D (J j.1)) ∧ IsClosed ((⋃ j, J j) \ D) := by
  have hiD : J i ⊆ D := by
    rw [← hbd, ← hr.image_eq]
    exact image_mono fun _ hx => hx.1
  let I : Set ι := {j | Disjoint D (J j)}
  have hi : i ∉ I := by
    intro hi
    obtain ⟨x, hx⟩ := (hJ i).nonempty
    exact disjoint_left.mp hi (hiD hx) hx
  have hcard : Nat.card I < Nat.card ι := Set.ncard_lt_card (fun h => hi (h ▸ mem_univ i))
  have htrace : ((⋃ j, J j) \ D) = ⋃ j : I, J j.1 := by
    ext x
    constructor
    · rintro ⟨hx, hxD⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      have hji : j ≠ i := fun hji => hxD (hiD (hji ▸ hxj))
      have hjbd : Disjoint (J j) (r '' stdSimplexBoundary 2) := hbd.symm ▸ hdis hji
      rcases hK.subset_or_disjoint_disk K hr hDK (hJ j).isConnected.isPreconnected
        (hJK j) hjbd with hsub | hsep
      · exact (hxD (hsub hxj)).elim
      · exact mem_iUnion.mpr ⟨⟨j, hsep⟩, hxj⟩
    · intro hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact ⟨mem_iUnion.mpr ⟨j.1, hxj⟩, fun hxD => disjoint_left.mp j.2 hxD hxj⟩
  refine ⟨I, hcard, htrace, fun j => j.2, ?_⟩
  rw [htrace]
  exact isClosed_iUnion_of_finite fun j => (hJ j.1).isPolyhedron.isClosed

end DifferentialGeometry.Topology.PiecewiseLinear
