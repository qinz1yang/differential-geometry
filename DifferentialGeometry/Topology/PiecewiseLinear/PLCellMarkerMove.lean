import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldPointTransport
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import Mathlib.Topology.Connected.LocallyConnected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_excluding_point_preserving_union {M : Type*} [TopologicalSpace M]
    [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {A B Bd U : Set M} (hB : IsPLCellOn 3 B Bd) (hU : IsOpen U) (hc : IsPreconnected U)
    (hUA : U ⊆ interior A) {p q : M} (hp : p ∈ U) (hq : q ∈ U) (hqB : q ∉ B) :
    ∃ C : Set M, IsPLCellOn 3 C (frontier C) ∧ p ∉ C ∧ A ∪ C = A ∪ B ∧
      interior A ∪ interior C = interior A ∪ interior B ∧
      frontier A ∩ frontier C = frontier A ∩ frontier B ∧ C \ U = B \ U ∧
      ((interior A ∩ interior C).Nonempty ↔ (interior A ∩ interior B).Nonempty) := by
  obtain ⟨K, φ, -, hKU, -, hφi, hfix, hφp⟩ :=
    exists_isPL_homeomorph_map_point_eqOn_compl (n := 3) hU hc hp hq
  have hfixU : EqOn φ id Uᶜ := fun x hx => hfix fun hxK => hx (hKU hxK)
  have hfixA : EqOn φ id (interior A)ᶜ :=
    fun x hx => hfixU fun hxU => hx (hUA hxU)
  have hmem (D : Set M) (x : M) : x ∈ φ.symm '' D ↔ φ x ∈ D := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [φ.apply_symm_apply] using hy
    · intro hx
      exact ⟨φ x, hx, φ.symm_apply_apply x⟩
  have hcell : IsPLCellOn 3 (φ.symm '' B) (φ.symm '' Bd) := by
    obtain ⟨P, r, u, hr, hu, hBe, hBde⟩ := hB
    have hP : IsCompact P := (IsPLBall.isPolyhedron ⟨r, hr⟩).isCompact
    have hcomp : IsPLHomeomorphInto 3 (φ.symm ∘ u) P :=
      (hφi.comp_isPLOn hu.isPLOn).isPLHomeomorphInto hP
        (fun _ hx _ hy he => hu.injOn hx hy (φ.symm.injective he))
    refine ⟨P, r, φ.symm ∘ u, hr, hcomp, ?_, ?_⟩
    · rw [hBe, image_comp]
    · rw [hBde, image_comp]
  refine ⟨φ.symm '' B, hcell.boundary_eq_frontier ▸ hcell, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem, hφp]
    exact hqB
  · ext x
    by_cases hx : x ∈ A
    · simp only [mem_union, hx, true_or]
    · have hxI : x ∉ interior A := fun hxI => hx (interior_subset hxI)
      simp only [mem_union, hx, false_or, hmem, hfixA hxI, id_eq]
  · rw [← φ.symm.image_interior]
    ext x
    by_cases hx : x ∈ interior A
    · simp only [mem_union, hx, true_or]
    · simp only [mem_union, hx, false_or, hmem, hfixA hx, id_eq]
  · rw [← φ.symm.image_frontier]
    ext x
    by_cases hx : x ∈ frontier A
    · have hxI : x ∉ interior A := hx.2
      simp only [mem_inter_iff, hx, true_and, hmem, hfixA hxI, id_eq]
    · simp only [mem_inter_iff, hx, false_and]
  · ext x
    by_cases hx : x ∈ U
    · simp only [mem_sdiff, hx, not_true_eq_false, and_false]
    · simp only [mem_sdiff, hx, not_false_eq_true, and_true, hmem, hfixU hx, id_eq]
  · have hAi (x : M) : φ x ∈ interior A ↔ x ∈ interior A := by
      constructor
      · intro hx
        by_contra hn
        exact hn (by simpa only [hfixA hn, id_eq] using hx)
      · intro hx
        by_contra hn
        have he : φ x = x := φ.injective (hfixA hn)
        exact hn (he.symm ▸ hx)
    rw [← φ.symm.image_interior]
    constructor
    · rintro ⟨x, hxA, hxB⟩
      exact ⟨φ x, (hAi x).mpr hxA, (hmem _ _).mp hxB⟩
    · rintro ⟨x, hxA, hxB⟩
      refine ⟨φ.symm x, (hAi _).mp ?_, ⟨x, hxB, rfl⟩⟩
      simpa only [φ.apply_symm_apply] using hxA

private theorem exists_disjoint_connected_open_supersets {X : Type*} [TopologicalSpace X]
    [T2Space X] [LocallyConnectedSpace X] {K₀ K₁ U₀ U₁ : Set X}
    (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁) (hc₀ : IsConnected K₀) (hc₁ : IsConnected K₁)
    (hdisj : Disjoint K₀ K₁) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hsub₀ : K₀ ⊆ U₀) (hsub₁ : K₁ ⊆ U₁) :
    ∃ V₀ V₁ : Set X, IsOpen V₀ ∧ IsOpen V₁ ∧ IsPreconnected V₀ ∧ IsPreconnected V₁ ∧
      K₀ ⊆ V₀ ∧ K₁ ⊆ V₁ ∧ V₀ ⊆ U₀ ∧ V₁ ⊆ U₁ ∧ Disjoint V₀ V₁ := by
  obtain ⟨W₀, W₁, hW₀, hW₁, hKW₀, hKW₁, hWW⟩ :=
    SeparatedNhds.of_isCompact_isCompact hK₀ hK₁ hdisj
  obtain ⟨p₀, hp₀⟩ := hc₀.nonempty
  obtain ⟨p₁, hp₁⟩ := hc₁.nonempty
  refine ⟨connectedComponentIn (W₀ ∩ U₀) p₀, connectedComponentIn (W₁ ∩ U₁) p₁,
    (hW₀.inter hU₀).connectedComponentIn, (hW₁.inter hU₁).connectedComponentIn,
    isPreconnected_connectedComponentIn, isPreconnected_connectedComponentIn,
    hc₀.isPreconnected.subset_connectedComponentIn hp₀ (subset_inter hKW₀ hsub₀),
    hc₁.isPreconnected.subset_connectedComponentIn hp₁ (subset_inter hKW₁ hsub₁),
    (connectedComponentIn_subset _ _).trans inter_subset_right,
    (connectedComponentIn_subset _ _).trans inter_subset_right, ?_⟩
  exact hWW.mono ((connectedComponentIn_subset _ _).trans inter_subset_left)
    ((connectedComponentIn_subset _ _).trans inter_subset_left)

theorem exists_marked_cell_pair_of_disjoint_connected_routes {M : Type*} [TopologicalSpace M]
    [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {A B Ad Bd O K₀ K₁ : Set M} (hA : IsPLCellOn 3 A Ad) (hB : IsPLCellOn 3 B Bd)
    (hO : IsOpen O) (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hc₀ : IsConnected K₀) (hc₁ : IsConnected K₁) (hdisj : Disjoint K₀ K₁)
    (hsub₀ : K₀ ⊆ interior A ∩ O) (hsub₁ : K₁ ⊆ interior B ∩ O)
    {p₀ q₀ p₁ q₁ : M} (hp₀ : p₀ ∈ K₀) (hq₀ : q₀ ∈ K₀) (hq₀B : q₀ ∉ B)
    (hp₁ : p₁ ∈ K₁) (hq₁ : q₁ ∈ K₁) (hq₁A : q₁ ∉ A) :
    ∃ A' B' : Set M, IsPLCellOn 3 A' (frontier A') ∧ IsPLCellOn 3 B' (frontier B') ∧
      p₀ ∈ interior A' ∧ p₀ ∉ B' ∧ p₁ ∈ interior B' ∧ p₁ ∉ A' ∧
      A' ∪ B' = A ∪ B ∧ interior A' ∪ interior B' = interior A ∪ interior B ∧
      frontier A' ∩ frontier B' = frontier A ∩ frontier B ∧
      A' \ O = A \ O ∧ B' \ O = B \ O ∧
      ((interior A' ∩ interior B').Nonempty ↔ (interior A ∩ interior B).Nonempty) := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨U₀, U₁, hU₀, hU₁, hcU₀, hcU₁, hKU₀, hKU₁, hUV₀, hUV₁, hUU⟩ :=
    exists_disjoint_connected_open_supersets hK₀ hK₁ hc₀ hc₁ hdisj
      (isOpen_interior.inter hO) (isOpen_interior.inter hO) hsub₀ hsub₁
  obtain ⟨B', hB', hp₀B', huB, hiB, hfB, hdB, hnB⟩ :=
    hB.exists_excluding_point_preserving_union hU₀ hcU₀
      (hUV₀.trans inter_subset_left) (hKU₀ hp₀) (hKU₀ hq₀) hq₀B
  have hU₁B' : U₁ ⊆ interior B' := by
    apply interior_maximal _ hU₁
    intro x hx
    have hxU₀ : x ∉ U₀ := fun hx₀ => Set.disjoint_left.mp hUU hx₀ hx
    exact (hdB.symm.subset ⟨interior_subset (hUV₁ hx).1, hxU₀⟩).1
  obtain ⟨A', hA', hp₁A', huA, hiA, hfA, hdA, hnA⟩ :=
    hA.exists_excluding_point_preserving_union hU₁ hcU₁ hU₁B'
      (hKU₁ hp₁) (hKU₁ hq₁) hq₁A
  have hU₀A' : U₀ ⊆ interior A' := by
    apply interior_maximal _ hU₀
    intro x hx
    have hxU₁ : x ∉ U₁ := fun hx₁ => Set.disjoint_left.mp hUU hx hx₁
    exact (hdA.symm.subset ⟨interior_subset (hUV₀ hx).1, hxU₁⟩).1
  refine ⟨A', B', hA', hB', hU₀A' (hKU₀ hp₀), hp₀B', hU₁B' (hKU₁ hp₁), hp₁A',
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      A' ∪ B' = B' ∪ A' := union_comm _ _
      _ = B' ∪ A := huA
      _ = A ∪ B' := union_comm _ _
      _ = A ∪ B := huB
  · calc
      interior A' ∪ interior B' = interior B' ∪ interior A' := union_comm _ _
      _ = interior B' ∪ interior A := hiA
      _ = interior A ∪ interior B' := union_comm _ _
      _ = interior A ∪ interior B := hiB
  · calc
      frontier A' ∩ frontier B' = frontier B' ∩ frontier A' := inter_comm _ _
      _ = frontier B' ∩ frontier A := hfA
      _ = frontier A ∩ frontier B' := inter_comm _ _
      _ = frontier A ∩ frontier B := hfB
  · ext x
    by_cases hx : x ∈ O
    · simp only [mem_sdiff, hx, not_true_eq_false, and_false]
    · have hxU₁ : x ∉ U₁ := fun hxU => hx (hUV₁ hxU).2
      simpa only [mem_sdiff, hx, hxU₁, not_false_eq_true, and_true] using
        Set.ext_iff.mp hdA x
  · ext x
    by_cases hx : x ∈ O
    · simp only [mem_sdiff, hx, not_true_eq_false, and_false]
    · have hxU₀ : x ∉ U₀ := fun hxU => hx (hUV₀ hxU).2
      simpa only [mem_sdiff, hx, hxU₀, not_false_eq_true, and_true] using
        Set.ext_iff.mp hdB x
  · have hnA' : (interior A' ∩ interior B').Nonempty ↔
        (interior A ∩ interior B').Nonempty := by
      simpa only [inter_comm (interior B')] using hnA
    exact hnA'.trans hnB

end DifferentialGeometry.Topology.PiecewiseLinear
