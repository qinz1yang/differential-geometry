import DifferentialGeometry.Topology.PiecewiseLinear.ConeBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiber
import DifferentialGeometry.Topology.PiecewiseLinear.LinkHalfSpace
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem restrict_space_affine_ge_of_halfSpace_faces (K : Geometry.SimplicialComplex ℝ E)
    (a : E →ᵃ[ℝ] ℝ) (r : ℝ)
    (hside : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | a x ≤ r} ∨
      convexHull ℝ (s : Set E) ⊆ {x | r ≤ a x}) :
    (restrict K {x | r ≤ a x}).space = K.space ∩ {x | r ≤ a x} := by
  apply Subset.antisymm
  · exact subset_inter (space_mono_of_faces_subset (restrict_faces_subset K _))
      (restrict_space_subset K _)
  · rintro x ⟨hxK, hxa⟩
    obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hxK
    have hxc : x ∈ convexHull ℝ (s : Set E) := openSimplex_subset_convexHull s hxs
    refine (restrict K _).convexHull_subset_space ⟨hs, ?_⟩ hxc
    rcases hside s hs with hle | hge
    · have heq : a x = r := le_antisymm (hle hxc) hxa
      have hverts := (affineMap_eq_iff_of_mem_openSimplex_of_le a hxs
        (fun v hv => hle (subset_convexHull ℝ _ hv))).mp heq
      exact convexHull_min (fun v hv => (hverts v hv).ge) ((convex_Ici r).affine_preimage a)
    · exact hge

theorem geometricLink_restrict_convex [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E)
    {Q : Set E} (hQ : Convex ℝ Q) {p : E} (hpQ : p ∈ Q) :
    SimplicialComplex.geometricLink (restrict K Q) {p} =
      restrict (SimplicialComplex.geometricLink K {p}) Q := by
  ext s
  rw [SimplicialComplex.mem_geometricLink_singleton, mem_restrict_faces_iff,
    mem_restrict_faces_iff, SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨hne, hp, hs, hsQ⟩
    exact ⟨⟨hne, hp, hs⟩,
      (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert p s))).trans hsQ⟩
  · rintro ⟨⟨hne, hp, hs⟩, hsQ⟩
    refine ⟨hne, hp, hs, convexHull_min ?_ hQ⟩
    rintro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hpQ
    · exact hsQ (subset_convexHull ℝ _ hv)

theorem IsConeBase.mem_frontier_combo_iff [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ}
    (hn : Module.finrank ℝ E = n + 2) {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    {p : E} (hp : IsConeBase p L) (hL : IsPLBall (n + 1) L.space)
    {z : E} (hz : z ∈ L.space) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    p + s • (z - p) ∈ frontier (coneComplex hp).space ↔
      z ∈ (boundaryComplex (n + 1) L).space := by
  have hzp : z ≠ p := fun h => hp.notMem_space (h ▸ hz)
  have hxne : p + s • (z - p) ≠ p := by
    intro h
    have hz0 : s • (z - p) = 0 := by simpa only [add_eq_left] using h
    rcases smul_eq_zero.mp hz0 with h | h
    · exact hs.ne' h
    · exact hzp (sub_eq_zero.mp h)
  have hxL : p + s • (z - p) ∉ L.space := by
    intro hx
    have heq := hp.radial z hz _ hx s hs rfl
    have hvec : s • (z - p) = z - p := by
      calc
        s • (z - p) = (p + s • (z - p)) - p := by abel
        _ = z - p := congrArg (fun x => x - p) heq
    have hzero : (s - 1) • (z - p) = 0 := by rw [sub_smul, one_smul, hvec, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact hs1.ne (sub_eq_zero.mp h)
    · exact hzp (sub_eq_zero.mp h)
  rw [frontier_coneComplex hn hp hL, mem_union, or_iff_right hxL]
  constructor
  · intro hx
    rcases (mem_coneComplex_space_iff _).mp hx with h | ⟨w, hw, t, ht, -, hwt⟩
    · exact (hxne h).elim
    · have hzw := hp.radial.eq_of_add_smul_eq hz (boundaryComplex_space_subset (n + 1) L hw)
        hs ht hwt
      exact hzw.symm ▸ hw
  · intro hzB
    exact (mem_coneComplex_space_iff _).mpr (Or.inr ⟨z, hzB, s, hs, hs1.le, rfl⟩)

theorem IsConeBase.boundaryComplex_space_of_halfSpace_germ
    [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ} (hn : Module.finrank ℝ E = n + 2)
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] {p : E} (hp : IsConeBase p L)
    (hL : IsPLBall (n + 1) L.space) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hpℓ : ℓ p = 0)
    (hgerm : (coneComplex hp).space =ᶠ[𝓝 p] {x | 0 ≤ ℓ x}) :
    (boundaryComplex (n + 1) L).space = L.space ∩ {x | ℓ x = 0} := by
  have hsurj : Function.Surjective ℓ := ℓ.toLinearMap.surjective (by
    intro h
    apply hℓ
    ext x
    exact LinearMap.congr_fun h x)
  have hfront : frontier {x | 0 ≤ ℓ x} = {x | ℓ x = 0} := by
    change frontier (ℓ ⁻¹' Ici 0) = _
    rw [ℓ.frontier_preimage hsurj, frontier_Ici]
    rfl
  have hmem : ∀ z ∈ L.space,
      z ∈ (boundaryComplex (n + 1) L).space ↔ ℓ z = 0 := by
    intro z hz
    have htend : Filter.Tendsto (fun s : ℝ => p + s • (z - p)) (𝓝[>] 0) (𝓝 p) := by
      have hcont : Continuous (fun s : ℝ => p + s • (z - p)) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa only [zero_smul, add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hevent := (htend.eventually hgerm.eventuallyEq_nhds).and
      (Ioo_mem_nhdsGT (zero_lt_one' ℝ))
    obtain ⟨s, hsEq, hs, hs1⟩ := hevent.exists
    have hxC : p + s • (z - p) ∈ (coneComplex hp).space :=
      (mem_coneComplex_space_iff hp).mpr (Or.inr ⟨z, hz, s, hs, hs1.le, rfl⟩)
    have hxH : p + s • (z - p) ∈ {x | 0 ≤ ℓ x} := (iff_of_eq hsEq.eq_of_nhds).mp hxC
    have hfrontiff : p + s • (z - p) ∈ frontier (coneComplex hp).space ↔
        p + s • (z - p) ∈ frontier {x | 0 ≤ ℓ x} := by
      rw [mem_frontier_iff_notMem_interior hxC, mem_frontier_iff_notMem_interior hxH,
        hsEq.mem_interior_iff]
    rw [← hp.mem_frontier_combo_iff hn hL hz hs hs1, hfrontiff, hfront]
    change ℓ (p + s • (z - p)) = 0 ↔ ℓ z = 0
    simp only [map_add, map_smul, map_sub, hpℓ, zero_add, sub_zero, smul_eq_mul,
      mul_eq_zero, hs.ne', false_or]
  ext z
  exact ⟨fun hz => ⟨boundaryComplex_space_subset (n + 1) L hz,
      (hmem z (boundaryComplex_space_subset (n + 1) L hz)).mp hz⟩,
    fun hz => (hmem z hz.1).mpr hz.2⟩

theorem exists_isPLHomeomorphOn_geometricLink_halfSpace
    [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ} (hn : Module.finrank ℝ E = n + 2)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p : E} (hp : {p} ∈ K.faces)
    (hK : K.space ∈ 𝓝 p) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hpℓ : ℓ p = 0)
    (hside : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ 0} ∨
      convexHull ℝ (s : Set E) ⊆ {x | 0 ≤ ℓ x}) :
    ∃ f : (Fin (n + 2) → ℝ) → E,
      IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2)))
        ((SimplicialComplex.geometricLink K {p}).space ∩ {x | 0 ≤ ℓ x}) ∧
      f '' stdSimplexBoundary (n + 1) =
        (SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = 0} := by
  let H : Set E := {x | 0 ≤ ℓ x}
  let R := restrict K H
  let L := SimplicialComplex.geometricLink R {p}
  let _ : Finite R.faces := (restrict_faces_finite K H).to_subtype
  have hH : Convex ℝ H := (convex_Ici (0 : ℝ)).affine_preimage ℓ.toLinearMap.toAffineMap
  have hpH : p ∈ H := hpℓ.ge
  have hpR : {p} ∈ R.faces := ⟨hp, by simpa only [Finset.coe_singleton, convexHull_singleton,
    singleton_subset_iff] using hpH⟩
  have hRspace : R.space = K.space ∩ H :=
    restrict_space_affine_ge_of_halfSpace_faces K ℓ.toLinearMap.toAffineMap 0 hside
  have hRgerm : R.space =ᶠ[𝓝 p] H := by
    filter_upwards [hK] with x hx
    apply propext
    rw [hRspace]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have hL : IsPLBall (n + 1) L.space := isPLBall_geometricLink_of_halfSpace hn R hpR
    ℓ.toLinearMap (by intro h; apply hℓ; ext x; exact LinearMap.congr_fun h x) hpℓ
    ⟨K.space, hK, by rw [hRspace]; ext x; simp only [mem_inter_iff]; tauto⟩
  have hLspace : L.space = (SimplicialComplex.geometricLink K {p}).space ∩ H := by
    change (SimplicialComplex.geometricLink (restrict K H) {p}).space = _
    rw [geometricLink_restrict_convex K hH hpH]
    exact restrict_space_affine_ge_of_halfSpace_faces _ ℓ.toLinearMap.toAffineMap 0
      (fun s hs => hside s (SimplicialComplex.geometricLink_le K {p} hs))
  have hcone := isConeBase_geometricLink R (p := p)
  have hCgerm : (coneComplex hcone).space =ᶠ[𝓝 p] H := by
    apply Filter.EventuallyEq.trans (g := R.space) ?_ hRgerm
    rw [← closedStar_eq_coneComplex_space R hpR]
    obtain ⟨V, hV, hVstar⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
      (closedStar_mem_nhdsWithin R p)
    filter_upwards [hV] with x hx
    apply propext
    exact ⟨fun h => closedStar_subset_space R p h, fun h => hVstar ⟨hx, h⟩⟩
  have hboundary := hcone.boundaryComplex_space_of_halfSpace_germ hn hL ℓ hℓ hpℓ hCgerm
  obtain ⟨f, hf⟩ := hL
  refine ⟨f, hLspace ▸ hf, ?_⟩
  have hfB := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L hf
  rw [simplexBoundary_stdVertices_space] at hfB
  rw [← hfB, hboundary, hLspace]
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.ge⟩, h.2⟩⟩
end DifferentialGeometry.Topology.PiecewiseLinear
