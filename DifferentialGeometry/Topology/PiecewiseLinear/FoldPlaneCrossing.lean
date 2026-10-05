import DifferentialGeometry.Topology.PiecewiseLinear.RelativeNormalForm

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_nonneg_apply_eq_of_mem_linearHalfSpace {ℓ : E →ₗ[ℝ] ℝ} {S : Submodule ℝ E}
    (hS : S ≤ LinearMap.ker ℓ) {u y : E} (hy : y ∈ linearHalfSpace S u) :
    ∃ r : ℝ, 0 ≤ r ∧ ℓ y = r * ℓ u := by
  obtain ⟨z, hz, r, hr, rfl⟩ := hy
  refine ⟨r, hr, ?_⟩
  rw [map_add, map_smul, LinearMap.mem_ker.mp (hS hz), smul_eq_mul, zero_add]

theorem pos_or_pos_of_mem_foldedPlane {ℓ : E →ₗ[ℝ] ℝ} {S : Submodule ℝ E}
    (hS : S ≤ LinearMap.ker ℓ) {u v y : E} (hy : y ∈ foldedPlane S u v) (hpos : 0 < ℓ y) :
    0 < ℓ u ∨ 0 < ℓ v := by
  have key : ∀ w : E, y ∈ linearHalfSpace S w → 0 < ℓ w := by
    intro w hw
    obtain ⟨r, hr, hval⟩ := exists_nonneg_apply_eq_of_mem_linearHalfSpace hS hw
    refine not_le.mp fun hcon => ?_
    rw [hval] at hpos
    nlinarith
  rcases hy with hy | hy
  · exact Or.inl (key u hy)
  · exact Or.inr (key v hy)

theorem neg_or_neg_of_mem_foldedPlane {ℓ : E →ₗ[ℝ] ℝ} {S : Submodule ℝ E}
    (hS : S ≤ LinearMap.ker ℓ) {u v y : E} (hy : y ∈ foldedPlane S u v) (hneg : ℓ y < 0) :
    ℓ u < 0 ∨ ℓ v < 0 := by
  have key : ∀ w : E, y ∈ linearHalfSpace S w → ℓ w < 0 := by
    intro w hw
    obtain ⟨r, hr, hval⟩ := exists_nonneg_apply_eq_of_mem_linearHalfSpace hS hw
    refine not_le.mp fun hcon => ?_
    rw [hval] at hneg
    nlinarith
  rcases hy with hy | hy
  · exact Or.inl (key u hy)
  · exact Or.inr (key v hy)

theorem mul_neg_of_mem_foldedPlane_of_pos_of_neg {ℓ : E →ₗ[ℝ] ℝ} {S : Submodule ℝ E}
    (hS : S ≤ LinearMap.ker ℓ) {u v y z : E}
    (hy : y ∈ foldedPlane S u v) (hypos : 0 < ℓ y)
    (hz : z ∈ foldedPlane S u v) (hzneg : ℓ z < 0) :
    ℓ u * ℓ v < 0 := by
  rcases pos_or_pos_of_mem_foldedPlane hS hy hypos with hup | hvp <;>
    rcases neg_or_neg_of_mem_foldedPlane hS hz hzneg with hun | hvn
  · exact absurd hup (asymm hun)
  · exact mul_neg_of_pos_of_neg hup hvn
  · exact mul_neg_of_neg_of_pos hun hvp
  · exact absurd hvp (asymm hvn)

theorem apply_eq_linear_sub_of_eqOn_zero {ℓ : E →ᵃ[ℝ] ℝ} {A : Set E}
    (hzero : EqOn ℓ (fun _ => 0) A) {x : E} (hx : x ∈ affineSpan ℝ A) (z : E) :
    ℓ.linear (z - x) = ℓ z := by
  have hxzero : ℓ x = 0 :=
    AffineMap.eqOn_affineSpan (g := AffineMap.const ℝ E 0) hzero hx
  simpa only [vsub_eq_sub, hxzero, sub_zero] using ℓ.linearMap_vsub z x

theorem mem_affineSpan_of_mem_openSimplex {s : Finset E} {x : E} (hx : x ∈ openSimplex s) :
    x ∈ affineSpan ℝ (s : Set E) :=
  convexHull_subset_affineSpan _ (openSimplex_subset_convexHull s hx)

open Classical in
theorem mem_closure_inter_pos_of_coface_pos (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} {a x : E} (haK : insert a s ∈ K.faces) (hx : x ∈ openSimplex s)
    (ℓ : E →ᵃ[ℝ] ℝ) (hzero : EqOn ℓ (fun _ => 0) (s : Set E)) (ha : 0 < ℓ a) :
    x ∈ closure (K.space ∩ {y | 0 < ℓ y}) := by
  have hlinear := apply_eq_linear_sub_of_eqOn_zero hzero (mem_affineSpan_of_mem_openSimplex hx)
  have hcoe : (s : Set E) ⊆ ((insert a s : Finset E) : Set E) :=
    Finset.coe_subset.mpr (Finset.subset_insert a s)
  have hxhull : x ∈ convexHull ℝ ((insert a s : Finset E) : Set E) :=
    convexHull_mono hcoe (openSimplex_subset_convexHull s hx)
  have hahull : a ∈ convexHull ℝ ((insert a s : Finset E) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_insert_self a s)
  have hsub : openSegment ℝ x a ⊆ K.space ∩ {y | 0 < ℓ y} := by
    intro y hy
    refine ⟨K.convexHull_subset_space haK ((convex_convexHull ℝ _).segment_subset hxhull hahull
      (openSegment_subset_segment ℝ x a hy)), ?_⟩
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hy
    have hdiff : α • x + β • a - x = β • (a - x) := by
      have hαeq : α = 1 - β := by linarith
      rw [hαeq]
      module
    change 0 < ℓ (α • x + β • a)
    rw [← hlinear (α • x + β • a), hdiff, map_smul, smul_eq_mul, hlinear a]
    exact mul_pos hβ ha
  exact closure_mono hsub (segment_subset_closure_openSegment (left_mem_segment ℝ x a))

open Classical in
theorem mem_closure_inter_neg_of_coface_neg (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} {a x : E} (haK : insert a s ∈ K.faces) (hx : x ∈ openSimplex s)
    (ℓ : E →ᵃ[ℝ] ℝ) (hzero : EqOn ℓ (fun _ => 0) (s : Set E)) (ha : ℓ a < 0) :
    x ∈ closure (K.space ∩ {y | ℓ y < 0}) := by
  have hlinear := apply_eq_linear_sub_of_eqOn_zero hzero (mem_affineSpan_of_mem_openSimplex hx)
  have hcoe : (s : Set E) ⊆ ((insert a s : Finset E) : Set E) :=
    Finset.coe_subset.mpr (Finset.subset_insert a s)
  have hxhull : x ∈ convexHull ℝ ((insert a s : Finset E) : Set E) :=
    convexHull_mono hcoe (openSimplex_subset_convexHull s hx)
  have hahull : a ∈ convexHull ℝ ((insert a s : Finset E) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_insert_self a s)
  have hsub : openSegment ℝ x a ⊆ K.space ∩ {y | ℓ y < 0} := by
    intro y hy
    refine ⟨K.convexHull_subset_space haK ((convex_convexHull ℝ _).segment_subset hxhull hahull
      (openSegment_subset_segment ℝ x a hy)), ?_⟩
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hy
    have hdiff : α • x + β • a - x = β • (a - x) := by
      have hαeq : α = 1 - β := by linarith
      rw [hαeq]
      module
    change ℓ (α • x + β • a) < 0
    rw [← hlinear (α • x + β • a), hdiff, map_smul, smul_eq_mul, hlinear a]
    exact mul_neg_of_pos_of_neg hβ ha
  exact closure_mono hsub (segment_subset_closure_openSegment (left_mem_segment ℝ x a))

open Classical in
theorem mul_neg_of_mem_closure_inter_pos_of_mem_closure_inter_neg [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {s : Finset E} (hs : s ∈ K.faces)
    (hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1)
    {x a b : E} (hx : x ∈ openSimplex s)
    (hpair : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a, b})
    (ℓ : E →ᵃ[ℝ] ℝ) (hzero : EqOn ℓ (fun _ => 0) (s : Set E))
    (hpos : x ∈ closure (K.space ∩ {y | 0 < ℓ y}))
    (hneg : x ∈ closure (K.space ∩ {y | ℓ y < 0})) :
    ℓ a * ℓ b < 0 := by
  have hlinear := apply_eq_linear_sub_of_eqOn_zero hzero (mem_affineSpan_of_mem_openSimplex hx)
  have hker : vectorSpan ℝ (s : Set E) ≤ LinearMap.ker ℓ.linear := by
    intro v hv
    exact AffineMap.linear_eqOn_vectorSpan (g := AffineMap.const ℝ E 0) hzero hv
  have hlocal := eventually_mem_space_iff_mem_coface_pair_foldedPlane K hs hbound hx hpair
  obtain ⟨y, hymem, hyiff⟩ :=
    ((mem_closure_iff_frequently.mp hpos).and_eventually hlocal).exists
  obtain ⟨z, hzmem, hziff⟩ :=
    ((mem_closure_iff_frequently.mp hneg).and_eventually hlocal).exists
  have hyval : 0 < ℓ.linear (y - x) := by
    rw [hlinear]
    exact hymem.2
  have hzval : ℓ.linear (z - x) < 0 := by
    rw [hlinear]
    exact hzmem.2
  have hmul := mul_neg_of_mem_foldedPlane_of_pos_of_neg hker (hyiff.mp hymem.1) hyval
    (hziff.mp hzmem.1) hzval
  rwa [hlinear a, hlinear b] at hmul

open Classical in
theorem exists_coface_pair_pos_neg_of_mem_closure_inter [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {s : Finset E} (hs : s ∈ K.faces)
    (hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1)
    {x a b : E} (hx : x ∈ openSimplex s)
    (hpair : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a, b})
    (ℓ : E →ᵃ[ℝ] ℝ) (hzero : EqOn ℓ (fun _ => 0) (s : Set E))
    (hpos : x ∈ closure (K.space ∩ {y | 0 < ℓ y}))
    (hneg : x ∈ closure (K.space ∩ {y | ℓ y < 0})) :
    ∃ aPos aNeg, {w | w ∉ s ∧ insert w s ∈ K.faces} = {aPos, aNeg} ∧ 0 < ℓ aPos ∧ ℓ aNeg < 0 := by
  have hmul := mul_neg_of_mem_closure_inter_pos_of_mem_closure_inter_neg K hs hbound hx hpair
    ℓ hzero hpos hneg
  rcases mul_neg_iff.mp hmul with ⟨hap, hbn⟩ | ⟨han, hbp⟩
  · exact ⟨a, b, hpair, hap, hbn⟩
  · exact ⟨b, a, hpair.trans (Set.pair_comm a b), hbp, han⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_cofaces_pos_neg_of_mem_closure_inter
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = n + 1) (hsB : s ∉ (boundaryComplex (n + 1) K).faces)
    {x : E} (hx : x ∈ openSimplex s)
    (ℓ : E →ᵃ[ℝ] ℝ) (hzero : EqOn ℓ (fun _ => 0) (s : Set E))
    (hpos : x ∈ closure (K.space ∩ {y | 0 < ℓ y}))
    (hneg : x ∈ closure (K.space ∩ {y | ℓ y < 0})) :
    ∃ aPos aNeg, {w | w ∉ s ∧ insert w s ∈ K.faces} = {aPos, aNeg} ∧ 0 < ℓ aPos ∧ ℓ aNeg < 0 := by
  obtain ⟨a, b, _, hpair⟩ := hK.codimension_one_cofaces_of_notMem_boundary K hs hcard hsB
  have hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hcard]
    exact hK.card_le K hu
  exact exists_coface_pair_pos_neg_of_mem_closure_inter K hs hbound hx hpair ℓ hzero hpos hneg

open Classical in
theorem isArrangementGeneralFoldPair_of_mem_closure_inter [FiniteDimensional ℝ E]
    {κ : Type*} (l : κ → E →ᵃ[ℝ] ℝ)
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces)
    (hscard : s.card = 2) (htcard : t.card = 2)
    (hsB : s ∉ (boundaryComplex 2 K).faces) (htB : t ∉ (boundaryComplex 2 L).faces)
    {x : E} (hxs : x ∈ openSimplex s) (hxt : x ∈ openSimplex t)
    (k : κ) (hzeroS : EqOn (l k) (fun _ => 0) (s : Set E))
    (hzeroT : EqOn (l k) (fun _ => 0) (t : Set E))
    (hspan : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = LinearMap.ker (l k).linear)
    (hKpos : x ∈ closure (K.space ∩ {y | 0 < l k y}))
    (hKneg : x ∈ closure (K.space ∩ {y | l k y < 0}))
    (hLpos : x ∈ closure (L.space ∩ {y | 0 < l k y}))
    (hLneg : x ∈ closure (L.space ∩ {y | l k y < 0})) :
    IsArrangementGeneralFoldPair l K L s t x := by
  obtain ⟨aPos, aNeg, hKpair, haP, haN⟩ :=
    IsCombinatorialManifoldWithBoundary.exists_cofaces_pos_neg_of_mem_closure_inter K hK hs
      hscard hsB hxs (l k) hzeroS hKpos hKneg
  obtain ⟨bPos, bNeg, hLpair, hbP, hbN⟩ :=
    IsCombinatorialManifoldWithBoundary.exists_cofaces_pos_neg_of_mem_closure_inter L hL ht
      htcard htB hxt (l k) hzeroT hLpos hLneg
  have hxzero : l k x = 0 :=
    AffineMap.eqOn_affineSpan (g := AffineMap.const ℝ E 0) hzeroS
      (mem_affineSpan_of_mem_openSimplex hxs)
  exact ⟨k, aPos, aNeg, bPos, bNeg, hKpair, hLpair, hxzero, hspan, haP, haN, hbP, hbN⟩

open Classical in
theorem hasPLCrossingAt_of_mem_closure_inter_two_folds [FiniteDimensional ℝ E]
    {κ : Type*} (l : κ → E →ᵃ[ℝ] ℝ)
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdim : Module.finrank ℝ E = 3)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces)
    (hscard : s.card = 2) (htcard : t.card = 2)
    (hsB : s ∉ (boundaryComplex 2 K).faces) (htB : t ∉ (boundaryComplex 2 L).faces)
    {x : E} (hxs : x ∈ openSimplex s) (hxt : x ∈ openSimplex t)
    (k : κ) (hzeroS : EqOn (l k) (fun _ => 0) (s : Set E))
    (hzeroT : EqOn (l k) (fun _ => 0) (t : Set E))
    (hspan : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = LinearMap.ker (l k).linear)
    (hKpos : x ∈ closure (K.space ∩ {y | 0 < l k y}))
    (hKneg : x ∈ closure (K.space ∩ {y | l k y < 0}))
    (hLpos : x ∈ closure (L.space ∩ {y | 0 < l k y}))
    (hLneg : x ∈ closure (L.space ∩ {y | l k y < 0})) :
    HasPLCrossingAt K.space L.space x :=
  (isArrangementGeneralFoldPair_of_mem_closure_inter l K L hK hL hs ht hscard htcard hsB htB
    hxs hxt k hzeroS hzeroT hspan hKpos hKneg hLpos hLneg).hasPLCrossingAt hK hL hdim hs ht
      hscard htcard hxs hxt

end DifferentialGeometry.Topology.PiecewiseLinear
