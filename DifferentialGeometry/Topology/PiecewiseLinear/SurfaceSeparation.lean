import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCrossingObstruction
import DifferentialGeometry.Topology.PiecewiseLinear.SingleIntersectionCircle
import DifferentialGeometry.Topology.PiecewiseLinear.TransverseSegment

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem affineIndependent_of_card_eq_two_of_injOn
    {s : Finset E} (hs : s.card = 2) {f : E → F} (hf : InjOn f (s : Set E)) :
    AffineIndependent ℝ (fun x : s => f x) := by
  apply (affineIndependent_image_iff s f).mpr
  refine ⟨hf, ?_⟩
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
  have hne : f a ≠ f b := fun h => hab (hf (by simp) (by simp) h)
  have hrange : range (![f a, f b] : Fin 2 → F) = (Finset.image f {a, b} : Set F) := by
    ext y
    simp [or_comm]
  have h := (affineIndependent_of_ne ℝ hne).range
  change AffineIndependent ℝ ((↑) : range (![f a, f b] : Fin 2 → F) → F) at h
  rw [hrange] at h
  exact h

open Classical in
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem span_singleton_le_vectorSpan_image_of_affine_line
    {s : Finset E} (hs : s.card = 2) {f : E → F} (hf : InjOn f (s : Set E))
    {x v : F} (hline : ∀ y ∈ s, ∃ a : ℝ, f y = x + a • v) :
    Submodule.span ℝ {v} ≤ vectorSpan ℝ (s.image f : Set F) := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
  obtain ⟨α, hα⟩ := hline a (by simp)
  obtain ⟨β, hβ⟩ := hline b (by simp)
  have hne : α - β ≠ 0 := by
    intro h
    have heq : f a = f b := by rw [hα, hβ, sub_eq_zero.mp h]
    exact hab (hf (by simp) (by simp) heq)
  rw [Submodule.span_le, Set.singleton_subset_iff]
  change v ∈ vectorSpan ℝ (Finset.image f {a, b} : Set F)
  apply (Submodule.smul_mem_iff _ hne).mp
  have h := vsub_mem_vectorSpan ℝ
    (show f a ∈ (Finset.image f {a, b} : Set F) by simp)
    (show f b ∈ (Finset.image f {a, b} : Set F) by simp)
  simpa only [vsub_eq_sub, hα, hβ, add_sub_add_left_eq_sub, ← sub_smul] using h

private theorem injOn_of_affine_line_parameter {A : Set E} {γ : ℝ → E} {H : E → F}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) {x v : F} {r : ℝ} (hr : r ≠ 0) (hv : v ≠ 0)
    (hH : ∀ t ∈ Icc 0 1, H (γ t) = x + (r * t - r / 2) • v) : InjOn H A := by
  intro a ha b hb hab
  obtain ⟨u, hu, rfl⟩ := hγ.bijOn.surjOn ha
  obtain ⟨w, hw, rfl⟩ := hγ.bijOn.surjOn hb
  rw [hH u hu, hH w hw] at hab
  have heq : (r * u - r / 2) • v = (r * w - r / 2) • v := add_left_cancel hab
  have hc : r * u - r / 2 = r * w - r / 2 := (smul_left_injective ℝ hv) heq
  have huw : u = w := mul_left_cancel₀ hr (by linarith : r * u = r * w)
  rw [huw]

open Classical in
private theorem exists_pair_of_isPLSphere {S : Set E} (hS : IsPLSphere 1 S) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q := by
  obtain ⟨f, hf⟩ := hS
  have hp : (Pi.single (0 : Fin 3) (1 : ℝ)) ∈ stdSimplexBoundary 2 :=
    ⟨single_mem_stdSimplex ℝ _, 1, by simp⟩
  have hq : (Pi.single (1 : Fin 3) (1 : ℝ)) ∈ stdSimplexBoundary 2 :=
    ⟨single_mem_stdSimplex ℝ _, 0, by simp⟩
  refine ⟨_, hf.bijOn.mapsTo hp, _, hf.bijOn.mapsTo hq, ?_⟩
  intro heq
  have h := congrFun (hf.bijOn.injOn hp hq heq) 0
  norm_num at h


open Classical in
private theorem not_isPreconnected_compl_of_disk [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hDball : IsPLBall 2 D.space)
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ F = 3)
    (hne : L.space.Nonempty) : ¬ IsPreconnected L.spaceᶜ := by
  intro hconn
  obtain ⟨t, ht, x, hx, v, r, htcard, hr, hv, hspan, hline⟩ :=
    hL.exists_transverse_segment L hdim hne
  have hv0 : v ≠ 0 := fun heq => hv (heq ▸ (vectorSpan ℝ (t : Set F)).zero_mem)
  have hDman := hDball.isCombinatorialManifoldWithBoundary
  let S := (boundaryComplex 2 D).space
  have hS : IsPLSphere 1 S := isPLSphere_boundaryComplex_space_of_isPLBall D hDball
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_pair_of_isPLSphere hS
  obtain ⟨A, B, γ, δ, H, hγ, hδ, hunion, _, hH, hHA, hHB, _⟩ :=
    exists_piecewiseAffineOn_circle_single_intersection hS hp hq hpq
      (isPolyhedron_space L).isClosed hconn hr hline
  have hI : IsPLBall 1 (Icc (0 : ℝ) 1) := isPLBall_Icc (by norm_num)
  have hA := (hI.of_isPLHomeomorphOn hγ).isPolyhedron
  have hB := (hI.of_isPLHomeomorphOn hδ).isPolyhedron
  have hAD : A ⊆ D.space := (subset_union_left.trans hunion.subset).trans
    (boundaryComplex_space_subset 2 D)
  obtain ⟨D', hD', hD'fin, hAff⟩ :=
    (hH.mono_of_isPolyhedron (isPolyhedron_space D) (subset_univ _)).exists_isSubdivision_affineOn_faces D
  let _ : Finite D'.faces := hD'fin.to_subtype
  obtain ⟨R, hR, hRfin, hcover⟩ := exists_isSubdivision_subcomplexes D'
    (fun _ : Unit => A) (fun _ => hA) (fun _ => hAD.trans hD'.space_eq.symm.subset)
  let _ : Finite R.faces := hRfin.to_subtype
  have hRD := hR.trans hD'
  have hRman := hDman.of_isSubdivision hRD
  have hRS : (boundaryComplex 2 R).space = S := boundaryComplex_space_of_isSubdivision D R hDman hRD
  have hRAff : ∀ s ∈ R.faces, ∃ f : E →ᵃ[ℝ] F,
      EqOn H f (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨u, hu, hsu⟩ := hR.exists_face_subset hs
    obtain ⟨f, hf⟩ := hAff u hu
    exact ⟨f, hf.mono hsu⟩
  obtain ⟨a, u, hu, huZ, ha, hBavoid, htrace⟩ :=
    exists_translate_circle_single_intersection_avoiding_finite hγ hB.isCompact hunion
      (continuousOn_univ.mp hH.continuousOn) (isPolyhedron_space L).isClosed hHB hr hHA hline
      (SimplicialComplex.finite_vertices R)
  let φ : E → F := fun z => H z + a • v
  have hφAff : ∀ s ∈ R.faces, ∃ f : E →ᵃ[ℝ] F,
      EqOn φ f (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨f, hf⟩ := hRAff s hs
    refine ⟨f + AffineMap.const ℝ _ (a • v), fun z hz => ?_⟩
    change H z + a • v = f z + a • v
    rw [hf hz]
  have hsimp : EqOn (simplicialMap R φ) φ R.space := simplicialMap_eq_of_forall_affineOn R φ hφAff
  have hzA : γ u ∈ A := hγ.bijOn.mapsTo (Ioo_subset_Icc_self hu)
  have hzS : γ u ∈ S := hunion.subset (Or.inl hzA)
  have hzR : γ u ∈ (boundaryComplex 2 R).space := hRS.symm ▸ hzS
  obtain ⟨s, hs, hzs⟩ := exists_face_mem_openSimplex (boundaryComplex 2 R) hzR
  have hsR := boundaryComplex_faces_subset 2 R hs
  have hscard : s.card = 2 := by
    obtain ⟨w, _, hsw, hwcard, _⟩ := hs.2
    have hle := (Finset.card_le_card hsw).trans hwcard
    have hpos := Finset.card_pos.mpr (R.nonempty_of_mem_faces hsR)
    by_contra hnecard
    have hsone : s.card = 1 := by omega
    obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp hsone
    have heq : γ u = z := by
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
        openSimplex_subset_convexHull _ hzs
    apply huZ
    change {γ u} ∈ R.faces
    simpa only [heq] using hsR
  have hsA : convexHull ℝ (s : Set E) ⊆ A := by
    have hzA' := hzA
    rw [hcover ()] at hzA'
    obtain ⟨w, ⟨hw, hwA⟩, hzw⟩ := mem_iUnion₂.mp hzA'
    exact (convexHull_mono (Finset.coe_subset.mpr
      (face_subset_of_mem_openSimplex_of_mem_convexHull R hsR hw hzs hzw))).trans hwA
  have hHin : InjOn H A := injOn_of_affine_line_parameter hγ hr.ne' hv0 hHA
  have hφin : InjOn φ (s : Set E) := by
    intro z hz w hw heq
    exact hHin (hsA (subset_convexHull ℝ _ hz)) (hsA (subset_convexHull ℝ _ hw))
      (add_right_cancel heq)
  have hind := affineIndependent_of_card_eq_two_of_injOn hscard hφin
  have hvspan : Submodule.span ℝ {v} ≤ vectorSpan ℝ (s.image φ : Set F) := by
    apply span_singleton_le_vectorSpan_image_of_affine_line (x := x) hscard hφin
    intro z hz
    obtain ⟨b, hb, rfl⟩ := hγ.bijOn.surjOn (hsA (subset_convexHull ℝ _ hz))
    refine ⟨r * b - r / 2 + a, ?_⟩
    change H (γ b) + a • v = _
    rw [hHA b hb, add_assoc, ← add_smul]
  have htrans : vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t : Set F) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact sup_le_sup hvspan le_rfl
  have hφz : simplicialMap R φ (γ u) = x := by
    rw [hsimp (boundaryComplex_space_subset 2 R hzR)]
    change H (γ u) + a • v = x
    rw [hHA u (Ioo_subset_Icc_self hu), add_assoc, ← add_smul, ha]
    have heq : r * u - r / 2 + (r / 2 - r * u) = 0 := by ring
    rw [heq, zero_smul, add_zero]
  have htrace' : (boundaryComplex 2 R).space ∩ simplicialMap R φ ⁻¹' L.space = {γ u} := by
    rw [← htrace]
    ext z
    constructor
    · rintro ⟨hz, hzL⟩
      refine ⟨hRS ▸ hz, ?_⟩
      change φ z ∈ L.space
      rwa [mem_preimage, hsimp (boundaryComplex_space_subset 2 R hz)] at hzL
    · rintro ⟨hz, hzL⟩
      have hz' : z ∈ (boundaryComplex 2 R).space := hRS.symm ▸ hz
      refine ⟨hz', ?_⟩
      change simplicialMap R φ z ∈ L.space
      rw [hsimp (boundaryComplex_space_subset 2 R hz')]
      exact hzL
  exact boundary_preimage_ne_singleton_of_transverse_openSimplex R L φ hRman hL hdim
    hs hscard ht htcard hzs (hφz.symm ▸ hx) hind htrans htrace'

open Classical in
theorem IsCombinatorialManifold.not_isPreconnected_compl [FiniteDimensional ℝ F]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ F = 3)
    (hne : L.space.Nonempty) : ¬ IsPreconnected L.spaceᶜ := by
  let D := simplexComplex (stdVertices 1) (stdVertices_affineIndependent 1)
  let _ : Finite D.faces := (simplexComplex_faces_finite _ _).to_subtype
  have hDspace : D.space = stdSimplex ℝ (Fin 3) := by
    rw [simplexComplex_space _ _ (Finset.card_pos.mp (by rw [card_stdVertices]; norm_num)),
      convexHull_stdVertices]
  have hDball : IsPLBall 2 D.space := hDspace.symm ▸ isPLBall_stdSimplex 2
  exact not_isPreconnected_compl_of_disk D hDball L hL hdim hne

end DifferentialGeometry.Topology.PiecewiseLinear
