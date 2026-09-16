import DifferentialGeometry.Topology.PiecewiseLinear.HeightComplexStability
import DifferentialGeometry.Topology.PiecewiseLinear.FaceLevelPolygons
import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiberWitness
import DifferentialGeometry.Topology.PiecewiseLinear.CapLevelPolygons

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem eventually_exists_face_fiber_witness_outside_closed
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    {H : E → E} (hH : Continuous H) (hheight : ∀ x, ℓ (H x) = ℓ x)
    {Q D : Set E} (hQ : IsClosed Q) (hD : D ∈ levelPolygons K.space ℓ (ℓ p))
    (hDQ : ¬ D ⊆ Q) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ s ∈ K.faces, ∃ x ∈ openSimplex s,
      x ∉ Q ∧ f (H x) = f (H p) ∧ openSimplex s ∩ {y | ℓ y = ℓ p} ⊆ D := by
  have hex : ∃ q ∈ D, q ≠ p ∧ q ∉ Q := by
    by_contra! h
    have hsub : D \ {p} ⊆ Q := fun q hq => h q hq.1 hq.2
    exact hDQ ((hD.1.closure_sdiff_singleton_one p).symm.subset.trans (closure_minimal hsub hQ))
  obtain ⟨q, hqD, hqp, hqQ⟩ := hex
  obtain ⟨s, hs, hqs⟩ := exists_face_mem_openSimplex K (hD.2 hqD).1
  obtain ⟨d, hds, hd⟩ := exists_pos_height_direction_of_mem_openSimplex K ℓ hs hqs hqp
    (hD.2 hqD).2 (fun _ hv h => hinj hv hp h)
  have hpath : Filter.Tendsto (fun t : ℝ => q + t • d) (𝓝 0) (𝓝 q) := by
    have hcont : Continuous (fun t : ℝ => q + t • d) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using (hcont.continuousAt (x := (0 : ℝ))).tendsto
  have hlocal := (eventually_mem_openSimplex_of_mem_vectorSpan hqs hds).and
    (hpath (hQ.isOpen_compl.mem_nhds hqQ))
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) h
  have hsD := openSimplex_inter_fiber_subset_of_mem_levelPolygon K hK hdimE ℓ.toLinearMap
    hlinear hinj hp hD hs hqs hqD hqp
  filter_upwards [eventually_exists_eq_image_height_of_mem_ray_nhds hH ℓ hheight
    (hD.2 hqD).2 hd (U := openSimplex s ∩ Qᶜ) hlocal] with f hf
  obtain ⟨x, hx, hfx⟩ := hf
  exact ⟨s, hs, x, hx.1, hx.2, hfx, hsD⟩

private theorem eventually_exists_face_fiber_witness_below_upper_side
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    {H : E → E} (hH : Continuous H) (hheight : ∀ x, ℓ (H x) = ℓ x)
    {Q J : Set E} (hJ : J ∈ levelPolygons K.space ℓ (ℓ p))
    (hside : ∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → ℓ p ≤ ℓ x) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, (∀ q ∈ J \ {p}, f (H p) < f (H q)) →
      ∃ s ∈ K.faces, ∃ x ∈ openSimplex s,
        x ∉ Q ∧ f (H x) = f (H p) ∧ openSimplex s ∩ {y | ℓ y = ℓ p} ⊆ J := by
  obtain ⟨q, hqJ, hqp⟩ := (hJ.1.isConnected_sdiff_singleton_one p).nonempty
  obtain ⟨s, hs, hqs⟩ := exists_face_mem_openSimplex K (hJ.2 hqJ).1
  obtain ⟨d, hds, hd⟩ := exists_pos_height_direction_of_mem_openSimplex K ℓ hs hqs hqp
    (hJ.2 hqJ).2 (fun _ hv h => hinj hv hp h)
  have hpath : Filter.Tendsto (fun t : ℝ => q + t • d) (𝓝 0) (𝓝 q) := by
    have hcont : Continuous (fun t : ℝ => q + t • d) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using (hcont.continuousAt (x := (0 : ℝ))).tendsto
  have hlocal := (eventually_mem_openSimplex_of_mem_vectorSpan hqs hds).and
    (hpath (hside q ⟨hqJ, hqp⟩))
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) h
  have hsJ := openSimplex_inter_fiber_subset_of_mem_levelPolygon K hK hdimE ℓ.toLinearMap
    hlinear hinj hp hJ hs hqs hqJ hqp
  filter_upwards [eventually_exists_lt_height_eq_image_height_of_mem_ray_nhds hH ℓ hheight
    (hJ.2 hqJ).2 hd (U := openSimplex s ∩ {x | x ∈ Q → ℓ p ≤ ℓ x}) hlocal] with f hf
  intro hpush
  obtain ⟨x, hx, hxlow, hfx⟩ := hf (hpush q ⟨hqJ, hqp⟩)
  exact ⟨s, hs, x, hx.1, fun hxQ => (not_le.mpr hxlow) (hx.2 hxQ), hfx, hsJ⟩

theorem eventually_exists_isPLHomeomorphOn_fiber_deleting_levelPolygon_of_upper_side
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (hheight : ∀ x, ℓ (H x) = ℓ x)
    {Q J : Set E} (hQ : IsClosed Q) (hQK : Q ⊆ K.space)
    (hJ : J ∈ levelPolygons Q ℓ (ℓ p))
    (hside : ∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → ℓ p ≤ ℓ x) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, (∀ q ∈ J \ {p}, f (H p) < f (H q)) →
      ∃ g : E → E, IsPLHomeomorphOn g (K.space ∩ {x | f (H x) = f (H p)})
        (K.space ∩ {x | ℓ x = ℓ p}) ∧
        ∀ C ∈ levelPolygons Q (fun x => f (H x)) (f (H p)),
          g '' C ∈ levelPolygons Q ℓ (ℓ p) \ {J} := by
  classical
  let C₀ := levelPolygons K.space ℓ (ℓ p)
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) h
  have hfinite : C₀.Finite := finite_levelPolygons K (fun s hs => hK.card_le K hs)
    hdimE ℓ.toLinearMap hlinear hinj (ℓ p)
  let _ : Finite C₀ := hfinite.to_subtype
  let W : (E →L[ℝ] ℝ) → Set E → Prop := fun f D =>
    ∃ s ∈ K.faces, ∃ x ∈ openSimplex s,
      x ∉ Q ∧ f (H x) = f (H p) ∧ openSimplex s ∩ {y | ℓ y = ℓ p} ⊆ D
  have hbad : ∀ D : C₀, ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, (¬ D.val ⊆ Q) → W f D.val := by
    intro D
    by_cases hDQ : D.val ⊆ Q
    · exact Filter.Eventually.of_forall fun _ h => (h hDQ).elim
    · exact (eventually_exists_face_fiber_witness_outside_closed K hK hdimE ℓ hℓ hinj hp
        H.continuous hheight hQ D.property hDQ).mono fun _ h _ => h
  have hJK : J ∈ C₀ := ⟨hJ.1, fun x hx => ⟨hQK (hJ.2 hx).1, (hJ.2 hx).2⟩⟩
  filter_upwards [hK.isCombinatorialManifoldWithBoundary.eventually_exists_isPLHomeomorphOn_height_fiber
      H hH ℓ hheight hinj (fun _ hv h => hinj hv hp h), Filter.eventually_all.mpr hbad,
    eventually_exists_face_fiber_witness_below_upper_side K hK hdimE ℓ hℓ hinj hp
      H.continuous hheight hJK hside] with f hf hbadf hJf
  intro hpush
  obtain ⟨g, hg, hfaces⟩ := hf
  have hsource : ∀ C ∈ levelPolygons Q (fun x => f (H x)) (f (H p)),
      C ⊆ K.space ∩ {x | f (H x) = f (H p)} :=
    fun C hC x hx => ⟨hQK (hC.2 hx).1, (hC.2 hx).2⟩
  have hmiss : ∀ D, W f D → ∀ C ∈ levelPolygons Q (fun x => f (H x)) (f (H p)),
      g '' C ≠ D := by
    rintro D ⟨s, hs, x, hxs, hxQ, hfx, hsD⟩ C hC heq
    have hxsource : x ∈ K.space ∩ {x | f (H x) = f (H p)} :=
      ⟨K.convexHull_subset_space hs (openSimplex_subset_convexHull s hxs), hfx⟩
    have hgx := hg.bijOn.mapsTo hxsource
    have hgxs := mem_openSimplex_of_forall_mem_convexHull_iff K hs hxs hgx.1
      (fun t ht => hfaces t ht x hxsource)
    have hgxD : g x ∈ D := hsD ⟨hgxs, hgx.2⟩
    obtain ⟨y, hyC, hgy⟩ := heq.symm.subset hgxD
    have hxy : x = y := hg.bijOn.injOn hxsource (hsource C hC hyC) hgy.symm
    apply hxQ
    rw [hxy]
    exact (hC.2 hyC).1
  refine ⟨g, hg, ?_⟩
  intro C hC
  have hD : g '' C ∈ C₀ := by
    refine ⟨hC.1.of_isPLHomeomorphOn (hg.restrict hC.1.isPolyhedron (hsource C hC)), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hg.bijOn.mapsTo (hsource C hC hx)
  have hDQ : g '' C ⊆ Q := by
    by_contra hnot
    exact hmiss (g '' C) (hbadf ⟨g '' C, hD⟩ hnot) C hC rfl
  refine ⟨⟨hD.1, fun x hx => ⟨hDQ hx, (hD.2 hx).2⟩⟩, ?_⟩
  exact hmiss J (hJf hpush) C hC

theorem eventually_encard_levelPolygons_add_one_le_of_upper_side
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (hheight : ∀ x, ℓ (H x) = ℓ x)
    {Q J : Set E} (hQ : IsClosed Q) (hQK : Q ⊆ K.space)
    (hJ : J ∈ levelPolygons Q ℓ (ℓ p))
    (hside : ∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → ℓ p ≤ ℓ x) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, (∀ q ∈ J \ {p}, f (H p) < f (H q)) →
      (levelPolygons Q (fun x => f (H x)) (f (H p))).encard + 1 ≤
        (levelPolygons Q ℓ (ℓ p)).encard := by
  filter_upwards [eventually_exists_isPLHomeomorphOn_fiber_deleting_levelPolygon_of_upper_side
    K hK hdimE ℓ hℓ hinj hp H hH hheight hQ hQK hJ hside] with f hf
  intro hpush
  obtain ⟨g, hg, hmaps⟩ := hf hpush
  have hsource : ∀ C ∈ levelPolygons Q (fun x => f (H x)) (f (H p)),
      C ⊆ K.space ∩ {x | f (H x) = f (H p)} :=
    fun C hC x hx => ⟨hQK (hC.2 hx).1, (hC.2 hx).2⟩
  have hinjC : InjOn (fun C => g '' C) (levelPolygons Q (fun x => f (H x)) (f (H p))) := by
    intro C hC D hD heq
    exact (hg.bijOn.injOn.image_eq_image_iff (hsource C hC) (hsource D hD)).mp heq
  have hle : (levelPolygons Q (fun x => f (H x)) (f (H p))).encard ≤
      (levelPolygons Q ℓ (ℓ p) \ {J}).encard := by
    rw [← hinjC.encard_image]
    exact Set.encard_le_encard (by rintro _ ⟨C, hC, rfl⟩; exact hmaps C hC)
  calc
    (levelPolygons Q (fun x => f (H x)) (f (H p))).encard + 1 ≤
        (levelPolygons Q ℓ (ℓ p) \ {J}).encard + 1 := add_le_add hle le_rfl
    _ = (levelPolygons Q ℓ (ℓ p)).encard := Set.encard_sdiff_singleton_add_one hJ

theorem eventually_encard_levelPolygons_cap_add_one_le_of_upper_side
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (hheight : ∀ x, ℓ (H x) = ℓ x)
    {Q D J : Set E} (hQ : IsClosed Q) (hQK : Q ⊆ K.space)
    (hJ : J ∈ levelPolygons Q ℓ (ℓ p)) (hJD : J ⊆ D)
    (hside : ∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → ℓ p ≤ ℓ x) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, (∀ x ∈ H '' D \ {H p}, f (H p) < f x) →
      (levelPolygons (H '' (Q ∪ D)) f (f (H p))).encard + 1 ≤
        (levelPolygons Q ℓ (ℓ p)).encard := by
  filter_upwards [eventually_encard_levelPolygons_add_one_le_of_upper_side
    K hK hdimE ℓ hℓ hinj hp H hH hheight hQ hQK hJ hside] with f hf
  intro hpush
  have hcap : (H '' D) ∩ {x | f x = f (H p)} ⊆ {H p} := by
    intro x hx
    by_contra hxp
    exact (hpush x ⟨hx.1, hxp⟩).ne' hx.2
  have hJpush : ∀ q ∈ J \ {p}, f (H p) < f (H q) := by
    intro q hq
    exact hpush (H q) ⟨⟨q, hJD hq.1, rfl⟩, fun h => hq.2 (H.injective h)⟩
  have hcount : (levelPolygons (H '' Q) f (f (H p))).encard =
      (levelPolygons Q (fun x => f (H x)) (f (H p))).encard :=
    encard_levelPolygons_image H hH (fun _ _ => rfl) (f (H p))
  rw [image_union, levelPolygons_union_cap_of_fiber_subset_singleton (H.isClosedMap Q hQ)
    f (f (H p)) (H p) hcap, hcount]
  exact hf hJpush

theorem eventually_encard_levelPolygons_cap_add_one_le_of_lower_side
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (hheight : ∀ x, ℓ (H x) = ℓ x)
    {Q D J : Set E} (hQ : IsClosed Q) (hQK : Q ⊆ K.space)
    (hJ : J ∈ levelPolygons Q ℓ (ℓ p)) (hJD : J ⊆ D)
    (hside : ∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → ℓ x ≤ ℓ p) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, (∀ x ∈ H '' D \ {H p}, f x < f (H p)) →
      (levelPolygons (H '' (Q ∪ D)) f (f (H p))).encard + 1 ≤
        (levelPolygons Q ℓ (ℓ p)).encard := by
  have hinjneg : InjOn (-ℓ) K.vertices := by
    intro x hx y hy hxy
    apply hinj hx hy
    simpa only [neg_apply, neg_inj] using hxy
  have hJneg : J ∈ levelPolygons Q (-ℓ) ((-ℓ) p) := by
    exact ⟨hJ.1, fun x hx => ⟨(hJ.2 hx).1, congrArg Neg.neg (hJ.2 hx).2⟩⟩
  have hsideNeg : ∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → (-ℓ) p ≤ (-ℓ) x := by
    intro q hq
    filter_upwards [hside q hq] with x hx
    exact fun hxQ => neg_le_neg (hx hxQ)
  have hresult := eventually_encard_levelPolygons_cap_add_one_le_of_upper_side K hK hdimE
    (-ℓ) (neg_ne_zero.mpr hℓ) hinjneg hp H hH
    (fun x => by simp only [neg_apply, hheight]) hQ hQK hJneg hJD hsideNeg
  have hneg : Filter.Tendsto (fun f : E →L[ℝ] ℝ => -f) (𝓝 ℓ) (𝓝 (-ℓ)) :=
    continuous_neg.continuousAt.tendsto
  filter_upwards [hneg hresult] with f hf
  intro hpush
  have h := hf (fun x hx => neg_lt_neg (hpush x hx))
  simpa only [levelPolygons, neg_apply, neg_inj] using h
end DifferentialGeometry.Topology.PiecewiseLinear
