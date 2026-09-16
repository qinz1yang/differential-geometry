import DifferentialGeometry.Topology.PiecewiseLinear.HeightChart
import DifferentialGeometry.Topology.PiecewiseLinear.HeightCut
import DifferentialGeometry.Topology.PiecewiseLinear.HeightRotation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eventually_disjoint_fiber_of_isCompact {C : Set E} (hC : IsCompact C)
    (ℓ : E →L[ℝ] ℝ) {p : E} (hsep : ∀ x ∈ C, ℓ x ≠ ℓ p) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, Disjoint C {x | f x = f p} := by
  have hne : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∀ x ∈ C, f x ≠ f p := by
    apply hC.eventually_forall_of_forall_eventually
    intro x hx
    have hcont : Continuous (fun z : (E →L[ℝ] ℝ) × E => z.1 z.2 - z.1 p) := by fun_prop
    have hnear : ∀ᶠ z : (E →L[ℝ] ℝ) × E in 𝓝 (ℓ, x), z.1 z.2 - z.1 p ≠ 0 :=
      (hcont.continuousAt (x := (ℓ, x))).preimage_mem_nhds
        (isOpen_compl_singleton.mem_nhds (sub_ne_zero.mpr (hsep x hx)))
    exact hnear.mono fun _ hz => sub_ne_zero.mp hz
  exact hne.mono fun _ hf => Set.disjoint_left.mpr fun _ hx heq => hf _ hx heq

theorem levelPolygons_image_union_eq_of_eqOn_compl (h : E → E) (hinj : Function.Injective h)
    {A D C : Set E} (hfix : EqOn h id Cᶜ) (hDC : D ⊆ C) (ℓ : E → ℝ) (r : ℝ)
    (hdis : Disjoint C {x | ℓ x = r}) :
    levelPolygons (h '' (A ∪ D)) ℓ r = levelPolygons A ℓ r := by
  have hfiber : h '' (A ∪ D) ∩ {x | ℓ x = r} = A ∩ {x | ℓ x = r} := by
    ext x
    have hxC : ℓ x = r → x ∉ C := fun hx hmem => Set.disjoint_left.mp hdis hmem hx
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hxr⟩
      have heq : y = x := hinj (hyx.trans (hfix (hxC hxr)).symm)
      rw [heq] at hy
      exact ⟨hy.resolve_right (fun hxD => hxC hxr (hDC hxD)), hxr⟩
    · rintro ⟨hxA, hxr⟩
      exact ⟨⟨x, Or.inl hxA, hfix (hxC hxr)⟩, hxr⟩
  unfold levelPolygons
  rw [hfiber]

theorem mem_heightSingularPoints_image_cap_iff_of_eqOn_compl (H : E ≃ₜ E)
    {A B D C : Set E} (hfix : EqOn H id Cᶜ) (hC : IsClosed C) (hB : IsClosed B)
    (hAB : A ∩ B ⊆ D) (hDC : D ⊆ C) (ℓ : E → ℝ) {p : E} (hpC : p ∉ C) :
    p ∈ heightSingularPoints (H '' (A ∪ D)) ℓ ↔
      p ∈ heightSingularPoints (A ∪ B) ℓ ∧ p ∈ A := by
  have hlocal : ∀ᶠ y in 𝓝 p, y ∈ H '' (A ∪ D) ↔ y ∈ A := by
    filter_upwards [hC.isOpen_compl.mem_nhds hpC] with y hy
    constructor
    · rintro ⟨z, hz, hzy⟩
      have heq : z = y := H.injective (hzy.trans (hfix hy).symm)
      rw [heq] at hz
      exact hz.resolve_right (fun hyD => hy (hDC hyD))
    · intro hyA
      exact ⟨y, Or.inl hyA, hfix hy⟩
  rw [mem_heightSingularPoints_congr hlocal]
  by_cases hpA : p ∈ A
  · have hpB : p ∉ B := fun hpB => hpC (hDC (hAB ⟨hpA, hpB⟩))
    have hlocal' : ∀ᶠ y in 𝓝 p, y ∈ A ∪ B ↔ y ∈ A := by
      filter_upwards [hB.isOpen_compl.mem_nhds hpB] with y hy
      exact or_iff_left hy
    rw [mem_heightSingularPoints_congr hlocal', and_iff_left hpA]
  · exact ⟨fun hp => (hpA hp.1).elim, fun hp => (hpA hp.2).elim⟩

variable [FiniteDimensional ℝ E]

theorem eventually_mem_heightSingularPoints_image_cap_iff_and_encard_levelPolygons_le {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere (n + 1) K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices)
    {A B D C : Set E} (hunion : A ∪ B = K.space) (hB : IsClosed B) (hAB : A ∩ B ⊆ D)
    (hDC : D ⊆ C) (hC : IsCompact C) (hsep : ∀ x ∈ C, ℓ x ≠ ℓ p)
    (H : E ≃ₜ E) (hfix : EqOn H id Cᶜ) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      (p ∈ heightSingularPoints (H '' (A ∪ D)) f ↔ p ∈ heightSingularPoints K.space ℓ ∧ p ∈ A) ∧
      (levelPolygons (H '' (A ∪ D)) f (f p)).encard ≤ (levelPolygons K.space ℓ (ℓ p)).encard := by
  have hpC : p ∉ C := fun hpC => hsep p hpC rfl
  filter_upwards [eventually_disjoint_fiber_of_isCompact hC ℓ hsep,
    eventually_mem_heightSingularPoints_iff_and_encard_levelPolygons_eq K hK ℓ hℓ hinj hp] with f hf hstable
  refine ⟨?_, ?_⟩
  · rw [mem_heightSingularPoints_image_cap_iff_of_eqOn_compl H hfix hC.isClosed hB hAB hDC f hpC,
      hunion, hstable.1]
  · rw [levelPolygons_image_union_eq_of_eqOn_compl H H.injective hfix hDC f (f p) hf, ← hstable.2]
    apply Set.encard_mono
    rintro J ⟨hJ, hJA⟩
    exact ⟨hJ, fun x hx => ⟨hunion ▸ Or.inl (hJA hx).1, (hJA hx).2⟩⟩

theorem eventually_heightSingularPoints_image_cap_sdiff_subset_vertices
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsCombinatorialManifold 2 K) (hR : IsCombinatorialManifoldWithBoundary 2 R)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hinj : InjOn ℓ K.vertices)
    {A B D : Set E} (hunion : A ∪ B = K.space) (hB : IsClosed B) (hD : IsClosed D)
    (hAB : A ∩ B ⊆ D) (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ)
    (hheight : ∀ x, ℓ (H x) = ℓ x) (hRspace : R.space = H '' (A ∪ D)) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f ≠ 0 → InjOn f R.vertices →
      heightSingularPoints R.space f \ H '' D ⊆ H '' K.vertices := by
  let V : Set E := R.vertices \ (H '' D ∪ H '' K.vertices)
  have hV : V.Finite :=
    (Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite R.faces)).subset sdiff_subset
  have hcross : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∀ q ∈ V,
      HasPLCrossingAt (H '' K.space) {y | f y = f q} q := by
    rw [hV.eventually_all]
    intro q hq
    have hqR : q ∈ R.space := R.vertices_subset_space hq.1
    rw [hRspace] at hqR
    obtain ⟨x, hx, rfl⟩ := hqR
    have hxA : x ∈ A := hx.resolve_right (fun hxD => hq.2 (Or.inl ⟨x, hxD, rfl⟩))
    have hxK : x ∈ K.space := hunion ▸ Or.inl hxA
    have hxv : x ∉ K.vertices := fun hxv => hq.2 (Or.inr ⟨x, hxv, rfl⟩)
    exact eventually_hasPLCrossingAt_image_fiber_of_notMem_vertices K hK hdimE ℓ hinj hxK hxv H hH hheight
  have hABimage : H '' A ∩ H '' B ⊆ H '' D := by
    rintro q ⟨⟨x, hx, rfl⟩, y, hy, heq⟩
    have hyx : y = x := H.injective heq
    exact ⟨x, hAB ⟨hx, hyx ▸ hy⟩, rfl⟩
  filter_upwards [hcross] with f hf hfne hfinj
  have hflinear : f.toLinearMap ≠ 0 := by
    intro hz
    apply hfne
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  rintro q ⟨hq, hqD⟩
  by_contra hqv
  have hqV : q ∈ V := ⟨heightSingularPoints_subset_vertices R hR hdimE f.toLinearMap hflinear hfinj hq,
    fun h => h.elim hqD hqv⟩
  have hqcap : q ∈ heightSingularPoints (H '' A ∪ H '' D) f \ H '' D := by
    simpa only [hRspace, image_union] using (show q ∈ heightSingularPoints R.space f \ H '' D from ⟨hq, hqD⟩)
  rw [heightSingularPoints_cap_sdiff (H.isClosedMap B hB) (H.isClosedMap D hD) hABimage] at hqcap
  have hqold : q ∈ heightSingularPoints (H '' K.space) f := by
    rw [← hunion, image_union]
    exact hqcap.1.1
  exact hqold.2.1 (hf q hqV)

theorem exists_convex_open_neighborhood_disjoint_fibers {D A W : Set E}
    (hD : IsCompact D) (ℓ : E →L[ℝ] ℝ) {c : ℝ} (hDc : D ⊆ {x | ℓ x = c})
    (hA : A.Finite) (hAc : c ∉ ℓ '' A) (hW : IsOpen W) (hWconv : Convex ℝ W) (hDW : D ⊆ W) :
    ∃ U C : Set E, IsOpen U ∧ Convex ℝ U ∧ D ⊆ U ∧ U ⊆ W ∧ U ⊆ C ∧ IsCompact C ∧
      ∀ p ∈ A, Disjoint C {x | ℓ x = ℓ p} := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ((hA.image ℓ).isClosed.isOpen_compl.mem_nhds hAc)
  obtain ⟨r, -, hDr⟩ := hD.isBounded.subset_ball_lt 0 (0 : E)
  let U : Set E := (W ∩ ℓ ⁻¹' Metric.ball c (δ / 2)) ∩ Metric.ball 0 r
  let C : Set E := Metric.closedBall 0 r ∩ ℓ ⁻¹' Metric.closedBall c (δ / 2)
  have hhalf : 0 < δ / 2 := half_pos hδ
  refine ⟨U, C, (hW.inter (Metric.isOpen_ball.preimage ℓ.continuous)).inter Metric.isOpen_ball,
    (hWconv.inter ((convex_ball c (δ / 2)).linear_preimage ℓ.toLinearMap)).inter (convex_ball 0 r),
    ?_, inter_subset_left.trans inter_subset_left, ?_,
    (isCompact_closedBall (0 : E) r).inter_right (Metric.isClosed_closedBall.preimage ℓ.continuous), ?_⟩
  · intro x hx
    exact ⟨⟨hDW hx, by change dist (ℓ x) c < δ / 2; rw [hDc hx, dist_self]; exact hhalf⟩, hDr hx⟩
  · intro x hx
    exact ⟨Metric.ball_subset_closedBall hx.2, Metric.ball_subset_closedBall hx.1.2⟩
  · intro p hp
    apply Set.disjoint_left.mpr
    intro x hx hxp
    have hdist : dist (ℓ x) c ≤ δ / 2 := hx.2
    have hin : ℓ x ∈ Metric.ball c δ := hdist.trans_lt (half_lt_self hδ)
    exact hball hin ⟨p, hp, hxp.symm⟩

theorem eventually_heightSingularPoints_image_cap_sdiff_subset_and_encard_levelPolygons_le
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsPLSphere 2 K.space) (hR : IsCombinatorialManifoldWithBoundary 2 R)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (p : E) {A B D C : Set E} (hunion : A ∪ B = K.space) (hB : IsClosed B) (hD : IsClosed D)
    (hAB : A ∩ B ⊆ D) (hDC : D ⊆ C) (hC : IsCompact C)
    (hsep : ∀ q ∈ K.vertices \ {p}, Disjoint C {x | ℓ x = ℓ q})
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (hfix : EqOn H id Cᶜ)
    (hheight : ∀ x, ℓ (H x) = ℓ x) (hRspace : R.space = H '' (A ∪ D)) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f ≠ 0 → InjOn f R.vertices →
      heightSingularPoints R.space f \ (H '' D ∪ {H p}) ⊆ heightSingularPoints K.space ℓ ∧
      ∀ q ∈ K.vertices \ {p},
        (q ∈ heightSingularPoints R.space f ↔ q ∈ heightSingularPoints K.space ℓ ∧ q ∈ A) ∧
        (levelPolygons R.space f (f q)).encard ≤ (levelPolygons K.space ℓ (ℓ q)).encard := by
  have hV : (K.vertices \ {p}).Finite :=
    (Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)).subset sdiff_subset
  have hpoint : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∀ q ∈ K.vertices \ {p},
      (q ∈ heightSingularPoints R.space f ↔ q ∈ heightSingularPoints K.space ℓ ∧ q ∈ A) ∧
      (levelPolygons R.space f (f q)).encard ≤ (levelPolygons K.space ℓ (ℓ q)).encard := by
    rw [hV.eventually_all]
    intro q hq
    rw [hRspace]
    exact eventually_mem_heightSingularPoints_image_cap_iff_and_encard_levelPolygons_le K hK ℓ hℓ hinj hq.1
      hunion hB hAB hDC hC (fun x hx heq => Set.disjoint_left.mp (hsep q hq) hx heq) H hfix
  filter_upwards [hpoint, eventually_heightSingularPoints_image_cap_sdiff_subset_vertices K R
    hK.isCombinatorialManifold hR hdimE ℓ hinj hunion hB hD hAB H hH hheight hRspace]
    with f hf hvertices hfne hfinj
  refine ⟨?_, hf⟩
  rintro q ⟨hq, hqexc⟩
  have hqD : q ∉ H '' D := fun h => hqexc (Or.inl h)
  obtain ⟨v, hv, hvq⟩ := hvertices hfne hfinj ⟨hq, hqD⟩
  have hvp : v ≠ p := fun heq => hqexc (Or.inr (by rw [← hvq, heq]; rfl))
  have hvC : v ∉ C := fun h => Set.disjoint_left.mp (hsep v ⟨hv, hvp⟩) h rfl
  have hvfixed : H v = v := hfix hvC
  have hvq' : v = q := hvfixed.symm.trans hvq
  have hvR : v ∈ heightSingularPoints R.space f := hvq'.symm ▸ hq
  exact hvq' ▸ ((hf v ⟨hv, hvp⟩).1.mp hvR).1

end DifferentialGeometry.Topology.PiecewiseLinear
