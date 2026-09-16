import DifferentialGeometry.Topology.PiecewiseLinear.HeightPerturbationSymmetry
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeHeightDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.ParametricTriangleHeightSides
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleCapSingularComparisonSymmetry

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_small_opposite_triangle_cap_pair_with_level_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdimE : Module.finrank ℝ E = 3)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ heightSingularPoints K.space ℓ)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A B D J : Set E) (H : E ≃ₜ E) (R₁ R₂ : Geometry.SimplicialComplex ℝ E)
      (f₁ f₂ : E →L[ℝ] ℝ),
      A ∪ B = K.space ∧ A ∩ B = J ∧ J ∈ levelPolygons K.space ℓ (ℓ p) ∧
      (levelPolygons A ℓ (ℓ p)).encard + (levelPolygons B ℓ (ℓ p)).encard =
        (levelPolygons K.space ℓ (ℓ p)).encard + 1 ∧
      J ⊆ D ∧ IsPLBall 2 (H '' D) ∧ (∀ x ∈ H '' D, ℓ x = ℓ (H p)) ∧
      IsPLHomeomorphOn H univ univ ∧
      R₁.faces.Finite ∧ R₁.space = H '' (A ∪ D) ∧ IsPLSphere 2 R₁.space ∧
      R₂.faces.Finite ∧ R₂.space = H '' (B ∪ D) ∧ IsPLSphere 2 R₂.space ∧
      dist f₁ ℓ < ε ∧ f₁ ≠ 0 ∧ InjOn f₁ R₁.vertices ∧
      dist f₂ ℓ < ε ∧ f₂ ≠ 0 ∧ InjOn f₂ R₂.vertices ∧
      (∀ x ∈ K.vertices, ∀ y ∈ K.vertices, ℓ x < ℓ y → f₁ x < f₁ y) ∧
      (∀ x ∈ K.vertices, ∀ y ∈ K.vertices, ℓ x < ℓ y → f₂ x < f₂ y) ∧
      (((∀ x ∈ H '' D \ {H p}, f₁ (H p) < f₁ x) ∧
          (∀ x ∈ H '' D \ {H p}, f₂ x < f₂ (H p))) ∨
        ((∀ x ∈ H '' D \ {H p}, f₁ x < f₁ (H p)) ∧
          (∀ x ∈ H '' D \ {H p}, f₂ (H p) < f₂ x))) ∧
      (heightSingularPoints R₁.space f₁ \ {H p} ⊆
          heightSingularPoints K.space ℓ \ {p} ∧
        ∀ q ∈ K.vertices \ {p},
          (q ∈ heightSingularPoints R₁.space f₁ ↔
            q ∈ heightSingularPoints K.space ℓ ∧ q ∈ A) ∧
          (levelPolygons R₁.space f₁ (f₁ q)).encard ≤
            (levelPolygons K.space ℓ (ℓ q)).encard) ∧
      (heightSingularPoints R₂.space f₂ \ {H p} ⊆
          heightSingularPoints K.space ℓ \ {p} ∧
        ∀ q ∈ K.vertices \ {p},
          (q ∈ heightSingularPoints R₂.space f₂ ↔
            q ∈ heightSingularPoints K.space ℓ ∧ q ∈ B) ∧
          (levelPolygons R₂.space f₂ (f₂ q)).encard ≤
            (levelPolygons K.space ℓ (ℓ q)).encard) ∧
      EqOn H id (K.vertices \ {p}) ∧ EqOn H id Wᶜ ∧
      (levelPolygons R₁.space f₁ (f₁ (H p))).encard + 1 ≤ (levelPolygons A ℓ (ℓ p)).encard ∧
      (levelPolygons R₂.space f₂ (f₂ (H p))).encard + 1 ≤ (levelPolygons B ℓ (ℓ p)).encard ∧
      (A ∪ D) ∩ (B ∪ D) = D ∧ ((A ∪ D) ∪ (B ∪ D)) \ (D \ J) = K.space ∧
      ∃ u : (Fin 3 → ℝ) → E, IsPLHomeomorphOn u (stdSimplex ℝ (Fin 3)) D ∧
        u '' stdSimplexBoundary 2 = J := by
  classical
  obtain ⟨A, B, D, C, g, fA, fB, H, m, e, T, hunion, hinter, hJ, hfA, hfAJ,
      hfB, hfBJ, hSD, hg, hDW, -, hAD, hBD, hcap, hrecover, hcount, hC, hDC, hH, hfixC,
      hfixW, hfixV, hheight, -, hTcard, hT, he, htriangle, -, hsep, hmsep, hsides, -⟩ :=
    exists_parameterized_triangle_cut_with_opposite_height_sides K hK hdimE ℓ hℓ
      hinj hp hW hWconv hKW
  have hD : IsPLBall 2 D := ⟨g, hg⟩
  have hHD : IsPLBall 2 (H '' D) :=
    hD.of_isPLHomeomorphOn (hH.restrict hD.isPolyhedron (subset_univ D))
  have hlevelHD : ∀ x ∈ H '' D, ℓ x = ℓ (H p) := by
    rintro _ ⟨x, hxD, rfl⟩
    exact (hheight x).trans ((hDW hxD).2.trans (hheight p).symm)
  have hAB : A ∩ B ⊆ D := by
    intro x hx
    exact (hSD.symm.subset (hinter.subset hx)).2
  have hADinter : A ∩ D ⊆ g '' stdSimplexBoundary 2 := by
    intro x hx
    have hxK : x ∈ K.space := hunion ▸ (show x ∈ A ∪ B from Or.inl hx.1)
    exact hSD.subset ⟨hxK, hx.2⟩
  have hBDinter : B ∩ D ⊆ g '' stdSimplexBoundary 2 := by
    intro x hx
    have hxK : x ∈ K.space := hunion ▸ (show x ∈ A ∪ B from Or.inr hx.1)
    exact hSD.subset ⟨hxK, hx.2⟩
  have hJsubD : g '' stdSimplexBoundary 2 ⊆ D := by
    rw [← hSD]
    exact inter_subset_right
  have hKvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hpv := heightSingularPoints_subset_vertices K
    hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary hdimE ℓ.toLinearMap
    hlinear hinj hp
  have hAK : A ⊆ K.space := subset_union_left.trans_eq hunion
  have hBK : B ⊆ K.space := subset_union_right.trans_eq hunion
  have hJA : g '' stdSimplexBoundary 2 ∈ levelPolygons A ℓ (ℓ p) :=
    ⟨hJ.1, fun x hx => ⟨(hinter.symm.subset hx).1, (hJ.2 hx).2⟩⟩
  have hJB : g '' stdSimplexBoundary 2 ∈ levelPolygons B ℓ (ℓ p) :=
    ⟨hJ.1, fun x hx => ⟨(hinter.symm.subset hx).2, (hJ.2 hx).2⟩⟩
  rcases hsides with hsides | hsides
  · have hhalfA : ∀ q ∈ g '' stdSimplexBoundary 2 \ {p}, ∀ᶠ x in 𝓝 q,
        x ∈ A → ℓ q ≤ ℓ x := by
      intro q hq
      have hqlevel : ℓ q = ℓ p := (hJ.2 hq.1).2
      filter_upwards [hsides q hq] with x hx
      intro hxA
      rw [hqlevel]
      exact (hx.1.mp hxA).2
    have hhalfB : ∀ q ∈ g '' stdSimplexBoundary 2 \ {p}, ∀ᶠ x in 𝓝 q,
        x ∈ B → ℓ x ≤ ℓ q := by
      intro q hq
      have hqlevel : ℓ q = ℓ p := (hJ.2 hq.1).2
      filter_upwards [hsides q hq] with x hx
      intro hxB
      rw [hqlevel]
      exact (hx.2.mp hxB).2
    have hboundaryA : ∀ q ∈ g '' stdSimplexBoundary 2 \ {p},
        ∀ᶠ x in 𝓝 q,
          x ∈ g '' stdSimplexBoundary 2 ↔ x ∈ A ∧ ℓ x = ℓ q := by
      intro q hq
      have hqlevel : ℓ q = ℓ p := (hJ.2 hq.1).2
      have hsideA := (hsides q hq).mono fun _ hx => hx.1
      have hsideB := (hsides q hq).mono fun _ hx => hx.2
      have h := eventually_mem_inter_iff_left_and_eq_of_opposite_halfSpaces
        hinter ℓ (ℓ p) hsideA hsideB
      simpa only [hqlevel] using h
    have hboundaryB : ∀ q ∈ g '' stdSimplexBoundary 2 \ {p},
        ∀ᶠ x in 𝓝 q,
          x ∈ g '' stdSimplexBoundary 2 ↔ x ∈ B ∧ ℓ x = ℓ q := by
      intro q hq
      have hqlevel : ℓ q = ℓ p := (hJ.2 hq.1).2
      have hsideA := (hsides q hq).mono fun _ hx => hx.1
      have hsideB := (hsides q hq).mono fun _ hx => hx.2
      have h := eventually_mem_inter_iff_right_and_eq_of_opposite_halfSpaces
        hinter ℓ (ℓ p) hsideA hsideB
      simpa only [hqlevel] using h
    obtain ⟨R₁, hR₁fin, hR₁space, hR₁, hR₁event⟩ :=
      exists_triangle_cap_with_singular_comparison hdimE K hK ℓ hℓ hinj hfA hg
        hfAJ rfl hAD hunion (IsPLBall.isPolyhedron ⟨fB, hfB⟩ |>.isClosed) hAB
        hADinter (hDW.trans inter_subset_right) hDC hC hsep H hH hfixC hfixV
        hheight e T hT hTcard he htriangle (Or.inr hhalfA) hboundaryA
    obtain ⟨R₂, hR₂fin, hR₂space, hR₂, hR₂event⟩ :=
      exists_triangle_cap_with_singular_comparison_of_cap_below hdimE K hK ℓ hℓ
        hinj hfB hg hfBJ rfl hBD ((union_comm B A).trans hunion)
        (IsPLBall.isPolyhedron ⟨fA, hfA⟩ |>.isClosed)
        ((inter_comm B A).trans_le hAB) hBDinter (hDW.trans inter_subset_right)
        hDC hC hsep H hH hfixC hfixV hheight e T hT hTcard he htriangle
        (Or.inl hhalfB) hboundaryB
    have hdelete₁ := eventually_encard_levelPolygons_cap_add_one_le_of_upper_side K
      hK.isCombinatorialManifold hdimE ℓ hℓ hinj hpv H hH hheight
      (IsPLBall.isPolyhedron ⟨fA, hfA⟩ |>.isClosed) hAK hJA hJsubD (by
        intro q hq
        have hqlevel : ℓ q = ℓ p := (hJ.2 hq.1).2
        rw [← hqlevel]
        exact hhalfA q hq)
    have hdelete₂ := eventually_encard_levelPolygons_cap_add_one_le_of_lower_side K
      hK.isCombinatorialManifold hdimE ℓ hℓ hinj hpv H hH hheight
      (IsPLBall.isPolyhedron ⟨fB, hfB⟩ |>.isClosed) hBK hJB hJsubD (by
        intro q hq
        have hqlevel : ℓ q = ℓ p := (hJ.2 hq.1).2
        rw [← hqlevel]
        exact hhalfB q hq)
    have hR₁vertices : R₁.vertices.Finite :=
      Set.Finite.preimage Finset.singleton_injective.injOn hR₁fin
    have hR₂vertices : R₂.vertices.Finite :=
      Set.Finite.preimage Finset.singleton_injective.injOn hR₂fin
    have hgeneral₁ : (R₁.vertices ∪ ((T.image e : Finset E) : Set E)).Finite :=
      hR₁vertices.union (T.image e).finite_toSet
    have hgeneral₂ : (R₂.vertices ∪ ((T.image e : Finset E) : Set E)).Finite :=
      hR₂vertices.union (T.image e).finite_toSet
    have hclose : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, dist f ℓ < ε :=
      Metric.ball_mem_nhds ℓ hε
    obtain ⟨δ₁, hδ₁, hδgood₁⟩ := Metric.mem_nhds_iff.mp (hR₁event.and (hdelete₁.and hclose))
    obtain ⟨f₁, hfδ₁, hf₁ne, hf₁inj, hf₁order, hf₁cap⟩ :=
      exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_of_isPolyhedron
        hgeneral₁ hKvertices ℓ (LinearMap.toContinuousLinearMap m) hℓ hHD.isPolyhedron
        (H p) hlevelHD hmsep hδ₁
    obtain ⟨hf₁comparison, hf₁delete, hf₁ε⟩ := hδgood₁ hfδ₁
    have hcomparison₁ := hf₁comparison hf₁ne hf₁inj hf₁cap
    have hdecrease₁ := hf₁delete hf₁cap
    rw [← hR₁space] at hdecrease₁
    obtain ⟨δ₂, hδ₂, hδgood₂⟩ := Metric.mem_nhds_iff.mp (hR₂event.and (hdelete₂.and hclose))
    obtain ⟨f₂, hfδ₂, hf₂ne, hf₂inj, hf₂order, hf₂cap⟩ :=
      exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_below_of_isPolyhedron
        hgeneral₂ hKvertices ℓ (LinearMap.toContinuousLinearMap m) hℓ hHD.isPolyhedron
        (H p) hlevelHD hmsep hδ₂
    obtain ⟨hf₂comparison, hf₂delete, hf₂ε⟩ := hδgood₂ hfδ₂
    have hcomparison₂ := hf₂comparison hf₂ne hf₂inj hf₂cap
    have hdecrease₂ := hf₂delete hf₂cap
    rw [← hR₂space] at hdecrease₂
    exact ⟨A, B, D, g '' stdSimplexBoundary 2, H, R₁, R₂, f₁, f₂, hunion,
      hinter, hJ, hcount, hJsubD, hHD, hlevelHD, hH, hR₁fin, hR₁space, hR₁,
      hR₂fin, hR₂space, hR₂, hf₁ε, hf₁ne, hf₁inj.mono subset_union_left,
      hf₂ε, hf₂ne, hf₂inj.mono subset_union_left, hf₁order, hf₂order,
      Or.inl ⟨hf₁cap, hf₂cap⟩, hcomparison₁, hcomparison₂, hfixV, hfixW, hdecrease₁, hdecrease₂,
      hcap, hrecover, g, hg, rfl⟩
  · have hhalfA : ∀ q ∈ g '' stdSimplexBoundary 2 \ {p}, ∀ᶠ x in 𝓝 q,
        x ∈ A → ℓ x ≤ ℓ q := by
      intro q hq
      have hqlevel : ℓ q = ℓ p := (hJ.2 hq.1).2
      filter_upwards [hsides q hq] with x hx
      intro hxA
      rw [hqlevel]
      exact (hx.1.mp hxA).2
    have hhalfB : ∀ q ∈ g '' stdSimplexBoundary 2 \ {p}, ∀ᶠ x in 𝓝 q,
        x ∈ B → ℓ q ≤ ℓ x := by
      intro q hq
      have hqlevel : ℓ q = ℓ p := (hJ.2 hq.1).2
      filter_upwards [hsides q hq] with x hx
      intro hxB
      rw [hqlevel]
      exact (hx.2.mp hxB).2
    have hboundaryA : ∀ q ∈ g '' stdSimplexBoundary 2 \ {p},
        ∀ᶠ x in 𝓝 q,
          x ∈ g '' stdSimplexBoundary 2 ↔ x ∈ A ∧ ℓ x = ℓ q := by
      intro q hq
      have hqlevel : ℓ q = ℓ p := (hJ.2 hq.1).2
      have hsideA := (hsides q hq).mono fun _ hx => hx.1
      have hsideB := (hsides q hq).mono fun _ hx => hx.2
      have h := eventually_mem_inter_iff_right_and_eq_of_opposite_halfSpaces
        ((inter_comm B A).trans hinter) ℓ (ℓ p) hsideB hsideA
      simpa only [hqlevel] using h
    have hboundaryB : ∀ q ∈ g '' stdSimplexBoundary 2 \ {p},
        ∀ᶠ x in 𝓝 q,
          x ∈ g '' stdSimplexBoundary 2 ↔ x ∈ B ∧ ℓ x = ℓ q := by
      intro q hq
      have hqlevel : ℓ q = ℓ p := (hJ.2 hq.1).2
      have hsideA := (hsides q hq).mono fun _ hx => hx.1
      have hsideB := (hsides q hq).mono fun _ hx => hx.2
      have h := eventually_mem_inter_iff_left_and_eq_of_opposite_halfSpaces
        ((inter_comm B A).trans hinter) ℓ (ℓ p) hsideB hsideA
      simpa only [hqlevel] using h
    obtain ⟨R₁, hR₁fin, hR₁space, hR₁, hR₁event⟩ :=
      exists_triangle_cap_with_singular_comparison_of_cap_below hdimE K hK ℓ hℓ
        hinj hfA hg hfAJ rfl hAD hunion
        (IsPLBall.isPolyhedron ⟨fB, hfB⟩ |>.isClosed) hAB hADinter
        (hDW.trans inter_subset_right) hDC hC hsep H hH hfixC hfixV hheight e T hT
        hTcard he htriangle (Or.inl hhalfA) hboundaryA
    obtain ⟨R₂, hR₂fin, hR₂space, hR₂, hR₂event⟩ :=
      exists_triangle_cap_with_singular_comparison hdimE K hK ℓ hℓ hinj hfB hg
        hfBJ rfl hBD ((union_comm B A).trans hunion)
        (IsPLBall.isPolyhedron ⟨fA, hfA⟩ |>.isClosed)
        ((inter_comm B A).trans_le hAB) hBDinter (hDW.trans inter_subset_right)
        hDC hC hsep H hH hfixC hfixV hheight e T hT hTcard he htriangle
        (Or.inr hhalfB) hboundaryB
    have hdelete₁ := eventually_encard_levelPolygons_cap_add_one_le_of_lower_side K
      hK.isCombinatorialManifold hdimE ℓ hℓ hinj hpv H hH hheight
      (IsPLBall.isPolyhedron ⟨fA, hfA⟩ |>.isClosed) hAK hJA hJsubD (by
        intro q hq
        have hqlevel : ℓ q = ℓ p := (hJ.2 hq.1).2
        rw [← hqlevel]
        exact hhalfA q hq)
    have hdelete₂ := eventually_encard_levelPolygons_cap_add_one_le_of_upper_side K
      hK.isCombinatorialManifold hdimE ℓ hℓ hinj hpv H hH hheight
      (IsPLBall.isPolyhedron ⟨fB, hfB⟩ |>.isClosed) hBK hJB hJsubD (by
        intro q hq
        have hqlevel : ℓ q = ℓ p := (hJ.2 hq.1).2
        rw [← hqlevel]
        exact hhalfB q hq)
    have hR₁vertices : R₁.vertices.Finite :=
      Set.Finite.preimage Finset.singleton_injective.injOn hR₁fin
    have hR₂vertices : R₂.vertices.Finite :=
      Set.Finite.preimage Finset.singleton_injective.injOn hR₂fin
    have hgeneral₁ : (R₁.vertices ∪ ((T.image e : Finset E) : Set E)).Finite :=
      hR₁vertices.union (T.image e).finite_toSet
    have hgeneral₂ : (R₂.vertices ∪ ((T.image e : Finset E) : Set E)).Finite :=
      hR₂vertices.union (T.image e).finite_toSet
    have hclose : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, dist f ℓ < ε :=
      Metric.ball_mem_nhds ℓ hε
    obtain ⟨δ₁, hδ₁, hδgood₁⟩ := Metric.mem_nhds_iff.mp (hR₁event.and (hdelete₁.and hclose))
    obtain ⟨f₁, hfδ₁, hf₁ne, hf₁inj, hf₁order, hf₁cap⟩ :=
      exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_below_of_isPolyhedron
        hgeneral₁ hKvertices ℓ (LinearMap.toContinuousLinearMap m) hℓ hHD.isPolyhedron
        (H p) hlevelHD hmsep hδ₁
    obtain ⟨hf₁comparison, hf₁delete, hf₁ε⟩ := hδgood₁ hfδ₁
    have hcomparison₁ := hf₁comparison hf₁ne hf₁inj hf₁cap
    have hdecrease₁ := hf₁delete hf₁cap
    rw [← hR₁space] at hdecrease₁
    obtain ⟨δ₂, hδ₂, hδgood₂⟩ := Metric.mem_nhds_iff.mp (hR₂event.and (hdelete₂.and hclose))
    obtain ⟨f₂, hfδ₂, hf₂ne, hf₂inj, hf₂order, hf₂cap⟩ :=
      exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_of_isPolyhedron
        hgeneral₂ hKvertices ℓ (LinearMap.toContinuousLinearMap m) hℓ hHD.isPolyhedron
        (H p) hlevelHD hmsep hδ₂
    obtain ⟨hf₂comparison, hf₂delete, hf₂ε⟩ := hδgood₂ hfδ₂
    have hcomparison₂ := hf₂comparison hf₂ne hf₂inj hf₂cap
    have hdecrease₂ := hf₂delete hf₂cap
    rw [← hR₂space] at hdecrease₂
    exact ⟨A, B, D, g '' stdSimplexBoundary 2, H, R₁, R₂, f₁, f₂, hunion,
      hinter, hJ, hcount, hJsubD, hHD, hlevelHD, hH, hR₁fin, hR₁space, hR₁,
      hR₂fin, hR₂space, hR₂, hf₁ε, hf₁ne, hf₁inj.mono subset_union_left,
      hf₂ε, hf₂ne, hf₂inj.mono subset_union_left, hf₁order, hf₂order,
      Or.inr ⟨hf₁cap, hf₂cap⟩, hcomparison₁, hcomparison₂, hfixV, hfixW, hdecrease₁, hdecrease₂,
      hcap, hrecover, g, hg, rfl⟩

theorem exists_small_opposite_triangle_cap_pair_with_singular_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdimE : Module.finrank ℝ E = 3)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ heightSingularPoints K.space ℓ)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A B D J : Set E) (H : E ≃ₜ E) (R₁ R₂ : Geometry.SimplicialComplex ℝ E)
      (f₁ f₂ : E →L[ℝ] ℝ),
      A ∪ B = K.space ∧ A ∩ B = J ∧ J ∈ levelPolygons K.space ℓ (ℓ p) ∧
      (levelPolygons A ℓ (ℓ p)).encard + (levelPolygons B ℓ (ℓ p)).encard =
        (levelPolygons K.space ℓ (ℓ p)).encard + 1 ∧
      J ⊆ D ∧ IsPLBall 2 (H '' D) ∧ (∀ x ∈ H '' D, ℓ x = ℓ (H p)) ∧
      IsPLHomeomorphOn H univ univ ∧
      R₁.faces.Finite ∧ R₁.space = H '' (A ∪ D) ∧ IsPLSphere 2 R₁.space ∧
      R₂.faces.Finite ∧ R₂.space = H '' (B ∪ D) ∧ IsPLSphere 2 R₂.space ∧
      dist f₁ ℓ < ε ∧ f₁ ≠ 0 ∧ InjOn f₁ R₁.vertices ∧
      dist f₂ ℓ < ε ∧ f₂ ≠ 0 ∧ InjOn f₂ R₂.vertices ∧
      (∀ x ∈ K.vertices, ∀ y ∈ K.vertices, ℓ x < ℓ y → f₁ x < f₁ y) ∧
      (∀ x ∈ K.vertices, ∀ y ∈ K.vertices, ℓ x < ℓ y → f₂ x < f₂ y) ∧
      (((∀ x ∈ H '' D \ {H p}, f₁ (H p) < f₁ x) ∧
          (∀ x ∈ H '' D \ {H p}, f₂ x < f₂ (H p))) ∨
        ((∀ x ∈ H '' D \ {H p}, f₁ x < f₁ (H p)) ∧
          (∀ x ∈ H '' D \ {H p}, f₂ (H p) < f₂ x))) ∧
      (heightSingularPoints R₁.space f₁ \ {H p} ⊆
          heightSingularPoints K.space ℓ \ {p} ∧
        ∀ q ∈ K.vertices \ {p},
          (q ∈ heightSingularPoints R₁.space f₁ ↔
            q ∈ heightSingularPoints K.space ℓ ∧ q ∈ A) ∧
          (levelPolygons R₁.space f₁ (f₁ q)).encard ≤
            (levelPolygons K.space ℓ (ℓ q)).encard) ∧
      (heightSingularPoints R₂.space f₂ \ {H p} ⊆
          heightSingularPoints K.space ℓ \ {p} ∧
        ∀ q ∈ K.vertices \ {p},
          (q ∈ heightSingularPoints R₂.space f₂ ↔
            q ∈ heightSingularPoints K.space ℓ ∧ q ∈ B) ∧
          (levelPolygons R₂.space f₂ (f₂ q)).encard ≤
            (levelPolygons K.space ℓ (ℓ q)).encard) := by
  obtain ⟨A, B, D, J, H, R₁, R₂, f₁, f₂, hAB, hAJ, hJ, hcount, hJD, hD, hlevel,
    hH, hR₁fin, hR₁space, hR₁, hR₂fin, hR₂space, hR₂, hf₁close, hf₁ne, hf₁inj,
    hf₂close, hf₂ne, hf₂inj, hf₁order, hf₂order, hpush, hcomparison₁, hcomparison₂,
    -, -, -, -, -, -, -⟩ :=
    exists_small_opposite_triangle_cap_pair_with_level_comparison hdimE K hK ℓ hℓ hinj hp
      hW hWconv hKW hε
  exact ⟨A, B, D, J, H, R₁, R₂, f₁, f₂, hAB, hAJ, hJ, hcount, hJD, hD, hlevel,
    hH, hR₁fin, hR₁space, hR₁, hR₂fin, hR₂space, hR₂, hf₁close, hf₁ne, hf₁inj,
    hf₂close, hf₂ne, hf₂inj, hf₁order, hf₂order, hpush, hcomparison₁, hcomparison₂⟩
end DifferentialGeometry.Topology.PiecewiseLinear
