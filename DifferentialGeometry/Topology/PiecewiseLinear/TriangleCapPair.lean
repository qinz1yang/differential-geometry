import DifferentialGeometry.Topology.PiecewiseLinear.ParametricTriangleHeightSides
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleCapSingularComparison

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_triangle_cap_pair_with_singular_comparison
    [FiniteDimensional ℝ E] (hdimE : Module.finrank ℝ E = 3)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ heightSingularPoints K.space ℓ)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W) :
    ∃ (A B D : Set E) (H : E ≃ₜ E) (m : E →ₗ[ℝ] ℝ) (U : Finset E)
      (R₁ R₂ : Geometry.SimplicialComplex ℝ E),
      A ∪ B = K.space ∧
      (levelPolygons A ℓ (ℓ p)).encard + (levelPolygons B ℓ (ℓ p)).encard =
        (levelPolygons K.space ℓ (ℓ p)).encard + 1 ∧
      IsPLBall 2 (H '' D) ∧
      (∀ x ∈ H '' D, ℓ x = ℓ (H p)) ∧
      IsPLHomeomorphOn H univ univ ∧
      (∀ x, ℓ (H x) = ℓ x) ∧
      m ≠ 0 ∧
      (∀ x ∈ H '' D \ {H p}, m (H p) < m x) ∧
      R₁.faces.Finite ∧ R₁.space = H '' (A ∪ D) ∧ IsPLSphere 2 R₁.space ∧
      R₂.faces.Finite ∧ R₂.space = H '' (B ∪ D) ∧ IsPLSphere 2 R₂.space ∧
      ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f ≠ 0 →
        InjOn f (R₁.vertices ∪ R₂.vertices ∪ (U : Set E)) →
        (∀ x ∈ H '' D \ {H p}, f (H p) < f x) →
        (heightSingularPoints R₁.space f \ {H p} ⊆
            heightSingularPoints K.space ℓ \ {p} ∧
          ∀ q ∈ K.vertices \ {p},
            (q ∈ heightSingularPoints R₁.space f ↔
              q ∈ heightSingularPoints K.space ℓ ∧ q ∈ A) ∧
            (levelPolygons R₁.space f (f q)).encard ≤
              (levelPolygons K.space ℓ (ℓ q)).encard) ∧
        (heightSingularPoints R₂.space f \ {H p} ⊆
            heightSingularPoints K.space ℓ \ {p} ∧
          ∀ q ∈ K.vertices \ {p},
            (q ∈ heightSingularPoints R₂.space f ↔
              q ∈ heightSingularPoints K.space ℓ ∧ q ∈ B) ∧
            (levelPolygons R₂.space f (f q)).encard ≤
              (levelPolygons K.space ℓ (ℓ q)).encard) := by
  classical
  obtain ⟨A, B, D, C, g, fA, fB, H, m, e, T, hunion, hinter, hJ, hfA, hfAJ,
      hfB, hfBJ, hSD, hg, hDW, -, hAD, hBD, -, -, hcount, hC, hDC, hH, hfixC,
      -, hfixV, hheight, -, hTcard, hT, he, htriangle, hm, hsep, hmsep, hsides, -⟩ :=
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
  have hsidedata :
      (((∀ q ∈ g '' stdSimplexBoundary 2 \ {p}, ∀ᶠ x in 𝓝 q,
          x ∈ A → ℓ x ≤ ℓ q) ∨
        (∀ q ∈ g '' stdSimplexBoundary 2 \ {p}, ∀ᶠ x in 𝓝 q,
          x ∈ A → ℓ q ≤ ℓ x)) ∧
        ∀ q ∈ g '' stdSimplexBoundary 2 \ {p}, ∀ᶠ x in 𝓝 q,
          x ∈ g '' stdSimplexBoundary 2 ↔ x ∈ A ∧ ℓ x = ℓ q) ∧
      (((∀ q ∈ g '' stdSimplexBoundary 2 \ {p}, ∀ᶠ x in 𝓝 q,
          x ∈ B → ℓ x ≤ ℓ q) ∨
        (∀ q ∈ g '' stdSimplexBoundary 2 \ {p}, ∀ᶠ x in 𝓝 q,
          x ∈ B → ℓ q ≤ ℓ x)) ∧
        ∀ q ∈ g '' stdSimplexBoundary 2 \ {p}, ∀ᶠ x in 𝓝 q,
          x ∈ g '' stdSimplexBoundary 2 ↔ x ∈ B ∧ ℓ x = ℓ q) := by
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
      exact ⟨⟨Or.inr hhalfA, hboundaryA⟩, ⟨Or.inl hhalfB, hboundaryB⟩⟩
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
      exact ⟨⟨Or.inl hhalfA, hboundaryA⟩, ⟨Or.inr hhalfB, hboundaryB⟩⟩
  obtain ⟨R₁, hR₁fin, hR₁space, hR₁, hR₁event⟩ :=
    exists_triangle_cap_with_singular_comparison hdimE K hK ℓ hℓ hinj hfA hg
      hfAJ rfl hAD hunion (IsPLBall.isPolyhedron ⟨fB, hfB⟩ |>.isClosed) hAB hADinter
      (hDW.trans inter_subset_right) hDC hC hsep H hH hfixC hfixV hheight e T hT
      hTcard he htriangle hsidedata.1.1 hsidedata.1.2
  obtain ⟨R₂, hR₂fin, hR₂space, hR₂, hR₂event⟩ :=
    exists_triangle_cap_with_singular_comparison hdimE K hK ℓ hℓ hinj hfB hg
      hfBJ rfl hBD ((union_comm B A).trans hunion)
      (IsPLBall.isPolyhedron ⟨fA, hfA⟩ |>.isClosed)
      ((inter_comm B A).trans_le hAB) hBDinter (hDW.trans inter_subset_right)
      hDC hC hsep H hH hfixC hfixV hheight e T hT hTcard he htriangle
      hsidedata.2.1 hsidedata.2.2
  let U : Finset E := T.image e
  refine ⟨A, B, D, H, m, U, R₁, R₂, hunion, hcount, hHD, hlevelHD, hH, hheight,
    hm, hmsep, hR₁fin, hR₁space, hR₁, hR₂fin, hR₂space, hR₂, ?_⟩
  filter_upwards [hR₁event, hR₂event] with f hf₁ hf₂
  intro hfne hfinj hcap
  have hfinj₁ : InjOn f (R₁.vertices ∪ ((T.image e : Finset E) : Set E)) := by
    apply hfinj.mono
    rintro x (hx | hx)
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
  have hfinj₂ : InjOn f (R₂.vertices ∪ ((T.image e : Finset E) : Set E)) := by
    apply hfinj.mono
    rintro x (hx | hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  exact ⟨hf₁ hfne hfinj₁ hcap, hf₂ hfne hfinj₂ hcap⟩

end DifferentialGeometry.Topology.PiecewiseLinear
