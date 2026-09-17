import DifferentialGeometry.Topology.PlanarJordan.BandCutRounding
import DifferentialGeometry.Topology.PlanarJordan.CutPair
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.PlanarJordan.BoundaryGermExtension
import DifferentialGeometry.Topology.PlanarJordan.Homeomorph
import DifferentialGeometry.Topology.Manifold.AmbientCornerRoundingComparison

open Set Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.PlanarJordan

noncomputable section

attribute [local instance] instChartedSpaceFinTwo

theorem exists_diffeomorph_eqOn_neighborhood_of_corner_curve
    (c : PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane)
      Schoenflies.Plane Schoenflies.Plane ∞)
    (e : PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane) (𝓘(ℝ, PUnit.{1}).prod 𝓘(ℝ, ℝ × ℝ))
      Schoenflies.Plane (Fin 2 × (ℝ × ℝ)) ∞)
    {r k : ℝ} (hr : 0 < r) (hk : 0 < k)
    (htarget : e.target = univ ×ˢ (Ioo (-r) r ×ˢ Ioo (-k) k))
    (hec : e.source ⊆ c.source)
    {J₀ J₁ : Set Schoenflies.Plane}
    (hJ₀ : Schoenflies.IsJordanCurve J₀) (hJ₁ : Schoenflies.IsJordanCurve J₁)
    (hsource : J₀ ⊆ c.source)
    (hc : c.toOpenPartialHomeomorph.IsImage
      (closure (Schoenflies.inside J₀)) (closure (Schoenflies.inside J₁)))
    (hreg₀ : ∀ p ∈ J₀, p ∉ e.source →
      ∃ U : Set Schoenflies.Plane, ∃ f : Schoenflies.Plane → ℝ,
        IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
        (∀ x ∈ U, x ∈ J₀ ↔ f x = 0) ∧ fderiv ℝ f p ≠ 0)
    (hraw :
      (∀ p ∈ e.target, e.symm p ∈ closure (Schoenflies.inside J₀) ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) ∨
      (∀ p ∈ e.target, e.symm p ∈ closure (Schoenflies.inside J₀) ↔ p.2.1 ≤ 0 ∨ p.2.2 ≤ 0)) :
    ∃ F : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane,
      F '' J₀ = J₁ ∧ F '' closure (Schoenflies.inside J₀) = closure (Schoenflies.inside J₁) ∧
      ∃ U : Set Schoenflies.Plane, IsOpen U ∧ J₀ ⊆ U ∧ U ⊆ c.source ∧ EqOn F c U := by
  let f := c.symm.trans e
  have hft : f.target = e.target := by
    ext p
    change (p ∈ e.target ∧ e.symm p ∈ c.source) ↔ p ∈ e.target
    exact ⟨And.left, fun hp => ⟨hp, hec (e.map_target hp)⟩⟩
  have htarget₁ : f.target = univ ×ˢ (Ioo (-r) r ×ˢ Ioo (-k) k) := hft.trans htarget
  have hzrect : (0 : ℝ × ℝ) ∈ Ioo (-r) r ×ˢ Ioo (-k) k :=
    ⟨⟨neg_neg_of_pos hr, hr⟩, neg_neg_of_pos hk, hk⟩
  let δ := min r k / 2
  have hδ : 0 < δ := half_pos (lt_min hr hk)
  have hδlt : δ < min r k := half_lt_self (lt_min hr hk)
  have hstrip : (univ : Set (Fin 2)) ×ˢ closedBall (0 : ℝ × ℝ) δ ⊆ f.target := by
    rw [htarget₁]
    rintro ⟨i, x, y⟩ ⟨_, hz⟩
    have hh : max |x| |y| ≤ δ := by
      simp only [mem_closedBall, Prod.dist_eq, Real.dist_eq] at hz
      change max |x - 0| |y - 0| ≤ δ at hz
      simpa only [sub_zero] using hz
    have hx := (le_max_left |x| |y|).trans hh
    have hy := (le_max_right |x| |y|).trans hh
    have hdr := hδlt.trans_le (min_le_left r k)
    have hdk := hδlt.trans_le (min_le_right r k)
    exact ⟨mem_univ _, ⟨by linarith [(abs_le.mp hx).1], by linarith [(abs_le.mp hx).2]⟩,
      by linarith [(abs_le.mp hy).1], by linarith [(abs_le.mp hy).2]⟩
  obtain ⟨R₀, R₁, _, _, hK₀, hKs₀, _, hfixi₀, hquad₀, hreflex₀, _,
    _, _, _, _, _, _, _, _, _, _, hRc, hcomm, _, hunround⟩ := c.exists_diffeomorph_smoothAbs_corner_comparison e hδ hstrip
  have hrounded : c.toOpenPartialHomeomorph.IsImage
      (R₀ '' closure (Schoenflies.inside J₀)) (R₁ '' closure (Schoenflies.inside J₁)) := by
    intro x hx
    have hxR : R₀.symm x ∈ c.source := by
      obtain ⟨z, hz, hzx⟩ := hRc.symm ▸ hx
      have he : R₀.symm x = z := by rw [← hzx, R₀.symm_apply_apply]
      exact he.symm ▸ hz
    have he : R₁.symm (c x) = c (R₀.symm x) := by
      apply R₁.injective
      rw [R₁.apply_symm_apply, hcomm _ hxR, R₀.apply_symm_apply]
    change c x ∈ R₁ '' closure (Schoenflies.inside J₁) ↔ x ∈ R₀ '' closure (Schoenflies.inside J₀)
    have hm₀ : x ∈ R₀ '' closure (Schoenflies.inside J₀) ↔
        R₀.symm x ∈ closure (Schoenflies.inside J₀) := mem_image_equiv
    have hm₁ : c x ∈ R₁ '' closure (Schoenflies.inside J₁) ↔
        R₁.symm (c x) ∈ closure (Schoenflies.inside J₁) := mem_image_equiv
    rw [hm₀, hm₁, he]
    exact hc hxR
  have hprofile₀ :
      e.toOpenPartialHomeomorph.IsImage (R₀ '' closure (Schoenflies.inside J₀))
        {p | Real.smoothAbs δ (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2} ∨
      e.toOpenPartialHomeomorph.IsImage (R₀ '' closure (Schoenflies.inside J₀))
        {p | p.2.1 + p.2.2 ≤ Real.smoothAbs δ (p.2.1 - p.2.2)} := by
    rcases hraw with hraw | hraw
    · left
      rw [hquad₀ _ hraw]
      intro x hx
      exact (e.toOpenPartialHomeomorph.mem_smoothAbsQuadrantSet_iff _ _ hx).symm
    · right
      rw [hreflex₀ _ hraw]
      intro x hx
      constructor
      · intro hq
        exact Or.inr ⟨e x, ⟨e.map_source hx, hq⟩, e.left_inv hx⟩
      · rintro (⟨_, hn⟩ | ⟨q, hq, hqx⟩)
        · exact (hn hx).elim
        · have he : e x = q := by rw [← hqx]; exact e.right_inv hq.1
          change (e x) ∈ {p | p.2.1 + p.2.2 ≤ Real.smoothAbs δ (p.2.1 - p.2.2)}
          rw [he]
          exact hq.2
  obtain ⟨η₀, hη₀, hη₀range⟩ := exists_circle_embedding_of_corner_rounding e hJ₀ hreg₀ R₀ hK₀.isClosed hKs₀ hfixi₀ hprofile₀
  have hηsource : range η₀ ⊆ c.source := by
    rw [hη₀range]
    exact (image_mono hsource).trans hRc.subset
  let η₁ := c ∘ η₀
  have hη₁ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ η₁ :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph c hη₀ hηsource
  have hη₁range : range η₁ = R₁ '' J₁ := by
    apply (isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero hη₁.isEmbedding).eq_of_subset
      (by
        obtain ⟨f, hf, rfl⟩ := hJ₁
        refine ⟨R₁ ∘ f, ⟨R₁.continuous.comp_continuousOn hf.continuousOn, ?_, ?_⟩, ?_⟩
        · simp only [Function.comp_apply, hf.closes]
        · exact R₁.injective.injOn.comp hf.injOn (mapsTo_univ _ _)
        · rw [image_comp])
    rintro _ ⟨x, rfl⟩
    have hfr := hrounded.frontier (hηsource (mem_range_self x))
    rw [← R₀.image_frontier, ← R₁.image_frontier,
      (Schoenflies.jordan_curve_theorem hJ₀).frontier_closure_inside,
      (Schoenflies.jordan_curve_theorem hJ₁).frontier_closure_inside] at hfr
    exact hfr.mpr (hη₀range ▸ mem_range_self x)
  have hcη : c.toOpenPartialHomeomorph.IsImage
      (closure (Schoenflies.inside (range η₀))) (closure (Schoenflies.inside (range η₁))) := by
    rw [hη₀range, hη₁range, ← Schoenflies.image_closure_inside_homeomorph,
      ← Schoenflies.image_closure_inside_homeomorph]
    exact hrounded
  obtain ⟨Q, hQcurve, _, W, hW, hηW, _, hQc⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_jordan_curve hη₀ hη₁ c hcη hηsource
  have hcornerJ : e.symm '' (univ ×ˢ {(0 : ℝ × ℝ)}) ⊆ J₀ := by
    have hfr := (Schoenflies.jordan_curve_theorem hJ₀).frontier_closure_inside
    rcases hraw with hraw | hraw
    · have hI : e.toOpenPartialHomeomorph.IsImage (closure (Schoenflies.inside J₀))
          {p : Fin 2 × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2} := by
        intro x hx
        have he := hraw (e x) (e.map_source hx)
        have hei : e.symm (e x) = x := e.left_inv hx
        rw [hei] at he
        exact he.symm
      have hfrI := hI.frontier
      rw [hfr] at hfrI
      rintro _ ⟨⟨i, z⟩, ⟨_, hz⟩, rfl⟩
      obtain rfl := mem_singleton_iff.mp hz
      have ht : (i, (0 : ℝ × ℝ)) ∈ e.target := htarget.symm ▸ ⟨mem_univ _, hzrect⟩
      apply (hfrI (e.map_target ht)).mp
      change e (e.symm (i, 0)) ∈ frontier {p : Fin 2 × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2}
      have hei : e (e.symm (i, 0)) = (i, 0) := e.right_inv ht
      rw [hei, frontier_eq_closure_inter_closure]
      constructor
      · exact subset_closure ⟨le_rfl, le_rfl⟩
      · apply closure_mono (show (univ : Set (Fin 2)) ×ˢ (Iio (0 : ℝ) ×ˢ univ) ⊆
            {p : Fin 2 × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2}ᶜ from
          fun p hp hq => (not_lt_of_ge hq.1) hp.2.1)
        simp only [closure_prod_eq, closure_univ, closure_Iio, mem_prod, mem_univ,
          mem_Iic, true_and, and_true]
        exact le_rfl
    · have hI : e.toOpenPartialHomeomorph.IsImage (closure (Schoenflies.inside J₀))
          {p : Fin 2 × (ℝ × ℝ) | p.2.1 ≤ 0 ∨ p.2.2 ≤ 0} := by
        intro x hx
        have he := hraw (e x) (e.map_source hx)
        have hei : e.symm (e x) = x := e.left_inv hx
        rw [hei] at he
        exact he.symm
      have hfrI := hI.frontier
      rw [hfr] at hfrI
      rintro _ ⟨⟨i, z⟩, ⟨_, hz⟩, rfl⟩
      obtain rfl := mem_singleton_iff.mp hz
      have ht : (i, (0 : ℝ × ℝ)) ∈ e.target := htarget.symm ▸ ⟨mem_univ _, hzrect⟩
      apply (hfrI (e.map_target ht)).mp
      change e (e.symm (i, 0)) ∈ frontier {p : Fin 2 × (ℝ × ℝ) | p.2.1 ≤ 0 ∨ p.2.2 ≤ 0}
      have hei : e (e.symm (i, 0)) = (i, 0) := e.right_inv ht
      rw [hei, frontier_eq_closure_inter_closure]
      constructor
      · exact subset_closure (Or.inl le_rfl)
      · have he : {p : Fin 2 × (ℝ × ℝ) | p.2.1 ≤ 0 ∨ p.2.2 ≤ 0}ᶜ =
            univ ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
          ext p
          simp
        rw [he, closure_prod_eq]
        refine ⟨subset_closure (mem_univ _), ?_⟩
        change (0 : ℝ × ℝ) ∈ closure (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
        rw [closure_prod_eq]
        constructor
        · change (0 : ℝ) ∈ closure (Ioi (0 : ℝ))
          rw [closure_Ioi (a := (0 : ℝ))]
          exact (show (0 : ℝ) ≤ 0 from le_rfl)
        · change (0 : ℝ) ∈ closure (Ioi (0 : ℝ))
          rw [closure_Ioi (a := (0 : ℝ))]
          exact (show (0 : ℝ) ≤ 0 from le_rfl)
  have hZW : R₀ '' (e.symm '' (univ ×ˢ {(0 : ℝ × ℝ)})) ⊆ W :=
    (image_mono hcornerJ).trans (hη₀range ▸ hηW)
  have hQraw : Q '' (R₀ '' J₀) = R₁ '' J₁ := by rwa [hη₀range, hη₁range] at hQcurve
  obtain ⟨F, _, hFcurve, hU, _, hFc⟩ := hunround Q W hW hZW (hQc.mono inter_subset_left) J₀ J₁ hQraw
  refine ⟨F, hFcurve, ?_, c.source ∩ R₀ ⁻¹' W, hU, ?_, inter_subset_left, hFc⟩
  · have hh := Schoenflies.image_closure_inside_homeomorph F.toHomeomorph J₀
    change F '' closure (Schoenflies.inside J₀) = closure (Schoenflies.inside (F '' J₀)) at hh
    rwa [hFcurve] at hh
  · intro x hx
    exact ⟨hsource hx, hηW (hη₀range.symm ▸ mem_image_of_mem R₀ hx)⟩


private theorem exists_band_corner_chart_subset
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {b r k : ℝ}
    (hb : b ^ 2 = 1) (hr : 0 < r) (hk : 0 < k)
    {U : Set Schoenflies.Plane} (hU : IsOpen U)
    (hpoints : ({B (-1, 0), B (1, 0)} : Set Schoenflies.Plane) ⊆ U) :
    ∃ s : ℝ, 0 < s ∧ s < r ∧ s < k ∧
      ∃ e : PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane) (𝓘(ℝ, PUnit.{1}).prod 𝓘(ℝ, ℝ × ℝ))
        Schoenflies.Plane (Fin 2 × (ℝ × ℝ)) ∞,
        e.source ⊆ U ∧ e.target = univ ×ˢ (Ioo (-s) s ×ˢ Ioo (-s) s) ∧
        (∀ z ∈ Ioo (-s) s ×ˢ Ioo (-s) s,
          e.symm (0, z) = B (-1 * (1 - z.1), b * z.2)) ∧
        (∀ z ∈ Ioo (-s) s ×ˢ Ioo (-s) s,
          e.symm (1, z) = B (1 - z.1, b * z.2)) := by
  have hpre : IsOpen (B ⁻¹' U) := hU.preimage B.continuous
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.isOpen_iff.mp hpre (-1, 0) (hpoints (by simp))
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.mp hpre (1, 0) (hpoints (by simp))
  let s := min (min (min r 1) k) (min ε₀ ε₁) / 2
  have hm : 0 < min (min (min r 1) k) (min ε₀ ε₁) :=
    lt_min (lt_min (lt_min hr zero_lt_one) hk) (lt_min hε₀ hε₁)
  have hs : 0 < s := half_pos hm
  have hslt : s < min (min (min r 1) k) (min ε₀ ε₁) := half_lt_self hm
  have hsr₁ : s < min r 1 := (hslt.trans_le (min_le_left _ _)).trans_le (min_le_left _ _)
  have hsr : s < r := hsr₁.trans_le (min_le_left _ _)
  have hs₁ : s < 1 := hsr₁.trans_le (min_le_right _ _)
  have hsk : s < k := (hslt.trans_le (min_le_left _ _)).trans_le (min_le_right _ _)
  have hsε₀ : s < ε₀ := (hslt.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hsε₁ : s < ε₁ := (hslt.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  obtain ⟨e, hes, het, hel, her, _⟩ := exists_band_corner_chart B hb hs hs₁ hs
  refine ⟨s, hs, hsr, hsk, e, ?_, het, hel, her⟩
  rw [hes]
  rintro _ ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
  have huabs : |u| < s := abs_lt.mpr hu
  rcases hx with hx | hx
  · apply hball₀
    change dist (x, u) (-1, 0) < ε₀
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    apply (max_lt ?_ huabs).trans hsε₀
    exact abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · apply hball₁
    change dist (x, u) (1, 0) < ε₁
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    apply (max_lt ?_ huabs).trans hsε₁
    exact abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩


theorem exists_diffeomorph_eqOn_neighborhood_of_band_corner_curve
    (B₀ : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (c : PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane)
      Schoenflies.Plane Schoenflies.Plane ∞)
    {b r k : ℝ} (hb : b ^ 2 = 1) (hr : 0 < r) (hk : 0 < k)
    {U J₀ J₁ : Set Schoenflies.Plane} (hU : IsOpen U)
    (hpoints : ({B₀ (-1, 0), B₀ (1, 0)} : Set Schoenflies.Plane) ⊆ U)
    (hUc : U ⊆ c.source)
    (hJ₀ : Schoenflies.IsJordanCurve J₀) (hJ₁ : Schoenflies.IsJordanCurve J₁)
    (hsource : J₀ ⊆ c.source)
    (hc : c.toOpenPartialHomeomorph.IsImage
      (closure (Schoenflies.inside J₀)) (closure (Schoenflies.inside J₁)))
    (hreg₀ : ∀ p ∈ J₀, p ∉ ({B₀ (-1, 0), B₀ (1, 0)} : Set Schoenflies.Plane) →
      ∃ V : Set Schoenflies.Plane, ∃ g : Schoenflies.Plane → ℝ,
        IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ ∞ g V ∧
        (∀ x ∈ V, x ∈ J₀ ↔ g x = 0) ∧ fderiv ℝ g p ≠ 0)
    (hprofile :
      (∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ Ioo (a - r) (a + r) ×ˢ Ioo (-k) k,
        B₀ z ∈ closure (Schoenflies.inside J₀) ↔ a * z.1 ≤ 1 ∧ 0 ≤ b * z.2) ∨
      (∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ Ioo (a - r) (a + r) ×ˢ Ioo (-k) k,
        B₀ z ∈ closure (Schoenflies.inside J₀) ↔ 1 ≤ a * z.1 ∨ b * z.2 ≤ 0)) :
    ∃ F : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane,
      F '' J₀ = J₁ ∧ F '' closure (Schoenflies.inside J₀) = closure (Schoenflies.inside J₁) ∧
      ∃ V : Set Schoenflies.Plane, IsOpen V ∧ J₀ ⊆ V ∧ V ⊆ c.source ∧ EqOn F c V := by
  obtain ⟨s, hs, hsr, hsk, e, heU, het, hel, her⟩ :=
    exists_band_corner_chart_subset B₀ hb hr hk hU hpoints
  have hby {y : ℝ} (hy : y ∈ Ioo (-s) s) : b * y ∈ Ioo (-k) k := by
    rcases sq_eq_one_iff.mp hb with rfl | rfl
    · simp only [one_mul]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · simp only [neg_one_mul]
      exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hbmul (y : ℝ) : b * (b * y) = y := by
    calc
      b * (b * y) = b ^ 2 * y := by ring
      _ = y := by rw [hb, one_mul]
  have hzleft (z : ℝ × ℝ) (hz : z ∈ Ioo (-s) s ×ˢ Ioo (-s) s) :
      (-1 * (1 - z.1), b * z.2) ∈ Ioo (-1 - r) (-1 + r) ×ˢ Ioo (-k) k :=
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hby hz.2⟩
  have hzright (z : ℝ × ℝ) (hz : z ∈ Ioo (-s) s ×ˢ Ioo (-s) s) :
      (1 - z.1, b * z.2) ∈ Ioo (1 - r) (1 + r) ×ˢ Ioo (-k) k :=
    ⟨⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩, hby hz.2⟩
  have hz : (0 : ℝ × ℝ) ∈ Ioo (-s) s ×ˢ Ioo (-s) s :=
    ⟨⟨neg_neg_of_pos hs, hs⟩, neg_neg_of_pos hs, hs⟩
  have hpointsE : ({B₀ (-1, 0), B₀ (1, 0)} : Set Schoenflies.Plane) ⊆ e.source := by
    refine Set.pair_subset_iff.mpr ⟨?_, ?_⟩
    · have ht : (0, (0 : ℝ × ℝ)) ∈ e.target := by rw [het]; exact ⟨mem_univ _, hz⟩
      have he := e.map_target ht
      change e.symm (0, 0) ∈ e.source at he
      rw [hel 0 hz] at he
      simpa only [Prod.fst_zero, Prod.snd_zero, sub_zero, mul_one, mul_zero] using he
    · have ht : (1, (0 : ℝ × ℝ)) ∈ e.target := by rw [het]; exact ⟨mem_univ _, hz⟩
      have he := e.map_target ht
      change e.symm (1, 0) ∈ e.source at he
      rw [her 0 hz] at he
      simpa only [Prod.fst_zero, Prod.snd_zero, sub_zero, mul_zero] using he
  apply exists_diffeomorph_eqOn_neighborhood_of_corner_curve c e hs hs
    het (heU.trans hUc) hJ₀ hJ₁ hsource hc
    (fun p hp hps => hreg₀ p hp (fun h => hps (hpointsE h)))
  rcases hprofile with hprofile | hprofile
  · left
    rintro ⟨i, z⟩ hp
    have hz : z ∈ Ioo (-s) s ×ˢ Ioo (-s) s := (het ▸ hp).2
    fin_cases i
    · change e.symm (0, z) ∈ closure (Schoenflies.inside J₀) ↔ _
      rw [hel z hz, hprofile (-1) (by simp) _ (hzleft z hz)]
      simp only [neg_one_mul, neg_neg, hbmul]
      constructor <;> rintro ⟨hx, hy⟩ <;> exact ⟨by linarith, hy⟩
    · change e.symm (1, z) ∈ closure (Schoenflies.inside J₀) ↔ _
      rw [her z hz, hprofile 1 (by simp) _ (hzright z hz)]
      simp only [one_mul, hbmul]
      constructor <;> rintro ⟨hx, hy⟩ <;> exact ⟨by linarith, hy⟩
  · right
    rintro ⟨i, z⟩ hp
    have hz : z ∈ Ioo (-s) s ×ˢ Ioo (-s) s := (het ▸ hp).2
    fin_cases i
    · change e.symm (0, z) ∈ closure (Schoenflies.inside J₀) ↔ _
      rw [hel z hz, hprofile (-1) (by simp) _ (hzleft z hz)]
      simp only [neg_one_mul, neg_neg, hbmul]
      constructor <;> intro h <;> rcases h with hx | hy
      · exact Or.inl (by linarith)
      · exact Or.inr hy
      · exact Or.inl (by linarith)
      · exact Or.inr hy
    · change e.symm (1, z) ∈ closure (Schoenflies.inside J₀) ↔ _
      rw [her z hz, hprofile 1 (by simp) _ (hzright z hz)]
      simp only [one_mul, hbmul]
      constructor <;> intro h <;> rcases h with hx | hy
      · exact Or.inl (by linarith)
      · exact Or.inr hy
      · exact Or.inl (by linarith)
      · exact Or.inr hy


end

end DifferentialGeometry.Topology.PlanarJordan
