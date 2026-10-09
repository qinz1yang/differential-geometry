import DifferentialGeometry.Topology.PiecewiseLinear.CylinderCut
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalProduct
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChartTransport

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace IsCylindricalDiagram

variable {f : E × ℝ → F} {P : Set E} {S : Set F}

theorem fst_eq_of_eq_of_equal_ends (hf : IsCylindricalDiagram f P S)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1))
    {x y : E × ℝ} (hx : x ∈ P ×ˢ Icc 0 1) (hy : y ∈ P ×ˢ Icc 0 1)
    (hxy : f x = f y) : x.1 = y.1 := by
  exact ((hf.eq_iff_fst_eq_and_circle_eq hends hx hy).mp hxy).1

theorem mem_image_base_iff_of_equal_ends (hf : IsCylindricalDiagram f P S)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1))
    {x : E × ℝ} (hx : x ∈ P ×ˢ Icc 0 1) {Q : Set E} (hQ : Q ⊆ P) :
    f x ∈ f '' (Q ×ˢ Icc 0 1) ↔ x.1 ∈ Q := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact hf.fst_eq_of_eq_of_equal_ends hends ⟨hQ hy.1, hy.2⟩ hx hyx ▸ hy.1
  · exact fun h => ⟨x, ⟨h, hx.2⟩, rfl⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

private theorem exists_seam_strip (hf : IsCylindricalDiagram f P S)
    (hP : IsPolyhedron P) (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) :
    ∃ g : E × ℝ → F,
      IsPLHomeomorphOn g (P ×ˢ Icc (-1 / 4) (1 / 4))
        (g '' (P ×ˢ Icc (-1 / 4) (1 / 4))) ∧
      (∀ x ∈ P, g (x, 0) = f (x, 0)) ∧
      ∀ z ∈ P ×ˢ Icc (-1 / 4) (1 / 4),
        ∃ t ∈ Icc (0 : ℝ) 1, g z = f (z.1, t) := by
  classical
  let L := P ×ˢ Icc (-1 / 4 : ℝ) 0
  let R := P ×ˢ Icc (0 : ℝ) (1 / 4)
  let C := P ×ˢ Icc (-1 / 4 : ℝ) (1 / 4)
  let τ : E × ℝ → E × ℝ := fun z => (z.1, z.2 + 1)
  let g : E × ℝ → F := fun z => if 0 ≤ z.2 then f z else f (τ z)
  have hL : IsPolyhedron L := hP.prod isHPolytope_Icc.isPolyhedron
  have hR : IsPolyhedron R := hP.prod isHPolytope_Icc.isPolyhedron
  have hC : IsPolyhedron C := hP.prod isHPolytope_Icc.isPolyhedron
  have hτ : IsPiecewiseAffineOn τ univ := by
    exact (isPiecewiseAffineOn_of_affine
      (AffineMap.id ℝ (E × ℝ) + AffineMap.const ℝ (E × ℝ) (0, 1))
      isOpen_univ).congr fun z _ => by ext <;> simp [τ]
  have hτL : MapsTo τ L (P ×ˢ Icc 0 1) := by
    rintro z ⟨hzP, hz⟩
    exact ⟨hzP, by dsimp [τ]; constructor <;> linarith [hz.1, hz.2]⟩
  have hgL : EqOn g (f ∘ τ) L := by
    rintro z ⟨hzP, hz⟩
    by_cases h : 0 ≤ z.2
    · have hz0 : z.2 = 0 := le_antisymm hz.2 h
      have hz0' : z = (z.1, 0) := Prod.ext rfl hz0
      simp only [g, ite_eq_left h, Function.comp_apply, τ, hz0, zero_add]
      exact (congrArg f hz0').trans (hends z.1 hzP)
    · simp [g, h]
  have hgR : EqOn g f R := fun z hz => by simp [g, hz.2.1]
  have hcover : L ∪ R = C := by
    ext z
    simp only [L, R, C, mem_union, mem_prod, mem_Icc]
    constructor
    · rintro (⟨hz, h0, h1⟩ | ⟨hz, h0, h1⟩) <;> exact ⟨hz, by linarith, by linarith⟩
    · rintro ⟨hz, h0, h1⟩
      rcases le_total z.2 0 with h | h
      · exact Or.inl ⟨hz, h0, h⟩
      · exact Or.inr ⟨hz, h, h1⟩
  have hgpl : IsPiecewiseAffineOn g C := by
    rw [← hcover]
    apply IsPiecewiseAffineOn.union_of_isClosed _ _ hL.isClosed hR.isClosed
    · exact ((hf.isPiecewiseAffineOn.comp hτ).mono_of_isPolyhedron hL
        (fun z hz => ⟨mem_univ _, hτL hz⟩)).congr hgL
    · exact (hf.isPiecewiseAffineOn.mono_of_isPolyhedron hR
        (fun z hz => ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩)).congr hgR
  have hrep (z : E × ℝ) (hz : z ∈ C) :
      ∃ t ∈ Icc (0 : ℝ) 1, g z = f (z.1, t) := by
    by_cases h : 0 ≤ z.2
    · exact ⟨z.2, ⟨h, by linarith [hz.2.2]⟩, by simp [g, h]⟩
    · exact ⟨z.2 + 1, ⟨by linarith [hz.2.1], by linarith⟩, by simp [g, h, τ]⟩
  have hinj : InjOn g C := by
    intro x hx y hy hxy
    by_cases hx0 : 0 ≤ x.2 <;> by_cases hy0 : 0 ≤ y.2
    · simp only [g, ite_eq_left hx0, ite_eq_left hy0] at hxy
      exact hf.injOn_strip (a := 0) (b := 1 / 4) le_rfl (by norm_num)
        (Or.inr (by norm_num)) ⟨hx.1, hx0, hx.2.2⟩ ⟨hy.1, hy0, hy.2.2⟩ hxy
    · simp only [g, ite_eq_left hx0, ite_eq_right hy0] at hxy
      rcases hf.eq_or_endpoints x ⟨hx.1, hx0, by linarith [hx.2.2]⟩
        (τ y) ⟨hy.1, by dsimp [τ]; constructor <;> linarith [hy.2.1]⟩ hxy with
        heq | heq | heq
      · have ht := congrArg Prod.snd heq
        dsimp [τ] at ht
        linarith [hx.2.2, hy.2.1]
      · dsimp [τ] at heq
        linarith [heq.2]
      · linarith [heq.1, hx.2.2]
    · simp only [g, ite_eq_right hx0, ite_eq_left hy0] at hxy
      rcases hf.eq_or_endpoints (τ x)
        ⟨hx.1, by dsimp [τ]; constructor <;> linarith [hx.2.1]⟩
        y ⟨hy.1, hy0, by linarith [hy.2.2]⟩ hxy with heq | heq | heq
      · have ht := congrArg Prod.snd heq
        dsimp [τ] at ht
        linarith [hy.2.2, hx.2.1]
      · dsimp [τ] at heq
        linarith [heq.1, hx.2.1]
      · dsimp [τ] at heq
        linarith [heq.1]
    · simp only [g, ite_eq_right hx0, ite_eq_right hy0] at hxy
      have heq := hf.injOn_strip (a := 3 / 4) (b := 1) (by norm_num) le_rfl
        (Or.inl (by norm_num)) (x₁ := τ x) (x₂ := τ y)
        ⟨hx.1, by dsimp [τ]; constructor <;> linarith [hx.2.1]⟩
        ⟨hy.1, by dsimp [τ]; constructor <;> linarith [hy.2.1]⟩ hxy
      have hfst := congrArg (fun q : E × ℝ => q.1) heq
      change x.1 = y.1 at hfst
      apply Prod.ext hfst
      have ht := congrArg Prod.snd heq
      dsimp [τ] at ht
      linarith
  exact ⟨g, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hC hgpl hinj.bijOn_image,
    fun x _ => by simp [g], hrep⟩

private theorem isPLHomeomorphOn_open_strip {g : E × ℝ → F} {a b : ℝ}
    (hg : IsPLHomeomorphOn g (P ×ˢ Icc a b) (g '' (P ×ˢ Icc a b)))
    (hdim : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ F) :
    IsOpen (g '' (interior P ×ˢ Ioo a b)) ∧
      IsPLHomeomorphOn g (interior P ×ˢ Ioo a b) (g '' (interior P ×ˢ Ioo a b)) := by
  have hU : IsOpen (interior P ×ˢ Ioo a b) := isOpen_interior.prod isOpen_Ioo
  have hsub : interior P ×ˢ Ioo a b ⊆ P ×ˢ Icc a b :=
    prod_mono interior_subset Ioo_subset_Icc_self
  have himg := invariance_of_domain_isOpen_image_of_finrank_eq hdim hU
    (hg.isPiecewiseAffineOn.continuousOn.mono hsub) (hg.bijOn.injOn.mono hsub)
  exact ⟨himg, hg.restrict_isOpen hU hsub himg⟩

theorem exists_open_pl_chart_of_equal_ends (hf : IsCylindricalDiagram f P S)
    (hP : IsPolyhedron P) (hends : ∀ x ∈ P, f (x, 0) = f (x, 1))
    (hdim : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ F)
    {x : E} (hx : x ∈ interior P) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ (s : ℝ) (U : Set (E × ℝ)) (g : E × ℝ → F),
      IsOpen U ∧ (x, s) ∈ U ∧ U ⊆ interior P ×ˢ univ ∧ IsOpen (g '' U) ∧
      IsPLHomeomorphOn g U (g '' U) ∧ g (x, s) = f (x, t) ∧
      ∀ z ∈ U, ∀ Q ⊆ P, g z ∈ f '' (Q ×ˢ Icc 0 1) ↔ z.1 ∈ Q := by
  by_cases hti : t ∈ Ioo (0 : ℝ) 1
  · let a : ℝ := t / 2
    let b : ℝ := (t + 1) / 2
    have ha : 0 ≤ a := by dsimp [a]; linarith [hti.1]
    have hb : b ≤ 1 := by dsimp [b]; linarith [hti.2]
    have hab : 0 < a ∨ b < 1 := Or.inl (by dsimp [a]; linarith [hti.1])
    have hg := hf.isPLHomeomorphOn_strip hP ha hb hab
    obtain ⟨hV, hgU⟩ := isPLHomeomorphOn_open_strip hg hdim
    refine ⟨t, interior P ×ˢ Ioo a b, f, isOpen_interior.prod isOpen_Ioo,
      ⟨hx, by dsimp [a, b]; constructor <;> linarith [hti.1, hti.2]⟩,
      prod_mono Subset.rfl (subset_univ _), hV, hgU, rfl, ?_⟩
    intro z hz Q hQ
    exact hf.mem_image_base_iff_of_equal_ends hends
      ⟨interior_subset hz.1, ha.trans hz.2.1.le, hz.2.2.le.trans hb⟩ hQ
  · have htend : t = 0 ∨ t = 1 := by
      simp only [mem_Ioo, not_and_or, not_lt] at hti
      rcases hti with h | h
      · exact Or.inl (le_antisymm h ht.1)
      · exact Or.inr (le_antisymm ht.2 h)
    obtain ⟨g, hg, hg0, hrep⟩ := hf.exists_seam_strip hP hends
    obtain ⟨hV, hgU⟩ := isPLHomeomorphOn_open_strip hg hdim
    refine ⟨0, interior P ×ˢ Ioo (-1 / 4) (1 / 4), g,
      isOpen_interior.prod isOpen_Ioo, ⟨hx, by norm_num⟩,
      prod_mono Subset.rfl (subset_univ _), hV, hgU, ?_, ?_⟩
    · rcases htend with rfl | rfl
      · exact hg0 x (interior_subset hx)
      · exact (hg0 x (interior_subset hx)).trans (hends x (interior_subset hx))
    · intro z hz Q hQ
      obtain ⟨r, hr, hgr⟩ := hrep z ⟨interior_subset hz.1, hz.2.1.le, hz.2.2.le⟩
      rw [hgr]
      exact hf.mem_image_base_iff_of_equal_ends hends
        (x := (z.1, r)) ⟨interior_subset hz.1, hr⟩ hQ

end IsCylindricalDiagram

end DifferentialGeometry.Topology.PiecewiseLinear
