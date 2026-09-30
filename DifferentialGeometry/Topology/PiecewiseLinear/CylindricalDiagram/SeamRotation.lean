import DifferentialGeometry.Topology.PiecewiseLinear.CylinderCut
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalProduct

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_seam_rotation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {P : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∃ g : E × ℝ → F, IsCylindricalDiagram g P S ∧
      (∀ x ∈ P, g (x, 0) = f (x, r) ∧ g (x, 1) = f (x, r)) ∧
      (∀ Q ⊆ P, g '' (Q ×ˢ Icc 0 1) = f '' (Q ×ˢ Icc 0 1)) ∧
      ∀ z, g z = if z.2 ≤ 1 - r then f (z.1, z.2 + r) else f (z.1, z.2 + r - 1) := by
  classical
  let g : E × ℝ → F := fun z =>
    if z.2 ≤ 1 - r then f (z.1, z.2 + r) else f (z.1, z.2 + r - 1)
  let τ (d : ℝ) : E × ℝ →ᵃ[ℝ] E × ℝ :=
    { toFun := fun z => (z.1, z.2 + d)
      linear := LinearMap.id
      map_vadd' := by intro x y; ext <;> simp [vadd_eq_add, add_assoc] }
  let Q₀ := P ×ˢ Icc (0 : ℝ) (1 - r)
  let Q₁ := P ×ˢ Icc (1 - r) (1 : ℝ)
  have hQ₀ : IsPolyhedron Q₀ := hP.prod isHPolytope_Icc.isPolyhedron
  have hQ₁ : IsPolyhedron Q₁ := hP.prod isHPolytope_Icc.isPolyhedron
  have hcover : Q₀ ∪ Q₁ = P ×ˢ Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact ⟨hz.1, hz.2.1, by have := hz.2.2; linarith [hr.1]⟩
      · exact ⟨hz.1, by have := hz.2.1; linarith [hr.2], hz.2.2⟩
    · intro hz
      rcases le_total z.2 (1 - r) with h | h
      · exact Or.inl ⟨hz.1, hz.2.1, h⟩
      · exact Or.inr ⟨hz.1, h, hz.2.2⟩
  have hfirst : EqOn g (f ∘ τ r) Q₀ := by
    intro z hz
    exact ite_eq_left hz.2.2
  have hsecond : EqOn g (f ∘ τ (r - 1)) Q₁ := by
    intro z hz
    by_cases hc : z.2 ≤ 1 - r
    · have heq : z.2 = 1 - r := le_antisymm hc hz.2.1
      change (if z.2 ≤ 1 - r then _ else _) = f (z.1, z.2 + (r - 1))
      rw [ite_eq_left hc, heq]
      convert (hends z.1 hz.1).symm using 1 <;> congr 1 <;> congr 1 <;> ring
    · change (if z.2 ≤ 1 - r then _ else _) = f (z.1, z.2 + (r - 1))
      rw [ite_eq_right hc]
      congr 1
      ext <;> simp [sub_eq_add_neg, add_assoc]
  have hpa₀ : IsPiecewiseAffineOn (f ∘ τ r) Q₀ := by
    apply (hf.isPiecewiseAffineOn.comp
      (isPiecewiseAffineOn_of_affine (τ r) isOpen_univ)).mono_of_isPolyhedron hQ₀
    intro z hz
    exact ⟨mem_univ _, hz.1, by change 0 ≤ z.2 + r; linarith [hz.2.1, hr.1],
      by change z.2 + r ≤ 1; linarith [hz.2.2]⟩
  have hpa₁ : IsPiecewiseAffineOn (f ∘ τ (r - 1)) Q₁ := by
    apply (hf.isPiecewiseAffineOn.comp
      (isPiecewiseAffineOn_of_affine (τ (r - 1)) isOpen_univ)).mono_of_isPolyhedron hQ₁
    intro z hz
    exact ⟨mem_univ _, hz.1, by change 0 ≤ z.2 + (r - 1); linarith [hz.2.1],
      by change z.2 + (r - 1) ≤ 1; linarith [hz.2.2, hr.2]⟩
  have himage (Q : Set E) (hQP : Q ⊆ P) :
      g '' (Q ×ˢ Icc 0 1) = f '' (Q ×ˢ Icc 0 1) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      by_cases hc : z.2 ≤ 1 - r
      · exact ⟨(z.1, z.2 + r), ⟨hz.1, by linarith [hz.2.1, hr.1],
          by linarith⟩, (ite_eq_left hc).symm⟩
      · exact ⟨(z.1, z.2 + r - 1), ⟨hz.1, by linarith,
          by linarith [hz.2.2, hr.2]⟩, (ite_eq_right hc).symm⟩
    · rintro ⟨z, hz, rfl⟩
      by_cases hc : r ≤ z.2
      · refine ⟨(z.1, z.2 - r), ⟨hz.1, by linarith, by linarith [hz.2.2, hr.1]⟩, ?_⟩
        have hcut : z.2 - r ≤ 1 - r := by linarith [hz.2.2]
        change (if z.2 - r ≤ 1 - r then _ else _) = f z
        rw [ite_eq_left hcut, sub_add_cancel]
      · refine ⟨(z.1, z.2 - r + 1),
          ⟨hz.1, by linarith [hz.2.1, hr.2], by linarith⟩, ?_⟩
        by_cases hz0 : z.2 = 0
        · have hcut : z.2 - r + 1 ≤ 1 - r := by linarith
          change (if z.2 - r + 1 ≤ 1 - r then _ else _) = f z
          rw [ite_eq_left hcut]
          have htime : z.2 - r + 1 + r = 1 := by linarith
          rw [htime]
          have hzP : z.1 ∈ P := hQP hz.1
          exact (hends z.1 hzP).symm.trans (by congr 1; exact Prod.ext rfl hz0.symm)
        · have hzpos : 0 < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm hz0)
          have hcut : ¬z.2 - r + 1 ≤ 1 - r := by linarith
          change (if z.2 - r + 1 ≤ 1 - r then _ else _) = f z
          rw [ite_eq_right hcut]
          congr 1
          ext
          · rfl
          · dsimp
            ring
  have hend (x : E) : g (x, 0) = f (x, r) ∧ g (x, 1) = f (x, r) := by
    have hcut0 : (0 : ℝ) ≤ 1 - r := by linarith [hr.2]
    have hcut1 : ¬(1 : ℝ) ≤ 1 - r := by linarith [hr.1]
    simp [g, hcut0, hcut1, show 1 + r - 1 = r by ring]
  refine ⟨g, ⟨?_, ?_, ?_, ?_⟩, fun x _ => hend x, himage, fun _ => rfl⟩
  · rw [← hcover]
    exact (hpa₀.congr hfirst).union_of_isClosed (hpa₁.congr hsecond)
      hQ₀.isClosed hQ₁.isClosed
  · exact (himage P subset_rfl).trans hf.image_eq
  · ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht' : t = 1 := ht
      subst t
      exact ⟨(x, 0), ⟨hx, rfl⟩, (hend x).1.trans (hend x).2.symm⟩
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht' : t = 0 := ht
      subst t
      exact ⟨(x, 1), ⟨hx, rfl⟩, (hend x).2.trans (hend x).1.symm⟩
  · intro x hx y hy hxy
    by_cases hxc : x.2 ≤ 1 - r <;> by_cases hyc : y.2 ≤ 1 - r
    · have hfx : g x = f (x.1, x.2 + r) := ite_eq_left hxc
      have hfy : g y = f (y.1, y.2 + r) := ite_eq_left hyc
      have heq := hf.injOn_strip hr.1.le le_rfl (Or.inl hr.1)
        (x₁ := (x.1, x.2 + r)) (x₂ := (y.1, y.2 + r))
        ⟨hx.1, by linarith [hx.2.1], by linarith⟩
        ⟨hy.1, by linarith [hy.2.1], by linarith⟩ (hfx.symm.trans (hxy.trans hfy))
      exact Or.inl (Prod.ext (by simpa only using congrArg Prod.fst heq)
        (by have := congrArg Prod.snd heq; dsimp at this; linarith))
    · have hfx : g x = f (x.1, x.2 + r) := ite_eq_left hxc
      have hfy : g y = f (y.1, y.2 + r - 1) := ite_eq_right hyc
      rcases hf.eq_or_endpoints (x.1, x.2 + r)
        ⟨hx.1, by linarith [hx.2.1, hr.1], by linarith⟩
        (y.1, y.2 + r - 1) ⟨hy.1, by linarith, by linarith [hy.2.2, hr.2]⟩
        (hfx.symm.trans (hxy.trans hfy)) with heq | heq | heq
      · have he := congrArg Prod.snd heq
        dsimp at he
        exact Or.inr (Or.inl ⟨by linarith [hx.2.1, hy.2.2],
          by linarith [hx.2.1, hy.2.2]⟩)
      · have he := heq.1
        dsimp at he
        linarith [hx.2.1, hr.1]
      · have he := heq.2
        dsimp at he
        linarith
    · have hfx : g x = f (x.1, x.2 + r - 1) := ite_eq_right hxc
      have hfy : g y = f (y.1, y.2 + r) := ite_eq_left hyc
      rcases hf.eq_or_endpoints (x.1, x.2 + r - 1)
        ⟨hx.1, by linarith, by linarith [hx.2.2, hr.2]⟩
        (y.1, y.2 + r) ⟨hy.1, by linarith [hy.2.1, hr.1], by linarith⟩
        (hfx.symm.trans (hxy.trans hfy)) with heq | heq | heq
      · have he := congrArg Prod.snd heq
        dsimp at he
        exact Or.inr (Or.inr ⟨by linarith [hx.2.2, hy.2.1],
          by linarith [hx.2.2, hy.2.1]⟩)
      · have he := heq.1
        dsimp at he
        linarith
      · have he := heq.2
        dsimp at he
        linarith [hy.2.1, hr.1]
    · have hfx : g x = f (x.1, x.2 + r - 1) := ite_eq_right hxc
      have hfy : g y = f (y.1, y.2 + r - 1) := ite_eq_right hyc
      have heq := hf.injOn_strip le_rfl hr.2.le (Or.inr hr.2)
        (x₁ := (x.1, x.2 + r - 1)) (x₂ := (y.1, y.2 + r - 1))
        ⟨hx.1, by linarith, by linarith [hx.2.2]⟩
        ⟨hy.1, by linarith, by linarith [hy.2.2]⟩ (hfx.symm.trans (hxy.trans hfy))
      exact Or.inl (Prod.ext (by simpa only using congrArg Prod.fst heq)
        (by have := congrArg Prod.snd heq; dsimp at this; linarith))

theorem IsCylindricalDiagram.exists_seam_rotation_with_coordinates
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {P : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (e : S ≃ₜ (P × loopCircle))
    (he : ∀ (x : P) (t : Icc (0 : ℝ) 1), (e.symm (x, (t : ℝ)) : F) = f (x, t)) :
    ∃ (g : E × ℝ → F) (e' : S ≃ₜ (P × loopCircle)), IsCylindricalDiagram g P S ∧
      (∀ x ∈ P, g (x, 0) = f (x, r) ∧ g (x, 1) = f (x, r)) ∧
      (∀ Q ⊆ P, g '' (Q ×ˢ Icc 0 1) = f '' (Q ×ˢ Icc 0 1)) ∧
      (∀ (x : P) (t : Icc (0 : ℝ) 1), (e'.symm (x, (t : ℝ)) : F) = g (x, t)) ∧
      ∀ y : S, e' y = ((e y).1, (e y).2 - r) := by
  obtain ⟨g, hg, hgend, hgimage, hgformula⟩ := hf.exists_seam_rotation hP hends hr
  let e' : S ≃ₜ (P × loopCircle) :=
    e.trans ((Homeomorph.refl P).prodCongr (Homeomorph.subRight (r : loopCircle)))
  refine ⟨g, e', hg, hgend, hgimage, ?_, fun _ => rfl⟩
  intro x t
  have he' : e'.symm (x, ((t : ℝ) : loopCircle)) =
      e.symm (x, ((t : ℝ) : loopCircle) + (r : loopCircle)) := rfl
  rw [he', hgformula]
  by_cases hc : (t : ℝ) ≤ 1 - r
  · rw [ite_eq_left hc, ← AddCircle.coe_add]
    exact he x ⟨t + r, by linarith [t.2.1, hr.1], by linarith⟩
  · rw [ite_eq_right hc]
    have hcoe : ((t : ℝ) : loopCircle) + (r : loopCircle) =
        (((t : ℝ) + r - 1 : ℝ) : loopCircle) := by
      rw [AddCircle.coe_sub, AddCircle.coe_add, AddCircle.coe_period, sub_zero]
    rw [hcoe]
    exact he x ⟨t + r - 1, by linarith, by linarith [t.2.2, hr.2]⟩

end DifferentialGeometry.Topology.PiecewiseLinear
