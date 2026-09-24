import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianHeightSides

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_lift_height_sides_of_slice_germs
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {P : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S) (e : S ≃ₜ (P × loopCircle))
    (he : ∀ (x : P) (t : Icc (0 : ℝ) 1), (e.symm (x, (t : ℝ)) : F) = f (x, t))
    {g : F → ℝ} (hg : ContinuousOn g J) {r : ℝ}
    (hlift : ∀ y ∈ J, ∀ hy : y ∈ S, (g y : loopCircle) = (e ⟨y, hy⟩).2 - r)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) {x : E × ℝ}
    (hx : x ∈ ((P ×ˢ Icc a b) ∩ f ⁻¹' J) ∩ {y | y.2 = r})
    (hbelow : x ∈ closure (((P ×ˢ Icc a b) ∩ f ⁻¹' J) ∩ {y | y.2 < r}))
    (habove : x ∈ closure (((P ×ˢ Icc a b) ∩ f ⁻¹' J) ∩ {y | r < y.2})) :
    (∃ y ∈ J, g y < g (f x)) ∧ ∃ y ∈ J, g (f x) < g y := by
  let Q := (P ×ˢ Icc a b) ∩ f ⁻¹' J
  have hQP : Q ⊆ P ×ˢ Icc (0 : ℝ) 1 :=
    fun _ hy => ⟨hy.1.1, ha.trans hy.1.2.1, hy.1.2.2.trans hb⟩
  have hQJ : MapsTo f Q J := fun _ hy => hy.2
  have hgf : ContinuousOn (g ∘ f) Q :=
    hg.comp (hf.isPiecewiseAffineOn.continuousOn.mono hQP) hQJ
  have hcoe (y : E × ℝ) (hy : y ∈ Q) :
      ((g ∘ f) y : loopCircle) = ((y.2 - r : ℝ) : loopCircle) := by
    have hyP := hQP hy
    have hys : f y ∈ S := hf.image_eq ▸ ⟨y, hyP, rfl⟩
    have hye : e.symm (⟨y.1, hyP.1⟩, (y.2 : loopCircle)) = (⟨f y, hys⟩ : S) := by
      apply Subtype.ext
      exact he ⟨y.1, hyP.1⟩ ⟨y.2, hyP.2⟩
    change (g (f y) : loopCircle) = _
    rw [hlift (f y) (hQJ hy) hys, ← hye, e.apply_symm_apply, AddCircle.coe_sub]
  have hxr : x.2 = r := hx.2
  have hEqlo : Q ∩ {y | y.2 - r < x.2 - r} = Q ∩ {y | y.2 < r} := by
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, hxr, sub_self, sub_lt_zero]
  have hEqhi : Q ∩ {y | x.2 - r < y.2 - r} = Q ∩ {y | r < y.2} := by
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, hxr, sub_self, sub_pos]
  obtain ⟨hlo, hhi⟩ := mem_closure_height_sides_of_circle_lifts hgf
    (continuous_snd.sub continuous_const).continuousOn hcoe hx.1
    (hEqlo.symm ▸ hbelow) (hEqhi.symm ▸ habove)
  obtain ⟨y, hyQ, hy⟩ := closure_nonempty_iff.mp ⟨x, hlo⟩
  obtain ⟨z, hzQ, hz⟩ := closure_nonempty_iff.mp ⟨x, hhi⟩
  exact ⟨⟨f y, hQJ hyQ, hy⟩, f z, hQJ hzQ, hz⟩

end DifferentialGeometry.Topology.PiecewiseLinear
