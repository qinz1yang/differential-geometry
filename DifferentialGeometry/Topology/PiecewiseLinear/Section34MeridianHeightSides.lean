import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianBigonLift
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurveHeightSides

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem eventually_sub_eq_of_circle_lifts {X : Type*} [TopologicalSpace X]
    {Q : Set X} {g h : X → ℝ} (hg : ContinuousOn g Q) (hh : ContinuousOn h Q)
    (hcoe : ∀ y ∈ Q, (g y : loopCircle) = (h y : loopCircle)) {x : X} (hx : x ∈ Q) :
    ∀ᶠ y in 𝓝[Q] x, g y - g x = h y - h x := by
  have hcov : IsCoveringMap (fun t : ℝ => (t : loopCircle)) :=
    AddCircle.isCoveringMap_coe (1 : ℝ)
  obtain ⟨U, hU, hxU, hinj⟩ := hcov.isLocalHomeomorph.isLocallyInjective (g x)
  have ht : ContinuousWithinAt (fun y => h y + g x - h x) Q x :=
    ((hh x hx).add continuousWithinAt_const).sub continuousWithinAt_const
  have htU : ∀ᶠ y in 𝓝[Q] x, h y + g x - h x ∈ U := by
    apply ht.preimage_mem_nhdsWithin
    exact hU.mem_nhds (by simpa only [add_sub_cancel_left] using hxU)
  filter_upwards [(hg x hx).preimage_mem_nhdsWithin (hU.mem_nhds hxU), htU,
    self_mem_nhdsWithin] with y hyU hyU' hyQ
  have hycoe : (g y : loopCircle) = ((h y + g x - h x : ℝ) : loopCircle) := by
    rw [AddCircle.coe_sub, AddCircle.coe_add, hcoe y hyQ, hcoe x hx,
      add_sub_cancel_right]
  have hy := hinj hyU hyU' hycoe
  linarith

theorem mem_closure_height_sides_of_circle_lifts {X : Type*} [TopologicalSpace X]
    {Q : Set X} {g h : X → ℝ} (hg : ContinuousOn g Q) (hh : ContinuousOn h Q)
    (hcoe : ∀ y ∈ Q, (g y : loopCircle) = (h y : loopCircle)) {x : X} (hx : x ∈ Q)
    (hbelow : x ∈ closure (Q ∩ {y | h y < h x}))
    (habove : x ∈ closure (Q ∩ {y | h x < h y})) :
    x ∈ closure (Q ∩ {y | g y < g x}) ∧
      x ∈ closure (Q ∩ {y | g x < g y}) := by
  have heq := eventually_nhdsWithin_iff.mp (eventually_sub_eq_of_circle_lifts hg hh hcoe hx)
  constructor
  · apply mem_closure_iff_frequently.mpr
    apply ((mem_closure_iff_frequently.mp hbelow).and_eventually heq).mono
    rintro y ⟨⟨hyQ, hyh⟩, hyeq⟩
    change h y < h x at hyh
    exact ⟨hyQ, by change g y < g x; have := hyeq hyQ; linarith⟩
  · apply mem_closure_iff_frequently.mpr
    apply ((mem_closure_iff_frequently.mp habove).and_eventually heq).mono
    rintro y ⟨⟨hyQ, hyh⟩, hyeq⟩
    change h x < h y at hyh
    exact ⟨hyQ, by change g x < g y; have := hyeq hyQ; linarith⟩

theorem IsCylindricalDiagram.exists_lift_height_sides_of_regular_slice
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {P : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S) (e : S ≃ₜ (P × loopCircle))
    (he : ∀ (x : P) (t : Icc (0 : ℝ) 1), (e.symm (x, (t : ℝ)) : F) = f (x, t))
    {g : F → ℝ} (hg : ContinuousOn g J) {r : ℝ}
    (hlift : ∀ y ∈ J, ∀ hy : y ∈ S, (g y : loopCircle) = (e ⟨y, hy⟩).2 - r)
    (K : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite K.faces]
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hK : K.space = (P ×ˢ Icc a b) ∩ f ⁻¹' J)
    (hr : r ∉ Prod.snd '' K.vertices) {x : E × ℝ}
    (hx : x ∈ K.space ∩ {y | y.2 = r}) :
    (∃ y ∈ J, g y < g (f x)) ∧ ∃ y ∈ J, g (f x) < g y := by
  have hKP : K.space ⊆ P ×ˢ Icc (0 : ℝ) 1 := by
    rw [hK]
    exact fun _ hy => ⟨hy.1.1, ha.trans hy.1.2.1, hy.1.2.2.trans hb⟩
  have hKJ : MapsTo f K.space J := fun y hy => (hK ▸ hy).2
  have hgf : ContinuousOn (g ∘ f) K.space :=
    hg.comp (hf.isPiecewiseAffineOn.continuousOn.mono hKP) hKJ
  have hcoe (y : E × ℝ) (hy : y ∈ K.space) :
      ((g ∘ f) y : loopCircle) = ((y.2 - r : ℝ) : loopCircle) := by
    have hyP := hKP hy
    have hys : f y ∈ S := hf.image_eq ▸ ⟨y, hyP, rfl⟩
    have hye : e.symm (⟨y.1, hyP.1⟩, (y.2 : loopCircle)) = (⟨f y, hys⟩ : S) := by
      apply Subtype.ext
      exact he ⟨y.1, hyP.1⟩ ⟨y.2, hyP.2⟩
    change (g (f y) : loopCircle) = _
    rw [hlift (f y) (hKJ hy) hys, ← hye, e.apply_symm_apply, AddCircle.coe_sub]
  obtain ⟨hlo, hhi⟩ := mem_closure_height_sides_of_notMem_vertex_image K hcard
    (LinearMap.snd ℝ E ℝ) hr hx
  have hxr : x.2 = r := hx.2
  have hEqlo : K.space ∩ {y | y.2 - r < x.2 - r} = K.space ∩ {y | y.2 < r} := by
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, hxr, sub_self, sub_lt_zero]
  have hEqhi : K.space ∩ {y | x.2 - r < y.2 - r} = K.space ∩ {y | r < y.2} := by
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, hxr, sub_self, sub_pos]
  obtain ⟨hlo', hhi'⟩ := mem_closure_height_sides_of_circle_lifts hgf
    (continuous_snd.sub continuous_const).continuousOn hcoe hx.1
    (hEqlo.symm ▸ hlo) (hEqhi.symm ▸ hhi)
  obtain ⟨y, hyK, hy⟩ := closure_nonempty_iff.mp ⟨x, hlo'⟩
  obtain ⟨z, hzK, hz⟩ := closure_nonempty_iff.mp ⟨x, hhi'⟩
  exact ⟨⟨f y, hKJ hyK, hy⟩, f z, hKJ hzK, hz⟩

end DifferentialGeometry.Topology.PiecewiseLinear
