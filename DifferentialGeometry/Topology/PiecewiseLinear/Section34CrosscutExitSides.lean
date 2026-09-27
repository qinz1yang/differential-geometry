import DifferentialGeometry.Topology.PlanarJordan.LocalSides
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph

open Set Topology

namespace DifferentialGeometry.Topology

theorem ContinuousOn.same_side_endpoints_of_two_crossing_germs
    {X : Type*} [TopologicalSpace X] {γ : ℝ → X} {l a b r : ℝ} {U V : Set X}
    (hγ : ContinuousOn γ (Icc l r)) (hla : l < a) (hab : a < b) (hbr : b < r)
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : ∀ t ∈ Ioo l r, t ≠ a → t ≠ b → γ t ∈ U ∪ V)
    (ha : γ a ∉ U ∪ V) (hb : γ b ∉ U ∪ V)
    (haU : a ∈ closure (Icc l r ∩ γ ⁻¹' U))
    (haV : a ∈ closure (Icc l r ∩ γ ⁻¹' V))
    (hbU : b ∈ closure (Icc l r ∩ γ ⁻¹' U))
    (hbV : b ∈ closure (Icc l r ∩ γ ⁻¹' V)) :
    (γ l ∈ closure U ∧ γ r ∈ closure U ∧
      γ '' Ioo l a ⊆ U ∧ γ '' Ioo b r ⊆ U) ∨
      (γ l ∈ closure V ∧ γ r ∈ closure V ∧
        γ '' Ioo l a ⊆ V ∧ γ '' Ioo b r ⊆ V) := by
  have h₀sub : Ioo l a ⊆ Icc l r := fun _ ht => ⟨ht.1.le, by linarith [ht.2]⟩
  have h₁sub : Ioo a b ⊆ Icc l r := fun _ ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h₂sub : Ioo b r ⊆ Icc l r := fun _ ht => ⟨by linarith [ht.1], ht.2.le⟩
  have h₀ : γ '' Ioo l a ⊆ U ∨ γ '' Ioo l a ⊆ V := by
    apply (isPreconnected_Ioo.image γ (hγ.mono h₀sub)).subset_or_subset hU hV hdis
    rintro _ ⟨t, ht, rfl⟩
    exact hcover t ⟨ht.1, by linarith [ht.2]⟩ ht.2.ne (by linarith [ht.2])
  have h₁ : γ '' Ioo a b ⊆ U ∨ γ '' Ioo a b ⊆ V := by
    apply (isPreconnected_Ioo.image γ (hγ.mono h₁sub)).subset_or_subset hU hV hdis
    rintro _ ⟨t, ht, rfl⟩
    exact hcover t ⟨by linarith [ht.1], by linarith [ht.2]⟩ ht.1.ne' ht.2.ne
  have h₂ : γ '' Ioo b r ⊆ U ∨ γ '' Ioo b r ⊆ V := by
    apply (isPreconnected_Ioo.image γ (hγ.mono h₂sub)).subset_or_subset hU hV hdis
    rintro _ ⟨t, ht, rfl⟩
    exact hcover t ⟨by linarith [ht.1], ht.2⟩ (by linarith [ht.1]) ht.1.ne'
  have hleft (Z W : Set X) (hZW : Disjoint Z W)
      (haW : a ∈ closure (Icc l r ∩ γ ⁻¹' W)) (haNW : γ a ∉ W)
      (h₀Z : γ '' Ioo l a ⊆ Z) (h₁Z : γ '' Ioo a b ⊆ Z) : False := by
    obtain ⟨t, ht, htW⟩ := mem_closure_iff_nhds.mp haW (Ioo l b)
      (isOpen_Ioo.mem_nhds ⟨hla, hab⟩)
    rcases lt_trichotomy t a with hta | rfl | hat
    · exact disjoint_left.mp hZW (h₀Z ⟨t, ⟨ht.1, hta⟩, rfl⟩) htW.2
    · exact haNW htW.2
    · exact disjoint_left.mp hZW (h₁Z ⟨t, ⟨hat, ht.2⟩, rfl⟩) htW.2
  have hright (Z W : Set X) (hZW : Disjoint Z W)
      (hbW : b ∈ closure (Icc l r ∩ γ ⁻¹' W)) (hbNW : γ b ∉ W)
      (h₁Z : γ '' Ioo a b ⊆ Z) (h₂Z : γ '' Ioo b r ⊆ Z) : False := by
    obtain ⟨t, ht, htW⟩ := mem_closure_iff_nhds.mp hbW (Ioo a r)
      (isOpen_Ioo.mem_nhds ⟨hab, hbr⟩)
    rcases lt_trichotomy t b with htb | rfl | hbt
    · exact disjoint_left.mp hZW (h₁Z ⟨t, ⟨ht.1, htb⟩, rfl⟩) htW.2
    · exact hbNW htW.2
    · exact disjoint_left.mp hZW (h₂Z ⟨t, ⟨hbt, ht.2⟩, rfl⟩) htW.2
  have hends (Z : Set X) (h₀Z : γ '' Ioo l a ⊆ Z) (h₂Z : γ '' Ioo b r ⊆ Z) :
      γ l ∈ closure Z ∧ γ r ∈ closure Z ∧
        γ '' Ioo l a ⊆ Z ∧ γ '' Ioo b r ⊆ Z := by
    refine ⟨?_, ?_, h₀Z, h₂Z⟩
    · apply closure_mono h₀Z
      apply ((hγ l ⟨le_rfl, by linarith⟩).mono h₀sub).mem_closure_image
      rw [closure_Ioo hla.ne]
      exact ⟨le_rfl, hla.le⟩
    · apply closure_mono h₂Z
      apply ((hγ r ⟨by linarith, le_rfl⟩).mono h₂sub).mem_closure_image
      rw [closure_Ioo hbr.ne]
      exact ⟨hbr.le, le_rfl⟩
  rcases h₁ with h₁U | h₁V
  · exact Or.inr (hends V
      (h₀.resolve_left fun h₀U => hleft U V hdis haV (fun h => ha (Or.inr h)) h₀U h₁U)
      (h₂.resolve_left fun h₂U => hright U V hdis hbV (fun h => hb (Or.inr h)) h₁U h₂U))
  · exact Or.inl (hends U
      (h₀.resolve_right fun h₀V => hleft V U hdis.symm haU
        (fun h => ha (Or.inl h)) h₀V h₁V)
      (h₂.resolve_right fun h₂V => hright V U hdis.symm hbU
        (fun h => hb (Or.inl h)) h₁V h₂V))

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.mem_closure_preimage_of_mem_closure_inter
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {A : Set E} {B U : Set F} (hf : IsPLHomeomorphOn f A B)
    {x : E} (hx : x ∈ A) (hfx : f x ∈ closure (B ∩ U)) :
    x ∈ closure (A ∩ f ⁻¹' U) := by
  let g := Function.invFunOn f A
  have hcont : ContinuousWithinAt g (B ∩ U) (f x) :=
    (hf.symm.isPiecewiseAffineOn.continuousOn _ (hf.bijOn.mapsTo hx)).mono inter_subset_left
  have h := hcont.mem_closure_image hfx
  have himage : g '' (B ∩ U) ⊆ A ∩ f ⁻¹' U := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hf.symm.bijOn.mapsTo hy.1, ?_⟩
    change f (g y) ∈ U
    rw [show f (g y) = y from hf.bijOn.invOn_invFunOn.2 hy.1]
    exact hy.2
  have hxg : g (f x) = x := hf.bijOn.invOn_invFunOn.1 hx
  exact hxg ▸ closure_mono himage h

end DifferentialGeometry.Topology.PiecewiseLinear

namespace DifferentialGeometry.Topology.PlanarJordan

theorem flowBox_axis_accumulates_both_regions
    {X : Type*} [TopologicalSpace X] {C J U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = Cᶜ) (hfrU : frontier U = C) (hfrV : frontier V = C)
    (e : OpenPartialHomeomorph (ℝ × ℝ) X) {ε : ℝ} (hε : 0 < ε)
    (hsource : Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source)
    (hcurve : ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε, e p ∈ C ↔ p.2 = 0)
    (haxis : ∀ t ∈ Ioo (-ε) ε, e (0, t) ∈ J) :
    e (0, 0) ∈ closure (J ∩ U) ∧ e (0, 0) ∈ closure (J ∩ V) := by
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have he : ContinuousAt e (0, 0) :=
    e.continuousOn.continuousAt (e.open_source.mem_nhds (hsource ⟨hzero, hzero⟩))
  have hcont : ContinuousAt (fun t : ℝ => e (0, t)) 0 :=
    he.comp (continuous_const.prodMk continuous_id).continuousAt
  have hpos (Z : Set X) (hZ : e '' (Ioo (-ε) ε ×ˢ Ioo 0 ε) ⊆ Z) :
      e (0, 0) ∈ closure (J ∩ Z) := by
    have him : (fun t : ℝ => e (0, t)) '' Ioo 0 ε ⊆ J ∩ Z := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨haxis t ⟨by linarith [ht.1], ht.2⟩, hZ ⟨(0, t), ⟨hzero, ht⟩, rfl⟩⟩
    apply closure_mono him
    apply hcont.continuousWithinAt.mem_closure_image
    rw [closure_Ioo hε.ne]
    exact ⟨le_rfl, hε.le⟩
  have hneg (Z : Set X) (hZ : e '' (Ioo (-ε) ε ×ˢ Ioo (-ε) 0) ⊆ Z) :
      e (0, 0) ∈ closure (J ∩ Z) := by
    have him : (fun t : ℝ => e (0, t)) '' Ioo (-ε) 0 ⊆ J ∩ Z := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨haxis t ⟨ht.1, by linarith [ht.2]⟩, hZ ⟨(0, t), ⟨hzero, ht⟩, rfl⟩⟩
    apply closure_mono him
    apply hcont.continuousWithinAt.mem_closure_image
    rw [closure_Ioo (neg_neg_of_pos hε).ne]
    exact ⟨le_of_lt (neg_neg_of_pos hε), le_rfl⟩
  rcases flowBox_halves_in_opposite_regions hU hV hUV hcover hfrU hfrV e
    (by linarith : -ε < ε) hε hsource hcurve with ⟨hP, hN⟩ | ⟨hP, hN⟩
  · exact ⟨hpos U hP, hneg V hN⟩
  · exact ⟨hneg U hN, hpos V hP⟩

end DifferentialGeometry.Topology.PlanarJordan

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.same_side_endpoints_of_two_crossing_charts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {γ : ℝ → E} {J C U V : Set E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) J)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = Cᶜ) (hfrU : frontier U = C) (hfrV : frontier V = C)
    (t : Fin 2 → ℝ) (h₀ : 0 < t 0) (h₀₁ : t 0 < t 1) (h₁ : t 1 < 1)
    (htrace : ∀ s ∈ Ioo (0 : ℝ) 1, γ s ∈ C → s = t 0 ∨ s = t 1)
    (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) E) (ε : Fin 2 → ℝ)
    (hε : ∀ i, 0 < ε i)
    (hsource : ∀ i, Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i) ⊆ (e i).source)
    (hcenter : ∀ i, e i (0, 0) = γ (t i))
    (hcurve : ∀ i, ∀ p ∈ Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i),
      e i p ∈ C ↔ p.2 = 0)
    (haxis : ∀ i, ∀ s ∈ Ioo (-ε i) (ε i), e i (0, s) ∈ J) :
    (γ 0 ∈ closure U ∧ γ 1 ∈ closure U ∧
      γ '' Ioo 0 (t 0) ⊆ U ∧ γ '' Ioo (t 1) 1 ⊆ U) ∨
      (γ 0 ∈ closure V ∧ γ 1 ∈ closure V ∧
        γ '' Ioo 0 (t 0) ⊆ V ∧ γ '' Ioo (t 1) 1 ⊆ V) := by
  have ht : ∀ i, t i ∈ Icc (0 : ℝ) 1 := by
    intro i
    fin_cases i
    · exact ⟨h₀.le, (h₀₁.trans h₁).le⟩
    · exact ⟨(h₀.trans h₀₁).le, h₁.le⟩
  have hcross (i : Fin 2) :
      t i ∈ closure (Icc (0 : ℝ) 1 ∩ γ ⁻¹' U) ∧
        t i ∈ closure (Icc (0 : ℝ) 1 ∩ γ ⁻¹' V) := by
    have h := PlanarJordan.flowBox_axis_accumulates_both_regions hU hV hUV
      hcover hfrU hfrV (e i) (hε i) (hsource i) (hcurve i) (haxis i)
    rw [hcenter i] at h
    exact ⟨hγ.mem_closure_preimage_of_mem_closure_inter (ht i) h.1,
      hγ.mem_closure_preimage_of_mem_closure_inter (ht i) h.2⟩
  have hnot (i : Fin 2) : γ (t i) ∉ U ∪ V := by
    rw [hcover, notMem_compl_iff, ← hcenter i]
    apply (hcurve i (0, 0) ?_).mpr rfl
    exact ⟨⟨neg_neg_of_pos (hε i), hε i⟩, ⟨neg_neg_of_pos (hε i), hε i⟩⟩
  apply Topology.ContinuousOn.same_side_endpoints_of_two_crossing_germs
    hγ.isPiecewiseAffineOn.continuousOn h₀ h₀₁ h₁ hU hV hUV ?_ (hnot 0) (hnot 1)
      (hcross 0).1 (hcross 0).2 (hcross 1).1 (hcross 1).2
  intro s hs hs₀ hs₁
  rw [hcover]
  exact fun hsC => (htrace s hs hsC).elim hs₀ hs₁

end DifferentialGeometry.Topology.PiecewiseLinear
