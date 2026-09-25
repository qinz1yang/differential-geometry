import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalCircleCut
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalFibers
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PolyhedralArc

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem isPLSphere_image_Icc_of_eq_or_endpoints
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {g : ℝ → F} (hg : IsPiecewiseAffineOn g (Icc 0 1)) (hends : g 0 = g 1)
    (hinj : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, g s = g t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    IsPLSphere 1 (g '' Icc 0 1) := by
  let f : ℝ × ℝ → F := fun z => g z.2
  have hprod : IsPolyhedron (({0} : Set ℝ) ×ˢ Icc (0 : ℝ) 1) :=
    (isHPolytope_singleton 0).isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  have hf : IsCylindricalDiagram f {0} (g '' Icc 0 1) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hs := (isPiecewiseAffineOn_of_affine
        (LinearMap.snd ℝ ℝ ℝ).toAffineMap isOpen_univ).mono_of_isPolyhedron hprod
        (subset_univ _)
      have h := hg.comp hs
      change IsPiecewiseAffineOn f (({0} : Set ℝ) ×ˢ Icc (0 : ℝ) 1 ∩
        Prod.snd ⁻¹' Icc 0 1) at h
      rw [inter_eq_left.mpr (show ({0} : Set ℝ) ×ˢ Icc (0 : ℝ) 1 ⊆
        Prod.snd ⁻¹' Icc 0 1 from fun _ hx => hx.2)] at h
      exact h
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, hx.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨(0, t), ⟨rfl, ht⟩, rfl⟩
    · have hslice (r : ℝ) : f '' (({0} : Set ℝ) ×ˢ {r}) = {g r} := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact congrArg g hx.2
        · rintro rfl
          exact ⟨(0, r), ⟨rfl, rfl⟩, rfl⟩
      rw [hslice, hslice, hends]
    · intro x hx y hy hxy
      rcases hinj x.2 hx.2 y.2 hy.2 hxy with h | h | h
      · exact Or.inl (Prod.ext (hx.1.trans hy.1.symm) h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have h := hf.isPLSphere_fiber (fun _ _ => hends) (mem_singleton (0 : ℝ))
  rwa [hf.image_eq] at h

theorem IsCylindricalDiagram.preimage_circle_eq_of_spanning_arc
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hJ : IsPLSphere 1 J)
    {a : E} (ha : a ∈ P)
    (hinter : J ∩ f '' (P ×ˢ ({0} : Set ℝ)) = {f (a, 0)})
    {γ : ℝ → E × ℝ} {A : Set (E × ℝ)} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hA : A ⊆ (P ×ˢ Icc (0 : ℝ) 1) ∩ f ⁻¹' J)
    (hγ0 : γ 0 = (a, 0)) (hγ1 : γ 1 = (a, 1)) :
    (P ×ˢ Icc (0 : ℝ) 1) ∩ f ⁻¹' J = A := by
  have hγmap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := hA (hγ.bijOn.mapsTo ht)
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hseam {x : E × ℝ} (hx : x ∈ (P ×ˢ Icc (0 : ℝ) 1) ∩ f ⁻¹' J)
      (ht : x.2 = 0 ∨ x.2 = 1) : x.1 = a := by
    have hxp : f x = f (a, 0) := by
      rcases ht with ht | ht
      · exact hinter.subset ⟨hx.2, x, ⟨hx.1.1, ht⟩, rfl⟩
      · apply hinter.subset
        refine ⟨hx.2, (x.1, 0), ⟨hx.1.1, rfl⟩, ?_⟩
        rw [hends x.1 hx.1.1]
        exact congrArg f (Prod.ext rfl ht.symm)
    exact ((hf.eq_iff_fst_eq_and_circle_eq hends hx.1 ⟨ha, hzero⟩).mp hxp).1
  have hγheight {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {r : ℝ}
      (hr : r = 0 ∨ r = 1) (htr : (γ t).2 = r) : t = r := by
    have hbase := hseam (hγmap t ht) (htr ▸ hr)
    rcases hr with rfl | rfl
    · exact hγ.bijOn.injOn ht hzero ((Prod.ext hbase htr).trans hγ0.symm)
    · exact hγ.bijOn.injOn ht hone ((Prod.ext hbase htr).trans hγ1.symm)
  have hcomp : IsPiecewiseAffineOn (f ∘ γ) (Icc 0 1) := by
    have h := hf.isPiecewiseAffineOn.comp hγ.isPiecewiseAffineOn
    rwa [inter_eq_left.mpr (show Icc (0 : ℝ) 1 ⊆
      γ ⁻¹' (P ×ˢ Icc (0 : ℝ) 1) from fun t ht => (hγmap t ht).1)] at h
  have hloop : IsPLSphere 1 (f '' A) := by
    rw [← hγ.image_eq, ← image_comp]
    apply isPLSphere_image_Icc_of_eq_or_endpoints hcomp
      (by simpa only [Function.comp_apply, hγ0, hγ1] using hends a ha)
    intro s hs t ht hst
    rcases hf.eq_or_endpoints (γ s) (hγmap s hs).1 (γ t) (hγmap t ht).1 hst with
      h | h | h
    · exact Or.inl (hγ.bijOn.injOn hs ht h)
    · exact Or.inr (Or.inl ⟨hγheight hs (Or.inl rfl) h.1,
        hγheight ht (Or.inr rfl) h.2⟩)
    · exact Or.inr (Or.inr ⟨hγheight hs (Or.inr rfl) h.1,
        hγheight ht (Or.inl rfl) h.2⟩)
  have himage : f '' A = J := eq_of_subset_of_isPLSphere_one hloop hJ
    (image_subset_iff.mpr fun x hx => (hA hx).2)
  apply Subset.antisymm ?_ hA
  intro x hx
  obtain ⟨y, hy, hyx⟩ := himage.symm.subset hx.2
  rcases hf.eq_or_endpoints y (hA hy).1 x hx.1 hyx with h | h | h
  · exact h ▸ hy
  · have heq : x = γ 1 := (Prod.ext (hseam hx (Or.inr h.2)) h.2).trans hγ1.symm
    exact heq ▸ hγ.bijOn.mapsTo hone
  · have heq : x = γ 0 := (Prod.ext (hseam hx (Or.inl h.2)) h.2).trans hγ0.symm
    exact heq ▸ hγ.bijOn.mapsTo hzero


theorem IsCylindricalDiagram.exists_isPLHomeomorphOn_Icc_preimage_circle_of_singleton_seam
    {E : Type} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : E × ℝ → F} {P : Set E} {S J : Set F} {n : ℕ}
    (hf : IsCylindricalDiagram f P S) (hP : IsPLBall n P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hJ : IsPLSphere 1 J) (hJS : J ⊆ S)
    {p : F} (hinter : J ∩ f '' (P ×ˢ ({0} : Set ℝ)) = {p})
    (hnon : ¬ (⟨inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic) :
    ∃ (a : E) (γ : ℝ → E × ℝ), a ∈ P ∧ f (a, 0) = p ∧
      IsPLHomeomorphOn γ (Icc 0 1) ((P ×ˢ Icc (0 : ℝ) 1) ∩ f ⁻¹' J) ∧
      γ 0 = (a, 0) ∧ γ 1 = (a, 1) := by
  have hp := hinter.symm.subset (mem_singleton p)
  obtain ⟨⟨a, t⟩, ⟨ha, ht⟩, hap⟩ := hp.2
  have ht : t = 0 := ht
  subst t
  have hcut := hf.isPiecewiseAffineOn.isPolyhedron_inter_preimage_of_isPolyhedron
    (hP.isPolyhedron.prod isHPolytope_Icc.isPolyhedron) hJ.isPolyhedron
  have hc := hf.isConnected_preimage_circle_of_singleton_seam hP hends hJ hJS hinter hnon
  have ha0 : (a, (0 : ℝ)) ∈ (P ×ˢ Icc (0 : ℝ) 1) ∩ f ⁻¹' J :=
    ⟨⟨ha, le_rfl, zero_le_one⟩, by change f (a, 0) ∈ J; rw [hap]; exact hp.1⟩
  have ha1 : (a, (1 : ℝ)) ∈ (P ×ˢ Icc (0 : ℝ) 1) ∩ f ⁻¹' J :=
    ⟨⟨ha, zero_le_one, le_rfl⟩, by change f (a, 1) ∈ J; rw [← hends a ha]; exact ha0.2⟩
  obtain ⟨γ, hγ, hγ0, hγ1, hγsub⟩ :=
    hcut.exists_isPLHomeomorphOn_Icc_subset_of_isPreconnected hc.isPreconnected ha0 ha1
      (fun h => zero_ne_one (congrArg Prod.snd h))
  have heq := hf.preimage_circle_eq_of_spanning_arc hends hJ ha
    (hap.symm ▸ hinter) hγ hγsub hγ0 hγ1
  exact ⟨a, γ, ha, hap, heq.symm ▸ hγ, hγ0, hγ1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
