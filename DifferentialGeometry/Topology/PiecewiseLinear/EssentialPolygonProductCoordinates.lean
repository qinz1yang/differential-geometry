/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CarriesGeneratorOrIsPLCellOfDisjointCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePrismComparison
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndMap
import DifferentialGeometry.Topology.PiecewiseLinear.LateralAnnulusLevels
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isPLHomeomorphOn_mul_add_Icc_of_neg {m c a b a' b' : ℝ} (hm : m < 0)
    (ha' : m * b + c = a') (hb' : m * a + c = b') :
    IsPLHomeomorphOn (fun t : ℝ => m * t + c) (Icc a b) (Icc a' b') := by
  subst ha' hb'
  have hm0 : m ≠ 0 := hm.ne
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (m • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ c) isHPolytope_Icc) ⟨?_, ?_, ?_⟩
  · intro t ht
    change m * t + c ∈ Icc (m * b + c) (m * a + c)
    have h1 := mul_le_mul_of_nonpos_left ht.1 hm.le
    have h2 := mul_le_mul_of_nonpos_left ht.2 hm.le
    exact ⟨by linarith, by linarith⟩
  · intro s _ t _ hst
    change m * s + c = m * t + c at hst
    exact mul_left_cancel₀ hm0 (by linarith)
  · intro y hy
    have hy1 : m * b + c ≤ y := hy.1
    have hy2 : y ≤ m * a + c := hy.2
    have hdiv : m * ((y - c) / m) = y - c := by field_simp
    refine ⟨(y - c) / m, ⟨?_, ?_⟩, ?_⟩
    · by_contra h
      push Not at h
      nlinarith [mul_lt_mul_of_neg_left h hm]
    · by_contra h
      push Not at h
      nlinarith [mul_lt_mul_of_neg_left h hm]
    · change m * ((y - c) / m) + c = y
      rw [hdiv]
      ring

theorem exists_isCylindricalDiagram_eqOn_eqOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P : Set E} (hP : IsPolyhedron P) {A B D₀ D₁ : Set F} {f g : E × ℝ → F}
    (hf : IsPLHomeomorphOn f (P ×ˢ Icc 0 (1 / 2)) A)
    (hg : IsPLHomeomorphOn g (P ×ˢ Icc (1 / 2) 1) B)
    (hf₀ : f '' (P ×ˢ {0}) = D₀) (hg₁ : g '' (P ×ˢ {1}) = D₀)
    (hfm : f '' (P ×ˢ {1 / 2}) = D₁)
    (hfg : EqOn f g (P ×ˢ {1 / 2})) (hinter : A ∩ B = D₀ ∪ D₁) :
    ∃ φ : E × ℝ → F, IsCylindricalDiagram φ P (A ∪ B) ∧ EqOn φ f (P ×ˢ Icc 0 (1 / 2)) ∧
      EqOn φ g (P ×ˢ Icc (1 / 2) 1) := by
  classical
  have hfg' : EqOn f g (P ×ˢ Icc (0 : ℝ) (1 / 2) ∩ P ×ˢ Icc (1 / 2) 1) :=
    fun z hz => hfg ⟨hz.1.1, le_antisymm hz.1.2.2 hz.2.2.1⟩
  refine ⟨_, isCylindricalDiagram_piecewise hP hf hg hf₀ hg₁ hfm hfg hinter, ?_, ?_⟩
  · convert (P ×ˢ Icc (0 : ℝ) (1 / 2)).piecewise_eqOn f g
  · convert eqOn_piecewise_of_eqOn_inter hfg'

theorem IsCylindricalDiagram.exists_prod_chart_of_eq_ends {T : Set E3}
    {g : (Fin 3 → ℝ) × ℝ → E3} (hg : IsCylindricalDiagram g (stdSimplexBoundary 2) T)
    (hends : ∀ x ∈ stdSimplexBoundary 2, g (x, 0) = g (x, 1)) :
    ∃ (J Q : Set E3) (f : E3 × E3 → E3) (γ : ℝ → E3), IsPLSphere 1 J ∧ IsPLSphere 1 Q ∧
      IsPLHomeomorphOn f (J ×ˢ Q) T ∧ (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Q) ∧ InjOn γ (Ico 0 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, f '' (J ×ˢ {γ t}) = g '' (stdSimplexBoundary 2 ×ˢ {t}) := by
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  set e : (Fin 3 → ℝ) ≃L[ℝ] E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm with hedef
  let eA : (Fin 3 → ℝ) →ᵃ[ℝ] E3 := (e : (Fin 3 → ℝ) →L[ℝ] E3).toLinearMap.toAffineMap
  have heA : IsPiecewiseAffineOn eA (stdSimplexBoundary 2) :=
    (isPiecewiseAffineOn_of_affine eA isOpen_univ).mono_of_isPolyhedron hBpoly (subset_univ _)
  have he : IsPLHomeomorphOn e (stdSimplexBoundary 2) (e '' stdSimplexBoundary 2) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hBpoly heA e.injective.injOn.bijOn_image
  have hend : stdTriangleLoop 0 = stdTriangleLoop 1 := by norm_num [stdTriangleLoop]
  have hloop {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
      (hst : stdTriangleLoop s = stdTriangleLoop t) :
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    by_cases hs1 : s = 1
    · by_cases ht1 : t = 1
      · exact Or.inl (hs1.trans ht1.symm)
      · have ht0 : t = 0 := injOn_stdTriangleLoop ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
          ⟨le_rfl, zero_lt_one⟩ (hst.symm.trans (hs1 ▸ hend.symm))
        exact Or.inr (Or.inr ⟨hs1, ht0⟩)
    · by_cases ht1 : t = 1
      · have hs0 : s = 0 := injOn_stdTriangleLoop ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
          ⟨le_rfl, zero_lt_one⟩ (hst.trans (ht1 ▸ hend.symm))
        exact Or.inr (Or.inl ⟨hs0, ht1⟩)
      · exact Or.inl (injOn_stdTriangleLoop ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
          ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩ hst)
  have hfm : IsCylindricalDiagram (fun z : (Fin 3 → ℝ) × ℝ => (e z.1, e (stdTriangleLoop z.2)))
      (stdSimplexBoundary 2) ((e '' stdSimplexBoundary 2) ×ˢ (e '' stdSimplexBoundary 2)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact heA.prodMap (isPiecewiseAffineOn_stdTriangleLoop.affine_comp eA)
    · apply Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        exact ⟨⟨z.1, hz.1, rfl⟩, ⟨_, stdTriangleLoop_image.subset ⟨z.2, hz.2, rfl⟩, rfl⟩⟩
      · rintro ⟨u, v⟩ ⟨⟨x, hx, hxu⟩, ⟨y, hy, hyv⟩⟩
        obtain ⟨t, ht, hty⟩ := stdTriangleLoop_image.symm.subset hy
        refine ⟨(x, t), ⟨hx, ht⟩, ?_⟩
        change (e x, e (stdTriangleLoop t)) = (u, v)
        rw [hxu, hty, hyv]
    · apply Subset.antisymm
      · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
        change t = 1 at ht
        subst t
        exact ⟨(x, 0), ⟨hx, rfl⟩, by change (e x, e (stdTriangleLoop 0)) = _; rw [hend]⟩
      · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
        change t = 0 at ht
        subst t
        exact ⟨(x, 1), ⟨hx, rfl⟩, by change (e x, e (stdTriangleLoop 1)) = _; rw [← hend]⟩
    · intro z hz w hw hzw
      have h1 : z.1 = w.1 := e.injective (congrArg Prod.fst hzw)
      have h2 : stdTriangleLoop z.2 = stdTriangleLoop w.2 := e.injective (congrArg Prod.snd hzw)
      rcases hloop hz.2 hw.2 h2 with h | h | h
      · exact Or.inl (Prod.ext h1 h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  obtain ⟨H, hH, hHf⟩ := exists_isPLHomeomorphOn_of_eq_endMap hBpoly hfm hg
    hBpoly.isPLHomeomorphOn_id
    (fun x _ => by
      change (e x, e (stdTriangleLoop 0)) = (e x, e (stdTriangleLoop 1))
      rw [hend])
    (fun x hx => hends x hx)
  have hJ : IsPLSphere 1 (e '' stdSimplexBoundary 2) := ⟨e, he⟩
  refine ⟨e '' stdSimplexBoundary 2, e '' stdSimplexBoundary 2, H, fun t => e (stdTriangleLoop t),
    hJ, hJ, hH, fun t ht => ⟨_, stdTriangleLoop_image.subset ⟨t, ht, rfl⟩, rfl⟩,
    fun s hs t ht hst => injOn_stdTriangleLoop hs ht (e.injective hst), fun t ht => ?_⟩
  have hfib : (e '' stdSimplexBoundary 2) ×ˢ {e (stdTriangleLoop t)} =
      (fun z : (Fin 3 → ℝ) × ℝ => (e z.1, e (stdTriangleLoop z.2))) ''
        (stdSimplexBoundary 2 ×ˢ {t}) := by
    apply Subset.antisymm
    · rintro ⟨u, v⟩ ⟨⟨x, hx, hxu⟩, hv⟩
      refine ⟨(x, t), ⟨hx, rfl⟩, ?_⟩
      change (e x, e (stdTriangleLoop t)) = (u, v)
      rw [hxu, (mem_singleton_iff.mp hv).symm]
    · rintro _ ⟨z, hz, rfl⟩
      have hz2 : z.2 = t := hz.2
      refine ⟨⟨z.1, hz.1, rfl⟩, ?_⟩
      change e (stdTriangleLoop z.2) = e (stdTriangleLoop t)
      rw [hz2]
  rw [hfib, ← image_comp]
  refine image_congr fun z hz => hHf z ⟨hz.1, ?_⟩
  rw [mem_singleton_iff.mp hz.2]
  exact ht

theorem IsCylindricalDiagram.exists_eq_ends_of_isOrientable {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (L : Geometry.SimplicialComplex ℝ F)
    [Finite L.faces] (hL : IsCombinatorialManifoldWithBoundary 2 L) (hLo : IsOrientable 2 L)
    {T : Set F} (hTL : T ⊆ L.space) {g : (Fin 3 → ℝ) × ℝ → F}
    (hg : IsCylindricalDiagram g (stdSimplexBoundary 2) T) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ∃ g' : (Fin 3 → ℝ) × ℝ → F, IsCylindricalDiagram g' (stdSimplexBoundary 2) T ∧
      (∀ x ∈ stdSimplexBoundary 2, g' (x, 0) = g' (x, 1)) ∧
      ∀ z ∈ stdSimplexBoundary 2 ×ˢ Icc 0 c, g' z = g z := by
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  have hPsph : IsPLSphere 1 (stdSimplexBoundary 2) := ⟨id, hBpoly.isPLHomeomorphOn_id⟩
  obtain ⟨u, hu, hgu⟩ := hg.exists_isPLHomeomorphOn_endMap hBpoly
  have hv : IsPLCirclePositive (stdSimplexBoundary 2)
      (Function.invFunOn u (stdSimplexBoundary 2)) :=
    isPLCirclePositive_of_isOrientable_cylindricalDiagram L hL hLo hPsph hg hTL hu.symm
      fun x hx => by
        rw [hgu _ (hu.symm.bijOn.mapsTo hx), hu.bijOn.invOn_invFunOn.2 hx]
  have hupos : IsPLCirclePositive (stdSimplexBoundary 2) u :=
    hv.of_leftInverse hu.symm.bijOn hu.bijOn.mapsTo fun x hx => hu.bijOn.invOn_invFunOn.2 hx
  obtain ⟨Ψ, hΨ, hΨ0, hΨ1⟩ := isPLPseudoIsotopicToId_of_isPLCirclePositive hPsph hu hupos
  obtain ⟨Θ, hΘ, hΘlow, hΘhigh, -⟩ :=
    hBpoly.exists_isPLHomeomorphOn_prod_Icc_of_slab hΨ hΨ0 hu hΨ1 hc0 hc1 le_rfl
  have hΘ0 : ∀ x ∈ stdSimplexBoundary 2, Θ (x, 0) = (id x, 0) :=
    fun x hx => hΘlow (x, 0) ⟨hx, le_rfl, hc0⟩
  have hΘ1 : ∀ x ∈ stdSimplexBoundary 2, Θ (x, 1) = (u x, 1) :=
    fun x hx => hΘhigh (x, 1) ⟨hx, le_rfl, le_rfl⟩
  refine ⟨g ∘ Θ, hg.comp_of_ends hBpoly.isPLHomeomorphOn_id hu hΘ hΘ0 hΘ1, fun x hx => ?_,
    fun z hz => ?_⟩
  · change g (Θ (x, 0)) = g (Θ (x, 1))
    rw [hΘ0 x hx, hΘ1 x hx]
    exact hgu x hx
  · change g (Θ z) = g z
    rw [hΘlow z hz]

theorem IsPLHomeomorphOn.exists_prism_levels_of_essential {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {Rs : Set F} {h : (Fin 3 → ℝ) × ℝ → F}
    (hh : IsPLHomeomorphOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) Rs)
    {C : Set (Set F)} (hC : C.Finite) (hCsph : ∀ c ∈ C, IsPLSphere 1 c)
    (hCR : ∀ c ∈ C, c ⊆ Rs \ (h '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      h '' (stdSimplexBoundary 2 ×ˢ {1})))
    (hCess : ∀ c ∈ C, ¬ ∃ (D : Set F) (r : (Fin 3 → ℝ) → F),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ Rs ∧ r '' stdSimplexBoundary 2 = c)
    (hCdisj : C.PairwiseDisjoint id) :
    ∃ (h' : (Fin 3 → ℝ) × ℝ → F) (s : Set F → ℝ),
      IsPLHomeomorphOn h' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) Rs ∧
      h' '' (stdSimplexBoundary 2 ×ˢ {0}) = h '' (stdSimplexBoundary 2 ×ˢ {0}) ∧
      h' '' (stdSimplexBoundary 2 ×ˢ {1}) = h '' (stdSimplexBoundary 2 ×ˢ {1}) ∧
      ∀ c ∈ C, s c ∈ Ioo (0 : ℝ) 1 ∧ h' '' (stdSimplexBoundary 2 ×ˢ {s c}) = c := by
  have hhi : IsPLHomeomorphOn (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) Rs
      (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := hh.symm
  set k := Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) with hkdef
  have hcR : ∀ c ∈ C, c ⊆ Rs := fun c hc x hx => (hCR c hc hx).1
  have hhk : ∀ c ∈ C, h '' (k '' c) = c := fun c hc =>
    LeftInvOn.image_image (hh.bijOn.invOn_invFunOn.2.mono (hcR c hc))
  have hkC : ∀ c ∈ C, k '' c ⊆ stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1 := by
    rintro c hc _ ⟨x, hx, rfl⟩
    have hxR := hcR c hc hx
    have hyA := hhi.bijOn.mapsTo hxR
    have hhy : h (k x) = x := hh.bijOn.invOn_invFunOn.2 hxR
    refine ⟨hyA.1, lt_of_le_of_ne hyA.2.1 fun h0 => ?_, lt_of_le_of_ne hyA.2.2 fun h1 => ?_⟩
    · exact (hCR c hc hx).2 (Or.inl ⟨_, ⟨hyA.1, h0.symm⟩, hhy⟩)
    · exact (hCR c hc hx).2 (Or.inr ⟨_, ⟨hyA.1, h1⟩, hhy⟩)
  have hkS : ∀ c ∈ C, IsPLSphere 1 (k '' c) := fun c hc =>
    (hCsph c hc).of_isPLHomeomorphOn (hhi.restrict (hCsph c hc).isPolyhedron (hcR c hc))
  have hkE : ∀ c ∈ C, ¬ ∃ (D : Set ((Fin 3 → ℝ) × ℝ)) (r : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧
      r '' stdSimplexBoundary 2 = k '' c := by
    rintro c hc ⟨D, r, hr, hDA, hrb⟩
    exact hCess c hc ⟨h '' D, h ∘ r, hr.trans (hh.restrict (IsPLBall.isPolyhedron ⟨r, hr⟩) hDA),
      image_subset_iff.mpr fun d hd => hh.bijOn.mapsTo (hDA hd), by rw [image_comp, hrb, hhk c hc]⟩
  have hC'disj : ((fun c => k '' c) '' C).PairwiseDisjoint id := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ hne
    have hcc : c ≠ c' := fun hcc => hne (congrArg (fun c => k '' c) hcc)
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
    have e1 : h (k x') = x' := hh.bijOn.invOn_invFunOn.2 (hcR c' hc' hx')
    have e2 : h (k x) = x := hh.bijOn.invOn_invFunOn.2 (hcR c hc hx)
    have hx'x : x' = x := by rw [← e1, hxx', e2]
    exact disjoint_left.mp (hCdisj hc hc' hcc) hx (hx'x ▸ hx')
  obtain ⟨Φ, s, hΦ, hΦ0, hΦ1, hΦC⟩ := exists_isPLHomeomorphOn_prism_lateral_levels
    ((fun c => k '' c) '' C) (hC.image _) (by rintro _ ⟨c, hc, rfl⟩; exact hkS c hc)
    (by rintro _ ⟨c, hc, rfl⟩; exact hkC c hc) (by rintro _ ⟨c, hc, rfl⟩; exact hkE c hc)
    hC'disj
  refine ⟨h ∘ Φ, fun c => s (k '' c), hΦ.trans hh, by rw [image_comp, hΦ0],
    by rw [image_comp, hΦ1], fun c hc => ?_⟩
  obtain ⟨hs, hΦc⟩ := hΦC _ ⟨c, hc, rfl⟩
  exact ⟨hs, by rw [image_comp, hΦc, hhk c hc]⟩

theorem exists_isCylindricalDiagram_of_annulus_bicollar {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {Rs W J : Set F} {h : (Fin 3 → ℝ) × ℝ → F}
    {ρ : F × ℝ → F} (hh : IsPLHomeomorphOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) Rs)
    (hh0 : h '' (stdSimplexBoundary 2 ×ˢ {0}) = ρ '' (J ×ˢ {-1}))
    (hh1 : h '' (stdSimplexBoundary 2 ×ˢ {1}) = ρ '' (J ×ˢ {1})) (hJ : IsPolyhedron J)
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ J, ρ (x, 0) = x)
    (hWR : W ∩ Rs = ρ '' (J ×ˢ {-1, 1})) :
    ∃ g : (Fin 3 → ℝ) × ℝ → F, IsCylindricalDiagram g (stdSimplexBoundary 2) (Rs ∪ W) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        g '' (stdSimplexBoundary 2 ×ˢ {t / 2}) = h '' (stdSimplexBoundary 2 ×ˢ {t})) ∧
      g '' (stdSimplexBoundary 2 ×ˢ {3 / 4}) = J := by
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  have hsub1 : stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ) ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; norm_num⟩
  have hr1 : IsPLHomeomorphOn h (stdSimplexBoundary 2 ×ˢ {1}) (ρ '' (J ×ˢ {1})) := by
    have h' := hh.restrict (isPolyhedron_prod_singleton hBpoly 1) hsub1
    rwa [hh1] at h'
  have hJ1 : J ×ˢ ({1} : Set ℝ) ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    fun z hz => ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; norm_num⟩
  have hρ1 : IsPLHomeomorphOn ρ (J ×ˢ {1}) (ρ '' (J ×ˢ {1})) :=
    hρ.restrict (isPolyhedron_prod_singleton hJ 1) hJ1
  have hm : IsPLHomeomorphOn (Prod.fst ∘ Function.invFunOn ρ (J ×ˢ {1}) ∘ h ∘
      fun x => (x, (1 : ℝ))) (stdSimplexBoundary 2) J :=
    (((hBpoly.isPLHomeomorphOn_prod_const 1).trans hr1).trans hρ1.symm).trans
      (hJ.isPLHomeomorphOn_fst_prod_const 1)
  set m := Prod.fst ∘ Function.invFunOn ρ (J ×ˢ {1}) ∘ h ∘ fun x => (x, (1 : ℝ)) with hmdef
  have hmspec : ∀ x ∈ stdSimplexBoundary 2, ρ (m x, 1) = h (x, 1) := by
    intro x hx
    have hk : h (x, 1) ∈ ρ '' (J ×ˢ {1}) := hr1.bijOn.mapsTo ⟨hx, rfl⟩
    have hw : Function.invFunOn ρ (J ×ˢ {1}) (h (x, 1)) ∈ J ×ˢ ({1} : Set ℝ) :=
      hρ1.symm.bijOn.mapsTo hk
    have hw2 : (Function.invFunOn ρ (J ×ˢ {1}) (h (x, 1))).2 = 1 := hw.2
    calc ρ (m x, 1) = ρ (Function.invFunOn ρ (J ×ˢ {1}) (h (x, 1))) :=
          congrArg ρ (Prod.ext rfl hw2.symm)
      _ = h (x, 1) := hρ1.bijOn.invOn_invFunOn.2 hk
  have hf₁ : IsPLHomeomorphOn (h ∘ Prod.map id fun t : ℝ => 2 * t + 0)
      (stdSimplexBoundary 2 ×ˢ Icc 0 (1 / 2)) Rs :=
    (hBpoly.isPLHomeomorphOn_id.prodMap (isPLHomeomorphOn_mul_add_Icc two_pos (by norm_num)
      (by norm_num))).trans hh
  have hf₂ : IsPLHomeomorphOn (ρ ∘ Prod.map m fun t : ℝ => -4 * t + 3)
      (stdSimplexBoundary 2 ×ˢ Icc (1 / 2) 1) W :=
    (hm.prodMap (isPLHomeomorphOn_mul_add_Icc_of_neg (by norm_num) (by norm_num)
      (by norm_num))).trans hρ
  have hlev₁ : ∀ t : ℝ, Prod.map id (fun t : ℝ => 2 * t + 0) '' (stdSimplexBoundary 2 ×ˢ {t}) =
      stdSimplexBoundary 2 ×ˢ {2 * t} := by
    intro t
    rw [prodMap_image_prod, image_id, image_singleton, add_zero]
  have hlev₂ : ∀ t : ℝ, Prod.map m (fun t : ℝ => -4 * t + 3) '' (stdSimplexBoundary 2 ×ˢ {t}) =
      J ×ˢ {-4 * t + 3} := by
    intro t
    rw [prodMap_image_prod, hm.image_eq, image_singleton]
  have hf₀ : (h ∘ Prod.map id fun t : ℝ => 2 * t + 0) '' (stdSimplexBoundary 2 ×ˢ {0}) =
      ρ '' (J ×ˢ {-1}) := by
    rw [image_comp, hlev₁, mul_zero, hh0]
  have hg₁ : (ρ ∘ Prod.map m fun t : ℝ => -4 * t + 3) '' (stdSimplexBoundary 2 ×ˢ {1}) =
      ρ '' (J ×ˢ {-1}) := by
    rw [image_comp, hlev₂]
    norm_num
  have hfm : (h ∘ Prod.map id fun t : ℝ => 2 * t + 0) '' (stdSimplexBoundary 2 ×ˢ {1 / 2}) =
      ρ '' (J ×ˢ {1}) := by
    rw [image_comp, hlev₁, show (2 : ℝ) * (1 / 2) = 1 by norm_num, hh1]
  have hfg : EqOn (h ∘ Prod.map id fun t : ℝ => 2 * t + 0)
      (ρ ∘ Prod.map m fun t : ℝ => -4 * t + 3) (stdSimplexBoundary 2 ×ˢ {1 / 2}) := by
    intro z hz
    have hz2 : z.2 = 1 / 2 := hz.2
    rw [show z = (z.1, 1 / 2) from Prod.ext rfl hz2]
    change h (z.1, 2 * (1 / 2) + 0) = ρ (m z.1, -4 * (1 / 2) + 3)
    rw [show (2 : ℝ) * (1 / 2) + 0 = 1 by norm_num, show (-4 : ℝ) * (1 / 2) + 3 = 1 by norm_num,
      hmspec z.1 hz.1]
  have hinter : Rs ∩ W = ρ '' (J ×ˢ {-1}) ∪ ρ '' (J ×ˢ {1}) := by
    rw [inter_comm, hWR, ← singleton_union, prod_union, image_union]
  obtain ⟨g, hg, hg₁', hg₂'⟩ :=
    exists_isCylindricalDiagram_eqOn_eqOn hBpoly hf₁ hf₂ hf₀ hg₁ hfm hfg hinter
  refine ⟨g, hg, fun t ht => ?_, ?_⟩
  · have hsub : stdSimplexBoundary 2 ×ˢ ({t / 2} : Set ℝ) ⊆
        stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) (1 / 2) := fun z hz =>
      ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    rw [image_congr fun z hz => hg₁' (hsub hz), image_comp, hlev₁,
      show 2 * (t / 2) = t by ring]
  · have hsub : stdSimplexBoundary 2 ×ˢ ({3 / 4} : Set ℝ) ⊆
        stdSimplexBoundary 2 ×ˢ Icc (1 / 2 : ℝ) 1 := fun z hz =>
      ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; norm_num⟩
    rw [image_congr fun z hz => hg₂' (hsub hz), image_comp, hlev₂,
      show (-4 : ℝ) * (3 / 4) + 3 = 0 by norm_num]
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [show z = (z.1, 0) from Prod.ext rfl (mem_singleton_iff.mp hz.2), hzero z.1 hz.1]
      exact hz.1
    · intro y hy
      exact ⟨(y, 0), ⟨hy, rfl⟩, hzero y hy⟩

open Classical in
theorem exists_product_coordinates_for_disjoint_essential_polygons
    {S : Set E3} (hS : IsCombinatorialSolidTorus S) {n : ℕ} (G : Fin n → Set E3)
    (hn : 1 < n) (hG : ∀ i, IsPLSphere 1 (G i)) (hGS : ∀ i, G i ⊆ frontier S)
    (hdisj : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hess : ∀ i, ¬ ∃ (Δ : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ frontier S ∧
        G i = r '' stdSimplexBoundary 2) :
    ∃ (J Q : Set E3) (f : E3 × E3 → E3) (q : Fin n → E3),
      IsPLSphere 1 J ∧ IsPLSphere 1 Q ∧ IsPLHomeomorphOn f (J ×ˢ Q) (frontier S) ∧
      (∀ i, q i ∈ Q) ∧ Function.Injective q ∧ ∀ i, G i = f '' (J ×ˢ {q i}) := by
  have hT : IsPLTorus (frontier S) := hS.isPLTorus_frontier
  obtain ⟨L, hLfin, hL, hLc, hLT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hLo := hL.isOrientable_euclidean_three L hLc
  have hβ := hT.bettiOne_le_two
  rw [← hLT] at hβ
  have hχ := hL.eulerChar_eq_two_sub_bettiOne_of_isOrientable L hLc hLo
  have hGL : ∀ i, G i ⊆ L.space := fun i => hLT ▸ hGS i
  let i₀ : Fin n := ⟨0, by omega⟩
  have hnonsep : IsPreconnected (L.space \ G i₀) := by
    by_contra hsep
    rw [hLT] at hsep
    exact hess i₀
      (hT.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff (hG i₀) (hGS i₀) hsep)
  have hZ : IsClosed (⋃ i ∈ {i : Fin n | i ≠ i₀}, G i) :=
    (toFinite _).isClosed_biUnion fun i _ => (hG i).isPolyhedron.isClosed
  have hU : L.space \ ⋃ i ∈ {i : Fin n | i ≠ i₀}, G i ∈ 𝓝ˢ[L.space] G i₀ := by
    refine mem_nhdsSetWithin.mpr ⟨(⋃ i ∈ {i : Fin n | i ≠ i₀}, G i)ᶜ, hZ.isOpen_compl,
      fun x hx hxZ => ?_, fun x hx => ⟨hx.2, hx.1⟩⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxZ
    exact disjoint_left.mp (hdisj (Ne.symm hi)) hx hxi
  obtain ⟨R, hRfin, hR, -, hRc, hRχ, W, ρ, -, -, hWU, -, hρ, hzero, -, -, hRbd, hWR, hcover,
      hGm, hGp, hdisjpm⟩ :=
    hL.exists_connected_annulus_complement L hLo (hG i₀) (hGL i₀) hnonsep hU
  let _ : Finite R.faces := hRfin.to_subtype
  have hRbd' := hRbd.trans (show ρ '' (G i₀ ×ˢ {(-1 : ℝ), 1}) =
      ρ '' (G i₀ ×ˢ {(-1 : ℝ)}) ∪ ρ '' (G i₀ ×ˢ {(1 : ℝ)}) by
    rw [← singleton_union, prod_union, image_union])
  have hRχ0 : eulerChar R = 0 := by
    have hle := hR.eulerChar_nonpos_of_boundary_eq_union R hRc hGm hGp hdisjpm hRbd'
    omega
  obtain ⟨h, hh, hh0, hh1⟩ :=
    hR.exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero R hRc hRχ0 hGm hGp hdisjpm hRbd'
  have hCW : ρ '' (G i₀ ×ˢ {(-1 : ℝ)}) ∪ ρ '' (G i₀ ×ˢ {(1 : ℝ)}) ⊆ W := by
    rw [← hρ.image_eq]
    rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, ⟨hy.1, by rw [mem_singleton_iff.mp hy.2]; norm_num⟩, rfl⟩
    · exact ⟨y, ⟨hy.1, by rw [mem_singleton_iff.mp hy.2]; norm_num⟩, rfl⟩
  have hGW : ∀ i ∈ {i : Fin n | i ≠ i₀}, Disjoint (G i) W := by
    intro i hi
    refine disjoint_left.mpr fun x hx hxW => (hWU hxW).2 ?_
    exact mem_iUnion₂.mpr ⟨i, hi, hx⟩
  have hGR : ∀ i ∈ {i : Fin n | i ≠ i₀}, G i ⊆ R.space := by
    intro i hi x hx
    have hxL : x ∈ W ∪ R.space := by
      rw [hcover]
      exact hGL i hx
    exact hxL.resolve_left (disjoint_left.mp (hGW i hi) hx)
  have hRT : R.space ⊆ frontier S := by
    intro x hx
    rw [← hLT, ← hcover]
    exact Or.inr hx
  obtain ⟨h', s, hh', hh'0, hh'1, hh'C⟩ := hh.exists_prism_levels_of_essential
    ((toFinite {i : Fin n | i ≠ i₀}).image G)
    (by
      rintro _ ⟨i, -, rfl⟩
      exact hG i)
    (by
      rintro _ ⟨i, hi, rfl⟩ x hx
      refine ⟨hGR i hi hx, ?_⟩
      rintro (hx0 | hx1)
      · rw [hh0] at hx0
        exact disjoint_left.mp (hGW i hi) hx (hCW (Or.inl hx0))
      · rw [hh1] at hx1
        exact disjoint_left.mp (hGW i hi) hx (hCW (Or.inr hx1)))
    (by
      rintro _ ⟨i, -, rfl⟩ ⟨D, r, hr, hDR, hrb⟩
      exact hess i ⟨D, r, hr, hDR.trans hRT, hrb.symm⟩)
    (by
      rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩ hne
      exact hdisj fun hij => hne (congrArg G hij))
  obtain ⟨g, hg, hglev, hg34⟩ := exists_isCylindricalDiagram_of_annulus_bicollar hh'
    (hh'0.trans hh0) (hh'1.trans hh1) (hG i₀).isPolyhedron hρ hzero hWR
  have hRW : R.space ∪ W = frontier S := by
    rw [union_comm, hcover, hLT]
  obtain ⟨g', hg', hends, hgg'⟩ := hg.exists_eq_ends_of_isOrientable L
    hL.isCombinatorialManifoldWithBoundary hLo (hRW.trans hLT.symm).subset
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
  obtain ⟨J, Q, f, γ, hJ, hQ, hf, hγQ, hγinj, hfib⟩ := hg'.exists_prod_chart_of_eq_ends hends
  let t : Fin n → ℝ := fun i => if i = i₀ then 3 / 4 else s (G i) / 2
  have ht : ∀ i, t i ∈ Icc (0 : ℝ) (3 / 4) := by
    intro i
    by_cases hi : i = i₀
    · simp only [t, ite_eq_left hi]
      norm_num
    · simp only [t, ite_eq_right hi]
      obtain ⟨hs, -⟩ := hh'C (G i) ⟨i, hi, rfl⟩
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hlevel : ∀ i, g '' (stdSimplexBoundary 2 ×ˢ {t i}) = G i := by
    intro i
    by_cases hi : i = i₀
    · simp only [t, ite_eq_left hi]
      rw [hg34, hi]
    · simp only [t, ite_eq_right hi]
      obtain ⟨hs, hsG⟩ := hh'C (G i) ⟨i, hi, rfl⟩
      rw [hglev (s (G i)) ⟨hs.1.le, hs.2.le⟩, hsG]
  have ht1 : ∀ i, t i ∈ Icc (0 : ℝ) 1 :=
    fun i => Icc_subset_Icc le_rfl (by norm_num) (ht i)
  have hlevel' : ∀ i, f '' (J ×ˢ {γ (t i)}) = G i := by
    intro i
    rw [hfib (t i) (ht1 i), image_congr fun z hz =>
      hgg' z ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; exact ht i⟩, hlevel i]
  refine ⟨J, Q, f, γ ∘ t, hJ, hQ, hRW ▸ hf, fun i => hγQ (t i) (ht1 i), fun i j hij => ?_,
    fun i => (hlevel' i).symm⟩
  have hti : t i ∈ Ico (0 : ℝ) 1 := ⟨(ht i).1, by linarith [(ht i).2]⟩
  have htj : t j ∈ Ico (0 : ℝ) 1 := ⟨(ht j).1, by linarith [(ht j).2]⟩
  have htt : t i = t j := hγinj hti htj hij
  by_contra hne
  have hGij : G i = G j := by
    rw [← hlevel i, ← hlevel j, htt]
  obtain ⟨x, hx⟩ := (hG i).nonempty
  exact disjoint_left.mp (hdisj hne) hx (hGij ▸ hx)

end DifferentialGeometry.Topology.PiecewiseLinear
