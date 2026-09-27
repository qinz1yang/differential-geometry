import DifferentialGeometry.Topology.PiecewiseLinear.Section34CappedLateralAnnulus
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SpanningPairCrosscut

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_crosscut_disk_with_cap_contact
    {D C A : Set (EuclideanSpace ℝ (Fin 2))}
    (hD : IsPLBall 2 D) (hC : IsPLBall 2 C) (hCD : C ⊆ D)
    (hA : IsPLBall 1 A) {p q : EuclideanSpace ℝ (Fin 2)}
    (hcut : Schoenflies.IsCrosscut (frontier D) A p q)
    (hCA : Disjoint (interior C) A) :
    ∃ F B : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 2 F ∧ IsPLBall 1 B ∧ F ⊆ D ∧ F ∩ C = A ∩ C ∧
      frontier F = A ∪ B ∧ F ∩ frontier D = B ∧
      ∀ Z : Set (EuclideanSpace ℝ (Fin 2)), IsPreconnected Z → Z ⊆ D →
        Disjoint Z A → (Z ∩ C).Nonempty → Disjoint F Z := by
  obtain ⟨U, V, hU, hV, hcover, hmeet, hUF, hVF, hAU, hAV, hUB, hVB, hside⟩ :=
    exists_isPLBall_pair_with_boundary_arcs_of_isCrosscut hD hA hcut
  have hUD : U ⊆ D := subset_union_left.trans hcover.subset
  have hVD : V ⊆ D := subset_union_right.trans hcover.subset
  have hfront (F : Set (EuclideanSpace ℝ (Fin 2))) (hF : IsPLBall 2 F) (hFD : F ⊆ D)
      (hFA : frontier F ⊆ frontier D ∪ A) (hAF : A ⊆ frontier F) :
      frontier F = A ∪ (F ∩ frontier D) := by
    apply Subset.antisymm
    · intro x hx
      rcases hFA hx with hxD | hxA
      · exact Or.inr ⟨hF.isPolyhedron.isClosed.frontier_subset hx, hxD⟩
      · exact Or.inl hxA
    · rintro x (hxA | hxD)
      · exact hAF hxA
      · exact ⟨subset_closure hxD.1, fun hx => hxD.2.2 (interior_mono hFD hx)⟩
  have havoid (F V : Set (EuclideanSpace ℝ (Fin 2))) (hF : IsClosed F) (hV : IsClosed V)
      (hcover : F ∪ V = D) (hmeet : F ∩ V = A) (hCV : C ⊆ V)
      (Z : Set (EuclideanSpace ℝ (Fin 2))) (hZ : IsPreconnected Z) (hZD : Z ⊆ D)
      (hZA : Disjoint Z A) (hZC : (Z ∩ C).Nonempty) : Disjoint F Z := by
    obtain ⟨a, haZ, haC⟩ := hZC
    refine disjoint_left.mpr fun x hxF hxZ => ?_
    obtain ⟨y, hyZ, hyFV⟩ := isPreconnected_closed_iff.mp hZ F V hF hV
      (hZD.trans hcover.symm.subset) ⟨x, hxZ, hxF⟩ ⟨a, haZ, hCV haC⟩
    exact disjoint_left.mp hZA hyZ (hmeet.subset hyFV)
  rcases hside C hC hCD hCA with hCU | hCV
  · refine ⟨V, V ∩ frontier D, hV, hVB, hVD, ?_, hfront V hV hVD hVF hAV, rfl, ?_⟩
    · exact Subset.antisymm
        (fun x hx => ⟨hmeet.subset ⟨hCU hx.2, hx.1⟩, hx.2⟩)
        (fun x hx => ⟨(hmeet.symm.subset hx.1).2, hx.2⟩)
    · exact havoid V U hV.isPolyhedron.isClosed hU.isPolyhedron.isClosed
        ((union_comm V U).trans hcover) ((inter_comm V U).trans hmeet) hCU
  · refine ⟨U, U ∩ frontier D, hU, hUB, hUD, ?_, hfront U hU hUD hUF hAU, rfl, ?_⟩
    · exact Subset.antisymm
        (fun x hx => ⟨hmeet.subset ⟨hx.1, hCV hx.2⟩, hx.2⟩)
        (fun x hx => ⟨(hmeet.symm.subset hx.1).1, hx.2⟩)
    · exact havoid U V hU.isPolyhedron.isClosed hV.isPolyhedron.isClosed hcover hmeet hCV

theorem IsPLHomeomorphOn.exists_crosscut_disk_with_cap_contact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D C A : Set E} {r c : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hc : IsPLHomeomorphOn c (stdSimplex ℝ (Fin 3)) C) (hCD : C ⊆ D)
    {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) (hAD : A ⊆ D)
    (hends : A ∩ r '' stdSimplexBoundary 2 = {γ 0, γ 1})
    (hCA : C ∩ A ⊆ c '' stdSimplexBoundary 2) :
    ∃ (F B : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) F ∧ IsPLBall 1 B ∧
      F ⊆ D ∧ F ∩ C = A ∩ C ∧ q '' stdSimplexBoundary 2 = A ∪ B ∧
      F ∩ r '' stdSimplexBoundary 2 = B ∧
      ∀ Z : Set E, IsPreconnected Z → Z ⊆ D → Disjoint Z A →
        (Z ∩ C).Nonempty → Disjoint F Z := by
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hC : IsPLBall 2 C := ⟨c, hc⟩
  have hA : IsPLBall 1 A := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ
  obtain ⟨J, σ, hJ, hσ⟩ := exists_planar_coordinates_of_isPLBall_two hD
  let R := closure (Schoenflies.inside J)
  have hR : IsPLBall 2 R := isPLBall_closure_inside_of_isPLSphere_one hJ
  have hrimD : r '' stdSimplexBoundary 2 ⊆ D :=
    (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hσrim : σ '' (r '' stdSimplexBoundary 2) = J := by
    rw [← image_comp]
    exact (hr.trans hσ).image_stdSimplexBoundary.trans
      (frontier_closure_inside_of_isPLSphere_one hJ)
  have hσC := hσ.restrict hC.isPolyhedron hCD
  have hσA := hσ.restrict hA.isPolyhedron hAD
  have hC' : IsPLBall 2 (σ '' C) := hC.of_isPLHomeomorphOn hσC
  have hA' : IsPLBall 1 (σ '' A) := hA.of_isPLHomeomorphOn hσA
  have hC'R : σ '' C ⊆ R := image_subset_iff.mpr (hσ.bijOn.mapsTo.mono_left hCD)
  have hdis : Disjoint (interior (σ '' C)) (σ '' A) := by
    apply disjoint_left.mpr
    intro x hx
    rintro ⟨y, hy, hyx⟩
    obtain ⟨z, hz, hzx⟩ := interior_subset hx
    have hzy := hσ.bijOn.injOn (hCD hz) (hAD hy) (hzx.trans hyx.symm)
    have hyC : y ∈ C := hzy ▸ hz
    have hybd := hCA ⟨hyC, hy⟩
    have hxfront : x ∈ frontier (σ '' C) := by
      rw [← (hc.trans hσC).image_stdSimplexBoundary, image_comp]
      exact ⟨y, hybd, hyx⟩
    exact hxfront.2 hx
  have hcut := isCrosscut_image_of_disk_arc hJ hσ hσrim hrimD hγ hAD hends
  rw [← frontier_closure_inside_of_isPLSphere_one hJ] at hcut
  obtain ⟨F, B, hF, hB, hFR, hFC, hfrontF, hFB, havoid⟩ :=
    DifferentialGeometry.Topology.PiecewiseLinear.exists_crosscut_disk_with_cap_contact
      hR hC' hC'R hA' hcut hdis
  have hBR : B ⊆ R := hFB ▸ (inter_subset_left.trans hFR)
  let τ := Function.invFunOn σ D
  have hτ : IsPLHomeomorphOn τ R D := hσ.symm
  have hτF := hτ.restrict hF.isPolyhedron hFR
  have hτB := hτ.restrict hB.isPolyhedron hBR
  have hτimage (S : Set E) (hSD : S ⊆ D) : τ '' (σ '' S) = S := by
    rw [← image_comp]
    exact (show EqOn (τ ∘ σ) id S from fun _ hx =>
      hσ.bijOn.invOn_invFunOn.1 (hSD hx)).image_eq.trans (image_id S)
  have hτrim : τ '' frontier R = r '' stdSimplexBoundary 2 := by
    rw [frontier_closure_inside_of_isPLSphere_one hJ, ← hσrim]
    exact hτimage _ hrimD
  have hA'R : σ '' A ⊆ R := image_subset_iff.mpr (hσ.bijOn.mapsTo.mono_left hAD)
  obtain ⟨q, hq⟩ := hF
  refine ⟨τ '' F, τ '' B, τ ∘ q, hq.trans hτF, hB.of_isPLHomeomorphOn hτB,
    image_subset_iff.mpr (hτ.bijOn.mapsTo.mono_left hFR), ?_, ?_, ?_, ?_⟩
  · rw [← hτimage C hCD, ← hτ.bijOn.injOn.image_inter hFR hC'R, hFC,
      hτ.bijOn.injOn.image_inter hA'R hC'R, hτimage A hAD]
  · rw [image_comp, hq.image_stdSimplexBoundary, hfrontF, image_union, hτimage A hAD]
  · rw [← hτrim, ← hτ.bijOn.injOn.image_inter hFR hR.isPolyhedron.isClosed.frontier_subset,
      hFB]
  · intro Z hZ hZD hZA hZC
    have hσZ : IsPreconnected (σ '' Z) :=
      hZ.image _ (hσ.isPiecewiseAffineOn.continuousOn.mono hZD)
    have hσZD : σ '' Z ⊆ R := image_subset_iff.mpr (hσ.bijOn.mapsTo.mono_left hZD)
    have hσZA : Disjoint (σ '' Z) (σ '' A) := by
      apply disjoint_left.mpr
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
      have heq := hσ.bijOn.injOn (hAD hy) (hZD hx) hyx
      exact disjoint_left.mp hZA hx (heq ▸ hy)
    have hσZC : ((σ '' Z) ∩ (σ '' C)).Nonempty := by
      obtain ⟨x, hxZ, hxC⟩ := hZC
      exact ⟨σ x, mem_image_of_mem _ hxZ, mem_image_of_mem _ hxC⟩
    have hdis := havoid (σ '' Z) hσZ hσZD hσZA hσZC
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxZ
    exact disjoint_left.mp hdis hx
      ⟨τ x, hxZ, hσ.bijOn.invOn_invFunOn.2 (hFR hx)⟩

theorem exists_lateral_disk_of_crosscut
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P) {a b : ℝ} (hab : a < b)
    {A : Set (E × ℝ)} {γ : ℝ → E × ℝ} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hAside : A ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)
    (hends : A ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = {γ 0, γ 1}) :
    ∃ (F B : Set (E × ℝ)) (q : (Fin 3 → ℝ) → E × ℝ),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) F ∧ IsPLBall 1 B ∧
      F ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b ∧
      q '' stdSimplexBoundary 2 = A ∪ B ∧
      F ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = B ∧
      F ∩ (P ×ˢ ({a} : Set ℝ)) = A ∩ (P ×ˢ ({a} : Set ℝ)) ∧
      ∀ Z : Set (E × ℝ), IsPreconnected Z →
        Z ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b → Disjoint Z A →
        (Z ∩ (P ×ˢ ({a} : Set ℝ))).Nonempty → Disjoint F Z := by
  classical
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKP.symm ▸ hP
  have hrK : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) K.space := hKP.symm ▸ hr
  have hJ : (boundaryComplex 2 K).space = r '' stdSimplexBoundary 2 :=
    (hr.image_stdSimplexBoundary_eq_boundaryComplex K hKP).symm
  have hD := isPLBall_prism_bottom_union_side K hK hab
  rw [hKP, hJ] at hD
  obtain ⟨d, hd⟩ := hD
  have hrim : d '' stdSimplexBoundary 2 = (r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ) := by
    apply IsPLHomeomorphOn.capped_prism_boundary K hK hrK hab
    rwa [hKP]
  let c : (Fin 3 → ℝ) → E × ℝ := fun z => (r z, a)
  have hc : IsPLHomeomorphOn c (stdSimplex ℝ (Fin 3)) (P ×ˢ ({a} : Set ℝ)) :=
    hr.trans (hP.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hAD : A ⊆ P ×ˢ ({a} : Set ℝ) ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b :=
    hAside.trans subset_union_right
  have hCA : (P ×ˢ ({a} : Set ℝ)) ∩ A ⊆ c '' stdSimplexBoundary 2 := by
    intro z hz
    obtain ⟨w, hw, hwr⟩ := (hAside hz.2).1
    exact ⟨w, hw, Prod.ext hwr hz.1.2.symm⟩
  obtain ⟨F, B, q, hq, hB, hFD, hFC, hqbd, hFB, havoid⟩ :=
    hd.exists_crosscut_disk_with_cap_contact hc subset_union_left hγ hAD
      (hrim.symm ▸ hends) hCA
  refine ⟨F, B, q, hq, hB, ?_, hqbd, hrim ▸ hFB, hFC, ?_⟩
  · intro z hz
    rcases hFD hz with hzbase | hzside
    · exact hAside (hFC.subset ⟨hz, hzbase⟩).1
    · exact hzside
  · intro Z hZ hZside hZA hZC
    exact havoid Z hZ (hZside.trans subset_union_right) hZA hZC

theorem exists_lateral_disk_between_spanning_arcs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P A : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P)
    {T₀ T₁ : Set (E × ℝ)} {α β : ℝ → E × ℝ} {δ : ℝ → E}
    {a b : ℝ} {x y : E} (hab : a < b)
    (hα : IsPLHomeomorphOn α (Icc 0 1) T₀)
    (hβ : IsPLHomeomorphOn β (Icc 0 1) T₁)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) A)
    (hα₀ : α 0 = (x, a)) (hα₁ : α 1 = (x, b))
    (hβ₀ : β 0 = (y, a)) (hβ₁ : β 1 = (y, b))
    (hδ₀ : δ 0 = x) (hδ₁ : δ 1 = y)
    (hT₀ : T₀ ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)
    (hT₁ : T₁ ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)
    (hAP : A ⊆ r '' stdSimplexBoundary 2)
    (hT₀a : T₀ ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({a} : Set ℝ)) = {(x, a)})
    (hT₀b : T₀ ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = {(x, b)})
    (hT₁a : T₁ ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({a} : Set ℝ)) = {(y, a)})
    (hT₁b : T₁ ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = {(y, b)})
    (hdis : Disjoint T₀ T₁) :
    let U := (T₀ ∪ (A ×ˢ ({a} : Set ℝ))) ∪ T₁
    ∃ (F B : Set (E × ℝ)) (q : (Fin 3 → ℝ) → E × ℝ),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) F ∧ IsPLBall 1 B ∧
      F ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b ∧
      q '' stdSimplexBoundary 2 = U ∪ B ∧
      F ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = B ∧
      F ∩ (P ×ˢ ({a} : Set ℝ)) = A ×ˢ ({a} : Set ℝ) ∧
      U ∩ B = {(x, b), (y, b)} ∧
      ∀ Z : Set (E × ℝ), IsPreconnected Z →
        Z ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b → Disjoint Z U →
        (Z ∩ (P ×ˢ ({a} : Set ℝ))).Nonempty → Disjoint F Z := by
  obtain ⟨γ, hγ, hγ₀, hγ₁, hU, hUb, hUa⟩ :=
    exists_spanning_pair_returning_arc hab hα hβ hδ hα₀ hα₁ hβ₀ hβ₁ hδ₀ hδ₁
      hT₀ hT₁ hAP hT₀a hT₀b hT₁a hT₁b hdis
  have hends : ((T₀ ∪ (A ×ˢ ({a} : Set ℝ))) ∪ T₁) ∩
      ((r '' stdSimplexBoundary 2) ×ˢ ({b} : Set ℝ)) = {γ 0, γ 1} := by
    rw [hγ₀, hγ₁]
    exact hUb
  obtain ⟨F, B, q, hq, hB, hFside, hqbd, hFb, hFa, havoid⟩ :=
    exists_lateral_disk_of_crosscut hr hab hγ hU hends
  have hrP : r '' stdSimplexBoundary 2 ⊆ P :=
    (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hUa' : ((T₀ ∪ (A ×ˢ ({a} : Set ℝ))) ∪ T₁) ∩ (P ×ˢ ({a} : Set ℝ)) =
      A ×ˢ ({a} : Set ℝ) := by
    apply Subset.antisymm
    · intro z hz
      exact hUa.subset ⟨hz.1, (hU hz.1).1, hz.2.2⟩
    · intro z hz
      exact ⟨(hUa.symm.subset hz).1, hrP (hAP hz.1), hz.2⟩
  have hUF : (T₀ ∪ (A ×ˢ ({a} : Set ℝ))) ∪ T₁ ⊆ F :=
    (subset_union_left.trans hqbd.symm.subset).trans
      ((image_mono (fun _ hx => hx.1)).trans hq.image_eq.subset)
  refine ⟨F, B, q, hq, hB, hFside, hqbd, hFb, hFa.trans hUa', ?_, havoid⟩
  rw [← hUb, ← hFb, ← inter_assoc, inter_eq_left.mpr hUF]

end DifferentialGeometry.Topology.PiecewiseLinear
