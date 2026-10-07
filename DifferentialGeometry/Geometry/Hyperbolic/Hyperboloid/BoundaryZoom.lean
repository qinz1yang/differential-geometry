import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryNormalization
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryPlane
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundarySimilarity
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryTranslation
import DifferentialGeometry.Analysis.Calculus.LineDeriv

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "H3" => Hyperboloid E3
local notation "S2" => Metric.sphere (0 : E3) 1

private def homothetyIsometry (z : ℂ) (s : ℝ) (hs : 0 < s) : H3 ≃ᵢ H3 :=
  ((boundaryTranslation (-z)).trans (boundarySimilarity (s : ℂ) (Complex.ofReal_ne_zero.mpr hs.ne'))).trans
    (boundaryTranslation z)

private theorem homothetyIsometry_north (z : ℂ) (s : ℝ) (hs : 0 < s) :
    boundaryHomeomorph (homothetyIsometry z s hs) sphereNorthPole = sphereNorthPole := by
  simp only [homothetyIsometry, boundaryHomeomorph_trans, Homeomorph.trans_apply,
    boundaryHomeomorph_boundaryTranslation_northPole, boundaryHomeomorph_boundarySimilarity_northPole]

private theorem homothetyIsometry_chart (z : ℂ) (s : ℝ) (hs : 0 < s) (w : ℂ) :
    boundaryHomeomorph (homothetyIsometry z s hs) (stereographicComplex.symm w).val =
      (stereographicComplex.symm (z + (s : ℂ) * (w - z))).val := by
  simp only [homothetyIsometry, boundaryHomeomorph_trans, Homeomorph.trans_apply,
    boundaryHomeomorph_boundaryTranslation_stereographicComplex_symm,
    boundaryHomeomorph_boundarySimilarity_stereographicComplex_symm, sub_eq_add_neg, add_comm]

private theorem similarity_origin_dist (a : ℂ) (ha : a ≠ 0) :
    dist (origin : H3) (boundarySimilarity a ha origin) = Real.arcosh ((‖a‖ + ‖a‖⁻¹) / 2) := by
  have hc := congrArg Prod.fst (boundarySimilarity_coordinates a ha (origin : H3))
  simp only [origin_time, origin_space, PiLp.zero_apply, mul_one, mul_zero, add_zero] at hc
  rw [dist_eq_arcosh, origin_time, origin_space, one_mul, inner_zero_left, sub_zero, hc]

private theorem exists_eventually_similarity_origin_bound
    (D : ℝ → ℂ) (d : ℂ) (hd : d ≠ 0)
    (hD : Filter.Tendsto D Filter.atTop (𝓝 d)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ s : ℝ in Filter.atTop, ∀ hs : D s ≠ 0,
      dist (origin : H3) (boundarySimilarity (D s) hs origin) ≤ R := by
  let T := (‖d‖ + ‖d‖⁻¹) / 2 + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have ht : Filter.Tendsto (fun s => (‖D s‖ + ‖D s‖⁻¹) / 2) Filter.atTop
      (𝓝 ((‖d‖ + ‖d‖⁻¹) / 2)) :=
    (hD.norm.add (hD.norm.inv₀ (norm_ne_zero_iff.mpr hd))).div_const 2
  refine ⟨max 0 (Real.arcosh T), le_max_left _ _, ?_⟩
  filter_upwards [ht.eventually (gt_mem_nhds (lt_add_one _))] with s hs
  intro hne
  rw [similarity_origin_dist]
  exact ((Real.arcosh_le_arcosh (by positivity) hT).mpr hs.le).trans (le_max_right _ _)

private theorem prepost_distortion (f : C(H3, H3)) (A B : H3 ≃ᵢ H3) (L C : ℝ)
    (hf : ∀ x y : H3, L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ L * dist x y + C) (x y : H3) :
    L⁻¹ * dist x y - C ≤ dist (A (f (B x))) (A (f (B y))) ∧
      dist (A (f (B x))) (A (f (B y))) ≤ L * dist x y + C := by
  simpa only [A.dist_eq, B.dist_eq] using hf (B x) (B y)

private theorem boundaryMap_prepost (f : C(H3, H3)) (A B : H3 ≃ᵢ H3)
    (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hf : ∀ x y : H3, L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ L * dist x y + C) (ξ : S2) :
    boundaryMap ((A : C(H3, H3)).comp (f.comp (B : C(H3, H3))))
      ⟨L, C, hL, hC, prepost_distortion f A B L C hf⟩ ξ =
      boundaryHomeomorph A (boundaryMap f ⟨L, C, hL, hC, hf⟩ (boundaryHomeomorph B ξ)) := by
  have hB : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist (B x) (B y) ∧ dist (B x) (B y) ≤ L * dist x y + C := by
    refine ⟨1, 0, le_rfl, le_rfl, fun x y => ?_⟩
    simp only [B.dist_eq, inv_one, one_mul, sub_zero, add_zero, le_refl, and_self]
  have hA : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist (A x) (A y) ∧ dist (A x) (A y) ≤ L * dist x y + C := by
    refine ⟨1, 0, le_rfl, le_rfl, fun x y => ?_⟩
    simp only [A.dist_eq, inv_one, one_mul, sub_zero, add_zero, le_refl, and_self]
  have hfB : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist ((f.comp (B : C(H3, H3))) x) ((f.comp (B : C(H3, H3))) y) ∧
        dist ((f.comp (B : C(H3, H3))) x) ((f.comp (B : C(H3, H3))) y) ≤ L * dist x y + C := by
    refine ⟨L, C, hL, hC, fun x y => ?_⟩
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_apply, B.dist_eq] using hf (B x) (B y)
  rw [boundaryMap_comp (f.comp (B : C(H3, H3))) (A : C(H3, H3)) hfB hA,
    boundaryMap_comp (B : C(H3, H3)) f hB ⟨L, C, hL, hC, hf⟩]
  simp only [ContinuousMap.comp_apply, boundaryMap_isometryEquiv, ContinuousMap.coe_apply]

private def chartTriple (z : ℂ) : Fin 3 → S2 :=
  ![sphereNorthPole, (stereographicComplex.symm z).val, (stereographicComplex.symm (z + 1)).val]

private theorem chartTriple_injective (z : ℂ) : Function.Injective (chartTriple z) := by
  intro i j h
  have hz := (stereographicComplex.symm z).property
  have ho := (stereographicComplex.symm (z + 1)).property
  have hzo : (stereographicComplex.symm z).val ≠ (stereographicComplex.symm (z + 1)).val := by
    intro he
    have he' := stereographicComplex.symm.injective (Subtype.ext he)
    have he'' : (0 : ℂ) = 1 := add_left_cancel ((add_zero z).trans he')
    exact zero_ne_one he''
  fin_cases i <;> fin_cases j <;> simp_all [chartTriple]

variable (f g : C(H3, H3))
  (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
    L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
  (hg : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
    L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ L * dist x y + C)
  (hgf : ∃ C : ℝ, ∀ x : H3, dist (g (f x)) x ≤ C)
  (hfg : ∃ C : ℝ, ∀ x : H3, dist (f (g x)) x ≤ C)
  (hnorth : boundaryMap f hf sphereNorthPole = sphereNorthPole)

theorem exists_eventually_origin_bound_homothety_conjugate (z : ℂ)
    (hne : lineDeriv ℝ (boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth) z (1 : ℂ) ≠ 0) :
    let h := boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth
    let a (s : ℝ) (hs : 0 < s) : H3 ≃ᵢ H3 :=
      ((boundaryTranslation (-(h z))).trans
        (boundarySimilarity (s : ℂ) (Complex.ofReal_ne_zero.mpr hs.ne'))).trans
        (boundaryTranslation (h z))
    let b (s : ℝ) (hs : 0 < s) : H3 ≃ᵢ H3 :=
      ((boundaryTranslation (-z)).trans
        (boundarySimilarity ((s⁻¹ : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (inv_ne_zero hs.ne')))).trans
        (boundaryTranslation z)
    ∃ R s₀ : ℝ, 0 ≤ R ∧ ∃ hs₀ : 0 < s₀, ∀ (s : ℝ) (hss : s₀ ≤ s),
      dist (origin : H3)
        (((a s (hs₀.trans_le hss) : C(H3, H3)).comp
          (f.comp (b s (hs₀.trans_le hss) : C(H3, H3)))) origin) ≤ R := by
  intro h a b
  have hdiff : LineDifferentiableAt ℝ (h : ℂ → ℂ) z (1 : ℂ) := by
    by_contra hn
    exact hne (lineDeriv_zero_of_not_lineDifferentiableAt hn)
  let d := lineDeriv ℝ h z (1 : ℂ)
  let D (s : ℝ) := (s : ℂ) * (h (z + ((s⁻¹ : ℝ) : ℂ)) - h z)
  have hD : Filter.Tendsto D Filter.atTop (𝓝 d) := by
    have hv : HasLineDerivAt ℝ (h : ℂ → ℂ) d z (1 : ℂ) := hdiff.hasLineDerivAt
    have hh := (hv.tendsto_homothety_atTop 1).sub_const (h z)
    simpa only [one_smul, Complex.real_smul, mul_one, add_sub_cancel_left] using hh
  obtain ⟨R₁, hR₁, hRbound⟩ := exists_eventually_similarity_origin_bound D d hne hD
  have hDne : ∀ᶠ s : ℝ in Filter.atTop, D s ≠ 0 := hD.eventually (eventually_ne_nhds hne)
  obtain ⟨s₁, hs₁⟩ := Filter.eventually_atTop.mp (hRbound.and hDne)
  obtain ⟨L, C, hL, hC, hfxy⟩ := hf
  obtain ⟨B₀, hB₀, hnormalized⟩ := exists_origin_displacement_bound_of_boundaryMap_fixed_triple
    L C hL hC (chartTriple z) (chartTriple_injective z)
  have hchart (w : ℂ) : (stereographicComplex.symm (h w)).val =
      boundaryMap f ⟨L, C, hL, hC, hfxy⟩ (stereographicComplex.symm w).val :=
    stereographicComplex_symm_boundaryPlaneHomeomorph f g ⟨L, C, hL, hC, hfxy⟩ hg hgf hfg hnorth w
  let R := B₀ + dist (origin : H3) (boundaryTranslation (h z) origin) + R₁ +
    dist (origin : H3) (boundaryTranslation (-z) origin)
  have hs₀ : 0 < max s₁ 1 := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨R, max s₁ 1, by dsimp [R]; positivity, hs₀, ?_⟩
  intro s hss
  let hs : 0 < s := hs₀.trans_le hss
  have hDs : D s ≠ 0 := (hs₁ s ((le_max_left _ _).trans hss)).2
  have hsim : dist (origin : H3) (boundarySimilarity (D s) hDs origin) ≤ R₁ :=
    (hs₁ s ((le_max_left _ _).trans hss)).1 hDs
  let E := ((boundaryTranslation (-z)).trans (boundarySimilarity (D s) hDs)).trans
    (boundaryTranslation (h z))
  let N : C(H3, H3) := ((a s hs).trans E.symm : C(H3, H3)).comp (f.comp (b s hs : C(H3, H3)))
  have hNxy (x y : H3) : L⁻¹ * dist x y - C ≤ dist (N x) (N y) ∧
      dist (N x) (N y) ≤ L * dist x y + C :=
    prepost_distortion f ((a s hs).trans E.symm) (b s hs) L C hfxy x y
  have hNboundary (ξ : S2) : boundaryMap N ⟨L, C, hL, hC, hNxy⟩ ξ =
      (boundaryHomeomorph E).symm
        (boundaryHomeomorph (a s hs) (boundaryMap f ⟨L, C, hL, hC, hfxy⟩
          (boundaryHomeomorph (b s hs) ξ))) := by
    change boundaryMap (((a s hs).trans E.symm : C(H3, H3)).comp
      (f.comp (b s hs : C(H3, H3)))) _ ξ = _
    rw [boundaryMap_prepost f ((a s hs).trans E.symm) (b s hs) L C hL hC hfxy,
      boundaryHomeomorph_trans, Homeomorph.trans_apply, ← boundaryHomeomorph_symm]
  have hEnorth : boundaryHomeomorph E sphereNorthPole = sphereNorthPole := by
    simp only [E, boundaryHomeomorph_trans, Homeomorph.trans_apply,
      boundaryHomeomorph_boundaryTranslation_northPole, boundaryHomeomorph_boundarySimilarity_northPole]
  have hEchart (w : ℂ) : boundaryHomeomorph E (stereographicComplex.symm w).val =
      (stereographicComplex.symm (h z + D s * (w - z))).val := by
    simp only [E, boundaryHomeomorph_trans, Homeomorph.trans_apply,
      boundaryHomeomorph_boundaryTranslation_stereographicComplex_symm,
      boundaryHomeomorph_boundarySimilarity_stereographicComplex_symm, sub_eq_add_neg]
    exact congrArg (fun u : ℂ => (stereographicComplex.symm u).val) (add_comm _ _)
  have hzoomchart (w : ℂ) : boundaryHomeomorph (a s hs)
      (boundaryMap f ⟨L, C, hL, hC, hfxy⟩ (boundaryHomeomorph (b s hs) (stereographicComplex.symm w).val)) =
      (stereographicComplex.symm
        (h z + (s : ℂ) * (h (z + ((s⁻¹ : ℝ) : ℂ) * (w - z)) - h z))).val := by
    change boundaryHomeomorph (homothetyIsometry (h z) s hs)
      (boundaryMap f ⟨L, C, hL, hC, hfxy⟩ (boundaryHomeomorph
        (homothetyIsometry z s⁻¹ (inv_pos.mpr hs)) (stereographicComplex.symm w).val)) = _
    rw [homothetyIsometry_chart, ← hchart, homothetyIsometry_chart]
  have hfix (j : Fin 3) : boundaryMap N ⟨L, C, hL, hC, hNxy⟩ (chartTriple z j) = chartTriple z j := by
    rw [hNboundary]
    apply (boundaryHomeomorph E).injective
    rw [(boundaryHomeomorph E).apply_symm_apply]
    fin_cases j
    · change boundaryHomeomorph (homothetyIsometry (h z) s hs)
        (boundaryMap f ⟨L, C, hL, hC, hfxy⟩ (boundaryHomeomorph
          (homothetyIsometry z s⁻¹ (inv_pos.mpr hs)) sphereNorthPole)) = boundaryHomeomorph E sphereNorthPole
      rw [homothetyIsometry_north, hnorth, homothetyIsometry_north, hEnorth]
    · change boundaryHomeomorph (a s hs)
        (boundaryMap f ⟨L, C, hL, hC, hfxy⟩ (boundaryHomeomorph (b s hs)
          (stereographicComplex.symm z).val)) = boundaryHomeomorph E (stereographicComplex.symm z).val
      rw [hzoomchart, hEchart]
      simp only [sub_self, mul_zero, add_zero]
    · change boundaryHomeomorph (a s hs)
        (boundaryMap f ⟨L, C, hL, hC, hfxy⟩ (boundaryHomeomorph (b s hs)
          (stereographicComplex.symm (z + 1)).val)) =
        boundaryHomeomorph E (stereographicComplex.symm (z + 1)).val
      rw [hzoomchart, hEchart]
      simp only [add_sub_cancel_left, mul_one]
      rfl
  have hNbound : dist (origin : H3) (N origin) ≤ B₀ := hnormalized N hNxy hfix
  have hEbound : dist (origin : H3) (E origin) ≤
      dist (origin : H3) (boundaryTranslation (h z) origin) + R₁ +
        dist (origin : H3) (boundaryTranslation (-z) origin) := by
    have ht := dist_triangle (origin : H3) (boundaryTranslation (h z) origin) (E origin)
    have hu := dist_triangle (origin : H3) (boundarySimilarity (D s) hDs origin)
      (boundarySimilarity (D s) hDs (boundaryTranslation (-z) origin))
    change dist (origin : H3) (E origin) ≤
      dist (origin : H3) (boundaryTranslation (h z) origin) +
      dist (boundaryTranslation (h z) origin)
        (boundaryTranslation (h z) (boundarySimilarity (D s) hDs (boundaryTranslation (-z) origin))) at ht
    rw [(boundaryTranslation (h z)).dist_eq] at ht
    rw [(boundarySimilarity (D s) hDs).dist_eq] at hu
    linarith only [ht, hu, hsim]
  have hEN : E (N origin) = a s hs (f (b s hs origin)) := E.apply_symm_apply _
  change dist (origin : H3) (a s hs (f (b s hs origin))) ≤ R
  rw [← hEN]
  have ht := dist_triangle (origin : H3) (E origin) (E (N origin))
  rw [E.dist_eq] at ht
  dsimp only [R]
  linarith only [ht, hNbound, hEbound]

end DifferentialGeometry.Hyperboloid
