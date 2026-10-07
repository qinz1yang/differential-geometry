import DifferentialGeometry.Geometry.Affine.PlaneIsometry
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryPlaneMetric
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryTransitivity
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryStabilizer
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Horosphere
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.HorosphereAction
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.HorosphereDistance
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.HorosphericalCoordinates
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Proper
import DifferentialGeometry.Geometry.Metric.Isometry.ProperDiscontinuity

noncomputable section

namespace DifferentialGeometry.Hyperboloid

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private def northPolePlaneIsometry (e : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
    (hn : boundaryHomeomorph e sphereNorthPole = sphereNorthPole)
    (hs : (lorentzExtension e (1, (sphereNorthPole : E₃))).1 = 1) : ℂ ≃ᵢ ℂ := by
  have hnonpole (ξ : Metric.sphere (0 : E₃) 1) :
      ξ ≠ sphereNorthPole ↔ boundaryHomeomorph e ξ ≠ sphereNorthPole := by
    constructor
    · intro hξ hp
      exact hξ ((boundaryHomeomorph e).injective (hp.trans hn.symm))
    · intro hξ hp
      exact hξ (hp ▸ hn)
  let H : ℂ ≃ₜ ℂ := stereographicComplex.symm.trans
    (((boundaryHomeomorph e).subtype hnonpole).trans stereographicComplex)
  refine { toEquiv := H.toEquiv, isometry_toFun := Isometry.of_dist_eq ?_ }
  intro z w
  have hm := dist_stereographicComplex_boundaryHomeomorph e hn
    (stereographicComplex.symm z) (stereographicComplex.symm w)
  have hH (v : ℂ) : H v = stereographicComplex
      ⟨boundaryHomeomorph e (stereographicComplex.symm v).val,
        (hnonpole _).mp (stereographicComplex.symm v).property⟩ := by
    change stereographicComplex (((boundaryHomeomorph e).subtype hnonpole)
      (stereographicComplex.symm v)) = _
    apply congrArg stereographicComplex
    apply Subtype.ext
    rfl
  change dist (H z) (H w) = dist z w
  rw [hH z, hH w]
  simpa only [hs, one_mul, stereographicComplex.apply_symm_apply] using hm

private theorem northPolePlaneIsometry_apply (e : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
    (hn : boundaryHomeomorph e sphereNorthPole = sphereNorthPole)
    (hs : (lorentzExtension e (1, (sphereNorthPole : E₃))).1 = 1) (z : ℂ) :
    northPolePlaneIsometry e hn hs z = stereographicComplex
      ⟨boundaryHomeomorph e (stereographicComplex.symm z).val, by
        intro hp
        exact (stereographicComplex.symm z).property
          ((boundaryHomeomorph e).injective (hp.trans hn.symm))⟩ := by
  apply congrArg stereographicComplex
  apply Subtype.ext
  rfl

private theorem northPolePlaneIsometry_action (e : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
    (hn : boundaryHomeomorph e sphereNorthPole = sphereNorthPole)
    (hs : (lorentzExtension e (1, (sphereNorthPole : E₃))).1 = 1)
    (h : ℝ) (hh : 0 < h) (z : ℂ) :
    e ((northPoleHorosphereHomeomorph h hh).symm z).val =
      ((northPoleHorosphereHomeomorph h hh).symm (northPolePlaneIsometry e hn hs z)).val := by
  have ha := isometryEquiv_northPoleHorosphereHomeomorph_symm e hn h hh z
  dsimp only at ha
  rw [northPolePlaneIsometry_apply]
  have he (k : ℝ) (hk : 0 < k) (heq : k = h) (w : ℂ) :
      ((northPoleHorosphereHomeomorph k hk).symm w).val =
        ((northPoleHorosphereHomeomorph h hh).symm w).val := by
    subst k
    rfl
  exact ha.trans (he _ _ (by rw [hs, div_one]) _)

private theorem horospherePoint_injective (h : ℝ) (hh : 0 < h) :
    Function.Injective (fun z : ℂ => ((northPoleHorosphereHomeomorph h hh).symm z).val) :=
  Subtype.val_injective.comp (northPoleHorosphereHomeomorph h hh).symm.injective

private theorem northPolePlaneIsometry_no_fixed_point
    (e : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
    (hn : boundaryHomeomorph e sphereNorthPole = sphereNorthPole)
    (hs : (lorentzExtension e (1, (sphereNorthPole : E₃))).1 = 1)
    (hf : ∀ x, e x ≠ x) (z : ℂ) : northPolePlaneIsometry e hn hs z ≠ z := by
  intro hz
  apply hf (((northPoleHorosphereHomeomorph 1 zero_lt_one).symm z).val)
  rw [northPolePlaneIsometry_action e hn hs, hz]

private theorem horospherePoint_one_zero :
    ((northPoleHorosphereHomeomorph 1 zero_lt_one).symm 0).val =
      (origin : Hyperboloid E₃) := by
  apply Hyperboloid.ext
  have hs := congrArg Prod.snd (northPoleHorosphereHomeomorph_symm_coordinates 1 zero_lt_one 0)
  dsimp only at hs
  rw [hs, origin_space]
  ext i
  fin_cases i <;> norm_num

private theorem northPole_plane_displacement_sq_lower
    (Γ : Subgroup (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃))
    (hfree : ∀ γ : Γ, γ ≠ 1 → ∀ x, (γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) x ≠ x)
    (hn : ∀ γ : Γ, boundaryHomeomorph (γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
      sphereNorthPole = sphereNorthPole)
    (hs : ∀ γ : Γ, (lorentzExtension (γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
      (1, (sphereNorthPole : E₃))).1 = 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ γ : Γ, γ ≠ 1 → δ ≤ dist
      ((γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) origin) origin)
    (γ : Γ) (hγ : γ ≠ 1) (z : ℂ) :
    2 * (Real.cosh δ - 1) ≤ dist (northPolePlaneIsometry γ (hn γ) (hs γ) z) z ^ 2 := by
  let H := northPolePlaneIsometry γ (hn γ) (hs γ)
  let P : ℂ → Hyperboloid E₃ := fun w =>
    ((northPoleHorosphereHomeomorph 1 zero_lt_one).symm w).val
  have hH : ∀ w, H w ≠ w := northPolePlaneIsometry_no_fixed_point γ (hn γ) (hs γ) (hfree γ hγ)
  have hsq : γ * γ ≠ 1 := by
    intro he
    have hp : (γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
        ((γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) (P 0)) = P 0 := by
      change ((γ * γ : Γ) : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) (P 0) = P 0
      rw [he]
      rfl
    have ha (w : ℂ) : (γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) (P w) = P (H w) :=
      northPolePlaneIsometry_action γ (hn γ) (hs γ) 1 zero_lt_one w
    rw [ha, ha] at hp
    exact H.apply_apply_ne_of_no_fixed_point hH 0 (horospherePoint_injective 1 zero_lt_one hp)
  have horigin : (origin : Hyperboloid E₃) = P 0 := horospherePoint_one_zero.symm
  have ha (w : ℂ) : (γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) (P w) = P (H w) :=
    northPolePlaneIsometry_action γ (hn γ) (hs γ) 1 zero_lt_one w
  have hgap' := hgap (γ * γ) hsq
  have hcosh : Real.cosh δ ≤ Real.cosh (dist
      (((γ * γ : Γ) : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) origin) origin) :=
    Real.cosh_le_cosh.mpr (by simpa only [abs_of_pos hδ, abs_of_nonneg dist_nonneg] using hgap')
  rw [horigin] at hcosh
  change Real.cosh δ ≤ Real.cosh (dist
    ((γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) ((γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) (P 0))) (P 0)) at hcosh
  rw [ha, ha] at hcosh
  have hformula := cosh_dist_northPoleHorosphereHomeomorph_symm
    1 1 zero_lt_one zero_lt_one (H (H 0)) 0
  change Real.cosh (dist (P (H (H 0))) (P 0)) = _ at hformula
  rw [hformula] at hcosh
  have htriangle : dist (H (H z)) z ≤ 2 * dist (H z) z := by
    calc
      dist (H (H z)) z ≤ dist (H (H z)) (H z) + dist (H z) z := dist_triangle _ _ _
      _ = 2 * dist (H z) z := by rw [H.dist_eq]; ring
  rw [H.apply_apply_eq_add_of_no_fixed_point hH z] at htriangle
  have hshift : dist (z + H (H 0)) z = dist (H (H 0)) 0 := by simp [dist_eq_norm]
  rw [hshift] at htriangle
  have hsqdist : dist (H (H 0)) 0 ^ 2 ≤ 4 * dist (H z) z ^ 2 := by
    nlinarith [dist_nonneg (x := H (H 0)) (y := 0), dist_nonneg (x := H z) (y := z)]
  norm_num only at hcosh
  nlinarith

private theorem exists_bound_north_height_of_small_displacement
    (Γ : Subgroup (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)) [DiscreteTopology Γ]
    (hfree : ∀ γ : Γ, γ ≠ 1 → ∀ x, (γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) x ≠ x)
    (hn : ∀ γ : Γ, boundaryHomeomorph (γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
      sphereNorthPole = sphereNorthPole)
    (hs : ∀ γ : Γ, (lorentzExtension (γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
      (1, (sphereNorthPole : E₃))).1 = 1)
    (ε : ℝ) :
    ∃ C : ℝ, ∀ x : Hyperboloid E₃,
      (∃ γ : Γ, γ ≠ 1 ∧ dist ((γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) x) x < ε) →
      x.time - x.space 0 ≤ C := by
  obtain ⟨δ, hδ, hgap⟩ := IsometryEquiv.exists_pos_le_dist_apply_self Γ origin
    (fun γ hγ => hfree γ hγ origin)
  let A := Real.cosh δ - 1
  have hA : 0 < A := sub_pos.mpr (Real.one_lt_cosh.mpr hδ.ne')
  let C := Real.sqrt (4 * Real.cosh ε / A)
  refine ⟨C, ?_⟩
  intro x hx
  obtain ⟨γ, hγ, hsmall⟩ := hx
  let u := horosphericalDiffeomorph x
  let h := u.val 0
  have hh : 0 < h := u.property
  let z : ℂ := (u.val 1 : ℂ) + (u.val 2 : ℂ) * Complex.I
  have hxP : x = ((northPoleHorosphereHomeomorph h hh).symm z).val := by
    rw [← horosphericalDiffeomorph_symm_apply]
    exact (horosphericalDiffeomorph.symm_apply_apply x).symm
  have hheight : x.time - x.space 0 = h := by
    change x.time - x.space 0 = (horosphericalDiffeomorph x).val 0
    rw [horosphericalDiffeomorph_apply]
    rfl
  let H := northPolePlaneIsometry γ (hn γ) (hs γ)
  have hlower : 2 * A ≤ dist (H z) z ^ 2 :=
    northPole_plane_displacement_sq_lower Γ hfree hn hs δ hδ hgap γ hγ z
  have hformula : Real.cosh (dist ((γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) x) x) =
      1 + h ^ 2 * dist (H z) z ^ 2 / 8 := by
    rw [hxP, northPolePlaneIsometry_action γ (hn γ) (hs γ)]
    rw [cosh_dist_northPoleHorosphereHomeomorph_symm]
    field_simp
    ring
  have hupper : Real.cosh (dist ((γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) x) x) ≤ Real.cosh ε :=
    Real.cosh_le_cosh.mpr (by
      rw [abs_of_nonneg dist_nonneg, abs_of_pos (lt_of_le_of_lt dist_nonneg hsmall)]
      exact hsmall.le)
  have hm := mul_le_mul_of_nonneg_left hlower (sq_nonneg h)
  have hb : h ^ 2 * A ≤ 4 * Real.cosh ε := by
    rw [hformula] at hupper
    nlinarith
  have hratio : h ^ 2 ≤ 4 * Real.cosh ε / A := (le_div_iff₀ hA).mpr hb
  have hCsq : C ^ 2 = 4 * Real.cosh ε / A := Real.sq_sqrt (by positivity)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  rw [hheight]
  nlinarith

local notation "H₃" => Hyperboloid E₃

theorem exists_bound_time_sub_inner_of_small_displacement
    (Γ : Subgroup (H₃ ≃ᵢ H₃)) [DiscreteTopology Γ]
    (hfree : ∀ γ : Γ, γ ≠ 1 → ∀ x : H₃, (γ : H₃ ≃ᵢ H₃) x ≠ x)
    (ξ : Metric.sphere (0 : E₃) 1)
    (hξ : ∀ γ : Γ, boundaryHomeomorph (γ : H₃ ≃ᵢ H₃) ξ = ξ)
    (hscale : ∀ γ : Γ, (lorentzExtension (γ : H₃ ≃ᵢ H₃) (1, (ξ : E₃))).1 = 1)
    (ε : ℝ) :
    ∃ C : ℝ, ∀ x : H₃,
      (∃ γ : Γ, γ ≠ 1 ∧ dist ((γ : H₃ ≃ᵢ H₃) x) x < ε) →
      x.time - inner ℝ x.space (ξ : E₃) ≤ C := by
  obtain ⟨e, he0, heξ⟩ := exists_isometryEquiv_origin_fixed_boundary_eq ξ sphereNorthPole
  have henull0 : lorentzExtension e (1, 0) = (1, 0) := by
    simpa only [origin_time, origin_space, he0] using lorentzExtension_apply e (origin : H₃)
  have hetime (v : ℝ × E₃) : (lorentzExtension e v).1 = v.1 := by
    have hp := (lorentzExtension e).map_app v (1, 0)
    rw [henull0] at hp
    simp only [lorentzForm_apply, inner_zero_left, one_mul, zero_sub] at hp
    linarith only [hp]
  have henull : lorentzExtension e (1, (ξ : E₃)) = (1, (sphereNorthPole : E₃)) := by
    have hp := boundaryHomeomorph_apply_coe e ξ
    rw [heξ, hetime] at hp
    simp only [inv_one, one_smul] at hp
    exact Prod.ext (hetime _) hp.symm
  have heinvnull : lorentzExtension e.symm (1, (sphereNorthPole : E₃)) = (1, (ξ : E₃)) := by
    rw [lorentzExtension_symm, ← henull]
    exact (lorentzExtension e).toLinearEquiv.symm_apply_apply _
  have heinv : boundaryHomeomorph e.symm sphereNorthPole = ξ := by
    rw [← boundaryHomeomorph_symm, ← heξ]
    exact (boundaryHomeomorph e).symm_apply_apply ξ
  let G := H₃ ≃ᵢ H₃
  let a : G ≃* G := MulAut.conj e
  let Γ' : Subgroup G := Γ.map a.toMonoidHom
  let j : Γ ≃* Γ' := a.subgroupMap Γ
  let jh : Γ ≃ₜ Γ' :=
    { toEquiv := j.toEquiv
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (IsTopologicalGroup.continuous_conj e).comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        change Continuous (fun g : Γ' => e⁻¹ * (g : G) * e)
        simpa only [inv_inv, Function.comp_def] using
          (IsTopologicalGroup.continuous_conj e⁻¹).comp continuous_subtype_val }
  let _ : DiscreteTopology Γ' := jh.symm.isEmbedding.discreteTopology
  have hfree' : ∀ γ : Γ', γ ≠ 1 → ∀ x : H₃, (γ : G) x ≠ x := by
    rintro ⟨g, hmem⟩ hne x hx
    obtain ⟨γ, hγ, rfl⟩ := hmem
    have hγne : (⟨γ, hγ⟩ : Γ) ≠ 1 := by
      intro h
      apply hne
      apply Subtype.ext
      have hv := congrArg Subtype.val h
      change γ = 1 at hv
      change a γ = 1
      rw [hv, map_one]
    apply hfree ⟨γ, hγ⟩ hγne (e.symm x)
    apply e.injective
    change e (γ (e.symm x)) = e (e.symm x)
    rw [e.apply_symm_apply]
    exact hx
  have hn' : ∀ γ : Γ', boundaryHomeomorph (γ : G) sphereNorthPole = sphereNorthPole := by
    rintro ⟨g, hmem⟩
    obtain ⟨γ, hγ, rfl⟩ := hmem
    change boundaryHomeomorph (e.symm.trans (γ.trans e)) sphereNorthPole = sphereNorthPole
    simp only [boundaryHomeomorph_trans, Homeomorph.trans_apply]
    rw [heinv, hξ ⟨γ, hγ⟩, heξ]
  have hs' : ∀ γ : Γ', (lorentzExtension (γ : G) (1, (sphereNorthPole : E₃))).1 = 1 := by
    rintro ⟨g, hmem⟩
    obtain ⟨γ, hγ, rfl⟩ := hmem
    have hgnull : lorentzExtension γ (1, (ξ : E₃)) = (1, (ξ : E₃)) := by
      rw [lorentzExtension_sphere_eq_smul_boundaryHomeomorph,
        hξ ⟨γ, hγ⟩, hscale ⟨γ, hγ⟩, one_smul]
    change (lorentzExtension (e.symm.trans (γ.trans e)) (1, (sphereNorthPole : E₃))).1 = 1
    simp only [lorentzExtension_trans]
    change (lorentzExtension e (lorentzExtension γ
      (lorentzExtension e.symm (1, (sphereNorthPole : E₃))))).1 = 1
    rw [heinvnull, hgnull, henull]
  obtain ⟨C, hC⟩ := exists_bound_north_height_of_small_displacement Γ' hfree' hn' hs' ε
  refine ⟨C, ?_⟩
  rintro x ⟨γ, hγ, hγx⟩
  have hjγ : j γ ≠ 1 := by
    intro h
    apply hγ
    apply j.injective
    simpa only [map_one] using h
  have hdisp : dist ((j γ : G) (e x)) (e x) < ε := by
    change dist (e ((γ : G) (e.symm (e x)))) (e x) < ε
    rwa [e.symm_apply_apply, e.dist_eq]
  have hbound := hC (e x) ⟨j γ, hjγ, hdisp⟩
  have hheight := time_sub_inner_boundaryHomeomorph e ξ x
  rw [heξ, hetime, div_one] at hheight
  have heighteq : (e x).time - (e x).space 0 = x.time - inner ℝ x.space (ξ : E₃) := by
    simpa only [sphereNorthPole_coe, EuclideanSpace.inner_single_right,
      starRingEnd_apply, star_trivial, one_mul] using hheight
  rwa [heighteq] at hbound


theorem exists_bound_time_sub_space_zero_of_small_displacement
    (Γ : Subgroup (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)) [DiscreteTopology Γ]
    (hfree : ∀ γ : Γ, γ ≠ 1 → ∀ x, (γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) x ≠ x)
    (hn : ∀ γ : Γ, boundaryHomeomorph (γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
      sphereNorthPole = sphereNorthPole)
    (hs : ∀ γ : Γ, (lorentzExtension (γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
      (1, (sphereNorthPole : E₃))).1 = 1)
    (ε : ℝ) :
    ∃ C : ℝ, ∀ x : Hyperboloid E₃,
      (∃ γ : Γ, γ ≠ 1 ∧ dist ((γ : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) x) x < ε) →
      x.time - x.space 0 ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_time_sub_inner_of_small_displacement
    Γ hfree sphereNorthPole hn hs ε
  refine ⟨C, ?_⟩
  intro x hx
  simpa only [sphereNorthPole_coe, EuclideanSpace.inner_single_right,
    starRingEnd_apply, star_trivial, one_mul] using hC x hx

end DifferentialGeometry.Hyperboloid
