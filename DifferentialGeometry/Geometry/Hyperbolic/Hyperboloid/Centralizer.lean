import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryOrbit
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Geodesic
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Proper
import DifferentialGeometry.Geometry.Metric.Isometry.ProperDiscontinuity
import DifferentialGeometry.Topology.GroupAction.CompactLifting

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem cosh_dist_eq_neg_lorentzForm (x y : Hyperboloid E) :
    Real.cosh (dist x y) = -lorentzForm E (x.time, x.space) (y.time, y.space) := by
  rw [cosh_dist, lorentzForm_apply]
  ring

private theorem exists_geodesicLine_dist_le_of_fixedPoint
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (p : Hyperboloid E)
    (hfp : f p = p) (hf : f ≠ IsometryEquiv.refl (Hyperboloid E)) :
    ∃ (v : ℝ × E) (hv : lorentzForm E v v = 1)
      (ho : lorentzForm E (p.time, p.space) v = 0),
      ∀ (a : Hyperboloid E ≃ᵢ Hyperboloid E),
        (∀ x : Hyperboloid E, f (a x) = a (f x)) →
        ∀ t : ℝ, 0 ≤ t →
          dist p (a p) ≤ dist (geodesicLine p v hv ho t) (a (geodesicLine p v hv ho t)) ∧
          t ≤ dist (geodesicLine p v hv ho t) (a p) := by
  let A := lorentzExtension f
  let P : ℝ × E := (p.time, p.space)
  have hAP : A P = P := by
    dsimp only [A, P]
    rw [lorentzExtension_apply, hfp]
  have hPP : lorentzForm E P P = -1 := by
    dsimp only [P]
    rw [lorentzForm_apply]
    nlinarith [p.time_sq_sub_inner_self]
  obtain ⟨q, hq⟩ : ∃ q : Hyperboloid E, f q ≠ q := by
    by_contra h
    push Not at h
    exact hf (IsometryEquiv.ext h)
  let Y : ℝ × E := (q.time, q.space)
  let D := A Y - Y
  have hD : D ≠ 0 := by
    intro hz
    have he : A Y = Y := sub_eq_zero.mp hz
    apply hq
    apply Hyperboloid.ext
    exact congrArg Prod.snd ((lorentzExtension_apply f q).symm.trans he)
  have hnormal (Z : ℝ × E) (hZ : A Z = Z) : lorentzForm E Z D = 0 := by
    dsimp only [D]
    rw [map_sub]
    have h := A.map_app Y Z
    rw [hZ] at h
    exact sub_eq_zero.mpr h
  have hPD : lorentzForm E P D = 0 := hnormal P hAP
  have hDs : D.2 ≠ 0 := by
    intro hs
    have ht := hPD
    rw [lorentzForm_apply, hs, inner_zero_right, zero_sub] at ht
    have ht' : D.1 = 0 :=
      (mul_eq_zero.mp (neg_eq_zero.mp ht)).resolve_left p.time_pos.ne'
    exact hD (Prod.ext ht' hs)
  have hDD : 0 < lorentzForm E D D := by
    have hbound := norm_snd_sq_le_mul_lorentzForm_self_of_orthogonal hPP.le hPD
    have hpos : 0 < ‖D.2‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hDs)
    by_contra hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg P.1) (le_of_not_gt hn)
    linarith
  let s := Real.sqrt (lorentzForm E D D)
  have hs : 0 < s := Real.sqrt_pos.mpr hDD
  have hs2 : s ^ 2 = lorentzForm E D D := Real.sq_sqrt hDD.le
  let v := s⁻¹ • D
  have hv : lorentzForm E v v = 1 := by
    dsimp only [v]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← hs2]
    field_simp [hs.ne']
  have hn (Z : ℝ × E) (hZ : A Z = Z) : lorentzForm E Z v = 0 := by
    dsimp only [v]
    rw [map_smul, hnormal Z hZ, smul_zero]
  have ho : lorentzForm E P v = 0 := hn P hAP
  refine ⟨v, hv, ho, ?_⟩
  intro a ha t ht
  let L := lorentzExtension a
  have hLi : L (L.symm P) = P := L.toLinearEquiv.apply_symm_apply P
  have hcomm : a.trans f = f.trans a := IsometryEquiv.ext ha
  have hAL (Z : ℝ × E) : A (L Z) = L (A Z) := by
    have h := congrArg lorentzExtension hcomm
    rw [lorentzExtension_trans, lorentzExtension_trans] at h
    exact congrArg (fun C => C Z) h
  have hLP : A (L P) = L P := by rw [hAL, hAP]
  have hLiP : A (L.symm P) = L.symm P := by
    apply L.toLinearEquiv.injective
    calc
      L (A (L.symm P)) = A (L (L.symm P)) := (hAL _).symm
      _ = A P := by rw [hLi]
      _ = P := hAP
      _ = L (L.symm P) := hLi.symm
  have hPLv : lorentzForm E P (L v) = 0 := by
    have h := L.map_app v (L.symm P)
    rw [hLi, hn _ hLiP] at h
    exact h
  have hvLP : lorentzForm E v (L P) = 0 := by
    have hsym : lorentzForm E v (L P) = lorentzForm E (L P) v := by
      simpa using (lorentzForm_isSymm E).eq v (L P)
    exact hsym.trans (hn _ hLP)
  have hP0 : P ≠ 0 := by
    intro h
    exact p.time_pos.ne' (congrArg Prod.fst h)
  have hLv : lorentzForm E (L v) (L v) = 1 := (L.map_app v v).trans hv
  have hvLv : lorentzForm E v (L v) ≤ 1 := by
    have h := lorentzForm_sq_le_of_orthogonal (hPP.le.trans (by norm_num)) hP0 ho hPLv
    rw [hv, hLv, one_mul] at h
    nlinarith
  have hPa : lorentzForm E P (L P) = -Real.cosh (dist p (a p)) := by
    dsimp only [L, P]
    rw [lorentzExtension_apply, cosh_dist, lorentzForm_apply]
    ring
  let c := geodesicLine p v hv ho t
  have hc : (c.time, c.space) = Real.cosh t • P + Real.sinh t • v := rfl
  have hac : ((a c).time, (a c).space) =
      Real.cosh t • L P + Real.sinh t • L v := by
    rw [← lorentzExtension_apply a, hc, map_add, map_smul, map_smul]
  have hdisp : Real.cosh (dist c (a c)) =
      Real.cosh t ^ 2 * Real.cosh (dist p (a p)) -
        Real.sinh t ^ 2 * lorentzForm E v (L v) := by
    rw [cosh_dist_eq_neg_lorentzForm, hc, hac]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hPLv, hvLP, hPa]
    ring
  have horbit : Real.cosh (dist c (a p)) =
      Real.cosh t * Real.cosh (dist p (a p)) := by
    rw [cosh_dist_eq_neg_lorentzForm, hc, ← lorentzExtension_apply a p]
    change -lorentzForm E (Real.cosh t • P + Real.sinh t • v) (L P) = _
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hvLP, hPa]
    ring
  constructor
  · have hcoef : 0 ≤ Real.cosh (dist p (a p)) - lorentzForm E v (L v) :=
      sub_nonneg.mpr (hvLv.trans (Real.one_le_cosh _))
    have hid : Real.cosh t ^ 2 = Real.sinh t ^ 2 + 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq t]
    have hle : Real.cosh (dist p (a p)) ≤ Real.cosh (dist c (a c)) := by
      rw [hdisp, hid]
      nlinarith [mul_nonneg (sq_nonneg (Real.sinh t)) hcoef]
    simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hle
  · have hle : Real.cosh t ≤ Real.cosh (dist c (a p)) := by
      rw [horbit]
      nlinarith [Real.one_le_cosh (dist p (a p)), Real.cosh_pos t]
    simpa only [abs_of_nonneg ht, abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hle

private theorem exists_pos_le_dist_apply
    [FiniteDimensional ℝ E] (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E))
    [DiscreteTopology Γ]
    (hfree : ∀ γ : Γ, γ ≠ 1 → ∀ x : Hyperboloid E,
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E) x ≠ x) (p : Hyperboloid E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : Γ, γ ≠ 1 →
      δ ≤ dist p ((γ : Hyperboloid E ≃ᵢ Hyperboloid E) p) := by
  let _ : IsIsometricSMul Γ (Hyperboloid E) := ⟨fun γ => γ.val.isometry⟩
  obtain ⟨U, hU, hd⟩ := ProperlyDiscontinuousSMul.exists_nhds_disjoint_image Γ p
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ, hδ, ?_⟩
  intro γ hγ
  by_contra hn
  have hpU : p ∈ U := mem_of_mem_nhds hU
  have hγpU : (γ : Hyperboloid E ≃ᵢ Hyperboloid E) p ∈ U :=
    hball (Metric.mem_ball'.mpr (lt_of_not_ge hn))
  exact Set.disjoint_left.mp (hd γ (hfree γ hγ p)) ⟨p, hpU, rfl⟩ hγpU

private theorem exists_fixedPoint_of_commutes
    [FiniteDimensional ℝ E] (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E))
    (hfree : ∀ γ : Γ, γ ≠ 1 → ∀ x : Hyperboloid E,
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E) x ≠ x)
    (hno : ¬ ∃ ξ : Metric.sphere (0 : E) 1,
      ∀ γ : Γ, boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ = ξ)
    (f : Hyperboloid E ≃ᵢ Hyperboloid E)
    (hcomm : ∀ (γ : Γ) (x : Hyperboloid E),
      f ((γ : Hyperboloid E ≃ᵢ Hyperboloid E) x) =
        (γ : Hyperboloid E ≃ᵢ Hyperboloid E) (f x)) :
    ∃ p : Hyperboloid E, f p = p := by
  by_contra h
  have hn : ∀ p : Hyperboloid E, f p ≠ p := by simpa only [not_exists] using h
  obtain ⟨ξ, hξ⟩ := fixedPoints_boundaryHomeomorph_nonempty f hn
  have hfinite := Set.finite_of_encard_le_coe (fixedPoints_boundaryHomeomorph_encard_le_two f hn)
  have horbit : (Set.range (fun γ : Γ =>
      boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ)).Finite := by
    apply hfinite.subset
    rintro η ⟨γ, rfl⟩
    change boundaryHomeomorph f (boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ) = _
    have hfg : (γ : Hyperboloid E ≃ᵢ Hyperboloid E).trans f =
        f.trans (γ : Hyperboloid E ≃ᵢ Hyperboloid E) := IsometryEquiv.ext (hcomm γ)
    have hb := congrArg (fun a => boundaryHomeomorph a ξ) hfg
    rw [boundaryHomeomorph_trans, boundaryHomeomorph_trans] at hb
    change boundaryHomeomorph f (boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ) =
      boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) (boundaryHomeomorph f ξ) at hb
    change boundaryHomeomorph f ξ = ξ at hξ
    rw [hξ] at hb
    exact hb
  exact hno ⟨ξ, boundaryHomeomorph_eq_self_of_finite_orbit Γ hfree ξ horbit⟩

theorem eq_refl_of_commutes_of_compact_thick_part
    [FiniteDimensional ℝ E] (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E))
    [DiscreteTopology Γ]
    (hfree : ∀ γ : Γ, γ ≠ 1 → ∀ x : Hyperboloid E,
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E) x ≠ x)
    (hthick : ∀ δ : ℝ, 0 < δ →
      IsCompact ((Quotient.mk (MulAction.orbitRel Γ (Hyperboloid E))) ''
        {x : Hyperboloid E | ∀ γ : Γ, γ ≠ 1 →
          δ ≤ dist x ((γ : Hyperboloid E ≃ᵢ Hyperboloid E) x)}))
    (hno : ¬ ∃ ξ : Metric.sphere (0 : E) 1,
      ∀ γ : Γ, boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ = ξ)
    (f : Hyperboloid E ≃ᵢ Hyperboloid E)
    (hcomm : ∀ (γ : Γ) (x : Hyperboloid E),
      f ((γ : Hyperboloid E ≃ᵢ Hyperboloid E) x) =
        (γ : Hyperboloid E ≃ᵢ Hyperboloid E) (f x)) :
    f = IsometryEquiv.refl (Hyperboloid E) := by
  let _ : IsIsometricSMul Γ (Hyperboloid E) := ⟨fun γ => γ.val.isometry⟩
  by_contra hf
  obtain ⟨p, hp⟩ := exists_fixedPoint_of_commutes Γ hfree hno f hcomm
  obtain ⟨v, hv, ho, hray⟩ := exists_geodesicLine_dist_le_of_fixedPoint f p hp hf
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_le_dist_apply Γ hfree p
  obtain ⟨K, hK, hrep⟩ := MulAction.exists_compact_representatives (hthick δ hδ)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall p
  let t := max R 0 + 1
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  let c := geodesicLine p v hv ho t
  have hct : ∀ γ : Γ, γ ≠ 1 → δ ≤ dist c ((γ : Hyperboloid E ≃ᵢ Hyperboloid E) c) := by
    intro γ hγ
    exact (hgap γ hγ).trans (hray γ (hcomm γ) t ht).1
  obtain ⟨γ, hγ⟩ := hrep c ⟨c, hct, rfl⟩
  have hle : t ≤ dist (γ • c) p := by
    have h := (hray (γ⁻¹ : Γ) (hcomm (γ⁻¹ : Γ)) t ht).2
    have he : dist (γ • c) p = dist c ((γ⁻¹ : Γ) • p) := by
      rw [← dist_smul γ c ((γ⁻¹ : Γ) • p), smul_inv_smul]
    rwa [he]
  have hb : dist (γ • c) p ≤ R := hR hγ
  have hmax : R ≤ max R 0 := le_max_left _ _
  dsimp only [t] at hle
  linarith

end DifferentialGeometry.Hyperboloid
