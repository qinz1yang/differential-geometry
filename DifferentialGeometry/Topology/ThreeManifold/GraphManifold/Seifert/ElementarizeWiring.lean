import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.AnnulusLongCollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Collar pieces as products over the planar annulus

Lane P1W, tier T1 (collar-piece adapter).

The planar annulus `planarSet 2` (`1/2 ≤ ‖z‖ ≤ 3`) is diffeomorphic to `S¹ × [0, L]` by the polar
coordinates `annulusRadial L : z ↦ (z / ‖z‖, 2L(3 - ‖z‖)/5)`, with inverse
`(t, r) ↦ (3 - 5r/(2L)) t`. Along the planar collar of the outer circle it reads `(t, Ls/10)`, along
the planar collar of the inner circle `(t⁻¹, L - Ls/10)`.

A collar piece `K : T² × [0, L] → X` is then the map `collarPieceMap L K` on
`planarSet 2 × S¹`, the composition of `K` with the diffeomorphism
`(q, v) ↦ ((annulusRadial L q).1, v, (annulusRadial L q).2)`. It is smooth with bijective
differential wherever `K` is, injective if `K` is, has the same range as `K`, and reads `K` on the
two planar collars (`collarPieceMap_collar_zero`, `collarPieceMap_collar_one`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert.Wiring

theorem norm_planarSet_two_bounds (x : planarSet.{u} 2) :
    1 / 2 ≤ ‖x.val.down‖ ∧ ‖x.val.down‖ ≤ 3 := by
  have hz := (mem_planarSet_iff (Or.inl rfl) x.val).mp x.2
  rw [mem_planarModel_two] at hz
  exact ⟨hz.2, hz.1⟩

theorem planarSet_two_down_ne_zero (x : planarSet.{u} 2) : x.val.down ≠ 0 := by
  rw [← norm_pos_iff]
  linarith [(norm_planarSet_two_bounds x).1]

variable (L : ℝ) [Fact (0 < L)]

def annulusRadialCoord (x : planarSet.{u} 2) : Set.Icc (0 : ℝ) L :=
  ⟨2 * L * (3 - ‖x.val.down‖) / 5, by
    have hL : 0 < L := Fact.out
    obtain ⟨h1, h2⟩ := norm_planarSet_two_bounds x
    constructor
    · exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by norm_num)
    · rw [div_le_iff₀ (by norm_num)]
      nlinarith⟩

theorem annulusRadialInv_mem (t : Circle) (r : Set.Icc (0 : ℝ) L) :
    ULift.up.{u} ((3 - 5 * (r : ℝ) / (2 * L)) • (t : ℂ)) ∈ planarSet.{u} 2 := by
  have hL : 0 < L := Fact.out
  have h0 := r.2.1
  have h1 := r.2.2
  have ha : 5 * (r : ℝ) / (2 * L) ≤ 5 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hb : 0 ≤ 5 * (r : ℝ) / (2 * L) := by positivity
  rw [mem_planarSet_iff (Or.inl rfl), ULift.down_up, mem_planarModel_two, norm_smul,
    Circle.norm_coe, mul_one, Real.norm_of_nonneg (by linarith)]
  constructor <;> linarith

def annulusRadialInv (p : Circle × Set.Icc (0 : ℝ) L) : planarSet.{u} 2 :=
  ⟨ULift.up ((3 - 5 * (p.2 : ℝ) / (2 * L)) • (p.1 : ℂ)), annulusRadialInv_mem L p.1 p.2⟩

theorem annulusRadialInv_factor_pos (r : Set.Icc (0 : ℝ) L) : 0 < 3 - 5 * (r : ℝ) / (2 * L) := by
  have hL : 0 < L := Fact.out
  have h1 := r.2.2
  have ha : 5 * (r : ℝ) / (2 * L) ≤ 5 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

def annulusRadial : planarSet.{u} 2 ≃ₘ⟮𝓡∂ 2, (𝓡 1).prod (𝓡∂ 1)⟯ (Circle × Set.Icc (0 : ℝ) L) where
  toFun x := (unitOf x.val.down, annulusRadialCoord L x)
  invFun := annulusRadialInv L
  left_inv x := by
    have hL : L ≠ 0 := (Fact.out : (0 : ℝ) < L).ne'
    apply Subtype.ext
    apply ULift.ext
    change (3 - 5 * (2 * L * (3 - ‖x.val.down‖) / 5) / (2 * L)) • ((unitOf x.val.down : ℂ)) =
      x.val.down
    rw [show 3 - 5 * (2 * L * (3 - ‖x.val.down‖) / 5) / (2 * L) = ‖x.val.down‖ by
      field_simp
      ring]
    exact norm_smul_unitOf _
  right_inv p := by
    obtain ⟨t, r⟩ := p
    have hL : L ≠ 0 := (Fact.out : (0 : ℝ) < L).ne'
    have ha := annulusRadialInv_factor_pos L r
    refine Prod.ext ?_ (Subtype.ext ?_)
    · exact unitOf_smul ha t
    · change 2 * L * (3 - ‖(3 - 5 * (r : ℝ) / (2 * L)) • (t : ℂ)‖) / 5 = r
      rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg ha.le]
      field_simp
      ring
  contMDiff_toFun := by
    refine (contMDiffOn_unitOf.comp_contMDiff (contMDiff_planarSet_down 2)
      fun x => planarSet_two_down_ne_zero x).prodMk ?_
    refine contMDiff_iff_comp_subtypeVal_Icc.mpr ⟨?_, ?_⟩
    · exact (((continuous_const.mul (continuous_const.sub (continuous_norm.comp
        (contMDiff_planarSet_down 2).continuous))).div_const 5)).subtype_mk _
    · intro x
      have hn : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞ (fun x : planarSet.{u} 2 => ‖x.val.down‖) x :=
        (contDiffAt_norm ℝ (planarSet_two_down_ne_zero x)).contMDiffAt.comp x
          (contMDiff_planarSet_down 2 x)
      exact ((contDiff_const.mul (contDiff_const.sub contDiff_id)).div_const
        5).contMDiff.contMDiffAt.comp x hn
  contMDiff_invFun := by
    refine ((planarAtlas.{u} 2).contMDiff_iff_subtype_val _).mpr ?_
    have hr : ContMDiff ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : Circle × Set.Icc (0 : ℝ) L => 3 - 5 * (p.2 : ℝ) / (2 * L)) :=
      (contDiff_const.sub ((contDiff_const.mul contDiff_id).div_const _)).contMDiff.comp
        (contMDiff_subtypeVal_Icc.comp contMDiff_snd)
    have hpair : ContMDiff ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ × ℂ) ∞
        (fun p : Circle × Set.Icc (0 : ℝ) L => (3 - 5 * (p.2 : ℝ) / (2 * L), (p.1 : ℂ))) :=
      hr.prodMk_space (contMDiff_circle_coe.comp contMDiff_fst)
    exact contMDiff_planeLift_up.comp
      ((contDiff_fst.smul contDiff_snd).contMDiff.comp hpair)

theorem annulusRadial_apply_fst (x : planarSet.{u} 2) : (annulusRadial L x).1 = unitOf x.val.down :=
  rfl

theorem annulusRadial_apply_snd (x : planarSet.{u} 2) :
    ((annulusRadial L x).2 : ℝ) = 2 * L * (3 - ‖x.val.down‖) / 5 :=
  rfl

theorem planarBase_two_collar_val (j : Fin 2) (t : Circle) {s : ℝ} (hs : 0 ≤ s) (h1 : s < 1) :
    ((planarBase.{u} 2 (Or.inl rfl)).collar j (t, halfPoint s hs)).val.down =
      planarCollarFormula 2 j ((t : ℂ), s) :=
  planarCollarMap_val.{u} (Or.inl rfl) j (p := (t, halfPoint s hs)) h1

theorem annulusRadial_of_down (x : planarSet.{u} 2) {a : ℝ} (ha : 0 < a) (w : Circle)
    (hx : x.val.down = a • (w : ℂ)) :
    (annulusRadial L x).1 = w ∧ ((annulusRadial L x).2 : ℝ) = 2 * L * (3 - a) / 5 := by
  rw [annulusRadial_apply_fst, annulusRadial_apply_snd, hx, norm_smul, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg ha.le]
  exact ⟨unitOf_smul ha w, rfl⟩

theorem annulusRadial_collar_zero (t : Circle) {s : ℝ} (hs : 0 ≤ s) (h1 : s < 1) :
    (annulusRadial L ((planarBase.{u} 2 (Or.inl rfl)).collar 0 (t, halfPoint s hs))).1 = t ∧
      ((annulusRadial L ((planarBase.{u} 2 (Or.inl rfl)).collar 0 (t, halfPoint s hs))).2 : ℝ) =
        L * s / 10 := by
  have he : planarCollarFormula 2 0 ((t : ℂ), s) = (3 - s / 4) • (t : ℂ) := by
    simp only [planarCollarFormula, planarCenter_two, planarRadius, planarSign, planarTwist,
      Fin.val_zero, ↓reduceIte, Complex.ofReal_zero, zero_add]
    congr 1
    ring
  have hp : 0 < 3 - s / 4 := by linarith
  have h := annulusRadial_of_down L _ hp t ((planarBase_two_collar_val 0 t hs h1).trans he)
  exact ⟨h.1, h.2.trans (by ring)⟩

theorem annulusRadial_collar_one (t : Circle) {s : ℝ} (hs : 0 ≤ s) (h1 : s < 1) :
    (annulusRadial L ((planarBase.{u} 2 (Or.inl rfl)).collar 1 (t, halfPoint s hs))).1 = t⁻¹ ∧
      ((annulusRadial L ((planarBase.{u} 2 (Or.inl rfl)).collar 1 (t, halfPoint s hs))).2 : ℝ) =
        L - L * s / 10 := by
  have he : planarCollarFormula 2 1 ((t : ℂ), s) = (1 / 2 + s / 4) • ((t⁻¹ : Circle) : ℂ) := by
    simp only [planarCollarFormula, planarCenter_two, planarRadius, planarSign, planarTwist,
      Fin.val_one, one_ne_zero, ↓reduceIte, Complex.ofReal_zero, zero_add, Circle.coe_inv_eq_conj]
    congr 1
    ring
  have hp : 0 < 1 / 2 + s / 4 := by linarith
  have h := annulusRadial_of_down L _ hp t⁻¹ ((planarBase_two_collar_val 1 t hs h1).trans he)
  exact ⟨h.1, h.2.trans (by ring)⟩

def annulusProduct :
    (planarSet.{u} 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), torusModel.prod (𝓡∂ 1)⟯
      (Torus × Set.Icc (0 : ℝ) L) where
  toFun q := (((annulusRadial L q.1).1, q.2), (annulusRadial L q.1).2)
  invFun p := ((annulusRadial L).symm (p.1.1, p.2), p.1.2)
  left_inv q := by simp
  right_inv p := by simp
  contMDiff_toFun :=
    ((contMDiff_fst.comp ((annulusRadial L).contMDiff.comp contMDiff_fst)).prodMk
      contMDiff_snd).prodMk (contMDiff_snd.comp ((annulusRadial L).contMDiff.comp contMDiff_fst))
  contMDiff_invFun :=
    ((annulusRadial L).symm.contMDiff.comp ((contMDiff_fst.comp contMDiff_fst).prodMk
      contMDiff_snd)).prodMk (contMDiff_snd.comp contMDiff_fst)

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]

def collarPieceMap (K : Torus × Set.Icc (0 : ℝ) L → X) :
    (planarBase.{u} 2 (Or.inl rfl)).surface.Carrier × Circle → X :=
  fun q => K (((annulusRadial L q.1).1, q.2), (annulusRadial L q.1).2)

omit [TopologicalSpace X] in
theorem collarPieceMap_eq_comp (K : Torus × Set.Icc (0 : ℝ) L → X) :
    collarPieceMap.{u} L K = K ∘ annulusProduct L :=
  rfl

theorem contMDiff_collarPieceMap {K : Torus × Set.Icc (0 : ℝ) L → X}
    (hK : ContMDiff (torusModel.prod (𝓡∂ 1)) I ∞ K) :
    ContMDiff ((SurfaceModel.model (planarBase.{u} 2 (Or.inl rfl)).surface.kind).prod (𝓡 1)) I ∞
      (collarPieceMap L K) :=
  hK.comp (annulusProduct L).contMDiff

theorem bijective_mfderiv_collarPieceMap [IsManifold I ∞ X]
    {K : Torus × Set.Icc (0 : ℝ) L → X}
    (hK : ContMDiff (torusModel.prod (𝓡∂ 1)) I ∞ K)
    (hKb : ∀ q, Function.Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) I K q))
    (q : (planarBase.{u} 2 (Or.inl rfl)).surface.Carrier × Circle) :
    Function.Bijective (mfderiv ((SurfaceModel.model
      (planarBase.{u} 2 (Or.inl rfl)).surface.kind).prod (𝓡 1)) I (collarPieceMap L K) q) :=
  mfderiv_comp_diffeomorph_symm_bijective (annulusProduct L) hK q (hKb _)

omit [TopologicalSpace X] in
theorem injective_collarPieceMap {K : Torus × Set.Icc (0 : ℝ) L → X}
    (hK : Function.Injective K) : Function.Injective (collarPieceMap.{u} L K) :=
  hK.comp (annulusProduct L).injective

omit [TopologicalSpace X] in
theorem range_collarPieceMap (K : Torus × Set.Icc (0 : ℝ) L → X) :
    Set.range (collarPieceMap.{u} L K) = Set.range K :=
  (annulusProduct L).surjective.range_comp K

omit [TopologicalSpace X] in
theorem collarPieceMap_collar_zero (K : Torus × Set.Icc (0 : ℝ) L → X) (t v : Circle) {s : ℝ}
    (hs : 0 ≤ s) (h1 : s < 1) :
    collarPieceMap L K ((planarBase.{u} 2 (Or.inl rfl)).collar 0 (t, halfPoint s hs), v) =
      K ((t, v), Set.projIcc 0 L (Fact.out : (0 : ℝ) < L).le (L * s / 10)) := by
  have hL : 0 < L := Fact.out
  obtain ⟨h1', h2'⟩ := annulusRadial_collar_zero L t hs h1
  have hm : L * s / 10 ∈ Set.Icc (0 : ℝ) L :=
    ⟨by positivity, by rw [div_le_iff₀ (by norm_num)]; nlinarith⟩
  change K (((annulusRadial L _).1, v), (annulusRadial L _).2) = _
  rw [h1', Set.projIcc_of_mem _ hm]
  congr
  exact Subtype.ext h2'

omit [TopologicalSpace X] in
theorem collarPieceMap_collar_one (K : Torus × Set.Icc (0 : ℝ) L → X) (t v : Circle) {s : ℝ}
    (hs : 0 ≤ s) (h1 : s < 1) :
    collarPieceMap L K ((planarBase.{u} 2 (Or.inl rfl)).collar 1 (t, halfPoint s hs), v) =
      K ((t⁻¹, v), Set.projIcc 0 L (Fact.out : (0 : ℝ) < L).le (L - L * s / 10)) := by
  have hL : 0 < L := Fact.out
  obtain ⟨h1', h2'⟩ := annulusRadial_collar_one L t hs h1
  have hm : L - L * s / 10 ∈ Set.Icc (0 : ℝ) L := ⟨by nlinarith, by nlinarith⟩
  change K (((annulusRadial L _).1, v), (annulusRadial L _).2) = _
  rw [h1', Set.projIcc_of_mem _ hm]
  congr
  exact Subtype.ext h2'

end GC.Seifert.Wiring
