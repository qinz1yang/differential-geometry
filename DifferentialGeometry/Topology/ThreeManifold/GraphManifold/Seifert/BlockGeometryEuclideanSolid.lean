import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockCharts
import DifferentialGeometry.Geometry.Thurston.Models.ConeModelSolidTorus
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanNormal
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryPantsPermutation
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanCharts

/-!
# Euclidean geometry for whole solid-torus blocks

Whole interior identifications use the covering chart package and preserve the actual interior
carrier. Compact product collar permutations and normal absorption reduce two fillings to one
on the same carrier before transport to a fibred solid torus.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

theorem solidTorusShape_counts (d : SeifertData) (h : d.IsSolidTorus) :
    (d.k = 1 ∧ d.cones.length = 0 ∧ d.normals.length = 0) ∨
      (d.k = 2 ∧ d.cones.length = 0 ∧ d.normals.length = 1) ∨
      (d.k = 2 ∧ d.cones.length = 1 ∧ d.normals.length = 0) ∨
      (d.k = 3 ∧ d.cones.length = 0 ∧ d.normals.length = 2) ∨
      (d.k = 3 ∧ d.cones.length = 1 ∧ d.normals.length = 1) := by
  have hk := d.ports_add_length_add_length
  have hmax := d.k_le_three
  rcases h with ⟨hp, hc⟩
  omega

theorem SeifertBlockCharts.productRegion_eq_wholeInterior
    {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
    (h : d.fillingCount = 0) : C.productRegion = W.pieceInterior ⊤ := by
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · intro hx
    exact ⟨trivial, C.productRegion_interior hx⟩
  · intro hx
    rcases C.covers x hx.2 with hp | ⟨m, hm⟩
    · exact hp
    · exact Fin.elim0 (Fin.cast h m)

def SeifertBlockCharts.unfilledWholeInteriorDiffeomorph
    {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
    (h : d.fillingCount = 0) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, PlaneCircleModel⟯ planarOpen d.k × Circle where
  toFun x := C.product.symm ⟨x.val, by
    rw [C.productRegion_eq_wholeInterior h]
    exact x.property⟩
  invFun y := ⟨C.product y, by
    rw [← C.productRegion_eq_wholeInterior h]
    exact (C.product y).property⟩
  left_inv x := by
    apply Subtype.ext
    change (C.product (C.product.symm ⟨x.val, _⟩)).val = x.val
    exact congrArg Subtype.val (C.product.apply_symm_apply _)
  right_inv y := C.product.symm_apply_apply y
  contMDiff_toFun := by
    apply C.product.symm.contMDiff.comp
    exact (ContMDiff.subtypeVal_comp_iff C.productRegion _).mp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (W.pieceInterior ⊤) _).mp
    change ContMDiff PlaneCircleModel W.model ∞ (fun y => (C.product y).val)
    exact contMDiff_subtype_val.comp C.product.contMDiff

theorem planarOpen_one_iff (z : ℂ) : z ∈ planarOpen 1 ↔ ‖z‖ < 3 := by
  change z ∈ interior (planarModel 1) ↔ _
  rw [planarModel_one, interior_closedBall (0 : ℂ) (by norm_num : (3 : ℝ) ≠ 0),
    Metric.mem_ball, dist_zero_right]

def planarOpenDiscDiffeomorph :
    planarOpen 1 ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ openUnitDisc where
  toFun x := ⟨x.val / 3, by
    apply mem_openUnitDisc.mpr
    rw [norm_div]
    norm_num
    exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
      (by simpa using (planarOpen_one_iff x.val).mp x.property)⟩
  invFun y := ⟨3 * y.val, by
    apply (planarOpen_one_iff _).mpr
    rw [norm_mul]
    norm_num
    linarith [(mem_openUnitDisc.mp y.property)]⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    ring
  right_inv y := by
    apply Subtype.ext
    dsimp
    ring
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff openUnitDisc _).mp
    have hs : ContDiff ℝ ∞ (fun z : ℂ => z / 3) := contDiff_id.div_const 3
    exact hs.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (planarOpen 1) _).mp
    have hs : ContDiff ℝ ∞ (fun z : ℂ => 3 * z) := contDiff_const.mul contDiff_id
    exact hs.contMDiff.comp contMDiff_subtype_val

def SeifertBlockCharts.unfilledSolidTorusDiffeomorph
    {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
    (h : d.IsSolidTorus) (hn : d.fillingCount = 0) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, 𝓡 3⟯ FibredSolidTorus 1 0 := by
  have hk : d.k = 1 := by
    have he := d.ports_add_length_add_length
    have hf : d.cones.length + d.normals.length = 0 := hn
    have hp := h.1
    omega
  let ep : (planarOpen d.k × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯
      (openUnitDisc × Circle) := by
    rw [hk]
    exact planarOpenDiscDiffeomorph.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)
  exact (C.unfilledWholeInteriorDiffeomorph hn).trans
    (ep.trans (solidTorusDiffeo 1 0).symm)

def solidTorusShapeGeometry_of_unfilled {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (h : d.IsSolidTorus) (hn : d.fillingCount = 0) :
    W.InteriorGeometry ⊤ :=
  interiorGeometryOfDiffeomorph
    (fibredSolidTorusGeometry .euclidean (by norm_num [ConnectionModel.baseCurvature]) 1 0)
    W ⊤ (C.unfilledSolidTorusDiffeomorph h hn)

theorem solidTorusShapeGeometry_of_unfilled_model
    {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
    (h : d.IsSolidTorus) (hn : d.fillingCount = 0) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (solidTorusShapeGeometry_of_unfilled C h hn).model = .euclidean :=
  rfl

def solidAnnulusDepthDiffeomorph (j : Fin 2) :
    ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toFun s := if j.val = 0 then 4 - s / 2 else -1 + s / 2
  invFun r := if j.val = 0 then 8 - 2 * r else 2 + 2 * r
  left_inv s := by
    dsimp
    split_ifs <;> ring
  right_inv r := by
    dsimp
    split_ifs <;> ring
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun s : ℝ => if j.val = 0 then 4 - s / 2 else -1 + s / 2)
    by_cases hj : j.val = 0
    · simp only [hj, ite_true]
      apply ContDiff.contMDiff
      exact contDiff_const.sub (contDiff_id.div_const 2)
    · simp only [hj, ite_false]
      apply ContDiff.contMDiff
      exact contDiff_const.add (contDiff_id.div_const 2)
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun r : ℝ => if j.val = 0 then 8 - 2 * r else 2 + 2 * r)
    by_cases hj : j.val = 0
    · simp only [hj, ite_true]
      apply ContDiff.contMDiff
      exact contDiff_const.sub (contDiff_const.mul contDiff_id)
    · simp only [hj, ite_false]
      apply ContDiff.contMDiff
      exact contDiff_const.add (contDiff_const.mul contDiff_id)

def solidAnnulusTorusFlip (j : Fin 2) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus where
  toFun t := (chartCircleFlip (decide (j.val ≠ 0)) t.1, t.2)
  invFun t := (chartCircleFlip (decide (j.val ≠ 0)) t.1, t.2)
  left_inv t := Prod.ext (chartCircleFlip_involutive _ t.1) rfl
  right_inv t := Prod.ext (chartCircleFlip_involutive _ t.1) rfl
  contMDiff_toFun := (contMDiff_chartCircleFlip _).comp contMDiff_fst |>.prodMk contMDiff_snd
  contMDiff_invFun := (contMDiff_chartCircleFlip _).comp contMDiff_fst |>.prodMk contMDiff_snd

def solidAnnulusRawSeam (p : ℕ) [NeZero p] (j : Fin 2) (A : GL (Fin 2) ℤ) :
    PartialDiffeomorph PlaneCircleModel PlaneCircleModel (ℂ × Circle) (ℂ × Circle) ∞ :=
  ((chartPolar p).trans
    (((linearTorusDiffeomorph A).trans (solidAnnulusTorusFlip j)).prodCongr
      (solidAnnulusDepthDiffeomorph j)).toPartialDiffeomorph).trans (chartPolar 1).symm

theorem solidAnnulusRawSeam_apply (p : ℕ) [NeZero p] (j : Fin 2)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) :
    solidAnnulusRawSeam p j A y =
      let t := linearTorusMap A (unitOf y.1, y.2)
      let r := planarRadius j + (if j.val = 0 then -1 else 1) * (‖y.1‖ ^ p - 1) / 2
      (r * (if j.val = 0 then (t.1 : ℂ) else conj (t.1 : ℂ)), t.2) := by
  have hn : ‖3 * y.1‖ / 3 = ‖y.1‖ := by simp
  have hr (s : ℝ) : seamRadius 1 s / 3 = 1 + s / 2 := by
    norm_num [seamRadius]
  change ((seamRadius 1
    (if j.val = 0 then 4 - seamDepth p ‖3 * y.1‖ / 2
      else -1 + seamDepth p ‖3 * y.1‖ / 2) / 3) •
      (chartCircleFlip (decide (j.val ≠ 0))
        (linearTorusMap A (unitOf y.1, y.2)).1 : ℂ),
    (linearTorusMap A (unitOf y.1, y.2)).2) = _
  rw [hr]
  by_cases hj : j.val = 0
  · simp only [hj, ite_true, ne_eq, not_true_eq_false, decide_false, chartCircleFlip,
      Bool.false_eq_true, ite_false, planarRadius]
    have he : 1 + (4 - seamDepth p ‖3 * y.1‖ / 2) / 2 =
        3 - (‖y.1‖ ^ p - 1) / 2 := by
      dsimp [seamDepth]
      rw [hn]
      ring
    rw [he, Complex.real_smul]
    congr 2
    push_cast
    ring
  · simp only [hj, ite_false, ne_eq, not_false_eq_true, decide_true, chartCircleFlip,
      ite_true, planarRadius]
    have he : 1 + (-1 + seamDepth p ‖3 * y.1‖ / 2) / 2 =
        1 / 2 + (‖y.1‖ ^ p - 1) / 2 := by
      dsimp [seamDepth]
      rw [hn]
      ring
    rw [he, Circle.coe_inv_eq_conj, Complex.real_smul]
    congr 2
    push_cast
    ring

theorem planarOpen_two_iff (z : ℂ) :
    z ∈ planarOpen 2 ↔ 1 / 2 < ‖z‖ ∧ ‖z‖ < 3 := by
  constructor
  · intro hz
    refine ⟨?_, chartPlanarInterior_lt hz⟩
    simpa [planarCenter] using
      chartPlanarInterior_hole_lt hz (1 : Fin 2) (by decide)
  · intro hz
    have ho : IsOpen {w : ℂ | 1 / 2 < ‖w‖ ∧ ‖w‖ < 3} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    have hs : {w : ℂ | 1 / 2 < ‖w‖ ∧ ‖w‖ < 3} ⊆ planarModel 2 := by
      intro w hw
      exact (mem_planarModel_two w).mpr ⟨hw.2.le, hw.1.le⟩
    exact interior_maximal hs ho hz

theorem solidAnnulusRawSeam_source (p : ℕ) [NeZero p] (j : Fin 2)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle)
    (hy : 1 < ‖y.1‖ ^ p ∧ ‖y.1‖ ^ p < 6) :
    y ∈ (solidAnnulusRawSeam p j A).source := by
  have hn : ‖3 * y.1‖ / 3 = ‖y.1‖ := by simp
  have hne : y.1 ≠ 0 := by
    intro he
    have hb := hy.1
    rw [he, norm_zero, zero_pow (NeZero.ne p)] at hb
    norm_num at hb
  change (y.1 ≠ 0 ∧ True) ∧
    -2 < (if j.val = 0 then 4 - seamDepth p ‖3 * y.1‖ / 2
      else -1 + seamDepth p ‖3 * y.1‖ / 2)
  refine ⟨⟨hne, trivial⟩, ?_⟩
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false]
  · dsimp [seamDepth]
    rw [hn]
    linarith [hy.2]
  · dsimp [seamDepth]
    rw [hn]
    linarith [hy.1]

theorem solidAnnulusRawSeam_target (p : ℕ) [NeZero p] (j : Fin 2)
    (A : GL (Fin 2) ℤ) (z : ℂ × Circle) (hz : z.1 ∈ planarOpen 2) :
    z ∈ (solidAnnulusRawSeam p j A).target := by
  have hb := (planarOpen_two_iff z.1).mp hz
  have hn : ‖3 * z.1‖ / 3 = ‖z.1‖ := by simp
  have hne : z.1 ≠ 0 := by
    intro he
    simp only [he, norm_zero] at hb
    linarith [hb.1]
  change z.1 ≠ 0 ∧ (True ∧
    -2 < (if j.val = 0 then 8 - 2 * seamDepth 1 ‖3 * z.1‖
      else 2 + 2 * seamDepth 1 ‖3 * z.1‖))
  refine ⟨hne, trivial, ?_⟩
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false]
  · dsimp [seamDepth]
    rw [hn]
    norm_num
    linarith [hb.2]
  · dsimp [seamDepth]
    rw [hn]
    norm_num
    linarith [hb.1]

theorem solidAnnulusRawSeam_norm (p : ℕ) [NeZero p] (j : Fin 2)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle)
    (hy : 1 < ‖y.1‖ ^ p ∧ ‖y.1‖ ^ p < 6) :
    ‖(solidAnnulusRawSeam p j A y).1‖ =
      if j.val = 0 then (7 - ‖y.1‖ ^ p) / 2 else ‖y.1‖ ^ p / 2 := by
  rw [solidAnnulusRawSeam_apply]
  by_cases hj : j.val = 0
  · simp only [hj, ite_true, planarRadius, norm_mul, Complex.norm_real,
      Circle.norm_coe, mul_one]
    rw [Real.norm_of_nonneg (by linarith [hy.2])]
    ring
  · simp only [hj, ite_false, planarRadius, norm_mul, Complex.norm_real,
      Complex.norm_conj, Circle.norm_coe, mul_one]
    rw [Real.norm_of_nonneg (by linarith [hy.1])]
    ring

theorem solidAnnulusRawSeam_mem_planarOpen (p : ℕ) [NeZero p] (j : Fin 2)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle)
    (hy : 1 < ‖y.1‖ ^ p ∧ ‖y.1‖ ^ p < 6) :
    (solidAnnulusRawSeam p j A y).1 ∈ planarOpen 2 := by
  rw [planarOpen_two_iff, solidAnnulusRawSeam_norm p j A y hy]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false]
  · constructor <;> linarith [hy.1, hy.2]
  · constructor <;> linarith [hy.1, hy.2]

theorem solidAnnulusRawSeam_symm_norm_pow (p : ℕ) [NeZero p] (j : Fin 2)
    (A : GL (Fin 2) ℤ) (z : ℂ × Circle) (hz : z.1 ∈ planarOpen 2) :
    ‖((solidAnnulusRawSeam p j A).symm z).1‖ ^ p =
      if j.val = 0 then 7 - 2 * ‖z.1‖ else 2 * ‖z.1‖ := by
  have hb := (planarOpen_two_iff z.1).mp hz
  have hn : ‖3 * z.1‖ / 3 = ‖z.1‖ := by simp
  let s := if j.val = 0 then 8 - 2 * seamDepth 1 ‖3 * z.1‖
    else 2 + 2 * seamDepth 1 ‖3 * z.1‖
  have hs : -2 < s := by
    dsimp [s, seamDepth]
    rw [hn]
    by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false, pow_one]
    · linarith [hb.2]
    · linarith [hb.1]
  change ‖(seamRadius p s / 3) •
    ((((linearTorusDiffeomorph A).trans (solidAnnulusTorusFlip j)).symm
      (unitOf z.1, z.2)).1 : ℂ)‖ ^ p = _
  rw [norm_smul, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg (div_nonneg (seamRadius_pos p hs).le (by norm_num)),
    div_three_pow_seamRadius p hs]
  dsimp [s, seamDepth]
  rw [hn]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false, pow_one] <;> ring

theorem solidAnnulusRawSeam_symm_bounds (p : ℕ) [NeZero p] (j : Fin 2)
    (A : GL (Fin 2) ℤ) (z : ℂ × Circle) (hz : z.1 ∈ planarOpen 2) :
    1 < ‖((solidAnnulusRawSeam p j A).symm z).1‖ ^ p ∧
      ‖((solidAnnulusRawSeam p j A).symm z).1‖ ^ p < 6 := by
  have hb := (planarOpen_two_iff z.1).mp hz
  rw [solidAnnulusRawSeam_symm_norm_pow p j A z hz]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false]
  · constructor <;> linarith [hb.1, hb.2]
  · constructor <;> linarith [hb.1, hb.2]

def solidOpenCongrDiffeomorph (U V : TopologicalSpace.Opens ℂ) (h : U = V) :
    U ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ V := by
  subst V
  exact Diffeomorph.refl 𝓘(ℝ, ℂ) U ∞

theorem solidOpenCongrDiffeomorph_apply (U V : TopologicalSpace.Opens ℂ) (h : U = V)
    (x : U) : (solidOpenCongrDiffeomorph U V h x : ℂ) = x := by
  subst V
  rfl

def SeifertBlockCharts.annulusProduct {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (hk : d.k = 2) :
    (planarOpen 2 × Circle) ≃ₘ⟮PlaneCircleModel, W.model⟯ C.productRegion :=
  ((solidOpenCongrDiffeomorph (planarOpen 2) (planarOpen d.k)
    (congrArg planarOpen hk).symm).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans C.product

theorem solidPlanarOpenTwo_nonempty : Nonempty (planarOpen 2) :=
  ⟨⟨1, (planarOpen_two_iff 1).mpr (by norm_num)⟩⟩

theorem SeifertBlockCharts.annulusRegion_nonempty {W : CompactCarrier.{u}}
    {d : SeifertData} (C : SeifertBlockCharts W d) (hk : d.k = 2) :
    Nonempty C.productRegion :=
  ⟨C.annulusProduct hk (Classical.choice solidPlanarOpenTwo_nonempty, 1)⟩

def SeifertBlockCharts.solidProductPatch {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (hk : d.k = 2) (p : ℕ) [NeZero p]
    (j : Fin 2) (A : GL (Fin 2) ℤ) :
    PartialDiffeomorph W.model PlaneCircleModel W.Carrier (ℂ × Circle) ∞ :=
  ((DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := W.model)
    C.productRegion (C.annulusRegion_nonempty hk)).symm.trans
      (C.annulusProduct hk).symm.toPartialDiffeomorph).trans
    ((DifferentialGeometry.Topology.PartialDiffeomorph.prod
      (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := 𝓘(ℝ, ℂ))
        (planarOpen 2) solidPlanarOpenTwo_nonempty)
      (Diffeomorph.refl (𝓡 1) Circle ∞).toPartialDiffeomorph).trans
        (solidAnnulusRawSeam p j A).symm)

theorem SeifertBlockCharts.solidProductPatch_source {W : CompactCarrier.{u}}
    {d : SeifertData} (C : SeifertBlockCharts W d) (hk : d.k = 2)
    (p : ℕ) [NeZero p] (j : Fin 2) (A : GL (Fin 2) ℤ) (x : W.Carrier) :
    x ∈ (C.solidProductPatch hk p j A).source ↔ x ∈ C.productRegion := by
  let z := (C.annulusProduct hk).symm
    ((DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := W.model)
      C.productRegion (C.annulusRegion_nonempty hk)).symm x)
  change ((x ∈ (C.productRegion.openPartialHomeomorphSubtypeCoe
    (C.annulusRegion_nonempty hk)).target ∧ True) ∧
    ((True ∧ True) ∧ (z.1.val, z.2) ∈ (solidAnnulusRawSeam p j A).target)) ↔ _
  rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  exact ⟨fun h => h.1.1, fun h =>
    ⟨⟨h, trivial⟩, ⟨⟨trivial, trivial⟩,
      solidAnnulusRawSeam_target p j A (z.1.val, z.2) z.1.property⟩⟩⟩

theorem SeifertBlockCharts.solidProductPatch_apply {W : CompactCarrier.{u}}
    {d : SeifertData} (C : SeifertBlockCharts W d) (hk : d.k = 2)
    (p : ℕ) [NeZero p] (j : Fin 2) (A : GL (Fin 2) ℤ) (x : W.Carrier)
    (hx : x ∈ C.productRegion) :
    C.solidProductPatch hk p j A x =
      (solidAnnulusRawSeam p j A).symm
        (((C.annulusProduct hk).symm ⟨x, hx⟩).1.val,
          ((C.annulusProduct hk).symm ⟨x, hx⟩).2) := by
  have he : (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := W.model)
      C.productRegion (C.annulusRegion_nonempty hk)).symm x = ⟨x, hx⟩ := by
    apply Subtype.ext
    exact (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := W.model)
      C.productRegion (C.annulusRegion_nonempty hk)).right_inv
      (by
        change x ∈ (C.productRegion.openPartialHomeomorphSubtypeCoe
          (C.annulusRegion_nonempty hk)).target
        rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
        exact hx)
  change (solidAnnulusRawSeam p j A).symm
    (((C.annulusProduct hk).symm
      ((DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := W.model)
      C.productRegion (C.annulusRegion_nonempty hk)).symm x)).1.val,
      ((C.annulusProduct hk).symm
        ((DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := W.model)
        C.productRegion (C.annulusRegion_nonempty hk)).symm x)).2) = _
  rw [he]

theorem SeifertBlockCharts.solidProductPatch_target {W : CompactCarrier.{u}}
    {d : SeifertData} (C : SeifertBlockCharts W d) (hk : d.k = 2)
    (p : ℕ) [NeZero p] (j : Fin 2) (A : GL (Fin 2) ℤ) (y : ℂ × Circle) :
    y ∈ (C.solidProductPatch hk p j A).target ↔
      1 < ‖y.1‖ ^ p ∧ ‖y.1‖ ^ p < 6 := by
  constructor
  · intro hy
    let x := (C.solidProductPatch hk p j A).symm y
    have hx := (C.solidProductPatch_source hk p j A x).mp
      ((C.solidProductPatch hk p j A).map_target hy)
    have he := (C.solidProductPatch hk p j A).right_inv hy
    change C.solidProductPatch hk p j A x = y at he
    rw [C.solidProductPatch_apply hk p j A x hx] at he
    rw [← he]
    exact solidAnnulusRawSeam_symm_bounds p j A _
      (((C.annulusProduct hk).symm ⟨x, hx⟩).1.property)
  · intro hy
    have hr := solidAnnulusRawSeam_source p j A y hy
    have hp := solidAnnulusRawSeam_mem_planarOpen p j A y hy
    let z : planarOpen 2 × Circle :=
      (⟨(solidAnnulusRawSeam p j A y).1, hp⟩, (solidAnnulusRawSeam p j A y).2)
    let x := C.annulusProduct hk z
    have hx := (C.solidProductPatch_source hk p j A x).mpr x.property
    have he : C.solidProductPatch hk p j A x = y := by
      rw [C.solidProductPatch_apply hk p j A x x.property]
      have hi := (C.annulusProduct hk).symm_apply_apply z
      rw [hi]
      exact (solidAnnulusRawSeam p j A).left_inv hr
    rw [← he]
    exact (C.solidProductPatch hk p j A).map_source hx

def solidWholeRadius (p : ℕ) : ℝ := seamRadius p 10 / 3

theorem solidWholeRadius_pos (p : ℕ) : 0 < solidWholeRadius p :=
  div_pos (seamRadius_pos p (by norm_num)) (by norm_num)

theorem solidWholeRadius_pow (p : ℕ) [NeZero p] : solidWholeRadius p ^ p = 6 := by
  exact (div_three_pow_seamRadius p (s := 10) (by norm_num)).trans (by norm_num)

theorem solidWholeRadius_gt_one (p : ℕ) [NeZero p] : 1 < solidWholeRadius p := by
  have hp := solidWholeRadius_pos p
  have he := solidWholeRadius_pow p
  have hl : (1 : ℝ) ^ p < solidWholeRadius p ^ p := by rw [he, one_pow]; norm_num
  exact (pow_lt_pow_iff_left₀ (by norm_num) hp.le (NeZero.ne p)).mp hl

theorem solidWholeRadius_norm_iff (p : ℕ) [NeZero p] (z : ℂ) :
    ‖z‖ ^ p < 6 ↔ ‖z‖ < solidWholeRadius p := by
  rw [← solidWholeRadius_pow p]
  exact pow_lt_pow_iff_left₀ (norm_nonneg z) (solidWholeRadius_pos p).le (NeZero.ne p)

def solidWholeInterior (p : ℕ) : TopologicalSpace.Opens (ℂ × Circle) :=
  ⟨{y | ‖y.1‖ ^ p < 6}, isOpen_lt ((continuous_norm.comp continuous_fst).pow p)
    continuous_const⟩

theorem solidWholeInterior_nonempty (p : ℕ) [NeZero p] : Nonempty (solidWholeInterior p) :=
  ⟨⟨(0, 1), by simp [solidWholeInterior, zero_pow (NeZero.ne p)]⟩⟩

def solidWholeInteriorDiffeomorph (p : ℕ) [NeZero p] :
    solidWholeInterior p ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯ (openUnitDisc × Circle) where
  toFun y := (⟨y.val.1 / solidWholeRadius p, by
    apply mem_openUnitDisc.mpr
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (solidWholeRadius_pos p).le]
    apply (div_lt_one (solidWholeRadius_pos p)).mpr
    exact (solidWholeRadius_norm_iff p y.val.1).mp y.property⟩, y.val.2)
  invFun z := ⟨((solidWholeRadius p : ℂ) * z.1.val, z.2), by
    apply (solidWholeRadius_norm_iff p _).mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (solidWholeRadius_pos p).le]
    have hz := (mem_openUnitDisc.mp z.1.property)
    nlinarith [solidWholeRadius_pos p]⟩
  left_inv y := by
    apply Subtype.ext
    apply Prod.ext
    · change (solidWholeRadius p : ℂ) * (y.val.1 / solidWholeRadius p) = y.val.1
      have hn : (solidWholeRadius p : ℂ) ≠ 0 := by
        exact_mod_cast (solidWholeRadius_pos p).ne'
      field_simp
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change (solidWholeRadius p : ℂ) * z.1.val / solidWholeRadius p = z.1.val
      have hn : (solidWholeRadius p : ℂ) ≠ 0 := by
        exact_mod_cast (solidWholeRadius_pos p).ne'
      field_simp
    · rfl
  contMDiff_toFun := by
    apply ContMDiff.prodMk
    · apply (ContMDiff.subtypeVal_comp_iff openUnitDisc _).mp
      have hs : ContDiff ℝ ∞ (fun z : ℂ => z / solidWholeRadius p) :=
        contDiff_id.div_const _
      exact hs.contMDiff.comp (contMDiff_fst.comp contMDiff_subtype_val)
    · exact contMDiff_snd.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (solidWholeInterior p) _).mp
    have hs : ContDiff ℝ ∞ (fun z : ℂ => (solidWholeRadius p : ℂ) * z) :=
      contDiff_const.mul contDiff_id
    exact (hs.contMDiff.comp (contMDiff_subtype_val.comp contMDiff_fst)).prodMk contMDiff_snd

theorem solidAnnulusRawSeam_norm_boundary (p : ℕ) [NeZero p] (j : Fin 2)
    (A : GL (Fin 2) ℤ) :
    ‖(solidAnnulusRawSeam p j A ((solidWholeRadius p : ℂ), 1)).1‖ =
      if j.val = 0 then 1 / 2 else 3 := by
  have hn : ‖(solidWholeRadius p : ℂ)‖ ^ p = 6 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (solidWholeRadius_pos p).le,
      solidWholeRadius_pow p]
  rw [solidAnnulusRawSeam_apply]
  by_cases hj : j.val = 0 <;>
    simp only [hj, ite_true, ite_false, planarRadius, norm_mul, Complex.norm_conj,
      Circle.norm_coe, mul_one] <;> rw [hn] <;> norm_num

theorem SeifertBlockCharts.solidAnnulusSeam_eq {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (hk : d.k = 2) (m : Fin d.fillingCount) (y : ℂ × Circle) :
    solidAnnulusRawSeam (d.fillingSlope m).1.natAbs (Fin.cast hk (C.port (.inr m)))
      (C.matrix m) y = seamModel d m (C.port (.inr m)) (C.matrix m) y := by
  have hc : planarCenter d.k (C.port (.inr m)) = 0 := by simp [planarCenter, hk]
  rw [solidAnnulusRawSeam_apply]
  dsimp only [seamModel]
  rw [hc]
  simp only [Complex.ofReal_zero, zero_add]
  rfl

theorem SeifertBlockCharts.solidTubeWidth_bound {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (hk : d.k = 2) (m : Fin d.fillingCount) :
    1 + C.ε ≤ solidWholeRadius (d.fillingSlope m).1.natAbs := by
  let p := (d.fillingSlope m).1.natAbs
  let j := Fin.cast hk (C.port (.inr m))
  by_contra hn
  have hr : solidWholeRadius p < 1 + C.ε := lt_of_not_ge hn
  let y : ℂ × Circle := ((solidWholeRadius p : ℂ), 1)
  have hy : y ∈ C.transitionDomain := by
    rw [C.transitionDomain_eq]
    change 1 < ‖(solidWholeRadius p : ℂ)‖ ∧ ‖(solidWholeRadius p : ℂ)‖ < 1 + C.ε
    rw [Complex.norm_real, Real.norm_of_nonneg (solidWholeRadius_pos p).le]
    exact ⟨solidWholeRadius_gt_one p, hr⟩
  have ht := C.transition_domain m hy
  change (seamModel d m (C.port (.inr m)) (C.matrix m) y).1 ∈ planarOpen d.k at ht
  have htwo : (solidAnnulusRawSeam p j (C.matrix m) y).1 ∈ planarOpen 2 := by
    rw [C.solidAnnulusSeam_eq hk m y]
    exact (congrArg planarOpen hk) ▸ ht
  have hb := (planarOpen_two_iff _).mp htwo
  have he := solidAnnulusRawSeam_norm_boundary p j (C.matrix m)
  change ‖(solidAnnulusRawSeam p j (C.matrix m) y).1‖ = _ at he
  rw [he] at hb
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false] at hb
  · linarith [hb.1]
  · linarith [hb.2]

theorem SeifertBlockCharts.solidTube_source_bound {W : CompactCarrier.{u}}
    {d : SeifertData} (C : SeifertBlockCharts W d) (hk : d.k = 2)
    (m : Fin d.fillingCount) (y : ℂ × Circle) (hy : y ∈ (C.tube m).source) :
    ‖y.1‖ ^ (d.fillingSlope m).1.natAbs < 6 := by
  rw [C.tube_source] at hy
  apply (solidWholeRadius_norm_iff _ _).mpr
  exact hy.trans_le (C.solidTubeWidth_bound hk m)

theorem SeifertBlockCharts.annulusProduct_val {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (hk : d.k = 2) (z : ℂ × Circle)
    (hz : z.1 ∈ planarOpen 2) :
    (C.annulusProduct hk (⟨z.1, hz⟩, z.2)).val =
      (C.product (⟨z.1, by rw [hk]; exact hz⟩, z.2)).val := by
  apply congrArg Subtype.val
  apply congrArg C.product
  apply Prod.ext
  · apply Subtype.ext
    exact solidOpenCongrDiffeomorph_apply (planarOpen 2) (planarOpen d.k)
      (congrArg planarOpen hk).symm ⟨z.1, hz⟩
  · rfl

theorem SeifertBlockCharts.solidProductPatch_symm_apply {W : CompactCarrier.{u}}
    {d : SeifertData} (C : SeifertBlockCharts W d) (hk : d.k = 2)
    (p : ℕ) [NeZero p] (j : Fin 2) (A : GL (Fin 2) ℤ) (y : ℂ × Circle)
    (hy : 1 < ‖y.1‖ ^ p ∧ ‖y.1‖ ^ p < 6) :
    (C.solidProductPatch hk p j A).symm y =
      (C.annulusProduct hk (⟨(solidAnnulusRawSeam p j A y).1,
        solidAnnulusRawSeam_mem_planarOpen p j A y hy⟩,
          (solidAnnulusRawSeam p j A y).2)).val := by
  let z : planarOpen 2 × Circle :=
    (⟨(solidAnnulusRawSeam p j A y).1, solidAnnulusRawSeam_mem_planarOpen p j A y hy⟩,
      (solidAnnulusRawSeam p j A y).2)
  let x := C.annulusProduct hk z
  have hx := (C.solidProductPatch_source hk p j A x).mpr x.property
  have he : C.solidProductPatch hk p j A x = y := by
    rw [C.solidProductPatch_apply hk p j A x x.property]
    have hi := (C.annulusProduct hk).symm_apply_apply z
    rw [hi]
    exact (solidAnnulusRawSeam p j A).left_inv (solidAnnulusRawSeam_source p j A y hy)
  change (C.solidProductPatch hk p j A).symm y = x.val
  rw [← he]
  exact (C.solidProductPatch hk p j A).left_inv hx

theorem SeifertBlockCharts.solidTransition_bounds {W : CompactCarrier.{u}}
    {d : SeifertData} (C : SeifertBlockCharts W d) (hk : d.k = 2)
    (m : Fin d.fillingCount) (y : ℂ × Circle) (hy : y ∈ C.transitionDomain) :
    1 < ‖y.1‖ ^ (d.fillingSlope m).1.natAbs ∧
      ‖y.1‖ ^ (d.fillingSlope m).1.natAbs < 6 := by
  rw [C.transitionDomain_eq] at hy
  constructor
  · simpa using (pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (norm_nonneg y.1) (NeZero.ne (d.fillingSlope m).1.natAbs)).mpr hy.1
  · apply (solidWholeRadius_norm_iff _ _).mpr
    exact hy.2.trans_le (C.solidTubeWidth_bound hk m)

theorem SeifertBlockCharts.solidProductPatch_transition {W : CompactCarrier.{u}}
    {d : SeifertData} (C : SeifertBlockCharts W d) (hk : d.k = 2)
    (m : Fin d.fillingCount) (y : ℂ × Circle) (hy : y ∈ C.transitionDomain) :
    (C.solidProductPatch hk (d.fillingSlope m).1.natAbs
      (Fin.cast hk (C.port (.inr m))) (C.matrix m)).symm y = C.tube m y := by
  rw [C.solidProductPatch_symm_apply hk _ _ _ y (C.solidTransition_bounds hk m y hy)]
  rw [C.annulusProduct_val]
  have he := C.solidAnnulusSeam_eq hk m y
  simp only [he]
  exact (C.transition m y hy).symm

theorem SeifertBlockCharts.solidProductPatch_forward_compatibility
    {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
    (hk : d.k = 2) (m : Fin d.fillingCount) (x : W.Carrier)
    (hp : x ∈ (C.solidProductPatch hk (d.fillingSlope m).1.natAbs
      (Fin.cast hk (C.port (.inr m))) (C.matrix m)).source)
    (ht : x ∈ (C.tube m).target) :
    C.solidProductPatch hk (d.fillingSlope m).1.natAbs
      (Fin.cast hk (C.port (.inr m))) (C.matrix m) x = (C.tube m).symm x := by
  have hx := (C.solidProductPatch_source hk _ _ _ x).mp hp
  have hi : x ∈ C.tube m '' C.transitionDomain := by
    rw [← C.tube_product_overlap]
    exact ⟨ht, hx⟩
  obtain ⟨y, hy, he⟩ := hi
  have hyTube : y ∈ (C.tube m).source := by
    rw [C.tube_source]
    have hd := hy
    rw [C.transitionDomain_eq] at hd
    exact hd.2
  have hyProduct : y ∈ (C.solidProductPatch hk (d.fillingSlope m).1.natAbs
      (Fin.cast hk (C.port (.inr m))) (C.matrix m)).target :=
    (C.solidProductPatch_target hk _ _ _ y).mpr (C.solidTransition_bounds hk m y hy)
  have hiProduct := (C.solidProductPatch_transition hk m y hy).trans he
  calc
    C.solidProductPatch hk (d.fillingSlope m).1.natAbs
        (Fin.cast hk (C.port (.inr m))) (C.matrix m) x =
      C.solidProductPatch hk (d.fillingSlope m).1.natAbs
        (Fin.cast hk (C.port (.inr m))) (C.matrix m)
          ((C.solidProductPatch hk (d.fillingSlope m).1.natAbs
            (Fin.cast hk (C.port (.inr m))) (C.matrix m)).symm y) :=
      congrArg (C.solidProductPatch hk (d.fillingSlope m).1.natAbs
        (Fin.cast hk (C.port (.inr m))) (C.matrix m)) hiProduct.symm
    _ = y := (C.solidProductPatch hk (d.fillingSlope m).1.natAbs
        (Fin.cast hk (C.port (.inr m))) (C.matrix m)).right_inv hyProduct
    _ = (C.tube m).symm x := by
      rw [← he]
      exact ((C.tube m).left_inv hyTube).symm

theorem SeifertBlockCharts.solidProductPatch_backward_compatibility
    {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
    (hk : d.k = 2) (m : Fin d.fillingCount) (y : ℂ × Circle)
    (hp : y ∈ (C.solidProductPatch hk (d.fillingSlope m).1.natAbs
      (Fin.cast hk (C.port (.inr m))) (C.matrix m)).target)
    (ht : y ∈ (C.tube m).source) :
    (C.solidProductPatch hk (d.fillingSlope m).1.natAbs
      (Fin.cast hk (C.port (.inr m))) (C.matrix m)).symm y = C.tube m y := by
  have hb := (C.solidProductPatch_target hk _ _ _ y).mp hp
  have hn : 1 < ‖y.1‖ := by
    apply (pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (norm_nonneg y.1) (NeZero.ne (d.fillingSlope m).1.natAbs)).mp
    simpa using hb.1
  apply C.solidProductPatch_transition hk m y
  rw [C.transitionDomain_eq]
  rw [C.tube_source] at ht
  exact ⟨hn, ht⟩

def SeifertBlockCharts.solidWholePatchFamily {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (hk : d.k = 2) (m : Fin d.fillingCount) (b : Bool) :
    PartialDiffeomorph W.model PlaneCircleModel W.Carrier (ℂ × Circle) ∞ :=
  if b then C.solidProductPatch hk (d.fillingSlope m).1.natAbs
    (Fin.cast hk (C.port (.inr m))) (C.matrix m) else (C.tube m).symm

def SeifertBlockCharts.singleFilledWholeInteriorDiffeomorph
    {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
    (hk : d.k = 2) (hf : d.fillingCount = 1) (m : Fin d.fillingCount) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, PlaneCircleModel⟯
      solidWholeInterior (d.fillingSlope m).1.natAbs := by
  let p := (d.fillingSlope m).1.natAbs
  let patches := C.solidWholePatchFamily hk m
  have hU : Nonempty (W.pieceInterior ⊤) := by
    obtain ⟨x⟩ := C.annulusRegion_nonempty hk
    exact ⟨⟨x, trivial, C.productRegion_interior x.property⟩⟩
  refine gluePartialDiffeomorphsOnOpens patches (W.pieceInterior ⊤) (solidWholeInterior p)
    hU (solidWholeInterior_nonempty p) ?_ ?_ ?_ ?_ ?_ ?_
  · intro b x hx
    cases b
    · exact ⟨trivial, C.tube_interior m hx⟩
    · exact ⟨trivial, C.productRegion_interior
        ((C.solidProductPatch_source hk _ _ _ x).mp hx)⟩
  · intro b y hy
    cases b
    · exact C.solidTube_source_bound hk m y hy
    · exact ((C.solidProductPatch_target hk _ _ _ y).mp hy).2
  · intro x hx
    rcases C.covers x hx.2 with hp | ⟨n, hn⟩
    · exact ⟨true, (C.solidProductPatch_source hk _ _ _ x).mpr hp⟩
    · have he : n = m := by
        apply Fin.ext
        have hm := m.isLt
        have hnlt := n.isLt
        omega
      subst n
      exact ⟨false, hn⟩
  · intro y hy
    by_cases ht : ‖y.1‖ < 1 + C.ε
    · refine ⟨false, ?_⟩
      change y ∈ (C.tube m).source
      rw [C.tube_source]
      exact ht
    · refine ⟨true, (C.solidProductPatch_target hk _ _ _ y).mpr ⟨?_, hy⟩⟩
      have hn : 1 < ‖y.1‖ := by linarith [C.ε_pos, le_of_not_gt ht]
      simpa using (pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        (norm_nonneg y.1) (NeZero.ne p)).mpr hn
  · intro b c x hb hc
    cases b <;> cases c
    · rfl
    · exact (C.solidProductPatch_forward_compatibility hk m x hc hb).symm
    · exact C.solidProductPatch_forward_compatibility hk m x hb hc
    · rfl
  · intro b c y hb hc
    cases b <;> cases c
    · rfl
    · exact (C.solidProductPatch_backward_compatibility hk m y hc hb).symm
    · exact C.solidProductPatch_backward_compatibility hk m y hb hc
    · rfl

def SeifertData.solidGeometryMultiplicity (d : SeifertData) (m : Fin d.fillingCount) : ℕ+ :=
  ⟨(d.fillingSlope m).1.natAbs, Nat.pos_of_ne_zero (NeZero.ne _)⟩

instance SeifertData.solidGeometryLengthNeZero (d : SeifertData) (m : Fin d.fillingCount) :
    Fact ((1 : ℝ) / (d.solidGeometryMultiplicity m : ℝ) ≠ 0) := ⟨by positivity⟩

def SeifertBlockCharts.singleFilledSolidTorusDiffeomorph
    {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
    (hk : d.k = 2) (hf : d.fillingCount = 1) (m : Fin d.fillingCount) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, 𝓡 3⟯
      FibredSolidTorus (d.solidGeometryMultiplicity m) (-C.a m) :=
  (C.singleFilledWholeInteriorDiffeomorph hk hf m).trans
    ((solidWholeInteriorDiffeomorph (d.fillingSlope m).1.natAbs).trans
      (solidTorusDiffeo
        (d.solidGeometryMultiplicity m) (-C.a m)).symm)

def solidTorusShapeGeometry_of_one_filling {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (h : d.IsSolidTorus) (hk : d.k = 2) :
    W.InteriorGeometry ⊤ := by
  have hf : d.fillingCount = 1 := by
    have he := d.ports_add_length_add_length
    have hp := h.1
    change d.cones.length + d.normals.length = 1
    omega
  let m : Fin d.fillingCount := ⟨0, by omega⟩
  exact interiorGeometryOfDiffeomorph
    (fibredSolidTorusGeometry .euclidean (by norm_num [ConnectionModel.baseCurvature])
      (d.solidGeometryMultiplicity m) (-C.a m))
    W ⊤ (C.singleFilledSolidTorusDiffeomorph hk hf m)

theorem solidTorusShapeGeometry_of_one_filling_model
    {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
    (h : d.IsSolidTorus) (hk : d.k = 2) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (solidTorusShapeGeometry_of_one_filling C h hk).model = .euclidean :=
  rfl

def solidTorusShapeGeometry_of_k_le_two {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (h : d.IsSolidTorus) (hk : d.k ≤ 2) :
    W.InteriorGeometry ⊤ :=
  if hn : d.fillingCount = 0 then solidTorusShapeGeometry_of_unfilled C h hn
  else solidTorusShapeGeometry_of_one_filling C h (by
    have hp := h.1
    have he := d.ports_add_length_add_length
    have hf : d.cones.length + d.normals.length ≠ 0 := hn
    omega)

theorem solidTorusShapeGeometry_of_k_le_two_model
    {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
    (h : d.IsSolidTorus) (hk : d.k ≤ 2) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (solidTorusShapeGeometry_of_k_le_two C h hk).model = .euclidean := by
  by_cases hn : d.fillingCount = 0
  · rw [solidTorusShapeGeometry_of_k_le_two, dite_eq_left hn]
    exact solidTorusShapeGeometry_of_unfilled_model C h hn
  · rw [solidTorusShapeGeometry_of_k_le_two, dite_eq_right hn]
    exact solidTorusShapeGeometry_of_one_filling_model C h _

theorem solidTorusShape_normal_of_three (d : SeifertData) (h : d.IsSolidTorus)
    (hk : d.k = 3) : 0 < d.normals.length := by
  have hp := h.1
  have hc := h.2
  have he := d.ports_add_length_add_length
  omega


section AbsorbedTubeLedger

variable {W : CompactCarrier.{u}} {d : SeifertData}

def SeifertBlockCharts.solidAbsorbedRegion (C : SeifertBlockCharts W d)
    (m : Fin d.fillingCount) : TopologicalSpace.Opens W.Carrier :=
  C.productRegion ⊔ ⟨(C.tube m).target, (C.tube m).open_target⟩

def SeifertBlockCharts.solidRetainedTube (C : SeifertBlockCharts W d)
    (n : Fin d.fillingCount) (η : ℝ) :
    PartialDiffeomorph PlaneCircleModel W.model (ℂ × Circle) W.Carrier ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.restrict (C.tube n)
    {y : ℂ × Circle | ‖y.1‖ < 1 + η}
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const)

theorem SeifertBlockCharts.solidRetainedTube_source (C : SeifertBlockCharts W d)
    (n : Fin d.fillingCount) {η : ℝ} (hη : η ≤ C.ε) :
    (C.solidRetainedTube n η).source = {y : ℂ × Circle | ‖y.1‖ < 1 + η} := by
  ext y
  change (y ∈ (C.tube n).source ∧ ‖y.1‖ < 1 + η) ↔ ‖y.1‖ < 1 + η
  rw [C.tube_source]
  exact ⟨fun hy => hy.2, fun hy => ⟨lt_of_lt_of_le hy (by linarith), hy⟩⟩

theorem SeifertBlockCharts.solidRetainedTube_target (C : SeifertBlockCharts W d)
    (n : Fin d.fillingCount) (η : ℝ) (x : W.Carrier) :
    x ∈ (C.solidRetainedTube n η).target ↔
      x ∈ (C.tube n).target ∧ ‖((C.tube n).symm x).1‖ < 1 + η := Iff.rfl

theorem SeifertBlockCharts.solidRetainedTube_apply (C : SeifertBlockCharts W d)
    (n : Fin d.fillingCount) (η : ℝ) (y : ℂ × Circle) :
    C.solidRetainedTube n η y = C.tube n y := rfl

theorem SeifertBlockCharts.solidRetainedTube_overlap (C : SeifertBlockCharts W d)
    (m n : Fin d.fillingCount) (hmn : m ≠ n) {η : ℝ} (hη : η ≤ C.ε) :
    (C.solidRetainedTube n η).target ∩ (C.solidAbsorbedRegion m : Set W.Carrier) =
      C.solidRetainedTube n η '' {y : ℂ × Circle | 1 < ‖y.1‖ ∧ ‖y.1‖ < 1 + η} := by
  ext x
  constructor
  · rintro ⟨hx, hU⟩
    rw [C.solidRetainedTube_target] at hx
    have hp : x ∈ C.productRegion := by
      rcases hU with hp | hm
      · exact hp
      · exact False.elim (Set.disjoint_left.mp (C.disjoint hmn) hm hx.1)
    have himage : x ∈ C.tube n '' C.transitionDomain :=
      C.tube_product_overlap n ▸ ⟨hx.1, hp⟩
    obtain ⟨y, hy, he⟩ := himage
    have hsrc : y ∈ (C.tube n).source := by
      rw [C.tube_source]
      exact (C.transitionDomain_eq ▸ hy).2
    have hsmall : ‖y.1‖ < 1 + η := by
      rw [← he, (C.tube n).symm_apply_apply hsrc] at hx
      exact hx.2
    exact ⟨y, ⟨(C.transitionDomain_eq ▸ hy).1, hsmall⟩, he⟩
  · rintro ⟨y, hy, he⟩
    have hsrc : y ∈ (C.solidRetainedTube n η).source :=
      C.solidRetainedTube_source n hη ▸ hy.2
    refine ⟨he ▸ (C.solidRetainedTube n η).map_source hsrc, Or.inl ?_⟩
    have htrans : y ∈ C.transitionDomain := by
      rw [C.transitionDomain_eq]
      exact ⟨hy.1, lt_of_lt_of_le hy.2 (by linarith)⟩
    have hproduct : C.tube n y ∈ C.productRegion := by
      have hmem : C.tube n y ∈ C.tube n '' C.transitionDomain := ⟨y, htrans, rfl⟩
      rw [← C.tube_product_overlap n] at hmem
      exact hmem.2
    exact he ▸ hproduct

theorem SeifertBlockCharts.solidRetainedTube_covers (C : SeifertBlockCharts W d)
    (hf : d.fillingCount = 2) (m n : Fin d.fillingCount) (hmn : m ≠ n)
    {η : ℝ} (hη0 : 0 < η) (x : W.Carrier) (hx : x ∈ W.interior) :
    x ∈ C.solidAbsorbedRegion m ∨ x ∈ (C.solidRetainedTube n η).target := by
  rcases C.covers x hx with hp | ⟨a, ha⟩
  · exact Or.inl (Or.inl hp)
  · have hamn : a = m ∨ a = n := by
      have ha := a.isLt
      have hm := m.isLt
      have hn := n.isLt
      have hne : m.val ≠ n.val := fun h => hmn (Fin.ext h)
      have he : a.val = m.val ∨ a.val = n.val := by omega
      exact he.imp Fin.ext Fin.ext
    rcases hamn with ham | han
    · subst a
      exact Or.inl (Or.inr ha)
    · subst a
      by_cases hsmall : ‖((C.tube n).symm x).1‖ < 1 + η
      · exact Or.inr ((C.solidRetainedTube_target n η x).mpr ⟨ha, hsmall⟩)
      · have hsrc := (C.tube n).map_target ha
        rw [C.tube_source] at hsrc
        have htrans : (C.tube n).symm x ∈ C.transitionDomain := by
          rw [C.transitionDomain_eq]
          exact ⟨by linarith, hsrc⟩
        have hmem : x ∈ C.tube n '' C.transitionDomain :=
          ⟨(C.tube n).symm x, htrans, (C.tube n).apply_symm_apply ha⟩
        rw [← C.tube_product_overlap n] at hmem
        exact Or.inl (Or.inl hmem.2)


end AbsorbedTubeLedger

section AbsorptionRadius

theorem exists_solidAbsorptionWidth (p : ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ η > (0 : ℝ), η ≤ ε ∧ ∀ r : ℝ, 1 < r → r < 1 + η →
      2 * (r ^ p - 1) < δ := by
  have hf : ContinuousAt (fun r : ℝ => 2 * (r ^ p - 1)) 1 :=
    continuousAt_const.mul ((continuousAt_id.pow p).sub continuousAt_const)
  obtain ⟨ρ, hρ, hclose⟩ := Metric.continuousAt_iff.mp hf δ hδ
  refine ⟨min ε ρ, lt_min hε hρ, min_le_left _ _, ?_⟩
  intro r hr hsmall
  have hd : dist r 1 < ρ := by
    rw [Real.dist_eq, abs_of_pos (by linarith : 0 < r - 1)]
    exact lt_of_lt_of_le (by linarith) (min_le_right ε ρ)
  have hh := hclose hd
  simp only [one_pow, sub_self, mul_zero, dist_zero_right, Real.norm_eq_abs] at hh
  exact lt_of_le_of_lt (le_abs_self (2 * (r ^ p - 1))) hh

def solidRetainedSlopeDatum (s : ℤ × ℤ) (hp : 0 < s.1) (hg : IsPrimitive s) :
    SeifertData where
  k := 2
  ports := 1
  cones := if s.1 = 1 then [] else [(s.1.natAbs, s.2)]
  normals := if s.1 = 1 then [s.2] else []
  one_le_k := by norm_num
  k_le_three := by norm_num
  two_le_of_mem_cones c hc := by
    by_cases hs : s.1 = 1
    · simp [hs] at hc
    · simp only [hs, ite_false, List.mem_singleton] at hc
      subst c
      have hn : (s.1.natAbs : ℤ) = s.1 := by
        rw [Int.natCast_natAbs, abs_of_pos hp]
      omega
  gcd_eq_one_of_mem_cones c hc := by
    by_cases hs : s.1 = 1
    · simp [hs] at hc
    · simp only [hs, ite_false, List.mem_singleton] at hc
      subst c
      have hn : (s.1.natAbs : ℤ) = s.1 := by
        rw [Int.natCast_natAbs, abs_of_pos hp]
      exact hn ▸ hg
  ports_add_length_add_length := by
    by_cases hs : s.1 = 1 <;> simp [hs]

theorem solidRetainedSlopeDatum_solid (s : ℤ × ℤ) (hp : 0 < s.1) (hg : IsPrimitive s) :
    (solidRetainedSlopeDatum s hp hg).IsSolidTorus := by
  constructor
  · rfl
  · by_cases hs : s.1 = 1 <;> simp [solidRetainedSlopeDatum, hs]

theorem solidRetainedSlopeDatum_fillingCount (s : ℤ × ℤ) (hp : 0 < s.1)
    (hg : IsPrimitive s) : (solidRetainedSlopeDatum s hp hg).fillingCount = 1 := by
  by_cases hs : s.1 = 1 <;> simp [solidRetainedSlopeDatum, SeifertData.fillingCount, hs]

theorem solidRetainedSlopeDatum_fillingSlope (s : ℤ × ℤ) (hp : 0 < s.1)
    (hg : IsPrimitive s) (n : Fin (solidRetainedSlopeDatum s hp hg).fillingCount) :
    (solidRetainedSlopeDatum s hp hg).fillingSlope n = s := by
  unfold SeifertData.fillingSlope
  induction n using Fin.addCases with
  | left j =>
    rw [Fin.append_left]
    by_cases hs : s.1 = 1
    · have hj : j.val < 0 := by simpa [solidRetainedSlopeDatum, hs] using j.isLt
      omega
    · have hget : (solidRetainedSlopeDatum s hp hg).cones[j] =
          (s.1.natAbs, s.2) := by
        have hm : (solidRetainedSlopeDatum s hp hg).cones[j] ∈
            (solidRetainedSlopeDatum s hp hg).cones := List.getElem_mem _
        simpa [solidRetainedSlopeDatum, hs] using hm
      rw [hget]
      exact Prod.ext (by rw [Int.natCast_natAbs, abs_of_pos hp]) rfl
  | right j =>
    rw [Fin.append_right]
    by_cases hs : s.1 = 1
    · have hget : (solidRetainedSlopeDatum s hp hg).normals[j] = s.2 := by
        have hm : (solidRetainedSlopeDatum s hp hg).normals[j] ∈
            (solidRetainedSlopeDatum s hp hg).normals := List.getElem_mem _
        simpa [solidRetainedSlopeDatum, hs] using hm
      rw [hget]
      exact Prod.ext hs.symm rfl
    · have hj : j.val < 0 := by simpa [solidRetainedSlopeDatum, hs] using j.isLt
      omega


end AbsorptionRadius

def solidAnnulusFlatProduct :
    (planarOpen 2 × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯ flatImage where
  toFun z := ⟨(z.1.val, z.2),
    mem_flatImage.mpr (planarOpen_two_iff z.1.val |>.mp z.1.property)⟩
  invFun z := (⟨z.val.1, (planarOpen_two_iff z.val.1).mpr (mem_flatImage.mp z.property)⟩, z.val.2)
  left_inv z := rfl
  right_inv z := rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff flatImage _).mp
    exact (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd
  contMDiff_invFun := by
    apply ContMDiff.prodMk
    · apply (ContMDiff.subtypeVal_comp_iff (planarOpen 2) _).mp
      exact contMDiff_fst.comp contMDiff_subtype_val
    · exact contMDiff_snd.comp contMDiff_subtype_val

def solidAnnulusInteriorProduct :
    (planarOpen 2 × Circle) ≃ₘ⟮PlaneCircleModel, annulusCircleCarrier.{u}.model⟯
      annulusCircleCarrier.{u}.pieceInterior ⊤ :=
  solidAnnulusFlatProduct.trans annulusInteriorEquiv

theorem solidAnnulusInteriorProduct_val (z : planarOpen 2 × Circle) :
    (solidAnnulusInteriorProduct.{u} z).val.val = (ULift.up z.1.val, z.2) := rfl

def solidNormalInnerPort : Fin 2 ⊕ Fin 1 ≃ Fin 3 :=
  (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3).trans (Equiv.swap (1 : Fin 3) 2)

theorem solidNormalInnerPort_filled : solidNormalInnerPort (.inr 0) = 1 := by
  change Equiv.swap (1 : Fin 3) 2 (2 : Fin 3) = 1
  simp

theorem solidNormalInnerPort_retained : solidNormalInnerPort (.inl 1) = 2 := by
  change Equiv.swap (1 : Fin 3) 2 (1 : Fin 3) = 2
  simp

variable {W : CompactCarrier.{u}} {d : SeifertData}

def SeifertBlockCharts.solidNormalReference (C : SeifertBlockCharts W d)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1) : ConeFilling where
  p := 1
  q := (d.fillingSlope m).2
  a := C.a m
  b := C.b m
  one_le := le_rfl
  det_eq := by
    have hb := C.bezout m
    rw [hn] at hb
    simpa using hb

theorem SeifertBlockCharts.solidNormalReference_matrix (C : SeifertBlockCharts W d)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1) :
    C.matrix m = (C.solidNormalReference m hn).matchingUnit := by
  apply Units.ext
  rw [C.matrix_eq m, hn]
  change !![-1, C.a m; -(d.fillingSlope m).2, C.b m] =
    (C.solidNormalReference m hn).matchingMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ConeFilling.matchingMatrix, ConeFilling.reflectMatrix, ConeFilling.chartMatrix,
      solidNormalReference, Matrix.mul_apply, Fin.sum_univ_two]

def SeifertBlockCharts.solidNormalReferenceCharts (C : SeifertBlockCharts W d)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1) :
    SeifertBlockCharts (C.solidNormalReference m hn).filledCarrier.{u}
      (normalT2IntervalDatum (d.fillingSlope m).2) :=
  (C.solidNormalReference m hn).normalInnerReferenceCharts rfl
    solidNormalInnerPort solidNormalInnerPort_filled

theorem SeifertBlockCharts.solidNormalReferenceCharts_matrix
    (C : SeifertBlockCharts W d) (m : Fin d.fillingCount)
    (hn : (d.fillingSlope m).1 = 1) :
    C.matrix m = (C.solidNormalReferenceCharts m hn).matrix 0 := by
  exact C.solidNormalReference_matrix m hn

def SeifertBlockCharts.solidInnerNormalRegionDiffeomorph
    (C : SeifertBlockCharts W d) (hk : d.k = 3)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1)
    (hport : Fin.cast hk (C.port (.inr m)) = (1 : Fin 3)) :
    C.selectedFilledRegion m ≃ₘ⟮W.model,
      (C.solidNormalReference m hn).filledCarrier.{u}.model⟯
      (C.solidNormalReference m hn).filledCarrier.{u}.pieceInterior ⊤ := by
  let D := C.solidNormalReferenceCharts m hn
  have hs : d.fillingSlope m = (normalT2IntervalDatum (d.fillingSlope m).2).fillingSlope 0 := by
    rw [normalT2IntervalDatum_fillingSlope]
    exact Prod.ext hn rfl
  have hp : Fin.cast hk (C.port (.inr m)) = D.port (.inr 0) := by
    change Fin.cast hk (C.port (.inr m)) = solidNormalInnerPort (.inr 0)
    rw [solidNormalInnerPort_filled]
    exact hport
  exact C.compareSelectedFillingInterior D hk m 0 hs hp
    (C.solidNormalReferenceCharts_matrix m hn) rfl

theorem SeifertBlockCharts.solidInnerNormalRegionDiffeomorph_product
    (C : SeifertBlockCharts W d) (hk : d.k = 3)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1)
    (hport : Fin.cast hk (C.port (.inr m)) = (1 : Fin 3))
    (z : planarOpen d.k × Circle) :
    (C.solidInnerNormalRegionDiffeomorph hk m hn hport
      ⟨C.product z, Or.inl (C.product z).property⟩).val =
        (C.solidNormalReference m hn).chartProduct
          (selectedPlanarOpenCast hk z.1, z.2) := by
  let D := C.solidNormalReferenceCharts m hn
  have hs : d.fillingSlope m = (normalT2IntervalDatum (d.fillingSlope m).2).fillingSlope 0 := by
    rw [normalT2IntervalDatum_fillingSlope]
    exact Prod.ext hn rfl
  have hp : Fin.cast hk (C.port (.inr m)) = D.port (.inr 0) := by
    change Fin.cast hk (C.port (.inr m)) = solidNormalInnerPort (.inr 0)
    rw [solidNormalInnerPort_filled]
    exact hport
  exact C.compareSelectedFillingInterior_product D hk m 0 hs hp
    (C.solidNormalReferenceCharts_matrix m hn) rfl z

def solidRemainingCollarHeight (d : SeifertData) (n : Fin d.fillingCount)
    (y : ℂ × Circle) : ℝ := 2 * (‖y.1‖ ^ (d.fillingSlope n).1.natAbs - 1)

def solidRemainingCollarParam (d : SeifertData) (n : Fin d.fillingCount)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) : Torus × EuclideanHalfSpace 1 :=
  (linearTorusMap A (unitOf y.1, y.2),
    Manifold.halfSpaceOneLift (solidRemainingCollarHeight d n y))

theorem solidRemainingCollarHeight_pos (d : SeifertData) (n : Fin d.fillingCount)
    (y : ℂ × Circle) (hy : 1 < ‖y.1‖) : 0 < solidRemainingCollarHeight d n y := by
  have hp := one_lt_pow₀ hy (NeZero.ne (d.fillingSlope n).1.natAbs)
  dsimp [solidRemainingCollarHeight]
  linarith

theorem solidRemainingCollarParam_height (d : SeifertData) (n : Fin d.fillingCount)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (hy : 1 < ‖y.1‖) :
    (solidRemainingCollarParam d n A y).2.val 0 = solidRemainingCollarHeight d n y := by
  change max (solidRemainingCollarHeight d n y) 0 = solidRemainingCollarHeight d n y
  exact max_eq_left (solidRemainingCollarHeight_pos d n y hy).le

theorem solidRemainingCollarParam_source (d : SeifertData) (n : Fin d.fillingCount)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (hy : 1 < ‖y.1‖)
    (hs : solidRemainingCollarHeight d n y < 1) :
    solidRemainingCollarParam d n A y ∈ halfCollarSource := by
  change (solidRemainingCollarParam d n A y).2.val 0 < 1
  rw [solidRemainingCollarParam_height d n A y hy]
  exact hs

theorem solidRemainingInnerSeam_collar (d : SeifertData) (n : Fin d.fillingCount)
    (hk : d.k = 3) (j : Fin d.k) (hj : Fin.cast hk j = (2 : Fin 3))
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (hy : 1 < ‖y.1‖)
    (hs : solidRemainingCollarHeight d n y < 1) :
    seamModel d n j A y =
      ((planarCollar.{u} 3 (Or.inr rfl) 2
        ((solidRemainingCollarParam d n A y).1.1,
          (solidRemainingCollarParam d n A y).2)).val.down,
        (solidRemainingCollarParam d n A y).1.2) := by
  have hjv : j.val = 2 := congrArg Fin.val hj
  have hsource := solidRemainingCollarParam_source d n A y hy hs
  have hbase : ((solidRemainingCollarParam d n A y).1.1,
      (solidRemainingCollarParam d n A y).2) ∈ circleCollarSource := hsource
  rw [planarCollar_apply_val (Or.inr rfl) 2 hbase]
  apply Prod.ext
  · simp only [seamModel, planarCollarFormula, planarCenter, planarRadius, planarSign,
      planarTwist, hk, hjv, Fin.val_two, Nat.reduceEqDiff, ite_false, ite_true]
    rw [solidRemainingCollarParam_height d n A y hy]
    simp only [solidRemainingCollarHeight, solidRemainingCollarParam, Complex.real_smul]
    push_cast
    ring
  · rfl

def SeifertBlockCharts.solidInnerAbsorbedProduct
    (C : SeifertBlockCharts W d) (hk : d.k = 3)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1)
    (hport : Fin.cast hk (C.port (.inr m)) = (1 : Fin 3))
    (e : (C.solidNormalReference m hn).filledCarrier.{u}.Carrier
      ≃ₘ⟮(C.solidNormalReference m hn).filledCarrier.{u}.model,
        annulusCircleCarrier.{u}.model⟯ annulusCircleCarrier.{u}.Carrier) :
    (planarOpen 2 × Circle) ≃ₘ⟮PlaneCircleModel, W.model⟯ C.selectedFilledRegion m :=
  solidAnnulusInteriorProduct.trans
    ((normalCarrierInteriorDiffeomorph e).symm.trans
      (C.solidInnerNormalRegionDiffeomorph hk m hn hport).symm)

theorem solidReferenceProduct_collar (c : ConeFilling) (z : planarOpen 3 × Circle)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource)
    (hz : (z.1.val, z.2) =
      ((planarCollar.{u} 3 (Or.inr rfl) 2 (p.1.1, p.2)).val.down, p.1.2)) :
    (c.chartProduct.{u} z : c.filledCarrier.{u}.Carrier) = c.externalCollar 1 p := by
  apply Subtype.ext
  rw [c.externalCollar_apply_val 1 hp]
  change c.coneLift (ULift.up z.1.val, z.2) =
    c.coneLift (productCollar.{u} 3 (Or.inr rfl) 2 p).val
  apply congrArg c.coneLift
  apply Prod.ext
  · apply ULift.ext
    exact congrArg Prod.fst hz
  · change z.2 = p.1.2
    exact congrArg Prod.snd hz

theorem SeifertBlockCharts.solidSelectedFilledRegion_interior
    (C : SeifertBlockCharts W d) (m : Fin d.fillingCount) :
    (C.selectedFilledRegion m : Set W.Carrier) ⊆ W.interior := by
  intro x hx
  rcases hx with hp | ht
  · exact C.productRegion_interior hp
  · exact C.tube_interior m ht

theorem SeifertBlockCharts.solidInnerAbsorbedProduct_transition_inner
    (C : SeifertBlockCharts W d) (hk : d.k = 3)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1)
    (hport : Fin.cast hk (C.port (.inr m)) = (1 : Fin 3))
    (e : (C.solidNormalReference m hn).filledCarrier.{u}.Carrier
      ≃ₘ⟮(C.solidNormalReference m hn).filledCarrier.{u}.model,
        annulusCircleCarrier.{u}.model⟯ annulusCircleCarrier.{u}.Carrier)
    {δ : ℝ} (hgerm : ∀ p : Torus × EuclideanHalfSpace 1,
      p ∈ halfCollarSource → p.2.val 0 < δ →
        e ((C.solidNormalReference m hn).externalCollar 1 p) =
          productCollar 2 (Or.inl rfl) 1 p)
    (n : Fin d.fillingCount) (hother : Fin.cast hk (C.port (.inr n)) = (2 : Fin 3))
    (y : ℂ × Circle) (hy : y ∈ C.transitionDomain)
    (hs : solidRemainingCollarHeight d n y < min δ 1) :
    ∃ hbase : (planarCollar.{u} 2 (Or.inl rfl) 1
      ((solidRemainingCollarParam d n (C.matrix n) y).1.1,
        (solidRemainingCollarParam d n (C.matrix n) y).2)).val.down ∈ planarOpen 2,
      (C.solidInnerAbsorbedProduct hk m hn hport e
        (⟨(planarCollar.{u} 2 (Or.inl rfl) 1
          ((solidRemainingCollarParam d n (C.matrix n) y).1.1,
            (solidRemainingCollarParam d n (C.matrix n) y).2)).val.down, hbase⟩,
          (solidRemainingCollarParam d n (C.matrix n) y).1.2)).val = C.tube n y := by
  let c := C.solidNormalReference m hn
  let p := solidRemainingCollarParam d n (C.matrix n) y
  have hy1 : 1 < ‖y.1‖ := (C.transitionDomain_eq ▸ hy).1
  have hp : p ∈ halfCollarSource :=
    solidRemainingCollarParam_source d n (C.matrix n) y hy1
      (lt_of_lt_of_le hs (min_le_right δ 1))
  have hpδ : p.2.val 0 < δ := by
    rw [solidRemainingCollarParam_height d n (C.matrix n) y hy1]
    exact lt_of_lt_of_le hs (min_le_left δ 1)
  let z : planarOpen d.k × Circle :=
    (⟨(seamModel d n (C.port (.inr n)) (C.matrix n) y).1,
      C.transition_domain n hy⟩, (seamModel d n (C.port (.inr n)) (C.matrix n) y).2)
  let x : C.selectedFilledRegion m := ⟨C.product z, Or.inl (C.product z).property⟩
  have hx : x.val = C.tube n y := (C.transition n y hy).symm
  let f := C.solidInnerNormalRegionDiffeomorph hk m hn hport
  have href : (f x).val = c.externalCollar 1 p := by
    apply (C.solidInnerNormalRegionDiffeomorph_product hk m hn hport z).trans
    apply solidReferenceProduct_collar c _ p hp
    apply Prod.ext
    · rw [selectedPlanarOpenCast_val]
      exact congrArg Prod.fst (solidRemainingInnerSeam_collar.{u} d n hk
        (C.port (.inr n)) hother (C.matrix n) y hy1 (lt_of_lt_of_le hs (min_le_right δ 1)))
    · rfl
  let P := f.trans (normalCarrierInteriorDiffeomorph e)
  have hP : (P x).val = productCollar 2 (Or.inl rfl) 1 p := by
    change e (f x).val = _
    rw [href]
    exact hgerm p hp hpδ
  let znew := solidAnnulusInteriorProduct.{u}.symm (P x)
  have hzactual : (ULift.up znew.1.val, znew.2) =
      (productCollar.{u} 2 (Or.inl rfl) 1 p).val := by
    exact (solidAnnulusInteriorProduct_val znew).symm.trans
      ((congrArg (fun a => a.val.val)
        (solidAnnulusInteriorProduct.{u}.apply_symm_apply (P x))).trans
          (congrArg Subtype.val hP))
  have hfirst : znew.1.val =
      (planarCollar.{u} 2 (Or.inl rfl) 1 (p.1.1, p.2)).val.down :=
    congrArg (fun a : PlaneLift.{u} × Circle => a.1.down) hzactual
  have hsecond : znew.2 = p.1.2 := congrArg Prod.snd hzactual
  have hbase := hfirst ▸ znew.1.property
  refine ⟨hbase, ?_⟩
  have ht : (⟨(planarCollar.{u} 2 (Or.inl rfl) 1 (p.1.1, p.2)).val.down, hbase⟩,
      p.1.2) = znew := Prod.ext (Subtype.ext hfirst.symm) hsecond.symm
  change (C.solidInnerAbsorbedProduct hk m hn hport e
    (⟨(planarCollar.{u} 2 (Or.inl rfl) 1 (p.1.1, p.2)).val.down, hbase⟩, p.1.2)).val = _
  rw [ht]
  have hQ : C.solidInnerAbsorbedProduct hk m hn hport e znew = x := by
    change P.symm (solidAnnulusInteriorProduct znew) = x
    rw [solidAnnulusInteriorProduct.apply_symm_apply]
    exact P.symm_apply_apply x
  exact (congrArg Subtype.val hQ).trans hx

theorem solidRetainedSeam_collar (d : SeifertData) (n : Fin d.fillingCount)
    (a : Fin (solidRetainedSlopeDatum (d.fillingSlope n)
      (d.fillingSlope_fst_pos n) (d.isPrimitive_fillingSlope n)).fillingCount)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (hy : 1 < ‖y.1‖)
    (hs : solidRemainingCollarHeight d n y < 1) :
    seamModel (solidRetainedSlopeDatum (d.fillingSlope n)
      (d.fillingSlope_fst_pos n) (d.isPrimitive_fillingSlope n)) a (1 : Fin 2) A y =
      ((planarCollar.{u} 2 (Or.inl rfl) 1
        ((solidRemainingCollarParam d n A y).1.1,
          (solidRemainingCollarParam d n A y).2)).val.down,
        (solidRemainingCollarParam d n A y).1.2) := by
  have hsource := solidRemainingCollarParam_source d n A y hy hs
  have hbase : ((solidRemainingCollarParam d n A y).1.1,
      (solidRemainingCollarParam d n A y).2) ∈ circleCollarSource := hsource
  rw [planarCollar_apply_val (Or.inl rfl) 1 hbase]
  apply Prod.ext
  · simp only [seamModel]
    rw [solidRetainedSlopeDatum_fillingSlope]
    simp only [solidRetainedSlopeDatum, planarCollarFormula, planarCenter, planarRadius,
      planarSign, planarTwist,
      Fin.val_one, Nat.reduceEqDiff, ite_false, ite_true]
    rw [solidRemainingCollarParam_height d n A y hy]
    simp only [solidRemainingCollarHeight, solidRemainingCollarParam, Complex.real_smul]
    push_cast
    ring
  · rfl

theorem SeifertBlockCharts.exists_solidInnerAbsorbedCharts
    (C : SeifertBlockCharts W d) (h : d.IsSolidTorus) (hk : d.k = 3)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1)
    (hport : Fin.cast hk (C.port (.inr m)) = (1 : Fin 3))
    (n : Fin d.fillingCount) (hother : Fin.cast hk (C.port (.inr n)) = (2 : Fin 3)) :
    ∃ d' : SeifertData, d'.k = 2 ∧ d'.IsSolidTorus ∧ Nonempty (SeifertBlockCharts W d') := by
  let c := C.solidNormalReference m hn
  obtain ⟨δ, hδ, e, hgerm, hfix⟩ := exists_normalConeAnnulus_inner_standard_germ.{u} c rfl
  let Q := C.solidInnerAbsorbedProduct hk m hn hport e
  let R := solidRetainedSlopeDatum (d.fillingSlope n)
    (d.fillingSlope_fst_pos n) (d.isPrimitive_fillingSlope n)
  have hR : R.fillingCount = 1 :=
    solidRetainedSlopeDatum_fillingCount _ _ _
  let port : Fin R.ports ⊕ Fin R.fillingCount ≃ Fin R.k :=
    (Equiv.sumCongr (Equiv.refl (Fin 1)) (finCongr hR)).trans finSumFinEquiv
  have hportR (a : Fin R.fillingCount) : port (.inr a) = (1 : Fin 2) := by
    apply Fin.ext
    have ha := a.isLt
    have hv : a.val = 0 := by omega
    change 1 + a.val = 1
    omega
  have hmn : m ≠ n := by
    intro he
    subst n
    rw [hport] at hother
    norm_num at hother
  have hf : d.fillingCount = 2 := by
    have hd := d.ports_add_fillingCount
    rw [h.1, hk] at hd
    omega
  obtain ⟨η, hη0, hη, hsmall⟩ := exists_solidAbsorptionWidth
    (d.fillingSlope n).1.natAbs C.ε_pos (lt_min hδ (by norm_num : (0 : ℝ) < 1))
  let U := C.selectedFilledRegion m
  let T := C.solidRetainedTube n η
  let S : Set (ℂ × Circle) := {y | 1 < ‖y.1‖ ∧ ‖y.1‖ < 1 + η}
  have hS (y : ℂ × Circle) (hy : y ∈ S) : y ∈ C.transitionDomain := by
    rw [C.transitionDomain_eq]
    exact ⟨hy.1, lt_of_lt_of_le hy.2 (by linarith)⟩
  have hcollar (y : ℂ × Circle) (hy : y ∈ S) :
      solidRemainingCollarHeight d n y < min δ 1 := hsmall ‖y.1‖ hy.1 hy.2
  have hseam (a : Fin R.fillingCount) (y : ℂ × Circle) (hy : y ∈ S) :
      seamModel R a (port (.inr a)) (C.matrix n) y =
        ((planarCollar.{u} 2 (Or.inl rfl) 1
          ((solidRemainingCollarParam d n (C.matrix n) y).1.1,
            (solidRemainingCollarParam d n (C.matrix n) y).2)).val.down,
          (solidRemainingCollarParam d n (C.matrix n) y).1.2) := by
    rw [hportR]
    exact solidRetainedSeam_collar.{u} d n a (C.matrix n) y hy.1
      (lt_of_lt_of_le (hcollar y hy) (min_le_right δ 1))
  have hdomain (a : Fin R.fillingCount) :
      Set.MapsTo (seamModel R a (port (.inr a)) (C.matrix n)) S
        {z | z.1 ∈ planarOpen 2} := by
    intro y hy
    obtain ⟨hbase, hQ⟩ := C.solidInnerAbsorbedProduct_transition_inner hk m hn hport e
      hgerm n hother y (hS y hy) (hcollar y hy)
    rw [hseam a y hy]
    exact hbase
  let D : SeifertBlockCharts W R :=
    { port := port
      matrix := Function.const _ (C.matrix n)
      a := Function.const _ (C.a n)
      b := Function.const _ (C.b n)
      matrix_eq := fun a => by
        rw [solidRetainedSlopeDatum_fillingSlope]
        exact C.matrix_eq n
      bezout := fun a => by
        rw [solidRetainedSlopeDatum_fillingSlope]
        exact C.bezout n
      productRegion := U
      productRegion_interior := C.solidSelectedFilledRegion_interior m
      product := Q
      ε := η
      ε_pos := hη0
      tube := Function.const _ T
      tube_source := fun a => C.solidRetainedTube_source n hη
      tube_interior := fun a x hx => C.tube_interior n
        ((C.solidRetainedTube_target n η x).mp hx).1
      transitionDomain := S
      transitionDomain_eq := rfl
      transition_domain := hdomain
      transition := fun a y hy => by
        obtain ⟨hbase, hQ⟩ := C.solidInnerAbsorbedProduct_transition_inner hk m hn hport e
          hgerm n hother y (hS y hy) (hcollar y hy)
        apply hQ.symm.trans
        apply congrArg (fun z => (Q z).val)
        apply Prod.ext
        · apply Subtype.ext
          exact (congrArg Prod.fst (hseam a y hy)).symm
        · exact (congrArg Prod.snd (hseam a y hy)).symm
      tube_product_overlap := fun a => C.solidRetainedTube_overlap m n hmn hη
      disjoint := fun a b hab => by
        have ha := a.isLt
        have hb := b.isLt
        have he : a = b := Fin.ext (by omega)
        exact False.elim (hab he)
      covers := fun x hx => by
        rcases C.solidRetainedTube_covers hf m n hmn hη0 x hx with hU | hT
        · exact Or.inl hU
        · exact Or.inr ⟨⟨0, by omega⟩, hT⟩ }
  exact ⟨R, rfl, solidRetainedSlopeDatum_solid _ _ _, ⟨D⟩⟩

section SolidOuterGerm

open Set Metric

open ElementaryPresentation

def retainedOuterAngle (t : Circle) : Circle :=
  unitOf (cappingPolarPoint (cappingOuterRadius t) t)

def retainedOuterAngleInverse (t : Circle) : Circle :=
  unitOf ((3 : ℂ) * (t : ℂ) + (3 / 2 : ℂ))

theorem retainedOuterAngleInverse_ne (t : Circle) :
    (3 : ℂ) * (t : ℂ) + (3 / 2 : ℂ) ≠ 0 := by
  intro he
  have h : (3 : ℂ) * (t : ℂ) = -(3 / 2 : ℂ) := by linear_combination he
  have hn := congrArg norm h
  rw [norm_mul, Circle.norm_coe, norm_neg] at hn
  norm_num at hn

theorem retainedOuterAngle_point (t : Circle) :
    (3 : ℂ) * (retainedOuterAngle t : ℂ) =
      cappingPolarPoint (cappingOuterRadius t) t := by
  have h := coe_norm_mul_unitOf (cappingPolarPoint (cappingOuterRadius t) t)
  rw [cappingPolarPoint_outer] at h
  exact h

theorem retainedOuterAngleInverse_left (t : Circle) :
    retainedOuterAngleInverse (retainedOuterAngle t) = t := by
  unfold retainedOuterAngleInverse
  rw [retainedOuterAngle_point]
  have h : cappingPolarPoint (cappingOuterRadius t) t + (3 / 2 : ℂ) =
      cappingOuterRadius t • (t : ℂ) := by
    unfold cappingPolarPoint
    push_cast
    ring
  rw [h, unitOf_smul (by linarith [cappingOuterRadius_gt_half t])]

theorem retainedOuterAngleInverse_radius (t : Circle) :
    cappingOuterRadius (retainedOuterAngleInverse t) =
      ‖(3 : ℂ) * (t : ℂ) + (3 / 2 : ℂ)‖ := by
  let z := (3 : ℂ) * (t : ℂ) + (3 / 2 : ℂ)
  let r := ‖z‖
  let v := retainedOuterAngleInverse t
  have hz : z ≠ 0 := retainedOuterAngleInverse_ne t
  have hr : 1 / 2 ≤ r := by
    have hn := norm_sub_le z (3 / 2 : ℂ)
    have he : z - (3 / 2 : ℂ) = (3 : ℂ) * (t : ℂ) := by dsimp [z]; ring
    rw [he, norm_mul, Circle.norm_coe] at hn
    norm_num at hn
    dsimp [r]
    linarith
  have hp : cappingPolarPoint r v = (3 : ℂ) * (t : ℂ) := by
    change ((-(3 / 2) : ℝ) : ℂ) + ‖z‖ • (unitOf z : ℂ) = _
    rw [norm_smul_unitOf]
    dsimp [z]
    push_cast
    ring
  have hn : ‖cappingPolarPoint r v‖ = 3 := by
    rw [hp, norm_mul, Circle.norm_coe]
    norm_num
  have he := cappingOuterRadius_eq v
  have hq := cappingPolarPoint_norm_sq r v
  rw [hn] at hq
  have hsq : 0 < cappingOuterRadius v + r - 3 * (v : ℂ).re := by
    have hs := Real.sq_sqrt (by positivity :
      0 ≤ (9 / 4) * (v : ℂ).re ^ 2 + 27 / 4)
    have hsp := Real.sqrt_nonneg ((9 / 4) * (v : ℂ).re ^ 2 + 27 / 4)
    dsimp [cappingOuterRadius]
    nlinarith
  have hprod : (r - cappingOuterRadius v) *
      (cappingOuterRadius v + r - 3 * (v : ℂ).re) = 0 := by nlinarith [he]
  have hrR := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hsq)
  change cappingOuterRadius v = r
  exact (sub_eq_zero.mp hrR).symm

theorem retainedOuterAngleInverse_right (t : Circle) :
    retainedOuterAngle (retainedOuterAngleInverse t) = t := by
  unfold retainedOuterAngle
  rw [retainedOuterAngleInverse_radius]
  change unitOf (((-(3 / 2) : ℝ) : ℂ) +
    ‖(3 : ℂ) * (t : ℂ) + (3 / 2 : ℂ)‖ •
      (unitOf ((3 : ℂ) * (t : ℂ) + (3 / 2 : ℂ)) : ℂ)) = t
  rw [norm_smul_unitOf]
  have h : ((-(3 / 2) : ℝ) : ℂ) +
      ((3 : ℂ) * (t : ℂ) + (3 / 2 : ℂ)) = (3 : ℝ) • (t : ℂ) := by
    simp [Complex.real_smul]
  rw [h, unitOf_smul (by norm_num)]

theorem retainedOuterAngle_smooth : ContMDiff (𝓡 1) (𝓡 1) ∞ retainedOuterAngle := by
  have hs : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun t : Circle => cappingPolarPoint (cappingOuterRadius t) t) :=
    contMDiff_const.add (cappingOuterRadius_smooth.smul contMDiff_circle_coe)
  exact contMDiffOn_unitOf.comp_contMDiff hs (fun t =>
    norm_pos_iff.mp (by rw [cappingPolarPoint_outer]; norm_num))

theorem retainedOuterAngleInverse_smooth :
    ContMDiff (𝓡 1) (𝓡 1) ∞ retainedOuterAngleInverse := by
  exact contMDiffOn_unitOf.comp_contMDiff
    (((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_circle_coe).add
      contMDiff_const)
    retainedOuterAngleInverse_ne

def retainedOuterAngleDiffeomorph : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toFun := retainedOuterAngle
  invFun := retainedOuterAngleInverse
  left_inv := retainedOuterAngleInverse_left
  right_inv := retainedOuterAngleInverse_right
  contMDiff_toFun := retainedOuterAngle_smooth
  contMDiff_invFun := retainedOuterAngleInverse_smooth

theorem annulusPoint_ne (x : planarSet.{u} 2) : x.val.down ≠ 0 := by
  have hx := ((mem_planarModel_two x.val.down).mp
    ((mem_planarSet_iff (Or.inl rfl) x.val).mp x.property)).2
  exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hx)

def annulusAngularMap (ψ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
    (x : planarSet.{u} 2) : planarSet.{u} 2 :=
  ⟨ULift.up (‖x.val.down‖ • (ψ (unitOf x.val.down) : ℂ)), by
    apply (mem_planarSet_iff (Or.inl rfl) _).mpr
    apply (mem_planarModel_two _).mpr
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (norm_nonneg _)]
    exact (mem_planarModel_two _).mp
      ((mem_planarSet_iff (Or.inl rfl) _).mp x.property)⟩

theorem annulusAngularMap_norm (ψ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
    (x : planarSet.{u} 2) : ‖(annulusAngularMap ψ x).val.down‖ = ‖x.val.down‖ := by
  change ‖‖x.val.down‖ • (ψ (unitOf x.val.down) : ℂ)‖ = _
  rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (norm_nonneg _)]

theorem annulusAngularMap_unitOf (ψ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
    (x : planarSet.{u} 2) : unitOf (annulusAngularMap ψ x).val.down =
      ψ (unitOf x.val.down) :=
  unitOf_smul (norm_pos_iff.mpr (annulusPoint_ne x)) _

theorem annulusAngularMap_inverse (ψ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
    (x : planarSet.{u} 2) : annulusAngularMap ψ.symm (annulusAngularMap ψ x) = x := by
  apply Subtype.ext
  apply ULift.ext
  change ‖(annulusAngularMap ψ x).val.down‖ •
    (ψ.symm (unitOf (annulusAngularMap ψ x).val.down) : ℂ) = x.val.down
  rw [annulusAngularMap_norm, annulusAngularMap_unitOf, Diffeomorph.symm_apply_apply,
    norm_smul_unitOf]

theorem annulusAngularMap_smooth (ψ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (annulusAngularMap.{u} ψ) := by
  apply ((planarAtlas 2).contMDiff_iff_subtype_val _).mpr
  intro x
  have hd := (contMDiff_planarSet_down 2).contMDiffAt (x := x)
  have hu := (contMDiffOn_unitOf.contMDiffAt
    (isOpen_ne.mem_nhds (annulusPoint_ne x))).comp x hd
  have hn := (contDiffAt_norm ℝ (annulusPoint_ne x)).contMDiffAt.comp x hd
  exact contMDiff_planeLift_up.contMDiffAt.comp x
    (hn.smul (contMDiff_circle_coe.contMDiffAt.comp x (ψ.contMDiffAt.comp x hu)))

def annulusAngularDiffeomorph (ψ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) :
    planarSet.{u} 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ planarSet.{u} 2 where
  toFun := annulusAngularMap ψ
  invFun := annulusAngularMap ψ.symm
  left_inv := annulusAngularMap_inverse ψ
  right_inv x := by
    apply Subtype.ext
    apply ULift.ext
    change ‖(annulusAngularMap ψ.symm x).val.down‖ •
      (ψ (unitOf (annulusAngularMap ψ.symm x).val.down) : ℂ) = x.val.down
    rw [annulusAngularMap_norm, annulusAngularMap_unitOf, Diffeomorph.apply_symm_apply,
      norm_smul_unitOf]
  contMDiff_toFun := annulusAngularMap_smooth ψ
  contMDiff_invFun := annulusAngularMap_smooth ψ.symm

theorem annulusAngularDiffeomorph_outer_zero
    (ψ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) (t : Circle) :
    annulusAngularDiffeomorph.{u} ψ (planarCollar.{u} 2 (Or.inl rfl) 0 (t, halfZero)) =
      planarCollar.{u} 2 (Or.inl rfl) 0 (ψ t, halfZero) := by
  apply Subtype.ext
  apply ULift.ext
  change ‖(planarCollar.{u} 2 (Or.inl rfl) 0 (t, halfZero)).val.down‖ •
    (ψ (unitOf (planarCollar.{u} 2 (Or.inl rfl) 0 (t, halfZero)).val.down) : ℂ) = _
  rw [planarCollar_zero_val, planarCollar_zero_val]
  have he (v : Circle) : planarCircleMap 2 0 v = (3 : ℝ) • (v : ℂ) := by
    simp [planarCircleMap, planarCenter, planarRadius, Complex.real_smul]
  rw [he, he, unitOf_smul (by norm_num), norm_smul, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]

def retainedOuterFibrePhase (q : ℤ) (t : Circle) : Circle :=
  unitOf ((3 : ℂ) * (t : ℂ) - (3 / 2 : ℂ)) ^ q

theorem retainedOuterFibrePhase_ne (t : Circle) :
    (3 : ℂ) * (t : ℂ) - (3 / 2 : ℂ) ≠ 0 := by
  intro he
  have h : (3 : ℂ) * (t : ℂ) = (3 / 2 : ℂ) := by linear_combination he
  have hn := congrArg norm h
  rw [norm_mul, Circle.norm_coe] at hn
  norm_num at hn

theorem retainedOuterFibrePhase_smooth (q : ℤ) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (retainedOuterFibrePhase q) := by
  exact (contMDiff_circle_zpow q).comp
    (contMDiffOn_unitOf.comp_contMDiff
      (((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_circle_coe).sub
        contMDiff_const) retainedOuterFibrePhase_ne)

def annulusOuterPhase (q : ℤ) (x : planarSet.{u} 2) : Circle :=
  retainedOuterFibrePhase q (unitOf x.val.down)

theorem annulusOuterPhase_smooth (q : ℤ) :
    ContMDiff (𝓡∂ 2) (𝓡 1) ∞ (annulusOuterPhase.{u} q) :=
  (retainedOuterFibrePhase_smooth q).comp
    (contMDiffOn_unitOf.comp_contMDiff (contMDiff_planarSet_down 2) annulusPoint_ne)

def annulusOuterUntwist (q : ℤ) :
    (planarSet.{u} 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), (𝓡∂ 2).prod (𝓡 1)⟯
      (planarSet.{u} 2 × Circle) where
  toFun x := (x.1, (annulusOuterPhase q x.1)⁻¹ * x.2)
  invFun x := (x.1, annulusOuterPhase q x.1 * x.2)
  left_inv x := by simp
  right_inv x := by simp
  contMDiff_toFun := contMDiff_fst.prodMk
    (((annulusOuterPhase_smooth q).inv.comp contMDiff_fst).mul contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk
    (((annulusOuterPhase_smooth q).comp contMDiff_fst).mul contMDiff_snd)

theorem annulusOuterPhase_zero (q : ℤ) (t : Circle) :
    annulusOuterPhase.{u} q (planarCollar.{u} 2 (Or.inl rfl) 0 (t, halfZero)) =
      retainedOuterFibrePhase q t := by
  unfold annulusOuterPhase
  rw [planarCollar_zero_val]
  have he : planarCircleMap 2 0 t = (3 : ℝ) • (t : ℂ) := by
    simp [planarCircleMap, planarCenter, planarRadius, Complex.real_smul]
  rw [he, unitOf_smul (by norm_num)]

theorem normalConeFilledDiffeomorph_outer_zero (c : ConeFilling) (hp : c.p = 1)
    (t : Torus) :
    normalConeFilledDiffeomorph c hp (c.externalCollar.{u} 0 (t, halfZero)) =
      (Merge.sectionFilling 0).externalCollar.{u} 0
        ((t.1, retainedOuterFibrePhase c.q t.1 * t.2), halfZero) := by
  apply Subtype.ext
  apply Prod.ext
  · apply ULift.ext
    have he := normalConePoint_basis c hp (c.externalCollar.{u} 0 (t, halfZero)).val
    rw [c.conePoint_externalCollar_zero, Merge.conePoint_sectionFilling] at he
    have ht := (Merge.sectionFilling 0).conePoint_externalCollar_zero.{u} 0
      (t.1, retainedOuterFibrePhase c.q t.1 * t.2)
    rw [Merge.conePoint_sectionFilling] at ht
    change (solidBasisLift false false (-c.a)
      (c.externalCollar.{u} 0 (t, halfZero)).val).1.down =
        ((Merge.sectionFilling 0).externalCollar.{u} 0
          ((t.1, retainedOuterFibrePhase c.q t.1 * t.2), halfZero)).val.1.down
    change ((3 / 2 : ℝ) : ℂ) +
      ((Merge.sectionFilling 0).externalCollar.{u} 0
        ((t.1, retainedOuterFibrePhase c.q t.1 * t.2), halfZero)).val.1.down / 6 =
          planarCircleMap 3 (ConeFilling.externalPort 0) t.1 at ht
    linear_combination (6 : ℂ) * he - (6 : ℂ) * ht
  · change (c.externalCollar.{u} 0 (t, halfZero)).val.2 =
      ((Merge.sectionFilling 0).externalCollar.{u} 0
        ((t.1, retainedOuterFibrePhase c.q t.1 * t.2), halfZero)).val.2
    rw [c.externalCollar_apply_val 0 (zero_mem_halfCollarSource t),
      (Merge.sectionFilling 0).externalCollar_apply_val 0
        (zero_mem_halfCollarSource (t.1, retainedOuterFibrePhase c.q t.1 * t.2))]
    have hs (x : PlaneLift.{u} × Circle) : (c.coneLift x).2 =
        unitOf (x.1.down - (3 / 2 : ℂ)) ^ c.q * x.2 := by
      simp [ConeFilling.coneLift, ConeFilling.coneTorus, ConeFilling.liftMatrix,
        linearTorusMap, hp]
    rw [hs, Merge.coneLift_snd_sectionFilling]
    simp only [zpow_zero, one_mul]
    change unitOf ((planarCollar.{u} 3 (Or.inr rfl) 0
      (t.1, halfZero)).val.down - (3 / 2 : ℂ)) ^ c.q * t.2 =
        retainedOuterFibrePhase c.q t.1 * t.2
    rw [planarCollar_zero_val]
    simp [retainedOuterFibrePhase, planarCircleMap, planarCenter, planarRadius]

theorem sectionCappingAnnulusProductDiffeomorph_outer_zero (t : Torus) :
    sectionCappingAnnulusProductDiffeomorph.{u} 0
      (planarCollar 2 (Or.inl rfl) 0 (t.1, halfZero), t.2) =
        (Merge.sectionFilling 0).externalCollar.{u} 0
          ((retainedOuterAngle t.1, t.2), halfZero) := by
  apply (sectionCappingDiffeomorph 0).symm.injective
  change (sectionCappingDiffeomorph 0).symm
    ((sectionCappingDiffeomorph 0)
      (cappingAnnulusDiffeomorph
        (planarCollar 2 (Or.inl rfl) 0 (t.1, halfZero)), t.2)) = _
  rw [Diffeomorph.symm_apply_apply]
  have he := sectionCappingDiffeomorph_retainedCollar.{u} 0 0
    ((retainedOuterAngle t.1, t.2), halfZero)
    (zero_mem_halfCollarSource (retainedOuterAngle t.1, t.2))
  apply Prod.ext
  · apply Subtype.ext
    apply ULift.ext
    exact (cappingAnnulusForward_outer.{u} t.1).trans (by
      have hh := he.1.symm
      change (planarCollar.{u} 3 (Or.inr rfl) 0
        (retainedOuterAngle t.1, halfZero)).val.down = _ at hh
      rw [planarCollar_zero_val] at hh
      have hp : planarCircleMap 3 0 (retainedOuterAngle t.1) =
          cappingPolarPoint (cappingOuterRadius t.1) t.1 := by
        simpa [planarCircleMap, planarCenter, planarRadius] using
          retainedOuterAngle_point t.1
      exact hp.symm.trans hh)
  · simpa using he.2.symm

theorem normalConeAnnulusDiffeomorph_outer_zero (c : ConeFilling) (hp : c.p = 1)
    (t : Torus) :
    normalConeAnnulusDiffeomorph.{u} c hp (c.externalCollar.{u} 0 (t, halfZero)) =
      productCollar 2 (Or.inl rfl) 0
        ((retainedOuterAngleInverse t.1, retainedOuterFibrePhase c.q t.1 * t.2),
          halfZero) := by
  change productDiffeomorph 2
    ((sectionCappingAnnulusProductDiffeomorph 0).symm
      (normalConeFilledDiffeomorph c hp (c.externalCollar.{u} 0 (t, halfZero)))) = _
  rw [normalConeFilledDiffeomorph_outer_zero]
  have he := sectionCappingAnnulusProductDiffeomorph_outer_zero.{u}
    (retainedOuterAngleInverse t.1, retainedOuterFibrePhase c.q t.1 * t.2)
  rw [retainedOuterAngleInverse_right] at he
  rw [← he, Diffeomorph.symm_apply_apply]
  rfl

def annulusOuterCorrection (q : ℤ) :
    annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model,
      annulusCircleCarrier.{u}.model⟯ annulusCircleCarrier.{u}.Carrier :=
  (productDiffeomorph 2).symm.trans
    ((((annulusAngularDiffeomorph retainedOuterAngleDiffeomorph).prodCongr
      (Diffeomorph.refl (𝓡 1) Circle ∞)).trans (annulusOuterUntwist q)).trans
        (productDiffeomorph 2))

theorem annulusOuterCorrection_zero (q : ℤ) (t : Torus) :
    annulusOuterCorrection.{u} q
      (productCollar 2 (Or.inl rfl) 0
        ((retainedOuterAngleInverse t.1, retainedOuterFibrePhase q t.1 * t.2),
          halfZero)) = productCollar 2 (Or.inl rfl) 0 (t, halfZero) := by
  change productDiffeomorph 2
    (annulusOuterUntwist q
      (((annulusAngularDiffeomorph retainedOuterAngleDiffeomorph).prodCongr
        (Diffeomorph.refl (𝓡 1) Circle ∞))
          ((productDiffeomorph 2).symm (productDiffeomorph 2
            (planarCollar 2 (Or.inl rfl) 0 (retainedOuterAngleInverse t.1, halfZero),
              retainedOuterFibrePhase q t.1 * t.2))))) = _
  rw [Diffeomorph.symm_apply_apply]
  change productDiffeomorph 2
    (annulusOuterUntwist q
      (annulusAngularDiffeomorph retainedOuterAngleDiffeomorph
        (planarCollar 2 (Or.inl rfl) 0 (retainedOuterAngleInverse t.1, halfZero)),
          retainedOuterFibrePhase q t.1 * t.2)) = _
  rw [annulusAngularDiffeomorph_outer_zero]
  change productDiffeomorph 2
    (annulusOuterUntwist q
      (planarCollar 2 (Or.inl rfl) 0
        (retainedOuterAngle (retainedOuterAngleInverse t.1), halfZero),
          retainedOuterFibrePhase q t.1 * t.2)) = _
  rw [retainedOuterAngleInverse_right]
  change productDiffeomorph 2
    (planarCollar 2 (Or.inl rfl) 0 (t.1, halfZero),
      (annulusOuterPhase q (planarCollar 2 (Or.inl rfl) 0 (t.1, halfZero)))⁻¹ *
        (retainedOuterFibrePhase q t.1 * t.2)) = _
  rw [annulusOuterPhase_zero, inv_mul_cancel_left]
  rfl

def normalConeAnnulusOuterDiffeomorph (c : ConeFilling) (hp : c.p = 1) :
    c.filledCarrier.{u}.Carrier ≃ₘ⟮c.filledCarrier.{u}.model,
      annulusCircleCarrier.{u}.model⟯ annulusCircleCarrier.{u}.Carrier :=
  (normalConeAnnulusDiffeomorph c hp).trans (annulusOuterCorrection c.q)

theorem normalConeAnnulusOuterDiffeomorph_zero (c : ConeFilling) (hp : c.p = 1)
    (t : Torus) :
    normalConeAnnulusOuterDiffeomorph.{u} c hp (c.externalCollar 0 (t, halfZero)) =
      productCollar 2 (Or.inl rfl) 0 (t, halfZero) := by
  change annulusOuterCorrection c.q
    (normalConeAnnulusDiffeomorph c hp (c.externalCollar 0 (t, halfZero))) = _
  rw [normalConeAnnulusDiffeomorph_outer_zero, annulusOuterCorrection_zero]

theorem exists_normalConeAnnulus_outer_standard_germ (c : ConeFilling) (hp : c.p = 1) :
    ∃ δ > (0 : ℝ), ∃ e : c.filledCarrier.{u}.Carrier ≃ₘ⟮
      c.filledCarrier.{u}.model, annulusCircleCarrier.{u}.model⟯
        annulusCircleCarrier.{u}.Carrier,
      ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource → p.2.val 0 < δ →
        e (c.externalCollar 0 p) = productCollar 2 (Or.inl rfl) 0 p := by
  let e := normalConeAnnulusOuterDiffeomorph.{u} c hp
  let B := c.external.transport e
  let c₀ := B.collar 0
  let c₁ : PartialDiffeomorph halfCollarModel annulusCircleCarrier.{u}.model
      (Torus × EuclideanHalfSpace 1) annulusCircleCarrier.{u}.Carrier ∞ :=
    productCollar.{u} 2 (Or.inl rfl) 0
  have hsrc (t : Torus) : (t, halfZero) ∈ c₀.source ∩ c₁.source := by
    constructor
    · rw [B.source_eq]
      exact zero_mem_halfCollarSource t
    · exact zero_mem_halfCollarSource t
  have h₀ (t : Torus) : c₀ (t, halfZero) = c₁ (t, halfZero) :=
    normalConeAnnulusOuterDiffeomorph_zero c hp t
  have hK : Set.range (fun t => c₀ (t, halfZero)) ⊆ c₁.target := by
    rintro x ⟨t, rfl⟩
    change c₀ (t, halfZero) ∈ c₁.target
    rw [h₀]
    exact c₁.map_source' (hsrc t).2
  obtain ⟨δ, hδ, Φ, hagree, _⟩ := exists_torusCollar_straightening c₀ c₁ hsrc h₀
    (B.boundary_zero 0) c₁.open_target hK
  refine ⟨δ, hδ, e.trans Φ, ?_⟩
  intro p hsource hsmall
  exact hagree p.1 p.2 hsmall


end SolidOuterGerm

theorem solidReferenceProduct_outer_collar (c : ConeFilling) (z : planarOpen 3 × Circle)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource)
    (hz : (z.1.val, z.2) =
      ((planarCollar.{u} 3 (Or.inr rfl) 0 (p.1.1, p.2)).val.down, p.1.2)) :
    (c.chartProduct.{u} z : c.filledCarrier.{u}.Carrier) = c.externalCollar 0 p := by
  apply Subtype.ext
  rw [c.externalCollar_apply_val 0 hp]
  change c.coneLift (ULift.up z.1.val, z.2) =
    c.coneLift (productCollar.{u} 3 (Or.inr rfl) 0 p).val
  apply congrArg c.coneLift
  apply Prod.ext
  · apply ULift.ext
    exact congrArg Prod.fst hz
  · change z.2 = p.1.2
    exact congrArg Prod.snd hz


theorem solidRemainingOuterSeam_collar (d : SeifertData) (n : Fin d.fillingCount)
    (hk : d.k = 3) (j : Fin d.k) (hj : Fin.cast hk j = (0 : Fin 3))
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (hy : 1 < ‖y.1‖)
    (hs : solidRemainingCollarHeight d n y < 1) :
    seamModel d n j A y =
      ((planarCollar.{u} 3 (Or.inr rfl) 0
        ((solidRemainingCollarParam d n A y).1.1,
          (solidRemainingCollarParam d n A y).2)).val.down,
        (solidRemainingCollarParam d n A y).1.2) := by
  have hjv : j.val = 0 := congrArg Fin.val hj
  have hsource := solidRemainingCollarParam_source d n A y hy hs
  have hbase : ((solidRemainingCollarParam d n A y).1.1,
      (solidRemainingCollarParam d n A y).2) ∈ circleCollarSource := hsource
  rw [planarCollar_apply_val (Or.inr rfl) 0 hbase]
  apply Prod.ext
  · simp only [seamModel, planarCollarFormula, planarCenter, planarRadius, planarSign,
      planarTwist, hk, hjv, Fin.val_zero, Nat.reduceEqDiff, ite_false, ite_true]
    rw [solidRemainingCollarParam_height d n A y hy]
    simp only [solidRemainingCollarHeight, solidRemainingCollarParam, Complex.real_smul]
    push_cast
    ring
  · rfl


theorem SeifertBlockCharts.solidInnerAbsorbedProduct_transition_outer
    (C : SeifertBlockCharts W d) (hk : d.k = 3)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1)
    (hport : Fin.cast hk (C.port (.inr m)) = (1 : Fin 3))
    (e : (C.solidNormalReference m hn).filledCarrier.{u}.Carrier
      ≃ₘ⟮(C.solidNormalReference m hn).filledCarrier.{u}.model,
        annulusCircleCarrier.{u}.model⟯ annulusCircleCarrier.{u}.Carrier)
    {δ : ℝ} (hgerm : ∀ p : Torus × EuclideanHalfSpace 1,
      p ∈ halfCollarSource → p.2.val 0 < δ →
        e ((C.solidNormalReference m hn).externalCollar 0 p) =
          productCollar 2 (Or.inl rfl) 0 p)
    (n : Fin d.fillingCount) (hother : Fin.cast hk (C.port (.inr n)) = (0 : Fin 3))
    (y : ℂ × Circle) (hy : y ∈ C.transitionDomain)
    (hs : solidRemainingCollarHeight d n y < min δ 1) :
    ∃ hbase : (planarCollar.{u} 2 (Or.inl rfl) 0
      ((solidRemainingCollarParam d n (C.matrix n) y).1.1,
        (solidRemainingCollarParam d n (C.matrix n) y).2)).val.down ∈ planarOpen 2,
      (C.solidInnerAbsorbedProduct hk m hn hport e
        (⟨(planarCollar.{u} 2 (Or.inl rfl) 0
          ((solidRemainingCollarParam d n (C.matrix n) y).1.1,
            (solidRemainingCollarParam d n (C.matrix n) y).2)).val.down, hbase⟩,
          (solidRemainingCollarParam d n (C.matrix n) y).1.2)).val = C.tube n y := by
  let c := C.solidNormalReference m hn
  let p := solidRemainingCollarParam d n (C.matrix n) y
  have hy1 : 1 < ‖y.1‖ := (C.transitionDomain_eq ▸ hy).1
  have hp : p ∈ halfCollarSource :=
    solidRemainingCollarParam_source d n (C.matrix n) y hy1
      (lt_of_lt_of_le hs (min_le_right δ 1))
  have hpδ : p.2.val 0 < δ := by
    rw [solidRemainingCollarParam_height d n (C.matrix n) y hy1]
    exact lt_of_lt_of_le hs (min_le_left δ 1)
  let z : planarOpen d.k × Circle :=
    (⟨(seamModel d n (C.port (.inr n)) (C.matrix n) y).1,
      C.transition_domain n hy⟩, (seamModel d n (C.port (.inr n)) (C.matrix n) y).2)
  let x : C.selectedFilledRegion m := ⟨C.product z, Or.inl (C.product z).property⟩
  have hx : x.val = C.tube n y := (C.transition n y hy).symm
  let f := C.solidInnerNormalRegionDiffeomorph hk m hn hport
  have href : (f x).val = c.externalCollar 0 p := by
    apply (C.solidInnerNormalRegionDiffeomorph_product hk m hn hport z).trans
    apply solidReferenceProduct_outer_collar c _ p hp
    apply Prod.ext
    · rw [selectedPlanarOpenCast_val]
      exact congrArg Prod.fst (solidRemainingOuterSeam_collar.{u} d n hk
        (C.port (.inr n)) hother (C.matrix n) y hy1 (lt_of_lt_of_le hs (min_le_right δ 1)))
    · rfl
  let P := f.trans (normalCarrierInteriorDiffeomorph e)
  have hP : (P x).val = productCollar 2 (Or.inl rfl) 0 p := by
    change e (f x).val = _
    rw [href]
    exact hgerm p hp hpδ
  let znew := solidAnnulusInteriorProduct.{u}.symm (P x)
  have hzactual : (ULift.up znew.1.val, znew.2) =
      (productCollar.{u} 2 (Or.inl rfl) 0 p).val := by
    exact (solidAnnulusInteriorProduct_val znew).symm.trans
      ((congrArg (fun a => a.val.val)
        (solidAnnulusInteriorProduct.{u}.apply_symm_apply (P x))).trans
          (congrArg Subtype.val hP))
  have hfirst : znew.1.val =
      (planarCollar.{u} 2 (Or.inl rfl) 0 (p.1.1, p.2)).val.down :=
    congrArg (fun a : PlaneLift.{u} × Circle => a.1.down) hzactual
  have hsecond : znew.2 = p.1.2 := congrArg Prod.snd hzactual
  have hbase := hfirst ▸ znew.1.property
  refine ⟨hbase, ?_⟩
  have ht : (⟨(planarCollar.{u} 2 (Or.inl rfl) 0 (p.1.1, p.2)).val.down, hbase⟩,
      p.1.2) = znew := Prod.ext (Subtype.ext hfirst.symm) hsecond.symm
  change (C.solidInnerAbsorbedProduct hk m hn hport e
    (⟨(planarCollar.{u} 2 (Or.inl rfl) 0 (p.1.1, p.2)).val.down, hbase⟩, p.1.2)).val = _
  rw [ht]
  have hQ : C.solidInnerAbsorbedProduct hk m hn hport e znew = x := by
    change P.symm (solidAnnulusInteriorProduct znew) = x
    rw [solidAnnulusInteriorProduct.apply_symm_apply]
    exact P.symm_apply_apply x
  exact (congrArg Subtype.val hQ).trans hx


theorem solidRetainedOuterSeam_collar (d : SeifertData) (n : Fin d.fillingCount)
    (a : Fin (solidRetainedSlopeDatum (d.fillingSlope n)
      (d.fillingSlope_fst_pos n) (d.isPrimitive_fillingSlope n)).fillingCount)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (hy : 1 < ‖y.1‖)
    (hs : solidRemainingCollarHeight d n y < 1) :
    seamModel (solidRetainedSlopeDatum (d.fillingSlope n)
      (d.fillingSlope_fst_pos n) (d.isPrimitive_fillingSlope n)) a (0 : Fin 2) A y =
      ((planarCollar.{u} 2 (Or.inl rfl) 0
        ((solidRemainingCollarParam d n A y).1.1,
          (solidRemainingCollarParam d n A y).2)).val.down,
        (solidRemainingCollarParam d n A y).1.2) := by
  have hsource := solidRemainingCollarParam_source d n A y hy hs
  have hbase : ((solidRemainingCollarParam d n A y).1.1,
      (solidRemainingCollarParam d n A y).2) ∈ circleCollarSource := hsource
  rw [planarCollar_apply_val (Or.inl rfl) 0 hbase]
  apply Prod.ext
  · simp only [seamModel]
    rw [solidRetainedSlopeDatum_fillingSlope]
    simp only [solidRetainedSlopeDatum, planarCollarFormula, planarCenter, planarRadius,
      planarSign, planarTwist,
      Fin.val_zero, Nat.reduceEqDiff, ite_false, ite_true]
    rw [solidRemainingCollarParam_height d n A y hy]
    simp only [solidRemainingCollarHeight, solidRemainingCollarParam, Complex.real_smul]
    push_cast
    ring
  · rfl


theorem SeifertBlockCharts.exists_solidInnerOuterAbsorbedCharts
    (C : SeifertBlockCharts W d) (h : d.IsSolidTorus) (hk : d.k = 3)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1)
    (hport : Fin.cast hk (C.port (.inr m)) = (1 : Fin 3))
    (n : Fin d.fillingCount) (hother : Fin.cast hk (C.port (.inr n)) = (0 : Fin 3)) :
    ∃ d' : SeifertData, d'.k = 2 ∧ d'.IsSolidTorus ∧ Nonempty (SeifertBlockCharts W d') := by
  let c := C.solidNormalReference m hn
  obtain ⟨δ, hδ, e, hgerm⟩ := exists_normalConeAnnulus_outer_standard_germ.{u} c rfl
  let Q := C.solidInnerAbsorbedProduct hk m hn hport e
  let R := solidRetainedSlopeDatum (d.fillingSlope n)
    (d.fillingSlope_fst_pos n) (d.isPrimitive_fillingSlope n)
  have hR : R.fillingCount = 1 :=
    solidRetainedSlopeDatum_fillingCount _ _ _
  let port : Fin R.ports ⊕ Fin R.fillingCount ≃ Fin R.k :=
    ((Equiv.sumCongr (Equiv.refl (Fin 1)) (finCongr hR)).trans finSumFinEquiv).trans
      (Equiv.swap (0 : Fin 2) 1)
  have hportR (a : Fin R.fillingCount) : port (.inr a) = (0 : Fin 2) := by
    have ha := a.isLt
    have hv : a.val = 0 := by omega
    have he : finSumFinEquiv
        ((Equiv.sumCongr (Equiv.refl (Fin 1)) (finCongr hR)) (.inr a)) =
          (1 : Fin 2) := Fin.ext (by change 1 + a.val = 1; omega)
    change Equiv.swap (0 : Fin 2) 1
      (finSumFinEquiv ((Equiv.sumCongr (Equiv.refl (Fin 1)) (finCongr hR)) (.inr a))) = 0
    rw [he]
    simp
  have hmn : m ≠ n := by
    intro he
    subst n
    rw [hport] at hother
    norm_num at hother
  have hf : d.fillingCount = 2 := by
    have hd := d.ports_add_fillingCount
    rw [h.1, hk] at hd
    omega
  obtain ⟨η, hη0, hη, hsmall⟩ := exists_solidAbsorptionWidth
    (d.fillingSlope n).1.natAbs C.ε_pos (lt_min hδ (by norm_num : (0 : ℝ) < 1))
  let U := C.selectedFilledRegion m
  let T := C.solidRetainedTube n η
  let S : Set (ℂ × Circle) := {y | 1 < ‖y.1‖ ∧ ‖y.1‖ < 1 + η}
  have hS (y : ℂ × Circle) (hy : y ∈ S) : y ∈ C.transitionDomain := by
    rw [C.transitionDomain_eq]
    exact ⟨hy.1, lt_of_lt_of_le hy.2 (by linarith)⟩
  have hcollar (y : ℂ × Circle) (hy : y ∈ S) :
      solidRemainingCollarHeight d n y < min δ 1 := hsmall ‖y.1‖ hy.1 hy.2
  have hseam (a : Fin R.fillingCount) (y : ℂ × Circle) (hy : y ∈ S) :
      seamModel R a (port (.inr a)) (C.matrix n) y =
        ((planarCollar.{u} 2 (Or.inl rfl) 0
          ((solidRemainingCollarParam d n (C.matrix n) y).1.1,
            (solidRemainingCollarParam d n (C.matrix n) y).2)).val.down,
          (solidRemainingCollarParam d n (C.matrix n) y).1.2) := by
    rw [hportR]
    exact solidRetainedOuterSeam_collar.{u} d n a (C.matrix n) y hy.1
      (lt_of_lt_of_le (hcollar y hy) (min_le_right δ 1))
  have hdomain (a : Fin R.fillingCount) :
      Set.MapsTo (seamModel R a (port (.inr a)) (C.matrix n)) S
        {z | z.1 ∈ planarOpen 2} := by
    intro y hy
    obtain ⟨hbase, hQ⟩ := C.solidInnerAbsorbedProduct_transition_outer hk m hn hport e
      hgerm n hother y (hS y hy) (hcollar y hy)
    rw [hseam a y hy]
    exact hbase
  let D : SeifertBlockCharts W R :=
    { port := port
      matrix := Function.const _ (C.matrix n)
      a := Function.const _ (C.a n)
      b := Function.const _ (C.b n)
      matrix_eq := fun a => by
        rw [solidRetainedSlopeDatum_fillingSlope]
        exact C.matrix_eq n
      bezout := fun a => by
        rw [solidRetainedSlopeDatum_fillingSlope]
        exact C.bezout n
      productRegion := U
      productRegion_interior := C.solidSelectedFilledRegion_interior m
      product := Q
      ε := η
      ε_pos := hη0
      tube := Function.const _ T
      tube_source := fun a => C.solidRetainedTube_source n hη
      tube_interior := fun a x hx => C.tube_interior n
        ((C.solidRetainedTube_target n η x).mp hx).1
      transitionDomain := S
      transitionDomain_eq := rfl
      transition_domain := hdomain
      transition := fun a y hy => by
        obtain ⟨hbase, hQ⟩ := C.solidInnerAbsorbedProduct_transition_outer hk m hn hport e
          hgerm n hother y (hS y hy) (hcollar y hy)
        apply hQ.symm.trans
        apply congrArg (fun z => (Q z).val)
        apply Prod.ext
        · apply Subtype.ext
          exact (congrArg Prod.fst (hseam a y hy)).symm
        · exact (congrArg Prod.snd (hseam a y hy)).symm
      tube_product_overlap := fun a => C.solidRetainedTube_overlap m n hmn hη
      disjoint := fun a b hab => by
        have ha := a.isLt
        have hb := b.isLt
        have he : a = b := Fin.ext (by omega)
        exact False.elim (hab he)
      covers := fun x hx => by
        rcases C.solidRetainedTube_covers hf m n hmn hη0 x hx with hU | hT
        · exact Or.inl hU
        · exact Or.inr ⟨⟨0, by omega⟩, hT⟩ }
  exact ⟨R, rfl, solidRetainedSlopeDatum_solid _ _ _, ⟨D⟩⟩


def solidPantsSwap (hk : d.k = 3) : Fin d.k ≃ Fin d.k :=
  (finCongr hk).trans ((Equiv.swap (1 : Fin 3) 2).trans (finCongr hk).symm)

theorem solidPantsSwap_cast (hk : d.k = 3) (j : Fin d.k) :
    Fin.cast hk (solidPantsSwap hk j) = Equiv.swap (1 : Fin 3) 2 (Fin.cast hk j) := rfl

theorem solidPantsOpen_neg_mem (hk : d.k = 3) {z : ℂ} (hz : z ∈ planarOpen d.k) :
    -z ∈ planarOpen d.k := by
  rw [hk] at hz ⊢
  exact normalPantsOpen_neg_mem hz

def solidPantsOpenNeg (hk : d.k = 3) :
    planarOpen d.k ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ planarOpen d.k where
  toFun z := ⟨-z.val, solidPantsOpen_neg_mem hk z.property⟩
  invFun z := ⟨-z.val, solidPantsOpen_neg_mem hk z.property⟩
  left_inv z := Subtype.ext (neg_neg z.val)
  right_inv z := Subtype.ext (neg_neg z.val)
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff (planarOpen d.k) _).mp (contMDiff_subtype_val.neg)
  contMDiff_invFun :=
    (ContMDiff.subtypeVal_comp_iff (planarOpen d.k) _).mp (contMDiff_subtype_val.neg)

def solidPantsProductNeg (hk : d.k = 3) :
    (planarOpen d.k × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯
      (planarOpen d.k × Circle) :=
  (solidPantsOpenNeg hk).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)

theorem solidPantsProductNeg_val (hk : d.k = 3) (z : planarOpen d.k × Circle) :
    ((solidPantsProductNeg hk z).1.val, (solidPantsProductNeg hk z).2) =
      (-z.1.val, z.2) := rfl

theorem solidPantsSeamNeg (hk : d.k = 3) (m : Fin d.fillingCount) (j : Fin d.k)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (hy : y.1 ≠ 0) :
    (-(seamModel d m (solidPantsSwap hk j) A y).1,
      (seamModel d m (solidPantsSwap hk j) A y).2) =
      seamModel d m j A (normalTubeTranslation (normalPantsTubeNegation A) y) := by
  let v := normalPantsTubeNegation A
  have ht : linearTorusMap A
      (unitOf (normalTubeTranslation v y).1, (normalTubeTranslation v y).2) =
        (circleI ^ 2, 1) * linearTorusMap A (unitOf y.1, y.2) := by
    change linearTorusMap A (unitOf ((v.1 : ℂ) * y.1), v.2 * y.2) = _
    rw [unitOf_mul (Circle.coe_ne_zero v.1) hy, unitOf_circle]
    change linearTorusMap A (v * (unitOf y.1, y.2)) = _
    rw [normalLinearTorusMap_mul_point, normalPantsTubeNegation_image]
  have hjlt : j.val < 3 := hk ▸ j.isLt
  have hcast := solidPantsSwap_cast hk j
  have hzero : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
  rcases hzero with hj | hj | hj
  all_goals
    have hsval : (solidPantsSwap hk j).val =
        (Equiv.swap (1 : Fin 3) 2 (Fin.cast hk j)).val := congrArg Fin.val hcast
    have hje : Fin.cast hk j = ⟨j.val, hjlt⟩ := rfl
    rw [hje] at hsval
    simp only [hj] at hsval
    norm_num [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1)
      (by decide : (0 : Fin 3) ≠ 2)] at hsval
    dsimp only [v] at ht
    simp only [seamModel, normalTubeTranslation_norm, ht, Prod.fst_mul,
      Prod.snd_mul, one_mul, planarCenter, planarRadius, hk, hj, hsval,
      Nat.reduceEqDiff, ite_true, ite_false, Circle.coe_mul, circleI_sq_coe,
      neg_one_mul, map_neg]
    apply Prod.ext
    · push_cast
      ring
    · rfl

def SeifertBlockCharts.solidPantsTranslatedTube (C : SeifertBlockCharts W d)
    (m : Fin d.fillingCount) :
    PartialDiffeomorph PlaneCircleModel W.model (ℂ × Circle) W.Carrier ∞ :=
  (normalTubeTranslation (normalPantsTubeNegation (C.matrix m))).toPartialDiffeomorph.trans
    (C.tube m)

theorem SeifertBlockCharts.solidPantsTranslatedTube_source (C : SeifertBlockCharts W d)
    (m : Fin d.fillingCount) :
    (C.solidPantsTranslatedTube m).source = {y : ℂ × Circle | ‖y.1‖ < 1 + C.ε} := by
  ext y
  change (y ∈ Set.univ ∧ normalTubeTranslation (normalPantsTubeNegation (C.matrix m)) y ∈
    (C.tube m).source) ↔ _
  rw [C.tube_source]
  simp only [Set.mem_univ, true_and, Set.mem_ofPred_eq, normalTubeTranslation_norm]

theorem SeifertBlockCharts.solidPantsTranslatedTube_target (C : SeifertBlockCharts W d)
    (m : Fin d.fillingCount) : (C.solidPantsTranslatedTube m).target = (C.tube m).target := by
  ext x
  change (x ∈ (C.tube m).target ∧ (C.tube m).symm x ∈ Set.univ) ↔ _
  simp only [Set.mem_univ, and_true]

def SeifertBlockCharts.solidPantsReflected (C : SeifertBlockCharts W d) (hk : d.k = 3) :
    SeifertBlockCharts W d where
  port := C.port.trans (solidPantsSwap hk)
  matrix := C.matrix
  a := C.a
  b := C.b
  matrix_eq := C.matrix_eq
  bezout := C.bezout
  productRegion := C.productRegion
  productRegion_interior := C.productRegion_interior
  product := (solidPantsProductNeg hk).trans C.product
  ε := C.ε
  ε_pos := C.ε_pos
  tube := C.solidPantsTranslatedTube
  tube_source := C.solidPantsTranslatedTube_source
  tube_interior m := C.solidPantsTranslatedTube_target m ▸ C.tube_interior m
  transitionDomain := C.transitionDomain
  transitionDomain_eq := C.transitionDomain_eq
  transition_domain m y hy := by
    let Q := normalTubeTranslation (normalPantsTubeNegation (C.matrix m))
    have hQ : Q y ∈ C.transitionDomain := by
      rw [C.transitionDomain_eq] at hy ⊢
      simpa only [Q, Set.mem_ofPred_eq, normalTubeTranslation_norm] using hy
    have hold := C.transition_domain m hQ
    have hnorm : y.1 ≠ 0 := by
      rw [C.transitionDomain_eq] at hy
      exact norm_pos_iff.mp (by linarith [hy.1])
    have hs := congrArg Prod.fst (solidPantsSeamNeg hk m (C.port (.inr m))
      (C.matrix m) y hnorm)
    let z : planarOpen d.k := ⟨(seamModel d m (C.port (.inr m)) (C.matrix m) (Q y)).1,
      hold⟩
    have hn := (solidPantsProductNeg hk (z, y.2)).1.property
    change (seamModel d m (solidPantsSwap hk (C.port (.inr m))) (C.matrix m) y).1 ∈
      planarOpen d.k
    have hv := congrArg Prod.fst (solidPantsProductNeg_val hk (z, y.2))
    dsimp only [Prod.fst] at hv
    rw [hv] at hn
    change -(seamModel d m (C.port (.inr m)) (C.matrix m) (Q y)).1 ∈ planarOpen d.k at hn
    dsimp only [Prod.fst] at hs
    have he : -(seamModel d m (C.port (.inr m)) (C.matrix m) (Q y)).1 =
        (seamModel d m (solidPantsSwap hk (C.port (.inr m))) (C.matrix m) y).1 := by
      change -(seamModel d m (C.port (.inr m)) (C.matrix m)
        (normalTubeTranslation (normalPantsTubeNegation (C.matrix m)) y)).1 = _
      rw [← hs, neg_neg]
    exact he ▸ hn
  transition m y hy := by
    let Q := normalTubeTranslation (normalPantsTubeNegation (C.matrix m))
    have hQ : Q y ∈ C.transitionDomain := by
      rw [C.transitionDomain_eq] at hy ⊢
      simpa only [Q, Set.mem_ofPred_eq, normalTubeTranslation_norm] using hy
    have hold := C.transition m (Q y) hQ
    change C.tube m (Q y) = _
    rw [hold]
    change (C.product _ : W.Carrier) = (C.product _ : W.Carrier)
    apply congrArg (fun z : planarOpen d.k × Circle => (C.product z : W.Carrier))
    have hnorm : y.1 ≠ 0 := by
      rw [C.transitionDomain_eq] at hy
      exact norm_pos_iff.mp (by linarith [hy.1])
    have hs := solidPantsSeamNeg hk m (C.port (.inr m)) (C.matrix m) y hnorm
    apply Prod.ext
    · apply Subtype.ext
      exact (congrArg Prod.fst hs).symm
    · exact (congrArg Prod.snd hs).symm
  tube_product_overlap m := by
    rw [C.solidPantsTranslatedTube_target, C.tube_product_overlap m]
    ext x
    constructor
    · rintro ⟨y, hy, hx⟩
      let Q := normalTubeTranslation (normalPantsTubeNegation (C.matrix m))
      refine ⟨Q.symm y, ?_, ?_⟩
      · rw [C.transitionDomain_eq] at hy ⊢
        have hn : ‖(Q.symm y).1‖ = ‖y.1‖ := by
          rw [← normalTubeTranslation_norm (normalPantsTubeNegation (C.matrix m))
            (Q.symm y), Q.apply_symm_apply]
        simpa only [Set.mem_ofPred_eq, hn] using hy
      · change C.tube m (Q (Q.symm y)) = x
        rw [Q.apply_symm_apply]
        exact hx
    · rintro ⟨y, hy, hx⟩
      refine ⟨normalTubeTranslation (normalPantsTubeNegation (C.matrix m)) y, ?_, hx⟩
      rw [C.transitionDomain_eq] at hy ⊢
      simpa only [Set.mem_ofPred_eq, normalTubeTranslation_norm] using hy
  disjoint m n hmn := by
    change Disjoint (C.solidPantsTranslatedTube m).target (C.solidPantsTranslatedTube n).target
    rw [C.solidPantsTranslatedTube_target, C.solidPantsTranslatedTube_target]
    exact C.disjoint hmn
  covers x hx := by
    rcases C.covers x hx with hp | ⟨m, hm⟩
    · exact Or.inl hp
    · exact Or.inr ⟨m, C.solidPantsTranslatedTube_target m ▸ hm⟩


theorem SeifertBlockCharts.solidPantsReflected_port_cast (C : SeifertBlockCharts W d)
    (hk : d.k = 3) (m : Fin d.fillingCount) :
    Fin.cast hk ((C.solidPantsReflected hk).port (.inr m)) =
      Equiv.swap (1 : Fin 3) 2 (Fin.cast hk (C.port (.inr m))) :=
  solidPantsSwap_cast hk (C.port (.inr m))

theorem SeifertBlockCharts.exists_solidInnerOneAbsorbedCharts
    (C : SeifertBlockCharts W d) (h : d.IsSolidTorus) (hk : d.k = 3)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1)
    (hport : Fin.cast hk (C.port (.inr m)) = (1 : Fin 3)) :
    ∃ d' : SeifertData, d'.k = 2 ∧ d'.IsSolidTorus ∧ Nonempty (SeifertBlockCharts W d') := by
  have hf : d.fillingCount = 2 := by
    have hd := d.ports_add_fillingCount
    rw [h.1, hk] at hd
    omega
  let n : Fin d.fillingCount := ⟨if m.val = 0 then 1 else 0, by
    have hm := m.isLt
    split <;> omega⟩
  have hmn : m ≠ n := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [n] at hv
    split at hv <;> omega
  have hpne : Fin.cast hk (C.port (.inr n)) ≠ (1 : Fin 3) := by
    intro he
    have heq : C.port (.inr m) = C.port (.inr n) := Fin.ext
      (congrArg (fun j : Fin 3 => j.val) (hport.trans he.symm))
    exact hmn (Sum.inr.inj (C.port.injective heq))
  have hpval := (Fin.cast hk (C.port (.inr n))).isLt
  have hcases : Fin.cast hk (C.port (.inr n)) = (0 : Fin 3) ∨
      Fin.cast hk (C.port (.inr n)) = (2 : Fin 3) := by
    have hvne : (C.port (.inr n)).val ≠ 1 := by
      intro he
      exact hpne (Fin.ext he)
    rcases (show (C.port (.inr n)).val = 0 ∨ (C.port (.inr n)).val = 2 by omega) with he | he
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Fin.ext he)
  rcases hcases with hp | hp
  · exact C.exists_solidInnerOuterAbsorbedCharts h hk m hn hport n hp
  · exact C.exists_solidInnerAbsorbedCharts h hk m hn hport n hp

theorem SeifertBlockCharts.exists_solidInnerNormalAbsorbedCharts
    (C : SeifertBlockCharts W d) (h : d.IsSolidTorus) (hk : d.k = 3)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1)
    (hport : Fin.cast hk (C.port (.inr m)) ≠ (0 : Fin 3)) :
    ∃ d' : SeifertData, d'.k = 2 ∧ d'.IsSolidTorus ∧ Nonempty (SeifertBlockCharts W d') := by
  have hv := (Fin.cast hk (C.port (.inr m))).isLt
  have hvne : (C.port (.inr m)).val ≠ 0 := by
    intro he
    exact hport (Fin.ext he)
  have hcases : Fin.cast hk (C.port (.inr m)) = (1 : Fin 3) ∨
      Fin.cast hk (C.port (.inr m)) = (2 : Fin 3) := by
    rcases (show (C.port (.inr m)).val = 1 ∨ (C.port (.inr m)).val = 2 by omega) with he | he
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Fin.ext he)
  rcases hcases with hp | hp
  · exact C.exists_solidInnerOneAbsorbedCharts h hk m hn hp
  · let D := C.solidPantsReflected hk
    have hD : Fin.cast hk (D.port (.inr m)) = (1 : Fin 3) := by
      rw [C.solidPantsReflected_port_cast hk m, hp, Equiv.swap_apply_right]
    exact D.exists_solidInnerOneAbsorbedCharts h hk m hn hD

def solidTorusShapeGeometryOfReduction
    (H : ∃ d' : SeifertData, d'.k = 2 ∧ d'.IsSolidTorus ∧
      Nonempty (SeifertBlockCharts W d')) : W.InteriorGeometry ⊤ :=
  let d' := Classical.choose H
  let h' := Classical.choose_spec H
  let D : SeifertBlockCharts W d' := Classical.choice h'.2.2
  solidTorusShapeGeometry_of_k_le_two D h'.2.1 (Nat.le_of_eq h'.1)

theorem solidTorusShapeGeometryOfReduction_model
    (H : ∃ d' : SeifertData, d'.k = 2 ∧ d'.IsSolidTorus ∧
      Nonempty (SeifertBlockCharts W d')) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (solidTorusShapeGeometryOfReduction H).model = .euclidean :=
  solidTorusShapeGeometry_of_k_le_two_model
    (Classical.choice (Classical.choose_spec H).2.2)
    (Classical.choose_spec H).2.1 (Nat.le_of_eq (Classical.choose_spec H).1)

def solidTorusShapeGeometry_of_inner_normal
    (C : SeifertBlockCharts W d) (h : d.IsSolidTorus) (hk : d.k = 3)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1)
    (hport : Fin.cast hk (C.port (.inr m)) ≠ (0 : Fin 3)) : W.InteriorGeometry ⊤ :=
  solidTorusShapeGeometryOfReduction
    (C.exists_solidInnerNormalAbsorbedCharts h hk m hn hport)

theorem solidTorusShapeGeometry_of_inner_normal_model
    (C : SeifertBlockCharts W d) (h : d.IsSolidTorus) (hk : d.k = 3)
    (m : Fin d.fillingCount) (hn : (d.fillingSlope m).1 = 1)
    (hport : Fin.cast hk (C.port (.inr m)) ≠ (0 : Fin 3)) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (solidTorusShapeGeometry_of_inner_normal C h hk m hn hport).model = .euclidean :=
  solidTorusShapeGeometryOfReduction_model _

def solidPantsInteriorProduct :
    (planarOpen 3 × Circle) ≃ₘ⟮PlaneCircleModel, (productCarrier.{u} 3 (Or.inr rfl)).model⟯
      (productCarrier.{u} 3 (Or.inr rfl)).pieceInterior ⊤ :=
  (productFibredPiece.{u} 3 (Or.inr rfl)).chartPieceInteriorDiffeomorph

theorem solidPantsInteriorProduct_val (z : planarOpen 3 × Circle) :
    (solidPantsInteriorProduct.{u} z).val.val = (ULift.up z.1.val, z.2) := by
  let F := productFibredPiece.{u} 3 (Or.inr rfl)
  let x := F.base.chartInteriorDiffeomorph.symm z.1
  have h := F.chartPieceInteriorDiffeomorph_apply (x, z.2)
  have hx := F.base.chartInteriorDiffeomorph_apply x
  rw [Diffeomorph.apply_symm_apply] at h hx
  have hval : x.val.val = ULift.up z.1.val := by
    apply ULift.ext
    exact hx.symm
  have hraw := congrArg Subtype.val h
  change (solidPantsInteriorProduct z).val.val = (x.val.val, z.2) at hraw
  rw [hval] at hraw
  exact hraw



def solidPantsInteriorPermutation
    (P : (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (𝓡∂ 2).prod (𝓡 1)⟯ (planarSet.{u} 3 × Circle)) :
    (planarOpen 3 × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯
      (planarOpen 3 × Circle) :=
  solidPantsInteriorProduct.trans
    ((normalCarrierInteriorDiffeomorph
      (W := productCarrier.{u} 3 (Or.inr rfl)) (V := productCarrier.{u} 3 (Or.inr rfl))
      ((productDiffeomorph 3).symm.trans (P.trans (productDiffeomorph 3)))).trans
        solidPantsInteriorProduct.symm)

theorem solidPantsInteriorPermutation_compact
    (P : (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (𝓡∂ 2).prod (𝓡 1)⟯ (planarSet.{u} 3 × Circle)) (z : planarOpen 3 × Circle) :
    (productDiffeomorph 3).symm
      (solidPantsInteriorProduct (solidPantsInteriorPermutation P z)).val =
        P ((productDiffeomorph 3).symm (solidPantsInteriorProduct z).val) := by
  change (productDiffeomorph 3).symm
    (solidPantsInteriorProduct
      (solidPantsInteriorProduct.symm
        (normalCarrierInteriorDiffeomorph
          (W := productCarrier.{u} 3 (Or.inr rfl)) (V := productCarrier.{u} 3 (Or.inr rfl))
          ((productDiffeomorph 3).symm.trans (P.trans (productDiffeomorph 3)))
            (solidPantsInteriorProduct z)))).val = _
  rw [Diffeomorph.apply_symm_apply]
  change (productDiffeomorph 3).symm
    (productDiffeomorph 3 (P ((productDiffeomorph 3).symm
      (solidPantsInteriorProduct z).val))) = _
  exact Diffeomorph.symm_apply_apply _ _

theorem solidPantsInteriorPermutation_collar
    (P : (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (𝓡∂ 2).prod (𝓡 1)⟯ (planarSet.{u} 3 × Circle)) {δ : ℝ} {ρ : Fin 3 ≃ Fin 3}
    (hgerm : ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      P (planarCollar.{u} 3 (Or.inr rfl) j (p.1.1, p.2), p.1.2) =
        (planarCollar.{u} 3 (Or.inr rfl) (ρ j) (p.1.1, p.2), p.1.2))
    (j : Fin 3) (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource)
    (hs : p.2.val 0 < δ) (z : planarOpen 3 × Circle)
    (hz : (z.1.val, z.2) =
      ((planarCollar.{u} 3 (Or.inr rfl) j (p.1.1, p.2)).val.down, p.1.2)) :
    ((solidPantsInteriorPermutation P z).1.val, (solidPantsInteriorPermutation P z).2) =
      ((planarCollar.{u} 3 (Or.inr rfl) (ρ j) (p.1.1, p.2)).val.down, p.1.2) := by
  have hinput : (productDiffeomorph 3).symm (solidPantsInteriorProduct z).val =
      (planarCollar.{u} 3 (Or.inr rfl) j (p.1.1, p.2), p.1.2) := by
    apply Prod.ext
    · apply Subtype.ext
      apply ULift.ext
      have hval := solidPantsInteriorProduct_val.{u} z
      exact (congrArg (fun a : PlaneLift.{u} × Circle => a.1.down) hval).trans
        (congrArg Prod.fst hz)
    · have hval := solidPantsInteriorProduct_val.{u} z
      exact (congrArg Prod.snd hval).trans (congrArg Prod.snd hz)
  have hcompact := solidPantsInteriorPermutation_compact P z
  rw [hinput, hgerm j p hp hs] at hcompact
  have hval := solidPantsInteriorProduct_val.{u} (solidPantsInteriorPermutation P z)
  have hout := congrArg (fun a : planarSet.{u} 3 × Circle => (a.1.val.down, a.2)) hcompact
  exact (congrArg (fun a : PlaneLift.{u} × Circle => (a.1.down, a.2)) hval).symm.trans hout

theorem solidPantsSeam_collar (hk : d.k = 3) (m : Fin d.fillingCount) (j : Fin d.k)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (hy : 1 < ‖y.1‖)
    (hs : solidRemainingCollarHeight d m y < 1) :
    seamModel d m j A y =
      ((planarCollar.{u} 3 (Or.inr rfl) (Fin.cast hk j)
        ((solidRemainingCollarParam d m A y).1.1,
          (solidRemainingCollarParam d m A y).2)).val.down,
        (solidRemainingCollarParam d m A y).1.2) := by
  have hsource := solidRemainingCollarParam_source d m A y hy hs
  have hbase : ((solidRemainingCollarParam d m A y).1.1,
      (solidRemainingCollarParam d m A y).2) ∈ circleCollarSource := hsource
  rw [planarCollar_apply_val (Or.inr rfl) (Fin.cast hk j) hbase]
  apply Prod.ext
  · simp only [seamModel, planarCollarFormula, planarCenter, planarRadius,
      planarSign, planarTwist, hk, Fin.val_cast]
    rw [solidRemainingCollarParam_height d m A y hy]
    simp only [solidRemainingCollarHeight, solidRemainingCollarParam, Complex.real_smul]
    split_ifs <;> push_cast <;> ring
  · rfl


theorem SeifertBlockCharts.solidRetainedTube_product_overlap
    (C : SeifertBlockCharts W d) (m : Fin d.fillingCount) {η : ℝ} (hη : η ≤ C.ε) :
    (C.solidRetainedTube m η).target ∩ (C.productRegion : Set W.Carrier) =
      C.solidRetainedTube m η '' {y : ℂ × Circle | 1 < ‖y.1‖ ∧ ‖y.1‖ < 1 + η} := by
  ext x
  constructor
  · rintro ⟨hx, hp⟩
    rw [C.solidRetainedTube_target] at hx
    have himage : x ∈ C.tube m '' C.transitionDomain :=
      C.tube_product_overlap m ▸ ⟨hx.1, hp⟩
    obtain ⟨y, hy, he⟩ := himage
    have hsrc : y ∈ (C.tube m).source := by
      rw [C.tube_source]
      exact (C.transitionDomain_eq ▸ hy).2
    have hsmall : ‖y.1‖ < 1 + η := by
      rw [← he, (C.tube m).symm_apply_apply hsrc] at hx
      exact hx.2
    exact ⟨y, ⟨(C.transitionDomain_eq ▸ hy).1, hsmall⟩, he⟩
  · rintro ⟨y, hy, he⟩
    have hsrc : y ∈ (C.solidRetainedTube m η).source :=
      C.solidRetainedTube_source m hη ▸ hy.2
    refine ⟨he ▸ (C.solidRetainedTube m η).map_source hsrc, ?_⟩
    have htrans : y ∈ C.transitionDomain := by
      rw [C.transitionDomain_eq]
      exact ⟨hy.1, lt_of_lt_of_le hy.2 (by linarith)⟩
    have hmem : C.tube m y ∈ C.tube m '' C.transitionDomain := ⟨y, htrans, rfl⟩
    rw [← C.tube_product_overlap m] at hmem
    exact he ▸ hmem.2

def SeifertBlockCharts.shrinkTubeWidth (C : SeifertBlockCharts W d)
    {η : ℝ} (hη0 : 0 < η) (hη : η ≤ C.ε) : SeifertBlockCharts W d where
  port := C.port
  matrix := C.matrix
  a := C.a
  b := C.b
  matrix_eq := C.matrix_eq
  bezout := C.bezout
  productRegion := C.productRegion
  productRegion_interior := C.productRegion_interior
  product := C.product
  ε := η
  ε_pos := hη0
  tube m := C.solidRetainedTube m η
  tube_source m := C.solidRetainedTube_source m hη
  tube_interior m x hx := C.tube_interior m ((C.solidRetainedTube_target m η x).mp hx).1
  transitionDomain := {y : ℂ × Circle | 1 < ‖y.1‖ ∧ ‖y.1‖ < 1 + η}
  transitionDomain_eq := rfl
  transition_domain m y hy := C.transition_domain m (by
    rw [C.transitionDomain_eq]
    exact ⟨hy.1, lt_of_lt_of_le hy.2 (by linarith)⟩)
  transition m y hy := C.transition m y (by
    rw [C.transitionDomain_eq]
    exact ⟨hy.1, lt_of_lt_of_le hy.2 (by linarith)⟩)
  tube_product_overlap m := C.solidRetainedTube_product_overlap m hη
  disjoint m n hmn := Set.disjoint_of_subset_left (fun x hx => hx.1)
    (Set.disjoint_of_subset_right (fun x hx => hx.1) (C.disjoint hmn))
  covers x hx := by
    rcases C.covers x hx with hp | ⟨m, hm⟩
    · exact Or.inl hp
    · by_cases hs : ‖((C.tube m).symm x).1‖ < 1 + η
      · exact Or.inr ⟨m, hm, hs⟩
      · have hnorm : 1 < ‖((C.tube m).symm x).1‖ := by
          have hb := le_of_not_gt hs
          linarith
        have hsrc := (C.tube m).map_target hm
        have htrans : (C.tube m).symm x ∈ C.transitionDomain := by
          rw [C.transitionDomain_eq]
          rw [C.tube_source] at hsrc
          exact ⟨hnorm, hsrc⟩
        have hmem : x ∈ C.tube m '' C.transitionDomain :=
          ⟨(C.tube m).symm x, htrans, (C.tube m).apply_symm_apply hm⟩
        rw [← C.tube_product_overlap m] at hmem
        exact Or.inl hmem.2


def SeifertBlockCharts.reindexPantsProduct (C : SeifertBlockCharts W d)
    (Q : (planarOpen d.k × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯
      (planarOpen d.k × Circle)) (σ : Fin d.k ≃ Fin d.k)
    (hcompat : ∀ m y (hy : y ∈ C.transitionDomain),
      ((Q (⟨(seamModel d m (C.port (.inr m)) (C.matrix m) y).1,
        C.transition_domain m hy⟩,
          (seamModel d m (C.port (.inr m)) (C.matrix m) y).2)).1.val,
        (Q (⟨(seamModel d m (C.port (.inr m)) (C.matrix m) y).1,
          C.transition_domain m hy⟩,
            (seamModel d m (C.port (.inr m)) (C.matrix m) y).2)).2) =
        seamModel d m (σ (C.port (.inr m))) (C.matrix m) y) : SeifertBlockCharts W d where
  port := C.port.trans σ
  matrix := C.matrix
  a := C.a
  b := C.b
  matrix_eq := C.matrix_eq
  bezout := C.bezout
  productRegion := C.productRegion
  productRegion_interior := C.productRegion_interior
  product := Q.symm.trans C.product
  ε := C.ε
  ε_pos := C.ε_pos
  tube := C.tube
  tube_source := C.tube_source
  tube_interior := C.tube_interior
  transitionDomain := C.transitionDomain
  transitionDomain_eq := C.transitionDomain_eq
  transition_domain m y hy := by
    have hc := congrArg Prod.fst (hcompat m y hy)
    change (seamModel d m (σ (C.port (.inr m))) (C.matrix m) y).1 ∈ planarOpen d.k
    dsimp only [Prod.fst] at hc
    exact hc ▸ (Q (⟨(seamModel d m (C.port (.inr m)) (C.matrix m) y).1,
      C.transition_domain m hy⟩,
        (seamModel d m (C.port (.inr m)) (C.matrix m) y).2)).1.property
  transition m y hy := by
    have hold := C.transition m y hy
    rw [hold]
    change (C.product _).val = (C.product (Q.symm _)).val
    apply congrArg (fun z => (C.product z).val)
    apply (Q.symm_apply_apply _).symm.trans
    apply congrArg Q.symm
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (hcompat m y hy)
    · exact congrArg (fun z : ℂ × Circle => z.2) (hcompat m y hy)
  tube_product_overlap := C.tube_product_overlap
  disjoint := C.disjoint
  covers := C.covers

def solidPantsPortReindex (hk : d.k = 3) (ρ : Fin 3 ≃ Fin 3) : Fin d.k ≃ Fin d.k :=
  (finCongr hk).trans (ρ.trans (finCongr hk).symm)

def solidPantsCastProduct (hk : d.k = 3) :
    (planarOpen d.k × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯
      (planarOpen 3 × Circle) :=
  (selectedPlanarOpenCast hk).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)

def solidPantsInteriorPermutationCast (hk : d.k = 3)
    (P : (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (𝓡∂ 2).prod (𝓡 1)⟯ (planarSet.{u} 3 × Circle)) :
    (planarOpen d.k × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯
      (planarOpen d.k × Circle) :=
  (solidPantsCastProduct hk).trans
    ((solidPantsInteriorPermutation P).trans (solidPantsCastProduct hk).symm)

theorem solidPantsInteriorPermutationCast_val (hk : d.k = 3)
    (P : (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (𝓡∂ 2).prod (𝓡 1)⟯ (planarSet.{u} 3 × Circle)) (z : planarOpen d.k × Circle) :
    ((solidPantsInteriorPermutationCast hk P z).1.val,
      (solidPantsInteriorPermutationCast hk P z).2) =
        ((solidPantsInteriorPermutation P (solidPantsCastProduct hk z)).1.val,
          (solidPantsInteriorPermutation P (solidPantsCastProduct hk z)).2) := by
  change (((selectedPlanarOpenCast hk).symm
    (solidPantsInteriorPermutation P (solidPantsCastProduct hk z)).1).val, _) = _
  rw [selectedPlanarOpenCast_symm, selectedPlanarOpenCast_val]
  rfl

theorem solidPantsInteriorPermutationCast_seam (C : SeifertBlockCharts W d)
    (hk : d.k = 3)
    (P : (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (𝓡∂ 2).prod (𝓡 1)⟯ (planarSet.{u} 3 × Circle)) {δ : ℝ} {ρ : Fin 3 ≃ Fin 3}
    (hgerm : ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      P (planarCollar.{u} 3 (Or.inr rfl) j (p.1.1, p.2), p.1.2) =
        (planarCollar.{u} 3 (Or.inr rfl) (ρ j) (p.1.1, p.2), p.1.2))
    (m : Fin d.fillingCount) (y : ℂ × Circle) (hy : y ∈ C.transitionDomain)
    (hs : solidRemainingCollarHeight d m y < min δ 1) :
    let z : planarOpen d.k × Circle :=
      (⟨(seamModel d m (C.port (.inr m)) (C.matrix m) y).1, C.transition_domain m hy⟩,
        (seamModel d m (C.port (.inr m)) (C.matrix m) y).2)
    ((solidPantsInteriorPermutationCast hk P z).1.val,
      (solidPantsInteriorPermutationCast hk P z).2) =
        seamModel d m (solidPantsPortReindex hk ρ (C.port (.inr m))) (C.matrix m) y := by
  intro z
  let p := solidRemainingCollarParam d m (C.matrix m) y
  have hy1 : 1 < ‖y.1‖ := (C.transitionDomain_eq ▸ hy).1
  have hs1 := lt_of_lt_of_le hs (min_le_right δ 1)
  have hp := solidRemainingCollarParam_source d m (C.matrix m) y hy1 hs1
  have hδ : p.2.val 0 < δ := by
    rw [solidRemainingCollarParam_height d m (C.matrix m) y hy1]
    exact lt_of_lt_of_le hs (min_le_left δ 1)
  have hz : ((solidPantsCastProduct hk z).1.val, (solidPantsCastProduct hk z).2) =
      ((planarCollar.{u} 3 (Or.inr rfl) (Fin.cast hk (C.port (.inr m)))
        (p.1.1, p.2)).val.down, p.1.2) := by
    change ((selectedPlanarOpenCast hk z.1).val, z.2) = _
    rw [selectedPlanarOpenCast_val]
    exact solidPantsSeam_collar.{u} hk m (C.port (.inr m)) (C.matrix m) y hy1 hs1
  rw [solidPantsInteriorPermutationCast_val]
  apply (solidPantsInteriorPermutation_collar P hgerm _ p hp hδ _ hz).trans
  exact (solidPantsSeam_collar.{u} hk m (solidPantsPortReindex hk ρ (C.port (.inr m)))
    (C.matrix m) y hy1 hs1).symm


theorem SeifertBlockCharts.exists_reindexedPantsCharts
    (C : SeifertBlockCharts W d) (hk : d.k = 3) {δ : ℝ} (hδ : 0 < δ)
    (P : (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (𝓡∂ 2).prod (𝓡 1)⟯ (planarSet.{u} 3 × Circle)) (ρ : Fin 3 ≃ Fin 3)
    (hgerm : ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      P (planarCollar.{u} 3 (Or.inr rfl) j (p.1.1, p.2), p.1.2) =
        (planarCollar.{u} 3 (Or.inr rfl) (ρ j) (p.1.1, p.2), p.1.2)) :
    ∃ D : SeifertBlockCharts W d,
      D.port = C.port.trans (solidPantsPortReindex hk ρ) ∧ D.matrix = C.matrix := by
  let p : ℕ := Finset.univ.sup (fun m : Fin d.fillingCount => (d.fillingSlope m).1.natAbs)
  obtain ⟨η, hη0, hη, hsmall⟩ := exists_solidAbsorptionWidth p C.ε_pos
    (lt_min hδ (by norm_num : (0 : ℝ) < 1))
  let D := C.shrinkTubeWidth hη0 hη
  let Q := solidPantsInteriorPermutationCast hk P
  let σ := solidPantsPortReindex hk ρ
  have hcompat (m : Fin d.fillingCount) (y : ℂ × Circle) (hy : y ∈ D.transitionDomain) :
      ((Q (⟨(seamModel d m (D.port (.inr m)) (D.matrix m) y).1,
        D.transition_domain m hy⟩,
          (seamModel d m (D.port (.inr m)) (D.matrix m) y).2)).1.val,
        (Q (⟨(seamModel d m (D.port (.inr m)) (D.matrix m) y).1,
          D.transition_domain m hy⟩,
            (seamModel d m (D.port (.inr m)) (D.matrix m) y).2)).2) =
        seamModel d m (σ (D.port (.inr m))) (D.matrix m) y := by
    apply solidPantsInteriorPermutationCast_seam.{u} D hk P hgerm m y hy
    have hp : (d.fillingSlope m).1.natAbs ≤ p :=
      Finset.le_sup (f := fun a : Fin d.fillingCount => (d.fillingSlope a).1.natAbs)
        (Finset.mem_univ m)
    have hy1 : 1 < ‖y.1‖ := hy.1
    have hpow := pow_le_pow_right₀ (le_of_lt hy1) hp
    have hs := hsmall ‖y.1‖ hy.1 hy.2
    dsimp [solidRemainingCollarHeight]
    linarith
  exact ⟨D.reindexPantsProduct Q σ hcompat, rfl, rfl⟩

theorem SeifertBlockCharts.exists_pantsReindexedCharts
    (C : SeifertBlockCharts W d) (hk : d.k = 3) (ρ : Fin 3 ≃ Fin 3) :
    ∃ D : SeifertBlockCharts W d,
      D.port = C.port.trans (solidPantsPortReindex hk ρ) ∧ D.matrix = C.matrix := by
  obtain ⟨δ, hδ, P, hgerm⟩ := exists_pantsIdentityGermPermutation.{u} ρ
  exact C.exists_reindexedPantsCharts hk hδ P ρ hgerm

theorem SeifertBlockCharts.exists_pantsOuterHoleReindexedCharts
    (C : SeifertBlockCharts W d) (hk : d.k = 3) :
    ∃ D : SeifertBlockCharts W d,
      D.port = C.port.trans (solidPantsPortReindex hk (Equiv.swap 0 1)) ∧
        D.matrix = C.matrix := by
  obtain ⟨δ, hδ, P, hgerm⟩ := exists_pantsOuterHoleIdentityGermPermutation.{u}
  exact C.exists_reindexedPantsCharts hk hδ P (Equiv.swap 0 1) hgerm


theorem SeifertBlockCharts.exists_solidThreeAbsorbedCharts
    (C : SeifertBlockCharts W d) (h : d.IsSolidTorus) (hk : d.k = 3) :
    ∃ d' : SeifertData, d'.k = 2 ∧ d'.IsSolidTorus ∧ Nonempty (SeifertBlockCharts W d') := by
  have hn0 := solidTorusShape_normal_of_three d h hk
  let m : Fin d.fillingCount := Fin.natAdd d.cones.length ⟨0, hn0⟩
  have hn : (d.fillingSlope m).1 = 1 := by
    simp only [m, SeifertData.fillingSlope, Fin.append_right]
  by_cases hp : Fin.cast hk (C.port (.inr m)) = (0 : Fin 3)
  · obtain ⟨D, hDport, hDmatrix⟩ := C.exists_pantsOuterHoleReindexedCharts hk
    have hport : Fin.cast hk (D.port (.inr m)) = (1 : Fin 3) := by
      rw [hDport]
      change Equiv.swap (0 : Fin 3) 1 (Fin.cast hk (C.port (.inr m))) = 1
      rw [hp, Equiv.swap_apply_left]
    exact D.exists_solidInnerOneAbsorbedCharts h hk m hn hport
  · exact C.exists_solidInnerNormalAbsorbedCharts h hk m hn hp

def solidTorusShapeGeometry (C : SeifertBlockCharts W d) (h : d.IsSolidTorus) :
    W.InteriorGeometry ⊤ :=
  if hk : d.k ≤ 2 then solidTorusShapeGeometry_of_k_le_two C h hk
  else solidTorusShapeGeometryOfReduction
    (C.exists_solidThreeAbsorbedCharts h (by have hd := d.k_le_three; omega))

theorem solidTorusShapeGeometry_model (C : SeifertBlockCharts W d) (h : d.IsSolidTorus) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (solidTorusShapeGeometry C h).model = .euclidean := by
  by_cases hk : d.k ≤ 2
  · rw [solidTorusShapeGeometry, dite_eq_left hk]
    exact solidTorusShapeGeometry_of_k_le_two_model C h hk
  · rw [solidTorusShapeGeometry, dite_eq_right hk]
    exact solidTorusShapeGeometryOfReduction_model _


end GC.Seifert
