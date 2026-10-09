import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanCharts
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanUnfilled
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingProduct
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Topology.Order.IntermediateValue
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusCollarStraightening

/-!
# Absorbing normal fillings in two-port Seifert blocks

The shape bound leaves at most one normal filling. Its integral fibre twist is absorbed by a
smooth fibre shear on the punctured product and an extending solid-torus basis change.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

def normalT2IntervalDatum (q : ℤ) : SeifertData where
  k := 3
  ports := 2
  cones := []
  normals := [q]
  one_le_k := by decide
  k_le_three := by decide
  two_le_of_mem_cones c hc := by simp at hc
  gcd_eq_one_of_mem_cones c hc := by simp at hc
  ports_add_length_add_length := rfl

instance normalT2IntervalDatum_fillingCount_neZero (q : ℤ) :
    NeZero (normalT2IntervalDatum q).fillingCount :=
  ⟨by simp [normalT2IntervalDatum, SeifertData.fillingCount]⟩

theorem normalT2IntervalDatum_fillingSlope (q : ℤ)
    (m : Fin (normalT2IntervalDatum q).fillingCount) :
    (normalT2IntervalDatum q).fillingSlope m = (1, q) := by
  have hm : m = 0 := Fin.eq_zero m
  subst m
  rfl

theorem normalT2IntervalShape (d : SeifertData) (h : d.ports = 2 ∧ d.cones = []) :
    (d.k = 2 ∧ d.normals = [] ∧ d.fillingCount = 0) ∨
      (d.k = 3 ∧ ∃ q : ℤ, d.normals = [q] ∧ d.fillingCount = 1) := by
  have hcount := d.ports_add_length_add_length
  have hmax := d.k_le_three
  simp only [h.1, h.2, List.length_nil, add_zero] at hcount
  by_cases hn : d.normals.length = 0
  · have hnil := List.eq_nil_of_length_eq_zero hn
    exact Or.inl ⟨by omega, hnil, by simp [SeifertData.fillingCount, h.2, hnil]⟩
  · have hone : d.normals.length = 1 := by omega
    obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp hone
    exact Or.inr ⟨by omega, q, hq, by simp [SeifertData.fillingCount, h.2, hq]⟩

theorem normalT2IntervalDatum_eq (d : SeifertData) (q : ℤ)
    (hk : d.k = 3) (hp : d.ports = 2) (hc : d.cones = []) (hn : d.normals = [q]) :
    d = normalT2IntervalDatum q := by
  cases d with
  | mk k ports cones normals h1 h3 h2 hg hcount =>
    change k = 3 at hk
    change ports = 2 at hp
    change cones = [] at hc
    change normals = [q] at hn
    subst k
    subst ports
    subst cones
    subst normals
    rfl

def normalT2IntervalUnfilledGeometry {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (h : d.ports = 2 ∧ d.cones = [])
    (h0 : d.fillingCount = 0) : W.InteriorGeometry ⊤ :=
  unfilledT2IntervalGeometry C h0 (by
    have hc := d.ports_add_fillingCount
    rw [h.1, h0, add_zero] at hc
    exact hc.symm)

theorem normalT2IntervalUnfilledGeometry_model {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (h : d.ports = 2 ∧ d.cones = [])
    (h0 : d.fillingCount = 0) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (normalT2IntervalUnfilledGeometry C h h0).model = ThurstonModel.euclidean := rfl

theorem normalFillingSlope_fst (d : SeifertData) (hc : d.cones = [])
    (m : Fin d.fillingCount) : (d.fillingSlope m).1 = 1 := by
  induction m using Fin.addCases with
  | left c => exact Fin.elim0 (Fin.cast (congrArg List.length hc) c)
  | right n => simp only [SeifertData.fillingSlope, Fin.append_right]

def normalInnerPhase {k : ℕ} (j : Fin k) (q : ℤ) (z : planarOpen k) : Circle :=
  unitOf (z.val - planarCenter k j) ^ q

theorem normalInnerPhase_smooth {k : ℕ} (j : Fin k) (hj : j.val ≠ 0) (q : ℤ) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓡 1) ∞ (normalInnerPhase j q) := by
  intro z
  have hz := chartPlanarInterior_hole_lt z.property j hj
  have hne : z.val - planarCenter k j ≠ 0 := by
    intro he
    rw [he, norm_zero] at hz
    norm_num at hz
  exact (contMDiff_circle_zpow q).contMDiffAt.comp z
    ((contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp z
      ((contMDiff_subtype_val.sub contMDiff_const).contMDiffAt))

def normalInnerFibreShear {k : ℕ} (j : Fin k) (hj : j.val ≠ 0) (q : ℤ) :
    (planarOpen k × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯
      (planarOpen k × Circle) where
  toFun x := (x.1, normalInnerPhase j q x.1 * x.2)
  invFun y := (y.1, (normalInnerPhase j q y.1)⁻¹ * y.2)
  left_inv x := by simp
  right_inv y := by simp
  contMDiff_toFun := contMDiff_fst.prodMk
    (((normalInnerPhase_smooth j hj q).comp contMDiff_fst).mul contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk
    (((normalInnerPhase_smooth j hj q).inv.comp contMDiff_fst).mul contMDiff_snd)

def normalInnerTubeMap {k : ℕ} (j : Fin k) (a : ℤ) (y : ℂ × Circle) : ℂ × Circle :=
  (planarCenter k j + (solidBasisExtension false false (-a) y).1 / 2, y.2)

theorem normalInnerSeamModel {d : SeifertData} (m : Fin d.fillingCount)
    (hp : (d.fillingSlope m).1 = 1) (j : Fin d.k) (hj : j.val ≠ 0)
    (a b : ℤ) (hb : b - a * (d.fillingSlope m).2 = 1)
    (A : GL (Fin 2) ℤ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-1, a; -(d.fillingSlope m).2, b]) (y : ℂ × Circle) (hy : y.1 ≠ 0) :
    let z := seamModel d m j A y
    (z.1, unitOf (z.1 - planarCenter d.k j) ^ (d.fillingSlope m).2 * z.2) =
      normalInnerTubeMap j a y := by
  let t : Circle := unitOf y.1 * y.2 ^ (-a)
  have hfst : (linearTorusMap A (unitOf y.1, y.2)).1 = t⁻¹ := by
    simp [linearTorusMap, hA, t, mul_inv_rev, mul_comm]
  have hsnd : (linearTorusMap A (unitOf y.1, y.2)).2 =
      unitOf y.1 ^ (-(d.fillingSlope m).2) * y.2 ^ b := by
    simp [linearTorusMap, hA]
  have hnorm : 0 < ‖y.1‖ := norm_pos_iff.mpr hy
  have hbase : (seamModel d m j A y).1 =
      planarCenter d.k j + (‖y.1‖ / 2 : ℝ) • (t : ℂ) := by
    simp only [seamModel, hp, Int.natAbs_one, pow_one, planarRadius, hj, ite_false,
      hfst, Circle.coe_inv_eq_conj, starRingEnd_self_apply, Complex.real_smul]
    congr 2
    push_cast
    ring
  have hphase : unitOf ((seamModel d m j A y).1 - planarCenter d.k j) = t := by
    rw [hbase, add_sub_cancel_left, unitOf_smul (by positivity)]
  apply Prod.ext
  · change (seamModel d m j A y).1 = (normalInnerTubeMap j a y).1
    rw [hbase]
    change planarCenter d.k j + (‖y.1‖ / 2 : ℝ) •
      ((unitOf y.1 * y.2 ^ (-a) : Circle) : ℂ) =
      planarCenter d.k j + (y.1 * ((y.2 ^ (-a) : Circle) : ℂ)) / 2
    rw [Circle.coe_mul, Complex.real_smul, Complex.ofReal_div]
    have he : (‖y.1‖ : ℂ) * (unitOf y.1 : ℂ) = y.1 := by
      simpa only [Complex.real_smul] using norm_smul_unitOf y.1
    calc
      _ = planarCenter d.k j +
          ((‖y.1‖ : ℂ) * (unitOf y.1 : ℂ)) * ((y.2 ^ (-a) : Circle) : ℂ) / 2 := by
        push_cast
        ring
      _ = _ := by rw [he]
  · change unitOf ((seamModel d m j A y).1 - planarCenter d.k j) ^
      (d.fillingSlope m).2 * (seamModel d m j A y).2 = y.2
    rw [hphase]
    change t ^ (d.fillingSlope m).2 *
      (linearTorusMap A (unitOf y.1, y.2)).2 = y.2
    rw [hsnd]
    simp only [t, mul_zpow]
    rw [mul_mul_mul_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
    rw [← zpow_mul, ← zpow_add]
    have he : -a * (d.fillingSlope m).2 + b = 1 := by linarith
    rw [he, zpow_one]

theorem normalInnerZeroSeam (j : Fin 3) (hj : j.val ≠ 0)
    (y : ℂ × Circle) (hy : y.1 ≠ 0) :
    seamModel (normalT2IntervalDatum 0) 0 j (chartConventionUnit 1 0 0 1 (by simp)) y =
      (planarCenter 3 j + y.1 / 2, y.2) := by
  have he := normalInnerSeamModel (d := normalT2IntervalDatum 0) 0 (by rfl) j hj 0 1
    (by rfl) (chartConventionUnit 1 0 0 1 (by simp)) (by rfl) y hy
  simp only [normalT2IntervalDatum_fillingSlope, zpow_zero, one_mul] at he
  have hr : normalInnerTubeMap j 0 y = (planarCenter 3 j + y.1 / 2, y.2) := by
    apply Prod.ext
    · change planarCenter 3 j + (y.1 * ((y.2 ^ (-(0 : ℤ)) : Circle) : ℂ)) / 2 = _
      simp only [neg_zero, zpow_zero, Circle.coe_one, mul_one]
    · rfl
  exact he.trans hr

theorem normalSolidBasis_inverseNorm (a : ℤ) (y : ℂ × Circle) :
    ‖((solidBasisExtension false false (-a)).symm y).1‖ = ‖y.1‖ := by
  have he := solidBasisExtension_norm false false (-a)
    ((solidBasisExtension false false (-a)).symm y)
  rw [(solidBasisExtension false false (-a)).apply_symm_apply y] at he
  exact he.symm

theorem normalInnerNormalizeSeam {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q))
    (hj : (C.port (.inr 0)).val ≠ 0) (y : ℂ × Circle) (hy : y.1 ≠ 0) :
    let x := (solidBasisExtension false false (-C.a 0)).symm y
    let z := seamModel (normalT2IntervalDatum q) 0 (C.port (.inr 0)) (C.matrix 0) x
    (z.1, unitOf (z.1 - planarCenter 3 (C.port (.inr 0))) ^ q * z.2) =
      seamModel (normalT2IntervalDatum 0) 0 (C.port (.inr 0))
        (chartConventionUnit 1 0 0 1 (by simp)) y := by
  let H := solidBasisExtension false false (-C.a 0)
  have hx : (H.symm y).1 ≠ 0 := by
    apply norm_pos_iff.mp
    rw [normalSolidBasis_inverseNorm]
    exact norm_pos_iff.mpr hy
  have hb : C.b 0 - C.a 0 * q = 1 := by
    simpa only [normalT2IntervalDatum_fillingSlope, one_mul] using C.bezout 0
  have he := normalInnerSeamModel (d := normalT2IntervalDatum q) 0 (by rfl)
    (C.port (.inr 0)) hj (C.a 0) (C.b 0) hb (C.matrix 0) (C.matrix_eq 0) (H.symm y) hx
  dsimp only
  rw [normalInnerZeroSeam (C.port (.inr 0)) hj y hy]
  have hleft : ((seamModel (normalT2IntervalDatum q) 0 (C.port (.inr 0))
      (C.matrix 0) (H.symm y)).1,
      unitOf ((seamModel (normalT2IntervalDatum q) 0 (C.port (.inr 0)) (C.matrix 0)
        (H.symm y)).1 - planarCenter 3 (C.port (.inr 0))) ^ q *
        (seamModel (normalT2IntervalDatum q) 0 (C.port (.inr 0)) (C.matrix 0)
          (H.symm y)).2) = normalInnerTubeMap (C.port (.inr 0)) (C.a 0) (H.symm y) := by
    simpa only [normalT2IntervalDatum_fillingSlope] using! he
  apply hleft.trans
  have hh := H.apply_symm_apply y
  have hfirst := congrArg Prod.fst hh
  have hsecond := congrArg Prod.snd hh
  apply Prod.ext
  · change planarCenter 3 (C.port (.inr 0)) + (H (H.symm y)).1 / 2 = _
    rw [hfirst]
  · change (H.symm y).2 = y.2
    exact hsecond

def normalInnerAffine {k : ℕ} (j : Fin k) :
    (ℂ × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯ (ℂ × Circle) where
  toFun y := (planarCenter k j + y.1 / 2, y.2)
  invFun z := (2 * (z.1 - planarCenter k j), z.2)
  left_inv y := by
    apply Prod.ext
    · change 2 * (planarCenter k j + y.1 / 2 - planarCenter k j) = y.1
      ring
    · rfl
  right_inv z := by
    apply Prod.ext
    · change planarCenter k j + 2 * (z.1 - planarCenter k j) / 2 = z.1
      ring
    · rfl
  contMDiff_toFun :=
    (((contDiff_const.add (contDiff_id.div_const 2)).contMDiff).comp
      contMDiff_fst).prodMk contMDiff_snd
  contMDiff_invFun :=
    (((contDiff_const.mul (contDiff_id.sub contDiff_const)).contMDiff).comp
      contMDiff_fst).prodMk contMDiff_snd

def normalInnerTubeDiffeomorph {k : ℕ} (j : Fin k) (a : ℤ) :
    (ℂ × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯ (ℂ × Circle) :=
  (solidBasisExtension false false (-a)).trans (normalInnerAffine j)

theorem normalInnerTubeDiffeomorph_apply {k : ℕ} (j : Fin k) (a : ℤ) (y : ℂ × Circle) :
    normalInnerTubeDiffeomorph j a y = normalInnerTubeMap j a y := by
  apply Prod.ext
  · rfl
  · change chartCircleFlip false y.2 = y.2
    rfl

theorem normalConePoint_basis (c : ConeFilling) (hp : c.p = 1)
    (x : PlaneLift.{u} × Circle) :
    (Merge.sectionFilling 0).conePoint (solidBasisLift false false (-c.a) x) =
      c.conePoint x := by
  rw [Merge.conePoint_sectionFilling]
  change ((3 / 2 : ℝ) : ℂ) + (x.1.down * ((x.2 ^ (-c.a) : Circle) : ℂ)) / 6 = _
  rw [ConeFilling.conePoint, hp, pow_one]
  push_cast
  ring

theorem normalConeFilled_basis_mem (c : ConeFilling) (hp : c.p = 1)
    (x : PlaneLift.{u} × Circle) :
    solidBasisLift false false (-c.a) x ∈ (Merge.sectionFilling 0).filledSet ↔
      x ∈ c.filledSet := by
  change ConeFilling.filledFunction ((Merge.sectionFilling 0).conePoint
    (solidBasisLift false false (-c.a) x)) ≤ 0 ↔
      ConeFilling.filledFunction (c.conePoint x) ≤ 0
  rw [normalConePoint_basis c hp x]

def normalConeFilledDiffeomorph (c : ConeFilling) (hp : c.p = 1) :
    c.filledSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ (Merge.sectionFilling 0).filledSet.{u} where
  toFun x := ⟨solidBasisLift false false (-c.a) x.val,
    (normalConeFilled_basis_mem c hp x.val).mpr x.property⟩
  invFun y := ⟨(solidBasisLift false false (-c.a)).symm y.val,
    (normalConeFilled_basis_mem c hp _).mp (by
      rw [(solidBasisLift false false (-c.a)).apply_symm_apply y.val]
      exact y.property)⟩
  left_inv x := Subtype.ext ((solidBasisLift false false (-c.a)).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((solidBasisLift false false (-c.a)).apply_symm_apply y.val)
  contMDiff_toFun := by
    apply ((Merge.sectionFilling 0).filledAtlas.contMDiff_iff_subtype_val _).mpr
    exact (solidBasisLift false false (-c.a)).contMDiff.comp
      c.filledAtlas.contMDiff_subtype_val
  contMDiff_invFun := by
    apply (c.filledAtlas.contMDiff_iff_subtype_val _).mpr
    exact (solidBasisLift false false (-c.a)).symm.contMDiff.comp
      (Merge.sectionFilling 0).filledAtlas.contMDiff_subtype_val

def normalConeAnnulusDiffeomorph (c : ConeFilling) (hp : c.p = 1) :
    c.filledCarrier.{u}.Carrier ≃ₘ⟮c.filledCarrier.{u}.model, annulusCircleCarrier.{u}.model⟯
      annulusCircleCarrier.{u}.Carrier :=
  (normalConeFilledDiffeomorph c hp).trans
    ((ElementaryPresentation.sectionCappingAnnulusProductDiffeomorph 0).symm.trans
      (productDiffeomorph 2))

def normalCarrierTopDiffeomorph {W : CompactCarrier.{u}} {V : CompactCarrier.{u}}
    (e : W.Carrier ≃ₘ⟮W.model, V.model⟯ V.Carrier) :
    (⊤ : TopologicalSpace.Opens W.Carrier) ≃ₘ⟮W.model, V.model⟯
      (⊤ : TopologicalSpace.Opens V.Carrier) where
  toFun x := ⟨e x.val, trivial⟩
  invFun y := ⟨e.symm y.val, trivial⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff (⊤ : TopologicalSpace.Opens V.Carrier) _).mp
      (e.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun :=
    (ContMDiff.subtypeVal_comp_iff (⊤ : TopologicalSpace.Opens W.Carrier) _).mp
      (e.symm.contMDiff.comp contMDiff_subtype_val)

def normalCarrierInteriorDiffeomorph {W : CompactCarrier.{u}} {V : CompactCarrier.{u}}
    (e : W.Carrier ≃ₘ⟮W.model, V.model⟯ V.Carrier) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, V.model⟯ V.pieceInterior ⊤ :=
  pieceInteriorCongr (normalCarrierTopDiffeomorph e)

def normalConeInteriorDiffeomorph (c : ConeFilling) (hp : c.p = 1) :
    c.filledCarrier.{u}.pieceInterior ⊤ ≃ₘ⟮c.filledCarrier.{u}.model, 𝓡 3⟯ TorusTimesLine :=
  (normalCarrierInteriorDiffeomorph (normalConeAnnulusDiffeomorph c hp)).trans
    annulusCircleInteriorDiffeo

def normalTorusIntervalGeometryOfDiffeomorph {W : CompactCarrier.{u}}
    (e : W.pieceInterior ⊤ ≃ₘ⟮W.model, 𝓡 3⟯ TorusTimesLine) :
    W.InteriorGeometry ⊤ :=
  interiorGeometryOfDiffeomorph torusTimesLineGeometry W ⊤ e

theorem normalTorusIntervalGeometryOfDiffeomorph_model {W : CompactCarrier.{u}}
    (e : W.pieceInterior ⊤ ≃ₘ⟮W.model, 𝓡 3⟯ TorusTimesLine) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (normalTorusIntervalGeometryOfDiffeomorph e).model = ThurstonModel.euclidean := rfl

def normalConeInteriorGeometry (c : ConeFilling) (hp : c.p = 1) :
    c.filledCarrier.{u}.InteriorGeometry ⊤ :=
  interiorGeometryOfDiffeomorph torusTimesLineGeometry c.filledCarrier.{u} ⊤
    (normalConeInteriorDiffeomorph.{u} c hp)

def normalChartFilling {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q)) : ConeFilling where
  p := 1
  q := q
  a := C.a 0
  b := C.b 0
  one_le := le_rfl
  det_eq := by
    have hb := C.bezout 0
    rw [normalT2IntervalDatum_fillingSlope] at hb
    simpa using hb

theorem normalChartFilling_matrix {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q))
    (m : Fin (normalT2IntervalDatum q).fillingCount) :
    C.matrix m = (normalChartFilling C).matchingUnit := by
  have hm : m = 0 := Fin.eq_zero m
  subst m
  apply Units.ext
  rw [C.matrix_eq 0, normalT2IntervalDatum_fillingSlope]
  change !![-1, C.a 0; -q, C.b 0] = (normalChartFilling C).matchingMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ConeFilling.matchingMatrix, ConeFilling.reflectMatrix, ConeFilling.chartMatrix,
      normalChartFilling, Matrix.mul_apply, Fin.sum_univ_two]

namespace ConeFilling

variable (c : ConeFilling)

theorem normalInnerReferenceSeam_eq (hp : c.p = 1)
    (m : Fin (normalT2IntervalDatum c.q).fillingCount) (y : ℂ × Circle) :
    seamModel (normalT2IntervalDatum c.q) m (1 : Fin 3) c.matchingUnit y =
      ((c.coneChart (chartTubeScale.{u} y)).1.down,
        (c.coneChart (chartTubeScale.{u} y)).2) := by
  have hu : unitOf (3 * y.1) = unitOf y.1 := by
    by_cases hz : y.1 = 0
    · rw [hz, mul_zero]
    · have he : 3 * y.1 = (3 * ‖y.1‖ : ℝ) • (unitOf y.1 : ℂ) := by
        rw [mul_smul, norm_smul_unitOf]
        simp [Complex.real_smul]
      rw [he]
      exact unitOf_smul (by positivity) (unitOf y.1)
  have hr : ‖3 * y.1‖ / 3 = ‖y.1‖ := by simp
  have hm : (c.matchingUnit : Matrix (Fin 2) (Fin 2) ℤ) = c.matchingMatrix := rfl
  have hs : (normalT2IntervalDatum c.q).fillingSlope m = ((c.p : ℤ), c.q) := by
    rw [normalT2IntervalDatum_fillingSlope, hp]
    rfl
  simp only [seamModel, hs, Int.natAbs_natCast, hm, matchingMatrix, linearTorusMap_mul,
    linearTorusMap_reflect, Fin.val_one, one_ne_zero, ite_false]
  apply Prod.ext
  · change planarCenter 3 (1 : Fin 3) +
      ((planarRadius (1 : Fin 3) + 1 * (‖y.1‖ ^ c.p - 1) / 2 : ℝ) : ℂ) *
        conj (((linearTorusMap c.chartMatrix (unitOf y.1, y.2)).1⁻¹ : Circle) : ℂ) =
      c.conePoint (chartTubeScale.{u} y)
    have he := c.conePoint_sub (chartTubeScale.{u} y)
    change c.conePoint (chartTubeScale.{u} y) - ((3 / 2 : ℝ) : ℂ) =
      ((‖3 * y.1‖ / 3) ^ c.p / 2 : ℝ) •
        ((linearTorusMap c.chartMatrix (unitOf (3 * y.1), y.2)).1 : ℂ) at he
    rw [hu, hr] at he
    rw [Circle.coe_inv_eq_conj, starRingEnd_self_apply]
    norm_num [planarCenter, planarRadius]
    rw [Complex.real_smul] at he
    push_cast at he ⊢
    linear_combination -he
  · change (linearTorusMap c.chartMatrix (unitOf y.1, y.2)).2 =
      (linearTorusMap c.chartMatrix (unitOf (3 * y.1), y.2)).2
    rw [hu]

theorem normalInnerReferenceSeam_domain (hp : c.p = 1)
    (m : Fin (normalT2IntervalDatum c.q).fillingCount) (y : ℂ × Circle)
    (hy : 1 < ‖y.1‖ ∧ ‖y.1‖ < c.chartTubeRadius) :
    (seamModel (normalT2IntervalDatum c.q) m (1 : Fin 3) c.matchingUnit y).1 ∈ planarOpen 3 := by
  have ht : c.chartTube.{0} y ∈ c.chartTube.target :=
    c.chartTube.map_source (c.chartTube_source.symm ▸ hy.2)
  have hp' : c.chartTube.{0} y ∈ c.chartProductRegion := by
    apply (c.chartProductRegion_mem _).mpr
    refine ⟨c.chartTube_interior ht, ?_⟩
    rw [c.chartTube_apply_val y hy.2]
    change 3 < ‖3 * y.1‖
    simp only [norm_mul, Complex.norm_ofNat]
    linarith [hy.1]
  obtain ⟨x, hx⟩ := hp'
  rw [c.normalInnerReferenceSeam_eq.{0} hp m y]
  change c.conePoint (chartTubeScale.{0} y) ∈ planarOpen 3
  rw [← c.chartTube_apply_val y hy.2, ← hx, c.chartProductMap_val,
    c.conePoint_coneLift _ (chartProductMap_ne x)]
  exact x.1.property

theorem normalInnerReferenceSeam_transition (hp : c.p = 1)
    (m : Fin (normalT2IntervalDatum c.q).fillingCount) (y : ℂ × Circle)
    (hy : 1 < ‖y.1‖ ∧ ‖y.1‖ < c.chartTubeRadius) :
    c.chartTube.{u} y =
      (c.chartProduct (⟨(seamModel (normalT2IntervalDatum c.q) m (1 : Fin 3)
        c.matchingUnit y).1, c.normalInnerReferenceSeam_domain hp m y hy⟩,
        (seamModel (normalT2IntervalDatum c.q) m (1 : Fin 3) c.matchingUnit y).2) :
        c.filledSet.{u}) := by
  apply Subtype.ext
  rw [c.chartTube_apply_val y hy.2]
  change chartTubeScale.{u} y = c.coneLift
    (ULift.up (seamModel (normalT2IntervalDatum c.q) m (1 : Fin 3) c.matchingUnit y).1,
      (seamModel (normalT2IntervalDatum c.q) m (1 : Fin 3) c.matchingUnit y).2)
  rw [c.normalInnerReferenceSeam_eq.{u} hp m y]
  exact (c.coneLift_coneChart (chartTubeScale.{u} y) (by
    change 3 * y.1 ≠ 0
    exact mul_ne_zero (by norm_num) (norm_pos_iff.mp (by linarith [hy.1])))).symm

def normalInnerReferenceCharts (hp : c.p = 1) (port : Fin 2 ⊕ Fin 1 ≃ Fin 3)
    (hport : port (.inr 0) = 1) :
    SeifertBlockCharts c.filledCarrier.{u} (normalT2IntervalDatum c.q) where
  port := port
  matrix m := c.matchingUnit
  a m := c.a
  b m := c.b
  matrix_eq m := by
    rw [normalT2IntervalDatum_fillingSlope]
    change c.matchingMatrix = !![-1, c.a; -c.q, c.b]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matchingMatrix, reflectMatrix, chartMatrix, hp, Matrix.mul_apply, Fin.sum_univ_two]
  bezout m := by
    rw [normalT2IntervalDatum_fillingSlope]
    simpa only [hp, Nat.cast_one, one_mul] using c.det_eq
  productRegion := c.chartProductRegion
  productRegion_interior := c.chartProductRegion_interior
  product := c.chartProduct
  ε := c.chartTubeRadius - 1
  ε_pos := by linarith [c.chartTubeRadius_gt_one]
  tube m := c.chartTube
  tube_source m := by
    rw [c.chartTube_source]
    congr 1
    ext y
    simp
  tube_interior m := c.chartTube_interior
  transitionDomain := {y | 1 < ‖y.1‖ ∧ ‖y.1‖ < c.chartTubeRadius}
  transitionDomain_eq := by simp
  transition_domain m y hy := by
    have hm : m = 0 := Fin.eq_zero m
    subst m
    exact (congrArg (fun j : Fin 3 =>
      (seamModel (normalT2IntervalDatum c.q) (0 : Fin 1) j c.matchingUnit y).1 ∈
        planarOpen 3) hport).mpr (c.normalInnerReferenceSeam_domain hp 0 y hy)
  transition m y hy := by
    have hm : m = 0 := Fin.eq_zero m
    subst m
    apply Subtype.ext
    rw [c.chartTube_apply_val y hy.2]
    change chartTubeScale.{u} y = c.coneLift
      (ULift.up (seamModel (normalT2IntervalDatum c.q) (0 : Fin 1)
        (port (.inr 0)) c.matchingUnit y).1,
        (seamModel (normalT2IntervalDatum c.q) (0 : Fin 1)
          (port (.inr 0)) c.matchingUnit y).2)
    have he := congrArg (fun j : Fin 3 => c.coneLift.{u}
      (ULift.up (seamModel (normalT2IntervalDatum c.q) (0 : Fin 1)
        j c.matchingUnit y).1,
        (seamModel (normalT2IntervalDatum c.q) (0 : Fin 1)
          j c.matchingUnit y).2)) hport
    have hs := congrArg (fun z : ℂ × Circle => c.coneLift.{u} (ULift.up z.1, z.2))
      (c.normalInnerReferenceSeam_eq.{u} hp 0 y)
    exact (c.coneLift_coneChart (chartTubeScale.{u} y) (by
      change 3 * y.1 ≠ 0
      exact mul_ne_zero (by norm_num)
        (norm_pos_iff.mp (by linarith [hy.1])))).symm.trans (hs.symm.trans he.symm)
  tube_product_overlap m := c.chartTube_product_overlap
  disjoint := by
    intro m n hmn
    change Fin 1 at m n
    exact False.elim (hmn (Subsingleton.elim m n))
  covers y hy := by
    rcases c.chartTube_product_cover y hy with hp' | ht
    · exact Or.inl hp'
    · exact Or.inr ⟨0, ht⟩

theorem normalInnerReferenceCharts_port (hp : c.p = 1) (port : Fin 2 ⊕ Fin 1 ≃ Fin 3)
    (hport : port (.inr 0) = 1) : (c.normalInnerReferenceCharts hp port hport).port = port :=
  rfl

theorem normalInnerReferenceCharts_matrix (hp : c.p = 1) (port : Fin 2 ⊕ Fin 1 ≃ Fin 3)
    (hport : port (.inr 0) = 1) (m : Fin (normalT2IntervalDatum c.q).fillingCount) :
    (c.normalInnerReferenceCharts hp port hport).matrix m = c.matchingUnit :=
  rfl

theorem normalInnerReferenceCharts_product (hp : c.p = 1)
    (port : Fin 2 ⊕ Fin 1 ≃ Fin 3) (hport : port (.inr 0) = 1) :
    (c.normalInnerReferenceCharts hp port hport).product = c.chartProduct := rfl

theorem normalInnerReferenceCharts_tube (hp : c.p = 1)
    (port : Fin 2 ⊕ Fin 1 ≃ Fin 3) (hport : port (.inr 0) = 1)
    (m : Fin (normalT2IntervalDatum c.q).fillingCount) :
    (c.normalInnerReferenceCharts hp port hport).tube m = c.chartTube := rfl

end ConeFilling

def normalOuterRadialDenominator (r : ℝ) : ℝ :=
  seamCut r * (r * (7 - r) / 2) + (1 - seamCut r) * 3

theorem normalOuterRadialDenominator_core {r : ℝ} (hr : r ≤ 1 / 4) :
    normalOuterRadialDenominator r = 3 := by
  simp [normalOuterRadialDenominator, seamCut_of_le hr]

theorem normalOuterRadialDenominator_collar {r : ℝ} (hr : 1 / 2 ≤ r) :
    normalOuterRadialDenominator r = r * (7 - r) / 2 := by
  simp [normalOuterRadialDenominator, seamCut_of_ge hr]

theorem normalOuterRadialDenominator_smooth :
    ContDiff ℝ ∞ (fun z : ℂ => normalOuterRadialDenominator ‖z‖) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have he : (fun w : ℂ => normalOuterRadialDenominator ‖w‖) =ᶠ[𝓝 (0 : ℂ)]
        fun w => (3 : ℝ) := by
      filter_upwards [continuous_norm.continuousAt.eventually_lt_const
        (by norm_num : ‖(0 : ℂ)‖ < 1 / 4)] with w hw
      exact normalOuterRadialDenominator_core hw.le
    have hc : ContDiffAt ℝ ∞ (fun w : ℂ => (3 : ℝ)) 0 := contDiffAt_const
    exact hc.congr_of_eventuallyEq he
  · have hn : ContDiffAt ℝ ∞ (norm : ℂ → ℝ) z := contDiffAt_norm ℝ hz
    have hc := contDiff_seamCut.contDiffAt.comp z hn
    exact (hc.mul ((hn.mul (contDiffAt_const.sub hn)).div_const 2)).add
      ((contDiffAt_const.sub hc).mul contDiffAt_const)

theorem normalOuterRadialDenominator_gt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 5 / 4) :
    (3 / 2) * r < normalOuterRadialDenominator r := by
  by_cases hsmall : r ≤ 1 / 4
  · rw [normalOuterRadialDenominator_core hsmall]
    linarith
  · have hc0 : 0 ≤ seamCut r := Real.smoothTransition.nonneg _
    have hc1 : seamCut r ≤ 1 := Real.smoothTransition.le_one _
    have hrp : 0 < r := by linarith
    have ha : (3 / 2) * r < r * (7 - r) / 2 := by nlinarith
    have hb : (3 / 2) * r < 3 := by linarith
    have h1 := mul_nonneg hc0 (sub_nonneg.mpr ha.le)
    have h2 := mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hb.le)
    have hpos : 0 < seamCut r ∨ 0 < 1 - seamCut r := by
      by_cases hc : 0 < seamCut r
      · exact Or.inl hc
      · exact Or.inr (by linarith)
    rcases hpos with hpos | hpos
    · have ht := mul_pos hpos (sub_pos.mpr ha)
      dsimp [normalOuterRadialDenominator]
      nlinarith
    · have ht := mul_pos hpos (sub_pos.mpr hb)
      dsimp [normalOuterRadialDenominator]
      nlinarith

def normalOuterRadialMap (z : ℂ) : ℂ :=
  z / ((normalOuterRadialDenominator ‖z‖ : ℝ) - (3 / 2 : ℂ) * z)

theorem normalOuterRadialMap_denominator {z : ℂ} (hz : ‖z‖ < 5 / 4) :
    (normalOuterRadialDenominator ‖z‖ : ℂ) - (3 / 2 : ℂ) * z ≠ 0 := by
  intro he
  have hnorm := congrArg norm (sub_eq_zero.mp he)
  have hp := normalOuterRadialDenominator_gt (norm_nonneg z) hz
  have hpos : 0 < normalOuterRadialDenominator ‖z‖ :=
    lt_of_le_of_lt (mul_nonneg (by norm_num) (norm_nonneg z)) hp
  rw [Complex.norm_real, Real.norm_of_nonneg hpos.le, norm_mul] at hnorm
  norm_num at hnorm
  linarith

theorem normalOuterRadialMap_smooth :
    ContDiffOn ℝ ∞ normalOuterRadialMap {z : ℂ | ‖z‖ < 5 / 4} := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  change ContDiffAt ℝ ∞ (fun w : ℂ =>
    w / ((normalOuterRadialDenominator ‖w‖ : ℂ) - (3 / 2 : ℂ) * w)) z
  have hd : ContDiffAt ℝ ∞ (fun w : ℂ =>
      (normalOuterRadialDenominator ‖w‖ : ℂ) - (3 / 2 : ℂ) * w) z :=
    (Complex.ofRealCLM.contDiff.comp normalOuterRadialDenominator_smooth).contDiffAt.sub
      (contDiffAt_const.mul contDiffAt_id)
  simpa only [div_eq_mul_inv] using!
    (contDiffAt_id : ContDiffAt ℝ ∞ (id : ℂ → ℂ) z).mul
      (hd.inv (normalOuterRadialMap_denominator hz))

theorem normalOuterRadialMap_collar {z : ℂ} (hz : 1 < ‖z‖) :
    normalOuterRadialMap z = z / ((‖z‖ * (7 - ‖z‖) / 2 : ℝ) - (3 / 2 : ℂ) * z) := by
  rw [normalOuterRadialMap, normalOuterRadialDenominator_collar (by linarith)]

def normalOuterHostPhase (q : ℤ) (z : planarOpen 3) : Circle :=
  unitOf (z.val - (3 / 2 : ℂ)) ^ (-q)

theorem normalOuterHostPhase_smooth (q : ℤ) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓡 1) ∞ (normalOuterHostPhase q) := by
  convert normalInnerPhase_smooth (1 : Fin 3) (by decide) (-q) using 1
  ext z
  simp [normalOuterHostPhase, normalInnerPhase, planarCenter]

def normalOuterTubePhase (q : ℤ) (z : ℂ) : Circle :=
  unitOf ((normalOuterRadialDenominator ‖z‖ : ℂ) - (3 / 2 : ℂ) * z) ^ (-q)

theorem normalOuterTubePhase_smooth (q : ℤ) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ (normalOuterTubePhase q)
      {z : ℂ | ‖z‖ < 5 / 4} := by
  intro z hz
  apply ContMDiffAt.contMDiffWithinAt
  have hd : ContDiffAt ℝ ∞ (fun w : ℂ =>
      (normalOuterRadialDenominator ‖w‖ : ℂ) - (3 / 2 : ℂ) * w) z :=
    (Complex.ofRealCLM.contDiff.comp normalOuterRadialDenominator_smooth).contDiffAt.sub
      (contDiffAt_const.mul contDiffAt_id)
  exact (contMDiff_circle_zpow (-q)).contMDiffAt.comp z
    ((contMDiffOn_unitOf.contMDiffAt
      (isOpen_ne.mem_nhds (normalOuterRadialMap_denominator hz))).comp z hd.contMDiffAt)

def normalOuterTubeMap (q a : ℤ) (y : ℂ × Circle) : ℂ × Circle :=
  let z := (solidBasisExtension false false (-a) y).1
  (normalOuterRadialMap z, normalOuterTubePhase q z * y.2)

theorem normalOuterShear_cancel (τ w v : Circle) (q a b : ℤ) (hb : b - a * q = 1) :
    ((τ * w ^ (-a))⁻¹ * v) ^ (-q) * (τ ^ (-q) * w ^ b) = v ^ (-q) * w := by
  have hi : ((τ * w ^ (-a))⁻¹) ^ (-q) = (τ * w ^ (-a)) ^ q := by
    simp only [inv_zpow', neg_neg]
  rw [mul_zpow, hi, mul_zpow, ← zpow_mul]
  have he : -a * q + b = 1 := by linarith
  calc
    _ = v ^ (-q) * (τ ^ q * τ ^ (-q)) * (w ^ (-a * q) * w ^ b) := by
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = _ := by rw [← zpow_add, add_neg_cancel, zpow_zero, mul_one,
      ← zpow_add, he, zpow_one]

theorem normalOuterTubeRatio_eq {r : ℝ} (hr : 0 < r) :
    normalOuterRadialDenominator r / r =
      seamCut r * ((7 - r) / 2) + (1 - seamCut r) * (3 / r) := by
  dsimp [normalOuterRadialDenominator]
  field_simp

theorem normalOuterTubeRatio_gap {r : ℝ} (hr : 0 < r) (hrh : r < 1 / 2) :
    (7 - r) / 2 < 3 / r := by
  apply (lt_div_iff₀ hr).mpr
  nlinarith

theorem normalOuterTubeRatio_strictAnti :
    StrictAntiOn (fun r => normalOuterRadialDenominator r / r) (Set.Ioo (0 : ℝ) (5 / 4)) := by
  intro x hx y hy hxy
  change normalOuterRadialDenominator y / y < normalOuterRadialDenominator x / x
  rw [normalOuterTubeRatio_eq hx.1, normalOuterTubeRatio_eq hy.1]
  have hcx0 : 0 ≤ seamCut x := Real.smoothTransition.nonneg _
  have hcx1 : seamCut x ≤ 1 := Real.smoothTransition.le_one _
  have hcxy : seamCut x ≤ seamCut y :=
    Real.smoothTransition.monotone (by linarith)
  have hb : (7 - y) / 2 < (7 - x) / 2 := by linarith
  by_cases hyh : 1 / 2 ≤ y
  · rw [seamCut_of_ge hyh]
    simp only [one_mul, sub_self, zero_mul, add_zero]
    by_cases hxh : 1 / 2 ≤ x
    · rw [seamCut_of_ge hxh]
      simp only [one_mul, sub_self, zero_mul, add_zero]
      exact hb
    · have hgap := (normalOuterTubeRatio_gap hx.1 (not_le.mp hxh)).le
      have hmul := mul_nonneg (sub_nonneg.mpr hcx1) (sub_nonneg.mpr hgap)
      nlinarith
  · have hgap := (normalOuterTubeRatio_gap hy.1 (not_le.mp hyh)).le
    have ha : 3 / y < 3 / x := by
      apply (div_lt_div_iff₀ hy.1 hx.1).mpr
      linarith
    have hfirst : 0 < seamCut x * ((7 - x) / 2 - (7 - y) / 2) +
        (1 - seamCut x) * (3 / x - 3 / y) := by
      by_cases hc : seamCut x = 0
      · simp only [hc, zero_mul, sub_zero, one_mul, zero_add]
        exact sub_pos.mpr ha
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (lt_of_le_of_ne hcx0 (Ne.symm hc)) (sub_pos.mpr hb))
          (mul_nonneg (sub_nonneg.mpr hcx1) (sub_nonneg.mpr ha.le))
    have hthird := mul_nonneg (sub_nonneg.mpr hcxy) (sub_nonneg.mpr hgap)
    nlinarith

def normalOuterTubeRadius (r : ℝ) : ℝ := r / normalOuterRadialDenominator r

theorem normalOuterTubeRadius_strictMono :
    StrictMonoOn normalOuterTubeRadius (Set.Ico (0 : ℝ) (5 / 4)) := by
  intro x hx y hy hxy
  have hyp : 0 < y := lt_of_le_of_lt hx.1 hxy
  have hyH : 0 < normalOuterRadialDenominator y := lt_of_le_of_lt
    (mul_nonneg (by norm_num) hy.1)
    (normalOuterRadialDenominator_gt hy.1 (by linarith [hy.2]))
  by_cases hx0 : x = 0
  · subst x
    change 0 / normalOuterRadialDenominator 0 < y / normalOuterRadialDenominator y
    rw [zero_div]
    exact div_pos hyp hyH
  · have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hxH : 0 < normalOuterRadialDenominator x := lt_of_le_of_lt
      (mul_nonneg (by norm_num) hx.1)
      (normalOuterRadialDenominator_gt hx.1 (by linarith [hx.2]))
    have hF := normalOuterTubeRatio_strictAnti ⟨hxp, hx.2⟩ ⟨hyp, hy.2⟩ hxy
    have hcross := (div_lt_div_iff₀ hyp hxp).mp hF
    change x / normalOuterRadialDenominator x < y / normalOuterRadialDenominator y
    exact (div_lt_div_iff₀ hxH hyH).mpr (by nlinarith)

theorem normalOuterRadialDenominator_hasDerivAt (r : ℝ) :
    HasDerivAt normalOuterRadialDenominator
      (deriv seamCut r * (r * (7 - r) / 2 - 3) + seamCut r * (7 - 2 * r) / 2) r := by
  have hc := (contDiff_seamCut.differentiable (by simp)).differentiableAt.hasDerivAt (x := r)
  have h := (((hc.mul (hasDerivAt_id r)).mul
    ((hasDerivAt_const r 7).sub (hasDerivAt_id r))).div_const 2).add
      (((hasDerivAt_const r 1).sub hc).mul (hasDerivAt_const r 3))
  convert h using 1
  · ext x
    dsimp [normalOuterRadialDenominator]
    ring
  · dsimp
    ring

theorem normalOuterRadialDenominator_deriv_margin {r : ℝ} (hr : 0 ≤ r) :
    0 < normalOuterRadialDenominator r - r * deriv normalOuterRadialDenominator r := by
  have hc0 : 0 ≤ seamCut r := Real.smoothTransition.nonneg _
  have hc1 : seamCut r ≤ 1 := Real.smoothTransition.le_one _
  have hd0 : 0 ≤ deriv seamCut r :=
    (show Monotone seamCut from fun x y hxy =>
      Real.smoothTransition.monotone (by linarith)).deriv_nonneg
  rw [(normalOuterRadialDenominator_hasDerivAt r).deriv]
  have he : normalOuterRadialDenominator r - r *
      (deriv seamCut r * (r * (7 - r) / 2 - 3) + seamCut r * (7 - 2 * r) / 2) =
      -(deriv seamCut r * r * (r * (7 - r) / 2 - 3)) +
        seamCut r * r ^ 2 / 2 + 3 * (1 - seamCut r) := by
    dsimp [normalOuterRadialDenominator]
    ring
  rw [he]
  by_cases hrh : r ≤ 1 / 2
  · have hpoly : r * (7 - r) / 2 - 3 ≤ 0 := by nlinarith
    have hfirst : 0 ≤ -(deriv seamCut r * r * (r * (7 - r) / 2 - 3)) :=
      neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hd0 hr) hpoly)
    have hmiddle : 0 ≤ seamCut r * r ^ 2 / 2 :=
      div_nonneg (mul_nonneg hc0 (sq_nonneg r)) (by norm_num)
    by_cases hrq : r ≤ 1 / 4
    · rw [seamCut_of_le hrq]
      simpa using add_pos_of_nonneg_of_pos hfirst (by norm_num : (0 : ℝ) < 3)
    · have hrp : 0 < r := by linarith [not_le.mp hrq]
      by_cases hc : seamCut r = 0
      · rw [hc]
        simpa using add_pos_of_nonneg_of_pos hfirst (by norm_num : (0 : ℝ) < 3)
      · have hmpos : 0 < seamCut r * r ^ 2 / 2 :=
          div_pos (mul_pos (lt_of_le_of_ne hc0 (Ne.symm hc)) (sq_pos_of_pos hrp))
            (by norm_num)
        exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hfirst hmpos)
          (mul_nonneg (by norm_num) (sub_nonneg.mpr hc1))
  · have hrg : 1 / 2 < r := not_le.mp hrh
    have hE : seamCut =ᶠ[𝓝 r] fun x => (1 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hrg] with x hx
      exact seamCut_of_ge hx.le
    have hdz : deriv seamCut r = 0 := by rw [hE.deriv_eq, deriv_const]
    rw [hdz, seamCut_of_ge hrg.le]
    have hrp : 0 < r := by linarith
    simp only [zero_mul, neg_zero, one_mul, sub_self, mul_zero, zero_add, add_zero]
    exact div_pos (sq_pos_of_pos hrp) (by norm_num)

theorem normalOuterTubeRadius_deriv_pos {r : ℝ} (hr : 0 ≤ r) (hr2 : r < 5 / 4) :
    0 < deriv normalOuterTubeRadius r := by
  have hH : 0 < normalOuterRadialDenominator r := lt_of_le_of_lt
    (mul_nonneg (by norm_num) hr) (normalOuterRadialDenominator_gt hr (by linarith))
  have hD := (hasDerivAt_id r).div (normalOuterRadialDenominator_hasDerivAt r) hH.ne'
  have hder : deriv normalOuterTubeRadius r =
      (normalOuterRadialDenominator r - r * deriv normalOuterRadialDenominator r) /
        normalOuterRadialDenominator r ^ 2 := by
    rw [(show HasDerivAt normalOuterTubeRadius
      ((normalOuterRadialDenominator r - r * deriv normalOuterRadialDenominator r) /
        normalOuterRadialDenominator r ^ 2) r from by
      convert hD using 1
      · rfl
      · rw [(normalOuterRadialDenominator_hasDerivAt r).deriv]
        simp only [id_eq, one_mul]).deriv]
  rw [hder]
  exact div_pos (normalOuterRadialDenominator_deriv_margin hr) (sq_pos_of_pos hH)


def normalOuterRadialNormalize (z : ℂ) : ℂ :=
  (normalOuterRadialDenominator ‖z‖)⁻¹ • z

theorem normalOuterRadialNormalize_smooth :
    ContDiffOn ℝ ∞ normalOuterRadialNormalize {z : ℂ | ‖z‖ < 5 / 4} := by
  intro z hz
  have hH : 0 < normalOuterRadialDenominator ‖z‖ := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (norm_nonneg z))
    (normalOuterRadialDenominator_gt (norm_nonneg z) hz)
  exact ((normalOuterRadialDenominator_smooth.contDiffAt.inv hH.ne').smul
    contDiffAt_id).contDiffWithinAt

theorem normalOuterRadialNormalize_hasFDerivAt {z : ℂ} (hz : z ≠ 0)
    (hH : normalOuterRadialDenominator ‖z‖ ≠ 0) :
    HasFDerivAt normalOuterRadialNormalize
      ((normalOuterRadialDenominator ‖z‖)⁻¹ • ContinuousLinearMap.id ℝ ℂ +
        ((-(deriv normalOuterRadialDenominator ‖z‖) /
          normalOuterRadialDenominator ‖z‖ ^ 2) • fderiv ℝ norm z).smulRight z) z := by
  have hn : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) z :=
    (contDiffAt_norm ℝ hz : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) z).differentiableAt
      (by simp)
  have hh : HasDerivAt normalOuterRadialDenominator
      (deriv normalOuterRadialDenominator ‖z‖) ‖z‖ :=
    (normalOuterRadialDenominator_hasDerivAt ‖z‖).differentiableAt.hasDerivAt
  have hc := hh.inv hH
  exact (hc.comp_hasFDerivAt z hn.hasFDerivAt).smul (hasFDerivAt_id z)

theorem normalOuterRadialNormalize_fderiv_injective {z : ℂ}
    (hz : ‖z‖ < 5 / 4) (hz0 : z ≠ 0) :
    Function.Injective (fderiv ℝ normalOuterRadialNormalize z) := by
  have hn : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) z :=
    (contDiffAt_norm ℝ hz0 : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) z).differentiableAt
      (by simp)
  have hH : 0 < normalOuterRadialDenominator ‖z‖ := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (norm_nonneg z))
    (normalOuterRadialDenominator_gt (norm_nonneg z) hz)
  rw [(normalOuterRadialNormalize_hasFDerivAt hz0 hH.ne').fderiv]
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have hval : (normalOuterRadialDenominator ‖z‖)⁻¹ • v +
      ((-(deriv normalOuterRadialDenominator ‖z‖) /
        normalOuterRadialDenominator ‖z‖ ^ 2) * fderiv ℝ norm z v) • z = 0 := hv
  have hf := congrArg (fderiv ℝ norm z) hval
  rw [map_add, map_smul, map_smul, hn.fderiv_norm_self, map_zero] at hf
  have hmargin := normalOuterRadialDenominator_deriv_margin (norm_nonneg z)
  have he : (normalOuterRadialDenominator ‖z‖)⁻¹ +
      (-(deriv normalOuterRadialDenominator ‖z‖) /
        normalOuterRadialDenominator ‖z‖ ^ 2) * ‖z‖ =
      (normalOuterRadialDenominator ‖z‖ -
        ‖z‖ * deriv normalOuterRadialDenominator ‖z‖) /
          normalOuterRadialDenominator ‖z‖ ^ 2 := by
    field_simp
    ring
  have hcoef : 0 < (normalOuterRadialDenominator ‖z‖)⁻¹ +
      (-(deriv normalOuterRadialDenominator ‖z‖) /
        normalOuterRadialDenominator ‖z‖ ^ 2) * ‖z‖ := by
    rw [he]
    exact div_pos hmargin (sq_pos_of_pos hH)
  have hzero : fderiv ℝ norm z v = 0 := by
    have hp : ((normalOuterRadialDenominator ‖z‖)⁻¹ +
        (-(deriv normalOuterRadialDenominator ‖z‖) /
          normalOuterRadialDenominator ‖z‖ ^ 2) * ‖z‖) * fderiv ℝ norm z v = 0 := by
      simpa only [smul_eq_mul, add_mul, mul_assoc, mul_left_comm, mul_comm] using hf
    exact (mul_eq_zero.mp hp).resolve_left hcoef.ne'
  rw [hzero, mul_zero, zero_smul, add_zero] at hval
  exact (smul_eq_zero.mp hval).resolve_left (inv_ne_zero hH.ne')

def normalOuterMobius (a : ℂ) :
    PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ where
  toFun z := z / (1 - a * z)
  invFun z := z / (1 + a * z)
  source := {z | 1 - a * z ≠ 0}
  target := {z | 1 + a * z ≠ 0}
  map_source' z hz := by
    have he : 1 + a * (z / (1 - a * z)) = (1 - a * z)⁻¹ := by
      field_simp [show 1 - a * z ≠ 0 from hz]
      ring
    change 1 + a * (z / (1 - a * z)) ≠ 0
    rw [he]
    exact inv_ne_zero hz
  map_target' z hz := by
    have he : 1 - a * (z / (1 + a * z)) = (1 + a * z)⁻¹ := by
      field_simp [show 1 + a * z ≠ 0 from hz]
      ring
    change 1 - a * (z / (1 + a * z)) ≠ 0
    rw [he]
    exact inv_ne_zero hz
  left_inv' z hz := by
    have he : 1 + a * (z / (1 - a * z)) = (1 - a * z)⁻¹ := by
      field_simp [show 1 - a * z ≠ 0 from hz]
      ring
    rw [he, div_inv_eq_mul]
    exact div_mul_cancel₀ z hz
  right_inv' z hz := by
    have he : 1 - a * (z / (1 + a * z)) = (1 + a * z)⁻¹ := by
      field_simp [show 1 + a * z ≠ 0 from hz]
      ring
    rw [he, div_inv_eq_mul]
    exact div_mul_cancel₀ z hz
  open_source := isOpen_ne_fun (continuous_const.sub (continuous_const.mul continuous_id))
    continuous_const
  open_target := isOpen_ne_fun (continuous_const.add (continuous_const.mul continuous_id))
    continuous_const
  contMDiffOn_toFun := by
    intro z hz
    have hc : ContDiffAt ℂ ∞ (fun z : ℂ => z / (1 - a * z)) z :=
      contDiffAt_id.div (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)) hz
    exact (hc.restrict_scalars ℝ).contMDiffAt.contMDiffWithinAt
  contMDiffOn_invFun := by
    intro z hz
    have hc : ContDiffAt ℂ ∞ (fun z : ℂ => z / (1 + a * z)) z :=
      contDiffAt_id.div (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)) hz
    exact (hc.restrict_scalars ℝ).contMDiffAt.contMDiffWithinAt

theorem normalOuterRadialNormalize_fderiv_injective_zero :
    Function.Injective (fderiv ℝ normalOuterRadialNormalize 0) := by
  have hE : normalOuterRadialNormalize =ᶠ[𝓝 (0 : ℂ)] fun w => (1 / 3 : ℝ) • w := by
    filter_upwards [continuous_norm.continuousAt.eventually_lt_const
      (by norm_num : ‖(0 : ℂ)‖ < (1 / 4 : ℝ))] with w hw
    rw [normalOuterRadialNormalize, normalOuterRadialDenominator_core hw.le]
    norm_num
  rw [hE.fderiv_eq]
  have hd : HasFDerivAt (fun w : ℂ => (1 / 3 : ℝ) • w)
      ((1 / 3 : ℝ) • ContinuousLinearMap.id ℝ ℂ) 0 :=
    (hasFDerivAt_id (0 : ℂ)).const_smul (1 / 3 : ℝ)
  rw [hd.fderiv]
  intro v w h
  change (1 / 3 : ℝ) • v = (1 / 3 : ℝ) • w at h
  exact smul_right_injective ℂ (by norm_num : (1 / 3 : ℝ) ≠ 0) h

private theorem outerLocal_of_injective_fderiv {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {z : ℂ} (hz : z ∈ U)
    (hinj : Function.Injective (fderiv ℝ f z)) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f z := by
  let A : ℂ ≃L[ℝ] ℂ :=
    ((fderiv ℝ f z).toLinearMap.linearEquivOfInjective hinj rfl).toContinuousLinearEquiv
  have hdf : HasFDerivAt f (A : ℂ →L[ℝ] ℂ) z :=
    (hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp) |>.hasFDerivAt
  exact isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
      f hf.contMDiffOn hU z hz A hdf.hasMFDerivAt

theorem normalOuterRadialNormalize_local :
    IsLocalDiffeomorphOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ normalOuterRadialNormalize
      {z : ℂ | ‖z‖ < 5 / 4} := by
  rintro ⟨z, hz⟩
  apply outerLocal_of_injective_fderiv (isOpen_lt continuous_norm continuous_const)
    normalOuterRadialNormalize_smooth hz
  by_cases hz0 : z = 0
  · subst z
    exact normalOuterRadialNormalize_fderiv_injective_zero
  · exact normalOuterRadialNormalize_fderiv_injective hz hz0

theorem normalOuterRadialMap_factor {z : ℂ}
    (hH : normalOuterRadialDenominator ‖z‖ ≠ 0) :
    normalOuterRadialMap z = normalOuterMobius (3 / 2 : ℂ) (normalOuterRadialNormalize z) := by
  change z / ((normalOuterRadialDenominator ‖z‖ : ℂ) - (3 / 2 : ℂ) * z) =
    ((normalOuterRadialDenominator ‖z‖)⁻¹ • z) /
      (1 - (3 / 2 : ℂ) * ((normalOuterRadialDenominator ‖z‖)⁻¹ • z))
  rw [Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hH]

theorem normalOuterRadialMap_local :
    IsLocalDiffeomorphOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ normalOuterRadialMap
      {z : ℂ | ‖z‖ < 5 / 4} := by
  rintro ⟨z, hz⟩
  have hH : 0 < normalOuterRadialDenominator ‖z‖ := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (norm_nonneg z))
    (normalOuterRadialDenominator_gt (norm_nonneg z) hz)
  have hsrc : normalOuterRadialNormalize z ∈ (normalOuterMobius (3 / 2 : ℂ)).source := by
    change 1 - (3 / 2 : ℂ) * ((normalOuterRadialDenominator ‖z‖)⁻¹ • z) ≠ 0
    have hd := normalOuterRadialMap_denominator hz
    have he : 1 - (3 / 2 : ℂ) * ((normalOuterRadialDenominator ‖z‖)⁻¹ • z) =
        ((normalOuterRadialDenominator ‖z‖ : ℂ) - (3 / 2 : ℂ) * z) /
          normalOuterRadialDenominator ‖z‖ := by
      rw [Complex.real_smul]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hH.ne']
    rw [he]
    exact div_ne_zero hd (Complex.ofReal_ne_zero.mpr hH.ne')
  have hloc := (normalOuterRadialNormalize_local ⟨z, hz⟩).comp 𝓘(ℝ, ℂ) ℂ
    ((normalOuterMobius (3 / 2 : ℂ)).isLocalDiffeomorphAt _ _ ∞ hsrc)
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _ hloc
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
  exact normalOuterRadialMap_factor (ne_of_gt (lt_of_le_of_lt
    (mul_nonneg (by norm_num) (norm_nonneg w))
    (normalOuterRadialDenominator_gt (norm_nonneg w) hw)))

theorem normalOuterRadialNormalize_norm {z : ℂ} (hz : ‖z‖ < 5 / 4) :
    ‖normalOuterRadialNormalize z‖ = normalOuterTubeRadius ‖z‖ := by
  have hH : 0 < normalOuterRadialDenominator ‖z‖ := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (norm_nonneg z))
    (normalOuterRadialDenominator_gt (norm_nonneg z) hz)
  rw [normalOuterRadialNormalize, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hH.le)]
  dsimp [normalOuterTubeRadius]
  ring

theorem normalOuterRadialNormalize_injective :
    Set.InjOn normalOuterRadialNormalize {z : ℂ | ‖z‖ < 5 / 4} := by
  intro z hz w hw he
  have hn := congrArg norm he
  rw [normalOuterRadialNormalize_norm hz, normalOuterRadialNormalize_norm hw] at hn
  have hr : ‖z‖ = ‖w‖ := normalOuterTubeRadius_strictMono.injOn
    ⟨norm_nonneg z, hz⟩ ⟨norm_nonneg w, hw⟩ hn
  have hH : 0 < normalOuterRadialDenominator ‖w‖ := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (norm_nonneg w))
    (normalOuterRadialDenominator_gt (norm_nonneg w) hw)
  dsimp [normalOuterRadialNormalize] at he
  rw [hr] at he
  exact smul_right_injective ℂ (inv_ne_zero hH.ne') he

theorem normalOuterRadialNormalize_norm_lt {z : ℂ} (hz : ‖z‖ < 5 / 4) :
    ‖normalOuterRadialNormalize z‖ < 2 / 3 := by
  have hgt := normalOuterRadialDenominator_gt (norm_nonneg z) hz
  have hH : 0 < normalOuterRadialDenominator ‖z‖ := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (norm_nonneg z)) hgt
  rw [normalOuterRadialNormalize_norm hz]
  change ‖z‖ / normalOuterRadialDenominator ‖z‖ < 2 / 3
  apply (div_lt_iff₀ hH).mpr
  linarith

theorem normalOuterRadialNormalize_mobiusSource {z : ℂ} (hz : ‖z‖ < 5 / 4) :
    normalOuterRadialNormalize z ∈ (normalOuterMobius (3 / 2 : ℂ)).source := by
  change 1 - (3 / 2 : ℂ) * normalOuterRadialNormalize z ≠ 0
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  norm_num [norm_mul] at hn
  linarith [normalOuterRadialNormalize_norm_lt hz]

theorem normalOuterRadialMap_injective :
    Set.InjOn normalOuterRadialMap {z : ℂ | ‖z‖ < 5 / 4} := by
  intro z hz w hw he
  have hzH : 0 < normalOuterRadialDenominator ‖z‖ := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (norm_nonneg z))
    (normalOuterRadialDenominator_gt (norm_nonneg z) hz)
  have hwH : 0 < normalOuterRadialDenominator ‖w‖ := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (norm_nonneg w))
    (normalOuterRadialDenominator_gt (norm_nonneg w) hw)
  rw [normalOuterRadialMap_factor hzH.ne', normalOuterRadialMap_factor hwH.ne'] at he
  apply normalOuterRadialNormalize_injective hz hw
  exact (normalOuterMobius (3 / 2 : ℂ)).toPartialEquiv.injOn
    (normalOuterRadialNormalize_mobiusSource hz) (normalOuterRadialNormalize_mobiusSource hw) he


theorem normalPlanarOpen_nonempty (k : ℕ) : Nonempty (planarOpen k) := by
  let U : Set ℂ := {z | ‖z‖ < 3 ∧ 1 / 2 < |z.im|}
  have hU : IsOpen U :=
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const (Complex.continuous_im.abs))
  have hsub : U ⊆ planarModel k := by
    intro z hz
    refine ⟨hz.1.le, fun j hj => ?_⟩
    have hb := Complex.abs_im_le_norm (z - (planarCenter k j : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hb
    exact le_trans hz.2.le hb
  have hm : (2 : ℂ) * Complex.I ∈ U := by
    change ‖(2 : ℂ) * Complex.I‖ < 3 ∧ 1 / 2 < |((2 : ℂ) * Complex.I).im|
    norm_num
  exact ⟨⟨2 * Complex.I, interior_mono hsub (hU.interior_eq.symm ▸ hm)⟩⟩

def SeifertBlockCharts.productAmbient {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) :
    PartialDiffeomorph PlaneCircleModel W.model (planarOpen d.k × Circle) W.Carrier ∞ :=
  C.product.toPartialDiffeomorph.trans
    (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal C.productRegion
      (by
        obtain ⟨z⟩ := normalPlanarOpen_nonempty d.k
        exact ⟨C.product (z, 1)⟩))

theorem SeifertBlockCharts.productAmbient_source {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) : C.productAmbient.source = univ := by
  ext x
  change x ∈ univ ∧ C.product x ∈ univ ↔ x ∈ univ
  simp

theorem SeifertBlockCharts.productAmbient_apply {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (x : planarOpen d.k × Circle) :
    C.productAmbient x = (C.product x : W.Carrier) := rfl

theorem SeifertBlockCharts.productAmbient_target {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) : C.productAmbient.target = C.productRegion := by
  ext x
  constructor
  · intro hx
    rw [← C.productAmbient.apply_symm_apply hx, C.productAmbient_apply]
    exact (C.product (C.productAmbient.symm x)).property
  · intro hx
    let y := C.product.symm ⟨x, hx⟩
    have he : C.productAmbient y = x :=
      congrArg Subtype.val (C.product.apply_symm_apply ⟨x, hx⟩)
    rw [← he]
    exact C.productAmbient.map_source (C.productAmbient_source.symm ▸ mem_univ y)

section Compare

universe v
variable {W : CompactCarrier.{u}} {W' : CompactCarrier.{v}} {d : SeifertData}

def SeifertBlockCharts.comparisonPatch (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts W' d) : Option (Fin d.fillingCount) →
      PartialDiffeomorph W.model W'.model W.Carrier W'.Carrier ∞
  | none => C.productAmbient.symm.trans D.productAmbient
  | some m => (C.tube m).symm.trans (D.tube m)

theorem SeifertBlockCharts.comparisonPatch_none_source (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts W' d) :
    (C.comparisonPatch D none).source = C.productRegion := by
  ext x
  change x ∈ C.productAmbient.target ∧
    C.productAmbient.symm x ∈ D.productAmbient.source ↔ x ∈ C.productRegion
  rw [C.productAmbient_target, D.productAmbient_source]
  simp

theorem SeifertBlockCharts.comparisonPatch_some_source (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts W' d) (m : Fin d.fillingCount) (x : W.Carrier) :
    x ∈ (C.comparisonPatch D (some m)).source ↔
      x ∈ (C.tube m).target ∧ ‖((C.tube m).symm x).1‖ < 1 + D.ε := by
  change x ∈ (C.tube m).target ∧ (C.tube m).symm x ∈ (D.tube m).source ↔ _
  rw [D.tube_source]
  rfl

theorem SeifertBlockCharts.comparisonPatch_source_cover (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts W' d) (x : W.Carrier) (hx : x ∈ W.interior) :
    ∃ i, x ∈ (C.comparisonPatch D i).source := by
  rcases C.covers x hx with hp | ⟨m, hm⟩
  · exact ⟨none, (C.comparisonPatch_none_source D).symm ▸ hp⟩
  · by_cases hd : ‖((C.tube m).symm x).1‖ < 1 + D.ε
    · exact ⟨some m, (C.comparisonPatch_some_source D m x).mpr ⟨hm, hd⟩⟩
    · have hsrc := (C.tube m).map_target hm
      rw [C.tube_source] at hsrc
      have htrans : (C.tube m).symm x ∈ C.transitionDomain := by
        rw [C.transitionDomain_eq]
        exact ⟨by linarith [D.ε_pos], hsrc⟩
      have hp : x ∈ C.productRegion := by
        have himage : x ∈ C.tube m '' C.transitionDomain :=
          ⟨(C.tube m).symm x, htrans, (C.tube m).apply_symm_apply hm⟩
        rw [← C.tube_product_overlap m] at himage
        exact himage.2
      exact ⟨none, (C.comparisonPatch_none_source D).symm ▸ hp⟩
theorem SeifertBlockCharts.comparisonPatch_none_tube (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts W' d) (hport : C.port = D.port)
    (hmatrix : ∀ m, C.matrix m = D.matrix m) (m : Fin d.fillingCount)
    (y : ℂ × Circle) (hc : y ∈ C.transitionDomain) (hd : y ∈ D.transitionDomain) :
    C.comparisonPatch D none (C.tube m y) = D.tube m y := by
  change D.productAmbient (C.productAmbient.symm (C.tube m y)) = D.tube m y
  rw [C.transition m y hc]
  change D.productAmbient (C.productAmbient.symm (C.productAmbient
    (⟨(seamModel d m (C.port (.inr m)) (C.matrix m) y).1,
      C.transition_domain m hc⟩,
      (seamModel d m (C.port (.inr m)) (C.matrix m) y).2))) = D.tube m y
  rw [C.productAmbient.symm_apply_apply (C.productAmbient_source.symm ▸ mem_univ _)]
  rw [D.transition m y hd]
  change (D.product
    (⟨(seamModel d m (C.port (.inr m)) (C.matrix m) y).1,
      C.transition_domain m hc⟩,
      (seamModel d m (C.port (.inr m)) (C.matrix m) y).2) : W'.Carrier) = _
  congr 1
  apply congrArg D.product
  apply Prod.ext
  · apply Subtype.ext
    simp only [hport, hmatrix m]
  · simp only [hport, hmatrix m]

theorem SeifertBlockCharts.comparisonPatch_product_tube (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts W' d) (hport : C.port = D.port)
    (hmatrix : ∀ m, C.matrix m = D.matrix m) (m : Fin d.fillingCount) (x : W.Carrier)
    (hp : x ∈ (C.comparisonPatch D none).source)
    (ht : x ∈ (C.comparisonPatch D (some m)).source) :
    C.comparisonPatch D none x = C.comparisonPatch D (some m) x := by
  rw [C.comparisonPatch_none_source D] at hp
  rw [C.comparisonPatch_some_source D m x] at ht
  have htrans : (C.tube m).symm x ∈ C.transitionDomain := by
    have himage : x ∈ C.tube m '' C.transitionDomain :=
      C.tube_product_overlap m ▸ ⟨ht.1, hp⟩
    obtain ⟨y, hy, he⟩ := himage
    have hsrc : y ∈ (C.tube m).source := by
      rw [C.tube_source]
      rw [C.transitionDomain_eq] at hy
      exact hy.2
    rw [← he, (C.tube m).symm_apply_apply hsrc]
    exact hy
  have hd : (C.tube m).symm x ∈ D.transitionDomain := by
    rw [D.transitionDomain_eq]
    rw [C.transitionDomain_eq] at htrans
    exact ⟨htrans.1, ht.2⟩
  have he := C.comparisonPatch_none_tube D hport hmatrix m ((C.tube m).symm x)
    htrans hd
  rw [(C.tube m).apply_symm_apply ht.1] at he
  exact he

theorem SeifertBlockCharts.comparisonPatch_forward (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts W' d) (hport : C.port = D.port)
    (hmatrix : ∀ m, C.matrix m = D.matrix m)
    (i j : Option (Fin d.fillingCount)) (x : W.Carrier)
    (hi : x ∈ (C.comparisonPatch D i).source)
    (hj : x ∈ (C.comparisonPatch D j).source) :
    C.comparisonPatch D i x = C.comparisonPatch D j x := by
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some n => exact C.comparisonPatch_product_tube D hport hmatrix n x hi hj
  | some m =>
    cases j with
    | none => exact (C.comparisonPatch_product_tube D hport hmatrix m x hj hi).symm
    | some n =>
      by_cases hmn : m = n
      · subst n
        rfl
      · have hm := ((C.comparisonPatch_some_source D m x).mp hi).1
        have hn := ((C.comparisonPatch_some_source D n x).mp hj).1
        exact False.elim (Set.disjoint_left.mp (C.disjoint hmn) hm hn)

theorem SeifertBlockCharts.comparisonPatch_symm (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts W' d) (i : Option (Fin d.fillingCount)) :
    (C.comparisonPatch D i).symm = D.comparisonPatch C i := by
  cases i <;> rfl

theorem SeifertBlockCharts.comparisonPatch_source_interior (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts W' d) (i : Option (Fin d.fillingCount)) :
    (C.comparisonPatch D i).source ⊆ W.pieceInterior ⊤ := by
  intro x hx
  refine ⟨trivial, ?_⟩
  cases i with
  | none =>
    rw [C.comparisonPatch_none_source D] at hx
    exact C.productRegion_interior hx
  | some m =>
    exact C.tube_interior m (((C.comparisonPatch_some_source D m x).mp hx).1)

def SeifertBlockCharts.compareInterior (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts W' d) (hport : C.port = D.port)
    (hmatrix : ∀ m, C.matrix m = D.matrix m) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, W'.model⟯ W'.pieceInterior ⊤ := by
  let z := Classical.choice (normalPlanarOpen_nonempty d.k)
  have hW : Nonempty (W.pieceInterior ⊤) :=
    ⟨⟨C.product (z, 1), trivial, C.productRegion_interior (C.product (z, 1)).property⟩⟩
  have hW' : Nonempty (W'.pieceInterior ⊤) :=
    ⟨⟨D.product (z, 1), trivial, D.productRegion_interior (D.product (z, 1)).property⟩⟩
  apply gluePartialDiffeomorphsOnOpens (C.comparisonPatch D)
    (W.pieceInterior ⊤) (W'.pieceInterior ⊤) hW hW'
  · exact C.comparisonPatch_source_interior D
  · intro i
    rw [← PartialDiffeomorph.symm_source,
      C.comparisonPatch_symm D i]
    exact D.comparisonPatch_source_interior C i
  · intro x hx
    exact C.comparisonPatch_source_cover D x hx.2
  · intro x hx
    obtain ⟨i, hi⟩ := D.comparisonPatch_source_cover C x hx.2
    refine ⟨i, ?_⟩
    rw [← PartialDiffeomorph.symm_source, C.comparisonPatch_symm D i]
    exact hi
  · exact C.comparisonPatch_forward D hport hmatrix
  · intro i j y hi hj
    rw [C.comparisonPatch_symm D i, C.comparisonPatch_symm D j]
    rw [← PartialDiffeomorph.symm_source, C.comparisonPatch_symm D i] at hi
    rw [← PartialDiffeomorph.symm_source, C.comparisonPatch_symm D j] at hj
    exact D.comparisonPatch_forward C hport.symm (fun m => (hmatrix m).symm) i j y hi hj

end Compare


def normalInnerOneInteriorDiffeomorph {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q)) (hport : C.port (.inr 0) = (1 : Fin 3)) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, 𝓡 3⟯ TorusTimesLine := by
  let c := normalChartFilling C
  let D : SeifertBlockCharts c.filledCarrier.{u} (normalT2IntervalDatum q) :=
    c.normalInnerReferenceCharts rfl C.port hport
  exact (C.compareInterior D rfl (normalChartFilling_matrix C)).trans
    (normalConeInteriorDiffeomorph c rfl)

def normalInnerOneGeometry {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q)) (hport : C.port (.inr 0) = (1 : Fin 3)) :
    W.InteriorGeometry ⊤ :=
  normalTorusIntervalGeometryOfDiffeomorph (normalInnerOneInteriorDiffeomorph C hport)

theorem normalInnerOneGeometry_model {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q)) (hport : C.port (.inr 0) = (1 : Fin 3)) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (normalInnerOneGeometry C hport).model = ThurstonModel.euclidean := rfl

theorem normalPantsOpen_neg_mem {z : ℂ} (hz : z ∈ planarOpen 3) :
    -z ∈ planarOpen 3 :=
  (Homeomorph.neg ℂ).isOpenMap.mapsTo_interior
    (fun x hx => ElementaryPresentation.cappingPants_neg_mem x hx) hz

def normalPantsOpenNeg : planarOpen 3 ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ planarOpen 3 where
  toFun z := ⟨-z.val, normalPantsOpen_neg_mem z.property⟩
  invFun z := ⟨-z.val, normalPantsOpen_neg_mem z.property⟩
  left_inv z := Subtype.ext (neg_neg z.val)
  right_inv z := Subtype.ext (neg_neg z.val)
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff (planarOpen 3) _).mp (contMDiff_subtype_val.neg)
  contMDiff_invFun :=
    (ContMDiff.subtypeVal_comp_iff (planarOpen 3) _).mp (contMDiff_subtype_val.neg)

def normalTubeTranslation (v : Torus) :
    (ℂ × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯ (ℂ × Circle) where
  toFun y := ((v.1 : ℂ) * y.1, v.2 * y.2)
  invFun y := ((v.1⁻¹ : Circle) * y.1, v.2⁻¹ * y.2)
  left_inv y := by
    apply Prod.ext
    · change (v.1⁻¹ : Circle) * ((v.1 : ℂ) * y.1) = y.1
      rw [← mul_assoc, Circle.coe_inv, inv_mul_cancel₀ (Circle.coe_ne_zero v.1), one_mul]
    · exact inv_mul_cancel_left v.2 y.2
  right_inv y := by
    apply Prod.ext
    · change (v.1 : ℂ) * ((v.1⁻¹ : Circle) * y.1) = y.1
      rw [← mul_assoc, Circle.coe_inv, mul_inv_cancel₀ (Circle.coe_ne_zero v.1), one_mul]
    · exact mul_inv_cancel_left v.2 y.2
  contMDiff_toFun :=
    ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_fst).prodMk
      (contMDiff_const.mul contMDiff_snd)
  contMDiff_invFun :=
    ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_fst).prodMk
      (contMDiff_const.mul contMDiff_snd)

theorem normalTubeTranslation_norm (v : Torus) (y : ℂ × Circle) :
    ‖(normalTubeTranslation v y).1‖ = ‖y.1‖ := by
  change ‖(v.1 : ℂ) * y.1‖ = _
  rw [norm_mul, Circle.norm_coe, one_mul]

theorem normalLinearTorusMap_mul_point (A : Matrix (Fin 2) (Fin 2) ℤ) (v w : Torus) :
    linearTorusMap A (v * w) = linearTorusMap A v * linearTorusMap A w := by
  apply Prod.ext <;> simp only [linearTorusMap, Prod.fst_mul, Prod.snd_mul, mul_zpow]
  · exact mul_mul_mul_comm _ _ _ _
  · exact mul_mul_mul_comm _ _ _ _

def normalPantsTubeNegation (A : GL (Fin 2) ℤ) : Torus :=
  (linearTorusDiffeomorph A).symm (circleI ^ 2, 1)

theorem normalPantsTubeNegation_image (A : GL (Fin 2) ℤ) :
    linearTorusMap A (normalPantsTubeNegation A) = (circleI ^ 2, 1) :=
  (linearTorusDiffeomorph A).apply_symm_apply (circleI ^ 2, 1)

theorem normalPantsSeamNeg (q : ℤ) (m : Fin (normalT2IntervalDatum q).fillingCount)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (hy : y.1 ≠ 0) :
    (-(seamModel (normalT2IntervalDatum q) m (1 : Fin 3) A y).1,
      (seamModel (normalT2IntervalDatum q) m (1 : Fin 3) A y).2) =
      seamModel (normalT2IntervalDatum q) m (2 : Fin 3) A
        (normalTubeTranslation (normalPantsTubeNegation A) y) := by
  let v := normalPantsTubeNegation A
  have ht : linearTorusMap A
      (unitOf (normalTubeTranslation v y).1, (normalTubeTranslation v y).2) =
        (circleI ^ 2, 1) * linearTorusMap A (unitOf y.1, y.2) := by
    change linearTorusMap A (unitOf ((v.1 : ℂ) * y.1), v.2 * y.2) = _
    rw [unitOf_mul (Circle.coe_ne_zero v.1) hy, unitOf_circle]
    change linearTorusMap A (v * (unitOf y.1, y.2)) = _
    rw [normalLinearTorusMap_mul_point, normalPantsTubeNegation_image]
  dsimp only [v] at ht
  simp only [seamModel, normalT2IntervalDatum_fillingSlope, Int.natAbs_one,
    normalTubeTranslation_norm, pow_one, Fin.val_one, one_ne_zero, ite_false,
    show (2 : Fin 3).val = 2 from rfl, show (2 : ℕ) ≠ 0 by decide, ht,
    Prod.fst_mul, Prod.snd_mul, one_mul]
  apply Prod.ext
  · simp only [planarCenter, planarRadius, Circle.coe_mul, circleI_sq_coe,
      neg_one_mul, map_neg]
    norm_num [normalT2IntervalDatum]
    ring
  · rfl

def normalTubeTranslated {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q)) :
    PartialDiffeomorph PlaneCircleModel W.model (ℂ × Circle) W.Carrier ∞ :=
  (normalTubeTranslation (normalPantsTubeNegation (C.matrix 0))).toPartialDiffeomorph.trans
    (C.tube 0)

theorem normalTubeTranslated_source {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q)) :
    (normalTubeTranslated C).source = {y : ℂ × Circle | ‖y.1‖ < 1 + C.ε} := by
  ext y
  change (y ∈ Set.univ ∧ normalTubeTranslation (normalPantsTubeNegation (C.matrix 0)) y ∈
    (C.tube 0).source) ↔ _
  rw [C.tube_source]
  simp only [Set.mem_univ, true_and, Set.mem_ofPred_eq, normalTubeTranslation_norm]

theorem normalTubeTranslated_target {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q)) :
    (normalTubeTranslated C).target = (C.tube 0).target := by
  ext x
  change (x ∈ (C.tube 0).target ∧ (C.tube 0).symm x ∈ Set.univ) ↔ _
  simp only [Set.mem_univ, and_true]

def normalInnerTwoCharts {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q))
    (hport : C.port (.inr 0) = (2 : Fin 3)) :
    SeifertBlockCharts W (normalT2IntervalDatum q) where
  port := C.port.trans (Equiv.swap (1 : Fin 3) (2 : Fin 3))
  matrix := C.matrix
  a := C.a
  b := C.b
  matrix_eq := C.matrix_eq
  bezout := C.bezout
  productRegion := C.productRegion
  productRegion_interior := C.productRegion_interior
  product := (normalPantsOpenNeg.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans C.product
  ε := C.ε
  ε_pos := C.ε_pos
  tube m := normalTubeTranslated C
  tube_source m := normalTubeTranslated_source C
  tube_interior m := normalTubeTranslated_target C ▸ C.tube_interior 0
  transitionDomain := C.transitionDomain
  transitionDomain_eq := C.transitionDomain_eq
  transition_domain m y hy := by
    have hm : m = 0 := Fin.eq_zero m
    subst m
    have hQ : normalTubeTranslation (normalPantsTubeNegation (C.matrix 0)) y ∈
        C.transitionDomain := by
      rw [C.transitionDomain_eq] at hy ⊢
      simpa only [Set.mem_ofPred_eq, normalTubeTranslation_norm] using hy
    have hold := C.transition_domain 0 hQ
    have hnorm : y.1 ≠ 0 := by
      rw [C.transitionDomain_eq] at hy
      exact norm_pos_iff.mp (by linarith [hy.1])
    rw [hport] at hold
    have hs := congrArg Prod.fst (normalPantsSeamNeg q 0 (C.matrix 0) y hnorm)
    change (seamModel (normalT2IntervalDatum q) 0
      (Equiv.swap (1 : Fin 3) (2 : Fin 3) (C.port (.inr 0))) (C.matrix 0) y).1 ∈ planarOpen 3
    rw [hport, Equiv.swap_apply_right]
    have hn := normalPantsOpen_neg_mem hold
    simpa only [← hs, neg_neg] using hn
  transition m y hy := by
    have hm : m = 0 := Fin.eq_zero m
    subst m
    let Q := normalTubeTranslation (normalPantsTubeNegation (C.matrix 0))
    have hQ : Q y ∈ C.transitionDomain := by
      rw [C.transitionDomain_eq] at hy ⊢
      simpa only [Q, Set.mem_ofPred_eq, normalTubeTranslation_norm] using hy
    have hold := C.transition 0 (Q y) hQ
    change C.tube 0 (Q y) = _
    rw [hold]
    change (C.product _ : W.Carrier) = (C.product _ : W.Carrier)
    apply congrArg (fun z : planarOpen 3 × Circle => (C.product z : W.Carrier))
    have hnorm : y.1 ≠ 0 := by
      rw [C.transitionDomain_eq] at hy
      exact norm_pos_iff.mp (by linarith [hy.1])
    have hs := normalPantsSeamNeg q 0 (C.matrix 0) y hnorm
    apply Prod.ext
    · apply Subtype.ext
      change (seamModel (normalT2IntervalDatum q) 0 (C.port (.inr 0))
        (C.matrix 0) (Q y)).1 =
        -(seamModel (normalT2IntervalDatum q) 0
          (Equiv.swap (1 : Fin 3) (2 : Fin 3) (C.port (.inr 0)))
          (C.matrix 0) y).1
      rw [hport, Equiv.swap_apply_right]
      exact (congrArg Prod.fst hs).symm
    · change (seamModel (normalT2IntervalDatum q) 0 (C.port (.inr 0))
        (C.matrix 0) (Q y)).2 =
        (seamModel (normalT2IntervalDatum q) 0
          (Equiv.swap (1 : Fin 3) (2 : Fin 3) (C.port (.inr 0)))
          (C.matrix 0) y).2
      rw [hport, Equiv.swap_apply_right]
      exact (congrArg Prod.snd hs).symm
  tube_product_overlap m := by
    rw [normalTubeTranslated_target, C.tube_product_overlap 0]
    ext x
    constructor
    · rintro ⟨y, hy, hx⟩
      let Q := normalTubeTranslation (normalPantsTubeNegation (C.matrix 0))
      refine ⟨Q.symm y, ?_, ?_⟩
      · rw [C.transitionDomain_eq] at hy ⊢
        have hn : ‖(Q.symm y).1‖ = ‖y.1‖ := by
          rw [← normalTubeTranslation_norm (normalPantsTubeNegation (C.matrix 0))
            (Q.symm y), Q.apply_symm_apply]
        simpa only [Set.mem_ofPred_eq, hn] using hy
      · change C.tube 0 (Q (Q.symm y)) = x
        rw [Q.apply_symm_apply]
        exact hx
    · rintro ⟨y, hy, hx⟩
      refine ⟨normalTubeTranslation (normalPantsTubeNegation (C.matrix 0)) y, ?_, hx⟩
      rw [C.transitionDomain_eq] at hy ⊢
      simpa only [Set.mem_ofPred_eq, normalTubeTranslation_norm] using hy
  disjoint := by
    intro m n hmn
    change Fin 1 at m n
    exact False.elim (hmn (Subsingleton.elim m n))
  covers x hx := by
    rcases C.covers x hx with hp | ⟨m, hm⟩
    · exact Or.inl hp
    · have hz : m = 0 := Fin.eq_zero m
      subst m
      exact Or.inr ⟨0, normalTubeTranslated_target C ▸ hm⟩

theorem normalInnerTwoCharts_filledPort {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q))
    (hport : C.port (.inr 0) = (2 : Fin 3)) :
    (normalInnerTwoCharts C hport).port (.inr 0) = (1 : Fin 3) := by
  change Equiv.swap (1 : Fin 3) (2 : Fin 3) (C.port (.inr 0)) = (1 : Fin 3)
  rw [hport, Equiv.swap_apply_right]

def normalInnerTwoInteriorDiffeomorph {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q))
    (hport : C.port (.inr 0) = (2 : Fin 3)) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, 𝓡 3⟯ TorusTimesLine :=
  normalInnerOneInteriorDiffeomorph (normalInnerTwoCharts C hport)
    (normalInnerTwoCharts_filledPort C hport)

def normalInnerTwoGeometry {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q))
    (hport : C.port (.inr 0) = (2 : Fin 3)) : W.InteriorGeometry ⊤ :=
  normalTorusIntervalGeometryOfDiffeomorph (normalInnerTwoInteriorDiffeomorph C hport)

theorem normalInnerTwoGeometry_model {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q))
    (hport : C.port (.inr 0) = (2 : Fin 3)) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (normalInnerTwoGeometry C hport).model = ThurstonModel.euclidean := rfl

def normalRetainedInnerPhase (q : ℤ) (t : Circle) : Circle :=
  unitOf (planarCircleMap 3 (2 : Fin 3) t - (3 / 2 : ℂ)) ^ q

theorem normalRetainedInnerPhase_smooth (q : ℤ) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (normalRetainedInnerPhase q) := by
  have hs : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun t : Circle => planarCircleMap 3 (2 : Fin 3) t - (3 / 2 : ℂ)) := by
    have hv (t : Circle) : planarCircleMap 3 (2 : Fin 3) t =
        (-3 / 2 : ℂ) + (1 / 2 : ℂ) * conj (t : ℂ) := by
      simp [planarCircleMap, planarCenter, planarRadius]
      ring
    simp_rw [hv]
    exact contMDiff_const.add
      (((contDiff_const.mul Complex.conjCLE.contDiff).contMDiff).comp
        contMDiff_circle_coe) |>.sub contMDiff_const
  have hne (t : Circle) : planarCircleMap 3 (2 : Fin 3) t - (3 / 2 : ℂ) ≠ 0 := by
    have hf := ConeFilling.productCollar_far.{0} (1 : Fin 2)
      (zero_mem_halfCollarSource (t, (1 : Circle)))
    change 5 / 4 < ‖(planarCollar.{0} 3 (Or.inr rfl) 2 (t, halfZero)).val.down -
      ((3 / 2 : ℝ) : ℂ)‖ at hf
    rw [planarCollar_zero_val] at hf
    apply norm_pos_iff.mp
    exact lt_trans (by norm_num : (0 : ℝ) < 5 / 4) (by simpa using hf)
  exact (contMDiff_circle_zpow q).comp
    (contMDiffOn_unitOf.comp_contMDiff hs hne)

def normalRetainedInnerTwist (q : ℤ) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus where
  toFun t := (t.1, normalRetainedInnerPhase q t.1 * t.2)
  invFun t := (t.1, (normalRetainedInnerPhase q t.1)⁻¹ * t.2)
  left_inv t := by simp
  right_inv t := by simp
  contMDiff_toFun := contMDiff_fst.prodMk
    (((normalRetainedInnerPhase_smooth q).comp contMDiff_fst).mul contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk
    (((normalRetainedInnerPhase_smooth q).inv.comp contMDiff_fst).mul contMDiff_snd)

def normalAnnulusInnerPhase (q : ℤ) (x : planarSet.{u} 2) : Circle :=
  normalRetainedInnerPhase q ((unitOf x.val.down)⁻¹)

theorem normalAnnulusInnerPhase_smooth (q : ℤ) :
    ContMDiff (𝓡∂ 2) (𝓡 1) ∞ (normalAnnulusInnerPhase.{u} q) := by
  have hne (x : planarSet.{u} 2) : x.val.down ≠ 0 := by
    have hx := ((mem_planarModel_two x.val.down).mp
      ((mem_planarSet_iff (Or.inl rfl) x.val).mp x.property)).2
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hx)
  exact (normalRetainedInnerPhase_smooth q).comp
    ((contMDiffOn_unitOf.comp_contMDiff (contMDiff_planarSet_down 2) hne).inv)

def normalAnnulusInnerUntwist (q : ℤ) :
    (planarSet.{u} 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), (𝓡∂ 2).prod (𝓡 1)⟯
      (planarSet.{u} 2 × Circle) where
  toFun x := (x.1, (normalAnnulusInnerPhase q x.1)⁻¹ * x.2)
  invFun x := (x.1, normalAnnulusInnerPhase q x.1 * x.2)
  left_inv x := by simp
  right_inv x := by simp
  contMDiff_toFun := contMDiff_fst.prodMk
    (((normalAnnulusInnerPhase_smooth q).inv.comp contMDiff_fst).mul contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk
    (((normalAnnulusInnerPhase_smooth q).comp contMDiff_fst).mul contMDiff_snd)

def normalAnnulusInnerUntwistCarrier (q : ℤ) :
    annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model,
      annulusCircleCarrier.{u}.model⟯ annulusCircleCarrier.{u}.Carrier :=
  (productDiffeomorph 2).symm.trans
    ((normalAnnulusInnerUntwist q).trans (productDiffeomorph 2))

theorem normalAnnulusInnerPhase_collar (q : ℤ) (t : Circle) :
    normalAnnulusInnerPhase.{u} q (planarCollar 2 (Or.inl rfl) 1 (t, halfZero)) =
      normalRetainedInnerPhase q t := by
  unfold normalAnnulusInnerPhase
  rw [planarCollar_zero_val]
  have he : planarCircleMap 2 (1 : Fin 2) t = (1 / 2 : ℝ) • ((t⁻¹ : Circle) : ℂ) := by
    rw [Circle.coe_inv_eq_conj]
    simp [planarCircleMap, planarCenter, planarRadius, Complex.real_smul]
  rw [he, unitOf_smul (by norm_num), inv_inv]

theorem normalAnnulusInnerUntwistCarrier_zero (q : ℤ) (t : Torus) :
    normalAnnulusInnerUntwistCarrier.{u} q
      (productCollar 2 (Or.inl rfl) 1 (normalRetainedInnerTwist q t, halfZero)) =
        productCollar 2 (Or.inl rfl) 1 (t, halfZero) := by
  change productDiffeomorph 2
    (normalAnnulusInnerUntwist q ((productDiffeomorph 2).symm
      (productDiffeomorph 2
        (planarCollar 2 (Or.inl rfl) 1 (t.1, halfZero),
          normalRetainedInnerPhase q t.1 * t.2)))) = _
  rw [Diffeomorph.symm_apply_apply]
  change productDiffeomorph 2
    (planarCollar 2 (Or.inl rfl) 1 (t.1, halfZero),
      (normalAnnulusInnerPhase q
        (planarCollar 2 (Or.inl rfl) 1 (t.1, halfZero)))⁻¹ *
          (normalRetainedInnerPhase q t.1 * t.2)) = _
  rw [normalAnnulusInnerPhase_collar, inv_mul_cancel_left]
  rfl

theorem normalConeFilledDiffeomorph_retained_zero (c : ConeFilling) (hp : c.p = 1)
    (t : Torus) :
    normalConeFilledDiffeomorph c hp (c.externalCollar.{u} 1 (t, halfZero)) =
      (Merge.sectionFilling 0).externalCollar.{u} 1
        (normalRetainedInnerTwist c.q t, halfZero) := by
  apply Subtype.ext
  apply Prod.ext
  · apply ULift.ext
    have he := normalConePoint_basis c hp (c.externalCollar.{u} 1 (t, halfZero)).val
    rw [c.conePoint_externalCollar_zero,
      Merge.conePoint_sectionFilling] at he
    have ht := (Merge.sectionFilling 0).conePoint_externalCollar_zero.{u} 1
      (normalRetainedInnerTwist c.q t)
    rw [Merge.conePoint_sectionFilling] at ht
    change (solidBasisLift false false (-c.a)
      (c.externalCollar.{u} 1 (t, halfZero)).val).1.down =
        ((Merge.sectionFilling 0).externalCollar.{u} 1
        (normalRetainedInnerTwist c.q t, halfZero)).val.1.down
    change ((3 / 2 : ℝ) : ℂ) +
      ((Merge.sectionFilling 0).externalCollar.{u} 1
        (normalRetainedInnerTwist c.q t, halfZero)).val.1.down / 6 =
          planarCircleMap 3 (ConeFilling.externalPort 1) t.1 at ht
    linear_combination (6 : ℂ) * he - (6 : ℂ) * ht
  · change (c.externalCollar.{u} 1 (t, halfZero)).val.2 =
      ((Merge.sectionFilling 0).externalCollar.{u} 1
        (normalRetainedInnerTwist c.q t, halfZero)).val.2
    rw [c.externalCollar_apply_val 1 (zero_mem_halfCollarSource t),
      (Merge.sectionFilling 0).externalCollar_apply_val 1
        (zero_mem_halfCollarSource (normalRetainedInnerTwist c.q t))]
    have hs (x : PlaneLift.{u} × Circle) : (c.coneLift x).2 =
        unitOf (x.1.down - (3 / 2 : ℂ)) ^ c.q * x.2 := by
      simp [ConeFilling.coneLift, ConeFilling.coneTorus, ConeFilling.liftMatrix,
        linearTorusMap, hp]
    rw [hs, Merge.coneLift_snd_sectionFilling]
    simp only [zpow_zero, one_mul]
    change unitOf ((planarCollar.{u} 3 (Or.inr rfl) 2
      (t.1, halfZero)).val.down - (3 / 2 : ℂ)) ^ c.q * t.2 =
        normalRetainedInnerPhase c.q t.1 * t.2
    rw [planarCollar_zero_val]
    rfl

theorem sectionCappingAnnulusProductDiffeomorph_inner_zero (t : Torus) :
    ElementaryPresentation.sectionCappingAnnulusProductDiffeomorph.{u} 0
      (planarCollar 2 (Or.inl rfl) 1 (t.1, halfZero), t.2) =
        (Merge.sectionFilling 0).externalCollar.{u} 1 (t, halfZero) := by
  apply (ElementaryPresentation.sectionCappingDiffeomorph 0).symm.injective
  change (ElementaryPresentation.sectionCappingDiffeomorph 0).symm
    ((ElementaryPresentation.sectionCappingDiffeomorph 0)
      (ElementaryPresentation.cappingAnnulusDiffeomorph
        (planarCollar 2 (Or.inl rfl) 1 (t.1, halfZero)), t.2)) = _
  rw [Diffeomorph.symm_apply_apply]
  have he := ElementaryPresentation.sectionCappingDiffeomorph_retainedCollar.{u} 0 1
    (t, halfZero) (zero_mem_halfCollarSource t)
  apply Prod.ext
  · apply Subtype.ext
    apply ULift.ext
    exact (ElementaryPresentation.cappingAnnulusForward_inner.{u} t.1).trans
      (by
        have hh := he.1.symm
        change (planarCollar.{u} 3 (Or.inr rfl) 2
          (t.1, halfZero)).val.down = _ at hh
        rw [planarCollar_zero_val] at hh
        exact hh)
  · simpa using he.2.symm

theorem normalConeAnnulusDiffeomorph_inner_zero (c : ConeFilling) (hp : c.p = 1)
    (t : Torus) :
    normalConeAnnulusDiffeomorph.{u} c hp (c.externalCollar.{u} 1 (t, halfZero)) =
      productCollar.{u} 2 (Or.inl rfl) 1
        (normalRetainedInnerTwist c.q t, halfZero) := by
  change productDiffeomorph 2
    ((ElementaryPresentation.sectionCappingAnnulusProductDiffeomorph 0).symm
      (normalConeFilledDiffeomorph c hp (c.externalCollar.{u} 1 (t, halfZero)))) = _
  rw [normalConeFilledDiffeomorph_retained_zero]
  rw [← sectionCappingAnnulusProductDiffeomorph_inner_zero,
    Diffeomorph.symm_apply_apply]
  rfl

theorem exists_normalConeAnnulus_inner_germ (c : ConeFilling) (hp : c.p = 1) :
    ∃ δ > (0 : ℝ), ∃ e : c.filledCarrier.{u}.Carrier ≃ₘ⟮
      c.filledCarrier.{u}.model, annulusCircleCarrier.{u}.model⟯
        annulusCircleCarrier.{u}.Carrier,
      (∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource → p.2.val 0 < δ →
        e (c.externalCollar 1 p) = productCollar 2 (Or.inl rfl) 1
          (normalRetainedInnerTwist c.q p.1, p.2)) ∧
      ∀ x, normalConeAnnulusDiffeomorph c hp x ∉
        (productCollar 2 (Or.inl rfl) 1).target →
          e x = normalConeAnnulusDiffeomorph c hp x := by
  let e := normalConeAnnulusDiffeomorph.{u} c hp
  let B := c.external.transport e
  let c₀ := B.collar 1
  let ψ := normalRetainedInnerTwist c.q
  let c₁ : PartialDiffeomorph halfCollarModel annulusCircleCarrier.{u}.model
      (Torus × EuclideanHalfSpace 1) annulusCircleCarrier.{u}.Carrier ∞ :=
    PartialDiffeomorph.trans
      (ψ.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph
      (productCollar.{u} 2 (Or.inl rfl) 1)
  have hsrc (t : Torus) : (t, halfZero) ∈ c₀.source ∩ c₁.source := by
    constructor
    · rw [B.source_eq]
      exact zero_mem_halfCollarSource t
    · exact ⟨Set.mem_univ _, zero_mem_halfCollarSource (ψ t)⟩
  have h₀ (t : Torus) : c₀ (t, halfZero) = c₁ (t, halfZero) :=
    normalConeAnnulusDiffeomorph_inner_zero c hp t
  have hK : Set.range (fun t => c₀ (t, halfZero)) ⊆ c₁.target := by
    rintro x ⟨t, rfl⟩
    change c₀ (t, halfZero) ∈ c₁.target
    rw [h₀]
    exact c₁.map_source' (hsrc t).2
  obtain ⟨δ, hδ, Φ, hagree, hfix⟩ := exists_torusCollar_straightening c₀ c₁ hsrc h₀
    (B.boundary_zero 1) c₁.open_target hK
  refine ⟨δ, hδ, e.trans Φ, ?_, ?_⟩
  · intro p hsource hsmall
    exact hagree p.1 p.2 hsmall
  · intro x hx
    apply hfix
    change e x ∉ (productCollar 2 (Or.inl rfl) 1).target ∩
      (productCollar 2 (Or.inl rfl) 1).symm ⁻¹' Set.univ
    exact fun hm => hx hm.1

def normalConeAnnulusInnerDiffeomorph (c : ConeFilling) (hp : c.p = 1) :
    c.filledCarrier.{u}.Carrier ≃ₘ⟮c.filledCarrier.{u}.model,
      annulusCircleCarrier.{u}.model⟯ annulusCircleCarrier.{u}.Carrier :=
  (normalConeAnnulusDiffeomorph c hp).trans (normalAnnulusInnerUntwistCarrier c.q)

theorem normalConeAnnulusInnerDiffeomorph_zero (c : ConeFilling) (hp : c.p = 1)
    (t : Torus) :
    normalConeAnnulusInnerDiffeomorph.{u} c hp (c.externalCollar 1 (t, halfZero)) =
      productCollar 2 (Or.inl rfl) 1 (t, halfZero) := by
  change normalAnnulusInnerUntwistCarrier c.q
    (normalConeAnnulusDiffeomorph c hp (c.externalCollar 1 (t, halfZero))) = _
  rw [normalConeAnnulusDiffeomorph_inner_zero, normalAnnulusInnerUntwistCarrier_zero]

theorem exists_normalConeAnnulus_inner_standard_germ (c : ConeFilling) (hp : c.p = 1) :
    ∃ δ > (0 : ℝ), ∃ e : c.filledCarrier.{u}.Carrier ≃ₘ⟮
      c.filledCarrier.{u}.model, annulusCircleCarrier.{u}.model⟯
        annulusCircleCarrier.{u}.Carrier,
      (∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource → p.2.val 0 < δ →
        e (c.externalCollar 1 p) = productCollar 2 (Or.inl rfl) 1 p) ∧
      ∀ x, normalConeAnnulusInnerDiffeomorph c hp x ∉
        (productCollar 2 (Or.inl rfl) 1).target →
          e x = normalConeAnnulusInnerDiffeomorph c hp x := by
  let e := normalConeAnnulusInnerDiffeomorph.{u} c hp
  let B := c.external.transport e
  let c₀ := B.collar 1
  let c₁ : PartialDiffeomorph halfCollarModel annulusCircleCarrier.{u}.model
      (Torus × EuclideanHalfSpace 1) annulusCircleCarrier.{u}.Carrier ∞ :=
    productCollar.{u} 2 (Or.inl rfl) 1
  have hsrc (t : Torus) : (t, halfZero) ∈ c₀.source ∩ c₁.source := by
    constructor
    · rw [B.source_eq]
      exact zero_mem_halfCollarSource t
    · exact zero_mem_halfCollarSource t
  have h₀ (t : Torus) : c₀ (t, halfZero) = c₁ (t, halfZero) :=
    normalConeAnnulusInnerDiffeomorph_zero c hp t
  have hK : Set.range (fun t => c₀ (t, halfZero)) ⊆ c₁.target := by
    rintro x ⟨t, rfl⟩
    change c₀ (t, halfZero) ∈ c₁.target
    rw [h₀]
    exact c₁.map_source' (hsrc t).2
  obtain ⟨δ, hδ, Φ, hagree, hfix⟩ := exists_torusCollar_straightening c₀ c₁ hsrc h₀
    (B.boundary_zero 1) c₁.open_target hK
  refine ⟨δ, hδ, e.trans Φ, ?_, ?_⟩
  · intro p hsource hsmall
    exact hagree p.1 p.2 hsmall
  · intro x hx
    exact hfix hx

section SelectedFillingComparison

universe v

def selectedPlanarOpenCast {k l : ℕ} (h : k = l) :
    planarOpen k ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ planarOpen l := by
  subst l
  exact Diffeomorph.refl _ _ _

theorem selectedPlanarOpenCast_val {k l : ℕ} (h : k = l) (x : planarOpen k) :
    (selectedPlanarOpenCast h x).val = x.val := by
  subst l
  rfl

theorem selectedPlanarOpenCast_symm {k l : ℕ} (h : k = l) :
    (selectedPlanarOpenCast h).symm = selectedPlanarOpenCast h.symm := by
  subst l
  rfl

variable {W : CompactCarrier.{u}} {V : CompactCarrier.{v}} {d e : SeifertData}

def SeifertBlockCharts.selectedFilledRegion (C : SeifertBlockCharts W d)
    (m : Fin d.fillingCount) : TopologicalSpace.Opens W.Carrier :=
  C.productRegion ⊔ ⟨(C.tube m).target, (C.tube m).open_target⟩

def SeifertBlockCharts.selectedComparisonProduct (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts V e) (hk : d.k = e.k) :
    PartialDiffeomorph W.model V.model W.Carrier V.Carrier ∞ :=
  C.productAmbient.symm.trans
    (PartialDiffeomorph.trans
      ((selectedPlanarOpenCast hk).prodCongr
        (Diffeomorph.refl (𝓡 1) Circle ∞)).toPartialDiffeomorph D.productAmbient)

theorem SeifertBlockCharts.selectedComparisonProduct_source (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts V e) (hk : d.k = e.k) :
    (C.selectedComparisonProduct D hk).source = C.productRegion := by
  ext x
  change x ∈ C.productAmbient.target ∧
    C.productAmbient.symm x ∈ Set.univ ∩
      ((selectedPlanarOpenCast hk).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)) ⁻¹'
        D.productAmbient.source ↔ x ∈ C.productRegion
  rw [C.productAmbient_target, D.productAmbient_source]
  simp

theorem SeifertBlockCharts.selectedComparisonProduct_target (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts V e) (hk : d.k = e.k) :
    (C.selectedComparisonProduct D hk).target = D.productRegion := by
  ext x
  change (x ∈ D.productAmbient.target ∧ D.productAmbient.symm x ∈ Set.univ) ∧
    ((selectedPlanarOpenCast hk).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).symm
      (D.productAmbient.symm x) ∈ C.productAmbient.source ↔ x ∈ D.productRegion
  rw [D.productAmbient_target, C.productAmbient_source]
  simp

theorem SeifertBlockCharts.selectedComparisonProduct_symm_apply
    (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (x : V.Carrier) :
    (C.selectedComparisonProduct D hk).symm x = D.selectedComparisonProduct C hk.symm x := by
  change C.productAmbient
    (((selectedPlanarOpenCast hk).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).symm
      (D.productAmbient.symm x)) = _
  rw [Diffeomorph.prodCongr_symm, selectedPlanarOpenCast_symm]
  rfl

theorem selectedSeamModel_eq (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e)
    (hk : d.k = e.k) (m : Fin d.fillingCount) (n : Fin e.fillingCount)
    (hs : d.fillingSlope m = e.fillingSlope n)
    (hp : Fin.cast hk (C.port (.inr m)) = D.port (.inr n))
    (hA : C.matrix m = D.matrix n) (y : ℂ × Circle) :
    seamModel d m (C.port (.inr m)) (C.matrix m) y =
      seamModel e n (D.port (.inr n)) (D.matrix n) y := by
  have hj : (C.port (.inr m)).val = (D.port (.inr n)).val :=
    congrArg Fin.val hp
  simp only [seamModel, hs, hA, planarCenter, planarRadius, hk, hj]

def SeifertBlockCharts.selectedComparisonPatch (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount) (b : Bool) :
    PartialDiffeomorph W.model V.model W.Carrier V.Carrier ∞ :=
  if b then (C.tube m).symm.trans (D.tube n) else C.selectedComparisonProduct D hk

theorem SeifertBlockCharts.selectedComparisonPatch_source (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount) (b : Bool) (x : W.Carrier) :
    x ∈ (C.selectedComparisonPatch D hk m n b).source ↔
      if b then x ∈ (C.tube m).target ∧ ‖((C.tube m).symm x).1‖ < 1 + D.ε
        else x ∈ C.productRegion := by
  cases b
  · simp only [selectedComparisonPatch, Bool.false_eq_true, ite_false]
    rw [C.selectedComparisonProduct_source]
    rfl
  · change (x ∈ (C.tube m).target ∧ (C.tube m).symm x ∈ (D.tube n).source) ↔ _
    rw [D.tube_source]
    rfl

theorem SeifertBlockCharts.selectedComparisonPatch_target (C : SeifertBlockCharts W d)
    (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount) (b : Bool) (x : V.Carrier) :
    x ∈ (C.selectedComparisonPatch D hk m n b).target ↔
      x ∈ (D.selectedComparisonPatch C hk.symm n m b).source := by
  cases b
  · simp only [selectedComparisonPatch, Bool.false_eq_true, ite_false]
    rw [C.selectedComparisonProduct_target, D.selectedComparisonProduct_source]
  · rfl

theorem SeifertBlockCharts.selectedComparisonPatch_symm_apply
    (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount) (b : Bool) (x : V.Carrier) :
    (C.selectedComparisonPatch D hk m n b).symm x =
      D.selectedComparisonPatch C hk.symm n m b x := by
  cases b
  · exact C.selectedComparisonProduct_symm_apply D hk x
  · rfl

theorem SeifertBlockCharts.selectedComparisonPatch_source_cover
    (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount)
    (x : W.Carrier) (hx : x ∈ C.selectedFilledRegion m) :
    ∃ b, x ∈ (C.selectedComparisonPatch D hk m n b).source := by
  rcases hx with hp | hm
  · exact ⟨false, (C.selectedComparisonPatch_source D hk m n false x).mpr hp⟩
  · by_cases hd : ‖((C.tube m).symm x).1‖ < 1 + D.ε
    · exact ⟨true, (C.selectedComparisonPatch_source D hk m n true x).mpr ⟨hm, hd⟩⟩
    · have hsrc := (C.tube m).map_target hm
      rw [C.tube_source] at hsrc
      have htrans : (C.tube m).symm x ∈ C.transitionDomain := by
        rw [C.transitionDomain_eq]
        exact ⟨by linarith [D.ε_pos], hsrc⟩
      have hp : x ∈ C.productRegion := by
        have himage : x ∈ C.tube m '' C.transitionDomain :=
          ⟨(C.tube m).symm x, htrans, (C.tube m).apply_symm_apply hm⟩
        rw [← C.tube_product_overlap m] at himage
        exact himage.2
      exact ⟨false, (C.selectedComparisonPatch_source D hk m n false x).mpr hp⟩

theorem SeifertBlockCharts.selectedComparisonProduct_tube
    (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount)
    (hs : d.fillingSlope m = e.fillingSlope n)
    (hp : Fin.cast hk (C.port (.inr m)) = D.port (.inr n))
    (hA : C.matrix m = D.matrix n) (y : ℂ × Circle)
    (hc : y ∈ C.transitionDomain) (hd : y ∈ D.transitionDomain) :
    C.selectedComparisonProduct D hk (C.tube m y) = D.tube n y := by
  rw [C.transition m y hc]
  change D.productAmbient
    (((selectedPlanarOpenCast hk).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))
      (C.productAmbient.symm (C.productAmbient
        (⟨(seamModel d m (C.port (.inr m)) (C.matrix m) y).1,
          C.transition_domain m hc⟩,
          (seamModel d m (C.port (.inr m)) (C.matrix m) y).2)))) = _
  rw [C.productAmbient.symm_apply_apply (C.productAmbient_source.symm ▸ Set.mem_univ _),
    D.transition n y hd]
  apply congrArg D.productAmbient
  apply Prod.ext
  · apply Subtype.ext
    change (selectedPlanarOpenCast hk
      ⟨(seamModel d m (C.port (.inr m)) (C.matrix m) y).1,
        C.transition_domain m hc⟩).val =
          (seamModel e n (D.port (.inr n)) (D.matrix n) y).1
    rw [selectedPlanarOpenCast_val]
    exact congrArg Prod.fst (selectedSeamModel_eq C D hk m n hs hp hA y)
  · change (seamModel d m (C.port (.inr m)) (C.matrix m) y).2 =
      (seamModel e n (D.port (.inr n)) (D.matrix n) y).2
    exact congrArg Prod.snd (selectedSeamModel_eq C D hk m n hs hp hA y)

theorem SeifertBlockCharts.selectedComparisonPatch_product_tube
    (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount)
    (hs : d.fillingSlope m = e.fillingSlope n)
    (hp : Fin.cast hk (C.port (.inr m)) = D.port (.inr n))
    (hA : C.matrix m = D.matrix n) (x : W.Carrier)
    (hprod : x ∈ (C.selectedComparisonPatch D hk m n false).source)
    (htube : x ∈ (C.selectedComparisonPatch D hk m n true).source) :
    C.selectedComparisonPatch D hk m n false x =
      C.selectedComparisonPatch D hk m n true x := by
  rw [C.selectedComparisonPatch_source] at hprod htube
  have htrans : (C.tube m).symm x ∈ C.transitionDomain := by
    have himage : x ∈ C.tube m '' C.transitionDomain :=
      C.tube_product_overlap m ▸ ⟨htube.1, hprod⟩
    obtain ⟨y, hy, he⟩ := himage
    have hsrc : y ∈ (C.tube m).source := by
      rw [C.tube_source]
      rw [C.transitionDomain_eq] at hy
      exact hy.2
    rw [← he, (C.tube m).symm_apply_apply hsrc]
    exact hy
  have hd : (C.tube m).symm x ∈ D.transitionDomain := by
    rw [D.transitionDomain_eq]
    rw [C.transitionDomain_eq] at htrans
    exact ⟨htrans.1, htube.2⟩
  have he := C.selectedComparisonProduct_tube D hk m n hs hp hA ((C.tube m).symm x)
    htrans hd
  rw [(C.tube m).apply_symm_apply htube.1] at he
  exact he

theorem SeifertBlockCharts.selectedComparisonPatch_forward
    (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount)
    (hs : d.fillingSlope m = e.fillingSlope n)
    (hp : Fin.cast hk (C.port (.inr m)) = D.port (.inr n))
    (hA : C.matrix m = D.matrix n) (a b : Bool) (x : W.Carrier)
    (ha : x ∈ (C.selectedComparisonPatch D hk m n a).source)
    (hb : x ∈ (C.selectedComparisonPatch D hk m n b).source) :
    C.selectedComparisonPatch D hk m n a x = C.selectedComparisonPatch D hk m n b x := by
  cases a <;> cases b
  · rfl
  · exact C.selectedComparisonPatch_product_tube D hk m n hs hp hA x ha hb
  · exact (C.selectedComparisonPatch_product_tube D hk m n hs hp hA x hb ha).symm
  · rfl

theorem SeifertBlockCharts.selectedComparisonPatch_source_region
    (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount) (b : Bool) :
    (C.selectedComparisonPatch D hk m n b).source ⊆ C.selectedFilledRegion m := by
  intro x hx
  rw [C.selectedComparisonPatch_source] at hx
  cases b
  · exact Or.inl hx
  · exact Or.inr hx.1

def SeifertBlockCharts.compareSelectedFilling
    (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount)
    (hs : d.fillingSlope m = e.fillingSlope n)
    (hp : Fin.cast hk (C.port (.inr m)) = D.port (.inr n))
    (hA : C.matrix m = D.matrix n) :
    C.selectedFilledRegion m ≃ₘ⟮W.model, V.model⟯ D.selectedFilledRegion n := by
  let z := Classical.choice (normalPlanarOpen_nonempty d.k)
  have hC : Nonempty (C.selectedFilledRegion m) :=
    ⟨⟨C.product (z, 1), Or.inl (C.product (z, 1)).property⟩⟩
  let z' := selectedPlanarOpenCast hk z
  have hD : Nonempty (D.selectedFilledRegion n) :=
    ⟨⟨D.product (z', 1), Or.inl (D.product (z', 1)).property⟩⟩
  have hport : Fin.cast hk.symm (D.port (.inr n)) = C.port (.inr m) := by
    rw [← hp]
    simp
  apply gluePartialDiffeomorphsOnOpens (C.selectedComparisonPatch D hk m n)
    (C.selectedFilledRegion m) (D.selectedFilledRegion n) hC hD
  · exact C.selectedComparisonPatch_source_region D hk m n
  · intro b x hx
    exact D.selectedComparisonPatch_source_region C hk.symm n m b
      ((C.selectedComparisonPatch_target D hk m n b x).mp hx)
  · exact C.selectedComparisonPatch_source_cover D hk m n
  · intro x hx
    obtain ⟨b, hb⟩ := D.selectedComparisonPatch_source_cover C hk.symm n m x hx
    exact ⟨b, (C.selectedComparisonPatch_target D hk m n b x).mpr hb⟩
  · exact C.selectedComparisonPatch_forward D hk m n hs hp hA
  · intro a b x ha hb
    rw [C.selectedComparisonPatch_symm_apply, C.selectedComparisonPatch_symm_apply]
    exact D.selectedComparisonPatch_forward C hk.symm n m hs.symm hport hA.symm a b x
      ((C.selectedComparisonPatch_target D hk m n a x).mp ha)
      ((C.selectedComparisonPatch_target D hk m n b x).mp hb)

theorem SeifertBlockCharts.selectedFilledRegion_eq_wholeInterior
    (D : SeifertBlockCharts V e) (hf : e.fillingCount = 1) (n : Fin e.fillingCount) :
    D.selectedFilledRegion n = V.pieceInterior ⊤ := by
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · intro hx
    refine ⟨trivial, ?_⟩
    rcases hx with hp | ht
    · exact D.productRegion_interior hp
    · exact D.tube_interior n ht
  · intro hx
    rcases D.covers x hx.2 with hp | ⟨m, hm⟩
    · exact Or.inl hp
    · have hmn : m = n := by
        apply Fin.ext
        have hm := m.isLt
        have hn := n.isLt
        omega
      exact Or.inr (hmn ▸ hm)

def selectedCarrierOpenCast {A : CompactCarrier.{u}}
    (U V : TopologicalSpace.Opens A.Carrier) (h : U = V) : U ≃ₘ⟮A.model, A.model⟯ V := by
  subst V
  exact Diffeomorph.refl _ _ _

def SeifertBlockCharts.compareSelectedFillingInterior
    (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount)
    (hs : d.fillingSlope m = e.fillingSlope n)
    (hp : Fin.cast hk (C.port (.inr m)) = D.port (.inr n))
    (hA : C.matrix m = D.matrix n) (hf : e.fillingCount = 1) :
    C.selectedFilledRegion m ≃ₘ⟮W.model, V.model⟯ V.pieceInterior ⊤ :=
  (C.compareSelectedFilling D hk m n hs hp hA).trans
    (selectedCarrierOpenCast (D.selectedFilledRegion n) (V.pieceInterior ⊤)
      (D.selectedFilledRegion_eq_wholeInterior hf n))

theorem selectedGlue_apply
    (f : Bool → PartialDiffeomorph W.model V.model W.Carrier V.Carrier ∞)
    (U : TopologicalSpace.Opens W.Carrier) (R : TopologicalSpace.Opens V.Carrier)
    (hU : Nonempty U) (hR : Nonempty R)
    (hsource : ∀ b, (f b).source ⊆ U) (htarget : ∀ b, (f b).target ⊆ R)
    (hcover : ∀ x ∈ U, ∃ b, x ∈ (f b).source)
    (hcover' : ∀ y ∈ R, ∃ b, y ∈ (f b).target)
    (hforward : ∀ a b x, x ∈ (f a).source → x ∈ (f b).source → f a x = f b x)
    (hbackward : ∀ a b y, y ∈ (f a).target → y ∈ (f b).target →
      (f a).symm y = (f b).symm y)
    (b : Bool) (x : U) (hx : x.val ∈ (f b).source) :
    (gluePartialDiffeomorphsOnOpens f U R hU hR hsource htarget hcover hcover'
      hforward hbackward x).val = f b x.val := by
  have hxi : x ∈ (partialDiffeomorphOnOpens (f b) U R hU hR).source := by
    rw [partialDiffeomorphOnOpens_source (f b) U R hU hR (hsource b) (htarget b)]
    exact hx
  unfold gluePartialDiffeomorphsOnOpens
  rw [gluePartialDiffeomorphs_apply (i := b) (hx := hxi)]
  exact partialDiffeomorphOnOpens_apply (f b) U R hU hR (htarget b) x hx

theorem SeifertBlockCharts.compareSelectedFilling_apply
    (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount)
    (hs : d.fillingSlope m = e.fillingSlope n)
    (hp : Fin.cast hk (C.port (.inr m)) = D.port (.inr n))
    (hA : C.matrix m = D.matrix n) (b : Bool) (x : C.selectedFilledRegion m)
    (hx : x.val ∈ (C.selectedComparisonPatch D hk m n b).source) :
    (C.compareSelectedFilling D hk m n hs hp hA x).val =
      C.selectedComparisonPatch D hk m n b x.val := by
  unfold compareSelectedFilling
  exact selectedGlue_apply _ _ _ _ _ _ _ _ _ _ _ b x hx

theorem selectedCarrierOpenCast_val {A : CompactCarrier.{u}}
    (U R : TopologicalSpace.Opens A.Carrier) (h : U = R) (x : U) :
    (selectedCarrierOpenCast U R h x).val = x.val := by
  subst R
  rfl

theorem SeifertBlockCharts.compareSelectedFillingInterior_apply
    (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount)
    (hs : d.fillingSlope m = e.fillingSlope n)
    (hp : Fin.cast hk (C.port (.inr m)) = D.port (.inr n))
    (hA : C.matrix m = D.matrix n) (hf : e.fillingCount = 1)
    (b : Bool) (x : C.selectedFilledRegion m)
    (hx : x.val ∈ (C.selectedComparisonPatch D hk m n b).source) :
    (C.compareSelectedFillingInterior D hk m n hs hp hA hf x).val =
      C.selectedComparisonPatch D hk m n b x.val := by
  change (selectedCarrierOpenCast (A := V) (D.selectedFilledRegion n)
    (V.pieceInterior ⊤) (D.selectedFilledRegion_eq_wholeInterior hf n)
      (C.compareSelectedFilling D hk m n hs hp hA x)).val = _
  rw [selectedCarrierOpenCast_val, C.compareSelectedFilling_apply D hk m n hs hp hA b x hx]

theorem SeifertBlockCharts.compareSelectedFillingInterior_product
    (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V e) (hk : d.k = e.k)
    (m : Fin d.fillingCount) (n : Fin e.fillingCount)
    (hs : d.fillingSlope m = e.fillingSlope n)
    (hp : Fin.cast hk (C.port (.inr m)) = D.port (.inr n))
    (hA : C.matrix m = D.matrix n) (hf : e.fillingCount = 1)
    (z : planarOpen d.k × Circle) :
    (C.compareSelectedFillingInterior D hk m n hs hp hA hf
      ⟨C.product z, Or.inl (C.product z).property⟩).val =
        (D.product (selectedPlanarOpenCast hk z.1, z.2)).val := by
  rw [C.compareSelectedFillingInterior_apply D hk m n hs hp hA hf false]
  · change D.productAmbient
      (((selectedPlanarOpenCast hk).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))
        (C.productAmbient.symm (C.productAmbient z))) = _
    rw [C.productAmbient.symm_apply_apply (C.productAmbient_source.symm ▸ Set.mem_univ z)]
    rfl
  · rw [C.selectedComparisonPatch_source]
    exact (C.product z).property

end SelectedFillingComparison

theorem normalOuterTubeMap_seam (q a b : ℤ) (hb : b - a * q = 1)
    (y : ℂ × Circle) (hy : 1 < ‖y.1‖ ∧ ‖y.1‖ < 5 / 4) :
    let A := chartConventionUnit 1 q a b (by simpa only [one_mul] using hb)
    let s := seamModel (normalT2IntervalDatum q) 0 (0 : Fin 3) A y
    normalOuterTubeMap q a y =
      ((s.1 - (3 / 2 : ℂ))⁻¹, unitOf (s.1 - (3 / 2 : ℂ)) ^ (-q) * s.2) := by
  let A := chartConventionUnit 1 q a b (by simpa only [one_mul] using hb)
  let s := seamModel (normalT2IntervalDatum q) 0 (0 : Fin 3) A y
  let z := (solidBasisExtension false false (-a) y).1
  let r := ‖y.1‖
  change normalOuterTubeMap q a y =
    ((s.1 - (3 / 2 : ℂ))⁻¹, unitOf (s.1 - (3 / 2 : ℂ)) ^ (-q) * s.2)
  have hzn : ‖z‖ = r := solidBasisExtension_norm false false (-a) y
  have hz : z ≠ 0 := norm_pos_iff.mp (by rw [hzn]; exact lt_trans zero_lt_one hy.1)
  have hy0 : y.1 ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hy.1)
  have hunit : unitOf z = unitOf y.1 * y.2 ^ (-a) := by
    change unitOf (y.1 * ((y.2 ^ (-a) : Circle) : ℂ)) = _
    rw [unitOf_mul hy0 (Circle.coe_ne_zero _), unitOf_circle]
  have hs : s =
      ((((7 - r) / 2 : ℝ) : ℂ) * (((unitOf z)⁻¹ : Circle) : ℂ),
        unitOf y.1 ^ (-q) * y.2 ^ b) := by
    dsimp [s, A]
    simp only [seamModel, normalT2IntervalDatum_fillingSlope, Int.natAbs_one,
      pow_one, chartConventionUnit, PrimitiveSlope.val_unitOfDet,
      chartConventionMatrix, linearTorusMap, Fin.val_zero, ite_true,
      planarCenter, planarRadius]
    rw [hunit]
    simp only [mul_inv_rev, Circle.coe_mul]
    apply Prod.ext
    · dsimp [r]
      simp only [ite_self]
      push_cast
      simp only [zpow_neg, inv_inv, zpow_one]
      ring
    · rfl
  have hpolar : z = (r : ℂ) * (unitOf z : ℂ) := by
    rw [← hzn]
    exact (coe_norm_mul_unitOf z).symm
  have hinv : (((unitOf z)⁻¹ : Circle) : ℂ) * z = (r : ℂ) := by
    calc
      _ = (((unitOf z)⁻¹ : Circle) : ℂ) * ((r : ℂ) * (unitOf z : ℂ)) :=
        congrArg (fun w : ℂ => (((unitOf z)⁻¹ : Circle) : ℂ) * w) hpolar
      _ = (r : ℂ) * ((((unitOf z)⁻¹ : Circle) : ℂ) * (unitOf z : ℂ)) := by ring
      _ = _ := by rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, mul_one]
  have hbase : s.1 - (3 / 2 : ℂ) =
      ((normalOuterRadialDenominator ‖z‖ : ℂ) - (3 / 2 : ℂ) * z) / z := by
    apply (eq_div_iff hz).mpr
    rw [hs, hzn, normalOuterRadialDenominator_collar (by dsimp [r]; linarith [hy.1])]
    change ((((7 - r) / 2 : ℝ) : ℂ) * (((unitOf z)⁻¹ : Circle) : ℂ) -
      (3 / 2 : ℂ)) * z = ((r * (7 - r) / 2 : ℝ) : ℂ) - (3 / 2 : ℂ) * z
    calc
      _ = (((7 - r) / 2 : ℝ) : ℂ) *
        ((((unitOf z)⁻¹ : Circle) : ℂ) * z) - (3 / 2 : ℂ) * z := by ring
      _ = _ := by rw [hinv]; push_cast; ring
  have hupper : ‖z‖ < 5 / 4 := by rw [hzn]; exact hy.2
  have hden := normalOuterRadialMap_denominator hupper
  apply Prod.ext
  · change normalOuterRadialMap z = (s.1 - (3 / 2 : ℂ))⁻¹
    rw [hbase, inv_div]
    rfl
  · change normalOuterTubePhase q z * y.2 =
      unitOf (s.1 - (3 / 2 : ℂ)) ^ (-q) * s.2
    rw [hbase, unitOf_div hden hz, hunit, hs]
    dsimp only [normalOuterTubePhase, Prod.snd]
    rw [mul_comm (unitOf _) ((unitOf y.1 * y.2 ^ (-a))⁻¹)]
    exact (normalOuterShear_cancel (unitOf y.1) y.2
      (unitOf ((normalOuterRadialDenominator ‖z‖ : ℂ) - (3 / 2 : ℂ) * z))
      q a b hb).symm

def normalOuterRadialPartial :
    PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ :=
  Classical.choose (normalOuterRadialMap_local.exists_partialDiffeomorph_of_injOn
    (isOpen_lt continuous_norm continuous_const) ⟨0, by norm_num⟩
    normalOuterRadialMap_injective)

theorem normalOuterRadialPartial_source :
    normalOuterRadialPartial.source = {z : ℂ | ‖z‖ < 5 / 4} :=
  (Classical.choose_spec (normalOuterRadialMap_local.exists_partialDiffeomorph_of_injOn
    (isOpen_lt continuous_norm continuous_const) ⟨0, by norm_num⟩
    normalOuterRadialMap_injective)).1

theorem normalOuterRadialPartial_target :
    normalOuterRadialPartial.target =
      normalOuterRadialMap '' {z : ℂ | ‖z‖ < 5 / 4} :=
  (Classical.choose_spec (normalOuterRadialMap_local.exists_partialDiffeomorph_of_injOn
    (isOpen_lt continuous_norm continuous_const) ⟨0, by norm_num⟩
    normalOuterRadialMap_injective)).2.1

theorem normalOuterRadialPartial_apply (z : ℂ) :
    normalOuterRadialPartial z = normalOuterRadialMap z :=
  congrFun (Classical.choose_spec
    (normalOuterRadialMap_local.exists_partialDiffeomorph_of_injOn
      (isOpen_lt continuous_norm continuous_const) ⟨0, by norm_num⟩
      normalOuterRadialMap_injective)).2.2 z

def normalOuterPhasePartial (q : ℤ) :
    PartialDiffeomorph PlaneCircleModel PlaneCircleModel (ℂ × Circle) (ℂ × Circle) ∞ where
  toFun y := (y.1, normalOuterTubePhase q y.1 * y.2)
  invFun y := (y.1, (normalOuterTubePhase q y.1)⁻¹ * y.2)
  source := {y | ‖y.1‖ < 5 / 4}
  target := {y | ‖y.1‖ < 5 / 4}
  map_source' y hy := hy
  map_target' y hy := hy
  left_inv' y hy := by simp
  right_inv' y hy := by simp
  open_source := isOpen_lt (continuous_norm.comp continuous_fst) continuous_const
  open_target := isOpen_lt (continuous_norm.comp continuous_fst) continuous_const
  contMDiffOn_toFun := contMDiffOn_fst.prodMk
    (((normalOuterTubePhase_smooth q).comp contMDiffOn_fst (fun y hy => hy)).mul
      contMDiffOn_snd)
  contMDiffOn_invFun := contMDiffOn_fst.prodMk
    ((((normalOuterTubePhase_smooth q).inv).comp contMDiffOn_fst (fun y hy => hy)).mul
      contMDiffOn_snd)

def normalOuterTubePartial (q a : ℤ) :
    PartialDiffeomorph PlaneCircleModel PlaneCircleModel (ℂ × Circle) (ℂ × Circle) ∞ :=
  (solidBasisExtension false false (-a)).toPartialDiffeomorph.trans
    ((normalOuterPhasePartial q).trans
      (DifferentialGeometry.Topology.PartialDiffeomorph.prod normalOuterRadialPartial
        (Diffeomorph.refl (𝓡 1) Circle ∞).toPartialDiffeomorph))

theorem normalOuterTubePartial_source (q a : ℤ) :
    (normalOuterTubePartial q a).source = {y : ℂ × Circle | ‖y.1‖ < 5 / 4} := by
  ext y
  change (y ∈ Set.univ ∧
    (‖(solidBasisExtension false false (-a) y).1‖ < 5 / 4 ∧
      ((solidBasisExtension false false (-a) y).1 ∈ normalOuterRadialPartial.source ∧
        normalOuterTubePhase q (solidBasisExtension false false (-a) y).1 *
          (solidBasisExtension false false (-a) y).2 ∈ Set.univ))) ↔ _
  have hn : ‖(solidBasisExtension false false (-a) y).1‖ = ‖y.1‖ := by
    change ‖y.1 * ((y.2 ^ (-a) : Circle) : ℂ)‖ = ‖y.1‖
    rw [norm_mul, Circle.norm_coe, mul_one]
  rw [normalOuterRadialPartial_source]
  simp only [mem_univ, true_and, and_true, Set.mem_ofPred_eq, hn, and_self]

theorem normalOuterTubePartial_apply (q a : ℤ) (y : ℂ × Circle) :
    normalOuterTubePartial q a y = normalOuterTubeMap q a y := by
  change (normalOuterRadialPartial (solidBasisExtension false false (-a) y).1,
    normalOuterTubePhase q (solidBasisExtension false false (-a) y).1 *
      (solidBasisExtension false false (-a) y).2) = _
  rw [normalOuterRadialPartial_apply]
  rfl

theorem normalOuterFunction_neg_iff (w : ℂ) :
    ElementaryPresentation.outerCappingFunction w < 0 ↔
      ‖w‖ < 2 ∧ 2 / 35 < ‖w + (12 / 35 : ℂ)‖ := by
  have he : ElementaryPresentation.outerCappingFunction w =
      (‖w‖ ^ 2 - 2 ^ 2) * (‖w + (12 / 35 : ℂ)‖ ^ 2 - (2 / 35 : ℝ) ^ 2) := by
    simp [ElementaryPresentation.outerCappingFunction, sqDist, neg_div]
  constructor
  · intro h
    have hb := (ElementaryPresentation.outerCappingFunction_nonpos_iff w).mp h.le
    rw [he] at h
    constructor
    · by_contra hn
      have hh : ‖w‖ = 2 := le_antisymm hb.1 (not_lt.mp hn)
      rw [hh] at h
      norm_num at h
    · by_contra hn
      have hh : ‖w + (12 / 35 : ℂ)‖ = 2 / 35 := le_antisymm (not_lt.mp hn) hb.2
      rw [hh] at h
      norm_num at h
  · intro h
    rw [he]
    exact mul_neg_of_neg_of_pos (by nlinarith [norm_nonneg w])
      (by nlinarith [norm_nonneg (w + (12 / 35 : ℂ))])

theorem normalOuterInverse_function_neg (z : ℂ)
    (hp : 1 / 2 < ‖z - (3 / 2 : ℂ)‖) (hm : 1 / 2 < ‖z + (3 / 2 : ℂ)‖) :
    ElementaryPresentation.outerCappingFunction ((z - (3 / 2 : ℂ))⁻¹) < 0 := by
  have hne : z - (3 / 2 : ℂ) ≠ 0 := norm_pos_iff.mp (by linarith)
  have hd : 0 < ‖z - (3 / 2 : ℂ)‖ := norm_pos_iff.mpr hne
  apply (normalOuterFunction_neg_iff _).mpr
  refine ⟨?_, ?_⟩
  · rw [norm_inv, inv_eq_one_div]
    exact (div_lt_iff₀ hd).mpr (by linarith)
  · have he : ((z - (3 / 2 : ℂ))⁻¹ + (12 / 35 : ℂ)) * (z - (3 / 2 : ℂ)) =
        1 + (12 / 35 : ℂ) * (z - (3 / 2 : ℂ)) := by
      rw [add_mul, inv_mul_cancel₀ hne]
    have hn := congrArg (fun w : ℂ => ‖w‖ ^ 2) he
    rw [norm_mul, mul_pow] at hn
    have hi := ElementaryPresentation.outerCapping_circleIdentity (z - (3 / 2 : ℂ))
    have hs : z - (3 / 2 : ℂ) + 3 = z + (3 / 2 : ℂ) := by ring
    rw [hs] at hi
    by_contra hbad
    have hh : ‖(z - (3 / 2 : ℂ))⁻¹ + (12 / 35 : ℂ)‖ ^ 2 ≤ (2 / 35 : ℝ) ^ 2 := by
      nlinarith [norm_nonneg ((z - (3 / 2 : ℂ))⁻¹ + (12 / 35 : ℂ))]
    have hprod := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hh)
      (sq_nonneg ‖z - (3 / 2 : ℂ)‖)
    nlinarith [hi, hn, hprod, norm_nonneg (z + (3 / 2 : ℂ))]

theorem normalOuterRadialDenominator_gt_two {r : ℝ} (hr : 0 ≤ r) (hr2 : r < 5 / 4) :
    2 * r < normalOuterRadialDenominator r := by
  by_cases hz : r = 0
  · subst r
    rw [normalOuterRadialDenominator_core (by norm_num)]
    norm_num
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    by_cases hs : r ≤ 1 / 2
    · have hd := mul_nonneg
        (sub_nonneg.mpr (show seamCut r ≤ 1 from Real.smoothTransition.le_one _))
        (show 0 ≤ 3 - r * (7 - r) / 2 by nlinarith)
      unfold normalOuterRadialDenominator
      nlinarith
    · rw [normalOuterRadialDenominator_collar (not_le.mp hs).le]
      nlinarith

theorem normalOuterRadialMap_function_neg {z : ℂ} (hz : ‖z‖ < 5 / 4) :
    ElementaryPresentation.outerCappingFunction (normalOuterRadialMap z) < 0 := by
  by_cases hz0 : z = 0
  · subst z
    apply (normalOuterFunction_neg_iff _).mpr
    norm_num [normalOuterRadialMap]
  · let v : ℂ := (normalOuterRadialDenominator ‖z‖ : ℂ) / z
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hH : 0 < normalOuterRadialDenominator ‖z‖ := lt_trans (by positivity)
      (normalOuterRadialDenominator_gt_two (norm_nonneg z) hz)
    have hv : 2 < ‖v‖ := by
      change 2 < ‖(normalOuterRadialDenominator ‖z‖ : ℂ) / z‖
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hH.le]
      exact (lt_div_iff₀ hr).mpr (normalOuterRadialDenominator_gt_two (norm_nonneg z) hz)
    have hp : 1 / 2 < ‖v - (3 / 2 : ℂ)‖ := by
      have hh := norm_sub_norm_le v (3 / 2 : ℂ)
      norm_num at hh
      linarith
    have hm : 1 / 2 < ‖v + (3 / 2 : ℂ)‖ := by
      have hh := norm_sub_norm_le v (-(3 / 2 : ℂ))
      norm_num at hh
      linarith
    have he : normalOuterRadialMap z = (v - (3 / 2 : ℂ))⁻¹ := by
      have hd : v - (3 / 2 : ℂ) =
          ((normalOuterRadialDenominator ‖z‖ : ℂ) - (3 / 2 : ℂ) * z) / z := by
        dsimp [v]
        field_simp [hz0]
      rw [hd, inv_div]
      rfl
    rw [he]
    exact normalOuterInverse_function_neg v hp hm

theorem normalOuterProduct_mem_interior (p : PlaneLift.{u} × Circle)
    (hp : ElementaryPresentation.outerCappingFunction p.1.down < 0) :
    p ∈ interior ElementaryPresentation.outerCappingProductSet.{u} := by
  let U : Set (PlaneLift.{u} × Circle) :=
    {y | ElementaryPresentation.outerCappingFunction y.1.down < 0}
  have ho : IsOpen U :=
    isOpen_lt (ElementaryPresentation.outerCappingFunction_smooth.continuous.comp
      (continuous_uliftDown.comp continuous_fst)) continuous_const
  have hsub : U ⊆ ElementaryPresentation.outerCappingProductSet.{u} := by
    intro y hy
    exact (show ElementaryPresentation.outerCappingFunction y.1.down < 0 from hy).le
  exact interior_mono hsub (ho.interior_eq.symm ▸ hp)

theorem normalOuterRadialMap_mem_interior {z : ℂ} (hz : ‖z‖ < 5 / 4) (t : Circle) :
    ((ULift.up (normalOuterRadialMap z) : PlaneLift.{u}), t) ∈
      interior ElementaryPresentation.outerCappingProductSet.{u} :=
  normalOuterProduct_mem_interior (ULift.up (normalOuterRadialMap z), t)
    (normalOuterRadialMap_function_neg hz)

def normalOuterProductPoint : ElementaryPresentation.outerCappingProductSet.{u} :=
  ⟨(ULift.up 0, 1), by
    change ElementaryPresentation.outerCappingFunction 0 ≤ 0
    have h := normalOuterRadialMap_function_neg (z := 0) (by norm_num)
    simpa [normalOuterRadialMap] using h.le⟩

def normalOuterAnnulusModelDiffeomorph :
    ElementaryPresentation.outerCappingProductSet.{u} ≃ₘ⟮𝓡∂ 3,
      annulusCircleCarrier.{u}.model⟯ annulusCircleCarrier.{u}.Carrier :=
  ElementaryPresentation.outerCappingAnnulusProductDiffeomorph.symm.trans
    (productDiffeomorph 2)

def normalOuterTubeAtlas (q a : ℤ) :
    PartialDiffeomorph PlaneCircleModel (𝓡∂ 3) (ℂ × Circle)
      ElementaryPresentation.outerCappingProductSet.{u} ∞ :=
  ((normalOuterTubePartial q a).trans chartPlaneCircleLift.{u}.symm.toPartialDiffeomorph).trans
    (ElementaryPresentation.outerCappingProductAtlas.interiorPartialDiffeomorph
      normalOuterProductPoint.{u}).symm

theorem normalOuterTubeAtlas_source (q a : ℤ) :
    (normalOuterTubeAtlas.{u} q a).source = {y : ℂ × Circle | ‖y.1‖ < 5 / 4} := by
  ext y
  change ((y ∈ (normalOuterTubePartial q a).source ∧
    normalOuterTubePartial q a y ∈ Set.univ) ∧
      chartPlaneCircleLift.{u}.symm (normalOuterTubePartial q a y) ∈
        interior ElementaryPresentation.outerCappingProductSet.{u}) ↔ _
  rw [normalOuterTubePartial_source]
  constructor
  · exact fun h => h.1.1
  · intro hy
    refine ⟨⟨hy, trivial⟩, ?_⟩
    rw [normalOuterTubePartial_apply]
    let z := (solidBasisExtension false false (-a) y).1
    have hn : ‖z‖ = ‖y.1‖ := by
      change ‖y.1 * ((y.2 ^ (-a) : Circle) : ℂ)‖ = ‖y.1‖
      rw [norm_mul, Circle.norm_coe, mul_one]
    exact normalOuterRadialMap_mem_interior (hn ▸ hy) (normalOuterTubePhase q z * y.2)

theorem normalOuterTubeAtlas_apply_val (q a : ℤ) (y : ℂ × Circle)
    (hy : ‖y.1‖ < 5 / 4) :
    (normalOuterTubeAtlas.{u} q a y).val =
      (ULift.up (normalOuterTubeMap q a y).1, (normalOuterTubeMap q a y).2) := by
  have hm : y ∈ (normalOuterTubeAtlas.{u} q a).source :=
    (normalOuterTubeAtlas_source.{u} q a).symm ▸ hy
  have hi := hm.2
  have he := (ElementaryPresentation.outerCappingProductAtlas.interiorPartialDiffeomorph
    normalOuterProductPoint.{u}).right_inv hi
  change (normalOuterTubeAtlas.{u} q a y).val =
    chartPlaneCircleLift.{u}.symm (normalOuterTubeMap q a y)
  rw [← normalOuterTubePartial_apply q a y]
  exact he

def normalOuterAnnulusTube (q a : ℤ) :
    PartialDiffeomorph PlaneCircleModel annulusCircleCarrier.{u}.model
      (ℂ × Circle) annulusCircleCarrier.{u}.Carrier ∞ :=
  (normalOuterTubeAtlas.{u} q a).trans normalOuterAnnulusModelDiffeomorph.toPartialDiffeomorph

theorem normalOuterAnnulusTube_source (q a : ℤ) :
    (normalOuterAnnulusTube.{u} q a).source = {y : ℂ × Circle | ‖y.1‖ < 5 / 4} := by
  ext y
  change (y ∈ (normalOuterTubeAtlas.{u} q a).source ∧
    normalOuterTubeAtlas.{u} q a y ∈ Set.univ) ↔ _
  rw [normalOuterTubeAtlas_source.{u}]
  simp only [Set.mem_univ, and_true]

theorem normalOuterAnnulusTube_interior (q a : ℤ) :
    (normalOuterAnnulusTube.{u} q a).target ⊆ annulusCircleCarrier.{u}.interior := by
  intro y hy
  let T := normalOuterAnnulusTube.{u} q a
  have hi := ((T.isLocalDiffeomorphAt PlaneCircleModel annulusCircleCarrier.model ∞
    (T.map_target hy)).isInteriorPoint_iff (by simp)).mp
      BoundarylessManifold.isInteriorPoint
  rw [T.right_inv hy] at hi
  exact hi

theorem normalOuterRadialDenominator_pos_closed {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 5 / 4) :
    0 < normalOuterRadialDenominator r := by
  by_cases hrh : 1 / 2 ≤ r
  · rw [normalOuterRadialDenominator_collar hrh]
    have hrp : 0 < r := by linarith
    have hdiff : 0 < 7 - r := by linarith
    exact div_pos (mul_pos hrp hdiff) (by norm_num)
  · exact lt_of_le_of_lt (mul_nonneg (by norm_num) hr)
      (normalOuterRadialDenominator_gt hr (by linarith [not_le.mp hrh]))

theorem normalOuterTubeRadius_zero : normalOuterTubeRadius 0 = 0 := by
  simp [normalOuterTubeRadius]

theorem normalOuterTubeRadius_one : normalOuterTubeRadius 1 = 1 / 3 := by
  rw [normalOuterTubeRadius, normalOuterRadialDenominator_collar (by norm_num)]
  norm_num

theorem normalOuterTubeRadius_endpoint : normalOuterTubeRadius (5 / 4) = 8 / 23 := by
  rw [normalOuterTubeRadius, normalOuterRadialDenominator_collar (by norm_num)]
  norm_num

theorem normalOuterTubeRadius_continuous_closed :
    ContinuousOn normalOuterTubeRadius (Set.Icc (0 : ℝ) (5 / 4)) := by
  have hH : Continuous normalOuterRadialDenominator :=
    continuous_iff_continuousAt.mpr fun r =>
      (normalOuterRadialDenominator_hasDerivAt r).continuousAt
  exact continuousOn_id.div hH.continuousOn fun r hr =>
    (normalOuterRadialDenominator_pos_closed hr.1 hr.2).ne'

theorem exists_normalOuterTubeRadius {s : ℝ} (hs : 0 ≤ s) (hs2 : s < 8 / 23) :
    ∃ r ∈ Set.Ico (0 : ℝ) (5 / 4), normalOuterTubeRadius r = s := by
  have him := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 5 / 4)
    normalOuterTubeRadius_continuous_closed
  rw [normalOuterTubeRadius_zero, normalOuterTubeRadius_endpoint] at him
  obtain ⟨r, hr, he⟩ := him ⟨hs, hs2.le⟩
  refine ⟨r, ⟨hr.1, lt_of_le_of_ne hr.2 ?_⟩, he⟩
  intro hrb
  subst r
  rw [normalOuterTubeRadius_endpoint] at he
  linarith

theorem normalOuterTubeRadius_lt_endpoint {r : ℝ} (hr : 0 ≤ r) (hr2 : r < 5 / 4) :
    normalOuterTubeRadius r < 8 / 23 := by
  by_cases hrh : 1 / 2 ≤ r
  · rw [normalOuterTubeRadius, normalOuterRadialDenominator_collar hrh]
    have hrp : 0 < r := by linarith
    have hden : 0 < r * (7 - r) / 2 :=
      div_pos (mul_pos hrp (by linarith)) (by norm_num)
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  · have hm := normalOuterTubeRadius_strictMono
      ⟨hr, hr2⟩ ⟨by norm_num, by norm_num⟩ (not_le.mp hrh)
    have hh : normalOuterTubeRadius (1 / 2) = 4 / 13 := by
      rw [normalOuterTubeRadius, normalOuterRadialDenominator_collar (by norm_num)]
      norm_num
    rw [hh] at hm
    linarith

theorem normalOuterTubeRadius_lt_one_iff {r : ℝ} (hr : 0 ≤ r) (hr2 : r < 5 / 4) :
    normalOuterTubeRadius r < 1 / 3 ↔ r < 1 := by
  rw [← normalOuterTubeRadius_one]
  exact normalOuterTubeRadius_strictMono.lt_iff_lt ⟨hr, hr2⟩ ⟨by norm_num, by norm_num⟩

theorem normalOuterTubeRadius_le_one_iff {r : ℝ} (hr : 0 ≤ r) (hr2 : r < 5 / 4) :
    normalOuterTubeRadius r ≤ 1 / 3 ↔ r ≤ 1 := by
  rw [← normalOuterTubeRadius_one]
  exact normalOuterTubeRadius_strictMono.le_iff_le ⟨hr, hr2⟩ ⟨by norm_num, by norm_num⟩

theorem normalOuterTubeRadius_gt_one_iff {r : ℝ} (hr : 0 ≤ r) (hr2 : r < 5 / 4) :
    1 / 3 < normalOuterTubeRadius r ↔ 1 < r := by
  rw [← normalOuterTubeRadius_one]
  exact normalOuterTubeRadius_strictMono.lt_iff_lt ⟨by norm_num, by norm_num⟩ ⟨hr, hr2⟩

theorem normalOuterRadialNormalize_polar {r : ℝ} (hr : 0 ≤ r) (t : Circle) :
    normalOuterRadialNormalize (r • (t : ℂ)) = normalOuterTubeRadius r • (t : ℂ) := by
  have hn : ‖r • (t : ℂ)‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr, Circle.norm_coe, mul_one]
  rw [normalOuterRadialNormalize, hn, smul_smul, normalOuterTubeRadius, div_eq_mul_inv,
    mul_comm (normalOuterRadialDenominator r)⁻¹ r]

theorem exists_normalOuterRadialNormalize {w : ℂ} (hw : ‖w‖ < 8 / 23) :
    ∃ z : ℂ, ‖z‖ < 5 / 4 ∧ normalOuterRadialNormalize z = w := by
  obtain ⟨r, hr, he⟩ := exists_normalOuterTubeRadius (norm_nonneg w) hw
  refine ⟨r • (unitOf w : ℂ), ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg hr.1, Circle.norm_coe, mul_one]
    exact hr.2
  · rw [normalOuterRadialNormalize_polar hr.1, he]
    exact norm_smul_unitOf w

theorem normalOuterRadialNormalize_image :
    normalOuterRadialNormalize '' {z : ℂ | ‖z‖ < 5 / 4} = {w : ℂ | ‖w‖ < 8 / 23} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ‖normalOuterRadialNormalize z‖ < 8 / 23
    rw [normalOuterRadialNormalize_norm hz]
    exact normalOuterTubeRadius_lt_endpoint (norm_nonneg z) hz
  · exact exists_normalOuterRadialNormalize

theorem exists_normalOuterRadialNormalize_cap {w : ℂ} (hw : ‖w‖ ≤ 1 / 3) :
    ∃ z : ℂ, ‖z‖ ≤ 1 ∧ normalOuterRadialNormalize z = w := by
  obtain ⟨z, hz, he⟩ := exists_normalOuterRadialNormalize (lt_of_le_of_lt hw (by norm_num))
  refine ⟨z, ?_, he⟩
  apply (normalOuterTubeRadius_le_one_iff (norm_nonneg z) hz).mp
  rw [← normalOuterRadialNormalize_norm hz, he]
  exact hw

theorem normalOuterRadialNormalize_cap_image :
    normalOuterRadialNormalize '' {z : ℂ | ‖z‖ ≤ 1} = {w : ℂ | ‖w‖ ≤ 1 / 3} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ‖normalOuterRadialNormalize z‖ ≤ 1 / 3
    have hz2 : ‖z‖ < 5 / 4 := lt_of_le_of_lt hz (by norm_num)
    rw [normalOuterRadialNormalize_norm hz2]
    exact (normalOuterTubeRadius_le_one_iff (norm_nonneg z) hz2).mpr hz
  · exact exists_normalOuterRadialNormalize_cap

theorem normalOuterRadialNormalize_open_cap_image :
    normalOuterRadialNormalize '' {z : ℂ | ‖z‖ < 1} = {w : ℂ | ‖w‖ < 1 / 3} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ‖normalOuterRadialNormalize z‖ < 1 / 3
    have hz2 : ‖z‖ < 5 / 4 := lt_trans hz (by norm_num)
    rw [normalOuterRadialNormalize_norm hz2]
    exact (normalOuterTubeRadius_lt_one_iff (norm_nonneg z) hz2).mpr hz
  · intro hw
    obtain ⟨z, hz, he⟩ := exists_normalOuterRadialNormalize
      (lt_trans hw (by norm_num : (1 / 3 : ℝ) < 8 / 23))
    refine ⟨z, ?_, he⟩
    apply (normalOuterTubeRadius_lt_one_iff (norm_nonneg z) hz).mp
    rw [← normalOuterRadialNormalize_norm hz, he]
    exact hw

theorem normalOuterRadialNormalize_transition_image :
    normalOuterRadialNormalize '' {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < 5 / 4} =
      {w : ℂ | 1 / 3 < ‖w‖ ∧ ‖w‖ < 8 / 23} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    change 1 / 3 < ‖normalOuterRadialNormalize z‖ ∧
      ‖normalOuterRadialNormalize z‖ < 8 / 23
    rw [normalOuterRadialNormalize_norm hz.2]
    exact ⟨(normalOuterTubeRadius_gt_one_iff (norm_nonneg z) hz.2).mpr hz.1,
      normalOuterTubeRadius_lt_endpoint (norm_nonneg z) hz.2⟩
  · intro hw
    obtain ⟨z, hz, he⟩ := exists_normalOuterRadialNormalize hw.2
    refine ⟨z, ⟨?_, hz⟩, he⟩
    apply (normalOuterTubeRadius_gt_one_iff (norm_nonneg z) hz).mp
    rw [← normalOuterRadialNormalize_norm hz, he]
    exact hw.1

theorem normalOuterRadialMap_image :
    normalOuterRadialMap '' {z : ℂ | ‖z‖ < 5 / 4} =
      {w : ℂ | 1 + (3 / 2 : ℂ) * w ≠ 0 ∧
        ‖w / (1 + (3 / 2 : ℂ) * w)‖ < 8 / 23} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hH : 0 < normalOuterRadialDenominator ‖z‖ :=
      normalOuterRadialDenominator_pos_closed (norm_nonneg z) hz.le
    rw [normalOuterRadialMap_factor hH.ne']
    have hsrc := normalOuterRadialNormalize_mobiusSource hz
    have ht := (normalOuterMobius (3 / 2 : ℂ)).map_source hsrc
    refine ⟨ht, ?_⟩
    change ‖(normalOuterMobius (3 / 2 : ℂ)).symm
      (normalOuterMobius (3 / 2 : ℂ) (normalOuterRadialNormalize z))‖ < 8 / 23
    exact lt_of_eq_of_lt (congrArg norm
      ((normalOuterMobius (3 / 2 : ℂ)).left_inv hsrc))
      (lt_of_eq_of_lt (normalOuterRadialNormalize_norm hz)
        (normalOuterTubeRadius_lt_endpoint (norm_nonneg z) hz))
  · intro hw
    obtain ⟨z, hz, he⟩ := exists_normalOuterRadialNormalize hw.2
    refine ⟨z, hz, ?_⟩
    have hH : 0 < normalOuterRadialDenominator ‖z‖ :=
      normalOuterRadialDenominator_pos_closed (norm_nonneg z) hz.le
    rw [normalOuterRadialMap_factor hH.ne', he]
    exact (normalOuterMobius (3 / 2 : ℂ)).right_inv hw.1

theorem normalOuterRadialMap_cap_image :
    normalOuterRadialMap '' {z : ℂ | ‖z‖ ≤ 1} =
      {w : ℂ | 1 + (3 / 2 : ℂ) * w ≠ 0 ∧
        ‖w / (1 + (3 / 2 : ℂ) * w)‖ ≤ 1 / 3} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz2 : ‖z‖ < 5 / 4 := lt_of_le_of_lt hz (by norm_num)
    have hH : 0 < normalOuterRadialDenominator ‖z‖ :=
      normalOuterRadialDenominator_pos_closed (norm_nonneg z) hz2.le
    rw [normalOuterRadialMap_factor hH.ne']
    have hsrc := normalOuterRadialNormalize_mobiusSource hz2
    have ht := (normalOuterMobius (3 / 2 : ℂ)).map_source hsrc
    refine ⟨ht, ?_⟩
    change ‖(normalOuterMobius (3 / 2 : ℂ)).symm
      (normalOuterMobius (3 / 2 : ℂ) (normalOuterRadialNormalize z))‖ ≤ 1 / 3
    exact le_of_eq_of_le (congrArg norm
      ((normalOuterMobius (3 / 2 : ℂ)).left_inv hsrc))
      (le_of_eq_of_le (normalOuterRadialNormalize_norm hz2)
        ((normalOuterTubeRadius_le_one_iff (norm_nonneg z) hz2).mpr hz))
  · intro hw
    obtain ⟨z, hz, he⟩ := exists_normalOuterRadialNormalize_cap hw.2
    refine ⟨z, hz, ?_⟩
    have hz2 : ‖z‖ < 5 / 4 := lt_of_le_of_lt hz (by norm_num)
    have hH : 0 < normalOuterRadialDenominator ‖z‖ :=
      normalOuterRadialDenominator_pos_closed (norm_nonneg z) hz2.le
    rw [normalOuterRadialMap_factor hH.ne', he]
    exact (normalOuterMobius (3 / 2 : ℂ)).right_inv hw.1

theorem normalOuterRadialMap_transition_image :
    normalOuterRadialMap '' {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < 5 / 4} =
      {w : ℂ | 1 + (3 / 2 : ℂ) * w ≠ 0 ∧
        1 / 3 < ‖w / (1 + (3 / 2 : ℂ) * w)‖ ∧
          ‖w / (1 + (3 / 2 : ℂ) * w)‖ < 8 / 23} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hH : 0 < normalOuterRadialDenominator ‖z‖ :=
      normalOuterRadialDenominator_pos_closed (norm_nonneg z) hz.2.le
    rw [normalOuterRadialMap_factor hH.ne']
    have hsrc := normalOuterRadialNormalize_mobiusSource hz.2
    have ht := (normalOuterMobius (3 / 2 : ℂ)).map_source hsrc
    refine ⟨ht, ?_⟩
    change 1 / 3 < ‖(normalOuterMobius (3 / 2 : ℂ)).symm
      (normalOuterMobius (3 / 2 : ℂ) (normalOuterRadialNormalize z))‖ ∧
      ‖(normalOuterMobius (3 / 2 : ℂ)).symm
        (normalOuterMobius (3 / 2 : ℂ) (normalOuterRadialNormalize z))‖ < 8 / 23
    have hn : ‖(normalOuterMobius (3 / 2 : ℂ)).symm
        (normalOuterMobius (3 / 2 : ℂ) (normalOuterRadialNormalize z))‖ =
          normalOuterTubeRadius ‖z‖ :=
      (congrArg norm ((normalOuterMobius (3 / 2 : ℂ)).left_inv hsrc)).trans
        (normalOuterRadialNormalize_norm hz.2)
    exact ⟨lt_of_lt_of_eq
      ((normalOuterTubeRadius_gt_one_iff (norm_nonneg z) hz.2).mpr hz.1) hn.symm,
      lt_of_eq_of_lt hn (normalOuterTubeRadius_lt_endpoint (norm_nonneg z) hz.2)⟩
  · intro hw
    obtain ⟨z, hz, he⟩ := exists_normalOuterRadialNormalize hw.2.2
    have hz1 : 1 < ‖z‖ := by
      apply (normalOuterTubeRadius_gt_one_iff (norm_nonneg z) hz).mp
      rw [← normalOuterRadialNormalize_norm hz, he]
      exact hw.2.1
    refine ⟨z, ⟨hz1, hz⟩, ?_⟩
    have hH : 0 < normalOuterRadialDenominator ‖z‖ :=
      normalOuterRadialDenominator_pos_closed (norm_nonneg z) hz.le
    rw [normalOuterRadialMap_factor hH.ne', he]
    exact (normalOuterMobius (3 / 2 : ℂ)).right_inv hw.1

private theorem normalOuterNormalizePDiff_exists :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      P.source = {z : ℂ | ‖z‖ < 5 / 4} ∧
      P.target = {w : ℂ | ‖w‖ < 8 / 23} ∧ P.toFun = normalOuterRadialNormalize := by
  obtain ⟨P, hs, ht, hf⟩ := normalOuterRadialNormalize_local.exists_partialDiffeomorph_of_injOn
    (isOpen_lt continuous_norm continuous_const) ⟨0, by norm_num⟩
    normalOuterRadialNormalize_injective
  exact ⟨P, hs, normalOuterRadialNormalize_image ▸ ht, hf⟩

private def normalOuterNormalizePDiff :
    PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ := normalOuterNormalizePDiff_exists.choose

private theorem normalOuterNormalizePDiff_source :
    normalOuterNormalizePDiff.source = {z : ℂ | ‖z‖ < 5 / 4} :=
  normalOuterNormalizePDiff_exists.choose_spec.1

private theorem normalOuterNormalizePDiff_target :
    normalOuterNormalizePDiff.target = {w : ℂ | ‖w‖ < 8 / 23} :=
  normalOuterNormalizePDiff_exists.choose_spec.2.1

private theorem normalOuterNormalizePDiff_apply (z : ℂ) :
    normalOuterNormalizePDiff z = normalOuterRadialNormalize z :=
  congrFun normalOuterNormalizePDiff_exists.choose_spec.2.2 z

private theorem normalOuterDisc_val_norm (x : UnitDisc.{0}) : ‖x.down.val‖ ≤ 1 := by
  have h := x.down.property
  change ‖x.down.val‖ ^ 2 ≤ 1 at h
  nlinarith [norm_nonneg x.down.val]

def normalOuterDiscReparam (x : UnitDisc.{0}) : UnitDisc.{0} :=
  ULift.up ⟨(3 : ℝ) • normalOuterRadialNormalize x.down.val, by
    have hx := normalOuterDisc_val_norm x
    have hx2 : ‖x.down.val‖ < 5 / 4 := by linarith
    have hN : ‖normalOuterRadialNormalize x.down.val‖ ≤ 1 / 3 := by
      rw [normalOuterRadialNormalize_norm hx2]
      exact (normalOuterTubeRadius_le_one_iff (norm_nonneg _) hx2).mpr hx
    change ‖(3 : ℝ) • normalOuterRadialNormalize x.down.val‖ ^ 2 ≤ 1
    rw [norm_smul]
    norm_num
    nlinarith [norm_nonneg (normalOuterRadialNormalize x.down.val)]⟩

private theorem normalOuterDisc_scaled_target (x : UnitDisc.{0}) :
    (1 / 3 : ℝ) • x.down.val ∈ normalOuterNormalizePDiff.target := by
  rw [normalOuterNormalizePDiff_target]
  change ‖(1 / 3 : ℝ) • x.down.val‖ < 8 / 23
  rw [norm_smul]
  norm_num
  linarith [normalOuterDisc_val_norm x]

private theorem normalOuterDisc_inverse_normalize (x : UnitDisc.{0}) :
    normalOuterRadialNormalize
      (normalOuterNormalizePDiff.symm ((1 / 3 : ℝ) • x.down.val)) =
        (1 / 3 : ℝ) • x.down.val := by
  rw [← normalOuterNormalizePDiff_apply]
  exact normalOuterNormalizePDiff.right_inv (normalOuterDisc_scaled_target x)

private def normalOuterDiscReparamInverse (x : UnitDisc.{0}) : UnitDisc.{0} :=
  ULift.up ⟨normalOuterNormalizePDiff.symm ((1 / 3 : ℝ) • x.down.val), by
    have hsrc := normalOuterNormalizePDiff.map_target (normalOuterDisc_scaled_target x)
    rw [normalOuterNormalizePDiff_source] at hsrc
    have he := normalOuterDisc_inverse_normalize x
    have hn : normalOuterTubeRadius
        ‖normalOuterNormalizePDiff.symm ((1 / 3 : ℝ) • x.down.val)‖ =
          ‖(1 / 3 : ℝ) • x.down.val‖ :=
      (normalOuterRadialNormalize_norm hsrc).symm.trans (congrArg norm he)
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)] at hn
    have hn1 : normalOuterTubeRadius
        ‖normalOuterNormalizePDiff.symm ((1 / 3 : ℝ) • x.down.val)‖ ≤ 1 / 3 := by
      rw [hn]
      linarith [normalOuterDisc_val_norm x]
    have hr1 := (normalOuterTubeRadius_le_one_iff (norm_nonneg _) hsrc).mp hn1
    change ‖normalOuterNormalizePDiff.symm ((1 / 3 : ℝ) • x.down.val)‖ ^ 2 ≤ 1
    simpa only [one_pow] using pow_le_pow_left₀
      (norm_nonneg (normalOuterNormalizePDiff.symm ((1 / 3 : ℝ) • x.down.val))) hr1 2⟩

theorem normalOuterDiscReparam_smooth :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ normalOuterDiscReparam := by
  have hv : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞
      (fun x : UnitDisc.{0} => (3 : ℝ) • normalOuterRadialNormalize x.down.val) :=
    (((3 : ℝ) • ContinuousLinearMap.id ℝ ℂ).contDiff.contMDiff).comp
      (normalOuterRadialNormalize_smooth.contMDiffOn.comp_contMDiff contMDiff_disc_val
        (fun x => by change ‖x.down.val‖ < 5 / 4; linarith [normalOuterDisc_val_norm x]))
  have hd : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞
      (fun x : UnitDisc.{0} => (normalOuterDiscReparam x).down) :=
    (unitDiscAtlas.contMDiff_iff_subtype_val _).mpr hv
  exact (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).contMDiff.comp hd

private theorem normalOuterDiscReparamInverse_smooth :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ normalOuterDiscReparamInverse := by
  have hv : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞
      (fun x : UnitDisc.{0} =>
        normalOuterNormalizePDiff.symm ((1 / 3 : ℝ) • x.down.val)) :=
    normalOuterNormalizePDiff.symm.contMDiffOn.comp_contMDiff
      ((((1 / 3 : ℝ) • ContinuousLinearMap.id ℝ ℂ).contDiff.contMDiff).comp
        contMDiff_disc_val) normalOuterDisc_scaled_target
  have hd : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞
      (fun x : UnitDisc.{0} => (normalOuterDiscReparamInverse x).down) :=
    (unitDiscAtlas.contMDiff_iff_subtype_val _).mpr hv
  exact (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).contMDiff.comp hd

def normalOuterDiscReparamDiffeomorph : UnitDisc.{0} ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ UnitDisc.{0} where
  toFun := normalOuterDiscReparam
  invFun := normalOuterDiscReparamInverse
  left_inv x := by
    apply ULift.ext
    apply Subtype.ext
    change normalOuterNormalizePDiff.symm
      ((1 / 3 : ℝ) • ((3 : ℝ) • normalOuterRadialNormalize x.down.val)) = x.down.val
    rw [smul_smul]
    norm_num
    rw [← normalOuterNormalizePDiff_apply]
    apply normalOuterNormalizePDiff.left_inv
    rw [normalOuterNormalizePDiff_source]
    change ‖x.down.val‖ < 5 / 4
    linarith [normalOuterDisc_val_norm x]
  right_inv x := by
    apply ULift.ext
    apply Subtype.ext
    change (3 : ℝ) • normalOuterRadialNormalize
      (normalOuterNormalizePDiff.symm ((1 / 3 : ℝ) • x.down.val)) = x.down.val
    rw [normalOuterDisc_inverse_normalize, smul_smul]
    norm_num
  contMDiff_toFun := normalOuterDiscReparam_smooth
  contMDiff_invFun := normalOuterDiscReparamInverse_smooth

theorem normalOuterDiscReparamDiffeomorph_boundary (t : Circle) :
    normalOuterDiscReparamDiffeomorph (ElementaryPresentation.fillingDiscBoundary t) =
      ElementaryPresentation.fillingDiscBoundary t := by
  apply ULift.ext
  apply Subtype.ext
  change (3 : ℝ) • normalOuterRadialNormalize (t : ℂ) = t
  rw [normalOuterRadialNormalize, Circle.norm_coe,
    normalOuterRadialDenominator_collar (by norm_num), smul_smul]
  norm_num

theorem normalOuterDiscReparamDiffeomorph_map (x : UnitDisc.{0}) :
    ElementaryPresentation.cappingOuterDiscMap (normalOuterDiscReparamDiffeomorph x) =
      normalOuterRadialMap x.down.val := by
  have hx := normalOuterDisc_val_norm x
  have hx2 : ‖x.down.val‖ < 5 / 4 := by linarith
  have hH := normalOuterRadialDenominator_pos_closed (norm_nonneg x.down.val) hx2.le
  rw [normalOuterRadialMap_factor hH.ne']
  change ((3 : ℝ) • normalOuterRadialNormalize x.down.val) /
    (3 - (3 / 2 : ℂ) * ((3 : ℝ) • normalOuterRadialNormalize x.down.val)) =
      normalOuterRadialNormalize x.down.val /
        (1 - (3 / 2 : ℂ) * normalOuterRadialNormalize x.down.val)
  have hd : 1 - (3 / 2 : ℂ) * normalOuterRadialNormalize x.down.val ≠ 0 :=
    normalOuterRadialNormalize_mobiusSource hx2
  rw [Complex.real_smul]
  norm_num
  field_simp [hd]

theorem normalOuterDiscReparamDiffeomorph_phase (q : ℤ) (x : UnitDisc.{0}) :
    ElementaryPresentation.outerCappingCapPhase q (normalOuterDiscReparamDiffeomorph x) =
      normalOuterTubePhase q x.down.val := by
  have hx := normalOuterDisc_val_norm x
  have hx2 : ‖x.down.val‖ < 5 / 4 := by linarith
  have hH := normalOuterRadialDenominator_pos_closed (norm_nonneg x.down.val) hx2.le
  have he : 3 - (3 / 2 : ℂ) * ((3 : ℝ) • normalOuterRadialNormalize x.down.val) =
      (3 / normalOuterRadialDenominator ‖x.down.val‖ : ℝ) •
        ((normalOuterRadialDenominator ‖x.down.val‖ : ℂ) - (3 / 2 : ℂ) * x.down.val) := by
    rw [normalOuterRadialNormalize, Complex.real_smul, Complex.real_smul,
      Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hH.ne']
  change unitOf (3 - (3 / 2 : ℂ) * ((3 : ℝ) • normalOuterRadialNormalize x.down.val)) ^
    (-q) = _
  have hu : unitOf ((3 / normalOuterRadialDenominator ‖x.down.val‖ : ℝ) •
      ((normalOuterRadialDenominator ‖x.down.val‖ : ℂ) - (3 / 2 : ℂ) * x.down.val)) =
      unitOf ((normalOuterRadialDenominator ‖x.down.val‖ : ℂ) -
        (3 / 2 : ℂ) * x.down.val) := by
    let d : ℂ := (normalOuterRadialDenominator ‖x.down.val‖ : ℂ) - (3 / 2 : ℂ) * x.down.val
    have hd : d ≠ 0 := normalOuterRadialMap_denominator hx2
    change unitOf ((3 / normalOuterRadialDenominator ‖x.down.val‖ : ℝ) • d) = unitOf d
    calc
      _ = unitOf ((3 / normalOuterRadialDenominator ‖x.down.val‖ * ‖d‖ : ℝ) •
          (unitOf d : ℂ)) := by rw [mul_smul, norm_smul_unitOf]
      _ = unitOf d := unitOf_smul
        (mul_pos (div_pos (by norm_num) hH) (norm_pos_iff.mpr hd)) (unitOf d)
  rw [he, hu]
  rfl

def normalOuterHostBase : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ where
  toFun z := (z - (3 / 2 : ℂ))⁻¹
  invFun w := w⁻¹ + (3 / 2 : ℂ)
  source := {z | z - (3 / 2 : ℂ) ≠ 0}
  target := {w | w ≠ 0}
  map_source' z hz := inv_ne_zero hz
  map_target' w hw := by
    change w⁻¹ + (3 / 2 : ℂ) - (3 / 2 : ℂ) ≠ 0
    simpa only [add_sub_cancel_right] using inv_ne_zero hw
  left_inv' z hz := by simp
  right_inv' w hw := by simp
  open_source := isOpen_ne_fun (continuous_id.sub continuous_const) continuous_const
  open_target := isOpen_ne
  contMDiffOn_toFun := by
    intro z hz
    have hd := ((contDiffAt_id : ContDiffAt ℝ ∞ (id : ℂ → ℂ) z).sub contDiffAt_const).inv hz
    exact hd.contMDiffAt.contMDiffWithinAt
  contMDiffOn_invFun := by
    intro w hw
    have hd := ((contDiffAt_id : ContDiffAt ℝ ∞ (id : ℂ → ℂ) w).inv hw).add
      (contDiffAt_const (c := (3 / 2 : ℂ)))
    exact hd.contMDiffAt.contMDiffWithinAt

theorem normalPantsOpen_holes (z : planarOpen 3) :
    1 / 2 < ‖z.val - (3 / 2 : ℂ)‖ ∧ 1 / 2 < ‖z.val + (3 / 2 : ℂ)‖ := by
  have hz := (ConeFilling.chartPlanarOpen_three_iff z.val).mp z.property
  have hh := (planarFunction_three_neg_iff z.val).mp hz
  exact ⟨hh.2.1, by simpa only [neg_div, sub_neg_eq_add] using hh.2.2⟩

def normalOuterHostPlane (q : ℤ) :
    PartialDiffeomorph PlaneCircleModel PlaneCircleModel (planarOpen 3 × Circle)
      (ℂ × Circle) ∞ :=
  ((normalInnerFibreShear (1 : Fin 3) (by decide) (-q)).toPartialDiffeomorph.trans
    (DifferentialGeometry.Topology.PartialDiffeomorph.prod
      (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (planarOpen 3)
        (normalPlanarOpen_nonempty 3))
      (Diffeomorph.refl (𝓡 1) Circle ∞).toPartialDiffeomorph)).trans
    (DifferentialGeometry.Topology.PartialDiffeomorph.prod normalOuterHostBase
      (Diffeomorph.refl (𝓡 1) Circle ∞).toPartialDiffeomorph)

theorem normalOuterHostPlane_source (q : ℤ) : (normalOuterHostPlane q).source = Set.univ := by
  ext x
  change ((x ∈ Set.univ ∧
    ((normalInnerFibreShear (1 : Fin 3) (by decide) (-q) x).1 ∈ Set.univ ∧
      (normalInnerFibreShear (1 : Fin 3) (by decide) (-q) x).2 ∈ Set.univ)) ∧
        (x.1.val - (3 / 2 : ℂ) ≠ 0 ∧
          (normalInnerFibreShear (1 : Fin 3) (by decide) (-q) x).2 ∈ Set.univ)) ↔ _
  have hne : x.1.val - (3 / 2 : ℂ) ≠ 0 :=
    norm_pos_iff.mp (by linarith [(normalPantsOpen_holes x.1).1])
  simp only [Set.mem_univ, and_self, true_and]
  exact iff_of_true ⟨hne, trivial⟩ trivial

theorem normalOuterHostPlane_apply (q : ℤ) (x : planarOpen 3 × Circle) :
    normalOuterHostPlane q x =
      ((x.1.val - (3 / 2 : ℂ))⁻¹, normalOuterHostPhase q x.1 * x.2) := by
  apply Prod.ext
  · rfl
  · change normalInnerPhase (1 : Fin 3) (-q) x.1 * x.2 = _
    simp only [normalInnerPhase, normalOuterHostPhase, planarCenter]
    norm_num

def normalOuterHostAtlas (q : ℤ) :
    PartialDiffeomorph PlaneCircleModel (𝓡∂ 3) (planarOpen 3 × Circle)
      ElementaryPresentation.outerCappingProductSet.{u} ∞ :=
  ((normalOuterHostPlane q).trans chartPlaneCircleLift.{u}.symm.toPartialDiffeomorph).trans
    (ElementaryPresentation.outerCappingProductAtlas.interiorPartialDiffeomorph
      normalOuterProductPoint.{u}).symm

theorem normalOuterHostAtlas_source (q : ℤ) :
    (normalOuterHostAtlas.{u} q).source = Set.univ := by
  ext x
  change ((x ∈ (normalOuterHostPlane q).source ∧ normalOuterHostPlane q x ∈ Set.univ) ∧
    chartPlaneCircleLift.{u}.symm (normalOuterHostPlane q x) ∈
      interior ElementaryPresentation.outerCappingProductSet.{u}) ↔ _
  rw [normalOuterHostPlane_source]
  simp only [Set.mem_univ, and_self, true_and]
  apply iff_of_true
  · rw [normalOuterHostPlane_apply]
    exact normalOuterProduct_mem_interior
      (ULift.up ((x.1.val - (3 / 2 : ℂ))⁻¹), normalOuterHostPhase q x.1 * x.2)
      (normalOuterInverse_function_neg x.1.val (normalPantsOpen_holes x.1).1
        (normalPantsOpen_holes x.1).2)
  · trivial

theorem normalOuterHostAtlas_apply_val (q : ℤ) (x : planarOpen 3 × Circle) :
    (normalOuterHostAtlas.{u} q x).val =
      (ULift.up ((x.1.val - (3 / 2 : ℂ))⁻¹), normalOuterHostPhase q x.1 * x.2) := by
  have hm : x ∈ (normalOuterHostAtlas.{u} q).source :=
    (normalOuterHostAtlas_source.{u} q).symm ▸ Set.mem_univ x
  have hi := hm.2
  have he := (ElementaryPresentation.outerCappingProductAtlas.interiorPartialDiffeomorph
    normalOuterProductPoint.{u}).right_inv hi
  change (normalOuterHostAtlas.{u} q x).val =
    chartPlaneCircleLift.{u}.symm
      ((x.1.val - (3 / 2 : ℂ))⁻¹, normalOuterHostPhase q x.1 * x.2)
  rw [← normalOuterHostPlane_apply]
  exact he

def normalOuterAnnulusHost (q : ℤ) :
    PartialDiffeomorph PlaneCircleModel annulusCircleCarrier.{u}.model
      (planarOpen 3 × Circle) annulusCircleCarrier.{u}.Carrier ∞ :=
  (normalOuterHostAtlas.{u} q).trans normalOuterAnnulusModelDiffeomorph.toPartialDiffeomorph

theorem normalOuterAnnulusHost_source (q : ℤ) :
    (normalOuterAnnulusHost.{u} q).source = Set.univ := by
  ext x
  change (x ∈ (normalOuterHostAtlas.{u} q).source ∧
    normalOuterHostAtlas.{u} q x ∈ Set.univ) ↔ _
  rw [normalOuterHostAtlas_source.{u}]
  simp only [Set.mem_univ, and_self]

def normalOuterProductRegion (q : ℤ) :
    TopologicalSpace.Opens annulusCircleCarrier.{u}.Carrier :=
  ⟨(normalOuterAnnulusHost.{u} q).target, (normalOuterAnnulusHost.{u} q).open_target⟩

def normalOuterProduct (q : ℤ) :
    (planarOpen 3 × Circle) ≃ₘ⟮PlaneCircleModel, annulusCircleCarrier.{u}.model⟯
      normalOuterProductRegion.{u} q where
  toFun x := ⟨normalOuterAnnulusHost.{u} q x,
    (normalOuterAnnulusHost.{u} q).map_source
      ((normalOuterAnnulusHost_source.{u} q).symm ▸ Set.mem_univ x)⟩
  invFun y := (normalOuterAnnulusHost.{u} q).symm y.val
  left_inv x := (normalOuterAnnulusHost.{u} q).symm_apply_apply
    ((normalOuterAnnulusHost_source.{u} q).symm ▸ Set.mem_univ x)
  right_inv y := Subtype.ext ((normalOuterAnnulusHost.{u} q).apply_symm_apply y.property)
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (normalOuterProductRegion.{u} q) _).mp
    intro x
    exact ((normalOuterAnnulusHost.{u} q).isLocalDiffeomorphAt _ _ ∞
      ((normalOuterAnnulusHost_source.{u} q).symm ▸ Set.mem_univ x)).contMDiffAt
  contMDiff_invFun := by
    intro y
    have ht := ((normalOuterAnnulusHost.{u} q).symm.isLocalDiffeomorphAt
      _ _ ∞ y.property).contMDiffAt
    exact ht.comp y contMDiff_subtype_val.contMDiffAt

theorem normalOuterProductRegion_interior (q : ℤ) :
    (normalOuterProductRegion.{u} q : Set annulusCircleCarrier.{u}.Carrier) ⊆
      annulusCircleCarrier.{u}.interior := by
  intro y hy
  let P := normalOuterAnnulusHost.{u} q
  have hi := ((P.isLocalDiffeomorphAt PlaneCircleModel annulusCircleCarrier.model ∞
    (P.map_target hy)).isInteriorPoint_iff (by simp)).mp
      BoundarylessManifold.isInteriorPoint
  rw [P.right_inv hy] at hi
  exact hi

theorem normalOuterInverse_function_neg_iff (z : ℂ) (hne : z - (3 / 2 : ℂ) ≠ 0) :
    ElementaryPresentation.outerCappingFunction ((z - (3 / 2 : ℂ))⁻¹) < 0 ↔
      1 / 2 < ‖z - (3 / 2 : ℂ)‖ ∧ 1 / 2 < ‖z + (3 / 2 : ℂ)‖ := by
  constructor
  · intro h
    have hw := (normalOuterFunction_neg_iff _).mp h
    have hd : 0 < ‖z - (3 / 2 : ℂ)‖ := norm_pos_iff.mpr hne
    refine ⟨?_, ?_⟩
    · have he := hw.1
      rw [norm_inv, inv_eq_one_div] at he
      have hh := (div_lt_iff₀ hd).mp he
      linarith
    · have he : ((z - (3 / 2 : ℂ))⁻¹ + (12 / 35 : ℂ)) * (z - (3 / 2 : ℂ)) =
          1 + (12 / 35 : ℂ) * (z - (3 / 2 : ℂ)) := by
        rw [add_mul, inv_mul_cancel₀ hne]
      have hn := congrArg (fun w : ℂ => ‖w‖ ^ 2) he
      rw [norm_mul, mul_pow] at hn
      have hi := ElementaryPresentation.outerCapping_circleIdentity (z - (3 / 2 : ℂ))
      have hs : z - (3 / 2 : ℂ) + 3 = z + (3 / 2 : ℂ) := by ring
      rw [hs] at hi
      have hprod := mul_pos
        (show 0 < ‖(z - (3 / 2 : ℂ))⁻¹ + (12 / 35 : ℂ)‖ ^ 2 - (2 / 35 : ℝ) ^ 2 by
          nlinarith [hw.2, norm_nonneg ((z - (3 / 2 : ℂ))⁻¹ + (12 / 35 : ℂ))])
        (sq_pos_of_pos hd)
      nlinarith [hi, hn, hprod, norm_nonneg (z + (3 / 2 : ℂ))]
  · exact fun h => normalOuterInverse_function_neg z h.1 h.2

theorem normalOuterProduct_isInteriorPoint_iff
    (x : ElementaryPresentation.outerCappingProductSet.{u}) :
    (𝓡∂ 3).IsInteriorPoint x ↔
      ElementaryPresentation.outerCappingFunction x.val.1.down < 0 :=
  SmoothBoundaryAtlas.regularSublevel_isInteriorPoint_iff PlaneCircleModel (n := 2)
    finrank_planeCircleModel ElementaryPresentation.outerCappingProductFunction_smooth 0
    ElementaryPresentation.outerCappingProductFunction_regular x

theorem normalOuterHostAtlas_target_iff (q : ℤ)
    (x : ElementaryPresentation.outerCappingProductSet.{u}) (hx : (𝓡∂ 3).IsInteriorPoint x) :
    x ∈ (normalOuterHostAtlas.{u} q).target ↔
      x.val.1.down ≠ 0 ∧ ‖x.val.1.down⁻¹ + (3 / 2 : ℂ)‖ < 3 := by
  constructor
  · intro h
    let y := (normalOuterHostAtlas.{u} q).symm x
    have he : normalOuterHostAtlas.{u} q y = x :=
      (normalOuterHostAtlas.{u} q).apply_symm_apply h
    have hcoord := congrArg (fun z : ElementaryPresentation.outerCappingProductSet.{u} =>
      z.val.1.down) he
    rw [normalOuterHostAtlas_apply_val] at hcoord
    change (y.1.val - (3 / 2 : ℂ))⁻¹ = x.val.1.down at hcoord
    have hne : y.1.val - (3 / 2 : ℂ) ≠ 0 :=
      norm_pos_iff.mp (by linarith [(normalPantsOpen_holes y.1).1])
    refine ⟨hcoord ▸ inv_ne_zero hne, ?_⟩
    rw [← hcoord, inv_inv, sub_add_cancel]
    have hy := (ConeFilling.chartPlanarOpen_three_iff y.1.val).mp y.1.property
    exact ((planarFunction_three_neg_iff y.1.val).mp hy).1
  · rintro ⟨hne, hn⟩
    let z : ℂ := x.val.1.down⁻¹ + (3 / 2 : ℂ)
    have hz : z - (3 / 2 : ℂ) ≠ 0 := by
      dsimp [z]
      simpa only [add_sub_cancel_right] using inv_ne_zero hne
    have he : (z - (3 / 2 : ℂ))⁻¹ = x.val.1.down := by
      dsimp [z]
      rw [add_sub_cancel_right, inv_inv]
    have hp := (normalOuterProduct_isInteriorPoint_iff x).mp hx
    have hh := (normalOuterInverse_function_neg_iff z hz).mp (he.symm ▸ hp)
    have hbase : z ∈ planarOpen 3 := by
      apply (ConeFilling.chartPlanarOpen_three_iff z).mpr
      apply (planarFunction_three_neg_iff z).mpr
      exact ⟨hn, hh.1, by simpa only [neg_div, sub_neg_eq_add] using hh.2⟩
    let y : planarOpen 3 × Circle :=
      (⟨z, hbase⟩, (normalOuterHostPhase q ⟨z, hbase⟩)⁻¹ * x.val.2)
    have hy : normalOuterHostAtlas.{u} q y = x := by
      apply Subtype.ext
      rw [normalOuterHostAtlas_apply_val]
      apply Prod.ext
      · apply ULift.ext
        exact he
      · exact mul_inv_cancel_left (normalOuterHostPhase q ⟨z, hbase⟩) x.val.2
    rw [← hy]
    exact (normalOuterHostAtlas.{u} q).map_source
      ((normalOuterHostAtlas_source.{u} q).symm ▸ Set.mem_univ y)

theorem normalOuterTubeRatio_lt_three_iff {r : ℝ} (hr : 0 < r) (hr2 : r < 5 / 4) :
    normalOuterRadialDenominator r / r < 3 ↔ 1 < r := by
  have hone : (1 : ℝ) ∈ Set.Ioo 0 (5 / 4) := by norm_num
  have hval : normalOuterRadialDenominator 1 / 1 = 3 := by
    rw [normalOuterRadialDenominator_collar (by norm_num)]
    norm_num
  constructor
  · intro h
    by_contra hn
    have ha := normalOuterTubeRatio_strictAnti.antitoneOn ⟨hr, hr2⟩ hone (not_lt.mp hn)
    change normalOuterRadialDenominator 1 / 1 ≤ normalOuterRadialDenominator r / r at ha
    rw [hval] at ha
    linarith
  · intro h
    have ha := normalOuterTubeRatio_strictAnti hone ⟨hr, hr2⟩ h
    change normalOuterRadialDenominator r / r < normalOuterRadialDenominator 1 / 1 at ha
    rw [hval] at ha
    exact ha

theorem normalOuterTubeAtlas_product_iff (q a : ℤ) (y : ℂ × Circle)
    (hy : ‖y.1‖ < 5 / 4) :
    normalOuterTubeAtlas.{u} q a y ∈ (normalOuterHostAtlas.{u} q).target ↔ 1 < ‖y.1‖ := by
  have hs : y ∈ (normalOuterTubeAtlas.{u} q a).source :=
    (normalOuterTubeAtlas_source.{u} q a).symm ▸ hy
  have hi := ((normalOuterTubeAtlas.{u} q a).isLocalDiffeomorphAt PlaneCircleModel
    (𝓡∂ 3) ∞ hs).isInteriorPoint_iff (by simp) |>.mp BoundarylessManifold.isInteriorPoint
  have hc := normalOuterHostAtlas_target_iff q (normalOuterTubeAtlas.{u} q a y) hi
  rw [normalOuterTubeAtlas_apply_val q a y hy] at hc
  let z := (solidBasisExtension false false (-a) y).1
  have hn : ‖z‖ = ‖y.1‖ := solidBasisExtension_norm false false (-a) y
  have hz : ‖z‖ < 5 / 4 := hn ▸ hy
  change normalOuterTubeAtlas.{u} q a y ∈ (normalOuterHostAtlas.{u} q).target ↔
    normalOuterRadialMap z ≠ 0 ∧ ‖(normalOuterRadialMap z)⁻¹ + (3 / 2 : ℂ)‖ < 3 at hc
  rw [hc]
  by_cases hz0 : z = 0
  · rw [← hn, hz0]
    simp [normalOuterRadialMap]
  · have hH : 0 < normalOuterRadialDenominator ‖z‖ := lt_trans (by positivity)
      (normalOuterRadialDenominator_gt_two (norm_nonneg z) hz)
    have hw : normalOuterRadialMap z ≠ 0 :=
      div_ne_zero hz0 (normalOuterRadialMap_denominator hz)
    have he : (normalOuterRadialMap z)⁻¹ + (3 / 2 : ℂ) =
        (normalOuterRadialDenominator ‖z‖ : ℂ) / z := by
      unfold normalOuterRadialMap
      rw [inv_div]
      field_simp [hz0]
      ring
    simp only [he, norm_div, Complex.norm_real, Real.norm_of_nonneg hH.le]
    rw [← hn]
    constructor
    · intro h
      exact (normalOuterTubeRatio_lt_three_iff (norm_pos_iff.mpr hz0) hz).mp h.2
    · intro h
      exact ⟨hw, (normalOuterTubeRatio_lt_three_iff (norm_pos_iff.mpr hz0) hz).mpr h⟩

theorem normalOuterTubeAtlas_product_overlap (q a : ℤ) :
    (normalOuterTubeAtlas.{u} q a).target ∩ (normalOuterHostAtlas.{u} q).target =
      normalOuterTubeAtlas.{u} q a '' {y : ℂ × Circle | 1 < ‖y.1‖ ∧ ‖y.1‖ < 5 / 4} := by
  ext x
  constructor
  · intro hx
    let y := (normalOuterTubeAtlas.{u} q a).symm x
    have hs := (normalOuterTubeAtlas.{u} q a).map_target hx.1
    rw [normalOuterTubeAtlas_source] at hs
    have he : normalOuterTubeAtlas.{u} q a y = x :=
      (normalOuterTubeAtlas.{u} q a).apply_symm_apply hx.1
    refine ⟨y, ⟨?_, hs⟩, he⟩
    exact (normalOuterTubeAtlas_product_iff q a y hs).mp (he.symm ▸ hx.2)
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(normalOuterTubeAtlas.{u} q a).map_source
      ((normalOuterTubeAtlas_source.{u} q a).symm ▸ hy.2),
      (normalOuterTubeAtlas_product_iff q a y hy.2).mpr hy.1⟩


theorem normalOuterAnnulusHost_target (q : ℤ) (x : annulusCircleCarrier.{u}.Carrier) :
    x ∈ (normalOuterAnnulusHost.{u} q).target ↔
      normalOuterAnnulusModelDiffeomorph.{u}.symm x ∈ (normalOuterHostAtlas.{u} q).target := by
  change (x ∈ Set.univ ∧
    normalOuterAnnulusModelDiffeomorph.{u}.symm x ∈ (normalOuterHostAtlas.{u} q).target) ↔ _
  simp only [Set.mem_univ, true_and]

theorem normalOuterAnnulusTube_target (q a : ℤ) (x : annulusCircleCarrier.{u}.Carrier) :
    x ∈ (normalOuterAnnulusTube.{u} q a).target ↔
      normalOuterAnnulusModelDiffeomorph.{u}.symm x ∈
        (normalOuterTubeAtlas.{u} q a).target := by
  change (x ∈ Set.univ ∧
    normalOuterAnnulusModelDiffeomorph.{u}.symm x ∈ (normalOuterTubeAtlas.{u} q a).target) ↔ _
  simp only [Set.mem_univ, true_and]

theorem normalOuterAnnulusTube_product_overlap (q a : ℤ) :
    (normalOuterAnnulusTube.{u} q a).target ∩
      (normalOuterProductRegion.{u} q : Set annulusCircleCarrier.{u}.Carrier) =
        normalOuterAnnulusTube.{u} q a ''
          {y : ℂ × Circle | 1 < ‖y.1‖ ∧ ‖y.1‖ < 5 / 4} := by
  ext x
  constructor
  · intro hx
    have ha := (normalOuterAnnulusTube_target q a x).mp hx.1
    have hb := (normalOuterAnnulusHost_target q x).mp hx.2
    obtain ⟨y, hy, he⟩ := (normalOuterTubeAtlas_product_overlap.{u} q a ▸
      (show normalOuterAnnulusModelDiffeomorph.{u}.symm x ∈
        (normalOuterTubeAtlas.{u} q a).target ∩ (normalOuterHostAtlas.{u} q).target from
          ⟨ha, hb⟩))
    refine ⟨y, hy, ?_⟩
    change normalOuterAnnulusModelDiffeomorph.{u} (normalOuterTubeAtlas.{u} q a y) = x
    rw [he, normalOuterAnnulusModelDiffeomorph.apply_symm_apply]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(normalOuterAnnulusTube.{u} q a).map_source
      ((normalOuterAnnulusTube_source.{u} q a).symm ▸ hy.2), ?_⟩
    apply (normalOuterAnnulusHost_target q _).mpr
    change normalOuterAnnulusModelDiffeomorph.{u}.symm
      (normalOuterAnnulusModelDiffeomorph.{u} (normalOuterTubeAtlas.{u} q a y)) ∈ _
    rw [normalOuterAnnulusModelDiffeomorph.symm_apply_apply]
    exact (normalOuterTubeAtlas_product_iff q a y hy.2).mpr hy.1

theorem exists_normalOuterRawCap (x : ℂ) (hx : ‖x‖ ≤ 1) :
    ∃ z : ℂ, ‖z‖ < 5 / 4 ∧ normalOuterRadialMap z = x / (3 - (3 / 2 : ℂ) * x) := by
  let X : UnitDisc.{0} := ULift.up ⟨x, by
    change ‖x‖ ^ 2 ≤ 1
    nlinarith [norm_nonneg x]⟩
  let Y := normalOuterDiscReparamDiffeomorph.symm X
  have hY : ‖Y.down.val‖ ≤ 1 := by
    have h := Y.down.property
    change ‖Y.down.val‖ ^ 2 ≤ 1 at h
    nlinarith [norm_nonneg Y.down.val]
  refine ⟨Y.down.val, lt_of_le_of_lt hY (by norm_num), ?_⟩
  have he := normalOuterDiscReparamDiffeomorph_map Y
  change ElementaryPresentation.cappingOuterDiscMap
    (normalOuterDiscReparamDiffeomorph (normalOuterDiscReparamDiffeomorph.symm X)) = _ at he
  rw [normalOuterDiscReparamDiffeomorph.apply_symm_apply] at he
  exact he.symm

theorem normalOuterTubeAtlas_target_of_preimage (q a : ℤ)
    (x : ElementaryPresentation.outerCappingProductSet.{u}) (z : ℂ) (hz : ‖z‖ < 5 / 4)
    (he : normalOuterRadialMap z = x.val.1.down) :
    x ∈ (normalOuterTubeAtlas.{u} q a).target := by
  let H := solidBasisExtension false false (-a)
  let t := (normalOuterTubePhase q z)⁻¹ * x.val.2
  let y := H.symm (z, t)
  have hn : ‖y.1‖ = ‖z‖ := normalSolidBasis_inverseNorm a (z, t)
  have hy : ‖y.1‖ < 5 / 4 := hn ▸ hz
  have hfirst : (H y).1 = z := congrArg Prod.fst (H.apply_symm_apply (z, t))
  have hsecond : y.2 = t := congrArg Prod.snd (H.apply_symm_apply (z, t))
  have hm : normalOuterTubeMap q a y = (normalOuterRadialMap z, x.val.2) := by
    change (normalOuterRadialMap (H y).1,
      normalOuterTubePhase q (H y).1 * y.2) = _
    rw [hfirst, hsecond]
    exact Prod.ext rfl (mul_inv_cancel_left (normalOuterTubePhase q z) x.val.2)
  have hpoint : normalOuterTubeAtlas.{u} q a y = x := by
    apply Subtype.ext
    rw [normalOuterTubeAtlas_apply_val q a y hy, hm]
    exact Prod.ext (ULift.ext he) rfl
  rw [← hpoint]
  exact (normalOuterTubeAtlas.{u} q a).map_source
    ((normalOuterTubeAtlas_source.{u} q a).symm ▸ hy)

theorem normalOuterAtlas_cover (q a : ℤ)
    (x : ElementaryPresentation.outerCappingProductSet.{u}) (hx : (𝓡∂ 3).IsInteriorPoint x) :
    x ∈ (normalOuterHostAtlas.{u} q).target ∨ x ∈ (normalOuterTubeAtlas.{u} q a).target := by
  have hneg := (normalOuterProduct_isInteriorPoint_iff x).mp hx
  have hring := (ElementaryPresentation.outerCappingFunction_nonpos_iff _).mp hneg.le
  have hcap : ∀ v : ℂ, ‖v‖ ≤ 1 →
      x.val.1.down = v / (3 - (3 / 2 : ℂ) * v) →
        x ∈ (normalOuterTubeAtlas.{u} q a).target := by
    intro v hv he
    obtain ⟨z, hz, hh⟩ := exists_normalOuterRawCap v hv
    exact normalOuterTubeAtlas_target_of_preimage q a x z hz (hh.trans he.symm)
  rcases ElementaryPresentation.outerCappingRing_cover x.val.1.down hring with
    ⟨z, hz, he⟩ | ⟨v, hv, he⟩
  · have hmodel := (mem_planarModel_three z).mp hz
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg,
      sub_neg_eq_add] at hmodel
    have hne : z - (3 / 2 : ℂ) ≠ 0 := norm_pos_iff.mp (by linarith [hmodel.2.1])
    by_cases hlt : ‖z‖ < 3
    · left
      apply (normalOuterHostAtlas_target_iff q x hx).mpr
      refine ⟨he ▸ inv_ne_zero hne, ?_⟩
      rw [he, inv_inv, sub_add_cancel]
      exact hlt
    · right
      have heq : ‖z‖ = 3 := le_antisymm hmodel.1 (not_lt.mp hlt)
      have hz0 : z ≠ 0 := norm_pos_iff.mp (by rw [heq]; norm_num)
      apply hcap ((3 : ℂ) / z)
      · rw [norm_div, Complex.norm_ofNat, heq]
        norm_num
      · rw [he]
        have hd : 3 - (3 / 2 : ℂ) * ((3 : ℂ) / z) =
            (3 : ℂ) * (z - (3 / 2 : ℂ)) / z := by
          field_simp [hz0]
        have hdn : 3 - (3 / 2 : ℂ) * ((3 : ℂ) / z) ≠ 0 := by
          rw [hd]
          exact div_ne_zero (mul_ne_zero (by norm_num) hne) hz0
        field_simp [hz0, hne, hdn]
  · exact Or.inr (hcap v hv he)

theorem normalOuterAnnulus_cover (q a : ℤ) (x : annulusCircleCarrier.{u}.Carrier)
    (hx : x ∈ annulusCircleCarrier.{u}.interior) :
    x ∈ normalOuterProductRegion.{u} q ∨ x ∈ (normalOuterAnnulusTube.{u} q a).target := by
  let e := normalOuterAnnulusModelDiffeomorph.{u}
  have hi := ((e.symm.toPartialDiffeomorph.isLocalDiffeomorphAt _ _ ∞
    (Set.mem_univ x)).isInteriorPoint_iff (by simp)).mp hx
  rcases normalOuterAtlas_cover q a (e.symm x) hi with hp | ht
  · exact Or.inl ((normalOuterAnnulusHost_target q x).mpr hp)
  · exact Or.inr ((normalOuterAnnulusTube_target q a x).mpr ht)

theorem normalOuterSeam_norm (q : ℤ) (m : Fin (normalT2IntervalDatum q).fillingCount)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (hy : 1 < ‖y.1‖ ∧ ‖y.1‖ < 5 / 4) :
    ‖(seamModel (normalT2IntervalDatum q) m (0 : Fin 3) A y).1‖ = (7 - ‖y.1‖) / 2 := by
  simp only [seamModel, normalT2IntervalDatum_fillingSlope, Int.natAbs_one, pow_one,
    Fin.val_zero, ite_true, planarCenter, planarRadius]
  change ‖(0 : ℂ) + ((3 + -1 * (‖y.1‖ - 1) / 2 : ℝ) : ℂ) *
    ((linearTorusMap A (unitOf y.1, y.2)).1 : ℂ)‖ = _
  simp only [zero_add, norm_mul,
    Circle.norm_coe, mul_one, Complex.norm_real]
  rw [Real.norm_of_nonneg (by linarith [hy.2])]
  ring

theorem normalOuterSeam_domain (q : ℤ) (m : Fin (normalT2IntervalDatum q).fillingCount)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (hy : 1 < ‖y.1‖ ∧ ‖y.1‖ < 5 / 4) :
    (seamModel (normalT2IntervalDatum q) m (0 : Fin 3) A y).1 ∈ planarOpen 3 := by
  let z := (seamModel (normalT2IntervalDatum q) m (0 : Fin 3) A y).1
  have hn : ‖z‖ = (7 - ‖y.1‖) / 2 := normalOuterSeam_norm q m A y hy
  apply (ConeFilling.chartPlanarOpen_three_iff z).mpr
  apply (planarFunction_three_neg_iff z).mpr
  have hp := norm_sub_norm_le z (3 / 2 : ℂ)
  have hm := norm_sub_norm_le z (-3 / 2 : ℂ)
  norm_num at hp hm
  exact ⟨by linarith [hy.1], by linarith [hy.2], by linarith [hy.2]⟩

theorem normalOuterMatchingUnit (c : ConeFilling) (hp : c.p = 1) :
    c.matchingUnit = chartConventionUnit 1 c.q c.a c.b (by
      simpa only [hp, Nat.cast_one, one_mul] using c.det_eq) := by
  apply Units.ext
  change c.matchingMatrix = !![-1, c.a; -c.q, c.b]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ConeFilling.matchingMatrix, ConeFilling.reflectMatrix, ConeFilling.chartMatrix,
      hp, Matrix.mul_apply, Fin.sum_univ_two]

theorem normalOuterReferenceSeam_transition (c : ConeFilling) (hp : c.p = 1)
    (m : Fin (normalT2IntervalDatum c.q).fillingCount) (y : ℂ × Circle)
    (hy : 1 < ‖y.1‖ ∧ ‖y.1‖ < 5 / 4) :
    normalOuterAnnulusTube.{u} c.q c.a y =
      (normalOuterProduct.{u} c.q
        (⟨(seamModel (normalT2IntervalDatum c.q) m (0 : Fin 3) c.matchingUnit y).1,
          normalOuterSeam_domain c.q m c.matchingUnit y hy⟩,
          (seamModel (normalT2IntervalDatum c.q) m (0 : Fin 3) c.matchingUnit y).2) :
        annulusCircleCarrier.{u}.Carrier) := by
  have hm : m = 0 := Fin.eq_zero m
  subst m
  change normalOuterAnnulusModelDiffeomorph.{u} (normalOuterTubeAtlas.{u} c.q c.a y) =
    normalOuterAnnulusModelDiffeomorph.{u} (normalOuterHostAtlas.{u} c.q _)
  apply congrArg normalOuterAnnulusModelDiffeomorph.{u}
  apply Subtype.ext
  rw [normalOuterTubeAtlas_apply_val c.q c.a y hy.2, normalOuterHostAtlas_apply_val]
  have hb : c.b - c.a * c.q = 1 := by
    simpa only [hp, Nat.cast_one, one_mul] using c.det_eq
  have he := normalOuterTubeMap_seam c.q c.a c.b hb y hy
  change normalOuterTubeMap c.q c.a y = _ at he
  rw [← normalOuterMatchingUnit c hp] at he
  apply Prod.ext
  · exact ULift.ext (congrArg Prod.fst he)
  · change (normalOuterTubeMap c.q c.a y).2 =
      unitOf ((seamModel (normalT2IntervalDatum c.q) 0 (0 : Fin 3)
        c.matchingUnit y).1 - (3 / 2 : ℂ)) ^ (-c.q) *
          (seamModel (normalT2IntervalDatum c.q) 0 (0 : Fin 3) c.matchingUnit y).2
    exact congrArg (fun z : ℂ × Circle => z.2) he

def normalOuterReferenceCharts (c : ConeFilling) (hp : c.p = 1)
    (port : Fin 2 ⊕ Fin 1 ≃ Fin 3) (hport : port (.inr 0) = 0) :
    SeifertBlockCharts annulusCircleCarrier.{u} (normalT2IntervalDatum c.q) where
  port := port
  matrix m := c.matchingUnit
  a m := c.a
  b m := c.b
  matrix_eq m := by
    rw [normalT2IntervalDatum_fillingSlope, normalOuterMatchingUnit c hp]
    rfl
  bezout m := by
    rw [normalT2IntervalDatum_fillingSlope]
    simpa only [hp, Nat.cast_one, one_mul] using c.det_eq
  productRegion := normalOuterProductRegion c.q
  productRegion_interior := normalOuterProductRegion_interior c.q
  product := normalOuterProduct c.q
  ε := 1 / 4
  ε_pos := by norm_num
  tube m := normalOuterAnnulusTube c.q c.a
  tube_source m := by
    rw [normalOuterAnnulusTube_source]
    norm_num
  tube_interior m := normalOuterAnnulusTube_interior c.q c.a
  transitionDomain := {y | 1 < ‖y.1‖ ∧ ‖y.1‖ < 5 / 4}
  transitionDomain_eq := by norm_num
  transition_domain m y hy := by
    have hm : m = 0 := Fin.eq_zero m
    subst m
    exact (congrArg (fun j : Fin 3 =>
      (seamModel (normalT2IntervalDatum c.q) (0 : Fin 1) j c.matchingUnit y).1 ∈
        planarOpen 3) hport).mpr (normalOuterSeam_domain c.q 0 c.matchingUnit y hy)
  transition m y hy := by
    have hm : m = 0 := Fin.eq_zero m
    subst m
    change normalOuterAnnulusModelDiffeomorph.{u} (normalOuterTubeAtlas.{u} c.q c.a y) =
      normalOuterAnnulusModelDiffeomorph.{u} (normalOuterHostAtlas.{u} c.q _)
    apply congrArg normalOuterAnnulusModelDiffeomorph.{u}
    let S := seamModel (normalT2IntervalDatum c.q) (0 : Fin 1)
      (port (.inr (0 : Fin 1)) : Fin 3) c.matchingUnit y
    let X : planarOpen 3 × Circle := (⟨S.1, by
      exact (congrArg (fun j : Fin 3 =>
        (seamModel (normalT2IntervalDatum c.q) (0 : Fin 1) j c.matchingUnit y).1 ∈
          planarOpen 3) hport).mpr (normalOuterSeam_domain c.q 0 c.matchingUnit y hy)⟩, S.2)
    apply Subtype.ext
    change (normalOuterTubeAtlas.{u} c.q c.a y).val = (normalOuterHostAtlas.{u} c.q X).val
    rw [normalOuterTubeAtlas_apply_val c.q c.a y hy.2, normalOuterHostAtlas_apply_val]
    have hs := congrArg (fun j : Fin 3 =>
      seamModel (normalT2IntervalDatum c.q) (0 : Fin 1) j c.matchingUnit y) hport
    have hb : c.b - c.a * c.q = 1 := by
      simpa only [hp, Nat.cast_one, one_mul] using c.det_eq
    have he := normalOuterTubeMap_seam c.q c.a c.b hb y hy
    change normalOuterTubeMap c.q c.a y = _ at he
    rw [← normalOuterMatchingUnit c hp] at he
    apply Prod.ext
    · apply ULift.ext
      change (normalOuterTubeMap c.q c.a y).1 =
        ((seamModel (normalT2IntervalDatum c.q) 0 (port (.inr 0))
          c.matchingUnit y).1 - (3 / 2 : ℂ))⁻¹
      exact (congrArg (fun z : ℂ × Circle => z.1) he).trans
        (congrArg (fun z : ℂ × Circle => (z.1 - (3 / 2 : ℂ))⁻¹) hs.symm)
    · change (normalOuterTubeMap c.q c.a y).2 =
        unitOf ((seamModel (normalT2IntervalDatum c.q) 0 (port (.inr 0))
          c.matchingUnit y).1 - (3 / 2 : ℂ)) ^ (-c.q) *
          (seamModel (normalT2IntervalDatum c.q) 0 (port (.inr 0)) c.matchingUnit y).2
      exact (congrArg (fun z : ℂ × Circle => z.2) he).trans
        (congrArg (fun z : ℂ × Circle => unitOf (z.1 - (3 / 2 : ℂ)) ^ (-c.q) * z.2)
          hs.symm)
  tube_product_overlap m := normalOuterAnnulusTube_product_overlap c.q c.a
  disjoint := by
    intro m n hmn
    change Fin 1 at m n
    exact False.elim (hmn (Subsingleton.elim m n))
  covers y hy := by
    rcases normalOuterAnnulus_cover c.q c.a y hy with hprod | htube
    · exact Or.inl hprod
    · exact Or.inr ⟨0, htube⟩

def normalOuterInteriorDiffeomorph {W : CompactCarrier.{u}} {q : ℤ}
    (C : SeifertBlockCharts W (normalT2IntervalDatum q))
    (hport : C.port (.inr 0) = (0 : Fin 3)) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, 𝓡 3⟯ TorusTimesLine := by
  let c := normalChartFilling C
  let D : SeifertBlockCharts annulusCircleCarrier.{u} (normalT2IntervalDatum q) :=
    normalOuterReferenceCharts c rfl C.port hport
  exact (C.compareInterior D rfl (normalChartFilling_matrix C)).trans
    annulusCircleInteriorDiffeo

def normalT2IntervalInteriorDiffeomorph {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (h : d.ports = 2 ∧ d.cones = []) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, 𝓡 3⟯ TorusTimesLine := by
  classical
  by_cases h0 : d.fillingCount = 0
  · have hk : d.k = 2 := by
      have hc := d.ports_add_fillingCount
      rw [h.1, h0, add_zero] at hc
      exact hc.symm
    have e : W.pieceInterior ⊤ ≃ₘ⟮W.model, PlaneCircleModel⟯ (planarOpen 2 × Circle) := by
      have f := C.unfilledProductInteriorDiffeomorph h0
      rw [hk] at f
      exact f
    exact (e.trans annulusCirclePiece.{u}.chartPieceInteriorDiffeomorph).trans
      annulusCircleInteriorDiffeo
  · have hex : ∃ q : ℤ, d = normalT2IntervalDatum q := by
      rcases normalT2IntervalShape d h with hh | ⟨hk, q, hn, hf⟩
      · exact False.elim (h0 hh.2.2)
      · exact ⟨q, normalT2IntervalDatum_eq d q hk h.1 h.2 hn⟩
    let q := Classical.choose hex
    have hd : d = normalT2IntervalDatum q := Classical.choose_spec hex
    let D : SeifertBlockCharts W (normalT2IntervalDatum q) := hd ▸ C
    by_cases hp0 : D.port (.inr 0) = (0 : Fin 3)
    · exact normalOuterInteriorDiffeomorph D hp0
    · by_cases hp1 : D.port (.inr 0) = (1 : Fin 3)
      · exact normalInnerOneInteriorDiffeomorph D hp1
      · have hp2 : D.port (.inr 0) = (2 : Fin 3) := by
          have hh := (D.port (.inr 0)).isLt
          apply Fin.ext
          have hn0 : (D.port (.inr 0)).val ≠ 0 := by
            intro he
            exact hp0 (Fin.ext he)
          have hn1 : (D.port (.inr 0)).val ≠ 1 := by
            intro he
            exact hp1 (Fin.ext he)
          change (D.port (.inr 0)).val = 2
          change (D.port (.inr 0)).val < 3 at hh
          omega
        exact normalInnerTwoInteriorDiffeomorph D hp2

def normalT2IntervalGeometry {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (h : d.ports = 2 ∧ d.cones = []) :
    W.InteriorGeometry ⊤ :=
  normalTorusIntervalGeometryOfDiffeomorph (normalT2IntervalInteriorDiffeomorph C h)

theorem normalT2IntervalGeometry_model {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (h : d.ports = 2 ∧ d.cones = []) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (normalT2IntervalGeometry C h).model = ThurstonModel.euclidean := rfl

end GC.Seifert
