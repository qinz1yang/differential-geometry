import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanCharts
import DifferentialGeometry.Geometry.Thurston.FlatTwistedBundle
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanNormal
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanSolid
/-!
# Euclidean geometry for every two-cone twisted block
Actual collar permutations and upper-triangular solid coordinates align the chart ports.
A whole pants fibre shear reduces arbitrary odd slopes to the standard pair (2,1),(2,-1).
The resulting actual whole-interior diffeomorphism transports the flat twisted geometry.
-/
set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology ComplexConjugate
universe u

namespace GC.Seifert

theorem odd_of_twoCone_bezout (q a b : ℤ) (h : 2 * b - a * q = 1) : Odd q ∧ Odd a := by
  have hp : Odd (a * q) := by
    refine odd_iff_exists_bit1.mpr ⟨b - 1, ?_⟩
    linarith
  exact ⟨(Int.odd_mul.mp hp).2, (Int.odd_mul.mp hp).1⟩

theorem twoConeBasis_normalization (q a b q₀ b₀ : ℤ)
    (h : 2 * b - a * q = 1) (h₀ : 2 * b₀ - q₀ = 1) :
    ∃ n k : ℤ, q + 2 * n = q₀ ∧ a + 2 * k = 1 ∧
      !![1, 0; n, 1] * chartConventionMatrix 2 q a b =
        chartConventionMatrix 2 q₀ 1 b₀ * !![1, k; 0, 1] := by
  obtain ⟨hqodd, haodd⟩ := odd_of_twoCone_bezout q a b h
  obtain ⟨t, ht⟩ := hqodd.exists_bit1
  obtain ⟨s, hs⟩ := haodd.exists_bit1
  have hb : b = 2 * s * t + s + t + 1 := by
    rw [hs, ht] at h
    nlinarith [h]
  have hq₀ : q₀ = 2 * b₀ - 1 := by linarith
  refine ⟨b₀ - t - 1, -s, ?_, ?_, ?_⟩
  · omega
  · omega
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chartConventionMatrix, Matrix.mul_apply,
        Fin.sum_univ_two, ht, hs, hb, hq₀] <;> ring

theorem twoConeBasis_normalization_positive (q a b : ℤ) (h : 2 * b - a * q = 1) :
    ∃ n k : ℤ, q + 2 * n = 1 ∧ a + 2 * k = 1 ∧
      !![1, 0; n, 1] * chartConventionMatrix 2 q a b =
        chartConventionMatrix 2 1 1 1 * !![1, k; 0, 1] :=
  twoConeBasis_normalization q a b 1 1 h (by norm_num)

theorem twoConeBasis_normalization_negative (q a b : ℤ) (h : 2 * b - a * q = 1) :
    ∃ n k : ℤ, q + 2 * n = -1 ∧ a + 2 * k = 1 ∧
      !![1, 0; n, 1] * chartConventionMatrix 2 q a b =
        chartConventionMatrix 2 (-1) 1 0 * !![1, k; 0, 1] :=
  twoConeBasis_normalization q a b (-1) 0 h (by norm_num)

theorem twoConeBasis_solid_boundary (k : ℤ) (t : Torus) :
    solidBasisExtension false false k ((t.1 : ℂ), t.2) =
      (((linearTorusMap !![1, k; 0, 1] t).1 : ℂ),
        (linearTorusMap !![1, k; 0, 1] t).2) :=
  solidBasisExtension_boundary false false k t

theorem SeifertBlockCharts.twoConeBasis_normalization
    {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
    (m : Fin d.fillingCount) (hp : (d.fillingSlope m).1 = 2)
    (q₀ b₀ : ℤ) (h₀ : 2 * b₀ - q₀ = 1) :
    ∃ n k : ℤ, (d.fillingSlope m).2 + 2 * n = q₀ ∧ C.a m + 2 * k = 1 ∧
      !![1, 0; n, 1] * (C.matrix m : Matrix (Fin 2) (Fin 2) ℤ) =
        chartConventionMatrix 2 q₀ 1 b₀ * !![1, k; 0, 1] := by
  have h := C.bezout m
  rw [hp] at h
  obtain ⟨n, k, hq, ha, hmatrix⟩ :=
    GC.Seifert.twoConeBasis_normalization (d.fillingSlope m).2 (C.a m) (C.b m) q₀ b₀ h h₀
  refine ⟨n, k, hq, ha, ?_⟩
  rw [C.matrix_eq m, hp]
  exact hmatrix

theorem twoConeData_counts {d : SeifertData} (q₁ q₂ : ℤ)
    (hports : d.ports = 1) (hcones : d.cones = [(2, q₁), (2, q₂)]) :
    d.k = 3 ∧ d.normals = [] ∧ d.fillingCount = 2 := by
  have h := d.ports_add_length_add_length
  rw [hports, hcones] at h
  simp only [List.length_cons, List.length_nil] at h
  have hn : d.normals.length = 0 := by have hk := d.k_le_three; omega
  have he : d.normals = [] := List.length_eq_zero_iff.mp hn
  refine ⟨by omega, he, ?_⟩
  simp [SeifertData.fillingCount, hcones, he]

def twoHolePhase (n₁ n₂ : ℤ) (z : ℂ) : Circle :=
  holeShear z ^ n₁ * holeShear (-z) ^ n₂

theorem twoHolePhase_neg (n₁ n₂ : ℤ) (z : ℂ) :
    twoHolePhase (-n₁) (-n₂) z = (twoHolePhase n₁ n₂ z)⁻¹ := by
  rw [twoHolePhase, twoHolePhase, zpow_neg, zpow_neg, mul_inv_rev]
  exact mul_comm _ _

theorem contMDiffAt_twoHolePhase (n₁ n₂ : ℤ) {z : ℂ}
    (h₁ : z ≠ 3 / 2) (h₂ : z ≠ -(3 / 2)) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 1) ∞ (twoHolePhase n₁ n₂) z := by
  have hn : -z ≠ (3 / 2 : ℂ) := by
    intro he
    apply h₂
    linear_combination -he
  exact ((contMDiff_circle_zpow n₁).contMDiffAt.comp z (contMDiffAt_holeShear h₁)).mul
    ((contMDiff_circle_zpow n₂).contMDiffAt.comp z
      ((contMDiffAt_holeShear hn).comp z contDiffAt_id.neg.contMDiffAt))

theorem contMDiff_twoHoleShearBy (n₁ n₂ : ℤ) :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (pantsShearBy.{u} (twoHolePhase n₁ n₂)) := by
  refine ((productAtlas.{u} 3).contMDiff_iff_subtype_val _).mpr fun x => ?_
  have hv := (productAtlas.{u} 3).contMDiff_subtype_val x
  have hz : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞
      (fun x : productSet.{u} 3 => x.val.1.down) x :=
    (contMDiff_planeLift_down.comp contMDiff_fst).contMDiffAt.comp x hv
  exact (contMDiff_fst.contMDiffAt.comp x hv).prodMk
    ((contMDiff_snd.contMDiffAt.comp x hv).mul
      ((contMDiffAt_twoHolePhase n₁ n₂ (pantsGood_of_mem_productSet x).1
        (pantsGood_of_mem_productSet x).2).comp x hz))

def twoHoleProductShear (n₁ n₂ : ℤ) :
    productSet.{u} 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ productSet.{u} 3 where
  toFun := pantsShearBy (twoHolePhase n₁ n₂)
  invFun := pantsShearBy (twoHolePhase (-n₁) (-n₂))
  left_inv x := by
    apply Subtype.ext
    refine Prod.ext (Eq.refl x.val.1) ?_
    change x.val.2 * twoHolePhase n₁ n₂ x.val.1.down *
      twoHolePhase (-n₁) (-n₂) x.val.1.down = x.val.2
    rw [twoHolePhase_neg]
    exact mul_inv_cancel_right _ _
  right_inv x := by
    apply Subtype.ext
    refine Prod.ext (Eq.refl x.val.1) ?_
    change x.val.2 * twoHolePhase (-n₁) (-n₂) x.val.1.down *
      twoHolePhase n₁ n₂ x.val.1.down = x.val.2
    rw [twoHolePhase_neg]
    exact inv_mul_cancel_right _ _
  contMDiff_toFun := contMDiff_twoHoleShearBy n₁ n₂
  contMDiff_invFun := contMDiff_twoHoleShearBy (-n₁) (-n₂)

theorem twoConeData_odd {d : SeifertData} (q₁ q₂ : ℤ)
    (hcones : d.cones = [(2, q₁), (2, q₂)]) : Odd q₁ ∧ Odd q₂ := by
  have h₁ := d.gcd_eq_one_of_mem_cones (2, q₁) (by simp [hcones])
  have h₂ := d.gcd_eq_one_of_mem_cones (2, q₂) (by simp [hcones])
  constructor
  · exact Int.natAbs_odd.mp (Nat.coprime_two_left.mp h₁)
  · exact Int.natAbs_odd.mp (Nat.coprime_two_left.mp h₂)

theorem twoHolePhase_collar_one (n₁ n₂ : ℤ) (t : Circle) {m : ℝ}
    (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    twoHolePhase n₁ n₂ (planarCollarFormula 3 1 ((t : ℂ), m)) = t ^ (-n₁) := by
  have he : planarCollarFormula 3 1 ((t : ℂ), m) - 3 / 2 =
      ((1 / 2 + m / 4 : ℝ) : ℂ) * ((t⁻¹ : Circle) : ℂ) := by
    rw [planarCollarFormula_hole 1 (by decide), planarCenter_three_one]
    push_cast
    ring
  have hpos : (0 : ℝ) < 1 / 2 + m / 4 := by linarith
  have hn : ‖-planarCollarFormula 3 1 ((t : ℂ), m) + 3 / 2‖ ≤ 3 / 4 := by
    rw [show -planarCollarFormula 3 1 ((t : ℂ), m) + 3 / 2 =
      -(planarCollarFormula 3 1 ((t : ℂ), m) - 3 / 2) by ring, norm_neg, he,
      norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    linarith
  rw [twoHolePhase, holeShear_collar_one t h0 h1, holeShear_of_near_two hn]
  simp [inv_zpow']

theorem twoHolePhase_collar_two (n₁ n₂ : ℤ) (t : Circle) {m : ℝ}
    (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    twoHolePhase n₁ n₂ (planarCollarFormula 3 2 ((t : ℂ), m)) =
      (circleI ^ 2) ^ n₂ * t ^ (-n₂) := by
  have he : planarCollarFormula 3 2 ((t : ℂ), m) + 3 / 2 =
      ((1 / 2 + m / 4 : ℝ) : ℂ) * ((t⁻¹ : Circle) : ℂ) := by
    rw [planarCollarFormula_hole 2 (by decide), planarCenter_three_two]
    push_cast
    ring
  have hpos : (0 : ℝ) < 1 / 2 + m / 4 := by linarith
  have hn : ‖-planarCollarFormula 3 2 ((t : ℂ), m) - 3 / 2‖ ≤ 3 / 4 := by
    rw [show -planarCollarFormula 3 2 ((t : ℂ), m) - 3 / 2 =
      -(planarCollarFormula 3 2 ((t : ℂ), m) + 3 / 2) by ring, norm_neg, he,
      norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    linarith
  have hne : planarCollarFormula 3 2 ((t : ℂ), m) + 3 / 2 ≠ 0 := by
    rw [he]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne') (Circle.coe_ne_zero _)
  rw [twoHolePhase, holeShear_collar_two t h0 h1, one_zpow, one_mul,
    holeShear_of_near_one hn,
    show -planarCollarFormula 3 2 ((t : ℂ), m) - 3 / 2 =
      -(planarCollarFormula 3 2 ((t : ℂ), m) + 3 / 2) by ring,
    unitOf_neg hne, he, unitOf_ofReal_mul hpos, mul_zpow, inv_zpow']

theorem twoHoleProductShear_productCollar (n₁ n₂ : ℤ) (j : Fin 3)
    (p : Torus × EuclideanHalfSpace 1) :
    twoHoleProductShear n₁ n₂ (productCollar.{u} 3 (Or.inr rfl) j p) =
      productCollar.{u} 3 (Or.inr rfl) j
        ((p.1.1, p.1.2 * twoHolePhase n₁ n₂
          (planarCollarFormula 3 j ((p.1.1 : ℂ), min (p.2.val 0) 1))), p.2) := rfl

def twistedStandardCharts : SeifertBlockCharts mobiusBundleCarrier.{u} twistedIBundleData :=
  Classical.choice (mobiusTwistedIBundle.exists_charts_of_linear (fun m => by
    change holeMatching m = linearTorusDiffeomorph (torusUnit (holeMatching m))
    fin_cases m
    · change twistedMatching = linearTorusDiffeomorph (torusUnit twistedMatching)
      rw [twistedMatching, torusUnit_linearTorusDiffeomorph]
    · change seamMatching = linearTorusDiffeomorph (torusUnit seamMatching)
      rw [seamMatching, torusUnit_linearTorusDiffeomorph]))

theorem twoConeBasis_normalized_boundary (q a b q₀ b₀ : ℤ)
    (h : 2 * b - a * q = 1) (h₀ : 2 * b₀ - q₀ = 1) :
    ∃ n k : ℤ, q + 2 * n = q₀ ∧ a + 2 * k = 1 ∧ ∀ t : Torus,
      linearTorusMap (!![1, 0; n, 1])
        (linearTorusMap (chartConventionMatrix 2 q a b) t) =
      linearTorusMap (chartConventionMatrix 2 q₀ 1 b₀)
        (unitOf (solidBasisExtension false false k ((t.1 : ℂ), t.2)).1,
          (solidBasisExtension false false k ((t.1 : ℂ), t.2)).2) := by
  obtain ⟨n, k, hq, ha, hmatrix⟩ := twoConeBasis_normalization q a b q₀ b₀ h h₀
  refine ⟨n, k, hq, ha, fun t => ?_⟩
  rw [twoConeBasis_solid_boundary, unitOf_circle, ← linearTorusMap_mul,
    hmatrix, linearTorusMap_mul]

theorem twoHoleProductShear_productCollar_one (n₁ n₂ : ℤ)
    (p : Torus × EuclideanHalfSpace 1) :
    twoHoleProductShear n₁ n₂ (productCollar.{u} 3 (Or.inr rfl) 1 p) =
      productCollar.{u} 3 (Or.inr rfl) 1 ((p.1.1, p.1.2 * p.1.1 ^ (-n₁)), p.2) := by
  rw [twoHoleProductShear_productCollar,
    twoHolePhase_collar_one n₁ n₂ p.1.1 (min_mem_unit p.2).1 (min_mem_unit p.2).2]

theorem twoHoleProductShear_productCollar_two (n₁ n₂ : ℤ)
    (p : Torus × EuclideanHalfSpace 1) :
    twoHoleProductShear n₁ n₂ (productCollar.{u} 3 (Or.inr rfl) 2 p) =
      productCollar.{u} 3 (Or.inr rfl) 2
        ((p.1.1, p.1.2 * ((circleI ^ 2) ^ n₂ * p.1.1 ^ (-n₂))), p.2) := by
  rw [twoHoleProductShear_productCollar,
    twoHolePhase_collar_two n₁ n₂ p.1.1 (min_mem_unit p.2).1 (min_mem_unit p.2).2]

theorem twoHolePhase_seamModel_one (d : SeifertData) (m : Fin d.fillingCount)
    (j : Fin d.k) (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (n₁ n₂ : ℤ)
    (hk : d.k = 3) (hp : (d.fillingSlope m).1 = 2) (hj : j.val = 1)
    (h0 : 1 ≤ ‖y.1‖ ^ 2) (h1 : ‖y.1‖ ^ 2 ≤ 3 / 2) :
    twoHolePhase n₁ n₂ (seamModel d m j A y).1 =
      (linearTorusMap A (unitOf y.1, y.2)).1 ^ (-n₁) := by
  have he : (seamModel d m j A y).1 = planarCollarFormula 3 1
      (((linearTorusMap A (unitOf y.1, y.2)).1 : ℂ), 2 * (‖y.1‖ ^ 2 - 1)) := by
    simp only [seamModel, hp, planarCenter, planarRadius, hj, hk]
    norm_num [planarCollarFormula, planarSign, planarTwist, planarRadius, planarCenter]
    ring
  rw [he]
  exact twoHolePhase_collar_one n₁ n₂ _ (by linarith) (by linarith)

theorem twoHolePhase_seamModel_two (d : SeifertData) (m : Fin d.fillingCount)
    (j : Fin d.k) (A : GL (Fin 2) ℤ) (y : ℂ × Circle) (n₁ n₂ : ℤ)
    (hk : d.k = 3) (hp : (d.fillingSlope m).1 = 2) (hj : j.val = 2)
    (h0 : 1 ≤ ‖y.1‖ ^ 2) (h1 : ‖y.1‖ ^ 2 ≤ 3 / 2) :
    twoHolePhase n₁ n₂ (seamModel d m j A y).1 = (circleI ^ 2) ^ n₂ *
      (linearTorusMap A (unitOf y.1, y.2)).1 ^ (-n₂) := by
  have he : (seamModel d m j A y).1 = planarCollarFormula 3 2
      (((linearTorusMap A (unitOf y.1, y.2)).1 : ℂ), 2 * (‖y.1‖ ^ 2 - 1)) := by
    simp only [seamModel, hp, planarCenter, planarRadius, hj, hk]
    norm_num [planarCollarFormula, planarSign, planarTwist, planarRadius, planarCenter]
    ring
  rw [he]
  exact twoHolePhase_collar_two n₁ n₂ _ (by linarith) (by linarith)

def solidUpperBasisUnit (n : ℤ) : GL (Fin 2) ℤ :=
  PrimitiveSlope.unitOfDet !![1, n; 0, 1] (Or.inl (by simp [Matrix.det_fin_two_of]))

theorem solidUpperBasisUnit_val (n : ℤ) :
    (solidUpperBasisUnit n : Matrix (Fin 2) (Fin 2) ℤ) = !![1, n; 0, 1] :=
  PrimitiveSlope.val_unitOfDet _ _

theorem solidBasisExtension_unitOf (n : ℤ) (y : ℂ × Circle) (hy : y.1 ≠ 0) :
    (unitOf (solidBasisExtension false false n y).1,
      (solidBasisExtension false false n y).2) =
        linearTorusMap (solidUpperBasisUnit n) (unitOf y.1, y.2) := by
  apply Prod.ext
  · change unitOf (y.1 * ((y.2 ^ n : Circle) : ℂ)) = _
    rw [unitOf_mul hy (Circle.coe_ne_zero _), unitOf_circle, solidUpperBasisUnit_val]
    simp [linearTorusMap]
  · change y.2 = (linearTorusMap (solidUpperBasisUnit n) (unitOf y.1, y.2)).2
    simp [solidUpperBasisUnit_val, linearTorusMap]

theorem seamModel_solidBasisExtension (d : SeifertData) (m : Fin d.fillingCount)
    (j : Fin d.k) (A : GL (Fin 2) ℤ) (n : ℤ) (y : ℂ × Circle) (hy : y.1 ≠ 0) :
    seamModel d m j (A * solidUpperBasisUnit n) y =
      seamModel d m j A (solidBasisExtension false false n y) := by
  simp only [seamModel, solidBasisExtension_norm, solidBasisExtension_unitOf n y hy,
    Units.val_mul, linearTorusMap_mul]

def SeifertBlockCharts.rebasedTube {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (n : Fin d.fillingCount → ℤ) (m : Fin d.fillingCount) :
    PartialDiffeomorph PlaneCircleModel W.model (ℂ × Circle) W.Carrier ∞ :=
  (solidBasisExtension false false (n m)).toPartialDiffeomorph.trans (C.tube m)

theorem SeifertBlockCharts.rebasedTube_source {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (n : Fin d.fillingCount → ℤ) (m : Fin d.fillingCount) :
    (C.rebasedTube n m).source = {y : ℂ × Circle | ‖y.1‖ < 1 + C.ε} := by
  ext y
  change (y ∈ Set.univ ∧ solidBasisExtension false false (n m) y ∈ (C.tube m).source) ↔ _
  rw [C.tube_source]
  simp only [Set.mem_univ, true_and, Set.mem_ofPred_eq, solidBasisExtension_norm]

theorem SeifertBlockCharts.rebasedTube_target {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (n : Fin d.fillingCount → ℤ) (m : Fin d.fillingCount) :
    (C.rebasedTube n m).target = (C.tube m).target := by
  ext x
  change (x ∈ (C.tube m).target ∧ (C.tube m).symm x ∈ Set.univ) ↔ _
  simp only [Set.mem_univ, and_true]

theorem solidBasisExtension_transitionDomain {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (n : ℤ) (y : ℂ × Circle) :
    solidBasisExtension false false n y ∈ C.transitionDomain ↔ y ∈ C.transitionDomain := by
  rw [C.transitionDomain_eq]
  simp only [Set.mem_ofPred_eq, solidBasisExtension_norm]

def SeifertBlockCharts.rebasis {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (n : Fin d.fillingCount → ℤ) : SeifertBlockCharts W d where
  port := C.port
  matrix m := C.matrix m * solidUpperBasisUnit (n m)
  a m := C.a m - (d.fillingSlope m).1 * n m
  b m := C.b m - (d.fillingSlope m).2 * n m
  matrix_eq m := by
    rw [Units.val_mul, C.matrix_eq m, solidUpperBasisUnit_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  bezout m := by
    have h := C.bezout m
    nlinarith
  productRegion := C.productRegion
  productRegion_interior := C.productRegion_interior
  product := C.product
  ε := C.ε
  ε_pos := C.ε_pos
  tube := C.rebasedTube n
  tube_source := C.rebasedTube_source n
  tube_interior m := C.rebasedTube_target n m ▸ C.tube_interior m
  transitionDomain := C.transitionDomain
  transitionDomain_eq := C.transitionDomain_eq
  transition_domain m y hy := by
    have hne : y.1 ≠ 0 := by
      rw [C.transitionDomain_eq] at hy
      exact norm_pos_iff.mp (by linarith [hy.1])
    rw [seamModel_solidBasisExtension d m (C.port (.inr m)) (C.matrix m) (n m) y hne]
    exact C.transition_domain m ((solidBasisExtension_transitionDomain C (n m) y).mpr hy)
  transition m y hy := by
    have hne : y.1 ≠ 0 := by
      rw [C.transitionDomain_eq] at hy
      exact norm_pos_iff.mp (by linarith [hy.1])
    have he := seamModel_solidBasisExtension d m (C.port (.inr m)) (C.matrix m) (n m) y hne
    change C.tube m (solidBasisExtension false false (n m) y) = _
    rw [C.transition m _ ((solidBasisExtension_transitionDomain C (n m) y).mpr hy)]
    apply congrArg (fun z : planarOpen d.k × Circle => (C.product z : W.Carrier))
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst he.symm)
    · exact congrArg (fun z : ℂ × Circle => z.2) he.symm
  tube_product_overlap m := by
    rw [C.rebasedTube_target, C.tube_product_overlap m]
    ext x
    constructor
    · rintro ⟨y, hy, hx⟩
      let Q := solidBasisExtension false false (n m)
      refine ⟨Q.symm y, ?_, ?_⟩
      · have h := (solidBasisExtension_transitionDomain C (n m) (Q.symm y))
        rw [Q.apply_symm_apply] at h
        exact h.mp hy
      · change C.tube m (Q (Q.symm y)) = x
        rw [Q.apply_symm_apply]
        exact hx
    · rintro ⟨y, hy, hx⟩
      exact ⟨solidBasisExtension false false (n m) y,
        (solidBasisExtension_transitionDomain C (n m) y).mpr hy, hx⟩
  disjoint m l h := by
    change Disjoint (C.rebasedTube n m).target (C.rebasedTube n l).target
    rw [C.rebasedTube_target, C.rebasedTube_target]
    exact C.disjoint h
  covers x hx := by
    rcases C.covers x hx with hp | ⟨m, hm⟩
    · exact Or.inl hp
    · exact Or.inr ⟨m, C.rebasedTube_target n m ▸ hm⟩

theorem SeifertBlockCharts.rebasis_port {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (n : Fin d.fillingCount → ℤ) :
    (C.rebasis n).port = C.port := rfl

theorem SeifertBlockCharts.rebasis_matrix {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (n : Fin d.fillingCount → ℤ) (m : Fin d.fillingCount) :
    (C.rebasis n).matrix m = C.matrix m * solidUpperBasisUnit (n m) := rfl

def SeifertBlockCharts.twoConeCanonicalShift {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (hp : ∀ m, (d.fillingSlope m).1 = 2)
    (m : Fin d.fillingCount) : ℤ := by
  have h := C.bezout m
  rw [hp m] at h
  exact Classical.choose (odd_of_twoCone_bezout _ _ _ h).2.exists_bit1

theorem SeifertBlockCharts.twoConeCanonicalShift_spec {W : CompactCarrier.{u}}
    {d : SeifertData} (C : SeifertBlockCharts W d)
    (hp : ∀ m, (d.fillingSlope m).1 = 2) (m : Fin d.fillingCount) :
    C.a m = 2 * C.twoConeCanonicalShift hp m + 1 := by
  unfold twoConeCanonicalShift
  exact Classical.choose_spec (odd_of_twoCone_bezout _ _ _ (hp m ▸ C.bezout m)).2.exists_bit1

def SeifertBlockCharts.canonicalTwoConeCharts {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (hp : ∀ m, (d.fillingSlope m).1 = 2) :
    SeifertBlockCharts W d := C.rebasis (C.twoConeCanonicalShift hp)

theorem SeifertBlockCharts.canonicalTwoConeCharts_a {W : CompactCarrier.{u}}
    {d : SeifertData} (C : SeifertBlockCharts W d)
    (hp : ∀ m, (d.fillingSlope m).1 = 2) (m : Fin d.fillingCount) :
    (C.canonicalTwoConeCharts hp).a m = 1 := by
  change C.a m - (d.fillingSlope m).1 * C.twoConeCanonicalShift hp m = 1
  rw [hp m, C.twoConeCanonicalShift_spec hp m]
  ring

theorem SeifertBlockCharts.canonicalTwoConeCharts_matrix {W V : CompactCarrier.{u}}
    {d : SeifertData} (C : SeifertBlockCharts W d) (D : SeifertBlockCharts V d)
    (hp : ∀ m, (d.fillingSlope m).1 = 2) (m : Fin d.fillingCount) :
    (C.canonicalTwoConeCharts hp).matrix m = (D.canonicalTwoConeCharts hp).matrix m := by
  have hC := (C.canonicalTwoConeCharts hp).bezout m
  have hD := (D.canonicalTwoConeCharts hp).bezout m
  rw [C.canonicalTwoConeCharts_a hp m, hp m] at hC
  rw [D.canonicalTwoConeCharts_a hp m, hp m] at hD
  have hb : (C.canonicalTwoConeCharts hp).b m = (D.canonicalTwoConeCharts hp).b m := by
    omega
  apply Units.ext
  rw [(C.canonicalTwoConeCharts hp).matrix_eq, (D.canonicalTwoConeCharts hp).matrix_eq,
    C.canonicalTwoConeCharts_a, D.canonicalTwoConeCharts_a, hb]


abbrev twoConeDatum (q₁ q₂ : ℤ) (h₁ : Odd q₁) (h₂ : Odd q₂) : SeifertData where
  k := 3
  ports := 1
  cones := [(2, q₁), (2, q₂)]
  normals := []
  one_le_k := by decide
  k_le_three := by decide
  two_le_of_mem_cones c hc := by simp at hc; aesop
  gcd_eq_one_of_mem_cones c hc := by
    have hcc : c = (2, q₁) ∨ c = (2, q₂) := by simpa using hc
    rcases hcc with rfl | rfl
    · exact Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr h₁)
    · exact Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr h₂)
  ports_add_length_add_length := rfl

theorem twoConeDatum_fillingSlope (q₁ q₂ : ℤ) (h₁ : Odd q₁) (h₂ : Odd q₂)
    (m : Fin 2) : (twoConeDatum q₁ q₂ h₁ h₂).fillingSlope m =
      (2, if m = 0 then q₁ else q₂) := by
  fin_cases m <;> simp [twoConeDatum, SeifertData.fillingSlope, Fin.append, Fin.addCases]

theorem twoConeData_eq {d : SeifertData} (q₁ q₂ : ℤ)
    (hports : d.ports = 1) (hcones : d.cones = [(2, q₁), (2, q₂)]) :
    d = twoConeDatum q₁ q₂ (twoConeData_odd q₁ q₂ hcones).1
      (twoConeData_odd q₁ q₂ hcones).2 := by
  obtain ⟨hk, hn, _⟩ := twoConeData_counts q₁ q₂ hports hcones
  cases d
  dsimp only at hports hcones hk hn
  subst_vars
  rfl

def twoHoleOpenShear (n₁ n₂ : ℤ) :
    (planarOpen 3 × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯ (planarOpen 3 × Circle) where
  toFun x := (x.1, x.2 * twoHolePhase n₁ n₂ x.1.val)
  invFun x := (x.1, x.2 * twoHolePhase (-n₁) (-n₂) x.1.val)
  left_inv x := by
    refine Prod.ext rfl ?_
    change x.2 * twoHolePhase n₁ n₂ x.1.val * twoHolePhase (-n₁) (-n₂) x.1.val = x.2
    rw [twoHolePhase_neg]
    exact mul_inv_cancel_right _ _
  right_inv x := by
    refine Prod.ext rfl ?_
    change x.2 * twoHolePhase (-n₁) (-n₂) x.1.val * twoHolePhase n₁ n₂ x.1.val = x.2
    rw [twoHolePhase_neg]
    exact inv_mul_cancel_right _ _
  contMDiff_toFun := by
    have hphase : ContMDiff 𝓘(ℝ, ℂ) (𝓡 1) ∞
        (fun z : planarOpen 3 => twoHolePhase n₁ n₂ z.val) := by
      intro z
      have hm := interior_subset z.property
      have hg : z.val ≠ 3 / 2 ∧ z.val ≠ -(3 / 2) := by
        rcases (mem_planarModel_three z.val).mp hm with ⟨_, h1, h2⟩
        constructor
        · intro he
          norm_num [he] at h1
        · intro he
          norm_num [he] at h2
      exact (contMDiffAt_twoHolePhase n₁ n₂ hg.1 hg.2).comp z
        contMDiff_subtype_val.contMDiffAt
    exact contMDiff_fst.prodMk (contMDiff_snd.mul (hphase.comp contMDiff_fst))
  contMDiff_invFun := by
    have hphase : ContMDiff 𝓘(ℝ, ℂ) (𝓡 1) ∞
        (fun z : planarOpen 3 => twoHolePhase (-n₁) (-n₂) z.val) := by
      intro z
      have hm := interior_subset z.property
      have hg : z.val ≠ 3 / 2 ∧ z.val ≠ -(3 / 2) := by
        rcases (mem_planarModel_three z.val).mp hm with ⟨_, h1, h2⟩
        constructor
        · intro he
          norm_num [he] at h1
        · intro he
          norm_num [he] at h2
      exact (contMDiffAt_twoHolePhase (-n₁) (-n₂) hg.1 hg.2).comp z
        contMDiff_subtype_val.contMDiffAt
    exact contMDiff_fst.prodMk (contMDiff_snd.mul (hphase.comp contMDiff_fst))


def twoConeStandardSlope (m : Fin 2) : ℤ := if m = 0 then 1 else -1

def twoConeStandardBezout (m : Fin 2) : ℤ := if m = 0 then 1 else 0

def twoConeSlopeShift (q₁ q₂ : ℤ) (h₁ : Odd q₁) (h₂ : Odd q₂) (m : Fin 2) : ℤ :=
  if m = 0 then -Classical.choose h₁.exists_bit1 else -Classical.choose h₂.exists_bit1 - 1

theorem twoConeSlopeShift_spec (q₁ q₂ : ℤ) (h₁ : Odd q₁) (h₂ : Odd q₂) (m : Fin 2) :
    ((twoConeDatum q₁ q₂ h₁ h₂).fillingSlope m).2 +
      2 * twoConeSlopeShift q₁ q₂ h₁ h₂ m = twoConeStandardSlope m := by
  have ht₁ := Classical.choose_spec h₁.exists_bit1
  have ht₂ := Classical.choose_spec h₂.exists_bit1
  rw [twoConeDatum_fillingSlope]
  fin_cases m <;> simp [twoConeSlopeShift, twoConeStandardSlope] <;> omega

def twoConeStandardMatrix (m : Fin 2) : GL (Fin 2) ℤ :=
  chartConventionUnit 2 (twoConeStandardSlope m) 1 (twoConeStandardBezout m)
    (by fin_cases m <;> norm_num [twoConeStandardSlope, twoConeStandardBezout])

theorem twoConeNormalizedMatrix {W : CompactCarrier.{u}} (q₁ q₂ : ℤ)
    (h₁ : Odd q₁) (h₂ : Odd q₂) (C : SeifertBlockCharts W (twoConeDatum q₁ q₂ h₁ h₂))
    (ha : ∀ m, C.a m = 1) (m : Fin 2) :
    !![1, 0; twoConeSlopeShift q₁ q₂ h₁ h₂ m, 1] *
      (C.matrix m : Matrix (Fin 2) (Fin 2) ℤ) = twoConeStandardMatrix m := by
  have hp : ((twoConeDatum q₁ q₂ h₁ h₂).fillingSlope m).1 = 2 := by
    rw [twoConeDatum_fillingSlope]
  have hb := C.bezout m
  rw [hp, ha m] at hb
  have hn := twoConeSlopeShift_spec q₁ q₂ h₁ h₂ m
  have hz : 2 * twoConeStandardBezout m - twoConeStandardSlope m = 1 := by
    fin_cases m <;> norm_num [twoConeStandardBezout, twoConeStandardSlope]
  have hbn : C.b m + twoConeSlopeShift q₁ q₂ h₁ h₂ m = twoConeStandardBezout m := by omega
  rw [C.matrix_eq m, ha m, hp]
  change _ = chartConventionMatrix 2 (twoConeStandardSlope m) 1 (twoConeStandardBezout m)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartConventionMatrix, Matrix.mul_apply,
    Fin.sum_univ_two] <;> omega

def twoConeTubePhase (q₁ q₂ : ℤ) (h₁ : Odd q₁) (h₂ : Odd q₂) (m : Fin 2) : Torus :=
  (1, if m = 0 then 1 else (circleI ^ 2) ^ (-twoConeSlopeShift q₁ q₂ h₁ h₂ 1))

def twoConeTubeCorrection (q₁ q₂ : ℤ) (h₁ : Odd q₁) (h₂ : Odd q₂) (m : Fin 2) :
    (ℂ × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯ (ℂ × Circle) :=
  normalTubeTranslation ((linearTorusDiffeomorph (twoConeStandardMatrix m)).symm
    (twoConeTubePhase q₁ q₂ h₁ h₂ m))

theorem twoConeTubeCorrection_norm (q₁ q₂ : ℤ) (h₁ : Odd q₁) (h₂ : Odd q₂)
    (m : Fin 2) (y : ℂ × Circle) :
    ‖(twoConeTubeCorrection q₁ q₂ h₁ h₂ m y).1‖ = ‖y.1‖ :=
  normalTubeTranslation_norm _ _

theorem twoConeTubeCorrection_angles (q₁ q₂ : ℤ) (h₁ : Odd q₁) (h₂ : Odd q₂)
    (m : Fin 2) (y : ℂ × Circle) (hy : y.1 ≠ 0) :
    linearTorusMap (twoConeStandardMatrix m)
      (unitOf (twoConeTubeCorrection q₁ q₂ h₁ h₂ m y).1,
        (twoConeTubeCorrection q₁ q₂ h₁ h₂ m y).2) =
      twoConeTubePhase q₁ q₂ h₁ h₂ m *
        linearTorusMap (twoConeStandardMatrix m) (unitOf y.1, y.2) := by
  let v := (linearTorusDiffeomorph (twoConeStandardMatrix m)).symm
    (twoConeTubePhase q₁ q₂ h₁ h₂ m)
  change linearTorusMap (twoConeStandardMatrix m)
    (unitOf ((v.1 : ℂ) * y.1), v.2 * y.2) = _
  rw [unitOf_mul (Circle.coe_ne_zero v.1) hy, unitOf_circle]
  change linearTorusMap (twoConeStandardMatrix m) (v * (unitOf y.1, y.2)) = _
  rw [normalLinearTorusMap_mul_point]
  exact congrArg (fun t : Torus => t * linearTorusMap (twoConeStandardMatrix m)
    (unitOf y.1, y.2)) ((linearTorusDiffeomorph (twoConeStandardMatrix m)).apply_symm_apply _)


theorem twistedIBundleData_fillingSlope (m : Fin 2) :
    twistedIBundleData.fillingSlope m = (2, twoConeStandardSlope m) := by
  fin_cases m <;> simp [twistedIBundleData, SeifertData.fillingSlope, Fin.append, Fin.addCases,
    twoConeStandardSlope]

theorem twoConeNormalizedSeam {W : CompactCarrier.{u}} (q₁ q₂ : ℤ)
    (h₁ : Odd q₁) (h₂ : Odd q₂) (C : SeifertBlockCharts W (twoConeDatum q₁ q₂ h₁ h₂))
    (ha : ∀ m, C.a m = 1) (hport : ∀ m, C.port (.inr m) = m.succ)
    (m : Fin 2) (y : ℂ × Circle) (h0 : 1 ≤ ‖y.1‖ ^ 2) (h1 : ‖y.1‖ ^ 2 ≤ 3 / 2) :
    let z := seamModel (twoConeDatum q₁ q₂ h₁ h₂) m (C.port (.inr m)) (C.matrix m) y
    (z.1, z.2 * twoHolePhase (-twoConeSlopeShift q₁ q₂ h₁ h₂ 0)
      (-twoConeSlopeShift q₁ q₂ h₁ h₂ 1) z.1) =
      seamModel twistedIBundleData m m.succ (twoConeStandardMatrix m)
        (twoConeTubeCorrection q₁ q₂ h₁ h₂ m y) := by
  let d := twoConeDatum q₁ q₂ h₁ h₂
  let n := twoConeSlopeShift q₁ q₂ h₁ h₂
  let t := linearTorusMap (C.matrix m) (unitOf y.1, y.2)
  have hp : (d.fillingSlope m).1 = 2 := by rw [twoConeDatum_fillingSlope]
  have hps : (twistedIBundleData.fillingSlope m).1 = 2 := by
    rw [twistedIBundleData_fillingSlope]
  have hne : y.1 ≠ 0 := by
    intro he
    norm_num [he] at h0
  have ht : linearTorusMap (twoConeStandardMatrix m) (unitOf y.1, y.2) =
      (t.1, t.1 ^ n m * t.2) := by
    rw [← twoConeNormalizedMatrix q₁ q₂ h₁ h₂ C ha m, linearTorusMap_mul]
    simp [linearTorusMap, t, n]
  have hQ : linearTorusMap (twoConeStandardMatrix m)
      (unitOf (twoConeTubeCorrection q₁ q₂ h₁ h₂ m y).1,
        (twoConeTubeCorrection q₁ q₂ h₁ h₂ m y).2) =
      (t.1, (twoConeTubePhase q₁ q₂ h₁ h₂ m).2 * (t.1 ^ n m * t.2)) := by
    rw [twoConeTubeCorrection_angles q₁ q₂ h₁ h₂ m y hne, ht]
    exact Prod.ext (one_mul t.1) rfl
  have hphase : twoHolePhase (-n 0) (-n 1)
      (seamModel d m (C.port (.inr m)) (C.matrix m) y).1 =
        (twoConeTubePhase q₁ q₂ h₁ h₂ m).2 * t.1 ^ n m := by
    fin_cases m
    · have h := twoHolePhase_seamModel_one d (0 : Fin 2)
        (C.port (.inr (0 : Fin 2))) (C.matrix (0 : Fin 2)) y
        (-n 0) (-n 1) rfl hp (by rw [hport (0 : Fin 2)]; rfl) h0 h1
      simpa [twoConeTubePhase, t] using h
    · have h := twoHolePhase_seamModel_two d (1 : Fin 2)
        (C.port (.inr (1 : Fin 2))) (C.matrix (1 : Fin 2)) y
        (-n 0) (-n 1) rfl hp (by rw [hport (1 : Fin 2)]; rfl) h0 h1
      simpa [twoConeTubePhase, t, n] using h
  dsimp only
  change ((seamModel d m (C.port (.inr m)) (C.matrix m) y).1,
    (seamModel d m (C.port (.inr m)) (C.matrix m) y).2 *
      twoHolePhase (-n 0) (-n 1) (seamModel d m (C.port (.inr m)) (C.matrix m) y).1) = _
  rw [hphase]
  simp only [seamModel, hp, hps, hport m, twoConeTubeCorrection_norm, hQ]
  change (_, t.2 * ((twoConeTubePhase q₁ q₂ h₁ h₂ m).2 * t.1 ^ n m)) =
    (_, (twoConeTubePhase q₁ q₂ h₁ h₂ m).2 * (t.1 ^ n m * t.2))
  exact Prod.ext rfl (by ac_rfl)


theorem twoConeTubeCorrection_symm_norm (q₁ q₂ : ℤ) (h₁ : Odd q₁) (h₂ : Odd q₂)
    (m : Fin 2) (y : ℂ × Circle) :
    ‖((twoConeTubeCorrection q₁ q₂ h₁ h₂ m).symm y).1‖ = ‖y.1‖ := by
  have h := twoConeTubeCorrection_norm q₁ q₂ h₁ h₂ m
    ((twoConeTubeCorrection q₁ q₂ h₁ h₂ m).symm y)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm

theorem twoConeTubeCorrection_symm_domain {W : CompactCarrier.{u}} (q₁ q₂ : ℤ)
    (h₁ : Odd q₁) (h₂ : Odd q₂) (C : SeifertBlockCharts W (twoConeDatum q₁ q₂ h₁ h₂))
    (m : Fin 2) (y : ℂ × Circle) :
    (twoConeTubeCorrection q₁ q₂ h₁ h₂ m).symm y ∈ C.transitionDomain ↔
      y ∈ C.transitionDomain := by
  rw [C.transitionDomain_eq]
  simp only [Set.mem_ofPred_eq, twoConeTubeCorrection_symm_norm]

theorem twoConeNormalizedSeam_inverse {W : CompactCarrier.{u}} (q₁ q₂ : ℤ)
    (h₁ : Odd q₁) (h₂ : Odd q₂) (C : SeifertBlockCharts W (twoConeDatum q₁ q₂ h₁ h₂))
    (ha : ∀ m, C.a m = 1) (hport : ∀ m, C.port (.inr m) = m.succ) (hε : C.ε ≤ 1 / 8)
    (m : Fin 2) (y : ℂ × Circle) (hy : y ∈ C.transitionDomain) :
    let z := seamModel (twoConeDatum q₁ q₂ h₁ h₂) m (C.port (.inr m)) (C.matrix m)
      ((twoConeTubeCorrection q₁ q₂ h₁ h₂ m).symm y)
    (z.1, z.2 * twoHolePhase (-twoConeSlopeShift q₁ q₂ h₁ h₂ 0)
      (-twoConeSlopeShift q₁ q₂ h₁ h₂ 1) z.1) =
        seamModel twistedIBundleData m m.succ (twoConeStandardMatrix m) y := by
  have hn := twoConeTubeCorrection_symm_norm q₁ q₂ h₁ h₂ m y
  have hd := hy
  rw [C.transitionDomain_eq] at hd
  change 1 < ‖y.1‖ ∧ ‖y.1‖ < 1 + C.ε at hd
  have h0 : 1 ≤ ‖((twoConeTubeCorrection q₁ q₂ h₁ h₂ m).symm y).1‖ ^ 2 := by
    rw [hn]
    nlinarith
  have h1 : ‖((twoConeTubeCorrection q₁ q₂ h₁ h₂ m).symm y).1‖ ^ 2 ≤ 3 / 2 := by
    rw [hn]
    nlinarith [norm_nonneg y.1]
  have h := twoConeNormalizedSeam q₁ q₂ h₁ h₂ C ha hport m
    ((twoConeTubeCorrection q₁ q₂ h₁ h₂ m).symm y) h0 h1
  simpa only [Diffeomorph.apply_symm_apply] using h

theorem twoConeNormalizedDomain {W : CompactCarrier.{u}} (q₁ q₂ : ℤ)
    (h₁ : Odd q₁) (h₂ : Odd q₂) (C : SeifertBlockCharts W (twoConeDatum q₁ q₂ h₁ h₂))
    (ha : ∀ m, C.a m = 1) (hport : ∀ m, C.port (.inr m) = m.succ) (hε : C.ε ≤ 1 / 8)
    (m : Fin 2) (y : ℂ × Circle) (hy : y ∈ C.transitionDomain) :
    (seamModel twistedIBundleData m m.succ (twoConeStandardMatrix m) y).1 ∈ planarOpen 3 := by
  have h := congrArg Prod.fst (twoConeNormalizedSeam_inverse q₁ q₂ h₁ h₂ C ha hport hε m y hy)
  exact h ▸ C.transition_domain m ((twoConeTubeCorrection_symm_domain q₁ q₂ h₁ h₂ C m y).mpr hy)

def twoConeNormalizedTube {W : CompactCarrier.{u}} (q₁ q₂ : ℤ) (h₁ : Odd q₁) (h₂ : Odd q₂)
    (C : SeifertBlockCharts W (twoConeDatum q₁ q₂ h₁ h₂)) (m : Fin 2) :
    PartialDiffeomorph PlaneCircleModel W.model (ℂ × Circle) W.Carrier ∞ :=
  (twoConeTubeCorrection q₁ q₂ h₁ h₂ m).symm.toPartialDiffeomorph.trans (C.tube m)

theorem twoConeNormalizedTube_source {W : CompactCarrier.{u}} (q₁ q₂ : ℤ)
    (h₁ : Odd q₁) (h₂ : Odd q₂) (C : SeifertBlockCharts W (twoConeDatum q₁ q₂ h₁ h₂))
    (m : Fin 2) :
    (twoConeNormalizedTube q₁ q₂ h₁ h₂ C m).source = {y : ℂ × Circle | ‖y.1‖ < 1 + C.ε} := by
  ext y
  change (y ∈ Set.univ ∧ (twoConeTubeCorrection q₁ q₂ h₁ h₂ m).symm y ∈ (C.tube m).source) ↔ _
  rw [C.tube_source m]
  simp only [Set.mem_univ, true_and, Set.mem_ofPred_eq, twoConeTubeCorrection_symm_norm]

theorem twoConeNormalizedTube_target {W : CompactCarrier.{u}} (q₁ q₂ : ℤ)
    (h₁ : Odd q₁) (h₂ : Odd q₂) (C : SeifertBlockCharts W (twoConeDatum q₁ q₂ h₁ h₂))
    (m : Fin 2) : (twoConeNormalizedTube q₁ q₂ h₁ h₂ C m).target = (C.tube m).target := by
  ext x
  change (x ∈ (C.tube m).target ∧ (C.tube m).symm x ∈ Set.univ) ↔ _
  simp only [Set.mem_univ, and_true]

def twoConeNormalizedCharts {W : CompactCarrier.{u}} (q₁ q₂ : ℤ) (h₁ : Odd q₁) (h₂ : Odd q₂)
    (C : SeifertBlockCharts W (twoConeDatum q₁ q₂ h₁ h₂))
    (ha : ∀ m, C.a m = 1) (hport : ∀ m, C.port (.inr m) = m.succ) (hε : C.ε ≤ 1 / 8) :
    SeifertBlockCharts W twistedIBundleData where
  port := C.port
  matrix := twoConeStandardMatrix
  a _ := 1
  b := twoConeStandardBezout
  matrix_eq m := by
    change Fin 2 at m
    rw [twistedIBundleData_fillingSlope]
    rfl
  bezout m := by
    change Fin 2 at m
    rw [twistedIBundleData_fillingSlope]
    fin_cases m <;> norm_num [twoConeStandardSlope, twoConeStandardBezout]
  productRegion := C.productRegion
  productRegion_interior := C.productRegion_interior
  product := (twoHoleOpenShear (-twoConeSlopeShift q₁ q₂ h₁ h₂ 0)
    (-twoConeSlopeShift q₁ q₂ h₁ h₂ 1)).symm.trans C.product
  ε := C.ε
  ε_pos := C.ε_pos
  tube := twoConeNormalizedTube q₁ q₂ h₁ h₂ C
  tube_source := twoConeNormalizedTube_source q₁ q₂ h₁ h₂ C
  tube_interior m := twoConeNormalizedTube_target q₁ q₂ h₁ h₂ C m ▸ C.tube_interior m
  transitionDomain := C.transitionDomain
  transitionDomain_eq := C.transitionDomain_eq
  transition_domain m y hy := by
    change Fin 2 at m
    change (seamModel twistedIBundleData m (C.port (.inr m))
      (twoConeStandardMatrix m) y).1 ∈ planarOpen 3
    rw [hport m]
    exact twoConeNormalizedDomain q₁ q₂ h₁ h₂ C ha hport hε m y hy
  transition m y hy := by
    change Fin 2 at m
    let Q := twoConeTubeCorrection q₁ q₂ h₁ h₂ m
    let R := twoHoleOpenShear (-twoConeSlopeShift q₁ q₂ h₁ h₂ 0)
      (-twoConeSlopeShift q₁ q₂ h₁ h₂ 1)
    have hold := C.transition m (Q.symm y)
      ((twoConeTubeCorrection_symm_domain q₁ q₂ h₁ h₂ C m y).mpr hy)
    have he := twoConeNormalizedSeam_inverse q₁ q₂ h₁ h₂ C ha hport hε m y hy
    change C.tube m (Q.symm y) = (C.product (R.symm _)).val
    rw [hold]
    apply congrArg (fun z => (C.product z).val)
    apply (R.symm_apply_apply _).symm.trans
    apply congrArg R.symm
    apply Prod.ext
    · apply Subtype.ext
      change (seamModel (twoConeDatum q₁ q₂ h₁ h₂) m (C.port (.inr m))
        (C.matrix m) (Q.symm y)).1 =
          (seamModel twistedIBundleData m (C.port (.inr m)) (twoConeStandardMatrix m) y).1
      simpa only [hport m] using congrArg (fun z : ℂ × Circle => z.1) he
    · change (seamModel (twoConeDatum q₁ q₂ h₁ h₂) m (C.port (.inr m))
        (C.matrix m) (Q.symm y)).2 * twoHolePhase (-twoConeSlopeShift q₁ q₂ h₁ h₂ 0)
        (-twoConeSlopeShift q₁ q₂ h₁ h₂ 1)
          (seamModel (twoConeDatum q₁ q₂ h₁ h₂) m (C.port (.inr m))
            (C.matrix m) (Q.symm y)).1 =
              (seamModel twistedIBundleData m (C.port (.inr m)) (twoConeStandardMatrix m) y).2
      simpa only [hport m] using congrArg (fun z : ℂ × Circle => z.2) he
  tube_product_overlap m := by
    change Fin 2 at m
    rw [twoConeNormalizedTube_target, C.tube_product_overlap m]
    ext x
    constructor
    · rintro ⟨y, hy, hx⟩
      let Q := twoConeTubeCorrection q₁ q₂ h₁ h₂ m
      refine ⟨Q y, ?_, ?_⟩
      · have h := twoConeTubeCorrection_symm_domain q₁ q₂ h₁ h₂ C m (Q y)
        rw [Q.symm_apply_apply] at h
        exact h.mp hy
      · change C.tube m (Q.symm (Q y)) = x
        rw [Q.symm_apply_apply]
        exact hx
    · rintro ⟨y, hy, hx⟩
      exact ⟨(twoConeTubeCorrection q₁ q₂ h₁ h₂ m).symm y,
        (twoConeTubeCorrection_symm_domain q₁ q₂ h₁ h₂ C m y).mpr hy, hx⟩
  disjoint m l h := by
    change Fin 2 at m l
    rw [twoConeNormalizedTube_target, twoConeNormalizedTube_target]
    exact C.disjoint h
  covers x hx := by
    rcases C.covers x hx with hp | ⟨m, hm⟩
    · exact Or.inl hp
    · exact Or.inr ⟨m, twoConeNormalizedTube_target q₁ q₂ h₁ h₂ C m ▸ hm⟩


theorem exists_twoConeNormalizedCharts {W : CompactCarrier.{u}} (q₁ q₂ : ℤ)
    (h₁ : Odd q₁) (h₂ : Odd q₂) (C : SeifertBlockCharts W (twoConeDatum q₁ q₂ h₁ h₂)) :
    Nonempty (SeifertBlockCharts W twistedIBundleData) := by
  let π : Fin 1 ⊕ Fin 2 ≃ Fin 3 := finSumFinEquiv
  let ρ : Fin 3 ≃ Fin 3 := C.port.symm.trans π
  obtain ⟨D, hD, _⟩ := C.exists_pantsReindexedCharts rfl ρ
  have hp (m : Fin 2) : ((twoConeDatum q₁ q₂ h₁ h₂).fillingSlope m).1 = 2 := by
    rw [twoConeDatum_fillingSlope]
  have hportD : ∀ m : Fin 2, D.port (.inr m) = m.succ := by
    intro m
    rw [hD]
    change π (C.port.symm (C.port (.inr m))) = m.succ
    rw [C.port.symm_apply_apply]
    exact Fin.ext (by simp [π, finSumFinEquiv]; omega)
  let K := D.canonicalTwoConeCharts hp
  let η := min K.ε (1 / 8)
  have hη : 0 < η := lt_min K.ε_pos (by norm_num)
  let L := K.shrinkTubeWidth hη (min_le_left _ _)
  have hLa : ∀ m : Fin 2, L.a m = 1 := D.canonicalTwoConeCharts_a hp
  have hLp : ∀ m : Fin 2, L.port (.inr m) = m.succ := hportD
  have hLε : L.ε ≤ 1 / 8 := min_le_right _ _
  exact ⟨twoConeNormalizedCharts q₁ q₂ h₁ h₂ L hLa hLp hLε⟩

theorem exists_twistedIBundleCharts {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (q₁ q₂ : ℤ)
    (hports : d.ports = 1) (hcones : d.cones = [(2, q₁), (2, q₂)]) :
    Nonempty (SeifertBlockCharts W twistedIBundleData) := by
  have hd := twoConeData_eq q₁ q₂ hports hcones
  exact exists_twoConeNormalizedCharts q₁ q₂ _ _ (hd ▸ C)


variable {W : CompactCarrier.{u}}

theorem exists_standardTwistedPortCharts (C : SeifertBlockCharts W twistedIBundleData) :
    ∃ D : SeifertBlockCharts W twistedIBundleData,
      D.port = (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3) := by
  let ρ : Fin 3 ≃ Fin 3 := C.port.symm.trans finSumFinEquiv
  obtain ⟨D, hD, hmatrix⟩ := C.exists_pantsReindexedCharts rfl ρ
  refine ⟨D, hD.trans ?_⟩
  apply Equiv.ext
  intro x
  change finSumFinEquiv (C.port.symm (C.port x)) = finSumFinEquiv x
  rw [C.port.symm_apply_apply]

theorem twistedIBundleData_fillingSlope_fst_two
    (m : Fin twistedIBundleData.fillingCount) : (twistedIBundleData.fillingSlope m).1 = 2 := by
  change Fin 2 at m
  fin_cases m <;> rfl

def standardTwistedIBundleInteriorDiffeomorph
    (C : SeifertBlockCharts W twistedIBundleData) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, mobiusBundleCarrier.{u}.model⟯
      mobiusBundleCarrier.{u}.pieceInterior ⊤ := by
  let C' := Classical.choose (exists_standardTwistedPortCharts C)
  let D' := Classical.choose (exists_standardTwistedPortCharts twistedStandardCharts.{u})
  have hC : C'.port = (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3) :=
    Classical.choose_spec (exists_standardTwistedPortCharts C)
  have hD : D'.port = (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3) :=
    Classical.choose_spec (exists_standardTwistedPortCharts twistedStandardCharts.{u})
  let hp := twistedIBundleData_fillingSlope_fst_two
  let C'' := C'.canonicalTwoConeCharts hp
  let D'' := D'.canonicalTwoConeCharts hp
  have hport : C''.port = D''.port := hC.trans hD.symm
  exact C''.compareInterior D'' hport (C'.canonicalTwoConeCharts_matrix D' hp)


def twistedIBundleInteriorDiffeomorph {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (q₁ q₂ : ℤ)
    (hports : d.ports = 1) (hcones : d.cones = [(2, q₁), (2, q₂)]) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, mobiusBundleCarrier.{u}.model⟯
      mobiusBundleCarrier.{u}.pieceInterior ⊤ :=
  standardTwistedIBundleInteriorDiffeomorph
    (Classical.choice (exists_twistedIBundleCharts C q₁ q₂ hports hcones))

def twistedIBundleInteriorGeometry {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (q₁ q₂ : ℤ)
    (hports : d.ports = 1) (hcones : d.cones = [(2, q₁), (2, q₂)]) :
    W.InteriorGeometry ⊤ :=
  transportInteriorGeometry (twistedIBundleInteriorDiffeomorph C q₁ q₂ hports hcones)
    GC.Geometry.mobiusBundle_interiorGeometry.{u}

theorem twistedIBundleInteriorGeometry_model {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (q₁ q₂ : ℤ)
    (hports : d.ports = 1) (hcones : d.cones = [(2, q₁), (2, q₂)]) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (twistedIBundleInteriorGeometry C q₁ q₂ hports hcones).model = ThurstonModel.euclidean := rfl

def SeifertBlock.twistedIBundleInteriorGeometry {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (hT : TorusMappingClassLinear) (q₁ q₂ : ℤ)
    (hports : d.ports = 1) (hcones : d.cones = [(2, q₁), (2, q₂)]) :
    W.InteriorGeometry ⊤ :=
  GC.Seifert.twistedIBundleInteriorGeometry (Classical.choice (B.exists_charts hT))
    q₁ q₂ hports hcones

theorem SeifertBlock.twistedIBundleInteriorGeometry_model
    {W : CompactCarrier.{u}} {d : SeifertData} (B : SeifertBlock W d)
    (hT : TorusMappingClassLinear) (q₁ q₂ : ℤ)
    (hports : d.ports = 1) (hcones : d.cones = [(2, q₁), (2, q₂)]) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (B.twistedIBundleInteriorGeometry hT q₁ q₂ hports hcones).model =
      ThurstonModel.euclidean := rfl

end GC.Seifert
