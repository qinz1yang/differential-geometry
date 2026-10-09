import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MergedSolidTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPants
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusBlockAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LinearSeams
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.UnionGeometry
import DifferentialGeometry.Topology.Manifold.ImmersionInterior
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Interior
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
/-!
# Marked Seifert block charts and solid-torus basis normalization
Charts record the product region, shrunk radial transition annuli, uniform tube width,
coverage and disjointness. Basis changes extend smoothly across the solid-torus core.
-/
set_option autoImplicit false
noncomputable section
open Set Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ComplexConjugate
universe u

namespace GC.Seifert

def chartSign (s : Bool) : ℤ := if s then -1 else 1

def chartPlaneFlip (s : Bool) (z : ℂ) : ℂ := if s then conj z else z

def chartCircleFlip (s : Bool) (w : Circle) : Circle := if s then w⁻¹ else w

theorem chartPlaneFlip_involutive (s : Bool) : Function.Involutive (chartPlaneFlip s) := by
  cases s <;> intro z <;> simp [chartPlaneFlip]

theorem chartCircleFlip_involutive (s : Bool) : Function.Involutive (chartCircleFlip s) := by
  cases s <;> intro w <;> simp [chartCircleFlip]

theorem contMDiff_chartPlaneFlip (s : Bool) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartPlaneFlip s) := by
  cases s
  · exact contMDiff_id
  · exact Complex.conjCLE.contDiff.contMDiff

theorem contMDiff_chartCircleFlip (s : Bool) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (chartCircleFlip s) := by
  cases s
  · exact contMDiff_id
  · exact contMDiff_id.inv

theorem chartContMDiffComplexMul :
    ContMDiff 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ) ∞ (fun y : ℂ × ℂ => y.1 * y.2) :=
  (contDiff_fst.mul contDiff_snd).contMDiff

def solidBasisExtension (s t : Bool) (n : ℤ) :
    (ℂ × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯ (ℂ × Circle) where
  toFun x := (chartPlaneFlip s x.1 * ((x.2 ^ n : Circle) : ℂ), chartCircleFlip t x.2)
  invFun y :=
    (chartPlaneFlip s (y.1 * ((chartCircleFlip t y.2 ^ (-n) : Circle) : ℂ)),
      chartCircleFlip t y.2)
  left_inv x := by
    change (chartPlaneFlip s (chartPlaneFlip s x.1 * ((x.2 ^ n : Circle) : ℂ) *
      ((chartCircleFlip t (chartCircleFlip t x.2) ^ (-n) : Circle) : ℂ)),
      chartCircleFlip t (chartCircleFlip t x.2)) = x
    rw [chartCircleFlip_involutive t x.2]
    rw [mul_assoc, ← Circle.coe_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Circle.coe_one, mul_one, chartPlaneFlip_involutive]
  right_inv y := by
    change (chartPlaneFlip s (chartPlaneFlip s (y.1 *
      ((chartCircleFlip t y.2 ^ (-n) : Circle) : ℂ))) *
      ((chartCircleFlip t y.2 ^ n : Circle) : ℂ),
      chartCircleFlip t (chartCircleFlip t y.2)) = y
    rw [chartPlaneFlip_involutive s, chartCircleFlip_involutive t]
    rw [mul_assoc, ← Circle.coe_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Circle.coe_one, mul_one]
  contMDiff_toFun :=
    (chartContMDiffComplexMul.comp
      (((contMDiff_chartPlaneFlip s).comp contMDiff_fst).prodMk_space
        (contMDiff_circle_coe.comp ((contMDiff_circle_zpow n).comp contMDiff_snd)))).prodMk
      ((contMDiff_chartCircleFlip t).comp contMDiff_snd)
  contMDiff_invFun :=
    ((contMDiff_chartPlaneFlip s).comp (chartContMDiffComplexMul.comp
      (contMDiff_fst.prodMk_space
        (contMDiff_circle_coe.comp ((contMDiff_circle_zpow (-n)).comp
          ((contMDiff_chartCircleFlip t).comp contMDiff_snd)))))).prodMk
          ((contMDiff_chartCircleFlip t).comp contMDiff_snd)

theorem solidBasisExtension_norm (s t : Bool) (n : ℤ) (x : ℂ × Circle) :
    ‖(solidBasisExtension s t n x).1‖ = ‖x.1‖ := by
  change ‖chartPlaneFlip s x.1 * ((x.2 ^ n : Circle) : ℂ)‖ = ‖x.1‖
  cases s <;> simp [chartPlaneFlip]

theorem solidBasisExtension_boundary (s t : Bool) (n : ℤ) (x : Torus) :
    solidBasisExtension s t n ((x.1 : ℂ), x.2) =
      (((linearTorusMap !![chartSign s, n; 0, chartSign t] x).1 : ℂ),
        (linearTorusMap !![chartSign s, n; 0, chartSign t] x).2) := by
  change (chartPlaneFlip s (x.1 : ℂ) * ((x.2 ^ n : Circle) : ℂ),
    chartCircleFlip t x.2) = _
  have hc : conj (x.1 : ℂ) = (x.1 : ℂ)⁻¹ := by
    rw [← Circle.coe_inv_eq_conj, Circle.coe_inv]
  cases s
  · cases t <;> simp [chartPlaneFlip, chartCircleFlip, chartSign, linearTorusMap]
  · cases t <;> simp [chartPlaneFlip, chartCircleFlip, chartSign, linearTorusMap, hc]

end GC.Seifert

namespace GC.Seifert

def planarOpen (k : ℕ) : TopologicalSpace.Opens ℂ :=
  ⟨interior (planarModel k), isOpen_interior⟩

def seamModel (d : SeifertData) (m : Fin d.fillingCount) (j : Fin d.k)
    (A : GL (Fin 2) ℤ) (y : ℂ × Circle) : ℂ × Circle :=
  let t := linearTorusMap A (unitOf y.1, y.2)
  let r := planarRadius j + (if j.val = 0 then -1 else 1) *
    (‖y.1‖ ^ (d.fillingSlope m).1.natAbs - 1) / 2
  (planarCenter d.k j + r * (if j.val = 0 then (t.1 : ℂ) else conj (t.1 : ℂ)), t.2)

structure SeifertBlockCharts (W : CompactCarrier.{u}) (d : SeifertData) where
  port : Fin d.ports ⊕ Fin d.fillingCount ≃ Fin d.k
  matrix : Fin d.fillingCount → GL (Fin 2) ℤ
  a : Fin d.fillingCount → ℤ
  b : Fin d.fillingCount → ℤ
  matrix_eq : ∀ m, (matrix m : Matrix (Fin 2) (Fin 2) ℤ) =
    !![-(d.fillingSlope m).1, a m; -(d.fillingSlope m).2, b m]
  bezout : ∀ m, (d.fillingSlope m).1 * b m - a m * (d.fillingSlope m).2 = 1
  productRegion : TopologicalSpace.Opens W.Carrier
  productRegion_interior : (productRegion : Set W.Carrier) ⊆ W.interior
  product : (planarOpen d.k × Circle) ≃ₘ⟮PlaneCircleModel, W.model⟯ productRegion
  ε : ℝ
  ε_pos : 0 < ε
  tube : Fin d.fillingCount →
    PartialDiffeomorph PlaneCircleModel W.model (ℂ × Circle) W.Carrier ∞
  tube_source : ∀ m, (tube m).source = {y : ℂ × Circle | ‖y.1‖ < 1 + ε}
  tube_interior : ∀ m, (tube m).target ⊆ W.interior
  transitionDomain : Set (ℂ × Circle)
  transitionDomain_eq : transitionDomain = {y | 1 < ‖y.1‖ ∧ ‖y.1‖ < 1 + ε}
  transition_domain : ∀ m, MapsTo (seamModel d m (port (.inr m)) (matrix m))
    transitionDomain {z | z.1 ∈ planarOpen d.k}
  transition : ∀ m y (hy : y ∈ transitionDomain), tube m y =
    (product (⟨(seamModel d m (port (.inr m)) (matrix m) y).1,
      transition_domain m hy⟩, (seamModel d m (port (.inr m)) (matrix m) y).2) : W.Carrier)
  tube_product_overlap : ∀ m, (tube m).target ∩ (productRegion : Set W.Carrier) =
    tube m '' transitionDomain
  disjoint : Pairwise fun m n => Disjoint (tube m).target (tube n).target
  covers : ∀ x ∈ W.interior, x ∈ productRegion ∨ ∃ m, x ∈ (tube m).target

def chartConventionMatrix (p q a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-p, a; -q, b]

def chartConventionUnit (p q a b : ℤ) (h : p * b - a * q = 1) : GL (Fin 2) ℤ :=
  PrimitiveSlope.unitOfDet (chartConventionMatrix p q a b) (Or.inr (by
    simp only [chartConventionMatrix, Matrix.det_fin_two_of]
    linarith))

def normalizingBasis (A : GL (Fin 2) ℤ) (p q a b : ℤ) (h : p * b - a * q = 1) :
    GL (Fin 2) ℤ := A⁻¹ * chartConventionUnit p q a b h

theorem normalizingBasis_matrix (A : GL (Fin 2) ℤ) (p q a b : ℤ)
    (h : p * b - a * q = 1) :
    ((A * normalizingBasis A p q a b h : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      chartConventionMatrix p q a b := by
  simp [normalizingBasis, chartConventionUnit, PrimitiveSlope.val_unitOfDet]

theorem normalizingBasis_firstColumn (A : GL (Fin 2) ℤ) (p q a b : ℤ)
    (h : p * b - a * q = 1)
    (hcol : (A 0 0, A 1 0) = (p, q) ∨ (A 0 0, A 1 0) = -(p, q)) :
    let C := normalizingBasis A p q a b h
    (C 0 0 = 1 ∨ C 0 0 = -1) ∧ C 1 0 = 0 := by
  have hi : ((A⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * A = 1 := Units.inv_mul A
  have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hi
  have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hi
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Fin.reduceEq,
    ite_true, ite_false] at h0 h1
  dsimp only
  rcases hcol with hc | hc
  · have hc0 := congrArg Prod.fst hc
    have hc1 := congrArg Prod.snd hc
    dsimp only at hc0 hc1
    rw [hc0, hc1] at h0 h1
    refine ⟨Or.inr ?_, ?_⟩ <;>
      simp only [normalizingBasis, Units.val_mul, chartConventionUnit, PrimitiveSlope.val_unitOfDet,
        chartConventionMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.of_apply,
        Matrix.empty_val', Matrix.cons_val']
    · linear_combination -h0
    · linear_combination -h1
  · have hc0 := congrArg Prod.fst hc
    have hc1 := congrArg Prod.snd hc
    dsimp only [Prod.fst_neg, Prod.snd_neg] at hc0 hc1
    rw [hc0, hc1] at h0 h1
    refine ⟨Or.inl ?_, ?_⟩ <;>
      simp only [normalizingBasis, Units.val_mul, chartConventionUnit, PrimitiveSlope.val_unitOfDet,
        chartConventionMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.of_apply,
        Matrix.empty_val', Matrix.cons_val']
    · exact h0
    · exact h1

def SeifertBlock.chartsUnfilledInteriorDiffeomorph {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (h : d.fillingCount = 0) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, B.presentation.cutCarrier.model⟯
      B.presentation.cutCarrier.pieceInterior (B.presentation.components.piece (B.piece none)) :=
  (B.unfilledInteriorDiffeomorph h).symm

def chartPlaneCircleLift :
    (PlaneLift.{u} × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯ (ℂ × Circle) where
  toFun x := (x.1.down, x.2)
  invFun y := (ULift.up y.1, y.2)
  left_inv x := Prod.ext (ULift.ext rfl) (Eq.refl x.2)
  right_inv y := Prod.ext (Eq.refl y.1) (Eq.refl y.2)
  contMDiff_toFun := (contMDiff_planeLift_down.comp contMDiff_fst).prodMk contMDiff_snd
  contMDiff_invFun := (contMDiff_planeLift_up.comp contMDiff_fst).prodMk contMDiff_snd

def solidBasisLift (s t : Bool) (n : ℤ) :
    (PlaneLift.{u} × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯
      (PlaneLift.{u} × Circle) :=
  chartPlaneCircleLift.trans ((solidBasisExtension s t n).trans chartPlaneCircleLift.symm)

theorem solidBasisLift_norm (s t : Bool) (n : ℤ) (x : PlaneLift.{u} × Circle) :
    ‖(solidBasisLift s t n x).1.down‖ = ‖x.1.down‖ :=
  solidBasisExtension_norm s t n (x.1.down, x.2)

theorem solidBasisLift_mem (s t : Bool) (n : ℤ) (x : PlaneLift.{u} × Circle) :
    solidBasisLift s t n x ∈ solidSet ↔ x ∈ solidSet := by
  rw [mem_solidSet_iff, mem_solidSet_iff, solidBasisLift_norm]

def solidBasisExtensionClosed (s t : Bool) (n : ℤ) :
    solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u} where
  toFun x := ⟨solidBasisLift s t n x.val, (solidBasisLift_mem s t n x.val).mpr x.property⟩
  invFun y := ⟨(solidBasisLift s t n).symm y.val, by
    apply (solidBasisLift_mem s t n ((solidBasisLift s t n).symm y.val)).mp
    rw [Diffeomorph.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext ((solidBasisLift s t n).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((solidBasisLift s t n).apply_symm_apply y.val)
  contMDiff_toFun := (solidAtlas.contMDiff_iff_subtype_val _).mpr
    ((solidBasisLift s t n).contMDiff.comp solidAtlas.contMDiff_subtype_val)
  contMDiff_invFun := (solidAtlas.contMDiff_iff_subtype_val _).mpr
    ((solidBasisLift s t n).symm.contMDiff.comp solidAtlas.contMDiff_subtype_val)

theorem solidBasisLift_boundary (s t : Bool) (n : ℤ) (x : Torus) :
    solidBasisLift s t n ((ULift.up (3 * (x.1 : ℂ)) : PlaneLift.{u}), x.2) =
      (ULift.up (3 * ((linearTorusMap !![chartSign s, n; 0, chartSign t] x).1 : ℂ)),
        (linearTorusMap !![chartSign s, n; 0, chartSign t] x).2) := by
  have hc : conj (x.1 : ℂ) = (x.1 : ℂ)⁻¹ := by
    rw [← Circle.coe_inv_eq_conj, Circle.coe_inv]
  change (ULift.up (chartPlaneFlip s (3 * (x.1 : ℂ)) * ((x.2 ^ n : Circle) : ℂ)),
    chartCircleFlip t x.2) = _
  cases s
  · cases t <;> simp [chartPlaneFlip, chartCircleFlip, chartSign, linearTorusMap, mul_assoc]
  · cases t <;>
      simp [chartPlaneFlip, chartCircleFlip, chartSign, linearTorusMap, mul_assoc, hc, map_ofNat]

theorem triangularBasis_signs (C : GL (Fin 2) ℤ)
    (h0 : C 0 0 = 1 ∨ C 0 0 = -1) (h10 : C 1 0 = 0) :
    ∃ s t : Bool, (C : Matrix (Fin 2) (Fin 2) ℤ) = !![chartSign s, C 0 1; 0, chartSign t] := by
  have hd := Int.isUnit_iff.mp (Matrix.isUnits_det_units C)
  have h1 : C 1 1 = 1 ∨ C 1 1 = -1 := by
    rcases h0 with h0 | h0 <;> rcases hd with hd | hd <;>
      simp only [Matrix.det_fin_two, h0, h10, mul_zero, sub_zero,
        one_mul, neg_one_mul] at hd
    · exact Or.inl hd
    · exact Or.inr hd
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · refine ⟨false, false, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chartSign, h0, h1, h10]
  · refine ⟨false, true, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chartSign, h0, h1, h10]
  · refine ⟨true, false, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chartSign, h0, h1, h10]
  · refine ⟨true, true, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chartSign, h0, h1, h10]

def chartSolidBoundary (x : Torus) : solidSet.{u} :=
  ⟨(ULift.up (3 * (x.1 : ℂ)), x.2), by
    rw [mem_solidSet_iff]
    simp⟩

theorem solidBasisExtensionClosed_boundary (s t : Bool) (n : ℤ) (x : Torus) :
    solidBasisExtensionClosed s t n (chartSolidBoundary x) =
      chartSolidBoundary (linearTorusMap !![chartSign s, n; 0, chartSign t] x) :=
  Subtype.ext (solidBasisLift_boundary s t n x)

theorem exists_solidBasis_normalization (A : GL (Fin 2) ℤ) (p q a b : ℤ)
    (h : p * b - a * q = 1)
    (hcol : (A 0 0, A 1 0) = (p, q) ∨ (A 0 0, A 1 0) = -(p, q)) :
    ∃ (C : GL (Fin 2) ℤ) (Φ : solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u}),
      ((A * C : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![-p, a; -q, b] ∧
      ∀ x : Torus, Φ (chartSolidBoundary x) = chartSolidBoundary (linearTorusMap C x) := by
  let C := normalizingBasis A p q a b h
  obtain ⟨h0, h10⟩ := normalizingBasis_firstColumn A p q a b h hcol
  obtain ⟨s, t, hC⟩ := triangularBasis_signs C h0 h10
  refine ⟨C, solidBasisExtensionClosed s t (C 0 1),
    normalizingBasis_matrix A p q a b h, fun x => ?_⟩
  rw [hC]
  exact solidBasisExtensionClosed_boundary s t (C 0 1) x

theorem SeifertData.exists_chartBezout (d : SeifertData) (m : Fin d.fillingCount) :
    ∃ a b : ℤ, (d.fillingSlope m).1 * b - a * (d.fillingSlope m).2 = 1 := by
  have h := d.isPrimitive_fillingSlope m
  rw [IsPrimitive, ← Int.isCoprime_iff_gcd_eq_one] at h
  obtain ⟨b, v, hv⟩ := h
  exact ⟨-v, b, by linear_combination hv⟩

theorem SeifertBlock.exists_normalized_fillingMatrix {W : CompactCarrier.{u}}
    {d : SeifertData} (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    ∃ (a b : ℤ) (C : GL (Fin 2) ℤ)
      (Φ : solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u}),
      (d.fillingSlope m).1 * b - a * (d.fillingSlope m).2 = 1 ∧
      ((torusUnit (B.presentation.pairing.matching (B.seam m)) * C : GL (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) =
          !![-(d.fillingSlope m).1, a; -(d.fillingSlope m).2, b] ∧
      ∀ x : Torus, Φ (chartSolidBoundary x) = chartSolidBoundary (linearTorusMap C x) := by
  obtain ⟨a, b, h⟩ := d.exists_chartBezout m
  obtain ⟨C, Φ, hC, hΦ⟩ := exists_solidBasis_normalization
    (torusUnit (B.presentation.pairing.matching (B.seam m)))
    (d.fillingSlope m).1 (d.fillingSlope m).2 a b h (B.torusMatrix_meridian m)
  exact ⟨a, b, C, Φ, h, hC, hΦ⟩

def chartBaseInterior {k : ℕ} (P : PlanarBase.{u} k) :
    TopologicalSpace.Opens P.surface.Carrier :=
  ⟨(SurfaceModel.model P.surface.kind).interior P.surface.Carrier,
    (SurfaceModel.model P.surface.kind).isOpen_interior (n := ∞) (by simp)⟩

theorem chartBaseInterior_local {k : ℕ} (P : PlanarBase.{u} k) :
    IsLocalDiffeomorph (SurfaceModel.model P.surface.kind) 𝓘(ℝ, ℂ) ∞
      (fun x : chartBaseInterior P => P.embedding x.val) := by
  apply isLocalDiffeomorph_restrict_open
  intro x
  exact isLocalDiffeomorphAt_of_isInteriorPoint_of_isImmersion
    P.isSmoothEmbedding.isImmersion x.property
    (by rw [finrank_euclideanSpace_fin, Complex.finrank_real_complex])

theorem chartPlanarInterior_lt {k : ℕ} {z : ℂ} (hz : z ∈ interior (planarModel k)) :
    ‖z‖ < 3 := by
  have hs : planarModel k ⊆ closedBall 0 3 := fun z hz => by
    simpa only [mem_closedBall, dist_zero_right] using hz.1
  have hi := interior_mono hs hz
  rw [interior_closedBall 0 (by norm_num : (3 : ℝ) ≠ 0)] at hi
  simpa only [mem_ball, dist_zero_right] using hi

theorem chartPlanarInterior_hole_lt {k : ℕ} {z : ℂ}
    (hz : z ∈ interior (planarModel k)) (j : Fin k) (hj : j.val ≠ 0) :
    1 / 2 < ‖z - planarCenter k j‖ := by
  have hs : planarModel k ⊆ (ball (planarCenter k j : ℂ) (1 / 2))ᶜ := by
    intro x hx
    simp only [mem_compl_iff, mem_ball, dist_eq_norm]
    exact not_lt.mpr (hx.2 j hj)
  have hi := interior_mono hs hz
  rw [interior_compl, closure_ball (planarCenter k j : ℂ)
    (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hi
  simpa only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] using hi

theorem chartPlanarCircle_not_mem_interior {k : ℕ} (j : Fin k) (t : Circle) :
    planarCircleMap k j t ∉ interior (planarModel k) := by
  intro hz
  have hn := norm_planarCircleMap_sub k j t
  by_cases hj : j.val = 0
  · have hc : planarCenter k j = 0 := by simp [planarCenter, hj]
    rw [hc, Complex.ofReal_zero, sub_zero] at hn
    simp only [planarRadius, hj, ite_true] at hn
    have ht := chartPlanarInterior_lt hz
    linarith
  · have ht := chartPlanarInterior_hole_lt hz j hj
    simp only [planarRadius, hj, ite_false] at hn
    linarith

theorem chartBaseInterior_range {k : ℕ} (P : PlanarBase.{u} k) :
    range (fun x : chartBaseInterior P => P.embedding x.val) = interior (planarModel k) := by
  have ho : IsOpen (range (fun x : chartBaseInterior P => P.embedding x.val)) :=
    (chartBaseInterior_local P).isOpenMap.isOpen_range
  have hs : range (fun x : chartBaseInterior P => P.embedding x.val) ⊆ planarModel k := by
    rintro z ⟨x, rfl⟩
    rw [← P.range_embedding]
    exact mem_range_self x.val
  ext z
  constructor
  · intro hz
    exact interior_mono hs (mem_interior_iff_mem_nhds.mpr (ho.mem_nhds hz))
  · intro hz
    have hz' := interior_subset hz
    rw [← P.range_embedding] at hz'
    obtain ⟨x, rfl⟩ := hz'
    have hx : (SurfaceModel.model P.surface.kind).IsInteriorPoint x := by
      rcases (SurfaceModel.model P.surface.kind).isInteriorPoint_or_isBoundaryPoint x with hx | hx
      · exact hx
      · change x ∈ (SurfaceModel.model P.surface.kind).boundary P.surface.Carrier at hx
        rw [P.boundary_exhausted] at hx
        obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        obtain ⟨t, rfl⟩ := hj
        rw [P.embedding_collar] at hz
        exact False.elim (chartPlanarCircle_not_mem_interior j t hz)
    exact ⟨⟨x, hx⟩, rfl⟩

def PlanarBase.chartInteriorDiffeomorph {k : ℕ} (P : PlanarBase.{u} k) :
    chartBaseInterior P ≃ₘ⟮SurfaceModel.model P.surface.kind, 𝓘(ℝ, ℂ)⟯ planarOpen k := by
  let U := (chartBaseInterior_local P).image
  let e := diffeomorphOntoImage (fun x : chartBaseInterior P => P.embedding x.val)
    (chartBaseInterior_local P)
    (fun x y h => Subtype.ext (P.isSmoothEmbedding.isEmbedding.injective h))
  have he : (U : Set ℂ) = planarOpen k := chartBaseInterior_range P
  let f : U → planarOpen k := fun x => ⟨x.val, by
    change x.val ∈ (planarOpen k : Set ℂ)
    rw [← he]
    exact x.property⟩
  let g : planarOpen k → U := fun x => ⟨x.val, by
    change x.val ∈ (U : Set ℂ)
    rw [he]
    exact x.property⟩
  refine
    { toFun := fun x => f (e x)
      invFun := fun y => e.symm (g y)
      left_inv := ?_
      right_inv := ?_
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · intro x
    exact e.symm_apply_apply x
  · intro y
    apply Subtype.ext
    change (e (e.symm (g y))).val = y.val
    exact congrArg Subtype.val (e.apply_symm_apply (g y))
  · apply (ContMDiff.subtypeVal_comp_iff (planarOpen k) _).mp
    change ContMDiff (SurfaceModel.model P.surface.kind) 𝓘(ℝ, ℂ) ∞
      (fun x : chartBaseInterior P => (e x).val)
    exact contMDiff_subtype_val.comp e.contMDiff
  · apply e.symm.contMDiff.comp
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact contMDiff_subtype_val

theorem chartBaseProduct_interior {k : ℕ} (P : PlanarBase.{u} k)
    (x : chartBaseInterior P × Circle) :
    ((SurfaceModel.model P.surface.kind).prod (𝓡 1)).IsInteriorPoint (x.1.val, x.2) := by
  have h0 := isLocalDiffeomorphAt_of_isInteriorPoint_of_isImmersion
    P.isSmoothEmbedding.isImmersion x.1.property
    (by rw [finrank_euclideanSpace_fin, Complex.finrank_real_complex])
  have h1 := (Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph x.2
  exact ((h0.prodMap h1).isInteriorPoint_iff (by simp)).mpr
    BoundarylessManifold.isInteriorPoint

theorem chartBaseProduct_fst_interior {k : ℕ} (P : PlanarBase.{u} k)
    (x : P.surface.Carrier × Circle)
    (hx : ((SurfaceModel.model P.surface.kind).prod (𝓡 1)).IsInteriorPoint x) :
    (SurfaceModel.model P.surface.kind).IsInteriorPoint x.1 := by
  have hd : MDifferentiableAt ((SurfaceModel.model P.surface.kind).prod (𝓡 1))
      (SurfaceModel.model P.surface.kind) Prod.fst x := mdifferentiableAt_fst
  apply hd.isInteriorPoint_of_surjective_mfderiv ?_ hx
  rw [mfderiv_fst]
  intro v
  exact ⟨(v, 0), rfl⟩

def ProductFibredPiece.chartPieceInteriorDiffeomorph {W : CompactCarrier.{u}}
    {T : TorusPresentation W} {i : Fin T.components.count} {k : ℕ}
    (P : ProductFibredPiece T i k) :
    (planarOpen k × Circle) ≃ₘ⟮PlaneCircleModel, T.cutCarrier.model⟯
      T.cutCarrier.pieceInterior (T.components.piece i) := by
  let f := fun x : chartBaseInterior P.base × Circle =>
    P.trivialization (x.1.val, x.2)
  have hf : ∀ x : chartBaseInterior P.base × Circle,
      T.cutCarrier.model.IsInteriorPoint (f x : T.cutCarrier.Carrier) := by
    intro x
    have hi := (P.trivialization.isLocalDiffeomorph (x.1.val, x.2)).isInteriorPoint_iff
      (by simp)
    exact ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mp
      (hi.mp (chartBaseProduct_interior P.base x))
  let e : (chartBaseInterior P.base × Circle) ≃ₘ⟮
      (SurfaceModel.model P.base.surface.kind).prod (𝓡 1), T.cutCarrier.model⟯
      T.cutCarrier.pieceInterior (T.components.piece i) :=
    { toFun := fun x => ⟨(f x).val, (f x).property, hf x⟩
      invFun := fun y =>
        let z := P.trivialization.symm ⟨y.val, y.property.1⟩
        (⟨z.1, chartBaseProduct_fst_interior P.base z (by
          have hi := (P.trivialization.symm.isLocalDiffeomorph
            ⟨y.val, y.property.1⟩).isInteriorPoint_iff (by simp)
          exact hi.mp (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mpr
            y.property.2))⟩, z.2)
      left_inv := fun x => by
        apply Prod.ext
        · apply Subtype.ext
          change (P.trivialization.symm (P.trivialization (x.1.val, x.2))).1 = x.1.val
          exact congrArg Prod.fst (P.trivialization.symm_apply_apply (x.1.val, x.2))
        · change (P.trivialization.symm (P.trivialization (x.1.val, x.2))).2 = x.2
          exact congrArg Prod.snd (P.trivialization.symm_apply_apply (x.1.val, x.2))
      right_inv := fun y => by
        apply Subtype.ext
        change (P.trivialization (P.trivialization.symm ⟨y.val, y.property.1⟩)).val = y.val
        exact congrArg Subtype.val
          (P.trivialization.apply_symm_apply ⟨y.val, y.property.1⟩)
      contMDiff_toFun := by
        apply (ContMDiff.subtypeVal_comp_iff
          (T.cutCarrier.pieceInterior (T.components.piece i)) _).mp
        change ContMDiff ((SurfaceModel.model P.base.surface.kind).prod (𝓡 1))
          T.cutCarrier.model ∞ (fun x : chartBaseInterior P.base × Circle => (f x).val)
        exact contMDiff_subtype_val.comp (P.trivialization.contMDiff.comp
          ((contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd))
      contMDiff_invFun := by
        apply ContMDiff.prodMk
        · apply (ContMDiff.subtypeVal_comp_iff _ _).mp
          exact contMDiff_fst.comp (P.trivialization.symm.contMDiff.comp
            (contMDiff_inclusion (inf_le_left :
              T.cutCarrier.pieceInterior (T.components.piece i) ≤ T.components.piece i)))
        · exact contMDiff_snd.comp (P.trivialization.symm.contMDiff.comp
            (contMDiff_inclusion (inf_le_left :
              T.cutCarrier.pieceInterior (T.components.piece i) ≤ T.components.piece i))) }
  exact ((P.base.chartInteriorDiffeomorph.prodCongr
    (Diffeomorph.refl (𝓡 1) Circle ∞)).symm).trans e

theorem chartConventionMatrix_det (p q a b : ℤ) (h : p * b - a * q = 1) :
    (chartConventionMatrix p q a b).det = -1 := by
  simp only [chartConventionMatrix, Matrix.det_fin_two_of]
  linear_combination -h

theorem chartK20_inverse (p q a b : ℤ) (h : p * b - a * q = 1) :
    Int.ModEq p ((-a) * q) 1 := by
  apply Int.modEq_of_dvd
  exact ⟨b, by linear_combination -h⟩

theorem SeifertBlockCharts.matrix_firstColumn {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (m : Fin d.fillingCount) :
    ((C.matrix m) 0 0, (C.matrix m) 1 0) = -d.fillingSlope m := by
  rw [C.matrix_eq]
  rfl

theorem SeifertBlockCharts.matrix_det {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (m : Fin d.fillingCount) :
    (C.matrix m : Matrix (Fin 2) (Fin 2) ℤ).det = -1 := by
  rw [C.matrix_eq]
  exact chartConventionMatrix_det (d.fillingSlope m).1 (d.fillingSlope m).2
    (C.a m) (C.b m) (C.bezout m)

theorem SeifertBlockCharts.longitude_core {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (m : Fin d.fillingCount) :
    C.a m * (-(d.fillingSlope m).2) + C.b m * (d.fillingSlope m).1 = 1 := by
  linear_combination C.bezout m

theorem chartBezout_regression_5_2 :
    (5 : ℤ) * 1 - 2 * 2 = 1 ∧ Int.ModEq 5 ((-2) * 2) 1 ∧
      (-2 : ℤ) % 5 = 3 ∧ (3 : ℤ) % 5 ≠ 2 % 5 := by
  decide

theorem chartBezout_regression_2_1 :
    (2 : ℤ) * 1 - 1 * 1 = 1 ∧ Int.ModEq 2 ((-1) * 1) 1 := by decide

theorem chartBezout_regression_3_1 :
    (3 : ℤ) * 1 - 2 * 1 = 1 ∧ Int.ModEq 3 ((-2) * 1) 1 := by decide

theorem chartBezout_regression_3_2 :
    (3 : ℤ) * 1 - 1 * 2 = 1 ∧ Int.ModEq 3 ((-1) * 2) 1 := by decide

def SeifertBlock.unfilledCharts {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (h : d.fillingCount = 0) : SeifertBlockCharts W d where
  port := B.port
  matrix m := Fin.elim0 (h ▸ m)
  a m := Fin.elim0 (h ▸ m)
  b m := Fin.elim0 (h ▸ m)
  matrix_eq m := Fin.elim0 (h ▸ m)
  bezout m := Fin.elim0 (h ▸ m)
  productRegion := W.interior
  productRegion_interior := Subset.rfl
  product := by
    have e := B.product.chartPieceInteriorDiffeomorph.trans (B.unfilledInteriorDiffeomorph h)
    have he : W.pieceInterior ⊤ = W.interior := by
      apply TopologicalSpace.Opens.ext
      ext x
      simp [CompactCarrier.pieceInterior]
    rw [he] at e
    exact e
  ε := 1
  ε_pos := zero_lt_one
  tube m := Fin.elim0 (h ▸ m)
  tube_source m := Fin.elim0 (h ▸ m)
  tube_interior m := Fin.elim0 (h ▸ m)
  transitionDomain := {y : ℂ × Circle | 1 < ‖y.1‖ ∧ ‖y.1‖ < 1 + 1}
  transitionDomain_eq := rfl
  transition_domain m := Fin.elim0 (h ▸ m)
  transition m := Fin.elim0 (h ▸ m)
  tube_product_overlap m := Fin.elim0 (h ▸ m)
  disjoint := by
    intro m
    exact Fin.elim0 (h ▸ m)
  covers x hx := Or.inl hx

theorem SeifertBlock.exists_unfilled_charts {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (h : d.fillingCount = 0) :
    Nonempty (SeifertBlockCharts W d) :=
  ⟨B.unfilledCharts h⟩

def chartStandardBase (d : SeifertData) : PlanarBase.{u} d.k := by
  by_cases hk : d.k = 1
  · rw [hk]
    exact discPlanarBase 1
  · exact planarBase d.k (by have h1 := d.one_le_k; have h3 := d.k_le_three; omega)

theorem ProductFibredPiece.exists_standard_germ {W : CompactCarrier.{u}}
    {T : TorusPresentation W} {i : Fin T.components.count} {k : ℕ}
    (P : ProductFibredPiece T i k) (Q : PlanarBase.{u} k) :
    ∃ δ > (0 : ℝ), ∃ Θ : (Q.surface.Carrier × Circle) ≃ₘ⟮
      (SurfaceModel.model Q.surface.kind).prod (𝓡 1), T.cutCarrier.model⟯ T.components.piece i,
      ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
        T.pieceCollar i (P.port j) p = Θ (Q.collar j (p.1.1, p.2), p.1.2) := by
  let Θ := ((Q.diffeomorph P.base).prodCongr
    (Diffeomorph.refl (𝓡 1) Circle ∞)).trans P.trivialization
  have h0 : ∀ j (t : Torus), T.pieceCollar i (P.port j) (t, halfZero) =
      Θ (Q.collar j (t.1, halfZero), t.2) := by
    intro j t
    rw [P.collar_eq j (t, halfZero) (zero_mem_halfCollarSource t)]
    have hb : Q.diffeomorph P.base (Q.collar j (t.1, halfZero)) =
        P.base.collar j (t.1, halfZero) := by
      apply P.base.isSmoothEmbedding.isEmbedding.injective
      rw [PlanarBase.embedding_diffeomorph, Q.embedding_collar, P.base.embedding_collar]
    change P.trivialization (P.base.collar j (t.1, halfZero), t.2) =
      P.trivialization (Q.diffeomorph P.base (Q.collar j (t.1, halfZero)), t.2)
    rw [hb]
  exact T.exists_germ_trivialization i Q P.port
    (Function.const (Fin k) (Diffeomorph.refl torusModel Torus ∞)) Θ h0

theorem SeifertBlock.interior_eq_univ_of_ports_zero {W : CompactCarrier.{u}}
    {d : SeifertData} (B : SeifertBlock W d) (h : d.ports = 0) :
    (W.interior : Set W.Carrier) = univ := by
  apply eq_univ_of_forall
  intro x
  apply (W.model.isInteriorPoint_iff_not_isBoundaryPoint x).mpr
  intro hx
  change x ∈ W.model.boundary W.Carrier at hx
  rw [B.presentation.external_exhausted] at hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  have hn := (B.free.symm j).isLt
  omega

theorem SeifertBlockCharts.closed_cover {W : CompactCarrier.{u}} {d : SeifertData}
    (C : SeifertBlockCharts W d) (B : SeifertBlock W d) (h : d.ports = 0) (x : W.Carrier) :
    x ∈ C.productRegion ∨ ∃ m, x ∈ (C.tube m).target := by
  apply C.covers x
  change x ∈ (W.interior : Set W.Carrier)
  rw [B.interior_eq_univ_of_ports_zero h]
  trivial

namespace ConeFilling
variable (c : ConeFilling)

def chartTubeRadius : ℝ := seamRadius c.p 1 / 3

theorem chartTubeRadius_pow : c.chartTubeRadius ^ c.p = 3 / 2 := by
  have h := div_three_pow_seamRadius c.p (s := 1) (by norm_num)
  convert h using 1 <;> norm_num [chartTubeRadius]

theorem chartTubeRadius_gt_one : 1 < c.chartTubeRadius := by
  have hp := c.chartTubeRadius_pow
  have h0 : 0 ≤ c.chartTubeRadius := by
    exact div_nonneg (seamRadius_pos c.p (by norm_num)).le (by norm_num)
  by_contra hn
  have hle := pow_le_one₀ h0 (not_lt.mp hn) (n := c.p)
  rw [hp] at hle
  norm_num at hle

def chartTubeScale :
    (ℂ × Circle) ≃ₘ⟮(𝓘(ℝ, ℂ).prod (𝓡 1)), PlaneCircleModel⟯
      (PlaneLift.{u} × Circle) where
  toFun y := (ULift.up (3 * y.1), y.2)
  invFun x := (x.1.down / 3, x.2)
  left_inv y := by
    change (3 * y.1 / 3, y.2) = y
    simp
  right_inv x := by
    change (ULift.up (3 * (x.1.down / 3)), x.2) = x
    apply Prod.ext
    · apply ULift.ext
      change 3 * (x.1.down / 3) = x.1.down
      ring
    · exact Eq.refl x.2
  contMDiff_toFun :=
    (contMDiff_planeLift_up.comp
      (((contDiff_const.mul contDiff_id).contMDiff).comp contMDiff_fst)).prodMk contMDiff_snd
  contMDiff_invFun :=
    (((contDiff_id.div_const 3).contMDiff).comp
      (contMDiff_planeLift_down.comp contMDiff_fst)).prodMk contMDiff_snd

theorem chartTubeScale_mem_interior (y : ℂ × Circle) (hy : ‖y.1‖ < c.chartTubeRadius) :
    chartTubeScale.{u} y ∈ interior c.filledSet := by
  have hp : ‖y.1‖ ^ c.p < 3 / 2 := by
    rw [← c.chartTubeRadius_pow]
    exact pow_lt_pow_left₀ hy (norm_nonneg _) (NeZero.ne c.p)
  have hz : ‖c.conePoint (chartTubeScale.{u} y) - ((3 / 2 : ℝ) : ℂ)‖ < 1 := by
    rw [c.norm_conePoint_sub]
    change (‖3 * y.1‖ / 3) ^ c.p / 2 < 1
    have he : ‖3 * y.1‖ / 3 = ‖y.1‖ := by simp
    rw [he]
    linarith
  have hn := filledFunction_neg_of_near hz
  have ho : IsOpen {x : PlaneLift.{u} × Circle | filledFunction (c.conePoint x) < 0} :=
    isOpen_lt c.contMDiff_filledFunction_conePoint.continuous continuous_const
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (ho.mem_nhds hn)
  intro x hx
  exact (show filledFunction (c.conePoint x) < 0 from hx).le

def chartTube : PartialDiffeomorph PlaneCircleModel (𝓡∂ 3)
    (ℂ × Circle) c.filledSet.{u} ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    (chartTubeScale.toPartialDiffeomorph.trans
      (c.filledAtlas.interiorPartialDiffeomorph
        (c.solidFold (⟨(ULift.up 0, 1), by rw [mem_solidSet_iff]; simp⟩))).symm)
    {y : ℂ × Circle | ‖y.1‖ < c.chartTubeRadius}
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const)

theorem chartTube_source : c.chartTube.{u}.source =
    {y : ℂ × Circle | ‖y.1‖ < c.chartTubeRadius} := by
  ext y
  change (y ∈ univ ∧ chartTubeScale.{u} y ∈ interior c.filledSet) ∧
    ‖y.1‖ < c.chartTubeRadius ↔ ‖y.1‖ < c.chartTubeRadius
  exact ⟨fun h => h.2, fun h => ⟨⟨mem_univ y, c.chartTubeScale_mem_interior y h⟩, h⟩⟩

theorem chartTube_apply_val (y : ℂ × Circle) (hy : ‖y.1‖ < c.chartTubeRadius) :
    (c.chartTube.{u} y).val = chartTubeScale.{u} y := by
  exact (c.filledAtlas.interiorPartialDiffeomorph
    (c.solidFold (⟨(ULift.up 0, 1), by rw [mem_solidSet_iff]; simp⟩))).right_inv
      (c.chartTubeScale_mem_interior y hy)

theorem chartTube_target (y : c.filledSet.{u}) :
    y ∈ c.chartTube.target ↔ ‖y.val.1.down / 3‖ < c.chartTubeRadius := by
  constructor
  · intro hy
    have hs := c.chartTube.map_target hy
    rw [c.chartTube_source] at hs
    exact hs
  · intro hy
    let z : ℂ × Circle := (y.val.1.down / 3, y.val.2)
    have hz : ‖z.1‖ < c.chartTubeRadius := hy
    have he : chartTubeScale.{u} z = y.val := by
      apply Prod.ext
      · apply ULift.ext
        change 3 * (y.val.1.down / 3) = y.val.1.down
        ring
      · exact Eq.refl y.val.2
    have he' : c.chartTube z = y := Subtype.ext ((c.chartTube_apply_val z hz).trans he)
    rw [← he']
    exact c.chartTube.map_source ((c.chartTube_source).symm ▸ hz)

theorem chartTube_interior :
    c.chartTube.{u}.target ⊆ (𝓡∂ 3).interior c.filledSet.{u} := by
  intro y hy
  have hi := ((c.chartTube.isLocalDiffeomorphAt PlaneCircleModel (𝓡∂ 3) ∞
    (c.chartTube.map_target hy)).isInteriorPoint_iff (by simp)).mp
      BoundarylessManifold.isInteriorPoint
  rw [c.chartTube.right_inv hy] at hi
  exact hi

theorem chartPlanarOpen_three_iff (z : ℂ) :
    z ∈ planarOpen 3 ↔ planarFunction 3 z < 0 := by
  constructor
  · intro hz
    apply (planarFunction_three_neg_iff z).mpr
    refine ⟨chartPlanarInterior_lt hz, ?_, ?_⟩
    · simpa [planarCenter] using chartPlanarInterior_hole_lt hz (1 : Fin 3) (by decide)
    · simpa [planarCenter] using chartPlanarInterior_hole_lt hz (2 : Fin 3) (by decide)
  · intro hz
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset
      ((isOpen_lt (contDiff_planarFunction 3).continuous continuous_const).mem_nhds hz)
    intro y hy
    exact (planarFunction_nonpos_iff (Or.inr rfl) y).mp hy.le

def chartProductInput (x : planarOpen 3 × Circle) : productSet.{u} 3 :=
  ⟨(ULift.up x.1.val, x.2), (mem_productSet_iff _).mpr (interior_subset x.1.property)⟩

def chartProductMap (x : planarOpen 3 × Circle) : c.filledSet.{u} :=
  c.productFold (chartProductInput x)

theorem chartProductMap_val (x : planarOpen 3 × Circle) :
    (c.chartProductMap x).val = c.coneLift (ULift.up x.1.val, x.2) := rfl

theorem chartProductMap_ne (x : planarOpen 3 × Circle) : x.1.val ≠ ((3 / 2 : ℝ) : ℂ) := by
  have hh := chartPlanarInterior_hole_lt x.1.property (1 : Fin 3) (by decide)
  change 1 / 2 < ‖x.1.val - ((3 / 2 : ℝ) : ℂ)‖ at hh
  intro he
  rw [he, sub_self, norm_zero] at hh
  linarith

theorem chartProductMap_rawInterior (x : planarOpen 3 × Circle) :
    (c.chartProductMap x).val ∈ interior c.filledSet := by
  have hn := (planarFunction_three_neg_iff x.1.val).mp
    ((chartPlanarOpen_three_iff x.1.val).mp x.1.property)
  have hneg : filledFunction (c.conePoint (c.chartProductMap x).val) < 0 := by
    rw [c.chartProductMap_val, c.conePoint_coneLift _ (chartProductMap_ne x)]
    exact (filledFunction_neg_iff ((filledFunction_nonpos_iff _).mpr
      ⟨hn.1.le, hn.2.2.le⟩)).mpr ⟨hn.1, hn.2.2⟩
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset
    ((isOpen_lt c.contMDiff_filledFunction_conePoint.continuous continuous_const).mem_nhds hneg)
  intro y hy
  exact (show filledFunction (c.conePoint y) < 0 from hy).le

theorem chartProductMap_local :
    IsLocalDiffeomorph PlaneCircleModel (𝓡∂ 3) ∞ c.chartProductMap.{u} := by
  intro x
  apply c.filledAtlas.isLocalDiffeomorphAt_of_subtype_val (c.chartProductMap_rawInterior x)
  have hbase := isLocalDiffeomorph_subtype_val (I := 𝓘(ℝ, ℂ)) (planarOpen 3) x.1
  have hcircle := (Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph x.2
  have hprod := hbase.prodMap hcircle
  have hlift := chartPlaneCircleLift.symm.isLocalDiffeomorph (x.1.val, x.2)
  have hcone := c.coneLiftPartialDiffeomorph.isLocalDiffeomorphAt
    PlaneCircleModel PlaneCircleModel ∞ (x := (ULift.up x.1.val, x.2))
      (chartProductMap_ne x)
  exact (hprod.comp (K := PlaneCircleModel) (P := PlaneLift.{u} × Circle) hlift).comp
    (K := PlaneCircleModel) (P := PlaneLift.{u} × Circle) hcone

theorem chartProductMap_injective : Function.Injective c.chartProductMap.{u} := by
  intro x y h
  have hr := congrArg (fun z : c.filledSet.{u} => c.coneChart z.val) h
  rw [c.chartProductMap_val, c.chartProductMap_val,
    c.coneChart_coneLift _ (chartProductMap_ne x),
    c.coneChart_coneLift _ (chartProductMap_ne y)] at hr
  exact Prod.ext (Subtype.ext (congrArg (fun z : PlaneLift.{u} × Circle => z.1.down) hr))
    (congrArg (fun z : PlaneLift.{u} × Circle => z.2) hr)

def chartProductRegion : TopologicalSpace.Opens c.filledSet.{u} := c.chartProductMap_local.image

def chartProduct : (planarOpen 3 × Circle) ≃ₘ⟮PlaneCircleModel, 𝓡∂ 3⟯
    c.chartProductRegion.{u} :=
  diffeomorphOntoImage c.chartProductMap c.chartProductMap_local c.chartProductMap_injective

theorem chartProductMap_norm_gt (x : planarOpen 3 × Circle) :
    3 < ‖(c.chartProductMap.{u} x).val.1.down‖ := by
  have hh := chartPlanarInterior_hole_lt x.1.property (1 : Fin 3) (by decide)
  change 1 / 2 < ‖x.1.val - ((3 / 2 : ℝ) : ℂ)‖ at hh
  have he := c.norm_conePoint_sub (c.chartProductMap.{u} x).val
  rw [c.chartProductMap_val, c.conePoint_coneLift _ (chartProductMap_ne x)] at he
  by_contra h
  have hp : (‖(c.chartProductMap.{u} x).val.1.down‖ / 3) ^ c.p ≤ 1 :=
    pow_le_one₀ (div_nonneg (norm_nonneg _) (by norm_num))
      ((div_le_one₀ (by norm_num)).mpr (not_lt.mp h))
  change (‖(c.coneLift (ULift.up x.1.val, x.2)).1.down‖ / 3) ^ c.p ≤ 1 at hp
  linarith

theorem chartProductRegion_interior :
    (c.chartProductRegion.{u} : Set c.filledSet.{u}) ⊆ c.filledCarrier.interior := by
  rintro y ⟨x, rfl⟩
  exact ((c.chartProductMap_local x).isInteriorPoint_iff (by simp)).mp
    BoundarylessManifold.isInteriorPoint

theorem chartProductRegion_mem (y : c.filledSet.{u}) :
    y ∈ c.chartProductRegion ↔ (𝓡∂ 3).IsInteriorPoint y ∧ 3 < ‖y.val.1.down‖ := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨((c.chartProductMap_local x).isInteriorPoint_iff (by simp)).mp
      BoundarylessManifold.isInteriorPoint, c.chartProductMap_norm_gt x⟩
  · rintro ⟨hi, hn⟩
    have hneg := (c.filledSet_isInteriorPoint_iff y).mp hi
    obtain ⟨h1, h3⟩ := (filledFunction_neg_iff y.property).mp hneg
    have h2 : 1 / 2 < ‖c.conePoint y.val - ((3 / 2 : ℝ) : ℂ)‖ := by
      rw [c.norm_conePoint_sub]
      have hp : 1 < (‖y.val.1.down‖ / 3) ^ c.p :=
        one_lt_pow₀ ((one_lt_div₀ (by norm_num)).mpr hn) (NeZero.ne c.p)
      linarith
    have hp : c.conePoint y.val ∈ planarOpen 3 :=
      (chartPlanarOpen_three_iff _).mpr ((planarFunction_three_neg_iff _).mpr ⟨h1, h2, h3⟩)
    let x : planarOpen 3 × Circle := (⟨c.conePoint y.val, hp⟩, (c.coneChart y.val).2)
    refine ⟨x, Subtype.ext ?_⟩
    exact c.coneLift_coneChart y.val (ne_zero_of_three_lt hn)

theorem chartTube_product_overlap :
    c.chartTube.{u}.target ∩ (c.chartProductRegion : Set c.filledSet) =
      c.chartTube '' {y : ℂ × Circle | 1 < ‖y.1‖ ∧ ‖y.1‖ < c.chartTubeRadius} := by
  ext y
  constructor
  · rintro ⟨ht, hp⟩
    refine ⟨c.chartTube.symm y, ⟨?_, ?_⟩, c.chartTube.right_inv ht⟩
    · have hn := ((c.chartProductRegion_mem y).mp hp).2
      change 1 < ‖y.val.1.down / 3‖
      simpa only [norm_div, Complex.norm_ofNat] using
        (one_lt_div₀ (by norm_num : (0 : ℝ) < 3)).mpr hn
    · have hs := c.chartTube.map_target ht
      rw [c.chartTube_source] at hs
      exact hs
  · rintro ⟨z, ⟨hl, hu⟩, rfl⟩
    have hs : z ∈ c.chartTube.{u}.source := c.chartTube_source.symm ▸ hu
    refine ⟨c.chartTube.map_source hs, (c.chartProductRegion_mem _).mpr ⟨?_, ?_⟩⟩
    · exact c.chartTube_interior (c.chartTube.map_source hs)
    · rw [c.chartTube_apply_val z hu]
      change 3 < ‖3 * z.1‖
      simp only [norm_mul, Complex.norm_ofNat]
      linarith

theorem chartTube_product_cover (y : c.filledSet.{u}) (hy : y ∈ c.filledCarrier.interior) :
    y ∈ c.chartProductRegion ∨ y ∈ c.chartTube.target := by
  by_cases hn : 3 < ‖y.val.1.down‖
  · exact Or.inl ((c.chartProductRegion_mem y).mpr ⟨hy, hn⟩)
  · apply Or.inr
    apply (c.chartTube_target y).mpr
    have hle : ‖y.val.1.down / 3‖ ≤ 1 := by
      rw [norm_div, Complex.norm_ofNat]
      exact (div_le_one₀ (by norm_num)).mpr (not_lt.mp hn)
    exact lt_of_le_of_lt hle c.chartTubeRadius_gt_one

theorem chartSeam_eq (hp : 2 ≤ c.p) (m : Fin 1) (y : ℂ × Circle) :
    seamModel (oneConeData c.p c.q hp c.gcd_eq_one) m 1 c.matchingUnit y =
      ((c.coneChart (chartTubeScale.{u} y)).1.down,
        (c.coneChart (chartTubeScale.{u} y)).2) := by
  have hu : unitOf (3 * y.1) = unitOf y.1 := by
    by_cases hz : y.1 = 0
    · rw [hz, mul_zero]
    · have he : 3 * y.1 = (3 * ‖y.1‖ : ℝ) • (unitOf y.1 : ℂ) := by
        rw [mul_smul, norm_smul_unitOf]
        simp [Complex.real_smul]
      rw [he]
      exact unitOf_smul (by positivity) _
  have hr : ‖3 * y.1‖ / 3 = ‖y.1‖ := by simp
  have hm : (c.matchingUnit : Matrix (Fin 2) (Fin 2) ℤ) = c.matchingMatrix := rfl
  simp only [seamModel, fillingSlope_oneConeData, Int.natAbs_natCast, hm,
    matchingMatrix, linearTorusMap_mul, linearTorusMap_reflect, Fin.val_one,
    one_ne_zero, ite_false]
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

theorem chartSeam_domain (hp : 2 ≤ c.p) (m : Fin 1) (y : ℂ × Circle)
    (hy : 1 < ‖y.1‖ ∧ ‖y.1‖ < c.chartTubeRadius) :
    (seamModel (oneConeData c.p c.q hp c.gcd_eq_one) m 1 c.matchingUnit y).1 ∈
      planarOpen 3 := by
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
  rw [c.chartSeam_eq.{0} hp m y]
  change c.conePoint (chartTubeScale.{0} y) ∈ planarOpen 3
  rw [← c.chartTube_apply_val y hy.2, ← hx, c.chartProductMap_val,
    c.conePoint_coneLift _ (chartProductMap_ne x)]
  exact x.1.property

theorem chartSeam_transition (hp : 2 ≤ c.p) (m : Fin 1) (y : ℂ × Circle)
    (hy : 1 < ‖y.1‖ ∧ ‖y.1‖ < c.chartTubeRadius) :
    c.chartTube.{u} y =
      (c.chartProduct (⟨(seamModel (oneConeData c.p c.q hp c.gcd_eq_one) m 1
        c.matchingUnit y).1, c.chartSeam_domain hp m y hy⟩,
        (seamModel (oneConeData c.p c.q hp c.gcd_eq_one) m 1 c.matchingUnit y).2) :
        c.filledSet.{u}) := by
  apply Subtype.ext
  rw [c.chartTube_apply_val y hy.2]
  change chartTubeScale.{u} y = c.coneLift
    (ULift.up (seamModel (oneConeData c.p c.q hp c.gcd_eq_one) m 1 c.matchingUnit y).1,
      (seamModel (oneConeData c.p c.q hp c.gcd_eq_one) m 1 c.matchingUnit y).2)
  rw [c.chartSeam_eq.{u} hp m y]
  exact (c.coneLift_coneChart (chartTubeScale.{u} y) (by
    change 3 * y.1 ≠ 0
    exact mul_ne_zero (by norm_num) (norm_pos_iff.mp (by linarith [hy.1])))).symm

def filledCharts (hp : 2 ≤ c.p) :
    SeifertBlockCharts c.filledCarrier.{u} (oneConeData c.p c.q hp c.gcd_eq_one) where
  port := c.portEquiv hp
  matrix := fun m => c.matchingUnit
  a := fun m => c.a
  b := fun m => c.b
  matrix_eq m := by
    rw [c.fillingSlope_oneConeData hp m]
    change c.matchingMatrix = !![-(c.p : ℤ), c.a; -c.q, c.b]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matchingMatrix, reflectMatrix, chartMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  bezout m := by
    rw [c.fillingSlope_oneConeData hp m]
    exact c.det_eq
  productRegion := c.chartProductRegion
  productRegion_interior := c.chartProductRegion_interior
  product := c.chartProduct
  ε := c.chartTubeRadius - 1
  ε_pos := by linarith [c.chartTubeRadius_gt_one]
  tube := fun m => c.chartTube
  tube_source m := by
    rw [c.chartTube_source]
    congr 1
    ext y
    simp
  tube_interior m := c.chartTube_interior
  transitionDomain := {y | 1 < ‖y.1‖ ∧ ‖y.1‖ < c.chartTubeRadius}
  transitionDomain_eq := by simp
  transition_domain m y hy := c.chartSeam_domain hp m y hy
  transition m y hy := c.chartSeam_transition hp m y hy
  tube_product_overlap m := c.chartTube_product_overlap
  disjoint := by
    intro m n hmn
    change Fin 1 at m n
    exact False.elim (hmn (Subsingleton.elim m n))
  covers y hy := by
    rcases c.chartTube_product_cover y hy with hp' | ht
    · exact Or.inl hp'
    · exact Or.inr ⟨0, ht⟩

end ConeFilling

namespace ProductFibredPiece
variable {W : CompactCarrier.{u}} {T : TorusPresentation W}
  {i : Fin T.components.count} {k : ℕ} (P : ProductFibredPiece T i k)

def chartProductForward (x : planarOpen k × Circle) : W.Carrier :=
  T.cutMap (P.chartPieceInteriorDiffeomorph x).val

theorem chartProductForward_local :
    IsLocalDiffeomorph PlaneCircleModel W.model ∞ P.chartProductForward := by
  intro x
  let e := P.chartPieceInteriorDiffeomorph
  have hval := DifferentialGeometry.isLocalDiffeomorph_subtype_val
    (I := T.cutCarrier.model) (T.cutCarrier.pieceInterior (T.components.piece i)) (e x)
  have hcut := T.isLocalDiffeomorphAt_cutMap (e x).property.2
  exact (e.isLocalDiffeomorph x).comp W.model W.Carrier
    (hval.comp W.model W.Carrier hcut)

theorem chartProductForward_injective : Function.Injective P.chartProductForward := by
  intro x y h
  let e := P.chartPieceInteriorDiffeomorph
  let a : T.cutCarrier.interior := ⟨(e x).val, (e x).property.2⟩
  let b : T.cutCarrier.interior := ⟨(e y).val, (e y).property.2⟩
  have he : T.interiorDiffeomorph a = T.interiorDiffeomorph b := by
    apply Subtype.ext
    rw [T.interior_map, T.interior_map]
    exact h
  apply e.injective
  apply Subtype.ext
  exact congrArg (fun z : T.cutCarrier.interior => z.val) (T.interiorDiffeomorph.injective he)

def chartProductRegion : TopologicalSpace.Opens W.Carrier :=
  P.chartProductForward_local.image

def chartProductDiffeomorph :
    (planarOpen k × Circle) ≃ₘ⟮PlaneCircleModel, W.model⟯ P.chartProductRegion :=
  diffeomorphOntoImage P.chartProductForward P.chartProductForward_local
    P.chartProductForward_injective

theorem chartProductDiffeomorph_apply (x : planarOpen k × Circle) :
    (P.chartProductDiffeomorph x : W.Carrier) =
      T.cutMap (P.chartPieceInteriorDiffeomorph x).val := rfl

theorem chartProductRegion_interior :
    (P.chartProductRegion : Set W.Carrier) ⊆ W.interior := by
  rintro y ⟨x, rfl⟩
  exact ((P.chartProductForward_local x).isInteriorPoint_iff (by simp)).mp
    BoundarylessManifold.isInteriorPoint

theorem chartProductRegion_mem_iff (y : W.Carrier) :
    y ∈ P.chartProductRegion ↔
      ∃ x : T.cutCarrier.pieceInterior (T.components.piece i), T.cutMap x.val = y := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨P.chartPieceInteriorDiffeomorph x, hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := P.chartPieceInteriorDiffeomorph.surjective x
    exact ⟨z, hx⟩

end ProductFibredPiece

def mobiusChartProductRegion : TopologicalSpace.Opens mobiusBundleCarrier.{u}.Carrier :=
  mobiusProductPiece.chartProductRegion

def mobiusChartProductDiffeomorph :
    (planarOpen mobiusData.k × Circle) ≃ₘ⟮PlaneCircleModel, mobiusBundleCarrier.{u}.model⟯
      mobiusChartProductRegion.{u} :=
  mobiusProductPiece.chartProductDiffeomorph

theorem mobiusChartProductRegion_interior :
    (mobiusChartProductRegion.{u} : Set mobiusBundleCarrier.{u}.Carrier) ⊆
      mobiusBundleCarrier.{u}.interior :=
  mobiusProductPiece.chartProductRegion_interior

theorem mobiusChartProductRegion_iff (y : mobiusBundleCarrier.{u}.Carrier) :
    y ∈ mobiusChartProductRegion ↔ ‖mobiusBundleBase y‖ < 3 ∧
      1 / 2 < ‖mobiusBundleBase y - 3 / 2‖ ∧ 1 / 2 < ‖mobiusBundleBase y + 3 / 2‖ := by
  rw [mobiusChartProductRegion, mobiusProductPiece.chartProductRegion_mem_iff]
  constructor
  · rintro ⟨⟨x, hx, hi⟩, he⟩
    change x ∈ Set.range (Sum.inl : productSet.{u} 3 → MobiusCut.{u}) at hx
    obtain ⟨a, rfl⟩ := hx
    change mobiusPantsFold a = y at he
    rw [← he, mobiusBundleBase_mobiusPantsFold]
    exact (planarFunction_three_neg_iff' _).mp
      ((ConeFilling.productSet_isInteriorPoint_iff a).mp ((isInteriorPoint_inl_iff a).mp hi))
  · rintro ⟨h0, h1, h2⟩
    refine ⟨⟨Sum.inl (pantsOf y), ?_, ?_⟩, ?_⟩
    · exact ⟨pantsOf y, rfl⟩
    · exact (isInteriorPoint_inl_iff (pantsOf y)).mpr (pantsOf_interior h0 h1 h2)
    · exact mobiusPantsFold_pantsOf (mem_planarModel_of_far h1 h2)

theorem mobiusChartCover (y : mobiusBundleCarrier.{u}.Carrier)
    (hy : y ∈ mobiusBundleCarrier.{u}.interior) :
    y ∈ mobiusChartProductRegion ∨ y ∈ Set.range solidFoldPlus ∨
      y ∈ Set.range solidFoldMinus := by
  have h0 : ‖mobiusBundleBase y‖ < 3 := by
    have hn := mobiusBundleBase_norm_le y
    have hb := (mobiusBundleCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint y).mp hy
    change ¬ (𝓡∂ 3).IsBoundaryPoint (show mobiusBundleSet.{u} from y) at hb
    rw [mobiusBundleSet_isBoundaryPoint_iff_base] at hb
    exact lt_of_le_of_ne hn hb
  by_cases h1 : 1 / 2 < ‖mobiusBundleBase y - 3 / 2‖
  · by_cases h2 : 1 / 2 < ‖mobiusBundleBase y + 3 / 2‖
    · exact Or.inl ((mobiusChartProductRegion_iff y).mpr ⟨h0, h1, h2⟩)
    · exact Or.inr (Or.inr ⟨⟨solidNegChart y.val, solidNegChart_mem y (le_of_not_gt h2)⟩,
        solidFoldMinus_chart y (le_of_not_gt h2)⟩)
  · exact Or.inr (Or.inl ⟨⟨solidChart y.val, solidChart_mem y (le_of_not_gt h1)⟩,
      solidFoldPlus_chart y (le_of_not_gt h1)⟩)

theorem solidDiffeomorph_discBoundary (p : ℕ) [NeZero p] (t : Torus) :
    solidDiffeomorph.{u} ((discPlanarBase p).collar 0 (t.1, halfZero), t.2) =
      chartSolidBoundary t := by
  apply Subtype.ext
  apply Prod.ext
  · apply ULift.ext
    exact discCollar_zero_val.{u} p t.1
  · rfl

theorem SolidTorusPiece.exists_basis_germ {W : CompactCarrier.{u}}
    {T : TorusPresentation W} {i : Fin T.components.count} (P : SolidTorusPiece T i)
    (p : ℕ) [NeZero p] (C : GL (Fin 2) ℤ)
    (Φ : solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u})
    (hΦ : ∀ t, Φ (chartSolidBoundary t) = chartSolidBoundary (linearTorusMap C t)) :
    ∃ δ > (0 : ℝ), ∃ Θ : (discSet.{u} × Circle) ≃ₘ⟮
      (𝓡∂ 2).prod (𝓡 1), T.cutCarrier.model⟯ T.components.piece i,
      ∀ j t s, (t, s) ∈ halfCollarSource → s.val 0 < δ →
        T.pieceCollar i (P.port j) (linearTorusMap C t, s) =
          Θ ((discPlanarBase p).collar j (t.1, s), t.2) := by
  let Q : PlanarBase.{u} 1 := discPlanarBase p
  let Ψ := ((Q.diffeomorph P.base).prodCongr
    (Diffeomorph.refl (𝓡 1) Circle ∞)).trans P.trivialization
  let Θ : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), T.cutCarrier.model⟯
      T.components.piece i :=
    (solidDiffeomorph.trans Φ).trans (solidDiffeomorph.symm.trans Ψ)
  have h0 : ∀ j (t : Torus),
      T.pieceCollar i (P.port j) (linearTorusMap C t, halfZero) =
        Θ (Q.collar j (t.1, halfZero), t.2) := by
    intro j t
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    rw [P.collar_eq 0 (linearTorusMap C t, halfZero)
      (zero_mem_halfCollarSource (linearTorusMap C t))]
    change P.trivialization (P.base.collar 0 ((linearTorusMap C t).1, halfZero),
        (linearTorusMap C t).2) =
      Ψ (solidDiffeomorph.symm (Φ (solidDiffeomorph
        (Q.collar 0 (t.1, halfZero), t.2))))
    rw [solidDiffeomorph_discBoundary, hΦ,
      ← solidDiffeomorph_discBoundary p (linearTorusMap C t),
      solidDiffeomorph.symm_apply_apply]
    have hb : Q.diffeomorph P.base (Q.collar 0 ((linearTorusMap C t).1, halfZero)) =
        P.base.collar 0 ((linearTorusMap C t).1, halfZero) := by
      apply P.base.isSmoothEmbedding.isEmbedding.injective
      rw [PlanarBase.embedding_diffeomorph, Q.embedding_collar, P.base.embedding_collar]
    change P.trivialization (P.base.collar 0 ((linearTorusMap C t).1, halfZero),
        (linearTorusMap C t).2) =
      P.trivialization (Q.diffeomorph P.base (Q.collar 0 ((linearTorusMap C t).1, halfZero)),
        (linearTorusMap C t).2)
    rw [hb]
  obtain ⟨δ, hδ, Θ', hΘ'⟩ := T.exists_germ_trivialization i Q P.port
    (Function.const (Fin 1) (linearTorusDiffeomorph C)) Θ h0
  exact ⟨δ, hδ, Θ', fun j t s hs hlt => hΘ' j (t, s) hs hlt⟩


def SeifertBlock.linearized {W : CompactCarrier.{u}} {d : SeifertData}
    (hT : TorusMappingClassLinear) (B : SeifertBlock W d) : SeifertBlock W d where
  presentation := linearPresentation hT B.presentation
  piece := B.piece
  product := linearPiece hT B.product
  solid m := linearPiece hT (B.solid m)
  port := B.port
  seam := B.seam
  free := B.free
  free_port r := B.free_port r
  filled_port m := B.filled_port m
  solid_port m := B.solid_port m
  slope m := by
    change torusUnit (linearTorusDiffeomorph
      (torusUnit (B.presentation.pairing.matching (B.seam m)))) • meridianSlope = _
    rw [torusUnit_linearTorusDiffeomorph]
    exact B.slope m

theorem SeifertBlock.linearized_matching {W : CompactCarrier.{u}} {d : SeifertData}
    (hT : TorusMappingClassLinear) (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    (B.linearized hT).presentation.pairing.matching ((B.linearized hT).seam m) =
      linearTorusDiffeomorph (torusUnit ((B.linearized hT).presentation.pairing.matching
        ((B.linearized hT).seam m))) := by
  change linearTorusDiffeomorph (torusUnit (B.presentation.pairing.matching (B.seam m))) =
    linearTorusDiffeomorph (torusUnit (linearTorusDiffeomorph
      (torusUnit (B.presentation.pairing.matching (B.seam m)))))
  rw [torusUnit_linearTorusDiffeomorph]

def chartPolar (p : ℕ) [NeZero p] :
    PartialDiffeomorph PlaneCircleModel signedCollarModel (ℂ × Circle) (Torus × ℝ) ∞ where
  toFun y := ((unitOf y.1, y.2), seamDepth p ‖3 * y.1‖)
  invFun x := ((seamRadius p x.2 / 3) • (x.1.1 : ℂ), x.1.2)
  source := {y | y.1 ≠ 0}
  target := {x | -2 < x.2}
  map_source' y hy := by
    change -2 < 2 * ((‖3 * y.1‖ / 3) ^ p - 1)
    have hp : 0 < (‖3 * y.1‖ / 3) ^ p :=
      pow_pos (div_pos (norm_pos_iff.mpr (mul_ne_zero (by norm_num) hy)) (by norm_num)) p
    linarith
  map_target' x hx := by
    exact smul_ne_zero (div_ne_zero (seamRadius_pos p hx).ne' (by norm_num))
      (Circle.coe_ne_zero x.1.1)
  left_inv' y hy := by
    clear hy
    change ((seamRadius p (seamDepth p ‖3 * y.1‖) / 3) • (unitOf y.1 : ℂ), y.2) = y
    rw [seamRadius_seamDepth p (norm_nonneg _)]
    have he : ‖3 * y.1‖ / 3 = ‖y.1‖ := by simp
    rw [he, norm_smul_unitOf]
  right_inv' x hx := by
    change ((unitOf ((seamRadius p x.2 / 3) • (x.1.1 : ℂ)), x.1.2),
      seamDepth p ‖3 * ((seamRadius p x.2 / 3) • (x.1.1 : ℂ))‖) = x
    rw [unitOf_smul (div_pos (seamRadius_pos p hx) (by norm_num))]
    have hn : ‖3 * ((seamRadius p x.2 / 3) • (x.1.1 : ℂ))‖ = seamRadius p x.2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_smul, Circle.norm_coe, mul_one,
        Real.norm_of_nonneg (div_nonneg (seamRadius_pos p hx).le (by norm_num))]
      ring
    rw [hn, seamDepth_seamRadius p hx]
  open_source := isOpen_ne_fun continuous_fst continuous_const
  open_target := isOpen_lt continuous_const continuous_snd
  contMDiffOn_toFun := by
    intro y hy
    have hv : ContMDiffAt PlaneCircleModel (𝓡 1) ∞ (fun y : ℂ × Circle => unitOf y.1) y :=
      (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hy)).comp y contMDiffAt_fst
    have hd : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞ (fun y : ℂ × Circle => 3 * y.1) y :=
      ((contDiff_const.mul contDiff_id).contMDiff).contMDiffAt.comp y contMDiffAt_fst
    have hn := (contDiffAt_norm ℝ (mul_ne_zero (by norm_num) hy)).contMDiffAt.comp y hd
    exact ((hv.prodMk contMDiffAt_snd).prodMk
      ((contDiff_seamDepth p).contMDiff.contMDiffAt.comp y hn)).contMDiffWithinAt
  contMDiffOn_invFun := by
    intro x hx
    have hr : ContMDiffAt signedCollarModel 𝓘(ℝ, ℝ) ∞
        (fun x : Torus × ℝ => seamRadius p x.2 / 3) x :=
      ((contDiffAt_seamRadius p hx).div_const 3).contMDiffAt.comp x contMDiffAt_snd
    have hc : ContMDiffAt signedCollarModel 𝓘(ℝ, ℂ) ∞
        (fun x : Torus × ℝ => (x.1.1 : ℂ)) x :=
      contMDiff_circle_coe.contMDiffAt.comp x (contMDiffAt_fst.comp x contMDiffAt_fst)
    have hm : ContMDiff 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, ℂ) ∞
        (fun z : ℝ × ℂ => z.1 • z.2) := (contDiff_fst.smul contDiff_snd).contMDiff
    exact ((hm.contMDiffAt.comp x (hr.prodMk_space hc)).prodMk
      (contMDiffAt_snd.comp x contMDiffAt_fst)).contMDiffWithinAt

instance SeifertData.chartSlopeNeZero (d : SeifertData) (m : Fin d.fillingCount) :
    NeZero (d.fillingSlope m).1.natAbs := ⟨by
  intro h
  have hs := d.fillingSlope_fst_pos m
  have hz := Int.natAbs_eq_zero.mp h
  omega⟩

theorem SeifertBlock.exists_normalized_solid_germ {W : CompactCarrier.{u}}
    {d : SeifertData} (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    ∃ (a b : ℤ) (C : GL (Fin 2) ℤ) (δ : ℝ), 0 < δ ∧
      (d.fillingSlope m).1 * b - a * (d.fillingSlope m).2 = 1 ∧
      ((torusUnit (B.presentation.pairing.matching (B.seam m)) * C : GL (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) =
          !![-(d.fillingSlope m).1, a; -(d.fillingSlope m).2, b] ∧
      ∃ Θ : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
        B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece (some m)),
        ∀ j t s, (t, s) ∈ halfCollarSource → s.val 0 < δ →
          B.presentation.pieceCollar (B.piece (some m)) ((B.solid m).port j)
            (linearTorusMap C t, s) =
            Θ ((discPlanarBase (d.fillingSlope m).1.natAbs).collar j (t.1, s), t.2) := by
  obtain ⟨a, b, C, Φ, hab, hC, hΦ⟩ := B.exists_normalized_fillingMatrix m
  obtain ⟨δ, hδ, Θ, hΘ⟩ := (B.solid m).exists_basis_germ
    (d.fillingSlope m).1.natAbs C Φ hΦ
  exact ⟨a, b, C, δ, hδ, hab, hC, Θ, hΘ⟩


def chartDiscScale : ℂ ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ PlaneLift.{u} where
  toFun z := ULift.up (3 * z)
  invFun w := w.down / 3
  left_inv z := by change 3 * z / 3 = z; ring
  right_inv w := by apply ULift.ext; change 3 * (w.down / 3) = w.down; ring
  contMDiff_toFun := contMDiff_planeLift_up.comp (contDiff_const.mul contDiff_id).contMDiff
  contMDiff_invFun := (contDiff_id.div_const 3).contMDiff.comp contMDiff_planeLift_down

def chartDiscClip (z : ℂ) : discSet.{u} :=
  ⟨ULift.up (3 * (if ‖z‖ ≤ 1 then z else (unitOf z : ℂ))), by
    rw [mem_discSet_iff]
    by_cases hz : ‖z‖ ≤ 1
    · simp only [hz, ite_true, norm_mul, Complex.norm_ofNat]
      linarith
    · simp [hz]⟩

theorem chartDiscClip_val (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (chartDiscClip.{u} z).val = chartDiscScale z := by
  simp only [chartDiscClip, hz, ite_true]
  rfl

theorem chartDiscClip_rawInterior (z : ℂ) (hz : ‖z‖ < 1) :
    (chartDiscClip.{u} z).val ∈ interior discSet := by
  have hn : ‖(chartDiscClip.{u} z).val.down‖ < 3 := by
    rw [chartDiscClip_val z hz.le]
    change ‖3 * z‖ < 3
    simp only [norm_mul, Complex.norm_ofNat]
    linarith
  have ho : IsOpen {w : PlaneLift.{u} | ‖w.down‖ < 3} :=
    isOpen_lt (continuous_norm.comp continuous_uliftDown) continuous_const
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (ho.mem_nhds hn)
  intro w hw
  exact (mem_discSet_iff w).mpr hw.le

theorem chartDiscClip_local {z : ℂ} (hz : ‖z‖ < 1) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) (𝓡∂ 2) ∞ chartDiscClip.{u} z := by
  apply discAtlas.isLocalDiffeomorphAt_of_subtype_val (chartDiscClip_rawInterior z hz)
  apply IsLocalDiffeomorphAt.of_eventuallyEq ?_ (chartDiscScale.isLocalDiffeomorph z)
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
  exact chartDiscClip_val w hw.le

def chartCoreMap {W : CompactCarrier.{u}} (T : TorusPresentation W)
    (i : Fin T.components.count)
    (Θ : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), T.cutCarrier.model⟯
      T.components.piece i) (y : ℂ × Circle) : W.Carrier :=
  T.cutMap (Θ (chartDiscClip y.1, y.2)).val

theorem chartCoreMap_local {W : CompactCarrier.{u}} (T : TorusPresentation W)
    (i : Fin T.components.count)
    (Θ : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), T.cutCarrier.model⟯
      T.components.piece i) {y : ℂ × Circle} (hy : ‖y.1‖ < 1) :
    IsLocalDiffeomorphAt PlaneCircleModel W.model ∞ (chartCoreMap T i Θ) y := by
  have hd := (chartDiscClip_local hy).prodMap
    ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph y.2)
  have hΘ := Θ.isLocalDiffeomorph (chartDiscClip y.1, y.2)
  have hval := isLocalDiffeomorph_subtype_val
    (I := T.cutCarrier.model) (T.components.piece i) (Θ (chartDiscClip y.1, y.2))
  have hc := (hd.comp (K := T.cutCarrier.model) (P := T.components.piece i) hΘ).comp
    (K := T.cutCarrier.model) (P := T.cutCarrier.Carrier) hval
  have hi := (hc.isInteriorPoint_iff (by simp)).mp BoundarylessManifold.isInteriorPoint
  exact hc.comp (K := W.model) (P := W.Carrier) (T.isLocalDiffeomorphAt_cutMap hi)


theorem chartCoreMap_eq_seam {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (m : Fin d.fillingCount) (C : GL (Fin 2) ℤ)
    (δ : ℝ) (Θ : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece (some m)))
    (hg : ∀ j t s, (t, s) ∈ halfCollarSource → s.val 0 < δ →
      B.presentation.pieceCollar (B.piece (some m)) ((B.solid m).port j)
        (linearTorusMap C t, s) =
        Θ ((discPlanarBase (d.fillingSlope m).1.natAbs).collar j (t.1, s), t.2))
    (y : ℂ × Circle) (hy : ‖y.1‖ ≤ 1)
    (hδ : -seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < δ)
    (h1 : -seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1) :
    chartCoreMap B.presentation (B.piece (some m)) Θ y =
      B.presentation.seam (B.seam m) (linearTorusMap C (unitOf y.1, y.2),
        seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖) := by
  let p := (d.fillingSlope m).1.natAbs
  let σ := -seamDepth p ‖3 * y.1‖
  have hs0 : 0 ≤ σ := by
    apply neg_nonneg.mpr
    apply seamDepth_nonpos p (norm_nonneg _)
    simp only [norm_mul, Complex.norm_ofNat]
    linarith
  let s : EuclideanHalfSpace 1 := halfPoint σ hs0
  let t : Torus := (unitOf y.1, y.2)
  have hs : (t, s) ∈ halfCollarSource := h1
  have hb : (discPlanarBase p).collar 0 (t.1, s) = chartDiscClip.{u} y.1 := by
    apply Subtype.ext
    apply ULift.ext
    change (discCollarMap.{u} p (t.1, s)).val.down = (chartDiscClip.{u} y.1).val.down
    rw [discCollarMap_val p (show (t.1, s) ∈ circleCollarSource from h1),
      chartDiscClip_val y.1 hy]
    change seamRadius p (-σ) • (unitOf y.1 : ℂ) = 3 * y.1
    dsimp [σ]
    rw [neg_neg, seamRadius_seamDepth p (norm_nonneg _)]
    rw [norm_mul, Complex.norm_ofNat]
    change (3 * ‖y.1‖ : ℝ) • (unitOf y.1 : ℂ) = 3 * y.1
    rw [mul_smul, norm_smul_unitOf]
    simp [Complex.real_smul]
  change B.presentation.cutMap (Θ (chartDiscClip y.1, y.2)).val = _
  rw [← hb]
  have hΘ := hg 0 t s hs hδ
  rw [← hΘ, TorusPresentation.pieceCollar_apply _ _ _
    (show (linearTorusMap C t, s) ∈ halfCollarSource from h1)]
  rw [B.solid_port]
  change B.presentation.cutMap (B.presentation.pairing.leftCollar (B.seam m)
    (linearTorusMap C t, s)) = _
  rw [B.presentation.cutMap_leftCollar (B.seam m) (show
    (linearTorusMap C t, s) ∈ halfCollarSource from h1)]
  change B.presentation.seam (B.seam m) (linearTorusMap C t, -σ) = _
  dsimp [σ, t]
  rw [neg_neg]


namespace SeifertBlock
variable {W : CompactCarrier.{u}} {d : SeifertData} (B : SeifertBlock W d)
variable (m : Fin d.fillingCount) (C : GL (Fin 2) ℤ)
variable (Θ : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
  B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece (some m)))

open Classical in
def chartTubeMap (y : ℂ × Circle) : W.Carrier :=
  if ‖y.1‖ ≤ 1 then chartCoreMap B.presentation (B.piece (some m)) Θ y else
    B.presentation.seam (B.seam m) (linearTorusMap C (unitOf y.1, y.2),
      seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖)

variable (δ : ℝ)
variable (hg : ∀ j t s, (t, s) ∈ halfCollarSource → s.val 0 < δ →
  B.presentation.pieceCollar (B.piece (some m)) ((B.solid m).port j)
    (linearTorusMap C t, s) =
    Θ ((discPlanarBase (d.fillingSlope m).1.natAbs).collar j (t.1, s), t.2))

include hg in
theorem chartTubeMap_eq_seam (y : ℂ × Circle)
    (hδ : -seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < δ)
    (h1 : -seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1) :
    B.chartTubeMap m C Θ y = B.presentation.seam (B.seam m)
      (linearTorusMap C (unitOf y.1, y.2), seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖) := by
  by_cases hy : ‖y.1‖ ≤ 1
  · rw [chartTubeMap, ite_eq_left hy]
    exact chartCoreMap_eq_seam B m C δ Θ hg y hy hδ h1
  · rw [chartTubeMap, ite_eq_right hy]

theorem chartTubeMap_coreLocal {y : ℂ × Circle} (hy : ‖y.1‖ < 1) :
    IsLocalDiffeomorphAt PlaneCircleModel W.model ∞ (B.chartTubeMap m C Θ) y := by
  apply IsLocalDiffeomorphAt.of_eventuallyEq ?_ (chartCoreMap_local B.presentation
    (B.piece (some m)) Θ hy)
  filter_upwards [(isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).mem_nhds hy]
    with z hz
  exact ite_eq_left hz.le

include hg in
theorem chartTubeMap_seamLocal {y : ℂ × Circle}
    (hδ : -seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < δ)
    (h1 : -seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1)
    (hu : seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1) :
    IsLocalDiffeomorphAt PlaneCircleModel W.model ∞ (B.chartTubeMap m C Θ) y := by
  let p := (d.fillingSlope m).1.natAbs
  have hne : y.1 ≠ 0 := by
    intro h
    have hz := ne_zero_of_neg_seamDepth_lt p h1
    exact hz (by simp [h])
  have hpolar := (chartPolar p).isLocalDiffeomorphAt PlaneCircleModel signedCollarModel ∞ hne
  let e := (linearTorusDiffeomorph C).prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  have he := e.isLocalDiffeomorph (chartPolar p y)
  have hseam := (B.presentation.seam (B.seam m)).isLocalDiffeomorphAt
    signedCollarModel W.model ∞ (x := e (chartPolar p y)) (by
      rw [B.presentation.seam_source]
      exact ⟨by change -1 < seamDepth p ‖3 * y.1‖; linarith, hu⟩)
  have hl := (hpolar.comp (K := signedCollarModel) (P := Torus × ℝ) he).comp
    (K := W.model) (P := W.Carrier) hseam
  apply IsLocalDiffeomorphAt.of_eventuallyEq ?_ hl
  have hd : Continuous (fun z : ℂ × Circle => seamDepth p ‖3 * z.1‖) :=
    (contDiff_seamDepth p).continuous.comp
      (continuous_norm.comp (continuous_const.mul continuous_fst))
  filter_upwards [((isOpen_lt hd.neg continuous_const).inter
    (isOpen_lt hd.neg continuous_const)).mem_nhds ⟨hδ, h1⟩] with z hz
  exact B.chartTubeMap_eq_seam m C Θ δ hg z hz.1 hz.2


include hg in
theorem chartTubeMap_local {y : ℂ × Circle} (hδ : 0 < δ)
    (hy : seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1) :
    IsLocalDiffeomorphAt PlaneCircleModel W.model ∞ (B.chartTubeMap m C Θ) y := by
  by_cases hc : ‖y.1‖ < 1
  · exact B.chartTubeMap_coreLocal m C Θ hc
  · have hn : 0 ≤ seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ := by
      change 0 ≤ 2 * ((‖3 * y.1‖ / 3) ^ (d.fillingSlope m).1.natAbs - 1)
      have he : ‖3 * y.1‖ / 3 = ‖y.1‖ := by simp
      rw [he]
      have hp : 1 ≤ ‖y.1‖ ^ (d.fillingSlope m).1.natAbs := one_le_pow₀ (not_lt.mp hc)
      linarith
    exact B.chartTubeMap_seamLocal m C Θ δ hg (by linarith) (by linarith) hy


theorem rightPiece_eq : B.presentation.rightPiece (B.seam m) = B.piece none := by
  have h := (B.product.port (B.port (.inr m))).property
  rw [B.filled_port] at h
  exact h

theorem leftPiece_eq : B.presentation.leftPiece (B.seam m) = B.piece (some m) := by
  have h := ((B.solid m).port 0).property
  rw [B.solid_port] at h
  exact h

theorem cutMap_injective_solid :
    Function.Injective (fun x : B.presentation.components.piece (B.piece (some m)) =>
      B.presentation.cutMap x.val) := by
  intro x y h
  apply Subtype.ext
  rcases B.presentation.cutMap_eq_cases h with he | ⟨k, hk⟩
  · exact he
  · have hr : B.presentation.rightPiece k = B.piece none := by
      obtain ⟨n, rfl⟩ := B.seam.surjective k
      exact B.rightPiece_eq n
    rcases hk with ⟨hl, hr'⟩ | ⟨hr', hl⟩
    · have hp := B.presentation.right_owned k hr'
      rw [hr] at hp
      have he := B.presentation.piece_eq_of_mem y.property hp
      have hn := B.piece.injective he
      exact False.elim (Option.some_ne_none m hn)
    · have hp := B.presentation.right_owned k hr'
      rw [hr] at hp
      have he := B.presentation.piece_eq_of_mem x.property hp
      have hn := B.piece.injective he
      exact False.elim (Option.some_ne_none m hn)

theorem chartCoreMap_injective {x y : ℂ × Circle}
    (hx : ‖x.1‖ ≤ 1) (hy : ‖y.1‖ ≤ 1)
    (h : chartCoreMap B.presentation (B.piece (some m)) Θ x =
      chartCoreMap B.presentation (B.piece (some m)) Θ y) : x = y := by
  have he := B.cutMap_injective_solid m h
  have hΘ := Θ.injective he
  apply Prod.ext
  · have hz := congrArg (fun q : discSet.{u} × Circle => q.1.val.down) hΘ
    rw [chartDiscClip_val x.1 hx, chartDiscClip_val y.1 hy] at hz
    exact mul_left_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) hz
  · exact congrArg (fun q : discSet.{u} × Circle => q.2) hΘ


theorem chartCoreMap_not_mem_productRegion (y : ℂ × Circle) :
    chartCoreMap B.presentation (B.piece (some m)) Θ y ∉ B.product.chartProductRegion := by
  intro hp
  obtain ⟨x, hx⟩ := (B.product.chartProductRegion_mem_iff _).mp hp
  have he := B.presentation.eq_of_cutMap_eq_of_interior x.property.2 hx
  have hi := B.presentation.piece_eq_of_mem x.property.1 (he.symm ▸
    (Θ (chartDiscClip y.1, y.2)).property)
  have hn := B.piece.injective hi
  exact Option.some_ne_none m hn.symm

theorem chartTubeMap_positive_region (y : ℂ × Circle) (hy : 1 < ‖y.1‖)
    (hu : seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1) :
    B.chartTubeMap m C Θ y ∈ B.product.chartProductRegion := by
  let p := (d.fillingSlope m).1.natAbs
  let σ := seamDepth p ‖3 * y.1‖
  have hs0 : 0 < σ := by
    change 0 < 2 * ((‖3 * y.1‖ / 3) ^ p - 1)
    have he : ‖3 * y.1‖ / 3 = ‖y.1‖ := by simp
    rw [he]
    have hp := one_lt_pow₀ hy (NeZero.ne p)
    linarith
  let t : Torus := linearTorusMap C (unitOf y.1, y.2)
  let q : Torus × EuclideanHalfSpace 1 :=
    (B.presentation.pairing.matching (B.seam m) t, halfPoint σ hs0.le)
  have hq : q ∈ halfCollarSource := hu
  let z := B.presentation.pieceCollar (B.piece none)
    (B.product.port (B.port (.inr m))) q
  have hlocal := (B.presentation.pieceCollar (B.piece none)
    (B.product.port (B.port (.inr m)))).isLocalDiffeomorphAt
      halfCollarModel B.presentation.cutCarrier.model ∞ (by
        rw [B.presentation.pieceCollar_source]
        exact hq)
  have hi : B.presentation.cutCarrier.model.IsInteriorPoint z.val :=
    ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mp
      ((hlocal.isInteriorPoint_iff (by simp)).mp (halfCollarModel_isInteriorPoint hs0))
  apply (B.product.chartProductRegion_mem_iff _).mpr
  refine ⟨⟨z.val, z.property, hi⟩, ?_⟩
  rw [TorusPresentation.pieceCollar_apply _ _ _ hq, B.filled_port]
  change B.presentation.cutMap (B.presentation.pairing.rightCollar (B.seam m) q) = _
  rw [B.presentation.cutMap_rightCollar (B.seam m) hq]
  change B.presentation.seam (B.seam m)
    ((B.presentation.pairing.matching (B.seam m)).symm
      (B.presentation.pairing.matching (B.seam m) t), σ) = _
  rw [Diffeomorph.symm_apply_apply, chartTubeMap, ite_eq_right (not_le.mpr hy)]


theorem chartTubeMap_outer_injective {x y : ℂ × Circle}
    (hx : 1 < ‖x.1‖) (hy : 1 < ‖y.1‖)
    (hxu : seamDepth (d.fillingSlope m).1.natAbs ‖3 * x.1‖ < 1)
    (hyu : seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1)
    (h : B.chartTubeMap m C Θ x = B.chartTubeMap m C Θ y) : x = y := by
  let p := (d.fillingSlope m).1.natAbs
  have hn (z : ℂ × Circle) (hz : 1 < ‖z.1‖) : 0 < seamDepth p ‖3 * z.1‖ := by
    change 0 < 2 * ((‖3 * z.1‖ / 3) ^ p - 1)
    have he : ‖3 * z.1‖ / 3 = ‖z.1‖ := by simp
    rw [he]
    have hp := one_lt_pow₀ hz (NeZero.ne p)
    linarith
  let e := (linearTorusDiffeomorph C).prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  have hsx : e (chartPolar p x) ∈ (B.presentation.seam (B.seam m)).source := by
    rw [B.presentation.seam_source]
    exact ⟨by change -1 < seamDepth p ‖3 * x.1‖; linarith [hn x hx], hxu⟩
  have hsy : e (chartPolar p y) ∈ (B.presentation.seam (B.seam m)).source := by
    rw [B.presentation.seam_source]
    exact ⟨by change -1 < seamDepth p ‖3 * y.1‖; linarith [hn y hy], hyu⟩
  rw [chartTubeMap, ite_eq_right (not_le.mpr hx),
    chartTubeMap, ite_eq_right (not_le.mpr hy)] at h
  have hp := e.injective ((B.presentation.seam (B.seam m)).injOn hsx hsy h)
  exact (chartPolar p).injOn (norm_pos_iff.mp (by linarith))
    (norm_pos_iff.mp (by linarith)) hp

theorem chartTubeMap_injOn :
    InjOn (B.chartTubeMap m C Θ)
      {y : ℂ × Circle | seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1} := by
  intro x hx y hy h
  by_cases hxc : ‖x.1‖ ≤ 1
  · by_cases hyc : ‖y.1‖ ≤ 1
    · rw [chartTubeMap, ite_eq_left hxc, chartTubeMap, ite_eq_left hyc] at h
      exact B.chartCoreMap_injective m Θ hxc hyc h
    · have hp := B.chartTubeMap_positive_region m C Θ y (not_le.mp hyc) hy
      rw [← h, chartTubeMap, ite_eq_left hxc] at hp
      exact False.elim (B.chartCoreMap_not_mem_productRegion m Θ x hp)
  · by_cases hyc : ‖y.1‖ ≤ 1
    · have hp := B.chartTubeMap_positive_region m C Θ x (not_le.mp hxc) hx
      rw [h, chartTubeMap, ite_eq_left hyc] at hp
      exact False.elim (B.chartCoreMap_not_mem_productRegion m Θ y hp)
    · exact B.chartTubeMap_outer_injective m C Θ (not_le.mp hxc) (not_le.mp hyc) hx hy h

include hg in
theorem exists_chartTube (hδ : 0 < δ) :
    ∃ Γ : PartialDiffeomorph PlaneCircleModel W.model (ℂ × Circle) W.Carrier ∞,
      Γ.source = {y : ℂ × Circle | seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1} ∧
      Γ.target = B.chartTubeMap m C Θ '' Γ.source ∧ (Γ : ℂ × Circle → W.Carrier) =
        B.chartTubeMap m C Θ := by
  have ho : IsOpen {y : ℂ × Circle | seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1} :=
    isOpen_lt ((contDiff_seamDepth (d.fillingSlope m).1.natAbs).continuous.comp
      (continuous_norm.comp (continuous_const.mul continuous_fst))) continuous_const
  have hl : IsLocalDiffeomorphOn PlaneCircleModel W.model ∞ (B.chartTubeMap m C Θ)
      {y : ℂ × Circle | seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1} := by
    intro y
    exact B.chartTubeMap_local m C Θ δ hg hδ y.property
  obtain ⟨Γ, hsource, htarget, hmap⟩ := hl.exists_partialDiffeomorph_of_injOn ho
    ⟨(0, 1), by norm_num [seamDepth, zero_pow (NeZero.ne (d.fillingSlope m).1.natAbs)]⟩
    (B.chartTubeMap_injOn m C Θ)
  exact ⟨Γ, hsource, by rw [hsource]; exact htarget, hmap⟩

end SeifertBlock

def chartRadialPlanarBase (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3) : PlanarBase.{u} k := by
  by_cases h1 : k = 1
  · rw [h1]
    exact (discPlanarBase 1).shrink (δ := 1 / 6) (by norm_num) (by norm_num)
  · exact planarBase k (by
      rcases hk with h | h
      · exact (h1 h).elim
      · exact h)

theorem chartRadialPlanarBase_formula (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3)
    (j : Fin k) (t : Circle) (s : EuclideanHalfSpace 1) (hs : s.val 0 < 1) :
    (chartRadialPlanarBase.{u} k hk).embedding ((chartRadialPlanarBase k hk).collar j (t, s)) =
      planarCollarFormula k j ((t : ℂ), s.val 0) := by
  rcases hk with h1 | h2 | h3
  · subst k
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    change (discCollarMap.{u} 1 (t, halfSpaceScale (δ := 1 / 6) (by norm_num) s)).val.down = _
    rw [discCollarMap_val 1 (show
      (t, halfSpaceScale (δ := 1 / 6) (by norm_num) s) ∈ circleCollarSource from
        halfSpaceScale_mem (δ := 1 / 6) (by norm_num) (by norm_num) hs)]
    rw [halfSpaceScale_coord]
    simp only [seamRadius, Nat.cast_one, inv_one, Real.rpow_one, planarCollarFormula,
      planarCenter, planarRadius, planarSign, planarTwist, Fin.val_zero, ite_true]
    simp only [Complex.real_smul]
    push_cast
    ring
  · subst k
    exact planarCollarMap_val.{u} (Or.inl rfl) j hs
  · subst k
    exact planarCollarMap_val.{u} (Or.inr rfl) j hs


theorem PlanarBase.chartInteriorDiffeomorph_apply {k : ℕ} (P : PlanarBase.{u} k)
    (x : chartBaseInterior P) : (P.chartInteriorDiffeomorph x).val = P.embedding x.val := by
  rfl

theorem ProductFibredPiece.chartPieceInteriorDiffeomorph_apply {W : CompactCarrier.{u}}
    {T : TorusPresentation W} {i : Fin T.components.count} {k : ℕ}
    (P : ProductFibredPiece T i k) (x : chartBaseInterior P.base × Circle) :
    (P.chartPieceInteriorDiffeomorph (P.base.chartInteriorDiffeomorph x.1, x.2)).val =
      (P.trivialization (x.1.val, x.2)).val := by
  change (P.trivialization
    (((P.base.chartInteriorDiffeomorph).symm (P.base.chartInteriorDiffeomorph x.1)).val,
      x.2)).val = _
  rw [Diffeomorph.symm_apply_apply]

theorem ProductFibredPiece.chartProductDiffeomorph_applyInterior {W : CompactCarrier.{u}}
    {T : TorusPresentation W} {i : Fin T.components.count} {k : ℕ}
    (P : ProductFibredPiece T i k) (x : chartBaseInterior P.base × Circle) :
    (P.chartProductDiffeomorph (P.base.chartInteriorDiffeomorph x.1, x.2) : W.Carrier) =
      T.cutMap (P.trivialization (x.1.val, x.2)).val := by
  rw [P.chartProductDiffeomorph_apply, P.chartPieceInteriorDiffeomorph_apply]

theorem PlanarBase.collar_isInteriorPoint {k : ℕ} (P : PlanarBase.{u} k)
    (j : Fin k) (t : Circle) (s : EuclideanHalfSpace 1) (hs0 : 0 < s.val 0) (hs1 : s.val 0 < 1) :
    (SurfaceModel.model P.surface.kind).IsInteriorPoint (P.collar j (t, s)) := by
  have h1 : (𝓡∂ 1).IsInteriorPoint s := by
    rw [ModelWithCorners.IsInteriorPoint, interior_range_modelWithCornersEuclideanHalfSpace]
    exact hs0
  have h2 : (𝓡 1).IsInteriorPoint t := BoundarylessManifold.isInteriorPoint
  have hi : circleCollarModel.IsInteriorPoint (t, s) := by
    change (t, s) ∈ circleCollarModel.interior (Circle × EuclideanHalfSpace 1)
    rw [ModelWithCorners.interior_prod]
    exact ⟨h2, h1⟩
  have hs : (t, s) ∈ (P.collar j).source := P.source_eq j ▸ hs1
  exact (((P.collar j).isLocalDiffeomorphAt circleCollarModel
    (SurfaceModel.model P.surface.kind) ∞ hs).isInteriorPoint_iff (by simp)).mp hi

theorem seamModel_eq_planarCollarFormula (d : SeifertData) (m : Fin d.fillingCount)
    (j : Fin d.k) (A : GL (Fin 2) ℤ) (y : ℂ × Circle) :
    seamModel d m j A y =
      (planarCollarFormula d.k j
        ((linearTorusMap A (unitOf y.1, y.2)).1,
          seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖),
        (linearTorusMap A (unitOf y.1, y.2)).2) := by
  apply Prod.ext
  · simp only [seamModel, planarCollarFormula, planarSign, planarTwist, seamDepth,
      norm_mul, Complex.norm_ofNat, mul_div_cancel_left₀ _ (by norm_num : (3 : ℝ) ≠ 0),
      Complex.real_smul]
    push_cast
    ring
  · rfl

def ProductFibredPiece.chartGermProductPiece {W : CompactCarrier.{u}}
    {T : TorusPresentation W} {i : Fin T.components.count} {k : ℕ}
    (P : ProductFibredPiece T i k) (Q : PlanarBase.{u} k) (δ : ℝ)
    (Θ : (Q.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model Q.surface.kind).prod (𝓡 1),
      T.cutCarrier.model⟯ T.components.piece i)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hg : ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      T.pieceCollar i (P.port j) p = Θ (Q.collar j (p.1.1, p.2), p.1.2)) :
    ProductFibredPiece (T.shrink hδ hδ1) i k :=
  T.shrinkPiece i Q P.port Θ hδ hδ1 hg

theorem ProductFibredPiece.chartGermProductRegion_eq {W : CompactCarrier.{u}}
    {T : TorusPresentation W} {i : Fin T.components.count} {k : ℕ}
    (P : ProductFibredPiece T i k) (Q : PlanarBase.{u} k) (δ : ℝ)
    (Θ : (Q.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model Q.surface.kind).prod (𝓡 1),
      T.cutCarrier.model⟯ T.components.piece i)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hg : ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      T.pieceCollar i (P.port j) p = Θ (Q.collar j (p.1.1, p.2), p.1.2)) :
    (P.chartGermProductPiece Q δ Θ hδ hδ1 hg).chartProductRegion = P.chartProductRegion := by
  apply TopologicalSpace.Opens.ext
  ext y
  exact ((P.chartGermProductPiece Q δ Θ hδ hδ1 hg).chartProductRegion_mem_iff y).trans
    (P.chartProductRegion_mem_iff y).symm

theorem ProductFibredPiece.chartGermProduct_apply {W : CompactCarrier.{u}}
    {T : TorusPresentation W} {i : Fin T.components.count} {k : ℕ}
    (P : ProductFibredPiece T i k) (Q : PlanarBase.{u} k) (δ : ℝ)
    (Θ : (Q.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model Q.surface.kind).prod (𝓡 1),
      T.cutCarrier.model⟯ T.components.piece i)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hg : ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      T.pieceCollar i (P.port j) p = Θ (Q.collar j (p.1.1, p.2), p.1.2))
    (j : Fin k) (t : Torus) (s : EuclideanHalfSpace 1)
    (hs0 : 0 < s.val 0) (hs1 : s.val 0 < 1) (hsδ : s.val 0 < δ) :
    let R := P.chartGermProductPiece Q δ Θ hδ hδ1 hg
    let x : chartBaseInterior R.base :=
      ⟨Q.collar j (t.1, s), Q.collar_isInteriorPoint j t.1 s hs0 hs1⟩
    (R.chartProductDiffeomorph (R.base.chartInteriorDiffeomorph x, t.2) : W.Carrier) =
      T.cutMap (T.pieceCollar i (P.port j) (t, s)).val := by
  dsimp only
  have ha := (P.chartGermProductPiece Q δ Θ hδ hδ1 hg).chartProductDiffeomorph_applyInterior
    (⟨Q.collar j (t.1, s), Q.collar_isInteriorPoint j t.1 s hs0 hs1⟩, t.2)
  exact ha.trans (congrArg (fun x : T.components.piece i => T.cutMap x.val)
    (hg j (t, s) hs1 hsδ).symm)

theorem chartLinearMatching_mul {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (m : Fin d.fillingCount) (C : GL (Fin 2) ℤ)
    (h : B.presentation.pairing.matching (B.seam m) =
      linearTorusDiffeomorph (torusUnit (B.presentation.pairing.matching (B.seam m))))
    (t : Torus) :
    B.presentation.pairing.matching (B.seam m) (linearTorusMap C t) =
      linearTorusMap (torusUnit (B.presentation.pairing.matching (B.seam m)) * C) t := by
  conv_lhs => rw [h]
  exact (linearTorusMap_mul _ _ t).symm

theorem SeifertBlock.chartGermProduct_transition {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (m : Fin d.fillingCount) (C : GL (Fin 2) ℤ)
    (Θs : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece (some m)))
    (h : B.presentation.pairing.matching (B.seam m) =
      linearTorusDiffeomorph (torusUnit (B.presentation.pairing.matching (B.seam m))))
    (hk : d.k = 1 ∨ d.k = 2 ∨ d.k = 3) (δ : ℝ)
    (Θ : ((chartRadialPlanarBase.{u} d.k hk).surface.Carrier × Circle)
      ≃ₘ⟮(SurfaceModel.model (chartRadialPlanarBase d.k hk).surface.kind).prod (𝓡 1),
      B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece none))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hg : ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      B.presentation.pieceCollar (B.piece none) (B.product.port j) p =
        Θ ((chartRadialPlanarBase d.k hk).collar j (p.1.1, p.2), p.1.2))
    (y : ℂ × Circle) (hy : 1 < ‖y.1‖)
    (hyδ : seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < δ) :
    let R := B.product.chartGermProductPiece (chartRadialPlanarBase d.k hk) δ Θ hδ hδ1 hg
    let A := torusUnit (B.presentation.pairing.matching (B.seam m)) * C
    ∃ hz : (seamModel d m (B.port (.inr m)) A y).1 ∈ planarOpen d.k,
      B.chartTubeMap m C Θs y = (R.chartProductDiffeomorph
        (⟨(seamModel d m (B.port (.inr m)) A y).1, hz⟩,
          (seamModel d m (B.port (.inr m)) A y).2) : W.Carrier) := by
  let Q := chartRadialPlanarBase.{u} d.k hk
  let R := B.product.chartGermProductPiece Q δ Θ hδ hδ1 hg
  let A := torusUnit (B.presentation.pairing.matching (B.seam m)) * C
  let σ := seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖
  have hs0 : 0 < σ := by
    change 0 < 2 * ((‖3 * y.1‖ / 3) ^ (d.fillingSlope m).1.natAbs - 1)
    have he : ‖3 * y.1‖ / 3 = ‖y.1‖ := by simp
    rw [he]
    have hp := one_lt_pow₀ hy (NeZero.ne (d.fillingSlope m).1.natAbs)
    linarith
  have hs1 : σ < 1 := lt_of_lt_of_le hyδ hδ1
  let t := linearTorusMap A (unitOf y.1, y.2)
  let v := halfPoint σ hs0.le
  let x : chartBaseInterior R.base :=
    ⟨Q.collar (B.port (.inr m)) (t.1, v),
      Q.collar_isInteriorPoint (B.port (.inr m)) t.1 v hs0 hs1⟩
  have he : (R.base.chartInteriorDiffeomorph x).val =
      (seamModel d m (B.port (.inr m)) A y).1 := by
    rw [PlanarBase.chartInteriorDiffeomorph_apply]
    change Q.embedding (Q.collar (B.port (.inr m)) (t.1, v)) = _
    rw [chartRadialPlanarBase_formula d.k hk (B.port (.inr m)) t.1 v hs1,
      seamModel_eq_planarCollarFormula]
    rfl
  have hcoord : (R.base.chartInteriorDiffeomorph x, t.2) =
      (⟨(seamModel d m (B.port (.inr m)) A y).1,
        he ▸ (R.base.chartInteriorDiffeomorph x).property⟩,
        (seamModel d m (B.port (.inr m)) A y).2) := by
    apply Prod.ext
    · exact Subtype.ext he
    · rfl
  refine ⟨he ▸ (R.base.chartInteriorDiffeomorph x).property, ?_⟩
  have ha := B.product.chartGermProduct_apply Q δ Θ hδ hδ1 hg
    (B.port (.inr m)) t v hs0 hs1 hyδ
  change (R.chartProductDiffeomorph (R.base.chartInteriorDiffeomorph x, t.2) : W.Carrier) =
    B.presentation.cutMap (B.presentation.pieceCollar (B.piece none)
      (B.product.port (B.port (.inr m))) (t, v)).val at ha
  rw [hcoord] at ha
  rw [TorusPresentation.pieceCollar_apply _ _ _ hs1, B.filled_port] at ha
  have ht : t = B.presentation.pairing.matching (B.seam m)
      (linearTorusMap C (unitOf y.1, y.2)) := (chartLinearMatching_mul B m C h _).symm
  rw [ht] at ha
  change (R.chartProductDiffeomorph
    (⟨(seamModel d m (B.port (.inr m)) A y).1,
      he ▸ (R.base.chartInteriorDiffeomorph x).property⟩,
      (seamModel d m (B.port (.inr m)) A y).2) : W.Carrier) =
    B.presentation.cutMap (B.presentation.pairing.rightCollar (B.seam m)
      (B.presentation.pairing.matching (B.seam m)
        (linearTorusMap C (unitOf y.1, y.2)), v)) at ha
  have hc := B.presentation.cutMap_rightCollar (B.seam m)
    (show (B.presentation.pairing.matching (B.seam m)
      (linearTorusMap C (unitOf y.1, y.2)), v) ∈ halfCollarSource from hs1)
  rw [Diffeomorph.symm_apply_apply] at hc
  have ha := ha.trans hc
  exact (show B.chartTubeMap m C Θs y =
    B.presentation.seam (B.seam m) (linearTorusMap C (unitOf y.1, y.2), σ) from
      ite_eq_right (not_le.mpr hy)).trans ha.symm

theorem SeifertData.exists_uniform_chartRadius (d : SeifertData) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ε > (0 : ℝ), ∀ m : Fin d.fillingCount, ∀ y : ℂ × Circle,
      ‖y.1‖ < 1 + ε → seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < ρ := by
  let U : Set ℝ := ⋂ m : Fin d.fillingCount,
    {r : ℝ | seamDepth (d.fillingSlope m).1.natAbs (3 * r) < ρ}
  have ho : IsOpen U := isOpen_iInter_of_finite fun m =>
    isOpen_lt ((contDiff_seamDepth (d.fillingSlope m).1.natAbs).continuous.comp
      (continuous_const.mul continuous_id)) continuous_const
  have h1 : (1 : ℝ) ∈ U := by
    apply mem_iInter.mpr
    intro m
    simpa [seamDepth] using hρ
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds h1)
  refine ⟨ε, hε, fun m y hy => ?_⟩
  by_cases hc : ‖y.1‖ ≤ 1
  · exact lt_of_le_of_lt (seamDepth_nonpos (d.fillingSlope m).1.natAbs
      (norm_nonneg _) (by simpa using hc)) hρ
  · have hb : ‖y.1‖ ∈ ball (1 : ℝ) ε := by
      rw [mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [not_le.mp hc])]
      linarith
    have hr := mem_iInter.mp (he hb) m
    simpa using hr

theorem SeifertBlock.chartCoreMap_cross {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (m n : Fin d.fillingCount) (hmn : m ≠ n)
    (Θm : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece (some m)))
    (Θn : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece (some n)))
    (x y : ℂ × Circle) :
    chartCoreMap B.presentation (B.piece (some m)) Θm x ≠
      chartCoreMap B.presentation (B.piece (some n)) Θn y := by
  intro h
  rcases B.presentation.cutMap_eq_cases h with he | ⟨k, hk⟩
  · have hi := B.presentation.piece_eq_of_mem (Θm (chartDiscClip x.1, x.2)).property
      (he.symm ▸ (Θn (chartDiscClip y.1, y.2)).property)
    exact hmn (Option.some.inj (B.piece.injective hi))
  · have hr : B.presentation.rightPiece k = B.piece none := by
      obtain ⟨a, rfl⟩ := B.seam.surjective k
      exact B.rightPiece_eq a
    rcases hk with ⟨hl, hr'⟩ | ⟨hr', hl⟩
    · have hp := B.presentation.right_owned k hr'
      rw [hr] at hp
      have hi := B.presentation.piece_eq_of_mem (Θn (chartDiscClip y.1, y.2)).property hp
      exact Option.some_ne_none n (B.piece.injective hi)
    · have hp := B.presentation.right_owned k hr'
      rw [hr] at hp
      have hi := B.presentation.piece_eq_of_mem (Θm (chartDiscClip x.1, x.2)).property hp
      exact Option.some_ne_none m (B.piece.injective hi)

theorem SeifertBlock.chartCoreMap_surjective {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (m : Fin d.fillingCount)
    (Θ : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece (some m)))
    (x : B.presentation.components.piece (B.piece (some m))) :
    ∃ y : ℂ × Circle, ‖y.1‖ ≤ 1 ∧
      chartCoreMap B.presentation (B.piece (some m)) Θ y = B.presentation.cutMap x.val := by
  let z := Θ.symm x
  let y : ℂ × Circle := (z.1.val.down / 3, z.2)
  have hn : ‖z.1.val.down‖ ≤ 3 := by
    simpa only [mem_discSet_iff] using z.1.property
  have hy : ‖y.1‖ ≤ 1 := by
    change ‖z.1.val.down / 3‖ ≤ 1
    rw [norm_div, Complex.norm_ofNat]
    linarith
  have hd : chartDiscClip.{u} y.1 = z.1 := by
    apply Subtype.ext
    apply ULift.ext
    rw [chartDiscClip_val y.1 hy]
    change 3 * (z.1.val.down / 3) = z.1.val.down
    ring
  refine ⟨y, hy, ?_⟩
  change B.presentation.cutMap (Θ (chartDiscClip y.1, y.2)).val = _
  rw [hd]
  exact congrArg (fun v : B.presentation.components.piece (B.piece (some m)) =>
    B.presentation.cutMap v.val) (Θ.apply_symm_apply x)

theorem chartDepth_pos (d : SeifertData) (m : Fin d.fillingCount)
    (y : ℂ × Circle) (hy : 1 < ‖y.1‖) :
    0 < seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ := by
  change 0 < 2 * ((‖3 * y.1‖ / 3) ^ (d.fillingSlope m).1.natAbs - 1)
  have he : ‖3 * y.1‖ / 3 = ‖y.1‖ := by simp
  rw [he]
  have hp := one_lt_pow₀ hy (NeZero.ne (d.fillingSlope m).1.natAbs)
  linarith

theorem SeifertBlock.chartTubeMap_cross {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (m n : Fin d.fillingCount) (hmn : m ≠ n)
    (Cm Cn : GL (Fin 2) ℤ)
    (Θm : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece (some m)))
    (Θn : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece (some n)))
    (x y : ℂ × Circle)
    (hx : seamDepth (d.fillingSlope m).1.natAbs ‖3 * x.1‖ < 1)
    (hy : seamDepth (d.fillingSlope n).1.natAbs ‖3 * y.1‖ < 1) :
    B.chartTubeMap m Cm Θm x ≠ B.chartTubeMap n Cn Θn y := by
  intro h
  by_cases hxc : ‖x.1‖ ≤ 1
  · by_cases hyc : ‖y.1‖ ≤ 1
    · rw [chartTubeMap, ite_eq_left hxc, chartTubeMap, ite_eq_left hyc] at h
      exact B.chartCoreMap_cross m n hmn Θm Θn x y h
    · have hp := B.chartTubeMap_positive_region n Cn Θn y (not_le.mp hyc) hy
      rw [← h, chartTubeMap, ite_eq_left hxc] at hp
      exact B.chartCoreMap_not_mem_productRegion m Θm x hp
  · by_cases hyc : ‖y.1‖ ≤ 1
    · have hp := B.chartTubeMap_positive_region m Cm Θm x (not_le.mp hxc) hx
      rw [h, chartTubeMap, ite_eq_left hyc] at hp
      exact B.chartCoreMap_not_mem_productRegion n Θn y hp
    · rw [chartTubeMap, ite_eq_right hxc, chartTubeMap, ite_eq_right hyc] at h
      have hsm : (linearTorusMap Cm (unitOf x.1, x.2),
          seamDepth (d.fillingSlope m).1.natAbs ‖3 * x.1‖) ∈
          (B.presentation.seam (B.seam m)).source := by
        rw [B.presentation.seam_source]
        exact ⟨by linarith [chartDepth_pos d m x (not_le.mp hxc)], hx⟩
      have hsn : (linearTorusMap Cn (unitOf y.1, y.2),
          seamDepth (d.fillingSlope n).1.natAbs ‖3 * y.1‖) ∈
          (B.presentation.seam (B.seam n)).source := by
        rw [B.presentation.seam_source]
        exact ⟨by linarith [chartDepth_pos d n y (not_le.mp hyc)], hy⟩
      exact (B.presentation.seam_disjoint (fun e => hmn (B.seam.injective e))).le_bot
        ⟨(B.presentation.seam (B.seam m)).map_source hsm,
          h.symm ▸ (B.presentation.seam (B.seam n)).map_source hsn⟩

theorem SeifertBlock.chartCoreCover {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d)
    (Θ : ∀ m : Fin d.fillingCount, (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece (some m)))
    (w : W.Carrier) (hw : w ∈ W.interior) :
    w ∈ B.product.chartProductRegion ∨ ∃ m y, ‖y.1‖ ≤ 1 ∧
      chartCoreMap B.presentation (B.piece (some m)) (Θ m) y = w := by
  obtain ⟨z, rfl⟩ := B.presentation.cutMap_surjective w
  obtain ⟨i, hi⟩ := mem_iUnion.mp (B.presentation.components.covers.symm ▸ mem_univ z)
  obtain ⟨o, rfl⟩ := B.piece.surjective i
  cases o with
  | some m =>
    right
    obtain ⟨y, hy, he⟩ := B.chartCoreMap_surjective m (Θ m) ⟨z, hi⟩
    exact ⟨m, y, hy, he⟩
  | none =>
    rcases B.presentation.cutCarrier.model.isInteriorPoint_or_isBoundaryPoint z with hz | hz
    · left
      exact (B.product.chartProductRegion_mem_iff _).mpr ⟨⟨z, hi, hz⟩, rfl⟩
    · obtain ⟨s, t, ht⟩ := B.presentation.exists_sideCollar_zero_eq hz
      rcases s with k | k | e
      · have hp := (B.presentation.sideCollar_zero_mem (.inl k) t).2
        rw [ht] at hp
        obtain ⟨m, rfl⟩ := B.seam.surjective k
        change z ∈ B.presentation.components.piece (B.presentation.leftPiece (B.seam m)) at hp
        rw [B.leftPiece_eq] at hp
        exact False.elim (Option.some_ne_none m
          (B.piece.injective (B.presentation.piece_eq_of_mem hi hp)).symm)
      · obtain ⟨m, rfl⟩ := B.seam.surjective k
        let v := B.presentation.pairing.leftParam (B.seam m)
          ((B.presentation.pairing.matching (B.seam m)).symm t)
        have hv : v.val ∈ B.presentation.components.piece (B.piece (some m)) := by
          have hp := B.presentation.left_owned (B.seam m) v.property
          rwa [B.leftPiece_eq] at hp
        right
        obtain ⟨y, hy, he⟩ := B.chartCoreMap_surjective m (Θ m) ⟨v.val, hv⟩
        refine ⟨m, y, hy, he.trans ?_⟩
        have hr := B.presentation.cutMap_rightCollar (B.seam m)
          (zero_mem_halfCollarSource t)
        have hl := B.presentation.cutMap_leftCollar (B.seam m)
          (zero_mem_halfCollarSource
            ((B.presentation.pairing.matching (B.seam m)).symm t))
        rw [B.presentation.pairing.left_zero] at hl
        rw [← ht]
        have hl' : B.presentation.cutMap v.val =
            B.presentation.seam (B.seam m)
              ((B.presentation.pairing.matching (B.seam m)).symm t, 0) := by
          simpa [halfZero, GC.Endpoint.halfPoint, v] using hl
        have hr' : B.presentation.cutMap (B.presentation.pairing.rightCollar (B.seam m)
            (t, halfZero)) = B.presentation.seam (B.seam m)
              ((B.presentation.pairing.matching (B.seam m)).symm t, 0) := by
          simpa [halfZero, GC.Endpoint.halfPoint] using hr
        exact hl'.trans hr'.symm
      · have he : B.presentation.cutMap z = B.presentation.external.collar e (t, halfZero) := by
          rw [← ht]
          exact B.presentation.marked_collar e (t, halfZero) (zero_mem_halfCollarSource t)
        have hb := B.presentation.external.boundary_zero e t
        rw [← he] at hb
        exact False.elim ((W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hw hb)

theorem SeifertBlock.exists_chartTube_radius {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (m : Fin d.fillingCount) (C : GL (Fin 2) ℤ)
    (δ : ℝ) (Θ : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece (some m)))
    (hg : ∀ j t s, (t, s) ∈ halfCollarSource → s.val 0 < δ →
      B.presentation.pieceCollar (B.piece (some m)) ((B.solid m).port j)
        (linearTorusMap C t, s) =
        Θ ((discPlanarBase (d.fillingSlope m).1.natAbs).collar j (t.1, s), t.2))
    (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε)
    (hdepth : ∀ y : ℂ × Circle, ‖y.1‖ < 1 + ε →
      seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1) :
    ∃ Γ : PartialDiffeomorph PlaneCircleModel W.model (ℂ × Circle) W.Carrier ∞,
      Γ.source = {y : ℂ × Circle | ‖y.1‖ < 1 + ε} ∧
      Γ.target = B.chartTubeMap m C Θ '' Γ.source ∧
      (Γ : ℂ × Circle → W.Carrier) = B.chartTubeMap m C Θ ∧ Γ.target ⊆ W.interior := by
  let U : Set (ℂ × Circle) := {y | ‖y.1‖ < 1 + ε}
  have ho : IsOpen U := isOpen_lt (continuous_norm.comp continuous_fst) continuous_const
  have hl : IsLocalDiffeomorphOn PlaneCircleModel W.model ∞ (B.chartTubeMap m C Θ) U := by
    intro y
    exact B.chartTubeMap_local m C Θ δ hg hδ (hdepth y y.property)
  obtain ⟨Γ, hs, ht, hf⟩ := hl.exists_partialDiffeomorph_of_injOn ho
    ⟨(0, 1), by change ‖(0 : ℂ)‖ < 1 + ε; simp only [norm_zero]; linarith⟩
    ((B.chartTubeMap_injOn m C Θ).mono (fun y hy => hdepth y hy))
  refine ⟨Γ, hs, by rw [hs]; exact ht, hf, ?_⟩
  intro z hz
  rw [ht] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact ((hl ⟨y, hy⟩).isInteriorPoint_iff (by simp)).mp
    BoundarylessManifold.isInteriorPoint

theorem SeifertBlock.exists_charts_of_linear {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (h : ∀ m, B.presentation.pairing.matching (B.seam m) =
      linearTorusDiffeomorph (torusUnit (B.presentation.pairing.matching (B.seam m)))) :
    Nonempty (SeifertBlockCharts W d) := by
  classical
  by_cases hzero : d.fillingCount = 0
  · exact ⟨B.unfilledCharts hzero⟩
  have hk : d.k = 1 ∨ d.k = 2 ∨ d.k = 3 := by
    have h1 := d.one_le_k
    have h3 := d.k_le_three
    omega
  let Q := chartRadialPlanarBase.{u} d.k hk
  obtain ⟨δ0, hδ0, Θ, hg0⟩ := B.product.exists_standard_germ Q
  let δ := min δ0 1
  have hδ : 0 < δ := lt_min hδ0 (by norm_num)
  have hδ1 : δ ≤ 1 := min_le_right δ0 1
  have hg : ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      B.presentation.pieceCollar (B.piece none) (B.product.port j) p =
        Θ (Q.collar j (p.1.1, p.2), p.1.2) := by
    intro j p hp hlt
    exact hg0 j p hp (lt_of_lt_of_le hlt (min_le_left δ0 1))
  let R := B.product.chartGermProductPiece Q δ Θ hδ hδ1 hg
  have hR := B.product.chartGermProductRegion_eq Q δ Θ hδ hδ1 hg
  choose a b C δs hδs hab hmatrix Θs hgs using B.exists_normalized_solid_germ
  obtain ⟨ε, hε, hεdepth⟩ := d.exists_uniform_chartRadius δ hδ
  have hdepth (m : Fin d.fillingCount) (y : ℂ × Circle) (hy : ‖y.1‖ < 1 + ε) :
      seamDepth (d.fillingSlope m).1.natAbs ‖3 * y.1‖ < 1 :=
    lt_of_lt_of_le (hεdepth m y hy) hδ1
  choose Γ hsource htarget hmap hinterior using fun m =>
    B.exists_chartTube_radius m (C m) (δs m) (Θs m) (hgs m) (hδs m) ε hε (hdepth m)
  let A := fun m => torusUnit (B.presentation.pairing.matching (B.seam m)) * C m
  have ht (m : Fin d.fillingCount) (y : ℂ × Circle)
      (hy : 1 < ‖y.1‖ ∧ ‖y.1‖ < 1 + ε) :
      ∃ hz : (seamModel d m (B.port (.inr m)) (A m) y).1 ∈ planarOpen d.k,
        B.chartTubeMap m (C m) (Θs m) y = (R.chartProductDiffeomorph
          (⟨(seamModel d m (B.port (.inr m)) (A m) y).1, hz⟩,
            (seamModel d m (B.port (.inr m)) (A m) y).2) : W.Carrier) :=
    B.chartGermProduct_transition m (C m) (Θs m) (h m) hk δ Θ hδ hδ1 hg y hy.1
      (hεdepth m y hy.2)
  refine ⟨{
    port := B.port
    matrix := A
    a := a
    b := b
    matrix_eq := hmatrix
    bezout := hab
    productRegion := R.chartProductRegion
    productRegion_interior := R.chartProductRegion_interior
    product := R.chartProductDiffeomorph
    ε := ε
    ε_pos := hε
    tube := Γ
    tube_source := hsource
    tube_interior := hinterior
    transitionDomain := {y | 1 < ‖y.1‖ ∧ ‖y.1‖ < 1 + ε}
    transitionDomain_eq := rfl
    transition_domain := fun m y hy => (ht m y hy).choose
    transition := ?_
    tube_product_overlap := ?_
    disjoint := ?_
    covers := ?_ }⟩
  · intro m y hy
    exact (congrFun (hmap m) y).trans (ht m y hy).choose_spec
  · intro m
    ext z
    constructor
    · rintro ⟨hz, hp⟩
      rw [htarget m] at hz
      obtain ⟨y, hy, he⟩ := hz
      have hyε : ‖y.1‖ < 1 + ε := by
        rw [hsource m] at hy
        exact hy
      have hy1 : 1 < ‖y.1‖ := by
        by_contra hn
        have hc : ‖y.1‖ ≤ 1 := le_of_not_gt hn
        have hp' : z ∈ B.product.chartProductRegion := by
          change z ∈ R.chartProductRegion at hp
          rw [hR] at hp
          exact hp
        rw [← he, chartTubeMap, ite_eq_left hc] at hp'
        exact B.chartCoreMap_not_mem_productRegion m (Θs m) y hp'
      exact ⟨y, ⟨hy1, hyε⟩, (congrFun (hmap m) y).trans he⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(Γ m).map_source ((hsource m).symm ▸ hy.2), ?_⟩
      have hp := B.chartTubeMap_positive_region m (C m) (Θs m) y hy.1 (hdepth m y hy.2)
      change Γ m y ∈ R.chartProductRegion
      rw [hR]
      exact (congrFun (hmap m) y).symm ▸ hp
  · intro m n hmn
    rw [Set.disjoint_left]
    intro z hzm hzn
    rw [htarget m] at hzm
    rw [htarget n] at hzn
    obtain ⟨x, hx, hex⟩ := hzm
    obtain ⟨y, hy, hey⟩ := hzn
    exact B.chartTubeMap_cross m n hmn (C m) (C n) (Θs m) (Θs n) x y
      (hdepth m x (by rw [hsource m] at hx; exact hx))
      (hdepth n y (by rw [hsource n] at hy; exact hy)) (hex.trans hey.symm)
  · intro w hw
    rcases B.chartCoreCover Θs w hw with hp | ⟨m, y, hy, he⟩
    · left
      rw [hR]
      exact hp
    · right
      have hs : y ∈ (Γ m).source := (hsource m).symm ▸ (show ‖y.1‖ < 1 + ε by linarith)
      have heΓ : Γ m y = w := by
        rw [congrFun (hmap m) y, chartTubeMap, ite_eq_left hy]
        exact he
      exact ⟨m, heΓ ▸ (Γ m).map_source hs⟩

theorem SeifertBlock.exists_charts {W : CompactCarrier.{u}} {d : SeifertData}
    (hT : TorusMappingClassLinear) (B : SeifertBlock W d) :
    Nonempty (SeifertBlockCharts W d) :=
  (B.linearized hT).exists_charts_of_linear (B.linearized_matching hT)

theorem SeifertBlock.exists_closed_charts {W : CompactCarrier.{u}} {d : SeifertData}
    (hT : TorusMappingClassLinear) (B : SeifertBlock W d) (h : d.ports = 0) :
    Nonempty (SeifertBlockCharts W d) := by
  exact (And.intro (B.exists_charts hT) h).1

def mobiusCharts : SeifertBlockCharts mobiusBundleCarrier.{u} mobiusData :=
  Classical.choice (mobiusBlock.exists_charts_of_linear (fun m => by
    change seamMatching = linearTorusDiffeomorph (torusUnit seamMatching)
    rw [seamMatching, torusUnit_linearTorusDiffeomorph]))

end GC.Seifert
