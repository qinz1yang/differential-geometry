import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralModelMaps
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralEndModel
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab
import DifferentialGeometry.Topology.Manifold.GraphBand
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.PullbackParameter
import DifferentialGeometry.Geometry.Metric.Sphere.Round.ProjectedConnectionLeviCivita

/-!
Both physical endpoint maps descend from the actual diagonal quotient to the same dihedral
carrier and preserve its metric on explicit height domains. A genuine sphere-dependent odd
shear descends to a jointly smooth family of quotient diffeomorphisms. It moves the actual
anchor by the required height, with global height control and every-order compact metric
convergence. Internally constructed moving partial charts have literal forward/metric formulas
and contain every model ball within the physical margin.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse GC.Endpoint GC.Geometry.SphericalProduct
open scoped Manifold ContDiff RealInnerProductSpace
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension
  dihedralEndSigma dihedralEndMetrizable dihedralEndRawConnected
universe u
namespace DifferentialGeometry.Geometry.Collapse

def dihedralEndIsometry (L : ℝ) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) : CylinderIsometry :=
  (A, if b then AffineIsometryEquiv.pointReflection ℝ (L / 2) else 1)
def dihedralEndRawMap (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) : sphereCylinder →
    (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
  dihedralPhysicalMap L hL (dihedralEndIsometry L b A) ∘ sphereCylinderRechartDiffeomorph
theorem dihedralEndRawMap_formula (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (p : sphereCylinder) :
    dihedralEndRawMap.{u} L hL b A p = dihedralStandardPresentation.proj
      ((sphereDiffeo (n := 2) A) p.1, (if b then L - p.2 else p.2) / (2 * L)) := by
  change dihedralStandardPresentation.proj (sphereCylinderRechartDiffeomorph.symm
    (dihedralPhysicalDiffeo L hL (dihedralEndIsometry L b A)
      (sphereCylinderRechartDiffeomorph p))) = _
  rw [dihedralPhysical_formula]
  apply congrArg dihedralStandardPresentation.proj
  apply Prod.ext
  · rfl
  · cases b
    · rfl
    · change ((L / 2 - p.2) + L / 2) / (2 * L) = (L - p.2) / (2 * L)
      congr 1
      ring
private theorem dihedralSphere_neg
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (sphereDiffeo (n := 2) A) (-y) = -(sphereDiffeo (n := 2) A y) := by
  apply Subtype.ext
  exact A.map_neg y
private theorem dihedralEndRawMap_invariant (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (p : sphereCylinder) :
    dihedralEndRawMap.{u} L hL b A (cylinderDiagonalDiffeomorph p) =
      dihedralEndRawMap L hL b A p := by
  rw [cylinderDiagonalDiffeomorph_apply, dihedralEndRawMap_formula, dihedralEndRawMap_formula]
  cases b
  · apply ((dihedralStandardPresentation.fibres _ _).mpr
      ⟨dihedralReflectionZero, dihedralReflectionZero_mem, ?_⟩).symm
    rw [cylinderAct_dihedralReflectionZero]
    apply Prod.ext
    · exact (dihedralSphere_neg A p.1).symm
    · change -(p.2 / (2 * L)) = -p.2 / (2 * L)
      ring
  · apply ((dihedralStandardPresentation.fibres _ _).mpr
      ⟨dihedralReflectionHalf, dihedralReflectionHalf_mem, ?_⟩).symm
    rw [cylinderAct_dihedralReflectionHalf]
    apply Prod.ext
    · exact (dihedralSphere_neg A p.1).symm
    · change 1 - (L - p.2) / (2 * L) = (L - -p.2) / (2 * L)
      field_simp
      ring

def dihedralEndFactor (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) : CylinderDiagonalQuotient →
    (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
  Quotient.lift (dihedralEndRawMap L hL b A) (by
    intro p q hpq
    have heq : cylinderDiagonalQuotientMap p = cylinderDiagonalQuotientMap q := Quotient.sound hpq
    rcases cylinderDiagonalQuotientMap_eq_iff.mp heq with h | h
    · rw [h]
    · rw [h]
      exact dihedralEndRawMap_invariant L hL b A q)
def dihedralEndMap (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) : dihedralEndCarrier →
    (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
  dihedralEndFactor L hL b A ∘ dihedralEndRechart.symm
theorem dihedralEndProjection_surjective : Function.Surjective dihedralEndProjection :=
  dihedralEndRechart.surjective.comp
    (cylinderDiagonalQuotientMap_surjective.comp sphereCylinderRechartDiffeomorph.symm.surjective)
theorem dihedralEndMap_comp (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    dihedralEndMap.{u} L hL b A ∘ dihedralEndProjection =
      dihedralPhysicalMap L hL (dihedralEndIsometry L b A) := by
  funext z
  change dihedralEndFactor L hL b A (dihedralEndRechart.symm
    (dihedralEndRechart (cylinderDiagonalQuotientMap
      (sphereCylinderRechartDiffeomorph.symm z)))) = _
  rw [dihedralEndRechart.symm_apply_apply]
  change dihedralPhysicalMap L hL (dihedralEndIsometry L b A)
    (sphereCylinderRechartDiffeomorph (sphereCylinderRechartDiffeomorph.symm z)) = _
  rw [sphereCylinderRechartDiffeomorph.apply_symm_apply]
theorem dihedralEndMap_localDiffeomorph (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (dihedralEndMap.{u} L hL b A) := by
  have hcomp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (dihedralEndMap L hL b A ∘ dihedralEndProjection) := by
    rw [dihedralEndMap_comp]
    exact dihedralPhysicalMap_localDiffeomorph L hL (dihedralEndIsometry L b A)
  intro q
  obtain ⟨z, rfl⟩ := dihedralEndProjection_surjective q
  exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hcomp z)
    (dihedralEndProjection_localDiffeomorph z)
theorem dihedralEndMap_metric_pullback (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    localPullMetric (dihedralMetric.{u} ε L hε hL) (dihedralEndMap L hL b A)
      (dihedralEndMap_localDiffeomorph L hL b A) = dihedralEndMetric ε hε := by
  apply localPullMetric_injective_of_surjective dihedralEndProjection
    dihedralEndProjection_localDiffeomorph dihedralEndProjection_surjective
  calc
    _ = localPullMetric (dihedralMetric ε L hε hL)
        (dihedralEndMap L hL b A ∘ dihedralEndProjection)
        (isLocalDiffeomorph_comp (dihedralEndMap_localDiffeomorph L hL b A)
          dihedralEndProjection_localDiffeomorph) :=
      localPullMetric_comp _ (dihedralEndMap L hL b A) dihedralEndProjection
        (dihedralEndMap_localDiffeomorph L hL b A) dihedralEndProjection_localDiffeomorph _
    _ = localPullMetric (dihedralMetric ε L hε hL)
        (dihedralPhysicalMap L hL (dihedralEndIsometry L b A))
        (dihedralPhysicalMap_localDiffeomorph L hL (dihedralEndIsometry L b A)) := by
      simp only [dihedralEndMap_comp]
      rfl
    _ = dihedralRechartedMetric ε (1 / 2) hε (by norm_num) :=
      dihedralPhysicalMap_metric_pullback ε L hε hL (dihedralEndIsometry L b A)
    _ = _ := (dihedralEndMetric_pullback ε hε).symm

open private absAxialCoordinate absAxialCoordinate_proj continuous_absAxialCoordinate
from DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab
def dihedralEndHeight (q : dihedralEndCarrier) : ℝ :=
  absAxialCoordinate (dihedralEndRechart.symm q)
theorem dihedralEndHeight_projection (z : sphereCylinderRechart) :
    dihedralEndHeight (dihedralEndProjection z) = |z.point.2| := by
  change absAxialCoordinate (dihedralEndRechart.symm
    (dihedralEndRechart (cylinderDiagonalQuotientMap
      (sphereCylinderRechartDiffeomorph.symm z)))) = _
  rw [dihedralEndRechart.symm_apply_apply]
  exact absAxialCoordinate_proj _
theorem dihedralEndHeight_continuous : Continuous dihedralEndHeight :=
  continuous_absAxialCoordinate.comp dihedralEndRechart.symm.continuous
theorem dihedralEndProjection_covering : IsCoveringMap dihedralEndProjection :=
  (cylinderDiagonalQuotientMap_isCoveringMap.comp_homeomorph
    sphereCylinderRechartDiffeomorph.symm.toHomeomorph).homeomorph_comp
      dihedralEndRechart.toHomeomorph
theorem dihedralEndHeight_nonneg (q : dihedralEndCarrier) : 0 ≤ dihedralEndHeight q := by
  obtain ⟨z, rfl⟩ := dihedralEndProjection_surjective q
  rw [dihedralEndHeight_projection]
  exact abs_nonneg _

open private localPullMetric_eq_pullbackMetricCross
from DifferentialGeometry.Geometry.Metric.DistancePullback
open private dihedralModel_line_distance_le
from DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralModelMaps
theorem dihedralEndHeight_distance_le (ε : ℝ) (hε : 0 < ε) (x y : dihedralEndCarrier) :
    ENNReal.ofReal |dihedralEndHeight x - dihedralEndHeight y| ≤
      riemannianEDistOf (dihedralEndMetric ε hε) x y := by
  obtain ⟨z, rfl⟩ := dihedralEndProjection_surjective x
  apply le_edistOf_of_coveringMap_localPullMetric
    (dihedralRechartedMetric ε (1 / 2) hε (by norm_num)) (dihedralEndMetric ε hε)
    dihedralEndProjection_localDiffeomorph dihedralEndProjection_covering
    (dihedralEndMetric_pullback ε hε) z y
  intro w hw
  rw [← hw, dihedralEndHeight_projection, dihedralEndHeight_projection]
  exact (ENNReal.ofReal_le_ofReal (abs_abs_sub_abs_le_abs_sub z.point.2 w.point.2)).trans
    (dihedralModel_line_distance_le ε hε z w)
theorem exists_dihedralEndPositiveLift (q : dihedralEndCarrier) :
    ∃ p : sphereCylinder, dihedralEndRechart (cylinderDiagonalQuotientMap p) = q ∧
      0 ≤ p.2 ∧ dihedralEndHeight q = p.2 := by
  obtain ⟨z, hz⟩ := dihedralEndProjection_surjective q
  let p := sphereCylinderRechartDiffeomorph.symm z
  have hp : dihedralEndRechart (cylinderDiagonalQuotientMap p) = q := hz
  have hheight : dihedralEndHeight q = |p.2| := by
    rw [← hp]
    change absAxialCoordinate (dihedralEndRechart.symm
      (dihedralEndRechart (cylinderDiagonalQuotientMap p))) = _
    rw [dihedralEndRechart.symm_apply_apply]
    exact absAxialCoordinate_proj p
  by_cases hpos : 0 ≤ p.2
  · exact ⟨p, hp, hpos, hheight.trans (abs_of_nonneg hpos)⟩
  · refine ⟨(-p.1, -p.2), ?_, by linarith, ?_⟩
    · have hq : cylinderDiagonalQuotientMap (-p.1, -p.2) = cylinderDiagonalQuotientMap p := by
        apply cylinderDiagonalQuotientMap_eq_iff.mpr
        right
        exact (cylinderDiagonalDiffeomorph_apply p).symm
      exact (congrArg dihedralEndRechart hq).trans hp
    · exact hheight.trans (abs_of_neg (lt_of_not_ge hpos))

def dihedralEndDomain (L : ℝ) : Set dihedralEndCarrier := {q | dihedralEndHeight q < L / 2}
theorem dihedralEndDomain_open (L : ℝ) : IsOpen (dihedralEndDomain L) :=
  isOpen_lt dihedralEndHeight_continuous continuous_const
private theorem dihedralEndRawMap_fibre (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (p q : sphereCylinder) (hp : |p.2| < L / 2) (hq : |q.2| < L / 2)
    (heq : dihedralEndRawMap.{u} L hL b A p = dihedralEndRawMap L hL b A q) :
    cylinderDiagonalQuotientMap p = cylinderDiagonalQuotientMap q := by
  let P : sphereCylinder := ((sphereDiffeo (n := 2) A) p.1,
    (if b then L - p.2 else p.2) / (2 * L))
  let Q : sphereCylinder := ((sphereDiffeo (n := 2) A) q.1,
    (if b then L - q.2 else q.2) / (2 * L))
  rw [dihedralEndRawMap_formula, dihedralEndRawMap_formula] at heq
  obtain ⟨γ, hγ, hact⟩ := (dihedralStandardPresentation.fibres P Q).mp heq
  have hp' := abs_lt.mp hp
  have hq' := abs_lt.mp hq
  obtain ⟨n, hn | hn⟩ := dihedralStandard_integer_normalForm hγ
  · have hc := (hn P).symm.trans hact
    have ht := congrArg Prod.snd hc
    have hnlo : (-1 : ℝ) < n := by
      dsimp [P, Q] at ht
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at ht <;>
        field_simp at ht <;> nlinarith [hp'.1, hp'.2, hq'.1, hq'.2]
    have hnhi : (n : ℝ) < 1 := by
      dsimp [P, Q] at ht
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at ht <;>
        field_simp at ht <;> nlinarith [hp'.1, hp'.2, hq'.1, hq'.2]
    have hlo : (-1 : ℤ) < n := by exact_mod_cast hnlo
    have hhi : n < 1 := by exact_mod_cast hnhi
    have hn0 : n = 0 := by omega
    subst n
    apply cylinderDiagonalQuotientMap_eq_iff.mpr
    left
    apply Prod.ext
    · apply (sphereDiffeo (n := 2) A).injective
      change (sphereDiffeo (n := 2) A) p.1 = (sphereDiffeo (n := 2) A) q.1
      exact congrArg Prod.fst hc
    · dsimp [P, Q] at ht
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_zero, add_zero] at ht <;>
        field_simp at ht <;> linarith
  · have hc := (hn P).symm.trans hact
    have ht := congrArg Prod.snd hc
    have hnval : n = (if b then 1 else 0) := by
      cases b
      · have hnlo : (-1 : ℝ) < n := by
          dsimp [P, Q] at ht
          field_simp at ht
          nlinarith [hp'.1, hp'.2, hq'.1, hq'.2]
        have hnhi : (n : ℝ) < 1 := by
          dsimp [P, Q] at ht
          field_simp at ht
          nlinarith [hp'.1, hp'.2, hq'.1, hq'.2]
        have hlo : (-1 : ℤ) < n := by exact_mod_cast hnlo
        have hhi : n < 1 := by exact_mod_cast hnhi
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
      · have hnlo : (0 : ℝ) < n := by
          dsimp [P, Q] at ht
          field_simp at ht
          nlinarith [hp'.1, hp'.2, hq'.1, hq'.2]
        have hnhi : (n : ℝ) < 2 := by
          dsimp [P, Q] at ht
          field_simp at ht
          nlinarith [hp'.1, hp'.2, hq'.1, hq'.2]
        have hlo : (0 : ℤ) < n := by exact_mod_cast hnlo
        have hhi : n < 2 := by exact_mod_cast hnhi
        simp only [↓reduceIte]
        omega
    apply cylinderDiagonalQuotientMap_eq_iff.mpr
    right
    rw [cylinderDiagonalDiffeomorph_apply]
    apply Prod.ext
    · apply (sphereDiffeo (n := 2) A).injective
      change (sphereDiffeo (n := 2) A) p.1 = (sphereDiffeo (n := 2) A) (-q.1)
      rw [dihedralSphere_neg]
      have hs : -(sphereDiffeo (n := 2) A) p.1 = (sphereDiffeo (n := 2) A) q.1 :=
        congrArg Prod.fst hc
      simpa only [neg_neg] using congrArg Neg.neg hs
    · change p.2 = -q.2
      rw [hnval] at ht
      dsimp [P, Q] at ht
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_zero, Int.cast_one] at ht <;>
        field_simp at ht <;> linarith
theorem dihedralEndMap_injOn (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    Set.InjOn (dihedralEndMap.{u} L hL b A) (dihedralEndDomain L) := by
  intro x hx y hy heq
  obtain ⟨p, hp, hp0, hpx⟩ := exists_dihedralEndPositiveLift x
  obtain ⟨q, hq, hq0, hqy⟩ := exists_dihedralEndPositiveLift y
  have hpL : |p.2| < L / 2 := by
    rw [abs_of_nonneg hp0, ← hpx]
    exact hx
  have hqL : |q.2| < L / 2 := by
    rw [abs_of_nonneg hq0, ← hqy]
    exact hy
  have hraw : dihedralEndRawMap L hL b A p = dihedralEndRawMap L hL b A q := by
    rw [← hp, ← hq] at heq
    change dihedralEndFactor L hL b A
      (dihedralEndRechart.symm (dihedralEndRechart (cylinderDiagonalQuotientMap p))) =
        dihedralEndFactor L hL b A
      (dihedralEndRechart.symm (dihedralEndRechart (cylinderDiagonalQuotientMap q))) at heq
    rw [dihedralEndRechart.symm_apply_apply, dihedralEndRechart.symm_apply_apply] at heq
    exact heq
  rw [← hp, ← hq]
  exact congrArg dihedralEndRechart (dihedralEndRawMap_fibre L hL b A p q hpL hqL hraw)
theorem exists_dihedralEndPartial (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ∃ jm : PartialDiffeomorph (𝓡 3) (𝓡 3) dihedralEndCarrier
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier ∞,
      jm.source = dihedralEndDomain L ∧
      jm.target = dihedralEndMap L hL b A '' dihedralEndDomain L ∧
      (jm : dihedralEndCarrier → _) = dihedralEndMap L hL b A := by
  have hne : (dihedralEndDomain L).Nonempty := by
    refine ⟨dihedralEndProjection
      (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)), ?_⟩
    change dihedralEndHeight _ < L / 2
    rw [dihedralEndHeight_projection]
    change |(0 : ℝ)| < L / 2
    simpa only [abs_zero] using half_pos hL
  exact IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    ((dihedralEndMap_localDiffeomorph L hL b A).isLocalDiffeomorphOn _)
    (dihedralEndDomain_open L) hne (dihedralEndMap_injOn L hL b A)
theorem dihedralEndMap_axis (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (q : dihedralEndCarrier) (hq : q ∈ dihedralEndDomain L) :
    dihedralAxis L (dihedralEndMap.{u} L hL b A q) =
      if b then L - dihedralEndHeight q else dihedralEndHeight q := by
  obtain ⟨p, hp, hp0, hheight⟩ := exists_dihedralEndPositiveLift q
  have hpL : p.2 < L / 2 := by
    change dihedralEndHeight q < L / 2 at hq
    rwa [hheight] at hq
  have hraw : dihedralEndMap L hL b A q = dihedralEndRawMap L hL b A p := by
    rw [← hp]
    change dihedralEndFactor L hL b A (dihedralEndRechart.symm
      (dihedralEndRechart (cylinderDiagonalQuotientMap p))) = _
    rw [dihedralEndRechart.symm_apply_apply]
    rfl
  rw [hraw, dihedralEndRawMap_formula, hheight]
  let z := sphereCylinderRechartDiffeomorph ((sphereDiffeo (n := 2) A) p.1,
    (if b then L - p.2 else p.2) / (2 * L))
  change dihedralAxis L (dihedralProjection z) = _
  rw [dihedralAxis_projection]
  change 2 * L * ‖(((if b then L - p.2 else p.2) / (2 * L)) : AddCircle (1 : ℝ))‖ = _
  have hden : 0 < 2 * L := mul_pos (by norm_num) hL
  have hpos : 0 ≤ (if b then L - p.2 else p.2) / (2 * L) := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      apply div_nonneg <;> linarith
  have hupper : (if b then L - p.2 else p.2) / (2 * L) ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).mpr
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have hn := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr
    (by rw [abs_of_nonneg hpos, abs_one]; exact hupper)
  rw [hn, abs_of_nonneg hpos]
  field_simp
theorem dihedralEndDomain_ball_subset (ε L R : ℝ) (hε : 0 < ε) (p : dihedralEndCarrier)
    (hR : 0 < R) (hmargin : dihedralEndHeight p + R ≤ L / 2) :
    riemannianBallOf (dihedralEndMetric ε hε) p R ⊆ dihedralEndDomain L := by
  intro q hq
  have hd := (dihedralEndHeight_distance_le ε hε p q).trans_lt hq
  have hb := abs_lt.mp ((ENNReal.ofReal_lt_ofReal_iff hR).mp hd)
  change dihedralEndHeight q < L / 2
  linarith [hb.1]
theorem exists_dihedralEndPointedMetricChart (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (b : Bool) (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (p : dihedralEndCarrier) (hp : dihedralEndHeight p < L / 2) :
    ∃ jm : PartialDiffeomorph (𝓡 3) (𝓡 3) dihedralEndCarrier
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier ∞,
      ∃ hjm : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (jm : dihedralEndCarrier → _),
      jm.source = dihedralEndDomain L ∧
      jm.target = dihedralEndMap L hL b A '' dihedralEndDomain L ∧
      (jm : dihedralEndCarrier → _) = dihedralEndMap L hL b A ∧ p ∈ jm.source ∧
      localPullMetric (dihedralMetric ε L hε hL) jm hjm = dihedralEndMetric ε hε ∧
      ∀ R : ℝ, 0 < R → dihedralEndHeight p + R ≤ L / 2 →
        riemannianBallOf (dihedralEndMetric ε hε) p R ⊆ jm.source := by
  obtain ⟨jm, hsrc, htgt, hfun⟩ := exists_dihedralEndPartial L hL b A
  have hjm : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (jm : dihedralEndCarrier → _) := by
    rw [hfun]
    exact dihedralEndMap_localDiffeomorph L hL b A
  refine ⟨jm, hjm, hsrc, htgt, hfun, hsrc.symm ▸ hp, ?_, ?_⟩
  · simpa only [hfun] using dihedralEndMap_metric_pullback ε L hε hL b A
  · intro R hR hmargin
    rw [hsrc]
    exact dihedralEndDomain_ball_subset ε L R hε p hR hmargin
def dihedralRawOddShear (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) :
    sphereCylinder ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), (𝓡 2).prod 𝓘(ℝ, ℝ)⟯ sphereCylinder :=
  graphBandDiffeomorph (fun y => s * innerCoordFun (n := 2) (σ : EuclideanSpace ℝ (Fin 3)) y)
    (fun y => s * innerCoordFun (n := 2) (σ : EuclideanSpace ℝ (Fin 3)) y + 1)
    (contMDiff_const.mul (innerCoordFun (n := 2) (σ : EuclideanSpace ℝ (Fin 3))).contMDiff)
    ((contMDiff_const.mul
      (innerCoordFun (n := 2) (σ : EuclideanSpace ℝ (Fin 3))).contMDiff).add contMDiff_const)
    (fun y h => by linarith)
theorem dihedralRawOddShear_apply (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (s : ℝ) (p : sphereCylinder) :
    dihedralRawOddShear σ s p =
      (p.1, p.2 + s * ⟪(σ : EuclideanSpace ℝ (Fin 3)),
        (p.1 : EuclideanSpace ℝ (Fin 3))⟫) := by
  rw [dihedralRawOddShear, graphBandDiffeomorph_apply]
  apply Prod.ext
  · rfl
  · change s * ⟪(σ : EuclideanSpace ℝ (Fin 3)), (p.1 : EuclideanSpace ℝ (Fin 3))⟫ +
      (s * ⟪(σ : EuclideanSpace ℝ (Fin 3)), (p.1 : EuclideanSpace ℝ (Fin 3))⟫ + 1 -
        s * ⟪(σ : EuclideanSpace ℝ (Fin 3)), (p.1 : EuclideanSpace ℝ (Fin 3))⟫) * p.2 = _
    ring
theorem dihedralRawOddShear_diagonal (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (s : ℝ) (p : sphereCylinder) :
    dihedralRawOddShear σ s (cylinderDiagonalDiffeomorph p) =
      cylinderDiagonalDiffeomorph (dihedralRawOddShear σ s p) := by
  rw [cylinderDiagonalDiffeomorph_apply, dihedralRawOddShear_apply,
    dihedralRawOddShear_apply, cylinderDiagonalDiffeomorph_apply]
  apply Prod.ext
  · rfl
  · change -p.2 + s * ⟪(σ : EuclideanSpace ℝ (Fin 3)),
      -(p.1 : EuclideanSpace ℝ (Fin 3))⟫ =
        -(p.2 + s * ⟪(σ : EuclideanSpace ℝ (Fin 3)), (p.1 : EuclideanSpace ℝ (Fin 3))⟫)
    rw [inner_neg_right]
    ring
def dihedralRawOddShearFactor (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (s : ℝ) : CylinderDiagonalQuotient → CylinderDiagonalQuotient :=
  Quotient.lift (cylinderDiagonalQuotientMap ∘ dihedralRawOddShear σ s) (by
    intro p q hpq
    have heq : cylinderDiagonalQuotientMap p = cylinderDiagonalQuotientMap q := Quotient.sound hpq
    rcases cylinderDiagonalQuotientMap_eq_iff.mp heq with h | h
    · rw [h]
    · change cylinderDiagonalQuotientMap (dihedralRawOddShear σ s p) =
        cylinderDiagonalQuotientMap (dihedralRawOddShear σ s q)
      rw [h, dihedralRawOddShear_diagonal]
      apply cylinderDiagonalQuotientMap_eq_iff.mpr
      right
      rfl)
def dihedralOddShearMap (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (s : ℝ) : dihedralEndCarrier → dihedralEndCarrier :=
  dihedralEndRechart ∘ dihedralRawOddShearFactor σ s ∘ dihedralEndRechart.symm
def dihedralOddShearRecharted (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) :
    sphereCylinderRechart ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereCylinderRechart :=
  sphereCylinderRechartDiffeomorph.symm.trans
    ((dihedralRawOddShear σ s).trans sphereCylinderRechartDiffeomorph)
theorem dihedralOddShearMap_comp (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (s : ℝ) : dihedralOddShearMap σ s ∘ dihedralEndProjection =
      dihedralEndProjection ∘ dihedralOddShearRecharted σ s := by
  funext z
  change dihedralEndRechart (dihedralRawOddShearFactor σ s (dihedralEndRechart.symm
    (dihedralEndRechart (cylinderDiagonalQuotientMap
      (sphereCylinderRechartDiffeomorph.symm z))))) = _
  rw [dihedralEndRechart.symm_apply_apply]
  change dihedralEndRechart (cylinderDiagonalQuotientMap
      (dihedralRawOddShear σ s (sphereCylinderRechartDiffeomorph.symm z))) =
    dihedralEndRechart (cylinderDiagonalQuotientMap (sphereCylinderRechartDiffeomorph.symm
      (sphereCylinderRechartDiffeomorph
        (dihedralRawOddShear σ s (sphereCylinderRechartDiffeomorph.symm z)))))
  rw [sphereCylinderRechartDiffeomorph.symm_apply_apply]
theorem dihedralOddShearMap_localDiffeomorph
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (dihedralOddShearMap σ s) := by
  have hcomp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (dihedralOddShearMap σ s ∘ dihedralEndProjection) := by
    rw [dihedralOddShearMap_comp]
    exact isLocalDiffeomorph_comp dihedralEndProjection_localDiffeomorph
      (dihedralOddShearRecharted σ s).isLocalDiffeomorph
  intro q
  obtain ⟨z, rfl⟩ := dihedralEndProjection_surjective q
  exact isLocalDiffeomorphAt_of_comp (hcomp z) (dihedralEndProjection_localDiffeomorph z)
theorem dihedralOddShearMap_inverse
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) (q : dihedralEndCarrier) :
    dihedralOddShearMap σ (-s) (dihedralOddShearMap σ s q) = q := by
  obtain ⟨z, rfl⟩ := dihedralEndProjection_surjective q
  have hcomp (t : ℝ) (w : sphereCylinderRechart) :
      dihedralOddShearMap σ t (dihedralEndProjection w) =
        dihedralEndProjection (dihedralOddShearRecharted σ t w) :=
    congrFun (dihedralOddShearMap_comp σ t) w
  rw [hcomp s z, hcomp (-s) (dihedralOddShearRecharted σ s z)]
  apply congrArg dihedralEndProjection
  change sphereCylinderRechartDiffeomorph (dihedralRawOddShear σ (-s)
    (sphereCylinderRechartDiffeomorph.symm
      (sphereCylinderRechartDiffeomorph (dihedralRawOddShear σ s
        (sphereCylinderRechartDiffeomorph.symm z))))) = z
  rw [sphereCylinderRechartDiffeomorph.symm_apply_apply,
    dihedralRawOddShear_apply, dihedralRawOddShear_apply]
  have hraw : (z.point.1, z.point.2 + s *
      ⟪(σ : EuclideanSpace ℝ (Fin 3)), (z.point.1 : EuclideanSpace ℝ (Fin 3))⟫ +
      -s * ⟪(σ : EuclideanSpace ℝ (Fin 3)), (z.point.1 : EuclideanSpace ℝ (Fin 3))⟫) =
      sphereCylinderRechartDiffeomorph.symm z := by
    apply Prod.ext
    · rfl
    · change z.point.2 + s * _ + -s * _ = z.point.2
      ring
  change sphereCylinderRechartDiffeomorph (z.point.1, z.point.2 + s *
    ⟪(σ : EuclideanSpace ℝ (Fin 3)), (z.point.1 : EuclideanSpace ℝ (Fin 3))⟫ +
    -s * ⟪(σ : EuclideanSpace ℝ (Fin 3)), (z.point.1 : EuclideanSpace ℝ (Fin 3))⟫) = z
  rw [hraw, sphereCylinderRechartDiffeomorph.apply_symm_apply]
def dihedralOddShearDiffeomorph (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) :
    dihedralEndCarrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ dihedralEndCarrier where
  toEquiv := {
    toFun := dihedralOddShearMap σ s
    invFun := dihedralOddShearMap σ (-s)
    left_inv := dihedralOddShearMap_inverse σ s
    right_inv := fun q => by simpa only [neg_neg] using dihedralOddShearMap_inverse σ (-s) q }
  contMDiff_toFun := (dihedralOddShearMap_localDiffeomorph σ s).contMDiff
  contMDiff_invFun := (dihedralOddShearMap_localDiffeomorph σ (-s)).contMDiff
theorem dihedralRawOddShear_joint (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 2).prod 𝓘(ℝ, ℝ)))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × sphereCylinder => dihedralRawOddShear σ p.1 p.2) := by
  have hχ := (innerCoordFun (n := 2) (σ : EuclideanSpace ℝ (Fin 3))).contMDiff
  have h := contMDiff_snd.fst.prodMk
    (contMDiff_snd.snd.add (contMDiff_fst.mul (hχ.comp contMDiff_snd.fst)))
  convert h using 1
  funext p
  exact dihedralRawOddShear_apply σ p.1 p.2
theorem dihedralOddShearDiffeomorph_projection
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ)
    (z : sphereCylinderRechart) :
    dihedralOddShearDiffeomorph σ s (dihedralEndProjection z) =
      dihedralEndProjection (sphereCylinderRechartDiffeomorph
        (z.point.1, z.point.2 + s * ⟪(σ : EuclideanSpace ℝ (Fin 3)),
          (z.point.1 : EuclideanSpace ℝ (Fin 3))⟫)) := by
  have h : dihedralOddShearMap σ s (dihedralEndProjection z) =
      dihedralEndProjection (dihedralOddShearRecharted σ s z) :=
    congrFun (dihedralOddShearMap_comp σ s) z
  change dihedralOddShearMap σ s (dihedralEndProjection z) = _
  rw [h]
  change dihedralEndProjection (sphereCylinderRechartDiffeomorph
    (dihedralRawOddShear σ s (sphereCylinderRechartDiffeomorph.symm z))) = _
  rw [dihedralRawOddShear_apply]
  rfl
theorem dihedralOddShearDiffeomorph_zero
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    dihedralOddShearDiffeomorph σ 0 = Diffeomorph.refl (𝓡 3) dihedralEndCarrier ∞ := by
  apply Diffeomorph.ext
  intro q
  obtain ⟨z, rfl⟩ := dihedralEndProjection_surjective q
  rw [dihedralOddShearDiffeomorph_projection]
  simp only [zero_mul, add_zero]
  change dihedralEndProjection
    (sphereCylinderRechartDiffeomorph (sphereCylinderRechartDiffeomorph.symm z)) =
      dihedralEndProjection z
  rw [sphereCylinderRechartDiffeomorph.apply_symm_apply]
theorem dihedralOddShearDiffeomorph_joint
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : ℝ × dihedralEndCarrier => dihedralOddShearDiffeomorph σ p.1 p.2) := by
  let π := Prod.map (id : ℝ → ℝ) dihedralEndProjection
  have hπ : IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 3))
      (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞ π :=
    (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph.prodMap
      dihedralEndProjection_localDiffeomorph
  have hπsurj : Function.Surjective π := Function.Surjective.prodMap
    Function.surjective_id dihedralEndProjection_surjective
  apply hπ.contMDiff_of_comp_of_surjective hπsurj
  have hraw := (dihedralRawOddShear_joint σ).comp
    (contMDiff_fst.prodMk (sphereCylinderRechartDiffeomorph.symm.contMDiff.comp contMDiff_snd))
  have hsource := dihedralEndProjection_localDiffeomorph.contMDiff.comp
    (sphereCylinderRechartDiffeomorph.contMDiff.comp hraw)
  convert hsource using 1
  funext p
  exact congrFun (dihedralOddShearMap_comp σ p.1) p.2
theorem dihedralOddShear_metric_convergence (ε : ℝ) (hε : 0 < ε)
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (s : ℕ → ℝ) (hs : Filter.Tendsto s Filter.atTop (nhds 0))
    (R : SmoothRiemannianMetric (𝓡 3) dihedralEndCarrier)
    (K : Set dihedralEndCarrier) (hK : IsCompact K) (k : ℕ) :
    Filter.Tendsto (fun i => CheegerGromovCompactness.metricDerivNormSupOn K k
      (Diffeomorph.pullbackMetricCross (dihedralEndMetric ε hε)
        (dihedralOddShearDiffeomorph σ (s i))) (dihedralEndMetric ε hε) R)
      Filter.atTop (nhds 0) := by
  let g := dihedralEndMetric ε hε
  have hparam : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (Prod.snd : ℝ × dihedralEndCarrier → dihedralEndCarrier) := contMDiff_snd
  have hg := (g.contMDiff.comp hparam).contMDiffOn
    (s := Set.univ ×ˢ (Set.univ : Set dihedralEndCarrier))
  have hc := CheegerGromovCompactness.metricDerivNormSupOn_pullback_continuousOn
    (fun _ : ℝ => g) Set.univ hg (dihedralOddShearDiffeomorph σ)
    (dihedralOddShearDiffeomorph_joint σ) R hK k
  have ht := (continuousOn_univ.mp hc).tendsto 0
  rw [dihedralOddShearDiffeomorph_zero, Diffeomorph.pullbackMetricCross_refl,
    CheegerGromovCompactness.metricDerivNormSupOn_self] at ht
  exact ht.comp hs
theorem dihedralOddShearDiffeomorph_anchor
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s c : ℝ) :
    dihedralOddShearDiffeomorph σ s
      (dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, c))) =
    dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, c + s)) := by
  rw [dihedralOddShearDiffeomorph_projection]
  apply congrArg dihedralEndProjection
  apply congrArg sphereCylinderRechartDiffeomorph
  apply Prod.ext
  · rfl
  · have hn : ‖(σ : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using σ.property
    change c + s * ⟪(σ : EuclideanSpace ℝ (Fin 3)), (σ : EuclideanSpace ℝ (Fin 3))⟫ = c + s
    rw [real_inner_self_eq_norm_sq, hn]
    ring
theorem dihedralOddShear_height_control
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) (q : dihedralEndCarrier) :
    |dihedralEndHeight (dihedralOddShearDiffeomorph σ s q) - dihedralEndHeight q| ≤ |s| := by
  obtain ⟨z, rfl⟩ := dihedralEndProjection_surjective q
  rw [dihedralOddShearDiffeomorph_projection,
    dihedralEndHeight_projection, dihedralEndHeight_projection]
  have hσ : ‖(σ : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using σ.property
  have hy : ‖(z.point.1 : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using z.point.1.property
  have hχ : |⟪(σ : EuclideanSpace ℝ (Fin 3)), (z.point.1 : EuclideanSpace ℝ (Fin 3))⟫| ≤ 1 := by
    simpa only [hσ, hy, one_mul] using abs_real_inner_le_norm
      (σ : EuclideanSpace ℝ (Fin 3)) (z.point.1 : EuclideanSpace ℝ (Fin 3))
  change |(|z.point.2 + s * ⟪(σ : EuclideanSpace ℝ (Fin 3)),
      (z.point.1 : EuclideanSpace ℝ (Fin 3))⟫| - |z.point.2|)| ≤ |s|
  calc
    _ ≤ |z.point.2 + s * ⟪(σ : EuclideanSpace ℝ (Fin 3)),
        (z.point.1 : EuclideanSpace ℝ (Fin 3))⟫ - z.point.2| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |s| * |⟪(σ : EuclideanSpace ℝ (Fin 3)),
        (z.point.1 : EuclideanSpace ℝ (Fin 3))⟫| := by rw [add_sub_cancel_left, abs_mul]
    _ ≤ |s| := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hχ (abs_nonneg s)
def dihedralEndMovingMap (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) : dihedralEndCarrier →
    (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
  dihedralEndMap L hL b A ∘ dihedralOddShearDiffeomorph σ s
def dihedralEndMovingDomain (L : ℝ)
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) : Set dihedralEndCarrier :=
  dihedralOddShearDiffeomorph σ s ⁻¹' dihedralEndDomain L
theorem dihedralEndMovingMap_localDiffeomorph (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (dihedralEndMovingMap.{u} L hL b A σ s) :=
  isLocalDiffeomorph_comp (dihedralEndMap_localDiffeomorph L hL b A)
    (dihedralOddShearDiffeomorph σ s).isLocalDiffeomorph
theorem dihedralEndMovingMap_metric_pullback (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) :
    localPullMetric (dihedralMetric ε L hε hL) (dihedralEndMovingMap L hL b A σ s)
      (dihedralEndMovingMap_localDiffeomorph L hL b A σ s) =
        Diffeomorph.pullbackMetricCross
          (dihedralEndMetric ε hε) (dihedralOddShearDiffeomorph σ s) := by
  calc
    _ = localPullMetric
        (localPullMetric (dihedralMetric ε L hε hL) (dihedralEndMap L hL b A)
          (dihedralEndMap_localDiffeomorph L hL b A)) (dihedralOddShearDiffeomorph σ s)
          (dihedralOddShearDiffeomorph σ s).isLocalDiffeomorph :=
      (localPullMetric_comp _ (dihedralEndMap L hL b A) (dihedralOddShearDiffeomorph σ s)
        (dihedralEndMap_localDiffeomorph L hL b A)
        (dihedralOddShearDiffeomorph σ s).isLocalDiffeomorph
        (dihedralEndMovingMap_localDiffeomorph L hL b A σ s)).symm
    _ = localPullMetric (dihedralEndMetric ε hε) (dihedralOddShearDiffeomorph σ s)
        (dihedralOddShearDiffeomorph σ s).isLocalDiffeomorph := by
      rw [dihedralEndMap_metric_pullback]
    _ = _ := localPullMetric_eq_pullbackMetricCross _ _
theorem dihedralEndMovingDomain_ball_subset (ε L R : ℝ) (hε : 0 < ε)
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) (p : dihedralEndCarrier)
    (hR : 0 < R) (hmargin : dihedralEndHeight p + R + |s| ≤ L / 2) :
    riemannianBallOf (dihedralEndMetric ε hε) p R ⊆ dihedralEndMovingDomain L σ s := by
  intro q hq
  have hd := (dihedralEndHeight_distance_le ε hε p q).trans_lt hq
  have hb := abs_lt.mp ((ENNReal.ofReal_lt_ofReal_iff hR).mp hd)
  have hshift := (abs_le.mp (dihedralOddShear_height_control σ s q)).2
  change dihedralEndHeight (dihedralOddShearDiffeomorph σ s q) < L / 2
  linarith [hb.1]
theorem exists_dihedralEndMovingPartial (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) :
    ∃ jm : PartialDiffeomorph (𝓡 3) (𝓡 3) dihedralEndCarrier
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier ∞,
      jm.source = dihedralEndMovingDomain L σ s ∧
      jm.target = dihedralEndMovingMap L hL b A σ s '' dihedralEndMovingDomain L σ s ∧
      (jm : dihedralEndCarrier → _) = dihedralEndMovingMap L hL b A σ s := by
  have hU : IsOpen (dihedralEndMovingDomain L σ s) :=
    (dihedralEndDomain_open L).preimage (dihedralOddShearDiffeomorph σ s).continuous
  have hne : (dihedralEndMovingDomain L σ s).Nonempty := by
    let q := dihedralEndProjection
      (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0))
    refine ⟨(dihedralOddShearDiffeomorph σ s).symm q, ?_⟩
    change dihedralOddShearDiffeomorph σ s ((dihedralOddShearDiffeomorph σ s).symm q) ∈
      dihedralEndDomain L
    rw [(dihedralOddShearDiffeomorph σ s).apply_symm_apply]
    change dihedralEndHeight q < L / 2
    rw [dihedralEndHeight_projection]
    change |(0 : ℝ)| < L / 2
    simpa only [abs_zero] using half_pos hL
  have hinj : Set.InjOn (dihedralEndMovingMap.{u} L hL b A σ s)
      (dihedralEndMovingDomain L σ s) := by
    intro x hx y hy hxy
    apply (dihedralOddShearDiffeomorph σ s).injective
    exact dihedralEndMap_injOn L hL b A hx hy hxy
  exact IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    ((dihedralEndMovingMap_localDiffeomorph L hL b A σ s).isLocalDiffeomorphOn _) hU hne hinj
theorem exists_dihedralEndMovingPointedMetricChart (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (b : Bool) (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) (p : dihedralEndCarrier)
    (hp : dihedralEndHeight p + |s| < L / 2) :
    ∃ jm : PartialDiffeomorph (𝓡 3) (𝓡 3) dihedralEndCarrier
        (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier ∞,
      ∃ hjm : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (jm : dihedralEndCarrier → _),
      jm.source = dihedralEndMovingDomain L σ s ∧
      jm.target = dihedralEndMovingMap L hL b A σ s '' dihedralEndMovingDomain L σ s ∧
      (jm : dihedralEndCarrier → _) = dihedralEndMovingMap L hL b A σ s ∧ p ∈ jm.source ∧
      localPullMetric (dihedralMetric ε L hε hL) jm hjm =
        Diffeomorph.pullbackMetricCross (dihedralEndMetric ε hε) (dihedralOddShearDiffeomorph σ s) ∧
      ∀ R : ℝ, 0 < R → dihedralEndHeight p + R + |s| ≤ L / 2 →
        riemannianBallOf (dihedralEndMetric ε hε) p R ⊆ jm.source := by
  obtain ⟨jm, hsrc, htgt, hfun⟩ := exists_dihedralEndMovingPartial L hL b A σ s
  have hjm : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (jm : dihedralEndCarrier → _) := by
    rw [hfun]
    exact dihedralEndMovingMap_localDiffeomorph L hL b A σ s
  have hpm : p ∈ dihedralEndMovingDomain L σ s := by
    have hshift := (abs_le.mp (dihedralOddShear_height_control σ s p)).2
    change dihedralEndHeight (dihedralOddShearDiffeomorph σ s p) < L / 2
    linarith
  refine ⟨jm, hjm, hsrc, htgt, hfun, hsrc.symm ▸ hpm, ?_, ?_⟩
  · simpa only [hfun] using dihedralEndMovingMap_metric_pullback ε L hε hL b A σ s
  · intro R hR hmargin
    rw [hsrc]
    exact dihedralEndMovingDomain_ball_subset ε L R hε σ s p hR hmargin
theorem dihedralEndMap_projection_formula (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (p : sphereCylinder) :
    dihedralEndMap.{u} L hL b A (dihedralEndProjection (sphereCylinderRechartDiffeomorph p)) =
      dihedralStandardPresentation.proj
        ((sphereDiffeo (n := 2) A) p.1, (if b then L - p.2 else p.2) / (2 * L)) := by
  have h : dihedralEndMap L hL b A (dihedralEndProjection (sphereCylinderRechartDiffeomorph p)) =
      dihedralEndRawMap L hL b A p := congrFun (dihedralEndMap_comp L hL b A)
        (sphereCylinderRechartDiffeomorph p)
  exact h.trans (dihedralEndRawMap_formula L hL b A p)
theorem dihedralEndMovingMap_anchor (L : ℝ) (hL : 0 < L) (b : Bool)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s c : ℝ) :
    dihedralEndMovingMap.{u} L hL b A σ s
      (dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, c))) =
      dihedralStandardPresentation.proj
        ((sphereDiffeo (n := 2) A) σ, (if b then L - (c + s) else c + s) / (2 * L)) := by
  change dihedralEndMap L hL b A (dihedralOddShearDiffeomorph σ s
    (dihedralEndProjection (sphereCylinderRechartDiffeomorph (σ, c)))) = _
  rw [dihedralOddShearDiffeomorph_anchor, dihedralEndMap_projection_formula]

end DifferentialGeometry.Geometry.Collapse
