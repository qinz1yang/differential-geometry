import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotient
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralAxis

/-!
The fixed projection has actual integer dihedral fibres. Physical cylinder charts on explicit
open strips are genuine partial diffeomorphisms into the same connected sum; their global
forward maps pull its metric back to the fixed spherical scale and unit physical line, and
their domains contain every model ball within both physical margins.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Topology GC.Endpoint
open GC.Geometry.SphericalProduct
open scoped Manifold ContDiff
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension
namespace DifferentialGeometry.Geometry.Collapse

theorem dihedralStandard_integer_normalForm {γ : CylinderIsometry}
    (hγ : γ ∈ dihedralGroup 0 (1 / 2)) :
    ∃ n : ℤ, (∀ p : sphereCylinder, cylinderAct γ p = (p.1, p.2 + (n : ℝ))) ∨
      (∀ p : sphereCylinder, cylinderAct γ p = (-p.1, (n : ℝ) - p.2)) := by
  induction hγ using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with rfl | rfl
    · refine ⟨0, Or.inr ?_⟩
      intro p
      simpa only [dihedralReflectionZero, Int.cast_zero, zero_sub] using
        cylinderAct_dihedralReflectionZero p
    · refine ⟨1, Or.inr ?_⟩
      simpa only [dihedralReflectionHalf, Int.cast_one] using cylinderAct_dihedralReflectionHalf
  | one =>
    refine ⟨0, Or.inl ?_⟩
    intro p
    simp only [cylinderAct_one, Int.cast_zero, add_zero, Prod.mk.eta]
  | mul a b ham hbm ha hb =>
    obtain ⟨n, hn | hn⟩ := ha
    · obtain ⟨m, hm | hm⟩ := hb
      · refine ⟨n + m, Or.inl ?_⟩
        intro p
        rw [cylinderAct_mul, hm, hn]
        apply Prod.ext
        · rfl
        · simp only [Int.cast_add]
          ring
      · refine ⟨n + m, Or.inr ?_⟩
        intro p
        rw [cylinderAct_mul, hm, hn]
        apply Prod.ext
        · rfl
        · simp only [Int.cast_add]
          ring
    · obtain ⟨m, hm | hm⟩ := hb
      · refine ⟨n - m, Or.inr ?_⟩
        intro p
        rw [cylinderAct_mul, hm, hn]
        apply Prod.ext
        · rfl
        · simp only [Int.cast_sub]
          ring
      · refine ⟨n - m, Or.inl ?_⟩
        intro p
        rw [cylinderAct_mul, hm, hn]
        apply Prod.ext (neg_neg p.1)
        simp only [Int.cast_sub]
        ring
  | inv a ham ha =>
    obtain ⟨n, hn | hn⟩ := ha
    · refine ⟨-n, Or.inl ?_⟩
      intro p
      apply (cylinderActDiffeo a).injective
      change cylinderAct a (cylinderAct a⁻¹ p) = cylinderAct a (p.1, p.2 + ((-n : ℤ) : ℝ))
      rw [← cylinderAct_mul, mul_inv_cancel, cylinderAct_one, hn]
      apply Prod.ext
      · rfl
      · simp only [Int.cast_neg]
        ring
    · refine ⟨n, Or.inr ?_⟩
      intro p
      apply (cylinderActDiffeo a).injective
      change cylinderAct a (cylinderAct a⁻¹ p) = cylinderAct a (-p.1, (n : ℝ) - p.2)
      rw [← cylinderAct_mul, mul_inv_cancel, cylinderAct_one, hn]
      apply Prod.ext (neg_neg p.1).symm
      ring

universe u
theorem dihedralProjection_middle_injOn : Set.InjOn dihedralStandardPresentation.{u}.proj
    {p : sphereCylinder | 0 < p.2 ∧ p.2 < 1 / 2} := by
  intro p hp q hq hpq
  obtain ⟨γ, hγ, hact⟩ := (dihedralStandardPresentation.fibres p q).mp hpq
  obtain ⟨n, hn | hn⟩ := dihedralStandard_integer_normalForm hγ
  · have h := (hn p).symm.trans hact
    have ht := congrArg Prod.snd h
    have hn1 : (n : ℝ) < 1 := by dsimp only [Prod.snd] at ht; linarith [hp.1, hp.2, hq.1, hq.2]
    have hnm1 : (-1 : ℝ) < n := by dsimp only [Prod.snd] at ht; linarith [hp.1, hp.2, hq.1, hq.2]
    have hni : n < 1 := by exact_mod_cast hn1
    have hnmi : (-1 : ℤ) < n := by exact_mod_cast hnm1
    have hn0 : n = 0 := by omega
    subst n
    simpa only [Int.cast_zero, add_zero, Prod.mk.eta] using h
  · have h := (hn p).symm.trans hact
    have ht := congrArg Prod.snd h
    have hn1 : (n : ℝ) < 1 := by dsimp only [Prod.snd] at ht; linarith [hp.2, hq.2]
    have hn0 : (0 : ℝ) < n := by dsimp only [Prod.snd] at ht; linarith [hp.1, hq.1]
    have hni : n < 1 := by exact_mod_cast hn1
    have hnpi : (0 : ℤ) < n := by exact_mod_cast hn0
    omega

theorem dihedralProjection_quarter_same_diagonal {p q : sphereCylinder}
    (hp : |p.2| < 1 / 4) (hq : |q.2| < 1 / 4)
    (hpq : dihedralStandardPresentation.{u}.proj p = dihedralStandardPresentation.proj q) :
    cylinderDiagonalQuotientMap p = cylinderDiagonalQuotientMap q := by
  obtain ⟨γ, hγ, hact⟩ := (dihedralStandardPresentation.fibres p q).mp hpq
  obtain ⟨n, hn⟩ := dihedralStandard_integer_normalForm hγ
  have hp' := abs_lt.mp hp
  have hq' := abs_lt.mp hq
  have hn0 : n = 0 := by
    have ht : ((n : ℝ) = q.2 - p.2) ∨ ((n : ℝ) = q.2 + p.2) := by
      rcases hn with h | h
      · have hcoord := congrArg Prod.snd ((h p).symm.trans hact)
        left
        dsimp only [Prod.snd] at hcoord
        linarith
      · have hcoord := congrArg Prod.snd ((h p).symm.trans hact)
        right
        dsimp only [Prod.snd] at hcoord
        linarith
    have hupper : (n : ℝ) < 1 := by rcases ht with h | h <;> linarith [hp'.1, hp'.2, hq'.1, hq'.2]
    have hlower : (-1 : ℝ) < n := by rcases ht with h | h <;> linarith [hp'.1, hp'.2, hq'.1, hq'.2]
    have hi : n < 1 := by exact_mod_cast hupper
    have hlo : (-1 : ℤ) < n := by exact_mod_cast hlower
    omega
  subst n
  rcases hn with h | h
  · have heq : p = q := by
      simpa only [Int.cast_zero, add_zero, Prod.mk.eta] using (h p).symm.trans hact
    exact congrArg cylinderDiagonalQuotientMap heq
  · have heq : q = cylinderDiagonalDiffeomorph p := by
      rw [cylinderDiagonalDiffeomorph_apply]
      simpa only [cylinderDiagonal, Int.cast_zero, zero_sub] using
        ((h p).symm.trans hact).symm
    exact (cylinderDiagonalQuotientMap_eq_iff.mpr (Or.inr heq)).symm

def dihedralLineDilation (L : ℝ) (hL : 0 < L) : sphereCylinder ≃ₘ⟮
    (𝓡 2).prod 𝓘(ℝ, ℝ), (𝓡 2).prod 𝓘(ℝ, ℝ)⟯ sphereCylinder :=
  (Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ (2 * L)⁻¹
      (inv_ne_zero (mul_ne_zero (by norm_num) hL.ne'))).toContinuousLinearEquiv.toDiffeomorph
def dihedralPhysicalDiffeo (L : ℝ) (hL : 0 < L) (γ : CylinderIsometry) :
    sphereCylinderRechart ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereCylinderRechart :=
  sphereCylinderRechartDiffeomorph.symm.trans
    (((cylinderActDiffeo γ).trans (dihedralLineDilation L hL)).trans
      sphereCylinderRechartDiffeomorph)
def dihedralCylinderPhysicalDiffeo (L : ℝ) (hL : 0 < L) (s : ℝ)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    sphereCylinderRechart ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereCylinderRechart :=
  dihedralPhysicalDiffeo L hL (A, AffineIsometryEquiv.constVAdd ℝ ℝ s)
def dihedralPhysicalMap (L : ℝ) (hL : 0 < L) (γ : CylinderIsometry) :
    sphereCylinderRechart →
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
  dihedralProjection ∘ dihedralPhysicalDiffeo L hL γ
theorem dihedralPhysicalMap_localDiffeomorph (L : ℝ) (hL : 0 < L) (γ : CylinderIsometry) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (dihedralPhysicalMap.{u} L hL γ) :=
  isLocalDiffeomorph_comp dihedralProjection_localDiffeomorph
    (dihedralPhysicalDiffeo L hL γ).isLocalDiffeomorph
theorem dihedralCylinderPhysical_formula (L : ℝ) (hL : 0 < L) (s : ℝ)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (z : sphereCylinderRechart) :
    sphereCylinderRechartDiffeomorph.symm (dihedralCylinderPhysicalDiffeo L hL s A z) =
      ((sphereDiffeo (n := 2) A) z.point.1, (s + z.point.2) / (2 * L)) := by
  change sphereCylinderRechartDiffeomorph.symm
    (sphereCylinderRechartDiffeomorph
      (dihedralLineDilation L hL (cylinderActDiffeo
        (A, AffineIsometryEquiv.constVAdd ℝ ℝ s) (sphereCylinderRechartDiffeomorph.symm z)))) = _
  rw [sphereCylinderRechartDiffeomorph.symm_apply_apply]
  apply Prod.ext
  · rfl
  · change (2 * L)⁻¹ * (s + z.point.2) = (s + z.point.2) / (2 * L)
    rw [div_eq_mul_inv, mul_comm]
def dihedralCylinderMap (L : ℝ) (hL : 0 < L) (s : ℝ)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    sphereCylinderRechart →
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
  dihedralProjection ∘ dihedralCylinderPhysicalDiffeo L hL s A
theorem dihedralCylinderMap_localDiffeomorph (L : ℝ) (hL : 0 < L) (s : ℝ)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (dihedralCylinderMap.{u} L hL s A) :=
  isLocalDiffeomorph_comp dihedralProjection_localDiffeomorph
    (dihedralCylinderPhysicalDiffeo L hL s A).isLocalDiffeomorph
def dihedralCylinderDomain (L s : ℝ) : Set sphereCylinderRechart :=
  {z | -s < z.point.2 ∧ z.point.2 < L - s}
theorem dihedralCylinderMap_injOn (L : ℝ) (hL : 0 < L) (s : ℝ)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    Set.InjOn (dihedralCylinderMap.{u} L hL s A) (dihedralCylinderDomain L s) := by
  have hphase (z : sphereCylinderRechart) (hz : z ∈ dihedralCylinderDomain L s) :
      sphereCylinderRechartDiffeomorph.symm (dihedralCylinderPhysicalDiffeo L hL s A z) ∈
        {p : sphereCylinder | 0 < p.2 ∧ p.2 < 1 / 2} := by
    rw [dihedralCylinderPhysical_formula]
    have hp : 0 < 2 * L := mul_pos (by norm_num) hL
    constructor
    · exact div_pos (by change -s < z.point.2 ∧ z.point.2 < L - s at hz; linarith [hz.1]) hp
    · apply (div_lt_iff₀ hp).mpr
      change -s < z.point.2 ∧ z.point.2 < L - s at hz
      nlinarith [hz.2]
  intro z hz w hw hzw
  apply (dihedralCylinderPhysicalDiffeo L hL s A).injective
  apply sphereCylinderRechartDiffeomorph.symm.injective
  apply dihedralProjection_middle_injOn (hphase z hz) (hphase w hw)
  exact hzw
private theorem dihedralCylinderAxis_continuous :
    Continuous (fun z : sphereCylinderRechart => z.point.2) :=
  continuous_snd.comp sphereCylinderRechartDiffeomorph.symm.continuous
theorem dihedralCylinderDomain_open (L s : ℝ) : IsOpen (dihedralCylinderDomain L s) :=
  (isOpen_lt continuous_const dihedralCylinderAxis_continuous).inter
    (isOpen_lt dihedralCylinderAxis_continuous continuous_const)
theorem exists_dihedralCylinderPartial (L : ℝ) (hL : 0 < L) (s : ℝ) (hs : 0 < s) (hsL : s < L)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ∃ jm : PartialDiffeomorph (𝓡 3) (𝓡 3) sphereCylinderRechart
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier ∞,
      jm.source = dihedralCylinderDomain L s ∧
      jm.target = dihedralCylinderMap L hL s A '' dihedralCylinderDomain L s ∧
      (jm : sphereCylinderRechart → _) = dihedralCylinderMap L hL s A ∧
      sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0) ∈ jm.source := by
  have hn : sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0) ∈
      dihedralCylinderDomain L s := by
    change -s < (0 : ℝ) ∧ (0 : ℝ) < L - s
    constructor <;> linarith
  obtain ⟨jm, hsrc, htgt, hfun⟩ :=
    IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
      ((dihedralCylinderMap_localDiffeomorph L hL s A).isLocalDiffeomorphOn _)
      (dihedralCylinderDomain_open L s) ⟨_, hn⟩ (dihedralCylinderMap_injOn L hL s A)
  exact ⟨jm, hsrc, htgt, hfun, hsrc.symm ▸ hn⟩

private theorem dihedralThinDilationMetric (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    Diffeomorph.pullbackMetric (dihedralThinCylinderMetric ε L hε hL)
      (dihedralLineDilation L hL) = dihedralThinCylinderMetric ε (1 / 2) hε (by norm_num) := by
  simp only [dihedralThinCylinderMetric]
  rw [dihedralLineDilation, Diffeomorph.pullbackMetric_prodCongr, Diffeomorph.pullbackMetric_refl]
  rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetricCross_scaleMetric,
    Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetric_euclidean_smul]
  congr 1
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [scaleMetric_inner]
  have he : (2 * L) ^ 2 * ((2 * L)⁻¹) ^ 2 = 1 := by
    field_simp
  norm_num only
  rw [← mul_assoc, he, one_mul]
open private localPullMetric_eq_pullbackMetricCross
from DifferentialGeometry.Geometry.Metric.DistancePullback
theorem dihedralPhysicalMap_metric_pullback (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (γ : CylinderIsometry) :
    localPullMetric (dihedralMetric.{u} ε L hε hL) (dihedralPhysicalMap L hL γ)
      (dihedralPhysicalMap_localDiffeomorph L hL γ) =
      dihedralRechartedMetric ε (1 / 2) hε (by norm_num) := by
  have heq : (dihedralPhysicalDiffeo L hL γ).trans
      sphereCylinderRechartDiffeomorph.symm = sphereCylinderRechartDiffeomorph.symm.trans
      ((cylinderActDiffeo γ).trans
        (dihedralLineDilation L hL)) := by
    apply Diffeomorph.ext
    intro z
    change sphereCylinderRechartDiffeomorph.symm (sphereCylinderRechartDiffeomorph
      (dihedralLineDilation L hL (cylinderActDiffeo γ
        (sphereCylinderRechartDiffeomorph.symm z)))) = _
    rw [sphereCylinderRechartDiffeomorph.symm_apply_apply]
    rfl
  calc
    _ = localPullMetric
        (localPullMetric (dihedralMetric ε L hε hL) dihedralProjection
          dihedralProjection_localDiffeomorph)
        (dihedralPhysicalDiffeo L hL γ)
        (dihedralPhysicalDiffeo L hL γ).isLocalDiffeomorph :=
      (localPullMetric_comp _ dihedralProjection (dihedralPhysicalDiffeo L hL γ)
        dihedralProjection_localDiffeomorph
        (dihedralPhysicalDiffeo L hL γ).isLocalDiffeomorph
        (dihedralPhysicalMap_localDiffeomorph L hL γ)).symm
    _ = Diffeomorph.pullbackMetricCross (dihedralRechartedMetric ε L hε hL)
        (dihedralPhysicalDiffeo L hL γ) := by
      rw [dihedralMetric_pullback, localPullMetric_eq_pullbackMetricCross]
    _ = _ := by
      rw [dihedralRechartedMetric, Diffeomorph.pullbackMetricCross_trans, heq,
        ← Diffeomorph.pullbackMetricCross_trans,
        Diffeomorph.pullbackMetricCross_eq_pullbackMetric, ← Diffeomorph.pullbackMetric_trans,
        dihedralThinDilationMetric, dihedralThinCylinderMetric_invariant]
      rfl

theorem dihedralCylinderMap_metric_pullback (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) (s : ℝ)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    localPullMetric (dihedralMetric.{u} ε L hε hL) (dihedralCylinderMap L hL s A)
      (dihedralCylinderMap_localDiffeomorph L hL s A) =
      dihedralRechartedMetric ε (1 / 2) hε (by norm_num) :=
  dihedralPhysicalMap_metric_pullback ε L hε hL (A, AffineIsometryEquiv.constVAdd ℝ ℝ s)

private theorem dihedralHalfMetric_eq_prod (ε : ℝ) (hε : 0 < ε) :
    dihedralThinCylinderMetric ε (1 / 2) hε (by norm_num) =
      (scaleMetric (ε ^ 2) (pow_pos hε 2)
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).prod
          (DifferentialGeometry.euclideanMetric (E := ℝ)) := by
  dsimp only [dihedralThinCylinderMetric]
  congr 1
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [scaleMetric_inner]
  norm_num
private theorem dihedralModel_line_distance_le (ε : ℝ) (hε : 0 < ε)
    (z w : sphereCylinderRechart) :
    ENNReal.ofReal |z.point.2 - w.point.2| ≤
      riemannianEDistOf (dihedralRechartedMetric ε (1 / 2) hε (by norm_num)) z w := by
  rw [dihedralRechartedMetric, DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross,
    dihedralHalfMetric_eq_prod]
  have h := riemannianEDistOf_snd_le_prod
    (scaleMetric (ε ^ 2) (pow_pos hε 2)
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)))
    (DifferentialGeometry.euclideanMetric (E := ℝ)) z.point w.point
  rw [show DifferentialGeometry.euclideanMetric (E := ℝ) = standardEuclideanMetric ℝ from rfl,
    riemannianEDistOf_standardEuclideanMetric, edist_dist, Real.dist_eq] at h
  exact h
theorem dihedralCylinderDomain_ball_subset (ε L s R : ℝ) (hε : 0 < ε) (hR : 0 < R)
    (hRs : R ≤ s) (hRLs : R ≤ L - s) :
    riemannianBallOf (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
      (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) R ⊆
      dihedralCylinderDomain L s := by
  intro z hz
  have hdist := (dihedralModel_line_distance_le ε hε
    (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) z).trans_lt hz
  change ENNReal.ofReal |0 - z.point.2| < ENNReal.ofReal R at hdist
  have ht : |z.point.2| < R := by
    apply (ENNReal.ofReal_lt_ofReal_iff hR).mp
    simpa only [zero_sub, abs_neg] using hdist
  have habs := abs_lt.mp ht
  constructor <;> linarith [habs.1, habs.2]

theorem dihedralPhysical_formula (L : ℝ) (hL : 0 < L) (γ : CylinderIsometry)
    (z : sphereCylinderRechart) :
    sphereCylinderRechartDiffeomorph.symm (dihedralPhysicalDiffeo L hL γ z) =
      ((sphereDiffeo (n := 2) γ.1) z.point.1, γ.2 z.point.2 / (2 * L)) := by
  change sphereCylinderRechartDiffeomorph.symm
    (sphereCylinderRechartDiffeomorph
      (dihedralLineDilation L hL (cylinderActDiffeo γ
        (sphereCylinderRechartDiffeomorph.symm z)))) = _
  rw [sphereCylinderRechartDiffeomorph.symm_apply_apply]
  apply Prod.ext
  · rfl
  · change (2 * L)⁻¹ * (γ.2 z.point.2) = γ.2 z.point.2 / (2 * L)
    rw [div_eq_mul_inv, mul_comm]
theorem exists_dihedralCylinderPointedMetricChart (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (s : ℝ) (hs : 0 < s) (hsL : s < L)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ∃ (jm : PartialDiffeomorph (𝓡 3) (𝓡 3) sphereCylinderRechart
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier ∞)
      (hjm : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (jm : sphereCylinderRechart → _)),
      jm.source = dihedralCylinderDomain L s ∧
      jm.target = dihedralCylinderMap L hL s A '' dihedralCylinderDomain L s ∧
      (jm : sphereCylinderRechart → _) = dihedralCylinderMap L hL s A ∧
      sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0) ∈ jm.source ∧
      localPullMetric (dihedralMetric ε L hε hL) jm hjm =
        dihedralRechartedMetric ε (1 / 2) hε (by norm_num) ∧
      ∀ R : ℝ, 0 < R → R ≤ s → R ≤ L - s →
        riemannianBallOf (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
          (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) R ⊆
          jm.source := by
  obtain ⟨jm, hsrc, htgt, hfun, hn⟩ := exists_dihedralCylinderPartial L hL s hs hsL A
  have hjm : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (jm : sphereCylinderRechart → _) := by
    rw [hfun]
    exact dihedralCylinderMap_localDiffeomorph L hL s A
  refine ⟨jm, hjm, hsrc, htgt, hfun, hn, ?_, ?_⟩
  · simpa only [hfun] using dihedralCylinderMap_metric_pullback ε L hε hL s A
  · intro R hR hRs hRLs
    rw [hsrc]
    exact dihedralCylinderDomain_ball_subset ε L s R hε hR hRs hRLs

end DifferentialGeometry.Geometry.Collapse
