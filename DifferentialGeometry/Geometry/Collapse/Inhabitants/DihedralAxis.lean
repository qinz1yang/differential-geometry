import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralMetric
import DifferentialGeometry.Geometry.Metric.LocalIsometryCovering
import DifferentialGeometry.Geometry.Metric.DistancePullback
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
The folded axis of the same thin projective-sum metric has two genuine distinct tips.
The quotient projection is a covering by the actual complete cylindrical metric, allowing
lower distance estimates to be checked through lifted paths rather than presumed isometry.
-/

set_option autoImplicit false

noncomputable section

open Manifold Set Function
open DifferentialGeometry DifferentialGeometry.Topology
open GC.Endpoint GC.Geometry.SphericalProduct GC.GraphManifold.Assembly
open scoped Manifold ContDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] DifferentialGeometry.Geometry.Collapse.sphereDimension
  DifferentialGeometry.Geometry.Collapse.cylinderDimension
  DifferentialGeometry.Geometry.Collapse.sphereCompact
  DifferentialGeometry.Geometry.Collapse.sphereConnected
  DifferentialGeometry.Geometry.Collapse.threeSigmaCompact

open private slimSphere_factor_bound
from DifferentialGeometry.Geometry.Collapse.Inhabitants.SlimSphere

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem dihedralFold_invariant {γ : CylinderIsometry} (hγ : γ ∈ dihedralGroup 0 (1 / 2)) :
    ∀ t : ℝ, ‖(γ.2 t : AddCircle (1 : ℝ))‖ = ‖(t : AddCircle (1 : ℝ))‖ := by
  induction hγ using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with rfl | rfl
    · intro t
      simp only [AffineIsometryEquiv.pointReflection_apply, vsub_eq_sub, zero_sub,
        vadd_eq_add, add_zero, AddCircle.coe_neg, norm_neg]
    · intro t
      have heq : (AffineIsometryEquiv.pointReflection ℝ (1 / 2)) t = 1 - t := by
        simp only [AffineIsometryEquiv.pointReflection_apply, vsub_eq_sub, vadd_eq_add]
        ring
      rw [heq, AddCircle.coe_sub, AddCircle.coe_period, zero_sub, norm_neg]
  | one => intro t; rfl
  | mul a b ham hbm ha hb =>
    intro t
    exact (ha (b.2 t)).trans (hb t)
  | inv a ham ha =>
    intro t
    change ‖(a.2⁻¹ t : AddCircle (1 : ℝ))‖ = ‖(t : AddCircle (1 : ℝ))‖
    have h := ha (a.2⁻¹ t)
    rw [AffineIsometryEquiv.coe_inv, AffineIsometryEquiv.apply_symm_apply] at h
    exact h.symm

def dihedralAxis (L : ℝ) (x :
    (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier) : ℝ :=
  2 * L * ‖((sphereCylinderRechartDiffeomorph.symm
    (Classical.choose (dihedralProjection_surjective x))).2 : AddCircle (1 : ℝ))‖

theorem dihedralAxis_projection (L : ℝ) (p : sphereCylinderRechart) :
    dihedralAxis.{u} L (dihedralProjection p) =
      2 * L * ‖((sphereCylinderRechartDiffeomorph.symm p).2 : AddCircle (1 : ℝ))‖ := by
  let q := Classical.choose (dihedralProjection_surjective (dihedralProjection.{u} p))
  have hq : dihedralProjection.{u} q = dihedralProjection p :=
    Classical.choose_spec (dihedralProjection_surjective (dihedralProjection p))
  obtain ⟨γ, hγ, heq⟩ := (dihedralStandardPresentation.fibres
    (sphereCylinderRechartDiffeomorph.symm q)
    (sphereCylinderRechartDiffeomorph.symm p)).mp hq
  have ht := congrArg Prod.snd heq
  change γ.2 (sphereCylinderRechartDiffeomorph.symm q).2 =
    (sphereCylinderRechartDiffeomorph.symm p).2 at ht
  have hn := dihedralFold_invariant hγ (sphereCylinderRechartDiffeomorph.symm q).2
  rw [ht] at hn
  exact congrArg (fun r : ℝ => 2 * L * r) hn.symm

theorem dihedralAxis_mem_Icc (L : ℝ) (hL : 0 < L) (x :
    (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier) :
    dihedralAxis L x ∈ Set.Icc 0 L := by
  have hn := AddCircle.norm_le_half_period (1 : ℝ) (x :=
    ((sphereCylinderRechartDiffeomorph.symm
      (Classical.choose (dihedralProjection_surjective x))).2 : AddCircle (1 : ℝ)))
    one_ne_zero
  simp only [abs_one] at hn
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) hL.le) (norm_nonneg _)
  · dsimp only [dihedralAxis]
    nlinarith

theorem dihedralAxis_tips (L : ℝ) :
    dihedralAxis.{u} L
      (dihedralProjection (sphereCylinderRechartDiffeomorph (northPole, 0))) = 0 ∧
    dihedralAxis.{u} L
      (dihedralProjection (sphereCylinderRechartDiffeomorph (northPole, 1 / 2))) = L := by
  constructor
  · rw [dihedralAxis_projection, sphereCylinderRechartDiffeomorph.symm_apply_apply]
    simp
  · rw [dihedralAxis_projection, sphereCylinderRechartDiffeomorph.symm_apply_apply]
    have hn : ‖((1 / 2 : ℝ) : AddCircle (1 : ℝ))‖ = 1 / 2 := by
      simpa only [abs_one] using AddCircle.norm_half_period_eq (1 : ℝ)
    change 2 * L * ‖((1 / 2 : ℝ) : AddCircle (1 : ℝ))‖ = L
    rw [hn]
    ring

def dihedralLeftTip :
    (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
  dihedralProjection (sphereCylinderRechartDiffeomorph (northPole, 0))

def dihedralRightTip :
    (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
  dihedralProjection (sphereCylinderRechartDiffeomorph (northPole, 1 / 2))

theorem dihedralAxis_leftTip (L : ℝ) : dihedralAxis L dihedralLeftTip.{u} = 0 :=
  (dihedralAxis_tips L).1

theorem dihedralAxis_rightTip (L : ℝ) : dihedralAxis L dihedralRightTip.{u} = L :=
  (dihedralAxis_tips L).2

theorem dihedralTips_ne : dihedralLeftTip.{u} ≠ dihedralRightTip := by
  intro heq
  have h := congrArg (dihedralAxis 1) heq
  rw [dihedralAxis_leftTip, dihedralAxis_rightTip] at h
  norm_num at h

theorem dihedralRechartedMetric_complete (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    DifferentialGeometry.RiemannianMetricComplete (dihedralRechartedMetric ε L hε hL) := by
  apply DifferentialGeometry.RiemannianMetricComplete.pullbackCross
  exact ((DifferentialGeometry.RiemannianMetricComplete.of_compact
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).scaleMetric
      (ε ^ 2) (pow_pos hε 2)).prod
      ((euclideanMetric_complete (E := ℝ)).scaleMetric
        ((2 * L) ^ 2) (pow_pos (mul_pos (by norm_num) hL) 2))

theorem dihedralProjection_covering : IsCoveringMap dihedralProjection.{u} := by
  let onePositive : 0 < (1 : ℝ) := zero_lt_one
  let g := dihedralRechartedMetric 1 1 onePositive onePositive
  have hcomplete : DifferentialGeometry.RiemannianMetricComplete g :=
    dihedralRechartedMetric_complete 1 1 onePositive onePositive
  exact (DifferentialGeometry.isCoveringMap_of_isLocalIsometry g
    (dihedralMetric.{u} 1 1 onePositive onePositive) hcomplete
    dihedralProjection_localDiffeomorph (fun x v w =>
      (localPullMetric_inner (dihedralMetric.{u} 1 1 onePositive onePositive)
        dihedralProjection dihedralProjection_localDiffeomorph x v w).symm.trans
        (congrArg (fun metric => metric.inner x v w)
          (dihedralMetric_pullback 1 1 onePositive onePositive)))).1

private theorem dihedralFold_difference_le (s t : ℝ) :
    |‖(s : AddCircle (1 : ℝ))‖ - ‖(t : AddCircle (1 : ℝ))‖| ≤ |s - t| := by
  have hnorm : ‖((s - t : ℝ) : AddCircle (1 : ℝ))‖ ≤ |s - t| := by
    simpa only [Real.norm_eq_abs] using
      (QuotientAddGroup.norm_mk_le_norm (m := s - t)
        (S := AddSubgroup.zmultiples (1 : ℝ)))
  exact (abs_norm_sub_norm_le (s : AddCircle (1 : ℝ)) (t : AddCircle (1 : ℝ))).trans
    ((congrArg norm (AddCircle.coe_sub (1 : ℝ) s t)).symm.le.trans hnorm)

private theorem dihedralSource_axis_distance_le (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (x y : sphereCylinderRechart) :
    ENNReal.ofReal |dihedralAxis.{u} L (dihedralProjection x) -
      dihedralAxis L (dihedralProjection y)| ≤
      riemannianEDistOf (dihedralRechartedMetric ε L hε hL) x y := by
  let s := (sphereCylinderRechartDiffeomorph.symm x).2
  let t := (sphereCylinderRechartDiffeomorph.symm y).2
  have hL2 : 0 < 2 * L := mul_pos (by norm_num) hL
  have hfold : |2 * L * ‖(s : AddCircle (1 : ℝ))‖ -
      2 * L * ‖(t : AddCircle (1 : ℝ))‖| ≤ 2 * L * |s - t| := by
    rw [← mul_sub, abs_mul, abs_of_pos hL2]
    exact mul_le_mul_of_nonneg_left (dihedralFold_difference_le s t) hL2.le
  rw [dihedralAxis_projection, dihedralAxis_projection]
  refine (ENNReal.ofReal_le_ofReal hfold).trans ?_
  rw [dihedralRechartedMetric, riemannianEDistOf_pullbackMetricCross]
  have hprod := riemannianEDistOf_snd_le_prod
    (scaleMetric (ε ^ 2) (pow_pos hε 2)
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)))
    (scaleMetric ((2 * L) ^ 2) (pow_pos hL2 2)
      (DifferentialGeometry.euclideanMetric (E := ℝ)))
    (sphereCylinderRechartDiffeomorph.symm x) (sphereCylinderRechartDiffeomorph.symm y)
  have hline : riemannianEDistOf (DifferentialGeometry.euclideanMetric (E := ℝ)) s t =
      ENNReal.ofReal |s - t| := by
    rw [show DifferentialGeometry.euclideanMetric (E := ℝ) =
      standardEuclideanMetric ℝ from rfl, riemannianEDistOf_standardEuclideanMetric,
      edist_dist, Real.dist_eq]
  rw [edistOf_scale, Real.sqrt_sq_eq_abs, abs_of_pos hL2, hline,
    ← ENNReal.ofReal_mul hL2.le] at hprod
  exact hprod

theorem dihedralAxis_distance_le (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (x y : (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier) :
    ENNReal.ofReal |dihedralAxis L x - dihedralAxis L y| ≤
      riemannianEDistOf (dihedralMetric ε L hε hL) x y := by
  obtain ⟨p, rfl⟩ := dihedralProjection_surjective x
  apply le_edistOf_of_coveringMap_localPullMetric
    (dihedralRechartedMetric ε L hε hL) (dihedralMetric ε L hε hL)
    dihedralProjection_localDiffeomorph dihedralProjection_covering
    (dihedralMetric_pullback ε L hε hL) p y
  intro q hq
  rw [← hq]
  exact dihedralSource_axis_distance_le ε L hε hL p q

theorem dihedralTips_distance_ge (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    ENNReal.ofReal L ≤ riemannianEDistOf (dihedralMetric.{u} ε L hε hL)
      dihedralLeftTip dihedralRightTip := by
  have h := dihedralAxis_distance_le ε L hε hL dihedralLeftTip.{u} dihedralRightTip
  simpa only [dihedralAxis_leftTip, dihedralAxis_rightTip, zero_sub, abs_neg,
    abs_of_pos hL] using h


private theorem dihedralAct_projection (γ : CylinderIsometry)
    (hγ : γ ∈ dihedralGroup 0 (1 / 2)) (p : sphereCylinder) :
    dihedralProjection.{u} (sphereCylinderRechartDiffeomorph (cylinderAct γ p)) =
      dihedralProjection (sphereCylinderRechartDiffeomorph p) := by
  simp only [dihedralProjection, Function.comp_apply,
    sphereCylinderRechartDiffeomorph.symm_apply_apply]
  exact (dihedralStandardPresentation.fibres p (cylinderAct γ p)).mpr ⟨γ, hγ, rfl⟩ |>.symm

theorem exists_dihedralCanonicalLift
    (x : (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier) :
    ∃ p : sphereCylinder, dihedralProjection (sphereCylinderRechartDiffeomorph p) = x ∧
      p.2 ∈ Icc (0 : ℝ) (1 / 2) ∧ ∀ L, dihedralAxis L x = 2 * L * p.2 := by
  obtain ⟨q, hq⟩ := dihedralProjection_surjective x
  let p := sphereCylinderRechartDiffeomorph.symm q
  let t := p.2
  let a : CylinderIsometry :=
    (LinearIsometryEquiv.neg ℝ, AffineIsometryEquiv.pointReflection ℝ 0)
  let b : CylinderIsometry :=
    (LinearIsometryEquiv.neg ℝ, AffineIsometryEquiv.pointReflection ℝ (1 / 2))
  have ha : a ∈ dihedralGroup 0 (1 / 2) := Subgroup.subset_closure (Or.inl rfl)
  have hb : b ∈ dihedralGroup 0 (1 / 2) := Subgroup.subset_closure (Or.inr rfl)
  let c := b * a
  have hc : c ∈ dihedralGroup 0 (1 / 2) := (dihedralGroup 0 (1 / 2)).mul_mem hb ha
  have hcLine : ∀ s : ℝ, c.2 s = s + 1 := by
    intro s
    change (AffineIsometryEquiv.pointReflection ℝ (1 / 2))
      ((AffineIsometryEquiv.pointReflection ℝ 0) s) = s + 1
    simp only [AffineIsometryEquiv.pointReflection_apply, vsub_eq_sub, vadd_eq_add]
    ring
  let n : ℤ := -(round t)
  let p' := cylinderAct (c ^ n) p
  have hn : c ^ n ∈ dihedralGroup 0 (1 / 2) := (dihedralGroup 0 (1 / 2)).zpow_mem hc n
  have hp' : dihedralProjection (sphereCylinderRechartDiffeomorph p') = x := by
    rw [dihedralAct_projection (c ^ n) hn p]
    change dihedralProjection
      (sphereCylinderRechartDiffeomorph (sphereCylinderRechartDiffeomorph.symm q)) = x
    rw [sphereCylinderRechartDiffeomorph.apply_symm_apply]
    exact hq
  have ht' : p'.2 = t - (round t : ℝ) := by
    change ((c ^ n).2) t = _
    rw [Prod.pow_snd, line_zpow_apply hcLine n t]
    simp only [n, Int.cast_neg, mul_one, sub_eq_add_neg]
  have hnorm : ‖(t : AddCircle (1 : ℝ))‖ = |p'.2| := by
    rw [ht', AddCircle.norm_eq]
    simp only [inv_one, one_mul, mul_one]
  have assemble (y : sphereCylinder)
      (hy : dihedralProjection (sphereCylinderRechartDiffeomorph y) = x)
      (ht : y.2 = ‖(t : AddCircle (1 : ℝ))‖) :
      ∃ p : sphereCylinder, dihedralProjection (sphereCylinderRechartDiffeomorph p) = x ∧
        p.2 ∈ Icc (0 : ℝ) (1 / 2) ∧ ∀ L, dihedralAxis L x = 2 * L * p.2 := by
    have hhalf := AddCircle.norm_le_half_period (1 : ℝ)
      (x := (t : AddCircle (1 : ℝ))) one_ne_zero
    simp only [abs_one] at hhalf
    have hy0 : 0 ≤ y.2 := ht.symm ▸ norm_nonneg _
    have hyhalf : y.2 ≤ 1 / 2 := ht.symm ▸ hhalf
    refine ⟨y, hy, ⟨hy0, hyhalf⟩, ?_⟩
    have hny : ‖(y.2 : AddCircle (1 : ℝ))‖ = y.2 := by
      have h := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr
        (show |y.2| ≤ |(1 : ℝ)| / 2 by
          simpa only [abs_one, abs_of_nonneg hy0] using hyhalf)
      exact h.trans (abs_of_nonneg hy0)
    intro L
    rw [← hy, dihedralAxis_projection, sphereCylinderRechartDiffeomorph.symm_apply_apply]
    exact congrArg (fun r => 2 * L * r) hny
  by_cases hp0 : 0 ≤ p'.2
  · apply assemble p' hp'
    simpa only [abs_of_nonneg hp0] using hnorm.symm
  · let p'' := cylinderAct a p'
    have hp'' : dihedralProjection (sphereCylinderRechartDiffeomorph p'') = x :=
      (dihedralAct_projection a ha p').trans hp'
    apply assemble p'' hp''
    have ht'' : p''.2 = -p'.2 := by
      change (AffineIsometryEquiv.pointReflection ℝ 0) p'.2 = -p'.2
      simp only [AffineIsometryEquiv.pointReflection_apply, vsub_eq_sub,
        zero_sub, vadd_eq_add, add_zero]
    rw [ht'']
    simpa only [abs_of_neg (lt_of_not_ge hp0)] using hnorm.symm


theorem exists_dihedralAxis_distortion :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L),
      ∀ x y : (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier,
        riemannianEDistOf (dihedralMetric ε L hε hL) x y ≤
          ENNReal.ofReal (|dihedralAxis L x - dihedralAxis L y| + ε * D) := by
  obtain ⟨D, hD, hbound⟩ := slimSphere_factor_bound
  refine ⟨D, hD, ?_⟩
  intro ε L hε hL x y
  obtain ⟨px, hx, hrx, hax⟩ := exists_dihedralCanonicalLift x
  obtain ⟨py, hy, hry, hay⟩ := exists_dihedralCanonicalLift y
  let xp := sphereCylinderRechartDiffeomorph px
  let yp := sphereCylinderRechartDiffeomorph py
  have hinner (z : sphereCylinderRechart) (v : TangentSpace (𝓡 3) z) :
      (dihedralMetric ε L hε hL).inner (dihedralProjection z)
        (mfderiv (𝓡 3) (𝓡 3) dihedralProjection z v)
        (mfderiv (𝓡 3) (𝓡 3) dihedralProjection z v) =
      (dihedralRechartedMetric ε L hε hL).inner z v v :=
    (localPullMetric_inner (dihedralMetric ε L hε hL)
      dihedralProjection dihedralProjection_localDiffeomorph z v v).symm.trans
      (congrArg (fun metric => metric.inner z v v) (dihedralMetric_pullback ε L hε hL))
  have hmap := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
    (dihedralRechartedMetric ε L hε hL) (dihedralMetric ε L hε hL)
    dihedralProjection dihedralProjection_localDiffeomorph zero_lt_one
    (fun z v => by rw [one_mul]; exact (hinner z v).le) xp yp
  simp only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hmap
  change riemannianEDistOf (dihedralMetric ε L hε hL)
    (dihedralProjection (sphereCylinderRechartDiffeomorph px))
    (dihedralProjection (sphereCylinderRechartDiffeomorph py)) ≤ _ at hmap
  rw [hx, hy, dihedralRechartedMetric, riemannianEDistOf_pullbackMetricCross,
    sphereCylinderRechartDiffeomorph.symm_apply_apply,
    sphereCylinderRechartDiffeomorph.symm_apply_apply] at hmap
  have hL2 : 0 < 2 * L := mul_pos (by norm_num) hL
  have hsphere : riemannianEDistOf
      (scaleMetric (ε ^ 2) (pow_pos hε 2)
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))) px.1 py.1 ≤
      ENNReal.ofReal (ε * D) := by
    rw [edistOf_scale, Real.sqrt_sq_eq_abs, abs_of_pos hε, ENNReal.ofReal_mul hε.le]
    exact mul_le_mul_of_nonneg_left (hbound px.1 py.1) (by positivity)
  have hline : riemannianEDistOf
      (scaleMetric ((2 * L) ^ 2) (pow_pos hL2 2)
        (DifferentialGeometry.euclideanMetric (E := ℝ))) px.2 py.2 =
      ENNReal.ofReal (2 * L * |px.2 - py.2|) := by
    rw [edistOf_scale, Real.sqrt_sq_eq_abs, abs_of_pos hL2,
      show DifferentialGeometry.euclideanMetric (E := ℝ) =
        standardEuclideanMetric ℝ from rfl, riemannianEDistOf_standardEuclideanMetric,
      edist_dist, Real.dist_eq, ENNReal.ofReal_mul hL2.le]
  have htri := riemannianEDistOf_triangle (dihedralThinCylinderMetric ε L hε hL)
    px (py.1, px.2) py
  rw [dihedralThinCylinderMetric, riemannianEDistOf_prod_left,
    riemannianEDistOf_prod_right, hline] at htri
  have hu := htri.trans (add_le_add hsphere le_rfl)
  rw [← ENNReal.ofReal_add (mul_nonneg hε.le hD)
    (mul_nonneg hL2.le (abs_nonneg _))] at hu
  refine hmap.trans (hu.trans_eq ?_)
  rw [hax L, hay L, ← mul_sub, abs_mul, abs_of_pos hL2, add_comm]

end DifferentialGeometry.Geometry.Collapse
