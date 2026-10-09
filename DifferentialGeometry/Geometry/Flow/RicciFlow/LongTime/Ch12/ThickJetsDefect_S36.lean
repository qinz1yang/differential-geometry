import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickJetsSeed_S36
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitVolumeLimit_O5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCompactness_CX6

set_option autoImplicit false

/-! # CH12-S36: defect `< 1` gives scalar `≤ 0`; seeds at every point of a fixed ball;
restriction of local derivative bounds to the base component -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

/-- Normalised Ricci defect `< 1` forces normalised scalar curvature `≤ 0` (three-dimensional trace). -/
theorem scalar_le_zero_of_defect_S36 (s : RegularSlice F.observation) (q : s.stage.Carrier)
    (h : NormalizedRicciDefect_S13 s q < 1) : metricScalarAt s.normalizedMetric q ≤ 0 := by
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel q) = 3 := finrank_euclideanSpace_fin
  obtain ⟨basis, -, -, -, horth, -⟩ := exists_orthonormal_curvature_eigenframe s.normalizedMetric q hdim
  have hON : ∀ i j, s.normalizedMetric.inner q (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [horth i j]
    fin_cases i <;> fin_cases j <;> simp [delta3]
  have hi : ∀ i, 2 * ricciTensor s.normalizedMetric q (basis i) (basis i) + 1 ≤ 1 * 1 := by
    intro i
    have h1 := defect_quad_le_O5 s.normalizedMetric q (basis i)
    rw [hON i i] at h1
    simp only [ite_true, mul_one] at h1
    have h2 : sSup (defectSet_O5 s.normalizedMetric q) < 1 := h
    have := (le_abs_self _).trans h1
    linarith
  rw [metricScalarAt_eq_orthonormal_trace s.normalizedMetric q basis hON, Fin.sum_univ_three]
  have := hi 0
  have := hi 1
  have := hi 2
  linarith

/-- From a seed at the base points and LTF03: a seed `(b, w)` at every point of the fixed ball. -/
theorem ballSeeds_S36 (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v R : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v R)
    (S : LatePointSequence_S13 F) {a v : ℝ} (ha : 0 < a) (hv : 0 < v)
    (hseed : ∀ j, HasNormalizedSeed_S13 (S.slices j) (S.point j) a v) {R : ℝ} (hR : 0 < R) :
    ∃ b w : ℝ, 0 < b ∧ 0 < w ∧ ∀ᶠ j in atTop,
      ∀ q ∈ riemannianBallOf (S.slices j).normalizedMetric (S.point j) R,
        HasNormalizedSeed_S13 (S.slices j) q b w := by
  set Λ : ℝ := 2 * Real.sqrt 3 * (max (0 : ℝ) 0 / 2 + max (0 : ℝ) (Real.exp 4)) with hΛ
  have hΛ0 : 0 ≤ Λ := by
    have : 0 ≤ max (0 : ℝ) (Real.exp 4) := le_max_left _ _
    simp only [hΛ, max_self]; positivity
  obtain ⟨b, w, hb, hw, htr⟩ := seed_transfer_O5.{u} a v R Λ ha hv hR hΛ0
  refine ⟨b, w, hb, hw, ?_⟩
  have hd := hLTF03 S a v (3 * max R a) ha hv (by positivity) hseed 1 one_pos
  filter_upwards [hd] with j hj
  have hsec : ∀ y ∈ riemannianBallOf (S.slices j).normalizedMetric (S.point j) (3 * max R a),
      SectionalBoundedBelowAt (S.slices j).normalizedMetric y (-Λ) := fun y hy =>
    sec_lower_of_normScalar_le_S20 Hp (S.slices j) y (K := 0) (scalar_le_zero_of_defect_S36 _ _ (hj y hy))
  intro q hq
  exact htr _ (S.slices j).normalizedMetric (S.point j) (hseed j).2 hsec q hq

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

/-- A bound of `|∇^m Rm|` of the normalised slice on the ball of radius `R + 1` about the base point
gives `HasLocalCurvDerivBound` of the base component. -/
theorem localJets_component_S36 (S : LatePointSequence_S13 F) (n : ℕ) (R : ℝ) (m : ℕ) (C : ℝ)
    (h : ∀ q ∈ riemannianBallOf (S.slices n).normalizedMetric (S.point n) (R + 1),
      curvatureDerivativeNorm (S.slices n).normalizedMetric m q ≤ C) (hR : 0 ≤ R) :
    HasLocalCurvDerivBound (S.pointedSeq.connectedComponent.obj n)
      (S.pointedSeq.connectedComponent.obj n).basepoint R m C := by
  intro x hx
  let U : TopologicalSpace.Opens (S.slices n).stage.Carrier :=
    connectedComponentOpen (I := ThreeModel) (S.point n)
  let y : U := x
  have e := riemannianEDistOf_restrictOpen_of_isClosed (S.slices n).normalizedMetric U
    isClosed_connectedComponent (⟨S.point n, mem_connectedComponent⟩ : U) y
  have hd : riemannianEDistOf (S.slices n).normalizedMetric (S.point n) y.1 ≤ ENNReal.ofReal R := by
    rw [← e]; exact hx
  have hlt : y.1 ∈ riemannianBallOf (S.slices n).normalizedMetric (S.point n) (R + 1) := by
    change riemannianEDistOf (S.slices n).normalizedMetric (S.point n) y.1 < ENNReal.ofReal (R + 1)
    exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  have hc := curvDerivNorm_restrictOpen (S.slices n).normalizedMetric U m y
  have h2 := h y.1 hlt
  rw [curvatureDerivativeNorm_eq_curvDerivNorm, ← hc] at h2
  exact h2

end GC.LongTime.Ch12
