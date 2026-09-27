import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticRescalingComparison
import DifferentialGeometry.Geometry.Metric.CylinderAxial
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback

set_option autoImplicit false

noncomputable section

open Set Bundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Geometry.Curvature CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open Surgery.Topology (Sphere ThreeSpace)
open Geometry.Metric (cylinderAxialDiffeomorph cylinderAxialDiffeomorph_mfderiv)
open KappaSolutions (pullbackTensor02FieldCross pullbackTensor02FieldCross_apply
  tensor02CovDerivNormWith_pullbackTensor02FieldCross)

private local instance recenterSphereDimension :
    Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

private theorem cylinder_reference_pullback_translation
    (C : CylinderReference) (a : ℝ) :
    Diffeomorph.pullbackMetricCross (C.metric 0)
      (cylinderAxialDiffeomorph (I := I2) (M := Sphere 2) a 1 (by norm_num)) = C.metric 0 := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetricCross_inner,
    cylinderAxialDiffeomorph_mfderiv, cylinderAxialDiffeomorph_mfderiv]
  have hleft := C.inner_eq 0 le_rfl
    (cylinderAxialDiffeomorph (I := I2) (M := Sphere 2) a 1 (by norm_num) x)
    (v.1, 1 * v.2) (w.1, 1 * w.2)
  have hright := C.inner_eq 0 le_rfl x v w
  exact hleft.trans (by simpa +instances only [Geometry.Metric.cylinderAxialDiffeomorph_apply, one_mul] using hright.symm)

private def comparisonPrecompCylinderTranslation
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (C : CylinderReference) (g : SmoothRiemannianMetric I3 M)
    (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U V : Set Cylinder} {order : ℕ} {eps : ℝ}
    (cmp : MetricComparisonOn (fun _ => C.metric 0) (fun _ => g) F U {0} order eps)
    (a : ℝ) (hV : ∀ y ∈ V,
      cylinderAxialDiffeomorph (I := I2) (M := Sphere 2) a 1 (by norm_num) y ∈ U)
    (hU : U ⊆ F.source) :
    MetricComparisonOn (fun _ => C.metric 0) (fun _ => g)
      (partialDiffeomorphTransMixed
        (cylinderAxialDiffeomorph (I := I2) (M := Sphere 2) a 1 (by norm_num)).toPartialDiffeomorph F)
      V {0} order eps := by
  let T := cylinderAxialDiffeomorph (I := I2) (M := Sphere 2) a 1 (by norm_num)
  have hback : Diffeomorph.pullbackMetricCross (C.metric 0) T = C.metric 0 :=
    cylinder_reference_pullback_translation C a
  have hinner (y : Cylinder) (v w : TangentSpace IC y) :
      (C.metric 0).inner (T y) (mfderiv IC IC T y v) (mfderiv IC IC T y w) =
        (C.metric 0).inner y v w := by
    rw [← Diffeomorph.pullbackMetricCross_inner]
    exact congrArg (fun g => g.inner y v w) hback
  have hder (y : Cylinder) (hy : y ∈ V) (v : TangentSpace IC y) :
      mfderiv IC I3 (partialDiffeomorphTransMixed T.toPartialDiffeomorph F) y v =
        mfderiv IC I3 F (T y) (mfderiv IC IC T y v) := by
    change mfderiv IC I3 (F ∘ T) y v = _
    exact mfderiv_comp_apply y (F.mdifferentiableAt (by simp) (hU (hV y hy)))
      (T.mdifferentiable (by simp) y) v
  refine {
    pullback := fun s => pullbackTensor02FieldCross T (cmp.pullback s)
    pullback_eq := ?_
    jet := fun b s => pullbackTensor02FieldCross T (cmp.jet b s)
    jet_zero := ?_
    jet_succ := ?_
    equivalence := ?_
    close := ?_ }
  · intro s y hy v
    rw [pullbackTensor02FieldCross_apply, cmp.pullback_eq s (T y) (hV y hy)]
    rw [hder y hy (v 0), hder y hy (v 1)]
    rfl
  · intro s y v
    rw [pullbackTensor02FieldCross_apply, cmp.jet_zero, pullbackTensor02FieldCross_apply,
      hinner]
  · intro b s hs y hy v
    rw [pullbackTensor02FieldCross_apply]
    have hh := cmp.jet_succ b s hs (T y) (hV y hy) (fun j => mfderiv IC IC T y (v j))
    simpa only [pullbackTensor02FieldCross_apply] using hh
  · intro s hs y hy v
    have hh := cmp.equivalence s hs (T y) (hV y hy) (mfderiv IC IC T y v)
    simpa only [pullbackTensor02FieldCross_apply, hinner] using hh
  · intro j b hj s hs y hy
    have hh := tensor02CovDerivNormWith_pullbackTensor02FieldCross
      (C.metric 0) (C.metric 0) T (cmp.jet b s) j y
    rw [hback] at hh
    exact hh.trans_le (cmp.close j b hj s hs (T y) (hV y hy))

universe u

theorem SpatialNeck.exists_at_coordinate_of_scalar_close
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {p : M} {alpha beta eta a : ℝ}
    (nk : SpatialNeck g beta p) (hsmall : alpha < 1 / 11)
    (hbudget : (1 + eta) * beta + eta * Real.sqrt 3 ≤ alpha)
    (u : Sphere 2) (hfit : |a| + alpha⁻¹ ≤ beta⁻¹)
    (hratio : |metricScalarAt g (nk.map (u, a)) / metricScalarAt g p - 1| ≤ eta) :
    ∃ out : SpatialNeck g alpha (nk.map (u, a)), out.center = u ∧
      out.map = partialDiffeomorphTransMixed
        (cylinderAxialDiffeomorph (I := I2) (M := Sphere 2) a 1 (by norm_num)).toPartialDiffeomorph
        nk.map := by
  let q := nk.map (u, a)
  let ratio := metricScalarAt g q / metricScalarAt g p
  have heta_nonneg : 0 ≤ eta := (abs_nonneg _).trans hratio
  have hba : beta ≤ alpha := by
    have hnonneg := mul_nonneg heta_nonneg nk.eps_pos.le
    have hcorr := mul_nonneg heta_nonneg (Real.sqrt_nonneg 3)
    nlinarith only [hbudget, hnonneg, hcorr]
  have halpha : 0 < alpha := nk.eps_pos.trans_le hba
  have heta : eta < 1 := by
    have hroot : (1 : ℝ) ≤ Real.sqrt 3 := by norm_num
    have he := mul_le_mul_of_nonneg_left hroot heta_nonneg
    have hb : 0 ≤ (1 + eta) * beta := mul_nonneg (by linarith) nk.eps_pos.le
    nlinarith only [hbudget, he, hb, hsmall]
  have hratio_pos : 0 < ratio := by
    have hh := (abs_le.mp hratio).1
    change -eta ≤ ratio - 1 at hh
    linarith only [hh, heta]
  have hQq : 0 < metricScalarAt g q := (div_pos_iff_of_pos_right nk.Q_pos).mp hratio_pos
  let T := cylinderAxialDiffeomorph (I := I2) (M := Sphere 2) a 1 (by norm_num)
  have hdomain : ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹,
      T y ∈ univ ×ˢ Ioo (-beta⁻¹) beta⁻¹ := by
    intro y hy
    refine ⟨mem_univ _, ?_⟩
    change -beta⁻¹ < a + 1 * y.2 ∧ a + 1 * y.2 < beta⁻¹
    constructor <;> linarith only [hfit, neg_abs_le a, le_abs_self a, hy.2.1, hy.2.2]
  have horder : ⌈alpha⁻¹⌉₊ ≤ ⌈beta⁻¹⌉₊ := Nat.ceil_le_ceil (inv_anti₀ nk.eps_pos hba)
  have hratio_le : ratio ≤ 1 + eta := by
    have hh := (abs_le.mp hratio).2
    change ratio - 1 ≤ eta at hh
    linarith only [hh]
  have herror : ratio * beta + |ratio - 1| * Real.sqrt 3 ≤ alpha :=
    ((add_le_add (mul_le_mul_of_nonneg_right hratio_le nk.eps_pos.le)
      (mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg 3))).trans hbudget)
  let scaled := nk.comparison.staticRescale (by simp : (0 : ℝ) ∈ ({0} : Set ℝ))
    1 ratio zero_lt_one hratio_pos halpha.le (by
      intro order _horder
      norm_num only [inv_one, one_pow, Real.sqrt_one, one_mul, div_one,
        Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace,
        Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      exact herror)
  have href : DifferentialGeometry.scaleMetric 1 zero_lt_one (nk.cylinder.metric 0) = nk.cylinder.metric 0 := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [scaleMetric_inner, one_mul]
  have htgt : DifferentialGeometry.scaleMetric ratio hratio_pos (DifferentialGeometry.scaleMetric (metricScalarAt g p) nk.Q_pos g) =
      DifferentialGeometry.scaleMetric (metricScalarAt g q) hQq g := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [scaleMetric_inner, scaleMetric_inner, scaleMetric_inner]
    dsimp only [ratio]
    field_simp [nk.Q_pos.ne']
  have cmp0 : MetricComparisonOn (fun _ => nk.cylinder.metric 0)
      (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt g q) hQq g) nk.map
      (univ ×ˢ Ioo (-beta⁻¹) beta⁻¹) {0} ⌈beta⁻¹⌉₊ alpha := by
    simpa only [href, htgt] using scaled
  let shifted := comparisonPrecompCylinderTranslation nk.cylinder
    (DifferentialGeometry.scaleMetric (metricScalarAt g q) hQq g) nk.map cmp0 a hdomain nk.domain
  let map := partialDiffeomorphTransMixed T.toPartialDiffeomorph nk.map
  let out : SpatialNeck g alpha q := {
    eps_pos := halpha
    eps_small := hsmall
    Q_pos := hQq
    cylinder := nk.cylinder
    map := map
    center := u
    center_eq := by
      change nk.map (u, a + 1 * (0 : ℝ)) = q
      simp only [mul_zero, add_zero, q]
    domain := by
      intro y hy
      exact ⟨mem_univ _, nk.domain (hdomain y hy)⟩
    comparison := shifted.mono (subset_refl _) horder le_rfl }
  exact ⟨out, rfl, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
