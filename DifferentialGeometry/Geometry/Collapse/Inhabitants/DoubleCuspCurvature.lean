import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspProfile
import DifferentialGeometry.Geometry.Curvature.WarpedProduct.Mixed
import DifferentialGeometry.Geometry.Curvature.WarpedProduct.Vertical
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Operator.HessianComposition
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.Euclidean
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

/-!
The fixed double cusp log profile controls sectional curvature uniformly in the torus scale.
The real warped metric supplies the bound before restriction to the actual compact carrier.
-/

set_option autoImplicit false

noncomputable section

open GC.Endpoint GC.GraphManifold Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

private theorem real_id_hessian (x : ℝ) :
    hessFun (DifferentialGeometry.euclideanMetric (E := ℝ)) id x = 0 := by
  apply Module.Basis.ext (centeredChartTangentBasis (I := 𝓘(ℝ, ℝ)) x)
  intro i
  apply Module.Basis.ext (centeredChartTangentBasis (I := 𝓘(ℝ, ℝ)) x)
  intro j
  rw [hessFun_basis_apply, chartHessianTensor_def, chartIteratedPartialDeriv_def]
  have he : scalarOnE (I := 𝓘(ℝ, ℝ)) x id = id := by
    funext y
    rw [scalarOnE_def, extChartAt_model_space_eq_id]
    rfl
  rw [he]
  simp_rw [chartChristoffel_euclideanMetric]
  have hd : partialDeriv (E := ℝ) j id = fun y : ℝ => chartModelBasis ℝ j := by
    funext y
    simp [partialDeriv]
  rw [hd]
  simp [partialDeriv]
  rfl

private theorem real_hessian (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (x v w : ℝ) :
    hessFun (DifferentialGeometry.euclideanMetric (E := ℝ)) f x v w =
      deriv (deriv f) x * v * w := by
  have hh := hessFun_comp (DifferentialGeometry.euclideanMetric (E := ℝ)) hf
    (contMDiff_id (I := 𝓘(ℝ, ℝ))) x v w
  have hi (z : ℝ) : mvfderiv 𝓘(ℝ, ℝ) id x z = z := by
    erw [mvfderiv_real_model_eq_fderiv]
    change fderiv ℝ id x z = z
    simp
  have hz : hessFun (DifferentialGeometry.euclideanMetric (E := ℝ)) id x v w = 0 := by
    rw [real_id_hessian]
    rfl
  rw [hi, hi, hz] at hh
  simpa only [id_eq, mul_zero, add_zero] using hh

private theorem real_gradient (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    gradFun (DifferentialGeometry.euclideanMetric (E := ℝ)) f x = deriv f x := by
  have hh := gradFun_metricDual_mvfderiv (DifferentialGeometry.euclideanMetric (E := ℝ)) f x 1
  rw [mvfderiv_real_model_eq_fderiv,
    ((hf.differentiable (by simp)) x).hasDerivAt.hasFDerivAt.fderiv] at hh
  let b : ℝ := gradFun (DifferentialGeometry.euclideanMetric (E := ℝ)) f x
  erw [DifferentialGeometry.euclideanMetric_inner] at hh
  change inner ℝ b (1 : ℝ) = (1 : ℝ) * deriv f x at hh
  change b = deriv f x
  simpa only [RCLike.inner_apply, conj_trivial, mul_one, one_mul] using hh

private theorem warp_deriv (a r : ℝ) :
    deriv (doubleCuspWarp a) r = doubleCuspWarp a r * deriv doubleCuspLogProfile r := by
  have hd := doubleCuspLogProfile_smooth.differentiable (by simp) r
  have hh := ((hd.hasDerivAt.exp).const_mul a).deriv
  change deriv (doubleCuspWarp a) r =
    a * (Real.exp (doubleCuspLogProfile r) * deriv doubleCuspLogProfile r) at hh
  rw [hh, doubleCuspWarp]
  ring

private theorem warp_second (a r : ℝ) :
    deriv (deriv (doubleCuspWarp a)) r = doubleCuspWarp a r *
      (deriv (deriv doubleCuspLogProfile) r + (deriv doubleCuspLogProfile r) ^ 2) := by
  have hd : ContDiff ℝ ∞ (deriv doubleCuspLogProfile) :=
    (contDiff_infty_iff_deriv.mp doubleCuspLogProfile_smooth).2
  have he : deriv (doubleCuspWarp a) =
      fun x => doubleCuspWarp a x * deriv doubleCuspLogProfile x := funext (warp_deriv a)
  rw [he]
  change deriv (doubleCuspWarp a * deriv doubleCuspLogProfile) r = _
  rw [deriv_mul ((doubleCuspWarp_smooth a).differentiable (by simp) r)
    (hd.differentiable (by simp) r), warp_deriv]
  ring

private theorem log_derivatives_left {r : ℝ} (hr : r < 119) :
    deriv doubleCuspLogProfile r = -(1 / 2 : ℝ) ∧
      deriv (deriv doubleCuspLogProfile) r = 0 := by
  have he : doubleCuspLogProfile =ᶠ[𝓝 r] (fun x : ℝ => -x / 2) := by
    filter_upwards [Iio_mem_nhds hr] with x hx
    exact doubleCuspLogProfile_left (le_of_lt hx)
  constructor
  · rw [he.deriv_eq]
    norm_num
  · rw [he.deriv.deriv_eq]
    have hd : deriv (fun x : ℝ => -x / 2) = fun x => -(1 / 2 : ℝ) := by
      funext x
      norm_num
    rw [hd]
    simp

private theorem log_derivatives_right {r : ℝ} (hr : 121 < r) :
    deriv doubleCuspLogProfile r = (1 / 2 : ℝ) ∧
      deriv (deriv doubleCuspLogProfile) r = 0 := by
  have he : doubleCuspLogProfile =ᶠ[𝓝 r] (fun x : ℝ => -(240 - x) / 2) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact doubleCuspLogProfile_right (le_of_lt hx)
  have hd : deriv (fun x : ℝ => -(240 - x) / 2) = fun x => (1 / 2 : ℝ) := by
    funext x
    simp
  constructor
  · rw [he.deriv_eq, hd]
  · rw [he.deriv.deriv_eq, hd]
    simp

theorem doubleCuspLogProfile_derivatives_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ,
      (deriv doubleCuspLogProfile r) ^ 2 ≤ C ∧
        deriv (deriv doubleCuspLogProfile) r + (deriv doubleCuspLogProfile r) ^ 2 ≤ C := by
  have hd : ContDiff ℝ ∞ (deriv doubleCuspLogProfile) :=
    (contDiff_infty_iff_deriv.mp doubleCuspLogProfile_smooth).2
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (118 : ℝ) 122)).exists_bound_of_continuousOn
    (doubleCuspLogProfile_smooth.continuous_deriv (by simp)).continuousOn
  obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Set.Icc (118 : ℝ) 122)).exists_bound_of_continuousOn
    (hd.continuous_deriv (by simp)).continuousOn
  refine ⟨max 1 (|D| + |B| ^ 2), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro r
  by_cases hr : r ∈ Set.Icc (118 : ℝ) 122
  · have hb0 : |deriv doubleCuspLogProfile r| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB r hr
    have hb := hb0.trans (le_abs_self B)
    have hd0 : |deriv (deriv doubleCuspLogProfile) r| ≤ D := by
      simpa only [Real.norm_eq_abs] using hD r hr
    have hd' := (le_abs_self (deriv (deriv doubleCuspLogProfile) r)).trans
      (hd0.trans (le_abs_self D))
    have hsq : (deriv doubleCuspLogProfile r) ^ 2 ≤ |B| ^ 2 := by
      nlinarith [sq_abs (deriv doubleCuspLogProfile r), abs_nonneg B,
        abs_nonneg (deriv doubleCuspLogProfile r)]
    constructor <;> apply le_trans _ (le_max_right _ _) <;> nlinarith [abs_nonneg D]
  · have htail : (deriv doubleCuspLogProfile r) ^ 2 = (1 / 4 : ℝ) ∧
        deriv (deriv doubleCuspLogProfile) r = 0 := by
      rcases lt_or_ge r 118 with hr0 | hr0
      · obtain ⟨h1, h2⟩ := log_derivatives_left (by linarith [hr0])
        rw [h1, h2]
        norm_num
      · obtain ⟨h1, h2⟩ := log_derivatives_right (by
          have hh : 122 < r := lt_of_not_ge (fun h => hr ⟨hr0, h⟩)
          linarith)
        rw [h1, h2]
        norm_num
    rw [htail.1, htail.2]
    constructor <;> apply le_trans _ (le_max_left _ _) <;> norm_num

private theorem real_mixed (a : ℝ) (ha : 0 < a) (p : ℝ × GC.Endpoint.Torus)
    (u z : ℝ) (v w : TangentSpace torusModel p.2) :
    metricRm04StandardAt (doubleCuspRealMetric a ha) p
      (u, 0) (0, v) (0, w) (z, 0) =
      -(doubleCuspWarp a p.1 * deriv (deriv (doubleCuspWarp a)) p.1) * u * z *
        standardCuspTorusMetric.inner p.2 v w := by
  let g := DifferentialGeometry.euclideanMetric (E := ℝ)
  have hi : g.inner p.1 z ((LeviCivita g) (gradFun g (doubleCuspWarp a)) p.1 u) =
      deriv (deriv (doubleCuspWarp a)) p.1 * u * z := by
    erw [g.symm, ← hessFun_eq_cov_grad g (doubleCuspWarp_smooth a).contMDiff]
    exact real_hessian (doubleCuspWarp a) (doubleCuspWarp_smooth a) p.1 u z
  have hh := metricRm04StandardAt_warpedProduct_mixed g standardCuspTorusMetric
    (doubleCuspWarp a) (doubleCuspWarp_smooth a).contMDiff (doubleCuspWarp_pos ha) p u z v w
  change metricRm04StandardAt (doubleCuspRealMetric a ha) p
    (u, 0) (0, v) (0, w) (z, 0) = _ at hh
  rw [hi] at hh
  rw [hh]
  ring

private theorem real_vertical (a : ℝ) (ha : 0 < a) (p : ℝ × GC.Endpoint.Torus)
    (v w : TangentSpace torusModel p.2) (z : ℝ) :
    metricRm04StandardAt (doubleCuspRealMetric a ha) p
      (0, v) (0, w) (0, w) (z, v) =
      -(doubleCuspWarp a p.1) ^ 2 * (deriv (doubleCuspWarp a) p.1) ^ 2 *
        (standardCuspTorusMetric.inner p.2 v v * standardCuspTorusMetric.inner p.2 w w -
          standardCuspTorusMetric.inner p.2 v w ^ 2) := by
  have hh := metricRm04StandardAt_warpedProduct_vertical
    (DifferentialGeometry.euclideanMetric (E := ℝ)) standardCuspTorusMetric
    (doubleCuspWarp a) (doubleCuspWarp_smooth a).contMDiff (doubleCuspWarp_pos ha) p v w w v z
  rw [standardCuspTorusMetric_flat, real_gradient (doubleCuspWarp a)
    (doubleCuspWarp_smooth a)] at hh
  erw [DifferentialGeometry.euclideanMetric_inner] at hh
  have he : inner ℝ (deriv (doubleCuspWarp a) p.1) (deriv (doubleCuspWarp a) p.1) =
      (deriv (doubleCuspWarp a) p.1) ^ 2 := by
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
  erw [he] at hh
  change metricRm04StandardAt (doubleCuspRealMetric a ha) p
    (0, v) (0, w) (0, w) (z, v) = _ at hh
  rw [hh]
  ring

private theorem split_curvature {S : Type*} [AddCommGroup S] [Module ℝ S]
    {R : S → S → S → S → ℝ} (hR : IsAlgCurvForm R) (e U V : S) (a b : ℝ)
    (hU : R U V U e = 0) (hV : R U V V e = 0) :
    R (a • e + U) (b • e + V) (b • e + V) (a • e + U) =
      R e (a • V - b • U) (a • V - b • U) e + R U V V U := by
  have hs2 (c : ℝ) (x y z t : S) : R x (c • y) z t = c * R x y z t := by
    rw [hR.anti_first, hR.smul_left, hR.anti_first y x]
    ring
  have hs3 (c : ℝ) (x y z t : S) : R x y (c • z) t = c * R x y z t := by
    rw [hR.pair_swap, hR.smul_left, hR.pair_swap z t]
  have hs4 (c : ℝ) (x y z t : S) : R x y z (c • t) = c * R x y z t := by
    rw [hR.anti_last, hs3, hR.anti_last x y t]
    ring
  have hd1 (x y z : S) : R x x y z = 0 := by
    have hh := hR.anti_first x x y z
    linarith
  have hd2 (x y z : S) : R x y z z = 0 := by
    have hh := hR.anti_last x y z z
    linarith
  have h1 : R e V V U = 0 := by
    rw [hR.pair_swap, hR.anti_last, hR.anti_first, hV]
    ring
  have h2 : R U e V U = 0 := by
    rw [hR.pair_swap, hR.anti_first, hU]
    ring
  have h3 : R U V e U = 0 := by rw [hR.anti_last, hU]; ring
  have h4 : R e V e U = -R e V U e := hR.anti_last _ _ _ _
  have h5 : R U e V e = -R e U V e := hR.anti_first _ _ _ _
  have h6 : R U e e U = R e U U e := by
    rw [hR.anti_first, hR.anti_last e U]
    ring
  simp only [sub_eq_add_neg, ← neg_smul, hR.add_left, hR.add_two, hR.add_three,
    hR.add_four, hR.smul_left, hs2, hs3, hs4, hd1, hd2, hV, h1, h2, h3,
    h4, h5, h6]
  ring

private theorem curvature_zero_four {S : Type*} [AddCommGroup S] [Module ℝ S]
    {R : S → S → S → S → ℝ} (hR : IsAlgCurvForm R) (x y z : S) : R x y z 0 = 0 := by
  rw [hR.pair_swap, hR.anti_first]
  have hh := hR.smul_left 0 z z x y
  simpa only [zero_smul, zero_mul, neg_eq_zero] using hh

private theorem real_triple (a : ℝ) (ha : 0 < a) (p : ℝ × Torus)
    (v w t : TangentSpace torusModel p.2) :
    metricRm04StandardAt (doubleCuspRealMetric a ha) p (0, v) (0, w) (0, t) (1, 0) = 0 := by
  have hR := mem_algebraicCurvatureTensorSubmodule.mp
    (metricRm04At_mem_algebraicCurvatureTensorSubmodule standardCuspTorusMetric p.2)
  have hz := curvature_zero_four hR v w t
  change metricRm04StandardAt standardCuspTorusMetric p.2 v w t 0 = 0 at hz
  have hh := metricRm04StandardAt_warpedProduct_vertical
    (DifferentialGeometry.euclideanMetric (E := ℝ)) standardCuspTorusMetric
    (doubleCuspWarp a) (doubleCuspWarp_smooth a).contMDiff (doubleCuspWarp_pos ha)
    p v w t 0 1
  change metricRm04StandardAt (doubleCuspRealMetric a ha) p
    (0, v) (0, w) (0, t) (1, 0) = _ at hh
  rw [hz] at hh
  simpa only [map_zero, LinearMap.zero_apply, zero_apply,
    mul_zero, sub_zero, add_zero] using hh

private theorem real_sectional (a : ℝ) (ha : 0 < a) (p : ℝ × Torus)
    (v w : ℝ × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :
    metricRm04StandardAt (doubleCuspRealMetric a ha) p v w w v =
      -(doubleCuspWarp a p.1 * deriv (deriv (doubleCuspWarp a)) p.1) *
        standardCuspTorusMetric.inner p.2 (v.1 • w.2 - w.1 • v.2) (v.1 • w.2 - w.1 • v.2) -
      (doubleCuspWarp a p.1) ^ 2 * (deriv (doubleCuspWarp a) p.1) ^ 2 *
        (standardCuspTorusMetric.inner p.2 v.2 v.2 * standardCuspTorusMetric.inner p.2 w.2 w.2 -
          standardCuspTorusMetric.inner p.2 v.2 w.2 ^ 2) := by
  let R : (ℝ × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) →
      (ℝ × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) →
      (ℝ × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) →
      (ℝ × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) → ℝ :=
    metricRm04StandardAt (doubleCuspRealMetric a ha) p
  have hR : IsAlgCurvForm R := mem_algebraicCurvatureTensorSubmodule.mp
    (metricRm04At_mem_algebraicCurvatureTensorSubmodule (doubleCuspRealMetric a ha) p)
  have hs := split_curvature hR (1, 0) (0, v.2) (0, w.2) v.1 w.1
    (real_triple a ha p v.2 w.2 v.2) (real_triple a ha p v.2 w.2 w.2)
  have hv : v.1 • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) +
      (0, v.2) = v := by
    apply Prod.ext
    · change v.1 * (1 : ℝ) + 0 = v.1
      ring
    · change v.1 • (0 : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) + v.2 = v.2
      simp
  have hw : w.1 • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) +
      (0, w.2) = w := by
    apply Prod.ext
    · change w.1 * (1 : ℝ) + 0 = w.1
      ring
    · change w.1 • (0 : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) + w.2 = w.2
      simp
  have hz : v.1 • ((0 : ℝ), w.2) - w.1 • ((0 : ℝ), v.2) =
      (0, v.1 • w.2 - w.1 • v.2) := by
    apply Prod.ext <;> simp
  erw [hv, hw, hz] at hs
  change metricRm04StandardAt (doubleCuspRealMetric a ha) p v w w v = _ at hs
  have hm := real_mixed a ha p 1 1 (v.1 • w.2 - w.1 • v.2) (v.1 • w.2 - w.1 • v.2)
  have ht := real_vertical a ha p v.2 w.2 0
  refine hs.trans ((congrArg₂ (fun x y : ℝ => x + y) hm ht).trans ?_)
  ring

private theorem real_inner (a : ℝ) (ha : 0 < a) (p : ℝ × Torus)
    (v w : ℝ × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :
    (doubleCuspRealMetric a ha).inner p v w =
      v.1 * w.1 + (doubleCuspWarp a p.1) ^ 2 * standardCuspTorusMetric.inner p.2 v.2 w.2 := by
  unfold doubleCuspRealMetric
  erw [SmoothRiemannianMetric.warpedProduct_inner]
  erw [DifferentialGeometry.euclideanMetric_inner]
  let x : ℝ := v.1
  let y : ℝ := w.1
  change inner ℝ x y + _ = x * y + _
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem real_gram (a : ℝ) (ha : 0 < a) (p : ℝ × Torus)
    (v w : ℝ × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :
    (doubleCuspRealMetric a ha).inner p v v * (doubleCuspRealMetric a ha).inner p w w -
      (doubleCuspRealMetric a ha).inner p v w ^ 2 =
      (doubleCuspWarp a p.1) ^ 2 *
        standardCuspTorusMetric.inner p.2 (v.1 • w.2 - w.1 • v.2) (v.1 • w.2 - w.1 • v.2) +
      (doubleCuspWarp a p.1) ^ 4 *
        (standardCuspTorusMetric.inner p.2 v.2 v.2 * standardCuspTorusMetric.inner p.2 w.2 w.2 -
          standardCuspTorusMetric.inner p.2 v.2 w.2 ^ 2) := by
  have hz : standardCuspTorusMetric.inner p.2 (v.1 • w.2 - w.1 • v.2)
      (v.1 • w.2 - w.1 • v.2) =
      v.1 ^ 2 * standardCuspTorusMetric.inner p.2 w.2 w.2 -
      2 * v.1 * w.1 * standardCuspTorusMetric.inner p.2 v.2 w.2 +
      w.1 ^ 2 * standardCuspTorusMetric.inner p.2 v.2 v.2 := by
    let L : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) →L[ℝ]
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ :=
      standardCuspTorusMetric.inner p.2
    change L (v.1 • w.2 - w.1 • v.2) (v.1 • w.2 - w.1 • v.2) =
      v.1 ^ 2 * L w.2 w.2 - 2 * v.1 * w.1 * L v.2 w.2 + w.1 ^ 2 * L v.2 v.2
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    have he : L w.2 v.2 = L v.2 w.2 := standardCuspTorusMetric.symm p.2 w.2 v.2
    rw [he]
    ring
  erw [real_inner a ha p v v, real_inner a ha p w w, real_inner a ha p v w, hz]
  ring

theorem exists_doubleCuspRealMetric_sectionalBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a) (p : ℝ × Torus),
      SectionalBoundedBelowAt (doubleCuspRealMetric a ha) p (-C) := by
  obtain ⟨C, hC, hbound⟩ := doubleCuspLogProfile_derivatives_bounded
  refine ⟨C, hC, ?_⟩
  intro a ha p v w
  let f : ℝ := doubleCuspWarp a p.1
  let P : ℝ := deriv doubleCuspLogProfile p.1
  let Q : ℝ := deriv (deriv doubleCuspLogProfile) p.1
  let Z : ℝ := standardCuspTorusMetric.inner p.2
    ((v.1 : ℝ) • w.2 - (w.1 : ℝ) • v.2) ((v.1 : ℝ) • w.2 - (w.1 : ℝ) • v.2)
  let T : ℝ := standardCuspTorusMetric.inner p.2 v.2 v.2 *
    standardCuspTorusMetric.inner p.2 w.2 w.2 - standardCuspTorusMetric.inner p.2 v.2 w.2 ^ 2
  have hZ : 0 ≤ Z := metric_inner_self_nonneg
    standardCuspTorusMetric p.2 _
  have hT : 0 ≤ T := sub_nonneg.mpr
    (gInner_sq_le_mul standardCuspTorusMetric p.2 v.2 w.2)
  have hb1 : P ^ 2 ≤ C := (hbound p.1).1
  have hb2 : Q + P ^ 2 ≤ C := (hbound p.1).2
  have h1 : f ^ 2 * (Q + P ^ 2) * Z ≤ f ^ 2 * C * Z :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 (sq_nonneg f)) hZ
  have h2 : f ^ 4 * P ^ 2 * T ≤ f ^ 4 * C * T :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb1 (pow_nonneg (le_of_lt (doubleCuspWarp_pos ha p.1)) 4)) hT
  change -C * ((doubleCuspRealMetric a ha).inner p v v *
    (doubleCuspRealMetric a ha).inner p w w - (doubleCuspRealMetric a ha).inner p v w ^ 2) ≤ _
  have hg := real_gram a ha p v w
  have hr := real_sectional a ha p v w
  erw [hg, hr, warp_deriv a p.1, warp_second a p.1]
  change -C * (f ^ 2 * Z + f ^ 4 * T) ≤
    -(f * (f * (Q + P ^ 2))) * Z - f ^ 2 * (f * P) ^ 2 * T
  nlinarith only [h1, h2]

end DifferentialGeometry.Geometry.Collapse
