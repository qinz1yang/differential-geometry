import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspInterior
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormLocalPull
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BundleOverAnnulus
import DifferentialGeometry.Topology.Manifold.InteriorBoundary
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product

/-!
# The double cusp has curvature derivatives bounded uniformly in the torus scale (BDRY-INST)

Review 54 §4 (level 2) needs ONE derivative-control function for the whole family
`doubleCuspMetric a`, `a > 0`. Shrinking the flat torus does not change the local geometry:
the chart `Φ_a (r, x, y) = (r, cexp (x / a), cexp (y / a))` pulls `doubleCuspRealMetric a` back
to `dr² + e^{2φ(r)} (dx² + dy²)` for EVERY `a` (`doubleCuspScaleChart_pullback_INST`). Hence the
curvature derivative norms of all `doubleCuspRealMetric a` take the values of those of
`doubleCuspRealMetric 1`; on the carrier they are transported through the interior coordinate and
extended to the boundary by continuity.

* `doubleCuspRealMetric_derivative_eq_INST`: the norm of `doubleCuspRealMetric a` at `Φ_a q`
  equals the norm of `doubleCuspRealMetric 1` at `Φ_1 q`;
* `exists_doubleCuspMetric_derivative_bound_INST`: one bound `B` for all orders `k ≤ K`, all
  scales `a > 0` and all points of the compact carrier.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold
open GC.Endpoint GC.Seifert GC.GraphManifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The model of the scale chart domain `ℝ × (ℝ × ℝ)`. -/
abbrev scaleChartModel_INST := 𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))

/-- The circle chart at torus scale `a`: `t ↦ cexp (t / a)`. -/
def circleScale_INST (a t : ℝ) : Circle := AnnulusStraightening.cexp (a⁻¹ * t)

theorem isLocalDiffeomorph_circleScale_INST {a : ℝ} (ha : a ≠ 0) :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ (circleScale_INST a) := by
  let D := (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
    (Units.mk0 a⁻¹ (inv_ne_zero ha))).toDiffeomorph
  have he : AnnulusStraightening.cexp ∘ D = circleScale_INST a := by
    funext t
    rfl
  rw [← he]
  exact isLocalDiffeomorph_comp AnnulusStraightening.isLocalDiffeomorph_cexp D.isLocalDiffeomorph

theorem mfderiv_circleScale_INST (a t u : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (circleScale_INST a) t u =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) AnnulusStraightening.cexp (a⁻¹ * t) (a⁻¹ * u) := by
  have hl : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => a⁻¹ * s) t
      (a⁻¹ • ContinuousLinearMap.id ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr ((hasFDerivAt_id t).const_smul a⁻¹)
  have hc : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) AnnulusStraightening.cexp (a⁻¹ * t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) AnnulusStraightening.cexp (a⁻¹ * t)) :=
    (AnnulusStraightening.contMDiff_cexp.mdifferentiableAt (by simp)).hasMFDerivAt
  have h := hc.comp t hl
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (AnnulusStraightening.cexp ∘ fun s : ℝ => a⁻¹ * s) t u = _
  rw [h.mfderiv]
  rfl

/-- The flat circle metric in the covering coordinate `cexp`: unit speed. -/
theorem standardCuspCircleMetric_inner_cexp_INST (s u u' : ℝ) :
    standardCuspCircleMetric.inner (AnnulusStraightening.cexp s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) AnnulusStraightening.cexp s u)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) AnnulusStraightening.cexp s u') = u * u' := by
  have h1 : AddCircle.diffeomorphCircle.symm ∘ AnnulusStraightening.cexp =
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) := by
    funext t
    exact AddCircle.diffeomorphCircle.symm_apply_apply _
  have h2 (v : ℝ) : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) AddCircle.diffeomorphCircle.symm
      (AnnulusStraightening.cexp s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) AnnulusStraightening.cexp s v) =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) s v := by
    rw [← h1, mfderiv_comp s (AddCircle.diffeomorphCircle.symm.contMDiff.mdifferentiableAt
      (by simp)) (AnnulusStraightening.contMDiff_cexp.mdifferentiableAt (by simp))]
    rfl
  have h3 : AddCircle.diffeomorphCircle.symm (AnnulusStraightening.cexp s) =
      (s : AddCircle (1 : ℝ)) :=
    AddCircle.diffeomorphCircle.symm_apply_apply _
  rw [standardCuspCircleMetric, Diffeomorph.pullbackMetricCross_inner, h2, h2, h3]
  exact AddCircle.flatMetric_inner_mfderiv_coe s u u'

/-- The scale chart `Φ_a (r, x, y) = (r, cexp (x / a), cexp (y / a))`. -/
def doubleCuspScaleChart_INST (a : ℝ) : ℝ × (ℝ × ℝ) → ℝ × Torus :=
  Prod.map id (Prod.map (circleScale_INST a) (circleScale_INST a))

theorem isLocalDiffeomorph_doubleCuspScaleChart_INST {a : ℝ} (ha : a ≠ 0) :
    IsLocalDiffeomorph scaleChartModel_INST (𝓘(ℝ, ℝ).prod torusModel) ∞
      (doubleCuspScaleChart_INST a) :=
  (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph.prodMap
    ((isLocalDiffeomorph_circleScale_INST ha).prodMap (isLocalDiffeomorph_circleScale_INST ha))

/-- `Φ_a` pulls `doubleCuspRealMetric a` back to `dr² + e^{2φ(r)} (dx² + dy²)`. -/
theorem doubleCuspRealMetric_inner_scaleChart_INST (a : ℝ) (ha : 0 < a) (q : ℝ × (ℝ × ℝ))
    (v w : ℝ × (ℝ × ℝ)) :
    (doubleCuspRealMetric a ha).inner (doubleCuspScaleChart_INST a q)
        (mfderiv scaleChartModel_INST (𝓘(ℝ, ℝ).prod torusModel)
          (doubleCuspScaleChart_INST a) q v)
        (mfderiv scaleChartModel_INST (𝓘(ℝ, ℝ).prod torusModel)
          (doubleCuspScaleChart_INST a) q w) =
      (DifferentialGeometry.euclideanMetric (E := ℝ)).inner q.1 v.1 w.1 +
        Real.exp (doubleCuspLogProfile q.1) ^ 2 * (v.2.1 * w.2.1 + v.2.2 * w.2.2) := by
  have hc : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 1) (circleScale_INST a) :=
    (isLocalDiffeomorph_circleScale_INST ha.ne').contMDiff.mdifferentiable (by simp)
  have hd : mfderiv scaleChartModel_INST (𝓘(ℝ, ℝ).prod torusModel)
      (doubleCuspScaleChart_INST a) q =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id q.1).prodMap
        ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (circleScale_INST a) q.2.1).prodMap
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (circleScale_INST a) q.2.2)) := by
    rw [doubleCuspScaleChart_INST, mfderiv_prodMap mdifferentiableAt_id
      ((hc q.2.1).prodMap (hc q.2.2)), mfderiv_prodMap (hc q.2.1) (hc q.2.2)]
    rfl
  rw [hd]
  erw [doubleCuspRealMetric, SmoothRiemannianMetric.warpedProduct_inner]
  erw [SmoothRiemannianMetric.prod_inner]
  simp only [mfderiv_id]
  change (DifferentialGeometry.euclideanMetric (E := ℝ)).inner q.1 v.1 w.1 +
      doubleCuspWarp a q.1 ^ 2 *
        (standardCuspCircleMetric.inner (circleScale_INST a q.2.1)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (circleScale_INST a) q.2.1 v.2.1)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (circleScale_INST a) q.2.1 w.2.1) +
          standardCuspCircleMetric.inner (circleScale_INST a q.2.2)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (circleScale_INST a) q.2.2 v.2.2)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (circleScale_INST a) q.2.2 w.2.2)) = _
  simp only [mfderiv_circleScale_INST]
  simp only [circleScale_INST]
  erw [standardCuspCircleMetric_inner_cexp_INST (a⁻¹ * q.2.1) (a⁻¹ * v.2.1) (a⁻¹ * w.2.1),
    standardCuspCircleMetric_inner_cexp_INST (a⁻¹ * q.2.2) (a⁻¹ * v.2.2) (a⁻¹ * w.2.2)]
  rw [doubleCuspWarp]
  congr 1
  field_simp

/-- The pullback of `doubleCuspRealMetric a` by `Φ_a` does not depend on the torus scale `a`. -/
theorem doubleCuspScaleChart_pullback_INST (a : ℝ) (ha : 0 < a) :
    localPullMetric (doubleCuspRealMetric a ha) (doubleCuspScaleChart_INST a)
        (isLocalDiffeomorph_doubleCuspScaleChart_INST ha.ne') =
      localPullMetric (doubleCuspRealMetric 1 one_pos) (doubleCuspScaleChart_INST 1)
        (isLocalDiffeomorph_doubleCuspScaleChart_INST one_ne_zero) := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  rw [localPullMetric_inner, localPullMetric_inner]
  exact (doubleCuspRealMetric_inner_scaleChart_INST a ha q v w).trans
    (doubleCuspRealMetric_inner_scaleChart_INST 1 one_pos q v w).symm

/-- The curvature derivative norms of `doubleCuspRealMetric a` at `Φ_a q` are those of
`doubleCuspRealMetric 1` at `Φ_1 q`. -/
theorem doubleCuspRealMetric_derivative_eq_INST (a : ℝ) (ha : 0 < a) (k : ℕ)
    (q : ℝ × (ℝ × ℝ)) :
    curvatureDerivativeNorm (doubleCuspRealMetric a ha) k (doubleCuspScaleChart_INST a q) =
      curvatureDerivativeNorm (doubleCuspRealMetric 1 one_pos) k
        (doubleCuspScaleChart_INST 1 q) := by
  rw [← curvatureDerivativeNorm_localPullMetric_INST _ _
      (isLocalDiffeomorph_doubleCuspScaleChart_INST ha.ne'),
    ← curvatureDerivativeNorm_localPullMetric_INST _ _
      (isLocalDiffeomorph_doubleCuspScaleChart_INST one_ne_zero),
    doubleCuspScaleChart_pullback_INST]

/-- One bound for the curvature derivative norms of every `doubleCuspRealMetric a`, `a > 0`,
orders `k ≤ K`, on the heights `[0, 240]`. -/
theorem exists_doubleCuspRealMetric_derivative_bound_INST (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : ℝ) (ha : 0 < a) (k : ℕ), k ≤ K → ∀ p : ℝ × Torus,
      p.1 ∈ Icc (0 : ℝ) 240 → curvatureDerivativeNorm (doubleCuspRealMetric a ha) k p ≤ B := by
  have hS : IsCompact (Icc (0 : ℝ) 240 ×ˢ (univ : Set Torus)) :=
    isCompact_Icc.prod isCompact_univ
  have hbound : ∀ k : ℕ, ∃ C : ℝ, ∀ p ∈ Icc (0 : ℝ) 240 ×ˢ (univ : Set Torus),
      curvatureDerivativeNorm (doubleCuspRealMetric 1 one_pos) k p ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := hS.bddAbove_image
      (continuous_curvatureDerivativeNorm (doubleCuspRealMetric 1 one_pos) k).continuousOn
    exact ⟨C, fun p hp => hC (mem_image_of_mem _ hp)⟩
  choose C hC using hbound
  refine ⟨∑ k ∈ Finset.range (K + 1), max 0 (C k),
    Finset.sum_nonneg fun k _ => le_max_left _ _, ?_⟩
  intro a ha k hk p hp
  obtain ⟨s₁, hs₁⟩ := AnnulusStraightening.cexp_surjective p.2.1
  obtain ⟨s₂, hs₂⟩ := AnnulusStraightening.cexp_surjective p.2.2
  have hq : doubleCuspScaleChart_INST a (p.1, (a * s₁, a * s₂)) = p := by
    change (p.1, (AnnulusStraightening.cexp (a⁻¹ * (a * s₁)),
      AnnulusStraightening.cexp (a⁻¹ * (a * s₂)))) = p
    rw [inv_mul_cancel_left₀ ha.ne', inv_mul_cancel_left₀ ha.ne', hs₁, hs₂]
  rw [← hq, doubleCuspRealMetric_derivative_eq_INST]
  refine (hC k (doubleCuspScaleChart_INST 1 (p.1, (a * s₁, a * s₂))) ⟨hp, mem_univ _⟩).trans ?_
  exact (le_max_right _ _).trans (Finset.single_le_sum (fun j _ => le_max_left 0 (C j))
    (Finset.mem_range.mpr (by omega)))

local instance doubleCuspCompact_INST : CompactSpace (productSet.{u} 2) :=
  annulusCircleCarrier.{u}.compact

local instance doubleCuspSigma_INST : SigmaCompactSpace (productSet.{u} 2) :=
  CompactSpace.sigmaCompact

theorem doubleCuspInteriorCoordinate_derivative_INST
    (x : doubleCuspInteriorDomain.{u}) (v : TangentSpace (𝓡∂ 3) x) :
    mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) doubleCuspInteriorCoordinate.{u} x v =
      mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) doubleCuspCoordinate.{u} x.val v := by
  change mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel)
    (doubleCuspCoordinate.{u} ∘ Subtype.val) x v = _
  rw [mfderiv_comp x (doubleCuspCoordinate_smooth.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := (𝓡∂ 3)) (n := ∞)).mdifferentiableAt (by simp))]
  change mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) doubleCuspCoordinate.{u} x.val
    (mfderiv (𝓡∂ 3) (𝓡∂ 3) Subtype.val x v) = _
  rw [mfderiv_subtype_val_apply]

theorem doubleCuspInterior_metric_eq_INST (a : ℝ) (ha : 0 < a) :
    localPullMetric (doubleCuspMetric.{u} a ha)
        (Subtype.val : doubleCuspInteriorDomain.{u} → productSet.{u} 2)
        (isLocalDiffeomorph_subtype_val doubleCuspInteriorDomain.{u}) =
      localPullMetric (doubleCuspRealMetric a ha) doubleCuspInteriorCoordinate.{u}
        doubleCuspInteriorCoordinate_localDiffeomorph.{u} := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, localPullMetric_inner,
    mfderiv_subtype_val_apply, mfderiv_subtype_val_apply,
    doubleCuspInteriorCoordinate_derivative_INST, doubleCuspInteriorCoordinate_derivative_INST]
  rfl

/-- At interior points the curvature derivative norms of the carrier metric are those of the
real warped metric at the physical coordinate. -/
theorem doubleCuspMetric_derivative_interior_INST (a : ℝ) (ha : 0 < a) (k : ℕ)
    (p : productSet.{u} 2) (hp : p ∈ (𝓡∂ 3).interior (productSet.{u} 2)) :
    curvatureDerivativeNorm (doubleCuspMetric.{u} a ha) k p =
      curvatureDerivativeNorm (doubleCuspRealMetric a ha) k (doubleCuspCoordinate.{u} p) := by
  let x : doubleCuspInteriorDomain.{u} := ⟨p, hp⟩
  let : SigmaCompactSpace doubleCuspInteriorDomain.{u} :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡∂ 3)
        doubleCuspInteriorDomain.{u}.isOpen)
  have h1 := curvatureDerivativeNorm_localPullMetric_INST (doubleCuspMetric.{u} a ha)
    (Subtype.val : doubleCuspInteriorDomain.{u} → productSet.{u} 2)
    (isLocalDiffeomorph_subtype_val doubleCuspInteriorDomain.{u}) k x
  have h2 := curvatureDerivativeNorm_localPullMetric_INST (doubleCuspRealMetric a ha)
    doubleCuspInteriorCoordinate.{u} doubleCuspInteriorCoordinate_localDiffeomorph.{u} k x
  rw [doubleCuspInterior_metric_eq_INST] at h1
  exact h1.symm.trans h2

theorem doubleCuspCoordinate_height_mem_INST (p : productSet.{u} 2) :
    (doubleCuspCoordinate.{u} p).1 ∈ Icc (0 : ℝ) 240 := by
  change 240 * ((torusMonodromyPolarDiffeomorph.{u} p).2 : ℝ) ∈ Icc (0 : ℝ) 240
  obtain ⟨h0, h1⟩ := (torusMonodromyPolarDiffeomorph.{u} p).2.property
  constructor <;> nlinarith

/-- **The a-uniform derivative bound.** One constant `B` bounds the curvature derivative norms of
orders `k ≤ K` of every double cusp metric `doubleCuspMetric a`, `a > 0`, at every point of the
compact carrier (boundary included). -/
theorem exists_doubleCuspMetric_derivative_bound_INST (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : ℝ) (ha : 0 < a) (k : ℕ), k ≤ K → ∀ p : productSet.{u} 2,
      curvatureDerivativeNorm (doubleCuspMetric.{u} a ha) k p ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_doubleCuspRealMetric_derivative_bound_INST K
  refine ⟨B, hB, fun a ha k hk => ?_⟩
  have hint : (𝓡∂ 3).interior (productSet.{u} 2) ⊆
      {p | curvatureDerivativeNorm (doubleCuspMetric.{u} a ha) k p ≤ B} := by
    intro p hp
    change curvatureDerivativeNorm (doubleCuspMetric.{u} a ha) k p ≤ B
    rw [doubleCuspMetric_derivative_interior_INST a ha k p hp]
    exact hb a ha k hk _ (doubleCuspCoordinate_height_mem_INST p)
  have hclosed : IsClosed {p : productSet.{u} 2 |
      curvatureDerivativeNorm (doubleCuspMetric.{u} a ha) k p ≤ B} :=
    isClosed_le (continuous_curvatureDerivativeNorm _ k) continuous_const
  intro p
  exact closure_minimal hint hclosed
    (ModelWithCorners.dense_interior (𝓡∂ 3) (M := productSet.{u} 2) p)

end DifferentialGeometry.Geometry.Collapse
