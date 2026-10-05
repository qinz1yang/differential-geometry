import DifferentialGeometry.Geometry.Collapse.Inhabitants.CuspTruncation
import DifferentialGeometry.Geometry.Metric.Tensor.CompactBounds
import DifferentialGeometry.Geometry.Metric.Distance.CompactImage
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Restriction

/-!
The fixed height 200 cusp truncation has two actual boundary collars. Their tensor errors
and compact torus diameters have a common positive bound, without a small bound claim.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Tensor0SBundle
open GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

def cuspBoundaryReflection : (productSet.{u} 2) ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ (productSet.{u} 2) :=
  (torusMonodromyPolarDiffeomorph.{u}.trans torusMonodromyCylinderReflection).trans
    torusMonodromyPolarDiffeomorph.{u}.symm

def cuspTruncationUpperCollar : CuspHalfSpace → (productSet.{u} 2) :=
  cuspBoundaryReflection.{u} ∘ cuspTruncationCollar.{u}

private def cuspWindow : TopologicalSpace.Opens CuspHalfSpace :=
  ⟨{p | p.2.val 0 < 150}, isOpen_lt
    (contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd) continuous_const⟩

local instance boundaryCircleHausdorff : T2Space Circle := inferInstance

local instance boundaryTorusHausdorff : T2Space Torus :=
  inferInstanceAs (T2Space (Circle × Circle))

local instance boundaryHalfSpaceHausdorff : T2Space (EuclideanHalfSpace 1) :=
  inferInstanceAs (T2Space {x : EuclideanSpace ℝ (Fin 1) | 0 ≤ x 0})

local instance cuspHalfSpaceHausdorff : T2Space CuspHalfSpace :=
  inferInstanceAs (T2Space (Torus × EuclideanHalfSpace 1))

local instance cuspWindowHausdorff : T2Space cuspWindow :=
  inferInstanceAs (T2Space {p : CuspHalfSpace | p.2.val 0 < 150})

private theorem lowerCollar_window_smooth :
    ContMDiffOn halfCollarModel (𝓡∂ 3) ∞ cuspTruncationCollar.{u} cuspWindow := by
  change ContMDiffOn halfCollarModel (𝓡∂ 3) ∞
    (torusMonodromyPolarDiffeomorph.{u}.symm ∘
      (fun p : CuspHalfSpace => (p.1, Set.projIcc 0 1 (by norm_num) (p.2.val 0 / 200)))) _
  apply torusMonodromyPolarDiffeomorph.{u}.symm.contMDiff.comp_contMDiffOn
  apply contMDiff_fst.contMDiffOn.prodMk
  apply contMDiffOn_projIcc.comp
    ((contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd).div_const 200).contMDiffOn
  intro p hp
  change p.2.val 0 < 150 at hp
  change p.2.val 0 / 200 ∈ Icc (0 : ℝ) 1
  exact ⟨div_nonneg p.2.property (by norm_num), by linarith⟩

private theorem window_subset (p : CuspHalfSpace) (hp : p ∈ cuspDomain) : p ∈ cuspWindow := by
  change p.2.val 0 < 150
  change p.2.val 0 < 100 at hp
  linarith

private theorem upperCollar_window_smooth :
    ContMDiffOn halfCollarModel (𝓡∂ 3) ∞ cuspTruncationUpperCollar.{u} cuspWindow :=
  cuspBoundaryReflection.{u}.contMDiff.comp_contMDiffOn lowerCollar_window_smooth.{u}

private theorem upperCollar_embedding : _root_.Topology.IsEmbedding
    (fun p : cuspDomain => cuspTruncationUpperCollar.{u} p.val) :=
  cuspBoundaryReflection.{u}.toHomeomorph.isEmbedding.comp standardCuspTruncation.{u}.isEmbedding

private theorem upperCollar_immersion (p : CuspHalfSpace) (hp : p ∈ cuspDomain) :
    Injective (mfderiv halfCollarModel (𝓡∂ 3) cuspTruncationUpperCollar.{u} p) := by
  have hf := (lowerCollar_window_smooth.{u}.contMDiffAt
    (cuspWindow.isOpen.mem_nhds (window_subset p hp))).mdifferentiableAt (by simp)
  rw [cuspTruncationUpperCollar, mfderiv_comp p
    (cuspBoundaryReflection.{u}.contMDiff.mdifferentiableAt (by simp)) hf]
  have hR : Injective (mfderiv (𝓡∂ 3) (𝓡∂ 3) cuspBoundaryReflection.{u}
      (cuspTruncationCollar.{u} p)) := by
    rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe cuspBoundaryReflection.{u} (by simp)]
    exact (cuspBoundaryReflection.{u}.mfderivToContinuousLinearEquiv
      (by simp) (cuspTruncationCollar.{u} p)).injective
  exact hR.comp (standardCuspTruncation.{u}.immersion p hp)

private theorem reflection_polar (x : productSet.{u} 2) :
    torusMonodromyPolarDiffeomorph.{u} (cuspBoundaryReflection.{u} x) =
      torusMonodromyCylinderReflection (torusMonodromyPolarDiffeomorph.{u} x) := by
  exact torusMonodromyPolarDiffeomorph.{u}.apply_symm_apply _

private theorem reflection_end {a : unitInterval} {x : productSet.{u} 2} :
    cuspBoundaryReflection.{u} x ∈ torusMonodromyEnd.{u} a ↔
      x ∈ torusMonodromyEnd.{u} (torusMonodromyIntervalReflection a) := by
  change (torusMonodromyPolarDiffeomorph.{u} (cuspBoundaryReflection.{u} x)).2 = a ↔ _
  rw [reflection_polar]
  change torusMonodromyIntervalReflection (torusMonodromyPolarDiffeomorph.{u} x).2 = a ↔
    (torusMonodromyPolarDiffeomorph.{u} x).2 = torusMonodromyIntervalReflection a
  constructor
  · intro h
    have hh := congrArg Subtype.val h
    apply Subtype.ext
    change (torusMonodromyPolarDiffeomorph.{u} x).2.val = 1 - a.val
    change 1 - (torusMonodromyPolarDiffeomorph.{u} x).2.val = a.val at hh
    linarith
  · intro h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    change 1 - (torusMonodromyPolarDiffeomorph.{u} x).2.val = a.val
    change (torusMonodromyPolarDiffeomorph.{u} x).2.val = 1 - a.val at hh
    linarith

private theorem upperCollar_boundary_preimage {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    cuspTruncationUpperCollar.{u} p ∈ (𝓡∂ 3).boundary (productSet.{u} 2) ↔ p.2.val 0 = 0 := by
  exact ((cuspBoundaryReflection.{u}.isLocalDiffeomorph
    (cuspTruncationCollar.{u} p)).isBoundaryPoint_iff (by simp)).symm.trans
      (standardCuspTruncation.{u}.boundary_preimage hp)

private theorem truncationMap_smooth :
    ContMDiff (𝓡∂ 3) halfCollarModel ∞ cuspTruncationMap.{u} := by
  have ht : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞
      (fun r : unitInterval => halfSpaceOneLift (200 * r.val)) :=
    contMDiffOn_halfSpaceOneLift.comp_contMDiff
      (contMDiff_const.mul contMDiff_subtypeVal_Icc)
      (fun r => mul_nonneg (by norm_num) r.property.1)
  exact (contMDiff_id.prodMap ht).comp torusMonodromyPolarDiffeomorph.{u}.contMDiff

private theorem window_leftInverse {p : CuspHalfSpace} (hp : p ∈ cuspWindow) :
    cuspTruncationMap.{u} (cuspTruncationCollar.{u} p) = p := by
  have hm : p.2.val 0 / 200 ∈ Icc (0 : ℝ) 1 := by
    change p.2.val 0 < 150 at hp
    exact ⟨div_nonneg p.2.property (by norm_num), by linarith⟩
  change Prod.map id (fun r : unitInterval => halfSpaceOneLift (200 * r.val))
    (torusMonodromyPolarDiffeomorph.{u} (torusMonodromyPolarDiffeomorph.{u}.symm
      (p.1, Set.projIcc 0 1 (by norm_num) (p.2.val 0 / 200)))) = p
  rw [Diffeomorph.apply_symm_apply]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply (PiLp.equivOfUnique 2 ℝ (fun i : Fin 1 => ℝ)).injective
    change max (200 * (Set.projIcc 0 1 (by norm_num) (p.2.val 0 / 200)).val) 0 = p.2.val 0
    rw [Set.projIcc_of_mem (by norm_num) hm]
    change max (200 * (p.2.val 0 / 200)) 0 = p.2.val 0
    rw [show 200 * (p.2.val 0 / 200) = p.2.val 0 by ring]
    exact max_eq_left p.2.property

private theorem lowerWindow_derivative (p : CuspHalfSpace) (hp : p ∈ cuspWindow)
    (v : TangentSpace halfCollarModel p) :
    mfderiv (𝓡∂ 3) halfCollarModel cuspTruncationMap.{u} (cuspTruncationCollar.{u} p)
      (mfderiv halfCollarModel (𝓡∂ 3) cuspTruncationCollar.{u} p v) = v := by
  have he : cuspTruncationMap.{u} ∘ cuspTruncationCollar.{u} =ᶠ[𝓝 p] id := by
    filter_upwards [cuspWindow.isOpen.mem_nhds hp] with q hq
    exact window_leftInverse.{u} hq
  have hd := he.mfderiv_eq (I := halfCollarModel) (I' := halfCollarModel)
  have hc := mfderiv_comp p (truncationMap_smooth.{u}.mdifferentiableAt (by simp))
    ((lowerCollar_window_smooth.{u}.contMDiffAt
      (cuspWindow.isOpen.mem_nhds hp)).mdifferentiableAt (by simp))
  rw [mfderiv_id] at hd
  have hh := congrArg (fun L => L v) (hc.symm.trans hd)
  change _ = v at hh
  exact hh

private theorem upperWindow_immersion (p : cuspWindow) :
    Injective (mfderiv halfCollarModel (𝓡∂ 3)
      (fun q : cuspWindow => cuspTruncationUpperCollar.{u} q.val) p) := by
  rw [mfderiv_restrict_open]
  have hf := (lowerCollar_window_smooth.{u}.contMDiffAt
    (cuspWindow.isOpen.mem_nhds p.property)).mdifferentiableAt (by simp)
  rw [cuspTruncationUpperCollar, mfderiv_comp p.val
    (cuspBoundaryReflection.{u}.contMDiff.mdifferentiableAt (by simp)) hf]
  have hR : Injective (mfderiv (𝓡∂ 3) (𝓡∂ 3) cuspBoundaryReflection.{u}
      (cuspTruncationCollar.{u} p.val)) := by
    rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe cuspBoundaryReflection.{u} (by simp)]
    exact (cuspBoundaryReflection.{u}.mfderivToContinuousLinearEquiv
      (by simp) (cuspTruncationCollar.{u} p.val)).injective
  have hF : Injective (mfderiv halfCollarModel (𝓡∂ 3) cuspTruncationCollar.{u} p.val) := by
    intro v w hvw
    have hh := congrArg (mfderiv (𝓡∂ 3) halfCollarModel cuspTruncationMap.{u}
      (cuspTruncationCollar.{u} p.val)) hvw
    exact (lowerWindow_derivative.{u} p.val p.property v).symm.trans
      (hh.trans (lowerWindow_derivative.{u} p.val p.property w))
  exact hR.comp hF

private theorem upperWindow_smooth :
    ContMDiff halfCollarModel (𝓡∂ 3) ∞
      (fun q : cuspWindow => cuspTruncationUpperCollar.{u} q.val) := by
  intro q
  exact contMDiffAt_subtype_iff.mpr
    (upperCollar_window_smooth.{u}.contMDiffAt (cuspWindow.isOpen.mem_nhds q.property))

private def upperWindowMetric : SmoothRiemannianMetric halfCollarModel cuspWindow :=
  cuspTruncationMetric.{u}.pullbackOfImmersion
    (fun q : cuspWindow => cuspTruncationUpperCollar.{u} q.val)
    upperWindow_smooth.{u} upperWindow_immersion.{u}

private def upperWindowTensor : Tensor0SField (I := halfCollarModel)
    (M := cuspWindow) ∞ 2 :=
  metricTensorField upperWindowMetric.{u} -
    metricTensorField (standardHyperbolicCusp.metric.restrictOpen cuspWindow)

private theorem upperWindowTensor_error (q : cuspWindow) :
    upperWindowTensor.{u} q = cuspMetricError (W := annulusCircleCarrier.{u})
      cuspTruncationMetric.{u} standardHyperbolicCusp cuspTruncationUpperCollar.{u} q.val := by
  ext v
  change upperWindowMetric.{u}.inner q (v 0) (v 1) -
    standardHyperbolicCusp.metric.inner q.val (v 0) (v 1) =
      localPullInner (I := halfCollarModel) (J := 𝓡∂ 3) cuspTruncationMetric.{u}
        cuspTruncationUpperCollar.{u} q.val (v 0) (v 1) -
          standardHyperbolicCusp.metric.inner q.val (v 0) (v 1)
  have hD := mfderiv_restrict_open (I := halfCollarModel) (J := 𝓡∂ 3)
    cuspTruncationUpperCollar.{u} cuspWindow q
  have hI := congrArg (fun D : TangentSpace halfCollarModel q →L[ℝ]
      TangentSpace (𝓡∂ 3) (cuspTruncationUpperCollar.{u} q.val) =>
    cuspTruncationMetric.{u}.inner (cuspTruncationUpperCollar.{u} q.val)
      (D (v 0)) (D (v 1))) hD
  exact congrArg (fun r : ℝ => r -
    standardHyperbolicCusp.metric.inner q.val (v 0) (v 1)) hI

private def compactWindowMap (q : Torus × Icc (0 : ℝ) 100) : cuspWindow :=
  ⟨(q.1, halfSpaceOneLift q.2.val), by
    change max q.2.val 0 < 150
    rw [max_eq_left q.2.property.1]
    linarith [q.2.property.2]⟩

private theorem compactWindowMap_continuous : Continuous compactWindowMap := by
  have hh : Continuous halfSpaceOneLift :=
    (𝓡∂ 1).continuous_symm.comp
      (PiLp.equivOfUnique 2 ℝ (fun i : Fin 1 => ℝ)).symm.continuous
  exact (continuous_fst.prodMk
    (hh.comp (continuous_subtype_val.comp continuous_snd))).subtype_mk _

private theorem compactWindow_contains (p : CuspHalfSpace) (hp : p ∈ cuspDomain) :
    (⟨p, window_subset p hp⟩ : cuspWindow) ∈ Set.range compactWindowMap := by
  have h100 : p.2.val 0 ≤ 100 := by change p.2.val 0 < 100 at hp; exact hp.le
  refine ⟨(p.1, ⟨p.2.val 0, p.2.property, h100⟩), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply (PiLp.equivOfUnique 2 ℝ (fun i : Fin 1 => ℝ)).injective
    change max (p.2.val 0) 0 = p.2.val 0
    exact max_eq_left p.2.property

private theorem upperError_bound : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ cuspDomain,
    tensor0SFiberNorm standardHyperbolicCusp.metric p 2
      (cuspMetricError (W := annulusCircleCarrier.{u}) cuspTruncationMetric.{u}
        standardHyperbolicCusp cuspTruncationUpperCollar.{u} p) ≤ C := by
  obtain ⟨C, hC, hb⟩ := DifferentialGeometry.Geometry.Tensor.exists_pos_bound_norm_on_compact
    (standardHyperbolicCusp.metric.restrictOpen cuspWindow) upperWindowTensor.{u}
    (isCompact_range compactWindowMap_continuous)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hh := hb ⟨p, window_subset p hp⟩ (compactWindow_contains p hp)
  rw [normSq0S_restrictOpen_apply, upperWindowTensor_error.{u}] at hh
  exact hh

private theorem upperCollar_boundary_image :
    Set.range (fun t : Torus => cuspTruncationUpperCollar.{u} (t, halfZero)) =
      torusMonodromyEnd.{u} 1 := by
  have h10 : torusMonodromyIntervalReflection 1 = 0 := by
    apply Subtype.ext
    change (1 : ℝ) - 1 = 0
    norm_num
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    apply (reflection_end.{u} (a := 1)).mpr
    rw [h10]
    change cuspTruncationCollar.{u} (t, halfZero) ∈ cuspTruncationZeroEnd.{u}
    rw [← standardCuspTruncation.{u}.boundary_image]
    exact ⟨t, rfl⟩
  · intro hx
    have hy : cuspBoundaryReflection.{u}.symm x ∈ torusMonodromyEnd.{u} 0 := by
      have hh := (reflection_end.{u} (a := 1)
        (x := cuspBoundaryReflection.{u}.symm x)).mp
        (by simpa only [Diffeomorph.apply_symm_apply] using hx)
      rwa [h10] at hh
    change cuspBoundaryReflection.{u}.symm x ∈ cuspTruncationZeroEnd.{u} at hy
    rw [← standardCuspTruncation.{u}.boundary_image] at hy
    obtain ⟨t, ht⟩ := hy
    exact ⟨t, (congrArg cuspBoundaryReflection.{u} ht).trans
      (cuspBoundaryReflection.{u}.apply_symm_apply x)⟩

theorem exists_cuspTruncationUpperCollar : ∃ C : ℝ, 0 < C ∧ Nonempty
    (CuspEmbedding annulusCircleCarrier.{u} cuspTruncationMetric.{u} 0 C
      (torusMonodromyEnd.{u} 1)) := by
  obtain ⟨C, hC, hb⟩ := upperError_bound.{u}
  refine ⟨C, hC, ⟨{
    cusp := standardHyperbolicCusp
    toFun := cuspTruncationUpperCollar.{u}
    contMDiffOn := (upperCollar_window_smooth.{u}.mono window_subset).of_le (by simp)
    isEmbedding := upperCollar_embedding.{u}
    immersion := upperCollar_immersion.{u}
    boundary_image := upperCollar_boundary_image.{u}
    boundary_preimage := upperCollar_boundary_preimage.{u}
    metric_error := ?_ }⟩⟩
  intro k hk p hp
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
  subst k
  exact hb p hp

private def endParam (a : unitInterval) : C(Torus, productSet.{u} 2) where
  toFun t := (torusMonodromyEndParam.{u} a t).val
  continuous_toFun := continuous_subtype_val.comp (torusMonodromyEndParam.{u} a).continuous

private theorem endParam_range (a : unitInterval) :
    Set.range (endParam.{u} a) = torusMonodromyEnd.{u} a := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact (torusMonodromyEndParam.{u} a t).property
  · intro hx
    obtain ⟨t, ht⟩ := (torusMonodromyEndParam.{u} a).surjective ⟨x, hx⟩
    exact ⟨t, congrArg Subtype.val ht⟩

private theorem end_connected (a : unitInterval) : IsConnected (torusMonodromyEnd.{u} a) := by
  rw [← endParam_range.{u} a]
  exact isConnected_range (endParam.{u} a).continuous

private theorem end_closed (a : unitInterval) : IsClosed (torusMonodromyEnd.{u} a) :=
  isClosed_eq (continuous_snd.comp torusMonodromyPolarDiffeomorph.{u}.continuous) continuous_const

private theorem end_diameter_bound (a : unitInterval) : ∃ R : ℝ,
    ∀ x ∈ torusMonodromyEnd.{u} a, ∀ y ∈ torusMonodromyEnd.{u} a,
      riemannianEDistOf cuspTruncationMetric.{u} x y ≤ ENNReal.ofReal R := by
  obtain ⟨R, hR, hb⟩ := exists_uniform_riemannianEDistOf_bound_of_compact_preconnected
    cuspTruncationMetric.{u} (endParam.{u} a) (1, 1)
  refine ⟨R + R, fun x hx y hy => ?_⟩
  rw [← endParam_range.{u} a] at hx hy
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hy
  calc
    riemannianEDistOf cuspTruncationMetric.{u} (endParam.{u} a t) (endParam.{u} a s) ≤
        riemannianEDistOf cuspTruncationMetric.{u} (endParam.{u} a t) (endParam.{u} a (1, 1)) +
          riemannianEDistOf cuspTruncationMetric.{u} (endParam.{u} a (1, 1)) (endParam.{u} a s) :=
      riemannianEDistOf_triangle _ _ _ _
    _ ≤ ENNReal.ofReal R + ENNReal.ofReal R := add_le_add (hb t)
      (by rw [riemannianEDistOf_comm]; exact hb s)
    _ = ENNReal.ofReal (R + R) := (ENNReal.ofReal_add hR hR).symm

def cuspTruncationBoundaryComponent (i : Fin 2) : Set (productSet.{u} 2) :=
  torusMonodromyEnd.{u} (if i = 0 then 0 else 1)

private theorem components_disjoint : Pairwise
    (fun i j : Fin 2 => Disjoint (cuspTruncationBoundaryComponent.{u} i)
      (cuspTruncationBoundaryComponent.{u} j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · rw [Set.disjoint_left]
    intro x hx hy
    have hh := congrArg Subtype.val (hx.symm.trans hy)
    norm_num at hh
  · rw [Set.disjoint_left]
    intro x hx hy
    have hh := congrArg Subtype.val (hx.symm.trans hy)
    norm_num at hh
  · exact False.elim (hij rfl)

theorem cuspTruncationBoundaryComponent_cover :
    ⋃ i, cuspTruncationBoundaryComponent.{u} i = (𝓡∂ 3).boundary (productSet.{u} 2) := by
  rw [torusMonodromyGluing_boundary (Diffeomorph.refl torusModel Torus ∞)]
  change (⋃ i, cuspTruncationBoundaryComponent.{u} i) =
    ⋃ i : Fin 1, (torusMonodromyEnd.{u} 1 ∪ torusMonodromyEnd.{u} 0)
  ext x
  simp only [Set.mem_iUnion, Set.mem_union, Fin.exists_fin_two, Fin.exists_fin_one]
  change x ∈ torusMonodromyEnd.{u} 0 ∨ x ∈ torusMonodromyEnd.{u} 1 ↔
    x ∈ torusMonodromyEnd.{u} 1 ∨ x ∈ torusMonodromyEnd.{u} 0
  exact or_comm

theorem exists_cuspTruncationBoundary : ∃ δ : ℝ, 0 < δ ∧ Nonempty
    (NearlyCuspidalBoundary annulusCircleCarrier.{u} cuspTruncationMetric.{u} 0 δ) := by
  obtain ⟨C, hC, ⟨upper⟩⟩ := exists_cuspTruncationUpperCollar.{u}
  obtain ⟨R0, hb0⟩ := end_diameter_bound.{u} 0
  obtain ⟨R1, hb1⟩ := end_diameter_bound.{u} 1
  let δ : ℝ := max 1 (max C (max R0 R1))
  have h1 : 1 ≤ δ := le_max_left _ _
  have hCδ : C ≤ δ := (le_max_left _ _).trans (le_max_right _ _)
  have hR0δ : R0 ≤ δ := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hR1δ : R1 ≤ δ := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨δ, hC.trans_le hCδ, ⟨{
    count := 2
    count_pos := by norm_num
    component := cuspTruncationBoundaryComponent.{u}
    connected := fun i => end_connected.{u} _
    closed := fun i => end_closed.{u} _
    disjoint := components_disjoint.{u}
    covers := cuspTruncationBoundaryComponent_cover.{u}
    diameter := ?_
    collar := ?_ }⟩⟩
  · intro i x hx y hy
    fin_cases i
    · exact (hb0 x hx y hy).trans (ENNReal.ofReal_le_ofReal hR0δ)
    · exact (hb1 x hx y hy).trans (ENNReal.ofReal_le_ofReal hR1δ)
  · intro i
    exact Fin.cases (standardCuspTruncation.{u}.weaken h1)
      (fun j => Fin.cases (upper.weaken hCδ) (fun k => Fin.elim0 k) j) i

theorem cuspTruncationUpperCollar_polar (p : CuspHalfSpace) (hp : p ∈ cuspDomain) :
    (torusMonodromyPolarDiffeomorph.{u} (cuspTruncationUpperCollar.{u} p)).1 = p.1 ∧
      (torusMonodromyPolarDiffeomorph.{u} (cuspTruncationUpperCollar.{u} p)).2.val =
        1 - p.2.val 0 / 200 := by
  have hm : p.2.val 0 / 200 ∈ Icc (0 : ℝ) 1 := by
    change p.2.val 0 < 100 at hp
    exact ⟨div_nonneg p.2.property (by norm_num), by linarith⟩
  change (torusMonodromyPolarDiffeomorph.{u}
    (cuspBoundaryReflection.{u} (cuspTruncationCollar.{u} p))).1 = p.1 ∧
    (torusMonodromyPolarDiffeomorph.{u}
      (cuspBoundaryReflection.{u} (cuspTruncationCollar.{u} p))).2.val = 1 - p.2.val 0 / 200
  simp only [reflection_polar]
  change (torusMonodromyCylinderReflection
    (torusMonodromyPolarDiffeomorph.{u} (torusMonodromyPolarDiffeomorph.{u}.symm
      (p.1, Set.projIcc 0 1 (by norm_num) (p.2.val 0 / 200))))).1 = p.1 ∧
    (torusMonodromyCylinderReflection
      (torusMonodromyPolarDiffeomorph.{u} (torusMonodromyPolarDiffeomorph.{u}.symm
        (p.1, Set.projIcc 0 1 (by norm_num) (p.2.val 0 / 200))))).2.val = 1 - p.2.val 0 / 200
  rw [Diffeomorph.apply_symm_apply]
  change p.1 = p.1 ∧ 1 - (Set.projIcc 0 1 (by norm_num) (p.2.val 0 / 200)).val =
    1 - p.2.val 0 / 200
  rw [Set.projIcc_of_mem (by norm_num) hm]
  exact ⟨rfl, rfl⟩

end DifferentialGeometry.Geometry.Collapse

