import DifferentialGeometry.Geometry.Collapse.Inhabitants.CuspMetric
import DifferentialGeometry.Geometry.Collapse.CuspBoundary
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.TorusMonodromy
import DifferentialGeometry.Topology.Manifold.HalfLine

/-!
The annulus circle carrier carries the actual height 200 truncation of the standard cusp.
Its height zero end has an embedded collar whose pulled back metric error is zero.
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold.Interval
open GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

private def truncationHeight (r : unitInterval) : EuclideanHalfSpace 1 :=
  halfSpaceOneLift (200 * r.val)

private theorem truncationHeight_smooth :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ truncationHeight :=
  contMDiffOn_halfSpaceOneLift.comp_contMDiff
    (contMDiff_const.mul contMDiff_subtypeVal_Icc)
    (fun r => mul_nonneg (by norm_num) r.property.1)

private theorem truncationHeight_coordinate (r : unitInterval) :
    (truncationHeight r).val 0 = 200 * r.val := by
  change max (200 * r.val) 0 = 200 * r.val
  exact max_eq_left (mul_nonneg (by norm_num) r.property.1)

private theorem truncationHeight_injective_derivative (r : unitInterval) :
    Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1) truncationHeight r) := by
  have he : (fun r : unitInterval => (truncationHeight r).val 0) =
      (fun r : unitInterval => 200 * r.val) := funext truncationHeight_coordinate
  have hc := mfderiv_comp r
    (contMDiff_halfSpaceOneCoordinate.mdifferentiableAt (by simp))
    (truncationHeight_smooth.mdifferentiableAt (by simp))
  rw [show (fun t : EuclideanHalfSpace 1 => t.val 0) ∘ truncationHeight =
    (fun r : unitInterval => 200 * r.val) from he] at hc
  intro v w hvw
  have hh := congrArg (mfderiv (𝓡∂ 1) 𝓘(ℝ)
    (fun t : EuclideanHalfSpace 1 => t.val 0) (truncationHeight r)) hvw
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← hc] at hh
  have hd : mfderiv (𝓡∂ 1) 𝓘(ℝ) (fun r : unitInterval => 200 * r.val) r =
      (200 : ℝ) • mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) r := by
    exact (((contMDiff_subtypeVal_Icc (x := 0) (y := 1) (n := ∞)).mdifferentiableAt
      (by simp)).hasMFDerivAt.const_smul (200 : ℝ)).mfderiv
  rw [hd] at hh
  change (200 : ℝ) • (mfderiv (𝓡∂ 1) 𝓘(ℝ)
    (Subtype.val : unitInterval → ℝ) r v) = (200 : ℝ) •
    (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) r w) at hh
  apply (tangentCoordinateIcc r).injective
  rw [tangentCoordinateIcc_apply, tangentCoordinateIcc_apply]
  exact congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (r : ℝ))
    (by
      have he := congrArg (fun z : TangentSpace 𝓘(ℝ) (r : ℝ) => (1 / 200 : ℝ) • z) hh
      simpa only [smul_smul, show (1 / 200 : ℝ) * 200 = 1 by norm_num, one_smul] using he)

def cuspTruncationMap : (productSet.{u} 2) → CuspHalfSpace :=
  Prod.map id truncationHeight ∘ torusMonodromyPolarDiffeomorph.{u}

private theorem cuspTruncationMap_smooth :
    ContMDiff (𝓡∂ 3) halfCollarModel ∞ cuspTruncationMap.{u} :=
  (contMDiff_id.prodMap truncationHeight_smooth).comp
    torusMonodromyPolarDiffeomorph.{u}.contMDiff

private theorem cuspTruncationMap_immersion (x : (productSet.{u} 2)) :
    Injective (mfderiv (𝓡∂ 3) halfCollarModel cuspTruncationMap.{u} x) := by
  change Injective (mfderiv (𝓡∂ 3) halfCollarModel
    (Prod.map id truncationHeight ∘ torusMonodromyPolarDiffeomorph.{u})
    (x : productSet.{u} 2))
  rw [mfderiv_comp (I := 𝓡∂ 3)
    (I' := torusMonodromyCylinderModel) (I'' := halfCollarModel) x
    ((contMDiff_id.prodMap truncationHeight_smooth).mdifferentiableAt (by simp))
    (torusMonodromyPolarDiffeomorph.{u}.contMDiff.mdifferentiableAt (by simp))]
  have hi : Injective (mfderiv torusMonodromyCylinderModel halfCollarModel
      (Prod.map id truncationHeight) (torusMonodromyPolarDiffeomorph.{u} x)) := by
    rw [mfderiv_prodMap mdifferentiableAt_id
      (truncationHeight_smooth.mdifferentiableAt (by simp)), mfderiv_id]
    intro v w hvw
    change (v.1, mfderiv (𝓡∂ 1) (𝓡∂ 1) truncationHeight
      (torusMonodromyPolarDiffeomorph.{u} x).2 v.2) =
      (w.1, mfderiv (𝓡∂ 1) (𝓡∂ 1) truncationHeight
        (torusMonodromyPolarDiffeomorph.{u} x).2 w.2) at hvw
    apply Prod.ext
    · have hh := congrArg
        (fun z : TangentSpace halfCollarModel
          (Prod.map id truncationHeight (torusMonodromyPolarDiffeomorph.{u} x)) => z.1) hvw
      exact hh
    · exact truncationHeight_injective_derivative _ (congrArg Prod.snd hvw)
  have hj : Injective (mfderiv (𝓡∂ 3) torusMonodromyCylinderModel
      torusMonodromyPolarDiffeomorph.{u} x) := by
    rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
      torusMonodromyPolarDiffeomorph.{u} (by simp)]
    exact (torusMonodromyPolarDiffeomorph.{u}.mfderivToContinuousLinearEquiv (by simp) x).injective
  exact hi.comp hj

def cuspTruncationMetric : SmoothRiemannianMetric
    (𝓡∂ 3) (productSet.{u} 2) :=
  standardHyperbolicCusp.metric.pullbackOfImmersion cuspTruncationMap.{u}
    cuspTruncationMap_smooth.{u} cuspTruncationMap_immersion.{u}

private def truncationInterval (s : EuclideanHalfSpace 1) : unitInterval :=
  Set.projIcc 0 1 (by norm_num) (s.val 0 / 200)

private theorem truncationInterval_val {s : EuclideanHalfSpace 1}
    (hs : s.val 0 < 100) : (truncationInterval s).val = s.val 0 / 200 := by
  have hm : s.val 0 / 200 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg s.property (by norm_num)
    · linarith
  exact congrArg Subtype.val (Set.projIcc_of_mem (by norm_num) hm)

private theorem truncationInterval_smooth :
    ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞ truncationInterval {s | s.val 0 < 100} := by
  apply contMDiffOn_projIcc.comp
    (contMDiff_halfSpaceOneCoordinate.div_const 200).contMDiffOn
  intro s hs
  change s.val 0 < 100 at hs
  dsimp only [Set.mem_preimage, Set.mem_Icc]
  exact ⟨div_nonneg s.property (by norm_num), by linarith⟩

def cuspTruncationCollar : CuspHalfSpace → (productSet.{u} 2) :=
  torusMonodromyPolarDiffeomorph.{u}.symm ∘ Prod.map id truncationInterval

private theorem cuspTruncationCollar_smooth :
    ContMDiffOn halfCollarModel (𝓡∂ 3) ∞
      cuspTruncationCollar.{u} cuspDomain := by
  apply torusMonodromyPolarDiffeomorph.{u}.symm.contMDiff.comp_contMDiffOn
  exact contMDiff_fst.contMDiffOn.prodMk
    (truncationInterval_smooth.comp contMDiff_snd.contMDiffOn (fun p hp => hp))

private theorem cuspTruncationMap_collar {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    cuspTruncationMap.{u} (cuspTruncationCollar.{u} p) = p := by
  change Prod.map id truncationHeight
    (torusMonodromyPolarDiffeomorph.{u} (torusMonodromyPolarDiffeomorph.{u}.symm
      (Prod.map id truncationInterval p))) = p
  rw [Diffeomorph.apply_symm_apply]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply (PiLp.equivOfUnique 2 ℝ (fun i : Fin 1 => ℝ)).injective
    change (truncationHeight (truncationInterval p.2)).val 0 = p.2.val 0
    rw [truncationHeight_coordinate, truncationInterval_val hp]
    ring

private theorem truncationDomain_open : IsOpen cuspDomain :=
  isOpen_lt (contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd) continuous_const

private theorem cuspTruncationCollar_derivative {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) (v : TangentSpace halfCollarModel p) :
    mfderiv (𝓡∂ 3) halfCollarModel cuspTruncationMap.{u}
      (cuspTruncationCollar.{u} p)
      (mfderiv halfCollarModel (𝓡∂ 3) cuspTruncationCollar.{u} p v) = v := by
  have he : cuspTruncationMap.{u} ∘ cuspTruncationCollar.{u} =ᶠ[𝓝 p] id := by
    filter_upwards [truncationDomain_open.mem_nhds hp] with q hq
    exact cuspTruncationMap_collar.{u} hq
  have hd := he.mfderiv_eq (I := halfCollarModel) (I' := halfCollarModel)
  have hc := mfderiv_comp p
    (cuspTruncationMap_smooth.{u}.mdifferentiableAt (by simp))
    ((cuspTruncationCollar_smooth.{u}.contMDiffAt
      (truncationDomain_open.mem_nhds hp)).mdifferentiableAt (by simp))
  rw [mfderiv_id] at hd
  have hh := congrArg (fun L => L v) (hc.symm.trans hd)
  change _ = v at hh
  exact hh

private theorem cuspTruncationCollar_embedding :
    _root_.Topology.IsEmbedding
      (fun p : cuspDomain => cuspTruncationCollar.{u} p.val) := by
  apply _root_.Topology.IsEmbedding.of_comp
    cuspTruncationCollar_smooth.{u}.continuousOn.domRestrict
    cuspTruncationMap_smooth.{u}.continuous
  have he : cuspTruncationMap.{u} ∘
      (fun p : cuspDomain => cuspTruncationCollar.{u} p.val) = Subtype.val := by
    funext p
    exact cuspTruncationMap_collar.{u} p.property
  change _root_.Topology.IsEmbedding (cuspTruncationMap.{u} ∘
    (fun p : cuspDomain => cuspTruncationCollar.{u} p.val))
  rw [he]
  exact _root_.Topology.IsEmbedding.subtypeVal

def cuspTruncationZeroEnd : Set (productSet.{u} 2) :=
  torusMonodromyEnd.{u} 0

private theorem cuspTruncationCollar_boundary_image :
    Set.range (fun t : Torus => cuspTruncationCollar.{u} (t, halfZero)) =
      cuspTruncationZeroEnd.{u} := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    change (torusMonodromyPolarDiffeomorph.{u}
      (torusMonodromyPolarDiffeomorph.{u}.symm
        (t, truncationInterval halfZero))).2 = 0
    rw [Diffeomorph.apply_symm_apply]
    apply Subtype.ext
    rw [truncationInterval_val (by change (0 : ℝ) < 100; norm_num)]
    norm_num [halfZero, halfPoint]
  · intro hx
    refine ⟨(torusMonodromyPolarDiffeomorph.{u} x).1, ?_⟩
    change torusMonodromyPolarDiffeomorph.{u}.symm
      ((torusMonodromyPolarDiffeomorph.{u} x).1, truncationInterval halfZero) = x
    have hz : truncationInterval halfZero = 0 := by
      apply Subtype.ext
      rw [truncationInterval_val (by change (0 : ℝ) < 100; norm_num)]
      norm_num [halfZero, halfPoint]
    have hp : ((torusMonodromyPolarDiffeomorph.{u} x).1, truncationInterval halfZero) =
        torusMonodromyPolarDiffeomorph.{u} x := Prod.ext rfl (hz.trans hx.symm)
    exact (congrArg torusMonodromyPolarDiffeomorph.{u}.symm hp).trans
      (torusMonodromyPolarDiffeomorph.{u}.symm_apply_apply x)

private theorem cuspTruncationCollar_boundary_preimage {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) :
    (cuspTruncationCollar.{u} p ∈
      (𝓡∂ 3).boundary (productSet.{u} 2) ↔
        p.2.val 0 = 0) := by
  rw [torusMonodromyGluing_boundary (Diffeomorph.refl torusModel Torus ∞)]
  change cuspTruncationCollar.{u} p ∈
    ⋃ i : Fin 1, (torusMonodromyEnd.{u} 1 ∪ torusMonodromyEnd.{u} 0) ↔ _
  simp only [Set.mem_iUnion, Fin.exists_fin_one]
  change (torusMonodromyPolarDiffeomorph.{u} (cuspTruncationCollar.{u} p)).2 = 1 ∨
    (torusMonodromyPolarDiffeomorph.{u} (cuspTruncationCollar.{u} p)).2 = 0 ↔ _
  change (torusMonodromyPolarDiffeomorph.{u}
    (torusMonodromyPolarDiffeomorph.{u}.symm (Prod.map id truncationInterval p))).2 = 1 ∨
    (torusMonodromyPolarDiffeomorph.{u}
      (torusMonodromyPolarDiffeomorph.{u}.symm (Prod.map id truncationInterval p))).2 = 0 ↔ _
  rw [Diffeomorph.apply_symm_apply]
  have hv := truncationInterval_val hp
  have hlt : (truncationInterval p.2).val < 1 := by
    rw [hv]
    change p.2.val 0 < 100 at hp
    linarith
  constructor
  · rintro (h | h)
    · have hh := congrArg Subtype.val h
      have heq : (truncationInterval p.2).val = 1 := hh
      exact False.elim (hlt.ne heq)
    · have hh := congrArg Subtype.val h
      change (truncationInterval p.2).val = 0 at hh
      rw [hv] at hh
      linarith
  · intro h
    right
    apply Subtype.ext
    change (truncationInterval p.2).val = 0
    rw [hv, h]
    norm_num

private theorem cuspTruncationCollar_inner {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) (v w : TangentSpace halfCollarModel p) :
    localPullInner cuspTruncationMetric.{u} cuspTruncationCollar.{u} p v w =
      standardHyperbolicCusp.metric.inner p v w := by
  rw [localPullInner_apply, cuspTruncationMetric,
    SmoothRiemannianMetric.pullbackOfImmersion_inner,
    cuspTruncationCollar_derivative.{u} hp, cuspTruncationCollar_derivative.{u} hp,
    cuspTruncationMap_collar.{u} hp]

theorem cuspTruncationMetricError_zero {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    cuspMetricError (W := annulusCircleCarrier.{u}) cuspTruncationMetric.{u} standardHyperbolicCusp
      cuspTruncationCollar.{u} p = 0 := by
  unfold cuspMetricError
  ext v
  change localPullInner (I := halfCollarModel) (J := 𝓡∂ 3)
    cuspTruncationMetric.{u} cuspTruncationCollar.{u} p (v 0) (v 1) -
    standardHyperbolicCusp.metric.inner p (v 0) (v 1) = 0
  rw [cuspTruncationCollar_inner.{u} hp]
  exact sub_self _

def standardCuspTruncation : CuspEmbedding annulusCircleCarrier.{u}
    cuspTruncationMetric.{u} 0 1 cuspTruncationZeroEnd.{u} where
  cusp := standardHyperbolicCusp
  toFun := cuspTruncationCollar.{u}
  contMDiffOn := cuspTruncationCollar_smooth.{u}.of_le (by simp)
  isEmbedding := cuspTruncationCollar_embedding.{u}
  immersion p hp := by
    intro v w hvw
    have hh := congrArg (mfderiv (𝓡∂ 3) halfCollarModel
      cuspTruncationMap.{u} (cuspTruncationCollar.{u} p)) hvw
    exact (cuspTruncationCollar_derivative.{u} hp v).symm.trans
      (hh.trans (cuspTruncationCollar_derivative.{u} hp w))
  boundary_image := cuspTruncationCollar_boundary_image.{u}
  boundary_preimage := cuspTruncationCollar_boundary_preimage.{u}
  metric_error := by
    intro k hk p hp
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    change DifferentialGeometry.Tensor0SBundle.tensor0SFiberNorm standardHyperbolicCusp.metric p 2
      (cuspMetricError (W := annulusCircleCarrier.{u}) cuspTruncationMetric.{u}
        standardHyperbolicCusp cuspTruncationCollar.{u} p) ≤ 1
    rw [cuspTruncationMetricError_zero.{u} hp]
    simp [DifferentialGeometry.Tensor0SBundle.tensor0SFiberNorm,
      DifferentialGeometry.Tensor0SBundle.normSq0S, DifferentialGeometry.Tensor0SBundle.inner0S,
      DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner]

theorem exists_standardCuspTruncation :
    ∃ g : SmoothRiemannianMetric annulusCircleCarrier.{u}.model
      annulusCircleCarrier.{u}.Carrier, ∃ δ : ℝ, ∃ X0 : Set annulusCircleCarrier.{u}.Carrier,
        0 < δ ∧ Nonempty (CuspEmbedding annulusCircleCarrier g 0 δ X0) :=
  ⟨cuspTruncationMetric.{u}, 1, cuspTruncationZeroEnd.{u}, by norm_num,
    ⟨standardCuspTruncation.{u}⟩⟩

end DifferentialGeometry.Geometry.Collapse

