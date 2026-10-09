import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspProfile
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Collapse.Inhabitants.CuspBoundaryModel

/-!
The fixed compact double cusp metric has two actual depth 100 end collars. The reference
flat torus carries the actual fibre scale, and both collars have zero metric error.
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold.Interval
open GC.Endpoint GC.Seifert GC.GraphManifold Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.TensorLieDeriv DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

def doubleCuspInterval (i : Fin 2) (s : EuclideanHalfSpace 1) : unitInterval :=
  Set.projIcc 0 1 (by norm_num) (if i = 0 then s.val 0 / 240 else 1 - s.val 0 / 240)

theorem doubleCuspInterval_val (i : Fin 2) {s : EuclideanHalfSpace 1}
    (hs : s.val 0 < 100) :
    (doubleCuspInterval i s).val = if i = 0 then s.val 0 / 240 else 1 - s.val 0 / 240 := by
  apply congrArg Subtype.val (Set.projIcc_of_mem (by norm_num) ?_)
  split_ifs
  · exact ⟨div_nonneg s.property (by norm_num), by linarith⟩
  · constructor <;> linarith [s.property]

theorem doubleCuspInterval_smooth (i : Fin 2) :
    ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞ (doubleCuspInterval i) {s | s.val 0 < 100} := by
  apply contMDiffOn_projIcc.comp
  · by_cases hi : i = 0
    · simpa only [hi, ite_true] using
        (contMDiff_halfSpaceOneCoordinate.div_const 240).contMDiffOn
    · simpa only [hi, ite_false] using
        (contMDiff_const.sub (contMDiff_halfSpaceOneCoordinate.div_const 240)).contMDiffOn
  · intro s hs
    change s.val 0 < 100 at hs
    change (if i = 0 then s.val 0 / 240 else 1 - s.val 0 / 240) ∈ Icc (0 : ℝ) 1
    split_ifs
    · exact ⟨div_nonneg s.property (by norm_num), by linarith⟩
    · constructor <;> linarith [s.property]

def doubleCuspCollar (i : Fin 2) : CuspHalfSpace → (productSet.{u} 2) :=
  fun p => torusMonodromyPolarDiffeomorph.{u}.symm (p.1, doubleCuspInterval i p.2)

theorem doubleCuspCollar_smooth (i : Fin 2) :
    ContMDiffOn halfCollarModel (𝓡∂ 3) ∞ (doubleCuspCollar.{u} i) cuspDomain :=
  torusMonodromyPolarDiffeomorph.{u}.symm.contMDiff.comp_contMDiffOn
    (contMDiff_fst.contMDiffOn.prodMk
      ((doubleCuspInterval_smooth i).comp contMDiff_snd.contMDiffOn
        (fun p hp => show p.2.val 0 < 100 from hp)))

def doubleCuspEndCoordinate (i : Fin 2) (p : CuspHalfSpace) : ℝ × Torus :=
  (if i = 0 then p.2.val 0 else 240 - p.2.val 0, p.1)

theorem doubleCuspEndCoordinate_smooth (i : Fin 2) :
    ContMDiff halfCollarModel (𝓘(ℝ, ℝ).prod torusModel) ∞ (doubleCuspEndCoordinate i) := by
  change ContMDiff halfCollarModel (𝓘(ℝ, ℝ).prod torusModel) ∞
    (fun p : CuspHalfSpace =>
      (if i = 0 then p.2.val 0 else 240 - p.2.val 0, p.1))
  apply ContMDiff.prodMk
  · by_cases hi : i = 0
    · simpa only [hi, ite_true, Function.comp_def] using
        contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd
    · simpa only [hi, ite_false, Function.comp_def] using
        contMDiff_const.sub (contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)
  · exact contMDiff_fst

theorem doubleCuspCoordinate_collar (i : Fin 2) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) :
    doubleCuspCoordinate.{u} (doubleCuspCollar.{u} i p) = doubleCuspEndCoordinate i p := by
  simp only [doubleCuspCoordinate, Function.comp_apply, doubleCuspCollar,
    Diffeomorph.apply_symm_apply, doubleCuspCylinderCoordinate, doubleCuspHeight]
  rw [doubleCuspInterval_val i hp]
  apply Prod.ext
  · dsimp only [doubleCuspEndCoordinate, Prod.fst]
    split_ifs <;> ring
  · rfl

private def doubleCuspRecover (i : Fin 2) (x : (productSet.{u} 2)) : CuspHalfSpace :=
  ((doubleCuspCoordinate x).2,
    halfSpaceOneLift (if i = 0 then (doubleCuspCoordinate x).1
      else 240 - (doubleCuspCoordinate x).1))

private theorem doubleCuspRecover_continuous (i : Fin 2) :
    Continuous (doubleCuspRecover.{u} i) := by
  apply Continuous.prodMk
  · exact continuous_snd.comp doubleCuspCoordinate_smooth.{u}.continuous
  · have hL : Continuous halfSpaceOneLift :=
      (𝓡∂ 1).continuous_symm.comp
        (PiLp.equivOfUnique 2 ℝ (fun j : Fin 1 => ℝ)).symm.continuous
    apply hL.comp
    by_cases hi : i = 0
    · simpa only [hi, ite_true, Function.comp_def] using
        continuous_fst.comp doubleCuspCoordinate_smooth.{u}.continuous
    · simp only [hi, ite_false]
      exact (continuous_const (y := (240 : ℝ))).sub
        (continuous_fst.comp doubleCuspCoordinate_smooth.{u}.continuous)

private theorem doubleCuspRecover_collar (i : Fin 2) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) : doubleCuspRecover.{u} i (doubleCuspCollar.{u} i p) = p := by
  simp only [doubleCuspRecover, doubleCuspCoordinate_collar i hp, doubleCuspEndCoordinate]
  apply Prod.ext
  · rfl
  · have hr : (if i = 0 then (if i = 0 then p.2.val 0 else 240 - p.2.val 0)
        else 240 - (if i = 0 then p.2.val 0 else 240 - p.2.val 0)) = p.2.val 0 := by
      split_ifs <;> ring
    rw [hr]
    apply Subtype.ext
    apply (PiLp.equivOfUnique 2 ℝ (fun j : Fin 1 => ℝ)).injective
    change max (p.2.val 0) 0 = p.2.val 0
    exact max_eq_left p.2.property

theorem doubleCuspCollar_embedding (i : Fin 2) :
    _root_.Topology.IsEmbedding (fun p : cuspDomain => doubleCuspCollar.{u} i p.val) := by
  apply _root_.Topology.IsEmbedding.of_comp
    (doubleCuspCollar_smooth.{u} i).continuousOn.domRestrict
    (doubleCuspRecover_continuous.{u} i)
  have h : doubleCuspRecover.{u} i ∘
      (fun p : cuspDomain => doubleCuspCollar.{u} i p.val) = Subtype.val := by
    funext p
    exact doubleCuspRecover_collar i p.property
  change _root_.Topology.IsEmbedding (doubleCuspRecover.{u} i ∘
    (fun p : cuspDomain => doubleCuspCollar.{u} i p.val))
  rw [h]
  exact _root_.Topology.IsEmbedding.subtypeVal

theorem doubleCuspEndCoordinate_derivative (i : Fin 2) (p : CuspHalfSpace)
    (v : TangentSpace halfCollarModel p) :
    mfderiv halfCollarModel (𝓘(ℝ, ℝ).prod torusModel)
      (doubleCuspEndCoordinate i) p v = (if i = 0 then v.2 0 else -v.2 0, v.1) := by
  have hc := (hasMFDerivAt_halfSpaceOneCoordinate p.2).comp p
    (hasMFDerivAt_snd (I := torusModel) (I' := 𝓡∂ 1) p)
  fin_cases i
  · change mfderiv halfCollarModel (𝓘(ℝ, ℝ).prod torusModel)
      (fun p : CuspHalfSpace => (p.2.val 0, p.1)) p v = (v.2 0, v.1)
    have h := (hc.prodMk (hasMFDerivAt_fst (I := torusModel) (I' := 𝓡∂ 1) p)).mfderiv
    erw [h]
    rfl
  · change mfderiv halfCollarModel (𝓘(ℝ, ℝ).prod torusModel)
      (fun p : CuspHalfSpace => (240 - p.2.val 0, p.1)) p v = (-v.2 0, v.1)
    have h := (((hasMFDerivAt_const (I := halfCollarModel) (I' := 𝓘(ℝ, ℝ))
      240 p).sub hc).prodMk (hasMFDerivAt_fst (I := torusModel) (I' := 𝓡∂ 1) p)).mfderiv
    erw [h]
    change (0 - v.2 0, v.1) = (-v.2 0, v.1)
    simp only [zero_sub]

private theorem doubleCuspDomain_open : IsOpen cuspDomain :=
  isOpen_lt (contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd) continuous_const

theorem doubleCuspCoordinate_collar_derivative (i : Fin 2) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) (v : TangentSpace halfCollarModel p) :
    mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) doubleCuspCoordinate.{u}
      (doubleCuspCollar.{u} i p)
      (mfderiv halfCollarModel (𝓡∂ 3) (doubleCuspCollar.{u} i) p v) =
        (if i = 0 then v.2 0 else -v.2 0, v.1) := by
  have he : doubleCuspCoordinate.{u} ∘ doubleCuspCollar.{u} i =ᶠ[𝓝 p]
      doubleCuspEndCoordinate i := by
    filter_upwards [doubleCuspDomain_open.mem_nhds hp] with q hq
    exact doubleCuspCoordinate_collar i hq
  have h := he.mfderiv_eq (I := halfCollarModel) (I' := 𝓘(ℝ, ℝ).prod torusModel)
  rw [mfderiv_comp p (doubleCuspCoordinate_smooth.{u}.mdifferentiableAt (by simp))
    (((doubleCuspCollar_smooth.{u} i).contMDiffAt
      (doubleCuspDomain_open.mem_nhds hp)).mdifferentiableAt (by simp))] at h
  exact (congrArg (fun L => L v) h).trans (doubleCuspEndCoordinate_derivative i p v)

theorem doubleCuspCollar_immersion (i : Fin 2) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    Injective (mfderiv halfCollarModel (𝓡∂ 3) (doubleCuspCollar.{u} i) p) := by
  intro v w hvw
  have h := congrArg (mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel)
    doubleCuspCoordinate.{u} (doubleCuspCollar.{u} i p)) hvw
  rw [doubleCuspCoordinate_collar_derivative i hp,
    doubleCuspCoordinate_collar_derivative i hp] at h
  apply Prod.ext
  · exact congrArg Prod.snd h
  · apply (PiLp.equivOfUnique 2 ℝ (fun j : Fin 1 => ℝ)).injective
    have hh := congrArg Prod.fst h
    by_cases hi : i = 0
    · change v.2 0 = w.2 0
      simpa only [hi, ite_true] using hh
    · change v.2 0 = w.2 0
      exact neg_injective (by simpa only [hi, ite_false] using hh)

def doubleCuspReference (a : ℝ) (ha : 0 < a) : HyperbolicCusp where
  torusMetric := scaleMetric (a ^ 2) (sq_pos_of_pos ha) standardCuspTorusMetric
  torus_flat p v w := by
    rw [Geometry.Curvature.metricRmStandard_scale, standardCuspTorusMetric_flat, mul_zero]
  metric := (scaleMetric (a ^ 2) (sq_pos_of_pos ha)
    standardCuspTorusMetric).exponentialWarpedEnd (1 / 2)
  metric_formula p v w := by
    rw [SmoothRiemannianMetric.exponentialWarpedEnd_inner]
    congr 2
    ring_nf

theorem doubleCuspCollar_inner (a : ℝ) (ha : 0 < a) (i : Fin 2) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) (v w : TangentSpace halfCollarModel p) :
    localPullInner (doubleCuspMetric.{u} a ha) (doubleCuspCollar.{u} i) p v w =
      (doubleCuspReference a ha).metric.inner p v w := by
  rw [localPullInner_apply, doubleCuspMetric]
  erw [SmoothRiemannianMetric.pullback_inner, doubleCuspCoordinate_collar_derivative i hp,
    doubleCuspCoordinate_collar_derivative i hp, doubleCuspCoordinate_collar i hp]
  rw [(doubleCuspReference a ha).metric_formula]
  erw [doubleCuspRealMetric, SmoothRiemannianMetric.warpedProduct_inner,
    DifferentialGeometry.euclideanMetric_inner]
  change _ + doubleCuspWarp a (if i = 0 then p.2.val 0 else 240 - p.2.val 0) ^ 2 *
    standardCuspTorusMetric.inner p.1 v.1 w.1 = _
  have hl : doubleCuspLogProfile (if i = 0 then p.2.val 0 else 240 - p.2.val 0) =
      -p.2.val 0 / 2 := by
    change p.2.val 0 < 100 at hp
    split_ifs
    · exact doubleCuspLogProfile_left (by linarith)
    · rw [doubleCuspLogProfile_right (by linarith)]
      ring
  have he : Real.exp (-p.2.val 0 / 2) ^ 2 = Real.exp (-p.2.val 0) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [doubleCuspWarp, hl, mul_pow, he]
  change (if i = 0 then w.2 0 else -w.2 0) *
      (if i = 0 then v.2 0 else -v.2 0) +
      a ^ 2 * Real.exp (-p.2.val 0) * standardCuspTorusMetric.inner p.1 v.1 w.1 =
    v.2 0 * w.2 0 + Real.exp (-p.2.val 0) *
      (a ^ 2 * standardCuspTorusMetric.inner p.1 v.1 w.1)
  split_ifs <;> ring

def doubleCuspBoundary (i : Fin 2) : Set (productSet.{u} 2) :=
  torusMonodromyEnd.{u} (if i = 0 then 0 else 1)

theorem doubleCuspCollar_boundary_image (i : Fin 2) :
    Set.range (fun t : Torus => doubleCuspCollar.{u} i (t, halfZero)) =
      doubleCuspBoundary.{u} i := by
  have hz : doubleCuspInterval i halfZero = (if i = 0 then 0 else 1) := by
    apply Subtype.ext
    rw [doubleCuspInterval_val i (by change (0 : ℝ) < 100; norm_num)]
    split_ifs <;> norm_num [halfZero, halfPoint]
  ext x
  change (∃ t, torusMonodromyPolarDiffeomorph.{u}.symm
    (t, doubleCuspInterval i halfZero) = x) ↔
      (torusMonodromyPolarDiffeomorph.{u} x).2 = (if i = 0 then 0 else 1)
  rw [hz]
  constructor
  · rintro ⟨t, rfl⟩
    rw [Diffeomorph.apply_symm_apply]
  · intro hx
    have hh : ((torusMonodromyPolarDiffeomorph.{u} x).1, if i = 0 then 0 else 1) =
        torusMonodromyPolarDiffeomorph.{u} x := Prod.ext rfl hx.symm
    exact ⟨(torusMonodromyPolarDiffeomorph.{u} x).1,
      (congrArg torusMonodromyPolarDiffeomorph.{u}.symm hh).trans
        (torusMonodromyPolarDiffeomorph.{u}.symm_apply_apply x)⟩

theorem doubleCuspCollar_boundary_preimage {i : Fin 2} {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) :
    (doubleCuspCollar.{u} i p ∈ (𝓡∂ 3).boundary (productSet.{u} 2) ↔ p.2.val 0 = 0) := by
  rw [torusMonodromyGluing_boundary (Diffeomorph.refl torusModel Torus ∞)]
  change (doubleCuspCollar.{u} i p ∈
    ⋃ j : Fin 1, (torusMonodromyEnd.{u} 1 ∪ torusMonodromyEnd.{u} 0)) ↔ _
  simp only [Set.mem_iUnion, Fin.exists_fin_one]
  change ((torusMonodromyPolarDiffeomorph.{u} (doubleCuspCollar.{u} i p)).2 = 1 ∨
    (torusMonodromyPolarDiffeomorph.{u} (doubleCuspCollar.{u} i p)).2 = 0) ↔ _
  simp only [doubleCuspCollar, Diffeomorph.apply_symm_apply]
  have hv := doubleCuspInterval_val i hp
  change p.2.val 0 < 100 at hp
  by_cases hi : i = 0
  · have hv0 : (doubleCuspInterval i p.2).val = p.2.val 0 / 240 := by
      rw [hv]
      simp only [hi, ite_true]
    have hn : doubleCuspInterval i p.2 ≠ 1 := by
      intro h
      have hh := congrArg Subtype.val h
      change (doubleCuspInterval i p.2).val = 1 at hh
      rw [hv0] at hh
      linarith
    simp only [hn, false_or]
    rw [Subtype.ext_iff]
    change (doubleCuspInterval i p.2).val = 0 ↔ _
    rw [hv0]
    constructor <;> intro h <;> linarith
  · have hv0 : (doubleCuspInterval i p.2).val = 1 - p.2.val 0 / 240 := by
      rw [hv]
      simp only [hi, ite_false]
    have hn : doubleCuspInterval i p.2 ≠ 0 := by
      intro h
      have hh := congrArg Subtype.val h
      change (doubleCuspInterval i p.2).val = 0 at hh
      rw [hv0] at hh
      linarith
    simp only [hn, or_false]
    rw [Subtype.ext_iff]
    change (doubleCuspInterval i p.2).val = 1 ↔ _
    rw [hv0]
    constructor <;> intro h <;> linarith

private theorem doubleCusp_nabla_zero_on_open
    (g : SmoothRiemannianMetric halfCollarModel CuspHalfSpace) (s : ℕ)
    (T : (p : CuspHalfSpace) → Tensor0SSpace s halfCollarModel p)
    {U : Set CuspHalfSpace} (hU : IsOpen U) (hT : ∀ p ∈ U, T p = 0)
    {p : CuspHalfSpace} (hp : p ∈ U) : metricCovariantDerivative g s T p = 0 := by
  let tensorTopology := tensor0SBundleTopology (𝕜 := ℝ) (I := halfCollarModel)
    (M := CuspHalfSpace) (s + 1)
  have he : tensor0SModelInChart (I := halfCollarModel) s p T =ᶠ[
      𝓝 (extChartAt halfCollarModel p p)] (fun y => 0) := by
    have hu : ∀ᶠ y in 𝓝 (extChartAt halfCollarModel p p),
        (extChartAt halfCollarModel p).symm y ∈ U := by
      apply (continuousAt_extChartAt_symm p).eventually
      change U ∈ 𝓝 ((extChartAt halfCollarModel p).symm
        (extChartAt halfCollarModel p p))
      rw [extChartAt_to_inv]
      exact hU.mem_nhds hp
    filter_upwards [hu] with y hy
    ext slots
    rw [tensor0SModelInChart_apply, hT _ hy]
    rfl
  have hd : fderivWithin ℝ (tensor0SModelInChart (I := halfCollarModel) s p T)
      (range halfCollarModel) (extChartAt halfCollarModel p p) = 0 := by
    rw [he.fderivWithin_eq_of_nhds]
    erw [fderivWithin_const]
    rfl
  have h0 : tensor0SModelAt (I := halfCollarModel) s p p (T p) = 0 := by
    ext slots
    rw [tensor0SModelAt_apply, hT p hp]
    rfl
  have hz : ∀ Γ, totalCovDerivTensor0SModelAt (𝕜 := ℝ)
      (E := (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1)) s 0 Γ 0 = 0 := by
    intro Γ
    ext slots
    have hslot : slots = Fin.cons (slots 0) (fun j => slots j.succ) := by
      exact (Fin.cons_self_tail slots).symm
    rw [hslot, totalCovDeriv_tensor0SModelAt_apply_cons]
    simp [covariantDerivTensor0SModelAt, lieDerivCorrection, substituteArg]
  unfold metricCovariantDerivative
  rw [hd, h0, hz]
  let e := trivializationAt (Tensor0SModel (s + 1) ℝ
    ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)))
    (fun q : CuspHalfSpace => Tensor0SSpace (s + 1) halfCollarModel q) p
  change e.symm p 0 = 0
  have hb : p ∈ e.baseSet := mem_baseSet_trivializationAt
    (Tensor0SModel (s + 1) ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)))
    (fun q : CuspHalfSpace => Tensor0SSpace (s + 1) halfCollarModel q) p
  rw [← e.symmL_apply (R := ℝ) hb]
  exact map_zero _

private theorem doubleCusp_iterated_zero_on_open
    (g : SmoothRiemannianMetric halfCollarModel CuspHalfSpace) (s : ℕ)
    (T : (p : CuspHalfSpace) → Tensor0SSpace s halfCollarModel p)
    {U : Set CuspHalfSpace} (hU : IsOpen U) (hT : ∀ p ∈ U, T p = 0) (k : ℕ) :
    ∀ p ∈ U, iteratedMetricCovariantDerivative g s T k p = 0 := by
  induction k with
  | zero => exact hT
  | succ k hk =>
    intro p hp
    exact doubleCusp_nabla_zero_on_open g (s + k)
      (iteratedMetricCovariantDerivative g s T k) hU hk hp

theorem doubleCuspMetricError_zero (a : ℝ) (ha : 0 < a) (i : Fin 2)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    cuspMetricError (W := annulusCircleCarrier.{u}) (doubleCuspMetric.{u} a ha)
      (doubleCuspReference a ha) (doubleCuspCollar.{u} i) p = 0 := by
  unfold cuspMetricError
  ext v
  change localPullInner (doubleCuspMetric.{u} a ha) (doubleCuspCollar.{u} i)
    p (v 0) (v 1) - (doubleCuspReference a ha).metric.inner p (v 0) (v 1) = 0
  rw [doubleCuspCollar_inner a ha i hp, sub_self]

theorem doubleCuspMetricError_iterated_zero (a : ℝ) (ha : 0 < a) (i : Fin 2)
    (k : ℕ) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    iteratedMetricCovariantDerivative (doubleCuspReference a ha).metric 2
      (cuspMetricError (W := annulusCircleCarrier.{u}) (doubleCuspMetric.{u} a ha)
        (doubleCuspReference a ha) (doubleCuspCollar.{u} i)) k p = 0 :=
  doubleCusp_iterated_zero_on_open (doubleCuspReference a ha).metric 2
    (cuspMetricError (W := annulusCircleCarrier.{u}) (doubleCuspMetric.{u} a ha)
      (doubleCuspReference a ha) (doubleCuspCollar.{u} i)) doubleCuspDomain_open
    (fun q hq => show cuspMetricError (W := annulusCircleCarrier.{u})
      (doubleCuspMetric.{u} a ha) (doubleCuspReference a ha)
      (doubleCuspCollar.{u} i) q = 0 from doubleCuspMetricError_zero a ha i hq) k p hp

def doubleCuspEmbedding (a : ℝ) (ha : 0 < a) (K : ℕ) (i : Fin 2) :
    CuspEmbedding annulusCircleCarrier.{u} (doubleCuspMetric.{u} a ha) K 0
      (doubleCuspBoundary.{u} i) where
  cusp := doubleCuspReference a ha
  toFun := doubleCuspCollar.{u} i
  contMDiffOn := (doubleCuspCollar_smooth.{u} i).of_le (by simp)
  isEmbedding := doubleCuspCollar_embedding.{u} i
  immersion p hp := doubleCuspCollar_immersion.{u} i hp
  boundary_image := doubleCuspCollar_boundary_image.{u} i
  boundary_preimage := doubleCuspCollar_boundary_preimage.{u} (i := i)
  metric_error k hk p hp := by
    rw [doubleCuspMetricError_iterated_zero a ha i k hp]
    simp [tensor0SFiberNorm, normSq0S, inner0S, MetricFiberData.inner]

theorem doubleCuspEmbedding_torusMetric (a : ℝ) (ha : 0 < a) (K : ℕ) (i : Fin 2) :
    (doubleCuspEmbedding.{u} a ha K i).cusp.torusMetric =
      scaleMetric (a ^ 2) (sq_pos_of_pos ha) standardCuspTorusMetric := rfl

theorem doubleCuspEmbedding_apply (a : ℝ) (ha : 0 < a) (K : ℕ) (i : Fin 2)
    (p : CuspHalfSpace) : (doubleCuspEmbedding.{u} a ha K i).toFun p =
      torusMonodromyPolarDiffeomorph.{u}.symm (p.1, doubleCuspInterval i p.2) := rfl

theorem doubleCuspBoundary_connected (i : Fin 2) : IsConnected (doubleCuspBoundary.{u} i) := by
  apply isConnected_iff_connectedSpace.mpr
  exact (torusMonodromyEndParam.{u} (if i = 0 then 0 else 1)).connectedSpace_iff.mp
    inferInstance

theorem doubleCuspBoundary_closed (i : Fin 2) : IsClosed (doubleCuspBoundary.{u} i) := by
  change IsClosed {x : productSet.{u} 2 |
    (torusMonodromyPolarDiffeomorph x).2 = if i = 0 then 0 else 1}
  exact isClosed_eq (continuous_snd.comp torusMonodromyPolarDiffeomorph.continuous)
    continuous_const

theorem doubleCuspBoundary_disjoint : Pairwise
    (fun i j : Fin 2 => Disjoint (doubleCuspBoundary.{u} i) (doubleCuspBoundary.{u} j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh : (if i = 0 then (0 : unitInterval) else 1) = if j = 0 then 0 else 1 :=
    hx.symm.trans hy
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact hij rfl
  · have hh' := congrArg Subtype.val hh
    norm_num at hh'
  · have hh' := congrArg Subtype.val hh
    norm_num at hh'
  · exact hij rfl

theorem doubleCuspBoundary_cover :
    ⋃ i, doubleCuspBoundary.{u} i = (𝓡∂ 3).boundary (productSet.{u} 2) :=
  cuspTruncationBoundaryComponent_cover.{u}

end DifferentialGeometry.Geometry.Collapse
