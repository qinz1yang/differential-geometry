import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseProfile
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionMetric
import DifferentialGeometry.Geometry.Metric.ChartLipschitz.DistanceComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.MetricSpace.Lipschitz
import DifferentialGeometry.Geometry.Metric.PolarCoordinates

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev EC := EuclideanSpace ℝ (Fin 2) × ℝ
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def collapseMapAmbient (A : ℝ) (q : S2 × ℝ) : E3 :=
  max 0 (collapseRadius A q.2) • (q.1 : E3)

theorem collapseMapAmbient_norm (A : ℝ) (q : S2 × ℝ) :
    ‖collapseMapAmbient A q‖ = max 0 (collapseRadius A q.2) := by
  simp only [collapseMapAmbient, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere,
    mul_one, abs_of_nonneg (le_max_left (0 : ℝ) (collapseRadius A q.2))]

private theorem continuous_collapseMapAmbient (A : ℝ) : Continuous (collapseMapAmbient A) :=
  (continuous_const.max ((contDiff_collapseRadius A).continuous.comp continuous_snd)).smul
    (continuous_subtype_val.comp continuous_fst)

private theorem collapseMapAmbient_mem {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B) : collapseMapAmbient A q.val ∈ insertionBall B := by
  change ‖collapseMapAmbient A q.val‖ < transitionEnd + B
  rw [collapseMapAmbient_norm]
  have hB : 0 < B := by linarith
  apply max_lt
  · linarith [transitionEnd_pos]
  · by_cases hz : q.val.2 ≤ 0
    · have h := monotone_collapseRadius A hz
      rw [collapseRadius_zero hA] at h
      linarith
    · rw [collapseRadius_eq_conformalRadius (by linarith),
        conformalRadius_cylindrical (not_le.mp hz).le]
      linarith [q.property.2]

def collapseMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    DifferentialGeometry.Geometry.Neck.openCylinder B → insertionBall B :=
  fun q => ⟨collapseMapAmbient A q.val, collapseMapAmbient_mem hA hAB q⟩

theorem collapseMap_apply {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B) :
    (collapseMap hA hAB q : E3) = max 0 (collapseRadius A q.val.2) • (q.val.1 : E3) := rfl

theorem continuous_collapseMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    Continuous (collapseMap hA hAB) :=
  ((continuous_collapseMapAmbient A).comp continuous_subtype_val).subtype_mk _

theorem collapseMap_collapsed {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B) (hq : q.val.2 ≤ collapseTip A) :
    (collapseMap hA hAB q : E3) = 0 := by
  have hr := monotone_collapseRadius A hq
  rw [collapseRadius_tip] at hr
  rw [collapseMap_apply, max_eq_left hr, zero_smul]

theorem collapseMap_ne_zero_of_tip_lt {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B) (hq : collapseTip A < q.val.2) :
    (collapseMap hA hAB q : E3) ≠ 0 := by
  intro heq
  have hn := congrArg norm heq
  change ‖collapseMapAmbient A q.val‖ = ‖(0 : E3)‖ at hn
  rw [collapseMapAmbient_norm, max_eq_right (collapseRadius_pos_iff.mpr hq).le,
    norm_zero] at hn
  exact (collapseRadius_pos_iff.mpr hq).ne' hn

theorem collapseMap_radial {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B) (hq : collapseTip A ≤ q.val.2) :
    (collapseMap hA hAB q : E3) = collapseRadius A q.val.2 • (q.val.1 : E3) := by
  have hr := monotone_collapseRadius A hq
  rw [collapseRadius_tip] at hr
  rw [collapseMap_apply, max_eq_right hr]

theorem collapseMap_retained {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B) (hq : 0 ≤ q.val.2) :
    (collapseMap hA hAB q : E3) = (transitionEnd + q.val.2) • (q.val.1 : E3) := by
  rw [collapseMap_apply, collapseRadius_eq_conformalRadius (by linarith),
    max_eq_right (conformalRadius_pos _).le, conformalRadius_cylindrical hq]

theorem insertionCylinder_le_openCylinder {A B : ℝ} (hAB : 2 * A < B) :
    insertionCylinder A B ≤ DifferentialGeometry.Geometry.Neck.openCylinder B := by
  intro q hq
  constructor <;> linarith [hq.1, hq.2]

theorem collapseMap_insertionMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : insertionCylinder A B) :
    collapseMap hA hAB (Opens.inclusion (insertionCylinder_le_openCylinder hAB) q) =
      insertionMap hA hAB q := by
  apply Subtype.ext
  rw [collapseMap_apply, insertionMap_apply]
  change max 0 (collapseRadius A q.val.2) • (q.val.1 : E3) = conformalMap q.val
  rw [collapseRadius_eq_conformalRadius q.property.1.le,
    max_eq_right (conformalRadius_pos _).le]
  rfl

theorem contMDiffAt_collapseMap_of_height_ne {A B : ℝ} (hA : 0 < A)
    (hAB : 2 * A < B) (q : DifferentialGeometry.Geometry.Neck.openCylinder B)
    (hq : q.val.2 ≠ collapseTip A) :
    ContMDiffAt IC (𝓡 3) ∞ (collapseMap hA hAB) q := by
  apply codRestr_contMDiffAt (fun u => collapseMapAmbient_mem hA hAB u)
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · have heq : (fun u : DifferentialGeometry.Geometry.Neck.openCylinder B => collapseMapAmbient A u.val)
        =ᶠ[𝓝 q] (fun _ => (0 : E3)) := by
      filter_upwards [((continuous_snd.comp continuous_subtype_val).continuousAt
        (Iio_mem_nhds hlt))] with u hu
      exact collapseMap_collapsed hA hAB u hu.le
    exact heq.contMDiffAt_iff.mpr contMDiffAt_const
  · have hs : ContMDiff IC (𝓡 3) ∞
        (fun u : DifferentialGeometry.Geometry.Neck.openCylinder B =>
          collapseRadius A u.val.2 • (u.val.1 : E3)) :=
      ((contDiff_collapseRadius A).contMDiff.comp
        (contMDiff_snd.comp (contMDiff_subtype_val (U := DifferentialGeometry.Geometry.Neck.openCylinder B)))).smul
        ((contMDiff_coe_sphere (n := 2)).comp
          (contMDiff_fst.comp (contMDiff_subtype_val (U := DifferentialGeometry.Geometry.Neck.openCylinder B))))
    have heq : (fun u : DifferentialGeometry.Geometry.Neck.openCylinder B => collapseMapAmbient A u.val)
        =ᶠ[𝓝 q] (fun u => collapseRadius A u.val.2 • (u.val.1 : E3)) := by
      filter_upwards [((continuous_snd.comp continuous_subtype_val).continuousAt
        (Ioi_mem_nhds hgt))] with u hu
      exact collapseMap_radial hA hAB u hu.le
    exact heq.contMDiffAt_iff.mpr hs.contMDiffAt

theorem collapseMap_mfderiv_of_height_lt {A B : ℝ} (hA : 0 < A)
    (hAB : 2 * A < B) (q : DifferentialGeometry.Geometry.Neck.openCylinder B)
    (hq : q.val.2 < collapseTip A) :
    mfderiv IC (𝓡 3) (collapseMap hA hAB) q = 0 := by
  have heq : collapseMap hA hAB =ᶠ[𝓝 q] (fun _ => collapseMap hA hAB q) := by
    filter_upwards [((continuous_snd.comp continuous_subtype_val).continuousAt
      (Iio_mem_nhds hq))] with u hu
    apply Subtype.ext
    rw [collapseMap_collapsed hA hAB u hu.le, collapseMap_collapsed hA hAB q hq.le]
  rw [heq.mfderiv_eq (I := IC) (I' := 𝓡 3), mfderiv_const]

private def smoothRadialMap (A : ℝ) (q : S2 × ℝ) : E3 :=
  collapseRadius A q.2 • (q.1 : E3)

private theorem smooth_smoothRadialMap (A : ℝ) : ContMDiff IC (𝓡 3) ∞ (smoothRadialMap A) :=
  ((contDiff_collapseRadius A).contMDiff.comp contMDiff_snd).smul
    ((contMDiff_coe_sphere (n := 2)).comp contMDiff_fst)

private theorem profile_mfderiv (A z t : ℝ) :
    mfderiv 𝓘(ℝ) 𝓘(ℝ) (collapseRadius A) z t = deriv (collapseRadius A) z * t := by
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ (collapseRadius A) z t = _
  rw [((contDiff_collapseRadius A).differentiable (by simp) z).hasDerivAt.hasFDerivAt.fderiv]
  change t * deriv (collapseRadius A) z = deriv (collapseRadius A) z * t
  exact mul_comm _ _

private theorem radial_product_mfderiv (A : ℝ) (q : S2 × ℝ) (v : TangentSpace IC q) :
    mfderiv IC IC (Prod.map (id : S2 → S2) (collapseRadius A)) q v =
      (v.1, deriv (collapseRadius A) q.2 * v.2) := by
  have h := congrArg (fun D => D v) (mfderiv_prodMap (I := 𝓡 2) (I' := 𝓘(ℝ))
    (J := 𝓡 2) (J' := 𝓘(ℝ)) (f := id) (g := collapseRadius A)
    mdifferentiableAt_id
    ((contDiff_collapseRadius A).contMDiff.mdifferentiable (by decide) q.2))
  rw [mfderiv_id] at h
  change mfderiv IC IC (Prod.map (id : S2 → S2) (collapseRadius A)) q v =
    (v.1, mfderiv 𝓘(ℝ) 𝓘(ℝ) (collapseRadius A) q.2 v.2) at h
  exact h.trans (congrArg (fun t : ℝ => (v.1, t)) (profile_mfderiv A q.2 v.2))

private theorem smoothRadialMap_mfderiv (A : ℝ) (q : S2 × ℝ) (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (smoothRadialMap A) q v =
      (deriv (collapseRadius A) q.2 * v.2) • (q.1 : E3) +
        collapseRadius A q.2 • DifferentialGeometry.Geometry.dIncl (n := 2) q.1 v.1 := by
  have hprod : MDifferentiableAt IC IC (Prod.map (id : S2 → S2) (collapseRadius A)) q :=
    mdifferentiableAt_id.prodMap
      ((contDiff_collapseRadius A).contMDiff.mdifferentiable (by decide) q.2)
  have h := congrArg (fun D => D v) (mfderiv_comp (I := IC) (I' := IC) (I'' := 𝓡 3) q
    ((DifferentialGeometry.Geometry.Riemannian.euclideanPolarMap_smooth (E := E3) (n := 2)).mdifferentiable
      (by decide) _) hprod)
  change mfderiv IC (𝓡 3) (smoothRadialMap A) q v =
    mfderiv IC (𝓡 3) DifferentialGeometry.Geometry.Riemannian.euclideanPolarMap
      (q.1, collapseRadius A q.2)
      (mfderiv IC IC (Prod.map (id : S2 → S2) (collapseRadius A)) q v) at h
  rw [radial_product_mfderiv] at h
  exact h.trans (DifferentialGeometry.Geometry.Riemannian.euclideanPolarMap_mfderiv
    (n := 2) (q.1, collapseRadius A q.2) (v.1, deriv (collapseRadius A) q.2 * v.2))

theorem collapseMap_mfderiv_of_tip_lt {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B) (hq : collapseTip A < q.val.2)
    (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (collapseMap hA hAB) q v =
      (deriv (collapseRadius A) q.val.2 * v.2) • (q.val.1 : E3) +
        collapseRadius A q.val.2 • DifferentialGeometry.Geometry.dIncl (n := 2) q.val.1 v.1 := by
  have heq : (fun u : DifferentialGeometry.Geometry.Neck.openCylinder B => collapseMapAmbient A u.val)
      =ᶠ[𝓝 q] (fun u => smoothRadialMap A u.val) := by
    filter_upwards [((continuous_snd.comp continuous_subtype_val).continuousAt
      (Ioi_mem_nhds hq))] with u hu
    exact collapseMap_radial hA hAB u hu.le
  have hinc := congrArg (fun D => D v) (mfderiv_comp q
    ((contMDiff_subtype_val (I := 𝓡 3) (U := insertionBall B) (n := ∞)).mdifferentiable (by decide)
      (collapseMap hA hAB q))
    ((contMDiffAt_collapseMap_of_height_ne hA hAB q hq.ne').mdifferentiableAt (by decide)))
  change mfderiv IC (𝓡 3) (fun u : DifferentialGeometry.Geometry.Neck.openCylinder B =>
      collapseMapAmbient A u.val) q v =
    mfderiv (𝓡 3) (𝓡 3) (Subtype.val : insertionBall B → E3) (collapseMap hA hAB q)
      (mfderiv IC (𝓡 3) (collapseMap hA hAB) q v) at hinc
  rw [mfderiv_subtype_val_apply] at hinc
  have hlocal := congrArg (fun D => D v) (heq.mfderiv_eq (I := IC) (I' := 𝓡 3))
  have hres := congrArg (fun D => D v) (mfderiv_comp q
    ((smooth_smoothRadialMap A).mdifferentiable (by decide) q.val)
    ((contMDiff_subtype_val (I := IC) (U := DifferentialGeometry.Geometry.Neck.openCylinder B) (n := ∞)).mdifferentiable
      (by decide) q))
  change mfderiv IC (𝓡 3) (fun u : DifferentialGeometry.Geometry.Neck.openCylinder B =>
      smoothRadialMap A u.val) q v =
    mfderiv IC (𝓡 3) (smoothRadialMap A) q.val
      (mfderiv IC IC (Subtype.val : DifferentialGeometry.Geometry.Neck.openCylinder B → S2 × ℝ) q v) at hres
  rw [mfderiv_subtype_val_apply] at hres
  exact hinc.symm.trans (hlocal.trans (hres.trans (smoothRadialMap_mfderiv A q.val v)))

section ReverseChart
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [RegularSpace M]
  {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [RegularSpace N]

private theorem local_intrinsic_bound_of_coordinate
    (g : SmoothRiemannianMetric I M) (k : SmoothRiemannianMetric J N)
    (f : M → N) (p : M) (hc : ContinuousAt f p)
    (hcoord : ∃ C : ℝ≥0, ∃ s ∈ 𝓝 (metricChartEuclideanEquiv g p (extChartAt I p p)),
      LipschitzOnWith C (euclideanChartExpression g k f p (f p)) s) :
    ∃ L : ℝ≥0, ∃ t ∈ 𝓝 p, ∀ x ∈ t, ∀ y ∈ t,
      riemannianEDistOf k (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  let A := metricChartEuclideanEquiv g p
  let D := metricChartEuclideanEquiv k (f p)
  let φ := extChartAt I p
  let ψ := extChartAt J (f p)
  obtain ⟨C, s, hs, hC⟩ := hcoord
  obtain ⟨Ug, hpg, hgchart, hgcomp⟩ :=
    exists_open_riemannianEDistOf_comparison g p (K := 2) (by norm_num)
  obtain ⟨Uk, hpk, hkchart, hkcomp⟩ :=
    exists_open_riemannianEDistOf_comparison k (f p) (K := 2) (by norm_num)
  have hg (x : M) (hx : x ∈ Ug) (y : M) (hy : y ∈ Ug) :
      edist (A (φ x)) (A (φ y)) ≤ (2 : ℝ≥0∞) * riemannianEDistOf g x y := by
    rw [edist_metricChartEuclideanEquiv]
    simpa only [ENNReal.ofReal_ofNat] using (hgcomp x hx y hy).1
  have hk (x : N) (hx : x ∈ Uk) (y : N) (hy : y ∈ Uk) :
      riemannianEDistOf k x y ≤ (2 : ℝ≥0∞) * edist (D (ψ x)) (D (ψ y)) := by
    rw [edist_metricChartEuclideanEquiv]
    simpa only [ENNReal.ofReal_ofNat] using (hkcomp x hx y hy).2
  let t := (Ug : Set M) ∩ f ⁻¹' (Uk : Set N) ∩ φ.source ∩ (fun x => A (φ x)) ⁻¹' s
  have hφ : ContinuousAt φ p := (contMDiffAt_extChartAt (I := I) (n := ∞)).continuousAt
  have ht : t ∈ 𝓝 p := inter_mem (inter_mem
    (inter_mem (Ug.isOpen.mem_nhds hpg) (hc.preimage_mem_nhds (Uk.isOpen.mem_nhds hpk)))
    ((isOpen_extChartAt_source (I := I) p).mem_nhds (mem_extChartAt_source p)))
    ((A.continuousAt.comp hφ).preimage_mem_nhds hs)
  refine ⟨4 * C, t, ht, ?_⟩
  intro x hx y hy
  have hCxy : edist (D (ψ (f x))) (D (ψ (f y))) ≤
      (C : ℝ≥0∞) * edist (A (φ x)) (A (φ y)) := by
    have h := hC hx.2 hy.2
    change edist (D (ψ (f (φ.symm (A.symm (A (φ x)))))))
      (D (ψ (f (φ.symm (A.symm (A (φ y))))))) ≤ _ at h
    rwa [A.symm_apply_apply, A.symm_apply_apply, φ.left_inv hx.1.2, φ.left_inv hy.1.2] at h
  calc
    _ ≤ (2 : ℝ≥0∞) * edist (D (ψ (f x))) (D (ψ (f y))) :=
      hk _ hx.1.1.2 _ hy.1.1.2
    _ ≤ (2 : ℝ≥0∞) * ((C : ℝ≥0∞) * edist (A (φ x)) (A (φ y))) :=
      mul_right_mono hCxy
    _ ≤ (2 : ℝ≥0∞) * ((C : ℝ≥0∞) * (2 * riemannianEDistOf g x y)) :=
      mul_right_mono (mul_right_mono (hg _ hx.1.1.1 _ hy.1.1.1))
    _ = ((4 * C : ℝ≥0) : ℝ≥0∞) * riemannianEDistOf g x y := by
      simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
      ring
end ReverseChart

private def ambientClamp (A : ℝ) (q : E3 × ℝ) : E3 :=
  max 0 (collapseRadius A q.2) • q.1

private theorem lipschitz_ambientScalar (A : ℝ) :
    LipschitzWith 1 (fun q : E3 × ℝ => max 0 (collapseRadius A q.2)) := by
  intro x y
  have h := (((lipschitzWith_collapseRadius A).const_max 0).comp
    (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : E3 × ℝ → ℝ))) x y
  simpa only [one_mul, Function.comp_apply] using h

private theorem smooth_scalarMultiplication : ContDiff ℝ 1 (fun q : ℝ × E3 => q.1 • q.2) :=
  contDiff_fst.smul contDiff_snd

private theorem locallyLipschitz_scalarMultiplication :
    LocallyLipschitz (fun q : ℝ × E3 => q.1 • q.2) :=
  smooth_scalarMultiplication.locallyLipschitz

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem locallyLipschitz_ambientClamp (A : ℝ) : LocallyLipschitz (ambientClamp A) := by
  have hpair : LocallyLipschitz (fun q : E3 × ℝ => (max 0 (collapseRadius A q.2), q.1)) :=
    (lipschitz_ambientScalar A).locallyLipschitz.prodMk
      (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : E3 × ℝ → E3)).locallyLipschitz
  change LocallyLipschitz ((fun q : ℝ × E3 => q.1 • q.2) ∘
    fun q : E3 × ℝ => (max 0 (collapseRadius A q.2), q.1))
  exact locallyLipschitz_scalarMultiplication.comp hpair

private def cylinderAmbientInclusion {B : ℝ}
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B) : E3 × ℝ := ((q.val.1 : E3), q.val.2)

private theorem cylinderAmbientInclusion_smooth (B : ℝ) :
    ContMDiff IC 𝓘(ℝ, E3 × ℝ) ∞ (cylinderAmbientInclusion (B := B)) :=
  (((contMDiff_coe_sphere (n := 2)).comp contMDiff_fst).prodMk_space contMDiff_snd).comp
    (contMDiff_subtype_val (U := DifferentialGeometry.Geometry.Neck.openCylinder B))

private theorem euclidean_open_chart (B : ℝ) (p x : insertionBall B) :
    extChartAt (𝓡 3) p x = (x : E3) := by
  simp [extChartAt, TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]

private theorem collapseMap_coordinate_lipschitz {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (g : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (k : SmoothRiemannianMetric (𝓡 3) (insertionBall B))
    (p : DifferentialGeometry.Geometry.Neck.openCylinder B) :
    ∃ C : ℝ≥0, ∃ s ∈ 𝓝 (metricChartEuclideanEquiv g p (extChartAt IC p p)),
      LipschitzOnWith C (euclideanChartExpression g k (collapseMap hA hAB) p
        (collapseMap hA hAB p)) s := by
  let A0 := metricChartEuclideanEquiv g p
  let D := metricChartEuclideanEquiv k (collapseMap hA hAB p)
  let φ := extChartAt IC p
  let center := A0 (φ p)
  let χ := φ.symm ∘ A0.symm
  let e := cylinderAmbientInclusion ∘ χ
  have hφi : ContMDiffAt 𝓘(ℝ, EC) IC ∞ φ.symm (φ p) := by
    simpa only [IC.range_eq_univ, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := IC) (n := ∞) p)
  have hφi' : ContMDiffAt 𝓘(ℝ, EC) IC ∞ φ.symm (A0.symm center) := by
    simpa only [center, ContinuousLinearEquiv.symm_apply_apply] using hφi
  have hχ : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ EC))) IC ∞ χ center :=
    hφi'.comp center A0.symm.contDiff.contMDiff.contMDiffAt
  have he : ContDiffAt ℝ ∞ e center :=
    ((cylinderAmbientInclusion_smooth B).contMDiffAt.comp center hχ).contDiffAt
  obtain ⟨Ce, te, hte, hLe⟩ := (he.of_le (by decide : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).exists_lipschitzOnWith
  obtain ⟨CG, tG, htG, hLG⟩ := locallyLipschitz_ambientClamp A (e center)
  let s := te ∩ e ⁻¹' tG
  have hs : s ∈ 𝓝 center := inter_mem hte (he.continuousAt.preimage_mem_nhds htG)
  have hcomp : LipschitzOnWith (CG * Ce) (ambientClamp A ∘ e) s :=
    hLG.comp (hLe.mono inter_subset_left)
      ((mapsTo_preimage e tG).mono_left inter_subset_right)
  have hD := D.toContinuousLinearMap.lipschitz.comp_lipschitzOnWith hcomp
  refine ⟨‖D.toContinuousLinearMap‖₊ * (CG * Ce), s, hs, ?_⟩
  have heq : euclideanChartExpression g k (collapseMap hA hAB) p
      (collapseMap hA hAB p) = D ∘ ambientClamp A ∘ e := by
    funext z
    change D (extChartAt (𝓡 3) (collapseMap hA hAB p)
      (collapseMap hA hAB (χ z))) = D (ambientClamp A (e z))
    rw [euclidean_open_chart]
    rfl
  rw [heq]
  exact hD

theorem collapseMap_local_intrinsic_bound {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (g : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (k : SmoothRiemannianMetric (𝓡 3) (insertionBall B))
    (p : DifferentialGeometry.Geometry.Neck.openCylinder B) :
    ∃ L : ℝ≥0, ∃ t ∈ 𝓝 p, ∀ x ∈ t, ∀ y ∈ t,
      riemannianEDistOf k (collapseMap hA hAB x) (collapseMap hA hAB y) ≤
        L * riemannianEDistOf g x y :=
  local_intrinsic_bound_of_coordinate g k (collapseMap hA hAB) p
    (continuous_collapseMap hA hAB).continuousAt
    (collapseMap_coordinate_lipschitz hA hAB g k p)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem locallyLipschitz_collapseMap {A B η : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (hη : 0 < η) (g : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    (let cg := g.toContinuousRiemannianMetric
     letI : RiemannianBundle (TangentSpace IC : DifferentialGeometry.Geometry.Neck.openCylinder B → Type _) :=
       ⟨cg.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle EC
       (TangentSpace IC : DifferentialGeometry.Geometry.Neck.openCylinder B → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace (DifferentialGeometry.Geometry.Neck.openCylinder B) :=
       .ofRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)
     let k := insertedMetric hA hAB hη g
     let ck := k.toContinuousRiemannianMetric
     letI : RiemannianBundle (TangentSpace (𝓡 3) : insertionBall B → Type _) :=
       ⟨ck.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall B → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace (insertionBall B) := .ofRiemannianMetric (𝓡 3) (insertionBall B)
     LocallyLipschitz (collapseMap hA hAB)) :=
  (locallyLipschitz_iff_local_riemannianEDistOf_le g (insertedMetric hA hAB hη g)
    (collapseMap hA hAB)).mpr (collapseMap_local_intrinsic_bound hA hAB g _)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
