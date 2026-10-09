import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspTaylorPatch
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFiniteBoundary
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryInverse
import DifferentialGeometry.Geometry.Curvature.FiniteJetTransferInterior
import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalOperatorBound
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Algebraic.SectionalLowerBound
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

/-!
# Curvature of a nearly cuspidal collar (FT, finite second-order binding)

For a cusp embedding `e : CuspEmbedding W g K δ X` with `K ≥ 2` and `δ ≤ 1/2`, the curvature of
`g` on the collar is `Cδ`-close to the model value `-1/4`, with the explicit constant
`C = 360 + 81/2` (`cusp_metricRm04StandardAt_near_model`; at positive height by jet replacement
through a Taylor patch, at height zero by continuity). For `0 ≤ δ ≤ 1/6408` this gives the
sectional pinching `-1/2 ≤ sec_g ≤ -1/8` on every plane at every point of the collar
(`cusp_sectional_pinching`), in the shape consumed by `G_consumer_clauses_of_pinching`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter TopologicalSpace Function
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.TensorLieDeriv
open GC.Endpoint
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "Ec" => (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)

private theorem cuspCurv_finrank : (Module.finrank ℝ Ec : ℝ) = 3 := by
  simp [Module.finrank_prod]

private theorem cuspCurv_point_congr {W : CompactCarrier.{u}}
    (g : SmoothRiemannianMetric W.model W.Carrier) {y y' : W.Carrier} (h : y = y')
    (a b : EuclideanSpace ℝ (Fin 3)) :
    metricRm04StandardAt g y a b b a = metricRm04StandardAt g y' a b b a := by
  subst h
  rfl

/-- The model cusp metric restricted to an open set of interior points: the Riemann operator is
bounded by `81/2` (constant curvature `-1/4`, dimension `3`). -/
private theorem cuspCurv_hmodel (Hc : HyperbolicCusp) (P : Opens CuspHalfSpace) [T2Space P]
    [BoundarylessManifold halfCollarModel P] (x : P) (u v w : TangentSpace halfCollarModel x) :
    let r := riemannOp (LeviCivita (Hc.metric.restrictOpen P)) x u v w
    Real.sqrt ((Hc.metric.restrictOpen P).inner x r r) ≤
      (81 / 2 : ℝ) * Real.sqrt ((Hc.metric.restrictOpen P).inner x u u) *
        Real.sqrt ((Hc.metric.restrictOpen P).inner x v v) *
        Real.sqrt ((Hc.metric.restrictOpen P).inner x w w) := by
  let : T2Space (EuclideanHalfSpace 1) := by
    unfold EuclideanHalfSpace
    infer_instance
  have hk : ∀ a b : TangentSpace halfCollarModel x,
      |metricRm04StandardAt (Hc.metric.restrictOpen P) x a b b a| ≤
        (1 / 4 : ℝ) * (Hc.metric.restrictOpen P).inner x a a *
          (Hc.metric.restrictOpen P).inner x b b := by
    intro a b
    rw [metricRm04StandardAt_restrictOpen]
    simp only [DifferentialGeometry.mfderiv_subtype_val_apply]
    have hc : metricRm04StandardAt Hc.metric (x : CuspHalfSpace) a b b a =
        -(1 / 4 : ℝ) * (Hc.metric.inner (x : CuspHalfSpace) a a *
          Hc.metric.inner (x : CuspHalfSpace) b b - Hc.metric.inner (x : CuspHalfSpace) a b ^ 2) :=
      cusp_constant_sectional_curvature Hc (x : CuspHalfSpace) a b
    have hinner (a' b' : TangentSpace halfCollarModel x) :
        (Hc.metric.restrictOpen P).inner x a' b' = Hc.metric.inner x a' b' := rfl
    have haa := hinner a a
    have hbb := hinner b b
    have hcs := Riemannian.gInner_sq_le_mul Hc.metric (x : CuspHalfSpace) a b
    have hsq := sq_nonneg (Hc.metric.inner (x : CuspHalfSpace) a b)
    rw [abs_le, haa, hbb]
    constructor <;> linarith
  have h := sqrt_inner_riemannOp_le_of_abs_sectional_le (Hc.metric.restrictOpen P) x
    (by norm_num : (0 : ℝ) ≤ 1 / 4) hk u v w
  rw [cuspCurv_finrank] at h
  convert h using 4
  norm_num

/-- **FT at positive height (G2.b, interior).** At a point of positive height of a cusp collar
with `K ≥ 2` and `δ ≤ 1/2`, the curvature numerator of `g` on the image of a plane differs from
the model value `-1/4 · gram` by at most `(360 + 81/2) δ |v|² |w|²`. -/
theorem CuspEmbedding.abs_metricRm04StandardAt_add_quarter_le_of_height_pos
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    {X : Set W.Carrier} (e : CuspEmbedding W g K δ X) (hK : 2 ≤ K) (hδ : δ ≤ 1 / 2)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (hz : 0 < p.2.val 0)
    (v w : TangentSpace halfCollarModel p) :
    |metricRm04StandardAt g (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p w)
        (mfderiv halfCollarModel W.model e.toFun p w)
        (mfderiv halfCollarModel W.model e.toFun p v) +
      (1 / 4 : ℝ) * (e.cusp.metric.inner p v v * e.cusp.metric.inner p w w -
        (e.cusp.metric.inner p v w) ^ 2)| ≤
    (360 + 81 / 2 : ℝ) * δ * e.cusp.metric.inner p v v * e.cusp.metric.inner p w w := by
  obtain ⟨P, f, hpP, hPint, hloc, hfp, hmf, hTe, hTf, h0, h1, h2⟩ :=
    e.exists_taylorPatch hK hp hz
  let : T2Space (EuclideanHalfSpace 1) := by
    unfold EuclideanHalfSpace
    infer_instance
  let : T2Space P := inferInstance
  let : BoundarylessManifold halfCollarModel P :=
    ⟨fun x => halfCollarModel.isInteriorPoint_iff_isInteriorPoint_val.mpr (hPint x.property)⟩
  have hlocP : IsLocalDiffeomorph halfCollarModel W.model ∞ (fun x : P => f x) :=
    isLocalDiffeomorph_restrict_open P hloc
  let g' := localPullMetric g (fun x : P => f x) hlocP
  let x : P := ⟨p, hpP⟩
  have hpI : halfCollarModel.IsInteriorPoint (x : CuspHalfSpace) :=
    cusp_isInteriorPoint_of_height_pos hz
  have hg' : ∀ z : P, finiteMetricDifference g' (e.cusp.metric.restrictOpen P) z =
      Tensor0SSpace.ofModel (I := halfCollarModel) (x := z)
        (Tensor0SSpace.toModel (cuspMetricError g e.cusp f (z : CuspHalfSpace))) := by
    intro z
    ext m
    rw [finiteMetricDifference_apply, localPullMetric_inner, mfderiv_restrict_open]
    rfl
  have hsmall : ∀ k : ℕ, k ≤ 2 → tensor0SFiberNorm e.cusp.metric (x : CuspHalfSpace) (2 + k)
      (iteratedMetricCovariantDerivative e.cusp.metric 2 (cuspMetricError g e.cusp e.toFun) k
        (x : CuspHalfSpace)) ≤ δ :=
    fun k hk => e.metric_error k (hk.trans hK) p hp
  have hT := abs_metricRm04_sub_le_of_chart_jet_replacement_interior e.cusp.metric P g'
    (cuspMetricError g e.cusp e.toFun) (cuspMetricError g e.cusp f) x hδ hsmall hpI hTe hTf
    h0 h1 h2 hg' (cuspCurv_hmodel e.cusp P x) v w
  have hnat : metricRm04StandardAt g' x v w w v =
      metricRm04StandardAt g (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p w)
        (mfderiv halfCollarModel W.model e.toFun p w)
        (mfderiv halfCollarModel W.model e.toFun p v) := by
    refine (metricRm04StandardAt_localPullMetric g (fun x : P => f x) hlocP x v w w v).trans ?_
    have hd : mfderiv halfCollarModel W.model (fun y : P => f y) x =
        mfderiv halfCollarModel W.model e.toFun p :=
      (mfderiv_restrict_open f P x).trans hmf
    rw [hd]
    exact cuspCurv_point_congr g hfp _ _
  rw [hnat, cusp_constant_sectional_curvature] at hT
  have heq : metricRm04StandardAt g (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p w)
        (mfderiv halfCollarModel W.model e.toFun p w)
        (mfderiv halfCollarModel W.model e.toFun p v) +
      (1 / 4 : ℝ) * (e.cusp.metric.inner p v v * e.cusp.metric.inner p w w -
        (e.cusp.metric.inner p v w) ^ 2) =
      metricRm04StandardAt g (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p w)
        (mfderiv halfCollarModel W.model e.toFun p w)
        (mfderiv halfCollarModel W.model e.toFun p v) -
      -(1 / 4 : ℝ) * (e.cusp.metric.inner p v v * e.cusp.metric.inner p w w -
        e.cusp.metric.inner p v w ^ 2) := by ring
  rw [heq]
  refine hT.trans (le_of_eq ?_)
  ring

/-- **FT on the whole collar (G2.b).** For `K ≥ 2` and `δ ≤ 1/2` the estimate holds at every
point of the cusp domain, height zero included (continuity, `CuspFiniteBoundary`). -/
theorem CuspEmbedding.abs_metricRm04StandardAt_add_quarter_le
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    {X : Set W.Carrier} (e : CuspEmbedding W g K δ X) (hK : 2 ≤ K) (hδ : δ ≤ 1 / 2)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (v w : TangentSpace halfCollarModel p) :
    |metricRm04StandardAt g (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p w)
        (mfderiv halfCollarModel W.model e.toFun p w)
        (mfderiv halfCollarModel W.model e.toFun p v) +
      (1 / 4 : ℝ) * (e.cusp.metric.inner p v v * e.cusp.metric.inner p w w -
        (e.cusp.metric.inner p v w) ^ 2)| ≤
    (360 + 81 / 2 : ℝ) * δ * e.cusp.metric.inner p v v * e.cusp.metric.inner p w w :=
  cusp_metricRm04StandardAt_near_model_boundary (360 + 81 / 2) W g K δ X hK e
    (fun _ hq hz => e.abs_metricRm04StandardAt_add_quarter_le_of_height_pos hK hδ hq hz) p hp v w

/-- **FT, frozen final form (interior of the collar).** One constant `C = 360 + 81/2` for all
carriers, metrics, orders `K ≥ 2` and errors `δ ≤ 1/2`. -/
theorem cusp_metricRm04StandardAt_near_model :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
      (K : ℕ) (δ : ℝ) (X : Set W.Carrier), 2 ≤ K → δ ≤ 1 / 2 →
      ∀ (e : CuspEmbedding W g K δ X) (p : CuspHalfSpace), p ∈ cuspDomain → 0 < p.2.val 0 →
      ∀ v w : TangentSpace halfCollarModel p,
        |metricRm04StandardAt g (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
            (mfderiv halfCollarModel W.model e.toFun p w)
            (mfderiv halfCollarModel W.model e.toFun p w)
            (mfderiv halfCollarModel W.model e.toFun p v) +
          (1 / 4 : ℝ) * (e.cusp.metric.inner p v v * e.cusp.metric.inner p w w -
            (e.cusp.metric.inner p v w) ^ 2)| ≤
        C * δ * e.cusp.metric.inner p v v * e.cusp.metric.inner p w w :=
  ⟨360 + 81 / 2, by norm_num, fun _ _ _ _ _ hK hδ e _ hp hz v w =>
    e.abs_metricRm04StandardAt_add_quarter_le_of_height_pos hK hδ hp hz v w⟩

private theorem cuspCurv_lower_alg {α β x y z R δ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 6408) (hx : (1 - δ) * α ≤ x) (hy : (1 - δ) * β ≤ y)
    (hz : z ^ 2 ≤ δ ^ 2 * (α * β))
    (hR : -(1 / 4 : ℝ) * (α * β) - (360 + 81 / 2) * δ * (α * β) ≤ R) :
    -(1 / 2 : ℝ) * (x * y - z ^ 2) ≤ R := by
  have hP : 0 ≤ α * β := mul_nonneg hα hβ
  have h1 : 0 ≤ (1 - δ) * α := mul_nonneg (by linarith) hα
  have h2 : 0 ≤ (1 - δ) * β := mul_nonneg (by linarith) hβ
  have hprod : (1 - δ) * α * ((1 - δ) * β) ≤ x * y :=
    mul_le_mul hx hy h2 (h1.trans hx)
  have hcoef : 0 ≤ (1 / 2 - 803 * δ) * (α * β) := mul_nonneg (by linarith) hP
  have hd2 : δ ^ 2 * (α * β) ≤ δ * (α * β) := by
    have : δ ^ 2 ≤ δ := by nlinarith
    exact mul_le_mul_of_nonneg_right this hP
  nlinarith

private theorem cuspCurv_upper_alg {α β x y z R δ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 6408) (hx : x ≤ (1 + δ) * α) (hy : y ≤ (1 + δ) * β)
    (hy0 : 0 ≤ y) (hR : R ≤ -(1 / 4 : ℝ) * (α * β) + (360 + 81 / 2) * δ * (α * β)) :
    (1 / 8 : ℝ) * (x * y - z ^ 2) ≤ -R := by
  have hP : 0 ≤ α * β := mul_nonneg hα hβ
  have h1 : 0 ≤ (1 + δ) * α := mul_nonneg (by linarith) hα
  have hprod : x * y ≤ (1 + δ) * α * ((1 + δ) * β) := mul_le_mul hx hy hy0 h1
  have hcoef : 0 ≤ (1 / 4 - (360 + 81 / 2) * δ - (1 / 8) * (1 + δ) ^ 2) * (α * β) :=
    mul_nonneg (by nlinarith) hP
  have hz := sq_nonneg z
  nlinarith

/-- **Sectional pinching on the collar (G2.c).** For `K ≥ 2` and `0 ≤ δ ≤ 1/6408`, at every point
of the cusp domain (height zero included) every plane of `T_{e q} W` has
`-1/2 · gram ≤ Rm ≤ -1/8 · gram`. -/
theorem CuspEmbedding.sectional_pinching
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    {X : Set W.Carrier} (e : CuspEmbedding W g K δ X) (hK : 2 ≤ K) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 6408) {q : CuspHalfSpace} (hq : q ∈ cuspDomain)
    (u w : TangentSpace W.model (e.toFun q)) :
    -(1 / 2) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) ≤
        metricRm04StandardAt g (e.toFun q) u w w u ∧
      metricRm04StandardAt g (e.toFun q) u w w u ≤
        -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) := by
  have hint := e.abs_metricRm04StandardAt_add_quarter_le hK (by linarith) hq
  have hm := e.abs_pullback_inner_sub_le hq
  let A : TangentSpace halfCollarModel q → TangentSpace halfCollarModel q →
      TangentSpace halfCollarModel q → TangentSpace halfCollarModel q → ℝ :=
    fun a b c d => metricRm04StandardAt g (e.toFun q)
      (mfderiv halfCollarModel W.model e.toFun q a) (mfderiv halfCollarModel W.model e.toFun q b)
      (mfderiv halfCollarModel W.model e.toFun q c) (mfderiv halfCollarModel W.model e.toFun q d)
  have hB : IsAlgCurvForm (fun a b c d : TangentSpace W.model (e.toFun q) =>
      metricRm04StandardAt g (e.toFun q) a b c d) := by
    change IsAlgCurvForm (tensor04StandardAt (metricRm04At g (e.toFun q)))
    exact mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g (e.toFun q))
  have hA : IsAlgCurvForm A :=
    { add_left := fun a b y z t => by
        simp only [A, map_add]
        exact hB.add_left _ _ _ _ _
      smul_left := fun r a y z t => by
        simp only [A, map_smul]
        exact hB.smul_left _ _ _ _ _
      anti_first := fun a b z t => hB.anti_first _ _ _ _
      anti_last := fun a b z t => hB.anti_last _ _ _ _
      bianchi := fun a b z t => hB.bianchi _ _ _ _ }
  have hAn : IsAlgCurvForm (fun a b c d => -A a b c d) :=
    { add_left := fun a b y z t => by
        simp only [hA.add_left a b y z t]; ring
      smul_left := fun r a y z t => by
        simp only [hA.smul_left r a y z t]; ring
      anti_first := fun a b z t => by
        simp only [hA.anti_first a b z t]
      anti_last := fun a b z t => by
        simp only [hA.anti_last a b z t]
      bianchi := fun a b z t => by
        have h := hA.bianchi a b z t
        linarith }
  let G' : TangentSpace halfCollarModel q →ₗ[ℝ] TangentSpace halfCollarModel q →ₗ[ℝ] ℝ :=
    { toFun := fun a => (e.cusp.metric.inner q a).toLinearMap
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  let g'' : TangentSpace halfCollarModel q →ₗ[ℝ] TangentSpace halfCollarModel q →ₗ[ℝ] ℝ :=
    { toFun := fun a =>
        (localPullInner (I := halfCollarModel) (J := W.model) g e.toFun q a).toLinearMap
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hg'' (a b : TangentSpace halfCollarModel q) : g'' a b =
      g.inner (e.toFun q) (mfderiv halfCollarModel W.model e.toFun q a)
        (mfderiv halfCollarModel W.model e.toFun q b) :=
    localPullInner_apply (I := halfCollarModel) (J := W.model) g e.toFun q a b
  have hgsym (a b : TangentSpace halfCollarModel q) : g'' a b = g'' b a := by
    rw [hg'', hg'']
    exact g.symm _ _ _
  have hGpos (a : TangentSpace halfCollarModel q) (ha : a ≠ 0) : 0 < G' a a :=
    e.cusp.metric.pos q a ha
  have hdiag (a : TangentSpace halfCollarModel q) :
      (1 - δ) * e.cusp.metric.inner q a a ≤ g'' a a ∧
        g'' a a ≤ (1 + δ) * e.cusp.metric.inner q a a := by
    have h := hm a a
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)] at h
    rw [hg'']
    constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]
  have hoff (a b : TangentSpace halfCollarModel q) (hab : e.cusp.metric.inner q a b = 0) :
      (g'' a b) ^ 2 ≤ δ ^ 2 * (e.cusp.metric.inner q a a * e.cusp.metric.inner q b b) := by
    have hα := metric_inner_self_nonneg e.cusp.metric q a
    have hβ := metric_inner_self_nonneg e.cusp.metric q b
    have h := hm a b
    rw [hab, sub_zero] at h
    rw [hg'']
    have h2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h
    rw [sq_abs] at h2
    refine h2.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hα, Real.sq_sqrt hβ]
    ring
  have hcurv (a b : TangentSpace halfCollarModel q) (hab : e.cusp.metric.inner q a b = 0) :
      -(1 / 4 : ℝ) * (e.cusp.metric.inner q a a * e.cusp.metric.inner q b b) -
          (360 + 81 / 2) * δ * (e.cusp.metric.inner q a a * e.cusp.metric.inner q b b) ≤
        A a b b a ∧
      A a b b a ≤ -(1 / 4 : ℝ) * (e.cusp.metric.inner q a a * e.cusp.metric.inner q b b) +
          (360 + 81 / 2) * δ * (e.cusp.metric.inner q a a * e.cusp.metric.inner q b b) := by
    have h := hint a b
    rw [hab] at h
    have h' := abs_le.mp h
    constructor
    · change _ ≤ metricRm04StandardAt g (e.toFun q) _ _ _ _
      linarith [h'.1]
    · change metricRm04StandardAt g (e.toFun q) _ _ _ _ ≤ _
      linarith [h'.2]
  have hlow := hA.sectional_lower_bound_of_orthogonal G' g'' hGpos hgsym (c := -(1 / 2)) (by
    intro a b hab
    change e.cusp.metric.inner q a b = 0 at hab
    exact cuspCurv_lower_alg (metric_inner_self_nonneg _ _ _) (metric_inner_self_nonneg _ _ _)
      hδ0 hδ (hdiag a).1 (hdiag b).1 (hoff a b hab) (hcurv a b hab).1)
  have hup := hAn.sectional_lower_bound_of_orthogonal G' g'' hGpos hgsym (c := 1 / 8) (by
    intro a b hab
    change e.cusp.metric.inner q a b = 0 at hab
    have hgb : 0 ≤ g'' b b := by
      rw [hg'']
      exact metric_inner_self_nonneg _ _ _
    exact cuspCurv_upper_alg (metric_inner_self_nonneg _ _ _) (metric_inner_self_nonneg _ _ _)
      hδ0 hδ (hdiag a).2 (hdiag b).2 hgb (hcurv a b hab).2)
  obtain ⟨L, hL⟩ := e.isInvertible_mfderiv hq
  have hsurj (y : TangentSpace W.model (e.toFun q)) :
      mfderiv halfCollarModel W.model e.toFun q (L.symm y) = y := by
    rw [← hL]
    exact L.apply_symm_apply y
  have hl := hlow (L.symm u) (L.symm w)
  have hu' := hup (L.symm u) (L.symm w)
  simp only [hg'', A, hsurj] at hl hu'
  constructor
  · linarith
  · linarith

/-- **Pinching in the consumer shape of `G_consumer_clauses_of_pinching`.** -/
theorem cusp_sectional_pinching :
    ∃ δ₁ > 0, ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
      (K : ℕ) (δ : ℝ) (X : Set W.Carrier) (e : CuspEmbedding W g K δ X), 2 ≤ K → 0 ≤ δ →
      δ ≤ δ₁ → ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 → ∀ u w : TangentSpace W.model (e.toFun q),
        -(1 / 2) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) ≤
            metricRm04StandardAt g (e.toFun q) u w w u ∧
          metricRm04StandardAt g (e.toFun q) u w w u ≤
            -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) :=
  ⟨1 / 6408, by norm_num, fun _ _ _ _ _ e hK h0 h1 _ hq _ u w =>
    e.sectional_pinching hK h0 h1 hq u w⟩

end DifferentialGeometry.Geometry.Collapse
