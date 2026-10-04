import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.ProductMap
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Distance.FiniteProductDifferential

/-!
# The finite product metric of the actual zero factor

The product bilinear form uses the actual coordinate factor and induced zero-fibre metric.
Its finite regularity is tested in native local frames without imposing a smooth atlas.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section FiniteSections

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsManifold I 1 M]

omit [FiniteDimensional ℝ V] [IsManifold I (n + 1) M] in
private theorem finite_frame_smooth (a : M) (v : V) :
    ContMDiffAt I I.tangent n (fun x => (⟨x,
      (trivializationAt V (TangentSpace I) a).symmL ℝ x v⟩ : TangentBundle I M)) a := by
  rw [contMDiffAt_section]
  let tau := trivializationAt V (TangentSpace I) a
  apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
  filter_upwards [tau.open_baseSet.mem_nhds (mem_baseSet_trivializationAt V _ a)] with x hx
  rw [tau.symmL_apply hx, tau.apply_mk_symm hx]

omit [IsManifold I (n + 1) M] in
private theorem finite_bilinear_section_smooth
    (B : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (a : M)
    (h : ∀ v w : V, ContMDiffAt I 𝓘(ℝ, ℝ) n (fun x => B x
      ((trivializationAt V (TangentSpace I) a).symmL ℝ x v)
      ((trivializationAt V (TangentSpace I) a).symmL ℝ x w)) a) :
    ContMDiffAt I (I.prod 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ)) n
      (fun x => (⟨x, B x⟩ : TotalSpace (V →L[ℝ] V →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) a := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_pointwise
  intro v
  apply contMDiffAt_clm_of_pointwise
  intro w
  apply (h v w).congr_of_eventuallyEq
  filter_upwards [(trivializationAt V (TangentSpace I) a).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt V _ a)] with x hx
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
    Trivialization.symmL_apply (trivializationAt V (TangentSpace I) a) hx]

end FiniteSections

section Product

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}
  [IsManifold I (n + 1) M] [IsManifold J (n + 1) N]
  [IsManifold I 1 M] [IsManifold J 1 N]

def finiteProductInner
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _))
    (x : M × N) : TangentSpace (I.prod J) x →L[ℝ]
      TangentSpace (I.prod J) x →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.fst ℝ E F)).comp
      ((g.inner x.1).comp (ContinuousLinearMap.fst ℝ E F)) +
    (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.snd ℝ E F)).comp
      ((h.inner x.2).comp (ContinuousLinearMap.snd ℝ E F))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I (n + 1) M] [IsManifold J (n + 1) N] in
@[simp] theorem finiteProductInner_apply
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _))
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    finiteProductInner g h x v w = g.inner x.1 v.1 w.1 + h.inner x.2 v.2 w.2 := by
  rfl

omit [IsManifold I (n + 1) M] [IsManifold J (n + 1) N] in
theorem contMDiff_finiteProductInner
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _)) :
    ContMDiff (I.prod J) ((I.prod J).prod 𝓘(ℝ, (E × F) →L[ℝ] (E × F) →L[ℝ] ℝ)) n
      (fun x => (⟨x, finiteProductInner g h x⟩ :
        TotalSpace ((E × F) →L[ℝ] (E × F) →L[ℝ] ℝ)
          (fun x => TangentSpace (I.prod J) x →L[ℝ]
            TangentSpace (I.prod J) x →L[ℝ] ℝ))) := by
  intro a
  apply finite_bilinear_section_smooth
  intro v w
  have hframe (q : E × F) := finite_frame_smooth (I := I.prod J) (n := n) a q
  have hf : ContMDiff (I.prod J).tangent I.tangent n (tangentMap (I.prod J) I Prod.fst) :=
    (contMDiff_fst (I := I) (J := J) (M := M) (N := N) (n := n + 1)).contMDiff_tangentMap le_rfl
  have hs : ContMDiff (I.prod J).tangent J.tangent n (tangentMap (I.prod J) J Prod.snd) :=
    (contMDiff_snd (I := I) (J := J) (M := M) (N := N) (n := n + 1)).contMDiff_tangentMap le_rfl
  have hg := ContMDiffAt.clm_bundle_apply₂
    (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := Bundle.Trivial M ℝ)
    ((g.contMDiff.comp (contMDiff_fst (I := I) (J := J) (M := M) (N := N) (n := n))) a)
    ((hf _).comp a (hframe v)) ((hf _).comp a (hframe w))
  have hh := ContMDiffAt.clm_bundle_apply₂
    (E₁ := TangentSpace J) (E₂ := TangentSpace J) (E₃ := Bundle.Trivial N ℝ)
    ((h.contMDiff.comp (contMDiff_snd (I := I) (J := J) (M := M) (N := N) (n := n))) a)
    ((hs _).comp a (hframe v)) ((hs _).comp a (hframe w))
  rw [contMDiffAt_totalSpace] at hg hh
  apply (hg.2.add hh.2).congr_of_eventuallyEq
  filter_upwards [] with x
  simp only [finiteProductInner_apply, mfderiv_fst, mfderiv_snd]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I (n + 1) M] [IsManifold J (n + 1) N] in
private theorem finiteProductInner_pos
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _))
    (x : M × N) (v : TangentSpace (I.prod J) x) (hv : v ≠ 0) :
    0 < finiteProductInner g h x v v := by
  rw [finiteProductInner_apply]
  by_cases hfirst : v.1 = 0
  · have hsecond : v.2 ≠ 0 := by
      intro hzero
      exact hv (Prod.ext hfirst hzero)
    have hzero : g.inner x.1 (0 : TangentSpace I x.1) 0 = 0 := by
      rw [(g.inner x.1).map_zero, zero_apply]
    rw [hfirst]
    erw [hzero, zero_add]
    exact h.pos x.2 v.2 hsecond
  · have hnonneg : 0 ≤ h.inner x.2 v.2 v.2 := by
      by_cases hz : v.2 = 0
      · have hzero : h.inner x.2 (0 : TangentSpace J x.2) 0 = 0 := by
          rw [(h.inner x.2).map_zero, zero_apply]
        rw [hz]
        erw [hzero]
      · exact (h.pos x.2 v.2 hz).le
    exact add_pos_of_pos_of_nonneg (g.pos x.1 v.1 hfirst) hnonneg

def finiteProductMetric
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _)) :
    ContMDiffRiemannianMetric (I.prod J) n (E × F)
      (TangentSpace (I.prod J) : M × N → Type _) where
  inner := finiteProductInner g h
  symm x v w := by
    rw [finiteProductInner_apply, finiteProductInner_apply]
    exact congrArg₂ (· + ·) (g.symm x.1 v.1 w.1) (h.symm x.2 v.2 w.2)
  pos := finiteProductInner_pos g h
  isVonNBounded x := Geometry.posDef_isVonNBounded (E := E × F)
    (finiteProductInner g h x) (finiteProductInner_pos g h x)
  contMDiff := contMDiff_finiteProductInner g h

omit [IsManifold I (n + 1) M] [IsManifold J (n + 1) N] in
theorem finiteProductMetric_inner
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _))
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    (finiteProductMetric g h).inner x v w = g.inner x.1 v.1 w.1 + h.inner x.2 v.2 w.2 :=
  finiteProductInner_apply g h x v w

end Product

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def finiteEuclideanMetric (n : ℕ∞ω) :
    ContMDiffRiemannianMetric 𝓘(ℝ, W) n W (TangentSpace 𝓘(ℝ, W) : W → Type _) where
  inner := (riemannianMetricVectorSpace W).inner
  symm := (riemannianMetricVectorSpace W).symm
  pos := (riemannianMetricVectorSpace W).pos
  isVonNBounded := (riemannianMetricVectorSpace W).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace W).contMDiff.of_le le_top


section Actual

variable {E H M F Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y] [NeZero (Module.finrank ℝ E)] {r : ℕ∞}

local notation "P" => Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
local notation "IZ" => 𝓘(ℝ, P)
local notation "IP" => ModelWithCorners.prod (𝓘(ℝ, F)) IZ

def splittingProductMetric
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ContMDiffRiemannianMetric IP ((r : ℕ∞ω) + 1) (F × P)
      (TangentSpace IP : F × {x : M // (e x).fst = 0} → Type _) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let : IsManifold IZ ((r : ℕ∞ω) + 2) {x : M // (e x).fst = 0} :=
    splittingFactor_isManifold g hr hnorm e
  exact finiteProductMetric (finiteEuclideanMetric ((r : ℕ∞ω) + 1))
    (inducedMetric g hr hnorm e)

theorem splittingProductMetric_inner
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (p : F × {x : M // (e x).fst = 0}) (v w : TangentSpace IP p),
      (splittingProductMetric g hr hnorm e).inner p v w =
        inner ℝ v.1 w.1 + (inducedMetric g hr hnorm e).inner p.2 v.2 w.2 := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  intro p v w
  exact finiteProductMetric_inner (finiteEuclideanMetric ((r : ℕ∞ω) + 1))
    (inducedMetric g hr hnorm e) p v w


omit [CompleteSpace M] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
theorem splittingProductMap_dist_sq (e : M ≃ᵢ WithLp 2 (F × Y))
    (p q : F × {x : M // (e x).fst = 0}) :
    dist (splittingProductMap e p) (splittingProductMap e q) ^ 2 =
      dist p.2.val q.2.val ^ 2 + dist p.1 q.1 ^ 2 := by
  rw [← e.dist_eq, ← e.dist_eq]
  simp only [splittingProductMap, e.apply_symm_apply, WithLp.prod_dist_sq_eq_add_sq,
    WithLp.toLp_fst, WithLp.toLp_snd, p.2.property, q.2.property, dist_self,
    zero_pow (by decide : 2 ≠ 0), zero_add]
  exact add_comm _ _

theorem splittingProductMap_metric
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (p : F × {x : M // (e x).fst = 0}) (v w : TangentSpace IP p),
      g.inner (splittingProductMap e p)
        (mfderiv IP I (splittingProductMap e) p v)
        (mfderiv IP I (splittingProductMap e) p w) =
      inner ℝ v.1 w.1 + (inducedMetric g hr hnorm e).inner p.2 v.2 w.2 := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let Z := {x : M // (e x).fst = 0}
  let : IsManifold IZ ((r : ℕ∞ω) + 2) Z := splittingFactor_isManifold g hr hnorm e
  let : IsManifold IZ (r : ℕ∞ω) Z := IsManifold.of_le
    (n := (r : ℕ∞ω) + 2) le_self_add
  intro p v w
  let c := extChartAt IP p
  let x := c p
  have hc : ContMDiffAt 𝓘(ℝ, F × P) IP r c.symm x :=
    (contMDiffOn_extChartAt_symm (n := r) p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target p))
  have hr0 : (r : ℕ∞ω) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (one_le_two.trans hr)).ne'
  have hd := hc.mdifferentiableAt hr0
  have hbase : c.symm x = p := c.left_inv (mem_extChartAt_source p)
  have hDc : mfderiv 𝓘(ℝ, F × P) IP c.symm x = ContinuousLinearMap.id ℝ (F × P) := by
    have h := mfderivWithin_range_extChartAt_symm (I := IP) (x := p)
    rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
    change (mfderiv 𝓘(ℝ, F × P) IP c.symm x : (F × P) →L[ℝ] (F × P)) =
      ContinuousLinearMap.id ℝ (F × P) at h
    exact h
  have hu := (contMDiff_splittingProductMap g hr hnorm e (c.symm x)).mdifferentiableAt hr0
  have hv := ((contMDiff_splittingFactor_val g hr hnorm e).of_le
    (show (r : ℕ∞ω) ≤ (r : ℕ∞ω) + 2 from le_self_add)).comp
      (contMDiff_snd (I := 𝓘(ℝ, F)) (J := IZ) (M := F) (N := Z) (n := r))
  have ha : DifferentiableAt ℝ (fun y => (c.symm y).1) x :=
    ((contMDiff_fst (I := 𝓘(ℝ, F)) (J := IZ)
      (M := F) (N := Z) (n := r)).contMDiffAt.comp x hc).mdifferentiableAt hr0 |>.differentiableAt
  have H := FiniteMetricDistance.inner_mfderiv_eq_of_l2_dist_sq g hr hnorm
    (hu.comp x hd) ((hv _).mdifferentiableAt hr0 |>.comp x hd) ha
    (Filter.Eventually.of_forall (fun y => splittingProductMap_dist_sq e (c.symm x) (c.symm y)))
    v w
  rw [mfderiv_comp x hu hd, mfderiv_comp x ((hv _).mdifferentiableAt hr0) hd, hDc] at H
  change (g.inner (splittingProductMap e (c.symm x)) : E →L[ℝ] E →L[ℝ] ℝ)
      (mfderiv IP I (splittingProductMap e) (c.symm x) v)
      (mfderiv IP I (splittingProductMap e) (c.symm x) w) =
    (g.inner (c.symm x).2.val : E →L[ℝ] E →L[ℝ] ℝ)
      (mfderiv IP I (Subtype.val ∘ Prod.snd) (c.symm x) v)
      (mfderiv IP I (Subtype.val ∘ Prod.snd) (c.symm x) w) +
      inner ℝ (fderiv ℝ (fun y => (c.symm y).1) x v)
        (fderiv ℝ (fun y => (c.symm y).1) x w) at H
  have hA : fderiv ℝ (fun y => (c.symm y).1) x = ContinuousLinearMap.fst ℝ F P := by
    have h := mfderiv_comp x mdifferentiableAt_fst hd
    rw [hDc, mfderiv_fst] at h
    rw [mfderiv_eq_fderiv] at h
    change fderiv ℝ (fun y => (c.symm y).1) x = ContinuousLinearMap.fst ℝ F P at h
    exact h
  rw [hA, hbase] at H
  have hV := mfderiv_comp p
    ((contMDiff_splittingFactor_val g hr hnorm e).mdifferentiableAt (by simp))
    ((contMDiff_snd (I := 𝓘(ℝ, F)) (J := IZ) (M := F) (N := Z)
      (n := (1 : ℕ∞ω))).mdifferentiableAt one_ne_zero)
  rw [hV, mfderiv_snd] at H
  erw [inducedMetric_inner g hr hnorm e]
  exact H.trans (add_comm _ _)

theorem splittingProductMap_pullback_inner
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (p : F × {x : M // (e x).fst = 0}) (v w : TangentSpace IP p),
      g.inner (splittingProductMap e p)
        (mfderiv IP I (splittingProductMap e) p v)
        (mfderiv IP I (splittingProductMap e) p w) =
      inner ℝ v.1 w.1 + (inducedMetric g hr hnorm e).inner p.2 v.2 w.2 :=
  splittingProductMap_metric g hr hnorm e

end Actual

private theorem realProductMetric_enorm : ∀ (x : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) x),
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (realFrameMetric.inner x v v)) := by
  intro x v
  change ‖(v : ℝ)‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ (v : ℝ) v))
  rw [← norm_eq_sqrt_real_inner, ← ofReal_norm]

local instance realProductMetricDimension : NeZero (Module.finrank ℝ ℝ) :=
  ⟨by rw [Module.finrank_self]; decide⟩

theorem real_splittingProductMap_metric :
    letI := splittingFactorChartedSpace (r := 2) realFrameMetric le_rfl
      realProductMetric_enorm realFrameSplitting.{0}
    letI := splittingFactor_isManifold_one (r := 2) realFrameMetric le_rfl
      realProductMetric_enorm realFrameSplitting.{0}
    ∀ (p : ℝ × {x : ℝ // (realFrameSplitting.{0} x).fst = 0})
      (v w : TangentSpace ((𝓘(ℝ, ℝ)).prod
        𝓘(ℝ, Fin (Module.finrank ℝ ℝ - Module.finrank ℝ ℝ) → ℝ)) p),
      realFrameMetric.inner (splittingProductMap realFrameSplitting.{0} p)
        (mfderiv ((𝓘(ℝ, ℝ)).prod
          𝓘(ℝ, Fin (Module.finrank ℝ ℝ - Module.finrank ℝ ℝ) → ℝ)) 𝓘(ℝ, ℝ)
            (splittingProductMap realFrameSplitting.{0}) p v)
        (mfderiv ((𝓘(ℝ, ℝ)).prod
          𝓘(ℝ, Fin (Module.finrank ℝ ℝ - Module.finrank ℝ ℝ) → ℝ)) 𝓘(ℝ, ℝ)
            (splittingProductMap realFrameSplitting.{0}) p w) =
      (splittingProductMetric (r := 2) realFrameMetric le_rfl
        realProductMetric_enorm realFrameSplitting.{0}).inner p v w := by
  let _ := splittingFactorChartedSpace (r := 2) realFrameMetric le_rfl
    realProductMetric_enorm realFrameSplitting.{0}
  let _ := splittingFactor_isManifold_one (r := 2) realFrameMetric le_rfl
    realProductMetric_enorm realFrameSplitting.{0}
  intro p v w
  exact (splittingProductMap_metric (r := 2) realFrameMetric le_rfl
    realProductMetric_enorm realFrameSplitting.{0} p v w).trans
      (splittingProductMetric_inner (r := 2) realFrameMetric le_rfl
        realProductMetric_enorm realFrameSplitting.{0} p v w).symm

end DifferentialGeometry.Geometry.ExactSplitting
