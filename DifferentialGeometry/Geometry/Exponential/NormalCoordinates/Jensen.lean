import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Convexity
import DifferentialGeometry.Geometry.CenterOfMass.Basic

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Exponential Geodesic Variation
open Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

section PositiveRank

variable [NeZero (Module.finrank ℝ E)]

private theorem branch_hessian_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete g) {B K : ℝ}
    (hcurv : ∀ z : E, ‖z‖ < B → ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      g.inner z (Geometry.Curvature.riemannOp
        (Geometry.Connection.LeviCivita g) z v w w) v ≤
        K * g.inner z v v * g.inner z w w)
    (x : E) (u : TangentSpace 𝓘(ℝ, E) x)
    (hsmall : K * g.inner x u u < (Real.pi / 2) ^ 2) :
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩
    let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
    let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E := hcomplete.complete
    let hnorm : IsMetricNorm g :=
      fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g z v
    (∀ t ∈ Ioo (0 : ℝ) 1, ‖intrinsicGeodesic g hnorm x u t‖ < B) →
    ∀ C : ExponentialInverseBranch g hnorm x, (u : E) ∈ C.hom.source →
      ∀ Y : E, Y ≠ 0 →
        0 < Geometry.Operator.hessFun g (branchEnergy g C)
          (expMapIntrinsic g hnorm x u) Y Y := by
  dsimp only
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hnorm : IsMetricNorm g :=
    fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g z v
  intro hfence C hu Y hY
  apply branchEnergy_hess_pos C hu hsmall ?_ Y hY
  dsimp only
  intro t ht v
  let γ := intrinsicGeodesic g hnorm x u
  have hspeed : g.inner (γ t) (curveVelocity γ t) (curveVelocity γ t) = g.inner x u u := by
    simpa only [γ, curveVelocity] using! intrinsicGeodesic_speedSq_eq g hnorm x u t
  calc
    _ ≤ K * g.inner (γ t) v v * g.inner (γ t) (curveVelocity γ t) (curveVelocity γ t) :=
      hcurv (γ t) (hfence t ht) v (curveVelocity γ t)
    _ = (K * g.inner x u u) * g.inner (γ t) v v := by
      rw [hspeed]
      ring


variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem exists_jensen_of_pullback_extension
    (g : SmoothRiemannianMetric I M) (p : M) (U : Opens E)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞ (framedExpMap g p) U)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {B a K : ℝ}
    (hball : Metric.closedBall (0 : E) B ⊆ (U : Set E))
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ z : E, ‖z‖ ≤ B → ∀ v w : E,
      gExt.inner z v w = g.inner (framedExpMap g p z)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z w))
    (h3aB : 3 * a < B) (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hcurv : ∀ z : E, ‖z‖ < B → ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      gExt.inner z (Geometry.Curvature.riemannOp
        (Geometry.Connection.LeviCivita gExt) z v w w) v ≤
        K * gExt.inner z v v * gExt.inner z w w) :
    let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
      (isLocalDiffeomorph_restrict_open U hloc)
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
      ⟨gExt.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
    let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
    let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E := hcomplete.complete
    let hExt : IsMetricNorm gExt :=
      fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt z v
    ∃ join : U → U → ℝ → U,
      (∀ x : U, ‖(x : E)‖ ≤ a → ∀ y : U, ‖(y : E)‖ ≤ a →
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (join x y) ∧
        IsGeodesicOn gPull (join x y) (Icc (0 : ℝ) 1) ∧
        join x y 0 = x ∧ join x y 1 = y ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ‖(join x y t : E)‖ ≤ a) ∧
        EqOn (Subtype.val ∘ join x y) (minJoin gExt hExt (x : E) (y : E))
          (Icc (0 : ℝ) 1)) ∧
      ∀ pt : U, ‖(pt : E)‖ ≤ a →
        CenterOfMass.StrictMidJensenOn join {z : U | ‖(z : E)‖ ≤ a}
          (fun z => (1 / 2 : ℝ) * (riemannianEDistOf gPull pt z).toReal ^ 2) := by
  classical
  dsimp only
  let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
    (isLocalDiffeomorph_restrict_open U hloc)
  let : T2Space (TangentBundle I M) := inferInstance
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt z v
  have hscale : ∃ L : ℝ, 2 * a < L ∧ a + L < B ∧ K * L ^ 2 < (Real.pi / 2) ^ 2 := by
    have hc : ∀ᶠ L in 𝓝[>] (2 * a), K * L ^ 2 < (Real.pi / 2) ^ 2 :=
      Filter.Eventually.filter_mono inf_le_left
        ((continuous_const.mul (continuous_id.pow 2)).continuousAt (Iio_mem_nhds hsmall))
    obtain ⟨L, hLsmall, hLlow, hLhigh⟩ :=
      (hc.and (Ioo_mem_nhdsGT (by linarith : 2 * a < B - a))).exists
    exact ⟨L, hLlow, by linarith, hLsmall⟩
  obtain ⟨L, h2aL, hbudget, hsmallL⟩ := hscale
  have hdist (x y : E) (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
      riemannianEDistOf gExt x y ≤ ENNReal.ofReal (2 * a) := by
    have ha := (norm_nonneg x).trans hx
    exact (riemannianEDistOf_le_norm_add_norm_of_pullback_extension
      g p gExt hdom hmetric (hx.trans (by linarith)) (hy.trans (by linarith))).trans
        (ENNReal.ofReal_le_ofReal (by linarith))
  have hpairBudget (x y : E) (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
      ENNReal.ofReal ‖x‖ + riemannianEDistOf gExt x y < ENNReal.ofReal B := by
    have ha := (norm_nonneg x).trans hx
    apply (add_le_add (ENNReal.ofReal_le_ofReal hx) (hdist x y hx hy)).trans_lt
    rw [← ENNReal.ofReal_add ha (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have hcore (x y : E) (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
      ∀ t ∈ Icc (0 : ℝ) 1, ‖minJoin gExt hExt x y t‖ ≤ a := by
    have ha := (norm_nonneg x).trans hx
    have huL : Real.sqrt (gExt.inner x (minimizingVec gExt hExt x y)
        (minimizingVec gExt hExt x y)) ≤ L := by
      rw [minimizingVec_len]
      exact (ENNReal.toReal_le_of_le_ofReal (by positivity) (hdist x y hx hy)).trans h2aL.le
    have hlocal : K * (a + L / 2) ^ 2 < (Real.pi / 2) ^ 2 := by
      by_cases hK : 0 ≤ K
      · apply lt_of_le_of_lt ?_ hsmallL
        apply mul_le_mul_of_nonneg_left _ hK
        nlinarith
      · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hK) (sq_nonneg _)).trans_lt
          (sq_pos_of_pos (div_pos Real.pi_pos (by norm_num)))
    exact norm_intrinsicGeodesic_le_of_pullback_extension g p gExt hcomplete hdom hmetric hcurv
      hbudget hlocal hx hy (minimizingVec gExt hExt x y) huL (minJoin_one gExt hExt x y)
  have hget (x y : U) (hx : ‖(x : E)‖ ≤ a) (hy : ‖(y : E)‖ ≤ a) :
      ∃ Γ : ℝ → U, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ Γ ∧
        IsGeodesicOn gPull Γ (Icc (0 : ℝ) 1) ∧ Γ 0 = x ∧ Γ 1 = y ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ‖(Γ t : E)‖ ≤ a) ∧
        EqOn (Subtype.val ∘ Γ) (minJoin gExt hExt (x : E) (y : E)) (Icc (0 : ℝ) 1) := by
    obtain ⟨Γ, hΓ, hgeo, hzero, hone, _, _, heq⟩ :=
      exists_geodesic_restriction_of_pullback_extension g p U hloc gExt hcomplete hball hdom
        (fun z hz => hmetric z hz) (x : E) (y : E) (hpairBudget x y hx hy)
    have hEq := heq inferInstance
    refine ⟨Γ, hΓ, hgeo, Subtype.ext hzero, Subtype.ext hone, ?_, hEq⟩
    intro t ht
    change ‖(Subtype.val ∘ Γ) t‖ ≤ a
    rw [hEq ht]
    exact hcore x y hx hy t ht
  let join : U → U → ℝ → U := fun x y =>
    if hxy : ‖(x : E)‖ ≤ a ∧ ‖(y : E)‖ ≤ a then
      Classical.choose (hget x y hxy.1 hxy.2) else fun _ => x
  have hjoin (x : U) (hx : ‖(x : E)‖ ≤ a) (y : U) (hy : ‖(y : E)‖ ≤ a) :
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (join x y) ∧
      IsGeodesicOn gPull (join x y) (Icc (0 : ℝ) 1) ∧
      join x y 0 = x ∧ join x y 1 = y ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖(join x y t : E)‖ ≤ a) ∧
      EqOn (Subtype.val ∘ join x y) (minJoin gExt hExt (x : E) (y : E)) (Icc (0 : ℝ) 1) := by
    simpa only [join, dif_pos (And.intro hx hy)] using Classical.choose_spec (hget x y hx hy)
  refine ⟨join, hjoin, ?_⟩
  intro pt hpt
  let φ : U → ℝ := fun z => (1 / 2 : ℝ) * (riemannianEDistOf gPull pt z).toReal ^ 2
  apply CenterOfMass.jensen_of_strict
    (fun x hx y hy _ => (hjoin x hx y hy).2.2.2.2.1 (1 / 2) (by norm_num))
    (fun x hx y hy => (hjoin x hx y hy).2.2.1)
    (fun x hx y hy => (hjoin x hx y hy).2.2.2.1)
  intro x hx y hy hxy
  let uxy := minimizingVec gExt hExt (x : E) (y : E)
  let γ := minJoin gExt hExt (x : E) (y : E)
  have hγsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ :=
    intrinsicGeodesic_contMDiff gExt hExt (x : E) uxy
  have hγgeo : IsGeodesic gExt γ := intrinsicGeodesic_isGeodesic gExt hExt (x : E) uxy
  have hu0 : uxy ≠ 0 := by
    intro hu
    apply hxy
    apply Subtype.ext
    have hend := minimizingVec_exp gExt hExt (x : E) (y : E)
    change expMapIntrinsic gExt hExt (x : E) uxy = (y : E) at hend
    rw [hu, expMapIntrinsic_zero] at hend
    exact hend
  have hvelocity (t : ℝ) : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 : E) ≠ 0 :=
    intrinsicGeo_velocity_ne gExt hExt (x : E) uxy hu0 t
  let f : E → ℝ := fun z => (1 / 2 : ℝ) * (riemannianEDistOf gExt (pt : E) z).toReal ^ 2
  have hfinite : {z : E | riemannianEDist 𝓘(ℝ, E) (pt : E) z ≠ (⊤ : ℝ≥0∞)} = univ := by
    ext z
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact riemannianEDist_ne_top (I := 𝓘(ℝ, E)) (pt : E) z
  have hf : Continuous f := by
    have hc := continuousOn_riemannianEDist_toReal_on_finite gExt (pt : E)
    rw [hfinite] at hc
    exact continuous_const.mul ((continuousOn_univ.mp hc).pow 2)
  have hEq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : φ (join x y t) = f (γ t) := by
    have hd := riemannianEDistOf_eq_of_pullback_extension g p U hloc gExt hball hdom
      (fun z hz => hmetric z hz) pt (join x y t)
      (hpairBudget pt (join x y t) hpt ((hjoin x hx y hy).2.2.2.2.1 t ht))
    have he := (hjoin x hx y hy).2.2.2.2.2 ht
    change (1 / 2 : ℝ) * (riemannianEDistOf gPull pt (join x y t)).toReal ^ 2 = _
    rw [hd]
    exact congrArg f he
  apply strictConvexOn_of_deriv2_pos (convex_Icc (0 : ℝ) 1)
    ((hf.comp hγsmooth.continuous).continuousOn.congr hEq)
  intro t ht
  rw [interior_Icc] at ht
  have htIcc := Ioo_subset_Icc_self ht
  let q := join x y t
  have hq : ‖(q : E)‖ ≤ a := (hjoin x hx y hy).2.2.2.2.1 t htIcc
  have hqval : (q : E) = γ t := (hjoin x hx y hy).2.2.2.2.2 htIcc
  let u := minimizingVec gExt hExt (pt : E) (q : E)
  obtain ⟨β, huβ, hgerm⟩ := exists_branchEnergy_riemannianEDistOf_germ_of_pullback_extension
    g p U hloc gExt hcomplete hball hdom hmetric hcurv hbudget h2aL hsmallL pt q hpt hq
  have huLen : Real.sqrt (gExt.inner (pt : E) u u) ≤ 2 * a := by
    rw [minimizingVec_len]
    exact ENNReal.toReal_le_of_le_ofReal
      (by linarith [norm_nonneg (pt : E)]) (hdist pt q hpt hq)
  have huSmall : K * gExt.inner (pt : E) u u < (Real.pi / 2) ^ 2 := by
    have huNonneg := metric_inner_self_nonneg gExt (pt : E) u
    by_cases hK : 0 ≤ K
    · apply lt_of_le_of_lt ?_ hsmall
      apply mul_le_mul_of_nonneg_left _ hK
      nlinarith [Real.sq_sqrt huNonneg, Real.sqrt_nonneg (gExt.inner (pt : E) u u)]
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hK) huNonneg).trans_lt
        (sq_pos_of_pos (div_pos Real.pi_pos (by norm_num)))
  have huFence : ∀ s ∈ Ioo (0 : ℝ) 1, ‖intrinsicGeodesic gExt hExt (pt : E) u s‖ < B := by
    intro s hs
    exact (hcore pt q hpt hq s (Ioo_subset_Icc_self hs)).trans_lt
      (by linarith [norm_nonneg (pt : E)])
  have hpos := branch_hessian_pos gExt hcomplete hcurv (pt : E) u huSmall huFence β huβ
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1) (hvelocity t)
  have huEnd : expMapIntrinsic gExt hExt (pt : E) u = γ t :=
    (minimizingVec_exp gExt hExt (pt : E) (q : E)).trans hqval
  rw [huEnd] at hpos
  have hβmap : β.hom (u : E) = γ t := (β.hom_eq huβ).symm.trans huEnd
  have hβdom : γ t ∈ β.dom := by
    rw [← hβmap]
    exact β.hom.map_source huβ
  have hbranch : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (branchEnergy gExt β) β.dom := by
    have hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ β.inv β.dom := β.inv_contMDiffOn
    let gp : E →L[ℝ] E →L[ℝ] ℝ := gExt.inner (pt : E)
    have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
        (fun _ : E => gp) β.dom := contMDiffOn_const
    with_unfolding_all exact contMDiffOn_const.mul ((hg.clm_apply hi).clm_apply hi)
  have hd2 := deriv2_geo_on_at gExt β.hom.open_target hbranch hγsmooth (hγgeo t) hβdom
  have hgermAlong : (fun s => branchEnergy gExt β (join x y s : E)) =ᶠ[𝓝 t]
      (fun s => φ (join x y s)) :=
    hgerm.comp_tendsto ((hjoin x hx y hy).1.continuous.tendsto t)
  have hIcc : ∀ᶠ s in 𝓝 t, s ∈ Icc (0 : ℝ) 1 :=
    Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self
  have hcomp : branchEnergy gExt β ∘ γ =ᶠ[𝓝 t] (fun s => φ (join x y s)) := by
    filter_upwards [hgermAlong, hIcc] with s hs hsIcc
    change branchEnergy gExt β (γ s) = _
    exact (congrArg (branchEnergy gExt β)
      ((hjoin x hx y hy).2.2.2.2.2 hsIcc).symm).trans hs
  have hderiv : (deriv^[2] (fun s => φ (join x y s))) t =
      (deriv^[2] (branchEnergy gExt β ∘ γ)) t :=
    Filter.EventuallyEq.deriv_eq hcomp.symm.deriv
  with_unfolding_all exact (hderiv.trans hd2) ▸ hpos


end PositiveRank

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem exists_geodesic_join_strictMidJensenOn_of_pullback_extension
    (g : SmoothRiemannianMetric I M) (p : M) (U : Opens E)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞ (framedExpMap g p) U)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {B a K : ℝ}
    (hball : Metric.closedBall (0 : E) B ⊆ (U : Set E))
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ z : E, ‖z‖ ≤ B → ∀ v w : E,
      gExt.inner z v w = g.inner (framedExpMap g p z)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z w))
    (h3aB : 3 * a < B) (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hcurv : ∀ z : E, ‖z‖ < B → ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      gExt.inner z (Geometry.Curvature.riemannOp
        (Geometry.Connection.LeviCivita gExt) z v w w) v ≤
        K * gExt.inner z v v * gExt.inner z w w) :
    let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
      (isLocalDiffeomorph_restrict_open U hloc)
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
      ⟨gExt.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
    let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
    let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E := hcomplete.complete
    let hExt : IsMetricNorm gExt :=
      fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt z v
    ∃ join : U → U → ℝ → U,
      (∀ x : U, ‖(x : E)‖ ≤ a → ∀ y : U, ‖(y : E)‖ ≤ a →
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (join x y) ∧
        IsGeodesicOn gPull (join x y) (Icc (0 : ℝ) 1) ∧
        join x y 0 = x ∧ join x y 1 = y ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ‖(join x y t : E)‖ ≤ a) ∧
        ∀ hdim : NeZero (Module.finrank ℝ E), letI := hdim;
          EqOn (Subtype.val ∘ join x y) (minJoin gExt hExt (x : E) (y : E))
          (Icc (0 : ℝ) 1)) ∧
      ∀ pt : U, ‖(pt : E)‖ ≤ a →
        CenterOfMass.StrictMidJensenOn join {z : U | ‖(z : E)‖ ≤ a}
          (fun z => (1 / 2 : ℝ) * (riemannianEDistOf gPull pt z).toReal ^ 2) := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    dsimp only
    refine ⟨fun x _ _ => x, ?_, ?_⟩
    · intro x hx y _
      refine ⟨contMDiff_const, ?_, rfl, Subsingleton.elim _ _, fun _ _ => hx, ?_⟩
      · intro t _
        exact isGeodesic_const _ x t
      · intro hpos
        exact False.elim (hpos.out hdim)
    · intro pt _ x _ y _ hxy
      exact False.elim (hxy (Subsingleton.elim _ _))
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    obtain ⟨join, hjoin, hJensen⟩ :=
      exists_jensen_of_pullback_extension g p U hloc gExt hcomplete hball hdom hmetric
        h3aB hsmall hcurv
    refine ⟨join, ?_, hJensen⟩
    intro x hx y hy
    obtain ⟨hs, hg, hzero, hone, hcore, heq⟩ := hjoin x hx y hy
    exact ⟨hs, hg, hzero, hone, hcore, fun _ => heq⟩


end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
