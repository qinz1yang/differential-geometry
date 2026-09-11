import DifferentialGeometry.Analysis.ODE.IndexForm.SmoothNegativeDirection
import DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.IndexForm
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation.Minimizer

set_option autoImplicit false

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem contDiffOn_perpCoeff
    {ι : Type*} [Fintype ι] {n : ℕ∞}
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (F : ι → ∀ t, TangentSpace I (γ t)) (Y : ∀ t, TangentSpace I (γ t))
    {U : Set ℝ}
    (hF : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent n
      (fun t => (TotalSpace.mk' E (γ t) (F i t) : TangentBundle I M)) U)
    (hY : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent n
      (fun t => (TotalSpace.mk' E (γ t) (Y t) : TangentBundle I M)) U) :
    ContDiffOn ℝ n (perpCoeff (I := I) g F Y) U := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hi (i : ι) : ContDiffOn ℝ n (fun t => g.inner (γ t) (F i t) (Y t)) U := by
    have h := ContMDiffOn.inner_bundle (F := E) (B := M)
      (E := (TangentSpace I : M → Type _)) (b := γ) (v := F i) (w := Y) (hF i) hY
    exact contMDiffOn_iff_contDiffOn.mp h
  have hpi : ContDiffOn ℝ n (fun t => fun i => g.inner (γ t) (F i t) (Y t)) U :=
    contDiffOn_pi.mpr hi
  exact (EuclideanSpace.equiv ι ℝ).symm.contDiff.comp_contDiffOn hpi

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiff_indexForm_neg_of_isJacobiAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t, TangentSpace I (γ t)) {L c : ℝ} {U : Set ℝ}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hJ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (TotalSpace.mk' E (γ t) (J t) : TangentBundle I M)) U)
    (hU : IsOpen U) (hsub : Icc (0 : ℝ) L ⊆ U)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hJac : ∀ t ∈ Ioo (0 : ℝ) L, IsJacobiAt (I := I) g γ J t)
    (hvel : 0 < g.inner (γ 0) (curveVelocity (I := I) γ 0) (curveVelocity (I := I) γ 0))
    (hc : c ∈ Ioo (0 : ℝ) L) (hJ0 : J 0 = 0) (hJc : J c = 0)
    (hDJ0 : covDerivAlong (I := I) g γ J 0 ≠ 0) :
    ∃ V : ∀ t, TangentSpace I (γ t),
      ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M)) ∧
      (∀ t ∈ Icc (0 : ℝ) L, g.inner (γ t) (V t) (curveVelocity (I := I) γ t) = 0) ∧
      V 0 = 0 ∧ V L = 0 ∧ indexForm (I := I) g γ 0 L V V < 0 := by
  classical
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hL : 0 < L := hc.1.trans hc.2
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hL.le⟩
  have hcc : c ∈ Icc (0 : ℝ) L := Ioo_subset_Icc_self hc
  have hγ2 : ContMDiff 𝓘(ℝ, ℝ) I 2 γ := hγ.of_le (WithTop.coe_le_coe.mpr le_top)
  let DJ : ∀ t, TangentSpace I (γ t) := fun t => covDerivAlong (I := I) g γ J t
  have hDJ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (TotalSpace.mk' E (γ t) (DJ t) : TangentBundle I M)) U := by
    intro t ht
    exact (contMDiffAt_covDerivAlong (I := I) g (m := ⊤) (n := ⊤) (by simp)
      ((hJ t ht).contMDiffAt (hU.mem_nhds ht))).contMDiffWithinAt
  have hJmdiff t (ht : t ∈ Icc (0 : ℝ) L) :
      MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
        (fun r => (TotalSpace.mk' E (γ r) (J r) : TangentBundle I M)) t :=
    ((hJ t (hsub ht)).contMDiffAt (hU.mem_nhds (hsub ht))).mdifferentiableAt (by simp)
  have hDJmdiff t (ht : t ∈ Icc (0 : ℝ) L) :
      MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
        (fun r => (TotalSpace.mk' E (γ r) (DJ r) : TangentBundle I M)) t :=
    ((hDJ t (hsub ht)).contMDiffAt (hU.mem_nhds (hsub ht))).mdifferentiableAt (by simp)
  have hJdiff t (ht : t ∈ Icc (0 : ℝ) L) :=
    (mdifferentiableAt_tangentField_iff.mp (hJmdiff t ht)).2
  have hDJdiff t (ht : t ∈ Icc (0 : ℝ) L) :=
    (mdifferentiableAt_tangentField_iff.mp (hDJmdiff t ht)).2
  have hJacInterior : ∀ t ∈ interior (Icc (0 : ℝ) L), IsJacobiAt (I := I) g γ J t := by
    simpa only [interior_Icc] using hJac
  have hinner0 : g.inner (γ 0) (J 0) (curveVelocity (I := I) γ 0) = 0 := by
    simp only [hJ0, map_zero, zero_apply]
  have hinnerc : g.inner (γ c) (J c) (curveVelocity (I := I) γ c) = 0 := by
    simp only [hJc, map_zero, zero_apply]
  have hJperp t (ht : t ∈ Icc (0 : ℝ) L) :
      g.inner (γ t) (J t) (curveVelocity (I := I) γ t) = 0 :=
    inner_curveVelocity_eq_zero_of_isJacobiAt (I := I) g γ J (convex_Icc _ _)
      (fun t _ => hγ2 t) (hgeo.mono interior_subset) hJmdiff hDJmdiff hJacInterior
      h0 hcc ht hc.1.ne hinner0 hinnerc
  have hDJperp : g.inner (γ 0) (DJ 0) (curveVelocity (I := I) γ 0) = 0 :=
    inner_covDerivAlong_curveVelocity_eq_zero_of_isJacobiAt (I := I) g γ J
      (convex_Icc _ _) (fun t _ => hγ2 t) (hgeo.mono interior_subset)
      hJmdiff hDJmdiff hJacInterior h0 hcc h0 hc.1.ne (hinner0.trans hinnerc.symm)
  have hveldiff t : DifferentiableAt ℝ
      (chartRepAt (I := I) γ (curveVelocity (I := I) γ) t) t :=
    differentiableAt_chartRepAt_curveVelocity (hγ2 t)
  have hvelpar t (ht : t ∈ Icc (0 : ℝ) L) :
      covDerivAlong (I := I) g γ (curveVelocity (I := I) γ) t = 0 :=
    covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 (I := I) g γ t
      (hγ2 t) (hgeo.hasGeodesicEquationAt ht)
  have hspeed t (ht : t ∈ Icc (0 : ℝ) L) :
      0 < g.inner (γ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := by
    rw [parallel_transport_preserves_inner_product (I := I) g γ (N := 2) (by norm_num) hγ2
      (curveVelocity (I := I) γ) (curveVelocity (I := I) γ)
      (fun t _ => hveldiff t) (fun t _ => hveldiff t) hvelpar hvelpar t ht]
    exact hvel
  obtain ⟨F, hFdiff, hFpar, hON, hFperp, hFbundle⟩ :=
    exists_perp_par_pos (I := I) g γ hγ hL hgeo hvel
  let e : Fin (Module.finrank ℝ E - 1) → ∀ t, TangentSpace I (γ t) := fun i => (F i).toFun
  let R := perpCurvOp (I := I) g γ e
  let y := perpCoeff (I := I) g e J
  let v := perpCoeff (I := I) g e DJ
  have hR : ContDiff ℝ ∞ R :=
    perpCurv_smooth (I := I) g γ hγ e (fun i => hFbundle i)
  have hy : ContDiffOn ℝ ∞ y U :=
    contDiffOn_perpCoeff (I := I) g e J (fun i => (hFbundle i).contMDiffOn) hJ
  have hv : ContDiffOn ℝ ∞ v U :=
    contDiffOn_perpCoeff (I := I) g e DJ (fun i => (hFbundle i).contMDiffOn) hDJ
  have hode t (ht : t ∈ Ioo (0 : ℝ) L) :
      HasDerivAt y (v t) t ∧ HasDerivAt v (-(R t) (y t)) t := by
    have ht' := Ioo_subset_Icc_self ht
    exact perpCoeff_ode (I := I) (n := ∞) (by simp) g γ e J t (hγ t)
      (fun i => hFdiff i t ht') (hJdiff t ht') (hDJdiff t ht')
      (fun i => hFpar i t ht') (hJac t ht) (by simp) (hspeed t ht')
      (fun i => hFperp t ht' i) (hJperp t ht') (fun i j => hON t ht' i j)
  have hacc : ContinuousOn (fun t => -(R t) (y t)) (Icc (0 : ℝ) L) :=
    (hR.continuous.continuousOn.clm_apply (hy.continuousOn.mono hsub)).neg
  have hsol : DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn R 0 L y v :=
    DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.of_hasDerivAt_Ioo
      (hy.continuousOn.mono hsub) (hv.continuousOn.mono hsub) hacc hode
  have hy0 : y 0 = 0 := perpCoeff_zero (I := I) g e J 0 hJ0
  have hyc : y c = 0 := perpCoeff_zero (I := I) g e J c hJc
  have hv0 : v 0 ≠ 0 :=
    perpCoeff_ne_zero (I := I) g e DJ 0 (by simp) hvel
      (fun i => hFperp 0 h0 i) hDJperp (fun i j => hON 0 h0 i j) hDJ0
  have hyd : HasDerivAt y (deriv y 0) 0 :=
    ((hy 0 (hsub h0)).contDiffAt (hU.mem_nhds (hsub h0))).differentiableAt (by simp)
      |>.hasDerivAt
  have hydv : HasDerivAt y (v 0) 0 :=
    hyd.congr_deriv ((hyd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hL 0 h0)).symm.trans
      ((hsol.deriv_fst 0 h0).derivWithin (uniqueDiffOn_Icc hL 0 h0)))
  have hne : ∃ t ∈ Icc (0 : ℝ) L, y t ≠ 0 := by
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), y t ≠ 0 := by
      simpa only [hy0] using hydv.eventually_ne hv0
    have hgt : ∀ᶠ t in 𝓝[>] (0 : ℝ), y t ≠ 0 :=
      hev.filter_mono (nhdsWithin_mono _ (fun t ht => by
        simpa only [mem_compl_iff, mem_singleton_iff] using (ne_of_gt ht)))
    have hlt : Iio L ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hL)
    have hboth : ∀ᶠ t in 𝓝[>] (0 : ℝ), y t ≠ 0 ∧ 0 < t ∧ t < L := by
      filter_upwards [hgt, self_mem_nhdsWithin, hlt] with t ht ht0 htL
      exact ⟨ht, ht0, htL⟩
    obtain ⟨t, ht, ht0, htL⟩ := hboth.exists
    exact ⟨t, ⟨ht0.le, htL.le⟩, ht⟩
  obtain ⟨W, hW, hW0, hWL, hWneg⟩ :=
    hsol.exists_contDiff_indexForm_neg hc hR.continuous.continuousOn
      (fun t _ => perpCurv_symm (I := I) g γ e t) hy hU hsub hy0 hyc hne
  let V : ∀ t, TangentSpace I (γ t) := fun t => perpFrameLift (I := I) e W t
  have hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M)) :=
    perpLift_smooth (I := I) hγ e W hW (fun i => hFbundle i)
  have hVperp t (ht : t ∈ Icc (0 : ℝ) L) :
      g.inner (γ t) (V t) (curveVelocity (I := I) γ t) = 0 :=
    perpLift_perp (I := I) g e W t (curveVelocity (I := I) γ t)
      (fun i => hFperp t ht i)
  have hindex : indexForm (I := I) g γ 0 L V V =
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L W (deriv W) W (deriv W) := by
    exact perpLift_indexForm (I := I) g γ e W W 0 L
      (fun t _ => hW.differentiable (by simp) t)
      (fun t _ => hW.differentiable (by simp) t)
      (fun i t ht => hFdiff i t (by simpa only [uIcc_of_le hL.le] using ht))
      (fun i t ht => hFpar i t (by simpa only [uIcc_of_le hL.le] using ht))
      (fun t ht i j => hON t (by simpa only [uIcc_of_le hL.le] using ht) i j)
  exact ⟨V, hV, hVperp, perpLift_zero (I := I) e W 0 hW0,
    perpLift_zero (I := I) e W L hWL, hindex.trans_lt hWneg⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem jacobi_field_ne_zero_of_minimising_geodesic
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t, TangentSpace I (γ t)) {L c : ℝ} {U : Set ℝ}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hJ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (TotalSpace.mk' E (γ t) (J t) : TangentBundle I M)) U)
    (hU : IsOpen U) (hsub : Icc (0 : ℝ) L ⊆ U)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hJac : ∀ t ∈ Ioo (0 : ℝ) L, IsJacobiAt (I := I) g γ J t)
    (hunit : g.inner (γ 0) (curveVelocity (I := I) γ 0) (curveVelocity (I := I) γ 0) = 1)
    (hmin : ∀ η : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = γ 0 → η L = γ L →
      arcLength (I := I) g γ 0 L ≤ arcLength (I := I) g η 0 L)
    (hc : c ∈ Ioo (0 : ℝ) L) (hJ0 : J 0 = 0)
    (hDJ0 : covDerivAlong (I := I) g γ J 0 ≠ 0) :
    J c ≠ 0 := by
  intro hJc
  have hL : 0 < L := hc.1.trans hc.2
  obtain ⟨V, hV, hVperp, hV0, hVL, hneg⟩ :=
    exists_contMDiff_indexForm_neg_of_isJacobiAt (I := I) g γ J hγ hJ hU hsub hgeo
      hJac (by rw [hunit]; exact zero_lt_one) hc hJ0 hJc hDJ0
  have hγ2 : ContMDiff 𝓘(ℝ, ℝ) I 2 γ := hγ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hveldiff t : DifferentiableAt ℝ
      (chartRepAt (I := I) γ (curveVelocity (I := I) γ) t) t :=
    differentiableAt_chartRepAt_curveVelocity (hγ2 t)
  have hvelpar t (ht : t ∈ Icc (0 : ℝ) L) :
      covDerivAlong (I := I) g γ (curveVelocity (I := I) γ) t = 0 :=
    covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 (I := I) g γ t
      (hγ2 t) (hgeo.hasGeodesicEquationAt ht)
  have hUnit t (ht : t ∈ Icc (0 : ℝ) L) :
      g.inner (γ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) = 1 := by
    rw [parallel_transport_preserves_inner_product (I := I) g γ (N := 2) (by norm_num) hγ2
      (curveVelocity (I := I) γ) (curveVelocity (I := I) γ)
      (fun t _ => hveldiff t) (fun t _ => hveldiff t) hvelpar hvelpar t ht]
    exact hunit
  have hnonneg := indexForm_nonneg_of_minimising_geodesic (I := I) g γ L V hL.le
    (hV.of_le (WithTop.coe_le_coe.mpr le_top)) hgeo hmin hUnit hVperp hV0 hVL
  exact (not_lt_of_ge hnonneg) hneg

end DifferentialGeometry.Geometry.Riemannian.Variation
