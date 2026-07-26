import DifferentialGeometry.Analysis.ODE.IndexFormNegativeSmooth
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrameIndex
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariationMinimiser
import DifferentialGeometry.Geometry.Comparison.Variation.VariationFieldSmooth
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint
import DifferentialGeometry.Geometry.Exponential.IntrinsicSmooth

set_option autoImplicit false

/-!
# A minimizing geodesic has no interior conjugate vector

The proof realizes a conjugate Jacobi field in a parallel perpendicular frame,
uses the abstract negative-index smoothing theorem, and contradicts the
second-variation nonnegativity of a length-minimizing geodesic.
-/

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff RealInnerProductSpace Bundle

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A unit-speed intrinsic geodesic that minimizes length on `[0,L]`, for
`L > 0`, has no conjugate vector at any interior radial time. -/
theorem not_conj_of_min_len
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (u : E)
    (hunit : g.inner p u u = 1)
    (L : ℝ) (hL : 0 < L)
    (hmin : ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = p →
      η L = intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u) L →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u)) 0 L ≤
        arcLength (I := I) g η 0 L)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) L) :
    ¬ IsConjVec (I := I) g hEnorm p (c • u) := by
  classical
  intro hconj
  obtain ⟨z, hz, hJc_raw⟩ :=
    conjVec_jacobi_at (I := I) g hEnorm p u hc.1.ne' hconj
  let f : ℝ → ℝ → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from u + s • z) t
  let γ : ℝ → M := fun t => f 0 t
  have hγ :
      γ = intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u) := by
    funext t
    simp only [γ, f, zero_smul, add_zero]
  let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f s t) 0 (1 : ℝ)
  let DJ : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t => covDerivAlong (I := I) g γ J t
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
    have hvar := intrinsicVar_smooth (I := I) g hEnorm p u 0
    have hincl : ContMDiff 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => ((0 : ℝ), t)) :=
      contMDiff_const.prodMk contMDiff_id
    simpa only [γ, f, Function.comp_apply, zero_smul, smul_zero, add_zero] using
      hvar.comp hincl
  have hgeo : IsGeodesic (I := I) g γ := by
    simpa only [γ, f, zero_smul, add_zero] using
      intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u)
  have hf_infty :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : ℝ × ℝ => f q.1 q.2) := by
    simpa only [f] using
      intrinsicVar_smooth (I := I) g hEnorm p u z
  have hf_smooth : IsSmoothVariation (I := I) f :=
    hf_infty.of_le ENat.LEInfty.out
  have hJ_bundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (J t)) := by
    simpa only [γ, J] using
      varField_smooth (I := I) f hf_infty
  have hJdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t := by
    simpa only [γ, J] using
      variationField_chartRep_differentiableAt
        (I := I) g f hf_smooth t
  have hDJdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) γ DJ t) t := by
    simpa only [γ, J, DJ] using
      variationField_covDeriv_chartRep_differentiableAt
        (I := I) g f hf_smooth t
  have hJac : IsJacobiAlong (I := I) g γ J := by
    rw [hγ]
    simpa only [J, f] using
      intrinsic_jacobi (I := I) g hEnorm p u z
  have hJ0 : J 0 = 0 := by
    simpa only [γ, f, J, zero_smul, add_zero] using
      jacobiVar_zero (I := I) g hEnorm p u z
  have hJc : J c = 0 := by
    simpa only [γ, f, J] using hJc_raw
  have hJperp :
      ∀ t, g.inner (γ t) (J t) (curveVelocity (I := I) γ t) = 0 :=
    jacobi_perp_of_ends (I := I) g γ J hc.1.ne'
      hγ_smooth hgeo hJdiff hDJdiff hJac hJ0 hJc
  have hunit0 :
      g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 1 := by
    have hγ0 : γ 0 = p := by
      rw [hγ]
      simpa only using
        intrinsicGeodesic_zero (I := I) g hEnorm p
          (show TangentSpace I p from u)
    have hvel0 : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = u := by
      rw [hγ]
      simpa only using
        intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p
          (show TangentSpace I p from u)
    rw [hγ0]
    change g.inner p
      (show E from mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ))
      (show E from mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 1
    rw [hvel0]
    exact hunit
  obtain ⟨F, hFdiff, hFpar, hON, hFperp, hFbundle⟩ :=
    exists_parallel_perp_frame (I := I) g γ hγ_smooth
      (L := L) hL (hgeo.isGeodesicOn (Icc 0 L)) hunit0
  let e : Fin (Module.finrank ℝ E - 1) →
      ∀ t : ℝ, TangentSpace I (γ t) :=
    fun i => (F i).toFun
  let R : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCurvOp (I := I) g γ e
  let y : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCoeff (I := I) g e J
  let v : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCoeff (I := I) g e DJ
  have hspeed (t : ℝ) :
      0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by
    have hsq :=
      intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p
        (show TangentSpace I p from u) t
    have hsq' :
        g.inner (γ t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) = 1 := by
      rw [hγ]
      simpa only [curveVelocity] using hsq.trans hunit
    rw [hsq']
    exact zero_lt_one
  have hode (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      HasDerivAt y (v t) t ∧
        HasDerivAt v (-(R t) (y t)) t := by
    simpa only [y, v, R, e, DJ] using
      perpCoeff_ode (I := I) (n := ∞) (by simp) g γ e J t
        hγ_smooth.contMDiffAt
        (fun i => hFdiff i t ht)
        (hJdiff t) (hDJdiff t)
        (fun i => hFpar i t ht)
        (hJac t) (by simp) (hspeed t)
        (fun i => hFperp t ht i)
        (hJperp t) (fun i j => hON t ht i j)
  have hsol : IsJacobiSolOn R 0 L y v :=
    { deriv_fst := fun t ht => (hode t ht).1.hasDerivWithinAt
      deriv_snd := fun t ht => (hode t ht).2.hasDerivWithinAt }
  have hR_smooth : ContDiff ℝ ∞ R := by
    simpa only [R, e] using
      perpCurv_smooth (I := I) g γ hγ_smooth e
        (fun i => hFbundle i)
  have hR_symm :
      ∀ t, ∀ x x' : EuclideanSpace ℝ
        (Fin (Module.finrank ℝ E - 1)),
        ⟪R t x, x'⟫ = ⟪x, R t x'⟫ := by
    intro t x x'
    simpa only [R, e] using
      perpCurv_symm (I := I) g γ e t x x'
  have hy_smooth : ContDiff ℝ ∞ y := by
    simpa only [y, e] using
      perpCoeff_smooth (I := I) g e J
        (fun i => hFbundle i) hJ_bundle
  have hy0 : y 0 = 0 := by
    exact perpCoeff_zero (I := I) g e J 0 hJ0
  have hyc : y c = 0 := by
    exact perpCoeff_zero (I := I) g e J c hJc
  have hderiv :
      ∀ t ∈ Icc (0 : ℝ) L, deriv y t = v t :=
    fun t ht => (hode t ht).1.deriv
  have hDJ0 : (DJ 0 : E) = z := by
    change (covDerivAlong (I := I) g γ J 0 : E) = z
    have hcurve_ev :
        γ =ᶠ[𝓝 (0 : ℝ)]
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u) :=
      Filter.Eventually.of_forall fun t => congrFun hγ t
    have hfield_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
        (J t : E) =
          (show TangentSpace I
              (intrinsicGeodesic (I := I) g hEnorm p
                (show TangentSpace I p from u) t) from
            mfderiv 𝓘(ℝ, ℝ) I
              (fun s : ℝ =>
                intrinsicGeodesic (I := I) g hEnorm p
                  (show TangentSpace I p from u + s • z) t)
              0 (1 : ℝ) : E) := by
      filter_upwards with t
      rfl
    have htransport :=
      covDerivAlong_congr_curve (I := I) g J
        (fun t : ℝ =>
          show TangentSpace I
              (intrinsicGeodesic (I := I) g hEnorm p
                (show TangentSpace I p from u) t) from
            mfderiv 𝓘(ℝ, ℝ) I
              (fun s : ℝ =>
                intrinsicGeodesic (I := I) g hEnorm p
                  (show TangentSpace I p from u + s • z) t)
              0 (1 : ℝ))
        hcurve_ev hfield_ev
    exact htransport.trans
      (intrinsic_jacobi_d0 (I := I) g hEnorm p u z)
  have hveldiff :
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ (curveVelocity (I := I) γ) 0) 0 := by
    simpa only [curveVelocity] using
      velocity_chartRepAt_differentiableAt (I := I) γ hγ_smooth 0
  have hvelpar :
      covDerivAlong (I := I) g γ (curveVelocity (I := I) γ) 0 = 0 :=
    (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
      (I := I) g γ 0 hγ_smooth).mpr (hgeo.hasGeodesicEquationAt 0)
  have hinnerDeriv :
      HasDerivAt
        (fun t : ℝ =>
          g.inner (γ t) (curveVelocity (I := I) γ t) (J t))
        (g.inner (γ 0) (curveVelocity (I := I) γ 0) (DJ 0)) 0 := by
    simpa only [DJ] using
      parInner_deriv (I := I) (n := ∞) (by simp) g γ
        (curveVelocity (I := I) γ) J 0
        hγ_smooth.contMDiffAt hveldiff (hJdiff 0) hvelpar
  have hinnerZero :
      (fun t : ℝ =>
        g.inner (γ t) (curveVelocity (I := I) γ t) (J t)) =
        fun _ : ℝ => 0 := by
    funext t
    rw [g.symm]
    exact hJperp t
  have hDJperp :
      g.inner (γ 0) (DJ 0) (curveVelocity (I := I) γ 0) = 0 := by
    have hzero :
        g.inner (γ 0) (curveVelocity (I := I) γ 0) (DJ 0) = 0 := by
      rw [hinnerZero] at hinnerDeriv
      exact hinnerDeriv.unique (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
    rw [g.symm]
    exact hzero
  have hDJ0_ne : DJ 0 ≠ 0 := by
    intro hzero
    apply hz
    rw [← hDJ0]
    exact hzero
  have hv0_ne : v 0 ≠ 0 := by
    exact perpCoeff_ne_zero (I := I) g e DJ 0
      (by simp) (hspeed 0)
      (fun i => hFperp 0 ⟨le_rfl, hL.le⟩ i)
      hDJperp (fun i j => hON 0 ⟨le_rfl, hL.le⟩ i j) hDJ0_ne
  have hne : ∃ t ∈ Icc (0 : ℝ) L, y t ≠ 0 := by
    have hev : {t : ℝ | y t ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := by
      simpa only [hy0] using
        ((hode 0 ⟨le_rfl, hL.le⟩).1.eventually_ne hv0_ne :
          ∀ᶠ t in 𝓝[≠] (0 : ℝ), y t ≠ 0)
    obtain ⟨U, hU, hUsub⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    let t : ℝ := min (ε / 2) (L / 2)
    have htpos : 0 < t := by
      exact lt_min (by linarith) (by linarith)
    have htε : t < ε :=
      (min_le_left (ε / 2) (L / 2)).trans_lt (by linarith)
    have htL : t < L :=
      (min_le_right (ε / 2) (L / 2)).trans_lt (by linarith)
    refine ⟨t, ⟨htpos.le, htL.le⟩, ?_⟩
    apply hUsub
    refine ⟨hball ?_, ?_⟩
    · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos] using htε
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using htpos.ne'
  obtain ⟨W, hW_smooth, hW0, hWL, hWneg⟩ :=
    hsol.exists_smooth_neg_on hc hR_smooth.continuous.continuousOn
      hR_symm hy_smooth hderiv hy0 hyc hne
  let V : ℝ → E := fun t =>
    (perpFrameLift (I := I) e W t : E)
  have hV_bundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (V t)) := by
    simpa only [V] using
      perpLift_smooth (I := I) hγ_smooth e W hW_smooth
        (fun i => hFbundle i)
  have hVperp :
      ∀ t ∈ Icc (0 : ℝ) L,
        g.inner (γ t) (V t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 0 := by
    intro t ht
    simpa only [V, curveVelocity] using
      perpLift_perp (I := I) g e W t
        (curveVelocity (I := I) γ t)
        (fun i => hFperp t ht i)
  have hV0 : V 0 = 0 := by
    exact perpLift_zero (I := I) e W 0 hW0
  have hVL : V L = 0 := by
    exact perpLift_zero (I := I) e W L hWL
  have hindex_eq :
      indexForm (I := I) g γ 0 L V V =
        DifferentialGeometry.Analysis.ODE.indexForm R 0 L
          W (deriv W) W (deriv W) := by
    have h0L : uIcc (0 : ℝ) L = Icc (0 : ℝ) L :=
      uIcc_of_le hL.le
    simpa only [V, R, e] using
      perpLift_indexForm (I := I) g γ e W W 0 L
        (fun t _ => hW_smooth.differentiable (by simp) t)
        (fun t _ => hW_smooth.differentiable (by simp) t)
        (fun i t ht => hFdiff i t (by simpa only [h0L] using ht))
        (fun i t ht => hFpar i t (by simpa only [h0L] using ht))
        (fun t ht i j => hON t (by simpa only [h0L] using ht) i j)
  have hgeom_neg : indexForm (I := I) g γ 0 L V V < 0 := by
    rw [hindex_eq]
    exact hWneg
  have hUnit :
      ∀ t ∈ Icc (0 : ℝ) L,
        g.inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1 := by
    intro t _
    have hsq :=
      intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p
        (show TangentSpace I p from u) t
    rw [hγ]
    simpa only [hunit] using hsq
  have hminγ :
      ∀ η : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
        η 0 = γ 0 → η L = γ L →
        arcLength (I := I) g γ 0 L ≤
          arcLength (I := I) g η 0 L := by
    intro η hη hη0 hηL
    have hη0' : η 0 = p := hη0.trans (by
      rw [hγ]
      exact intrinsicGeodesic_zero (I := I) g hEnorm p
        (show TangentSpace I p from u))
    have hηL' :
        η L = intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u) L := hηL.trans (by rw [hγ])
    simpa only [hγ] using hmin η hη hη0' hηL'
  have hnonneg :
      0 ≤ indexForm (I := I) g γ 0 L V V :=
    indexForm_nonneg_of_minimising_geodesic
      (I := I) g hEnorm γ L V hL
      hγ_smooth hV_bundle (hgeo.isGeodesicOn (Icc 0 L)) hminγ
      hUnit hVperp hV0 hVL
  exact (not_lt_of_ge hnonneg) hgeom_neg

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A unit-speed intrinsic geodesic that minimizes length on `[0,1]` has no
conjugate vector at any interior radial time. -/
theorem not_conj_of_min
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (u : E)
    (hunit : g.inner p u u = 1)
    (hmin : ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 1) →
      η 0 = p →
      η 1 = intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u) 1 →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u)) 0 1 ≤
        arcLength (I := I) g η 0 1)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    ¬ IsConjVec (I := I) g hEnorm p (c • u) :=
  not_conj_of_min_len (I := I) g hEnorm p u hunit 1
    (by norm_num) hmin hc

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
