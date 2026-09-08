import DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.IndexForm
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Frame
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Analysis.ODE.IndexForm.BoundaryValue

open Set Manifold
open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem coeff_jacobi_ode
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (Y : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t)
    (hFdiff : ∀ i, DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t)
    (hYdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ Y t) t)
    (hDYdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => covDerivAlong (I := I) g γ Y s) t) t)
    (hFpar : ∀ i, covDerivAlong (I := I) g γ (F i) t = 0)
    (hY : IsJacobiAt (I := I) g γ Y t)
    (hcard : Fintype.card ι = Module.finrank ℝ (TangentSpace I (γ t)))
    (hON : ∀ i j, g.inner (γ t) (F i t) (F j t) = if i = j then 1 else 0) :
    HasDerivAt (perpCoeff (I := I) g F Y)
      (perpCoeff (I := I) g F (fun s => covDerivAlong (I := I) g γ Y s) t) t ∧
    HasDerivAt (perpCoeff (I := I) g F (fun s => covDerivAlong (I := I) g γ Y s))
      (-(perpCurvOp (I := I) g γ F t) (perpCoeff (I := I) g F Y t)) t := by
  let L : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι := (EuclideanSpace.equiv ι ℝ).symm
  constructor
  · have hpi := hasDerivAt_pi.mpr fun i =>
      parInner_deriv (I := I) le_rfl g γ (F i) Y t hγ
        (hFdiff i) hYdiff (hFpar i)
    exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hpi
  · have hpi : HasDerivAt
        (fun s => (fun i => g.inner (γ s) (F i s)
          (covDerivAlong (I := I) g γ Y s) : ι → ℝ))
        ((EuclideanSpace.equiv ι ℝ)
          (-(perpCurvOp (I := I) g γ F t) (perpCoeff (I := I) g F Y t))) t := by
      rw [hasDerivAt_pi]
      intro i
      let : Nonempty ι := ⟨i⟩
      have hi := parInner_d2 (I := I) le_rfl g γ (F i) Y t hγ
        (hFdiff i) hDYdiff (hFpar i) hY
      have hcoeff : g.inner (γ t) (F i t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
            (Y t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) =
          perpCurvOp (I := I) g γ F t (perpCoeff (I := I) g F Y t) i := by
        rw [parInner_curv_expand (I := I) g γ t F Y hON hcard i, perpCurvOp_apply]
        simp only [perpCoeff_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [g.symm (γ t) (F i t)]
        exact mul_comm _ _
      rw [hcoeff] at hi
      simpa using! hi
    have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hpi
    simpa only [L, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using! h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Fintype ι] [DecidableEq ι] in
theorem jacobi_eq_zero_of_endpoints_eq_zero
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) {U : Set ℝ} {a b : ℝ} (hab : a ≤ b)
    (hU : IsOpen U) (hseg : Icc a b ⊆ U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ U)
    (hJdiff : ∀ t ∈ Icc a b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hDJdiff : ∀ t ∈ Icc a b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hJac : ∀ t ∈ Icc a b, IsJacobiAt (I := I) g γ J t)
    (hJa : J a = 0) (hJb : J b = 0)
    {κ : ℝ} (hκ : κ * (b - a) ^ 2 < (Real.pi / 2) ^ 2)
    (hcurv : ∀ t ∈ Ioo a b,
      g.inner (γ t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) (J t) ≤
        κ * g.inner (γ t) (J t) (J t)) :
    ∀ t ∈ Icc a b, J t = 0 := by
  classical
  cases subsingleton_or_nontrivial E with
  | inl hsub =>
      intro t ht
      exact @Subsingleton.elim E hsub (J t) 0
  | inr hntr =>
      let : Nontrivial E := hntr
      let : NeZero (Module.finrank ℝ E) := ⟨ne_of_gt (Module.finrank_pos (R := ℝ) (M := E))⟩
      have hrank (z : M) : Module.finrank ℝ (TangentSpace I z) = Module.finrank ℝ E :=
        (tangentSpaceModelContinuousLinearEquiv (I := I) z).toLinearEquiv.finrank_eq
      let : NeZero (Module.finrank ℝ (TangentSpace I (γ a))) :=
        ⟨by rw [hrank]; exact NeZero.ne _⟩
      obtain ⟨basis, hbasis⟩ := Tensor0SBundle.exists_orthonormal_basis (I := I) g (γ a)
      obtain ⟨F, _, hFdiff, hFpar, hON⟩ :=
        exists_parallel_frame_on_Icc (I := I)
          g γ hγ hU hab hseg basis hbasis
      let R := perpCurvOp (I := I) g γ F
      let y := perpCoeff (I := I) g F J
      let v := perpCoeff (I := I) g F (fun s => covDerivAlong (I := I) g γ J s)
      have hγat t (ht : t ∈ Icc a b) : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t :=
        (hγ t (hseg ht)).contMDiffAt (hU.mem_nhds (hseg ht))
      have hode t (ht : t ∈ Icc a b) :
          HasDerivAt y (v t) t ∧ HasDerivAt v (-(R t) (y t)) t :=
        coeff_jacobi_ode g γ F J t ((hγat t ht).of_le (by norm_num))
          (fun i => hFdiff i t ht) (hJdiff t ht) (hDJdiff t ht)
          (fun i => hFpar i t ht) (hJac t ht) (by simp only [Fintype.card_fin, hrank]) (hON t ht)
      have hsol : DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn R a b y v :=
        ⟨fun t ht => (hode t ht).1.hasDerivWithinAt,
          fun t ht => (hode t ht).2.hasDerivWithinAt⟩
      have hexp t (ht : t ∈ Icc a b) : (∑ i, y t i • F i t) = J t := by
        simpa only [y, perpCoeff_apply] using
          (gON_expand (I := I) g (γ t) (fun i => F i t) (hON t ht)
            (by simp only [Fintype.card_fin, hrank]) (J t)).symm
      have hinner t (ht : t ∈ Icc a b) :
          g.inner (γ t) (J t) (J t) = (inner ℝ (y t) (y t)) := by
        rw [← hexp t ht]
        exact perpLift_inner (I := I) g F (y t) (y t) t (hON t ht)
      have hupper t (ht : t ∈ Ioo a b) :
          ⟪R t (y t), y t⟫ ≤ κ * ‖y t‖ ^ 2 := by
        have h := perpCurv_inner (I := I) g γ F (y t) (y t) t
        rw [hexp t (Ioo_subset_Icc_self ht)] at h
        change ⟪R t (y t), y t⟫ = _ at h
        rw [h]
        exact (hcurv t ht).trans_eq (by rw [hinner t (Ioo_subset_Icc_self ht), real_inner_self_eq_norm_sq])
      have hzero := hsol.eq_zero_of_endpoints_eq_zero hab
        (perpCoeff_zero (I := I) g F J a hJa) (perpCoeff_zero (I := I) g F J b hJb)
        hκ hupper
      intro t ht
      rw [← hexp t ht, hzero ht]
      simp

end DifferentialGeometry.Geometry.Riemannian.Variation
