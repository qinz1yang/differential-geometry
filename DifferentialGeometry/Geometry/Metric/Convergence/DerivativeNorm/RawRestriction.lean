import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.FiniteJetCongruence
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.MetricRestriction
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Restriction
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Metric.Scaling

set_option autoImplicit false

noncomputable section

open Bundle Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

omit [CompleteSpace E] [T2Space M] in
theorem raw_contMDiffAt_of_open_tensor
    (U : Opens M) (s : ℕ) (A : (y : M) → Tensor0SSpace s I y)
    (AU : Tensor0SField (I := I) (M := U) (n := ∞) s)
    (hA : ∀ (y : U) (v : Fin s → TangentSpace I y), AU y v = A (y : M) v)
    (x : U) :
    letI := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) s
    ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y => (⟨y, A y⟩ : TotalSpace (Tensor0SModel s ℝ E)
        (fun z => Tensor0SSpace s I z))) (x : M) := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) s
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := U) s
  rw [Bundle.contMDiffAt_section]
  apply (contMDiffAt_subtype_iff (x := x)).mp
  have hAU := AU.contMDiff_toFun.contMDiffAt (x := x)
  rw [Bundle.contMDiffAt_section] at hAU
  apply hAU.congr_of_eventuallyEq
  have hnb : {y : U | (y : M) ∈ (chartAt H (x : M)).source} ∈ 𝓝 x :=
    ((chartAt H (x : M)).open_source.preimage continuous_subtype_val).mem_nhds
      (mem_chart_source H (x : M))
  filter_upwards [hnb] with y hy
  have hvalue : AU y = Tensor0SSpace.ofModel (I := I) (x := y)
      (Tensor0SSpace.toModel (A (y : M))) := by
    ext v
    change AU y v = A (y : M) v
    exact hA y v
  change tensor0SModelAt s (x : M) (y : M) (A (y : M)) =
    tensor0SModelAt s x y (AU y)
  rw [hvalue]
  exact (tensor0SModelAt_opens s x y hy (A (y : M))).symm

theorem raw_covariant_derivative_restrict
    (h : SmoothRiemannianMetric I M) (U : Opens M) (s : ℕ)
    (A : (y : M) → Tensor0SSpace s I y)
    (AU : Tensor0SField (I := I) (M := U) (n := ∞) s)
    (hA : ∀ (y : U) (v : Fin s → TangentSpace I y), AU y v = A (y : M) v)
    (x : U) (slots : Fin (s + 1) → TangentSpace I x) :
    totalNabla0SFun s (metricCov (h.restrictOpen U)) AU x slots =
      metricCovariantDerivative h s A (x : M) slots := by
  classical
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) s
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M) (slots 0)
  let V : Fin s → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    fun q => (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M) (slots q.succ)).choose
  have hV (q : Fin s) : V q (x : M) = slots q.succ :=
    (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M) (slots q.succ)).choose_spec
  let XU := restrictOpenTangentSection U X
  let VU := fun q => restrictOpenTangentSection U (V q)
  have hslotsM : (Fin.cons (X (x : M)) (fun q => V q (x : M)) :
      Fin (s + 1) → TangentSpace I (x : M)) = slots := by
    funext q
    refine Fin.cases ?_ (fun p => ?_) q
    · exact hX
    · exact hV p
  have hslotsU : Fin.cons (XU x) (fun q => VU q x) = slots := by
    funext q
    refine Fin.cases ?_ (fun p => ?_) q
    · exact (restrictOpenTangentSection_apply U X x).trans hX
    · exact (restrictOpenTangentSection_apply U (V p) x).trans (hV p)
  have hAM := (raw_contMDiffAt_of_open_tensor U s A AU hA x).of_le
    (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hVM (q : Fin s) : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      (x : M) := (V q).contMDiff.contMDiffAt.of_le (by simp)
  have hl := (totalNabla0SFun_apply_section s (metricCov (h.restrictOpen U)) XU AU x
    (fun q => VU q x)).trans (nabla0SFun_eval_smooth_slots _ XU VU AU x)
  have hr := metricCovariantDerivative_apply_of_contMDiffAt h s A X
    (fun q y => V q y) (x : M) hAM hVM
  rw [hslotsU] at hl
  rw [hslotsM] at hr
  rw [hl, hr]
  have hscalar : (fun y : U => AU y (fun q => VU q y)) =
      fun y : U => A (y : M) (fun q => V q (y : M)) := by
    funext y
    simpa only [VU, restrictOpenTangentSection_apply] using hA y (fun q => VU q y)
  have hf : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => A y (fun q => V q y)) (x : M) :=
    (TensorMultilinear.contMDiffAt_section_apply_one A hAM (fun q y => V q y)
      hVM).mdifferentiableAt (by norm_num)
  apply congrArg₂ (· - ·)
  · rw [hscalar]
    exact (mvfderiv_restrictOpen U _ x (XU x) hf).trans
      (congrArg (fun v : TangentSpace I (x : M) =>
        mvfderiv (I := I) (fun y : M => A y (fun q => V q y)) (x : M) v)
        (restrictOpenTangentSection_apply U X x))
  apply Finset.sum_congr rfl
  intro p _
  rw [hA]
  apply congrArg (A (x : M))
  have hcov := (metricCov_restrictOpen_globalSection h U (V p) x (XU x)).trans
    (congrArg (fun v : TangentSpace I (x : M) =>
      (metricCov h (fun y : M => V p y) (x : M)) v)
      (restrictOpenTangentSection_apply U X x))
  ext q
  by_cases hqp : q = p
  · subst q
    simp only [Function.update_self]
    exact hcov
  · rw [Function.update_of_ne hqp, Function.update_of_ne hqp]
    exact restrictOpenTangentSection_apply U (V q) x

theorem raw_iterated_covariant_derivative_restrict
    (h : SmoothRiemannianMetric I M) (U : Opens M) (s : ℕ)
    (A : (y : M) → Tensor0SSpace s I y)
    (AU : Tensor0SField (I := I) (M := U) (n := ∞) s)
    (hA : ∀ (y : U) (v : Fin s → TangentSpace I y), AU y v = A (y : M) v)
    (k : ℕ) (x : U) (v : Fin (s + k) → TangentSpace I x) :
    iteratedMetricCovariantDerivative h s A k (x : M) v =
      iterCov (h.restrictOpen U) s AU k x v := by
  induction k generalizing x with
  | zero => exact (hA x v).symm
  | succ k ih =>
    change metricCovariantDerivative h (s + k)
        (iteratedMetricCovariantDerivative h s A k) (x : M) v =
      totalNabla0SFun (s + k) (metricCov (h.restrictOpen U))
        (iterCov (h.restrictOpen U) s AU k) x v
    exact (raw_covariant_derivative_restrict h U (s + k)
      (iteratedMetricCovariantDerivative h s A k) (iterCov (h.restrictOpen U) s AU k)
      (fun y w => (ih y w).symm) x v).symm

theorem metricDerivNorm_eq_raw_on_open
    (h : SmoothRiemannianMetric I M) (U : Opens M)
    (gU : SmoothRiemannianMetric I U)
    (A : (y : M) → Tensor0SSpace 2 I y)
    (hA : ∀ (y : U) (v : Fin 2 → TangentSpace I y),
      (metricTensorField gU - metricTensorField (h.restrictOpen U)) y v = A (y : M) v)
    (k : ℕ) (x : U) :
    metricDerivNorm k gU (h.restrictOpen U) (h.restrictOpen U) x =
      tensor0SFiberNorm h (x : M) (2 + k)
        (iteratedMetricCovariantDerivative h 2 A k (x : M)) := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (h.restrictOpen U) x
  have hinv : MetricInverseInBasis (h.restrictOpen U) x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have hh := metricInverseInBasis_of_orthonormal (h.restrictOpen U) basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using hh i j
  rw [metricDerivNorm_eq_iterCov gU (h.restrictOpen U) (h.restrictOpen U) k basis hinv]
  have htensor : iterCov (h.restrictOpen U) 2
      (metricTensorField gU - metricTensorField (h.restrictOpen U)) k x =
        iteratedMetricCovariantDerivative h 2 A k (x : M) := by
    ext v
    exact (raw_iterated_covariant_derivative_restrict h U 2 A _ hA k x v).symm
  rw [htensor]
  exact congrArg Real.sqrt (normSq0S_restrictOpen_apply h U (2 + k) x _)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ F] in
theorem metricDerivNorm_scaled_localPullMetric_eq_raw
    (h : SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric J N)
    (f : M → N) (U : Opens M)
    (hf : IsLocalDiffeomorph I J ∞ (fun x : U => f x))
    (c : ℝ) (hc : 0 < c) (k : ℕ) (x : U) :
    metricDerivNorm k (localPullMetric (scaleMetric c hc g) (fun y : U => f y) hf)
        (h.restrictOpen U) (h.restrictOpen U) x =
      tensor0SFiberNorm h (x : M) (2 + k)
        (iteratedMetricCovariantDerivative h 2
          (fun p : M =>
            ((continuousMultilinearCurryFin1 ℝ (TangentSpace I p) ℝ).symm.toContinuousLinearMap.comp
              (c • localPullInner g f p - h.inner p)).uncurryLeft)
          k (x : M)) := by
  apply metricDerivNorm_eq_raw_on_open h U _ _ ?_ k x
  intro y v
  simp only [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
    metricTensorField_apply, localPullMetric_inner, scaleMetric_inner,
    DifferentialGeometry.mfderiv_restrict_open]
  change c * g.inner (f (y : M))
      (mfderiv I J f (y : M) (v 0)) (mfderiv I J f (y : M) (v 1)) -
      h.inner (y : M) (v 0) (v 1) =
    ((c • localPullInner (I := I) g f (y : M) - h.inner (y : M)) :
      TangentSpace I (y : M) →L[ℝ] TangentSpace I (y : M) →L[ℝ] ℝ) (v 0) (v 1)
  rfl

end DifferentialGeometry.CheegerGromovCompactness
