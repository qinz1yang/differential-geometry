import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.FiniteJetBounds
import DifferentialGeometry.Analysis.Calculus.Inverse.FiniteFamilyBounds
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.LocalJacobi
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.CoerciveBilinearInverse

set_option autoImplicit false

noncomputable section

open Bundle Set Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

namespace DifferentialGeometry.CheegerGromovCompactness

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private local instance normalChartFormNormedAdd : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance normalChartFormNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private def rotateForm (Q : E ≃ₗᵢ[ℝ] E) :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (E →L[ℝ] ℝ)
    (ContinuousLinearMap.precomp ℝ Q.toContinuousLinearEquiv.toContinuousLinearMap)).comp
      ((ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ)).flip
        Q.toContinuousLinearEquiv.toContinuousLinearMap)

private theorem rotateForm_apply (Q : E ≃ₗᵢ[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    rotateForm Q B v w = B (Q v) (Q w) := rfl

private theorem rotateForm_norm_le (Q : E ≃ₗᵢ[ℝ] E) : ‖rotateForm Q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro B
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg B) (norm_nonneg v))
  intro w
  simpa only [rotateForm_apply, Q.norm_map] using B.le_opNorm₂ (Q v) (Q w)

variable [CompleteSpace E]

private theorem gramCLM_norm_le : ‖(IsCoercive.gramCLM :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro B
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro v
  change ‖(InnerProductSpace.toDual ℝ E).symm (B v)‖ ≤ ‖B‖ * ‖v‖
  rw [LinearIsometryEquiv.norm_map]
  exact B.le_opNorm v

private theorem inverse_gram_norm_le {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B v v) :
    IsUnit (IsCoercive.gramCLM B) ∧ ‖Ring.inverse (IsCoercive.gramCLM B)‖ ≤ 2 := by
  have hco : IsCoercive B := ⟨1 / 2, by norm_num, fun v => by
    simpa only [pow_two, mul_assoc] using hB v⟩
  refine ⟨IsCoercive.gramCLM_isUnit hco, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  have h := hco.sharp_norm_le (c := 1 / 2) (by norm_num)
    (fun w => by simpa only [pow_two, mul_assoc] using hB w)
    (InnerProductSpace.toDual ℝ E v)
  rw [hco.sharp_eq_inverse] at h
  simpa only [IsCoercive.gramCLM_apply, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.norm_map, one_div, inv_inv, Nat.cast_ofNat] using h

omit [CompleteSpace E] in
private theorem rotated_metric_derivative_le
    (Q : E ≃ₗᵢ[ℝ] E) (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ContDiff ℝ ∞ B) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => rotateForm Q (B (Q y))) x‖ ≤
      ‖iteratedFDeriv ℝ k B (Q x)‖ := by
  have h := (rotateForm Q).norm_iteratedFDeriv_comp_left (x := x)
    (hB.comp Q.contDiff).contDiffAt (show (k : ℕ∞ω) ≤ ∞ from by simp)
  refine h.trans ?_
  calc
    ‖rotateForm Q‖ * ‖iteratedFDeriv ℝ k (B ∘ Q) x‖ ≤
        1 * ‖iteratedFDeriv ℝ k (B ∘ Q) x‖ :=
      mul_le_mul_of_nonneg_right (rotateForm_norm_le Q) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ k B (Q x)‖ := by
      rw [one_mul, Q.norm_iteratedFDeriv_comp_right]

private theorem inverse_metric_derivative_le
    (K : ℕ) (D : ℝ) (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ContDiff ℝ ∞ B) (U : Set E) (hU : IsOpen U)
    (hlower : ∀ x ∈ U, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B x v v)
    (hderiv : ∀ k, k ≤ K → ∀ x ∈ U, ‖iteratedFDeriv ℝ k B x‖ ≤ D) :
    ContDiffOn ℝ K (fun x => Ring.inverse (IsCoercive.gramCLM (B x))) U ∧
      ∀ k, k ≤ K → ∀ x ∈ U,
        ‖iteratedFDeriv ℝ k (fun y => Ring.inverse (IsCoercive.gramCLM (B y))) x‖ ≤
          (K.factorial : ℝ) * ((K.factorial : ℝ) * 2 ^ (K + 1)) * max D 1 ^ K := by
  let G : E → E →L[ℝ] E := fun x => IsCoercive.gramCLM (B x)
  have hG : ContDiff ℝ ∞ G := (IsCoercive.gramCLM (F := E)).contDiff.comp hB
  have hGderiv : ∀ k, 1 ≤ k → k ≤ K → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ k G x‖ ≤ D := by
    intro k _ hk x hx
    have hb := IsCoercive.gramCLM.norm_iteratedFDeriv_comp_left
      (x := x) hB.contDiffAt (show (k : ℕ∞ω) ≤ ∞ from by simp)
    refine hb.trans ((mul_le_mul_of_nonneg_right gramCLM_norm_le (norm_nonneg _)).trans ?_)
    simpa only [one_mul] using hderiv k hk x hx
  have h := Analysis.uniform_iteratedFDeriv_ringInverse_bound K 2 D
    (fun _ : Unit => G) U hU
    (fun _ => hG.contDiffOn.of_le (by simp))
    (fun _ x hx => (inverse_gram_norm_le (hlower x hx)).1)
    (fun _ x hx => (inverse_gram_norm_le (hlower x hx)).2)
    (fun _ => hGderiv)
  refine ⟨h.1 (), ?_⟩
  intro k hk x hx
  simpa only [max_eq_left (by norm_num : (1 : ℝ) ≤ 2)] using h.2 () k hk x hx

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem pullbackMetricCoefficients_rotate
    (g : SmoothRiemannianMetric I M) (F : E → M)
    (hF : ContMDiff 𝓘(ℝ, E) I ∞ F) (Q : E ≃ₗᵢ[ℝ] E) (x : E) :
    pullbackMetricCoefficients g (F ∘ Q) x =
      rotateForm Q (pullbackMetricCoefficients g F (Q x)) := by
  have hQ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) Q x :=
    Q.toContinuousLinearEquiv.toContinuousLinearMap.mdifferentiableAt
  have hd := mfderiv_comp x (hF.contMDiffAt.mdifferentiableAt (by simp)) hQ
  have hdQ : fderiv ℝ (fun y => Q y) x = Q.toContinuousLinearEquiv.toContinuousLinearMap :=
    Q.toContinuousLinearEquiv.hasFDerivAt.fderiv
  rw [mfderiv_eq_fderiv, hdQ] at hd
  ext v w
  simp only [pullbackMetricCoefficients_apply, rotateForm_apply, hd,
    Function.comp_apply]
  rfl

private theorem pullbackMetricCoefficients_eqOn
    (g : SmoothRiemannianMetric I M) {F G : E → M} {U : Set E}
    (hU : IsOpen U) (hFG : EqOn F G U) :
    EqOn (pullbackMetricCoefficients g F) (pullbackMetricCoefficients g G) U := by
  intro x hx
  have he : F =ᶠ[𝓝 x] G := hU.eventually_mem hx |>.mono (fun y hy => hFG hy)
  ext v w
  simp only [pullbackMetricCoefficients_apply, he.mfderiv_eq]
  rw [he.eq_of_nhds]
  rfl

omit [IsManifold I ∞ M] in
private theorem exists_rotated_chart
    (c : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {r : ℝ}
    (hc : c.source = Metric.ball (0 : E) r) (Q : E ≃ₗᵢ[ℝ] E) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      Φ.source = Metric.ball (0 : E) r ∧
      Φ.target = (c ∘ Q) '' Metric.ball (0 : E) r ∧
      (Φ : E → M) = c ∘ Q := by
  let Φ := Q.toContinuousLinearEquiv.toDiffeomorph.toPartialDiffeomorph.trans c
  have hsource : Φ.source = Metric.ball (0 : E) r := by
    change Set.univ ∩ (Q ⁻¹' c.source) = _
    rw [hc]
    ext x
    simp only [mem_inter_iff, mem_univ, true_and, mem_preimage, Metric.mem_ball,
      dist_zero_right, Q.norm_map]
  refine ⟨Φ, hsource, ?_, rfl⟩
  have h := Φ.toOpenPartialHomeomorph.image_source_eq_target
  change (Φ : E → M) '' Φ.source = Φ.target at h
  rw [hsource] at h
  exact h.symm

end

theorem exists_uniform_complete_normal_charts (n K : ℕ) (hn : 0 < n)
    {A ι : ℝ} (hA : 0 < A) (hι : 0 < ι) :
    letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := ⟨by simpa using hn.ne'⟩
    letI : NormedAddCommGroup ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ 2 * a < min 1 ι ∧
      ∀ (P : PointedRiemannianManifold.{u} (𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))))
        (hcomplete : MetricComplete P)
        (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M) (p : P.M),
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) P.M := P.charted
    letI : IsManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) ∞ P.M := P.smooth
    letI : IsManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 1 P.M :=
      IsManifold.of_le (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x) :=
      P.riemBundle (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
    letI : (x : P.M) → InnerProductSpace Real (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x) :=
      P.riemInner (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (fun x : P.M => TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x) :=
      P.riemBundle_cont (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
    letI : EMetricSpace P.M := P.emetricSpace (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : ∀ (x : P.M) (v : TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt (P.metric.inner x v v)) := by
      intro x v
      with_unfolding_all
        exact
          Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) P.metric x v
    (∀ q : ℕ, q ≤ K → ∀ y : P.M,
      riemannianEDistOf P.metric p y < ENNReal.ofReal 1 →
        curvDerivNorm q P.metric y ≤ A) →
    HasInjRadiusAt P p ι →
    ∀ Q : (EuclideanSpace ℝ (Fin n)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin n)), ∃ Φ : PartialDiffeomorph 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (EuclideanSpace ℝ (Fin n)) P.M ∞,
      Φ.source = Metric.ball (0 : (EuclideanSpace ℝ (Fin n))) (2 * a) ∧
      Φ.target = (intrinsicFramedExp P.metric hEnorm p ∘ Q) ''
        Metric.ball (0 : (EuclideanSpace ℝ (Fin n))) (2 * a) ∧
      EqOn Φ (intrinsicFramedExp P.metric hEnorm p ∘ Q) (Metric.ball (0 : (EuclideanSpace ℝ (Fin n))) (2 * a)) ∧
      Φ 0 = p ∧
      ContDiffOn ℝ ∞ (pullbackMetricCoefficients P.metric Φ) (Metric.ball (0 : (EuclideanSpace ℝ (Fin n))) (2 * a)) ∧
      ContDiffOn ℝ K (fun z => Ring.inverse
        (IsCoercive.gramCLM (pullbackMetricCoefficients P.metric Φ z)))
        (Metric.ball (0 : (EuclideanSpace ℝ (Fin n))) (2 * a)) ∧
      ∀ z ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin n))) a,
        (∀ v : (EuclideanSpace ℝ (Fin n)), (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients P.metric Φ z v v ∧
          pullbackMetricCoefficients P.metric Φ z v v ≤ 2 * ‖v‖ ^ 2) ∧
        ∀ q : ℕ, q ≤ K →
          ‖iteratedFDeriv ℝ q (pullbackMetricCoefficients P.metric Φ) z‖ +
            ‖iteratedFDeriv ℝ q (fun y => Ring.inverse
              (IsCoercive.gramCLM (pullbackMetricCoefficients P.metric Φ y))) z‖ ≤ C := by
  let E := EuclideanSpace ℝ (Fin n)
  let _ : NeZero (Module.finrank ℝ E) := ⟨by simpa [E] using hn.ne'⟩
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  dsimp only
  obtain ⟨r, hr, hrhalf, herror⟩ :=
    exists_uniform_local_jacobi_scale (Module.finrank ℝ E)
      (show (0 : ℝ) < 1 / 2 by norm_num) hA.le
  let a : ℝ := min (r / 4) (min (1 / 8) (ι / 4))
  have ha : 0 < a := lt_min (div_pos hr (by norm_num))
    (lt_min (by norm_num) (div_pos hι (by norm_num)))
  have har : a ≤ r / 4 := min_le_left _ _
  have hai : a ≤ ι / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have haone : a ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have h2ar : 2 * a < r := by linarith
  have h2ahalf : 2 * a < 1 / 2 := h2ar.trans_le hrhalf
  have h2ai : 2 * a < ι := by linarith
  let b : ℕ → ℝ := fun q => ContinuousMultilinearMap.polarConst q *
    (2 * (2 ^ q * jacobiJetBound (fun _ => A) (1 / 2) 1 q ^ 2))
  let D : ℝ := ∑ q : Fin (K + 1), max (b q) 0
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hbD (q : ℕ) (hq : q ≤ K) : b q ≤ D := by
    let j : Fin (K + 1) := ⟨q, by omega⟩
    refine (le_max_left (b q) 0).trans ?_
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun k : Fin (K + 1) => max (b k) 0)
      (fun k _ => le_max_right (b k) 0) (Finset.mem_univ j)
  let T : ℝ := (K.factorial : ℝ) * ((K.factorial : ℝ) * 2 ^ (K + 1)) * max D 1 ^ K
  have hT : 0 ≤ T := by positivity
  refine ⟨a, 1 + D + T, ha, by linarith, lt_min (by linarith) h2ai, ?_⟩
  intro P hcomplete hconn p
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace E P.M := P.charted
  let _ : IsManifold 𝓘(ℝ, E) ∞ P.M := P.smooth
  let _ : IsManifold 𝓘(ℝ, E) 1 P.M :=
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := P.M) (n := ∞) (by decide)
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  let _ : T2Space P.M := P.t2
  let _ : T2Space (TangentBundle 𝓘(ℝ, E) P.M) := P.t2TangentBundle
  let _ : RiemannianBundle (fun x : P.M => TangentSpace 𝓘(ℝ, E) x) :=
    P.riemBundle (I := 𝓘(ℝ, E))
  let _ : (x : P.M) → InnerProductSpace Real (TangentSpace 𝓘(ℝ, E) x) :=
    P.riemInner (I := 𝓘(ℝ, E))
  let _ : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace 𝓘(ℝ, E) x) :=
    P.riemBundle_cont (I := 𝓘(ℝ, E))
  let _ : EMetricSpace P.M := P.emetricSpace (I := 𝓘(ℝ, E))
  let _ : CompleteSpace P.M :=
    MetricComplete.complete (I := 𝓘(ℝ, E)) P hcomplete
  let _ : ConnectedSpace P.M := hconn
  let hEnorm : ∀ (x : P.M) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖v‖ₑ = ENNReal.ofReal
        (Real.sqrt (P.metric.inner x v v)) := by
    intro x v
    with_unfolding_all
      exact
        Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(ℝ, E)) P.metric x v
  intro hcurv hinj Q
  have hclosed : ∀ q : ℕ, q ≤ K → HasLocalCurvDerivBound P p (1 / 2) q A := by
    intro q hq y hy
    exact hcurv q hq y (hy.trans_lt (by norm_num))
  have hRm : ∀ y : P.M, riemannianEDist 𝓘(ℝ, E) p y < ENNReal.ofReal 1 →
      Real.sqrt (Tensor0SBundle.normSq0S P.metric y 4
        (Curvature.metricRm04At P.metric y)) ≤ A := by
    intro y hy
    apply hcurv 0 (Nat.zero_le K) y
    rwa [riemannianEDistOf_eq_riemannianEDist P.metric hEnorm]
  let F : E → P.M := intrinsicFramedExp P.metric hEnorm p
  let B : E → E →L[ℝ] E →L[ℝ] ℝ := intrinsicFrameMetric P.metric hEnorm p
  have hB : ContDiff ℝ ∞ B := contDiff_intrinsicFrameMetric P.metric hEnorm p
  have hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ F := intrinsicFrame_smooth P.metric hEnorm p
  have hmetric : ∀ z ∈ Metric.ball (0 : E) (2 * a), ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B z v v ∧ B z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro z hz v
    have hzr : ‖z‖ < 2 * a := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact intrinsicFrameMetric_bounds_of_local_curvature P.metric hEnorm p hA.le hRm
      (by linarith) (herror ‖z‖ (norm_nonneg _) (hzr.le.trans h2ar.le)) v
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ F
      (Metric.ball (0 : E) (2 * a)) :=
    intrinsicFrame_localOn_of_local_curvature P.metric hEnorm p hA.le
      (by linarith : 2 * a ≤ 1) hRm
      (fun s hs hsr => herror s hs (hsr.trans h2ar.le))
  obtain ⟨c⟩ := exists_intrinsic_ball_chart P.metric hEnorm p hlocal
    (hinj.injOn_ball hcomplete h2ai)
  obtain ⟨Φ, hsource, htarget, hΦ⟩ := exists_rotated_chart c.hom c.source_eq Q
  have heq : EqOn Φ (F ∘ Q) (Metric.ball (0 : E) (2 * a)) := by
    intro z hz
    rw [hΦ]
    apply c.hom_eq
    simpa only [Metric.mem_ball, dist_zero_right, Q.norm_map] using hz
  have htarget' : Φ.target = (F ∘ Q) '' Metric.ball (0 : E) (2 * a) := by
    rw [htarget]
    apply Set.image_congr
    intro z hz
    exact c.hom_eq (by simpa only [Metric.mem_ball, dist_zero_right, Q.norm_map] using hz)
  let BQ : E → E →L[ℝ] E →L[ℝ] ℝ := fun z => rotateForm Q (B (Q z))
  have hBQ : ContDiff ℝ ∞ BQ := (rotateForm Q).contDiff.comp (hB.comp Q.contDiff)
  have hcoeff : EqOn (pullbackMetricCoefficients P.metric Φ) BQ
      (Metric.ball (0 : E) (2 * a)) := by
    intro z hz
    rw [pullbackMetricCoefficients_eqOn P.metric Metric.isOpen_ball heq hz,
      pullbackMetricCoefficients_rotate P.metric F hF Q z]
    rfl
  have hBQmetric : ∀ z ∈ Metric.ball (0 : E) (2 * a), ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ BQ z v v ∧ BQ z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro z hz v
    have hm := hmetric (Q z)
      (by simpa only [Metric.mem_ball, dist_zero_right, Q.norm_map] using hz) (Q v)
    simpa only [BQ, rotateForm_apply, Q.norm_map] using hm
  have hBQderiv : ∀ q, q ≤ K → ∀ z ∈ Metric.ball (0 : E) (2 * a),
      ‖iteratedFDeriv ℝ q BQ z‖ ≤ D := by
    intro q hq z hz
    have hzr : ‖Q z‖ ≤ (1 / 2 : ℝ) := by
      rw [Q.norm_map]
      have hz' : ‖z‖ < 2 * a := by simpa only [Metric.mem_ball, dist_zero_right] using hz
      linarith
    exact (rotated_metric_derivative_le Q B hB z q).trans
      ((intrinsicFrameMetric_iteratedFDeriv_norm_le_of_curvature_bounds P hcomplete hconn p
        K (fun _ => A) hclosed (Q z) q (1 / 2) le_rfl hzr hq).trans (hbD q hq))
  obtain ⟨hInvSmooth, hInvBound⟩ := inverse_metric_derivative_le K D BQ hBQ
    (Metric.ball (0 : E) (2 * a)) Metric.isOpen_ball
    (fun z hz v => (hBQmetric z hz v).1) hBQderiv
  refine ⟨Φ, hsource, htarget', heq, ?_, ?_, ?_, ?_⟩
  · rw [heq (by simpa using (show 0 < 2 * a by linarith))]
    simpa only [Function.comp_apply, map_zero] using intrinsicFrame_zero P.metric hEnorm p
  · exact hBQ.contDiffOn.congr (fun z hz => hcoeff hz)
  · exact hInvSmooth.congr (fun z hz => congrArg (fun B => Ring.inverse (IsCoercive.gramCLM B))
      (hcoeff hz))
  · intro z hz
    have hza : ‖z‖ ≤ a := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hzopen : z ∈ Metric.ball (0 : E) (2 * a) := by
      simpa only [Metric.mem_ball, dist_zero_right] using (show ‖z‖ < 2 * a by linarith)
    refine ⟨?_, ?_⟩
    · intro v
      rw [hcoeff hzopen]
      exact hBQmetric z hzopen v
    · intro q hq
      have hevent : pullbackMetricCoefficients P.metric Φ =ᶠ[𝓝 z] BQ :=
        Metric.isOpen_ball.eventually_mem hzopen |>.mono (fun y hy => hcoeff hy)
      have hievent : (fun y => Ring.inverse (IsCoercive.gramCLM
          (pullbackMetricCoefficients P.metric Φ y))) =ᶠ[𝓝 z]
          (fun y => Ring.inverse (IsCoercive.gramCLM (BQ y))) :=
        hevent.mono (fun y hy => congrArg (fun B => Ring.inverse (IsCoercive.gramCLM B)) hy)
      rw [(hevent.iteratedFDeriv ℝ q).eq_of_nhds, (hievent.iteratedFDeriv ℝ q).eq_of_nhds]
      exact (add_le_add (hBQderiv q hq z hzopen) (hInvBound q hq z hzopen)).trans (by
        change D + T ≤ 1 + D + T
        linarith)

end DifferentialGeometry.CheegerGromovCompactness
