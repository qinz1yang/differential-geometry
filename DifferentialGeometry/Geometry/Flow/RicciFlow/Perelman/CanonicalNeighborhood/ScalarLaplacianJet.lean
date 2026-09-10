import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ShiUniformConstant
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M]

theorem exists_iterCov_metricTrace
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (r + 2)) (k : ℕ) :
    ∃ e : Fin (r + 2 + k) ≃ Fin ((r + k) + 2),
      iterCov (I := I) g r (metricTraceFirstTwoField (I := I) g A) k =
        metricTraceFirstTwoField (I := I) g
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e
            (iterCov (I := I) g (r + 2) A k)) := by
  classical
  induction k with
  | zero =>
      refine ⟨Equiv.refl _, ?_⟩
      refine DFunLike.ext _ _ fun x => ?_
      exact tensor0SSpace_ext (I := I) r x fun v => rfl
  | succ k ih =>
      obtain ⟨e, he⟩ := ih
      let cov := leviCivitaConnectionOfMetric (I := I) g
      have hmc : IsMetricCompatible (I := I) cov g :=
        leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
      have hA := iterCov_realizes (I := I) g A k
      have hreindex := totalNabla0SRealizes_domDomCongr (I := I) cov e _ _ hA
      have htrace := nablaRealizes_metricTraceFirstTwo (I := I)
        (s := r + k) cov g hmc _ _ hreindex
      rw [← he] at htrace
      have hbase := iterCov_realizes (I := I) g (metricTraceFirstTwoField (I := I) g A) k
      have hout := Tensor0SBundle.totalNabla0SRealizes_unique (I := I) hbase htrace
      refine ⟨(frontExtendEquiv e).trans (traceNablaShuffle (r + k)), ?_⟩
      rw [← Tensor0SField.domDomCongr_trans]
      exact hout

theorem iterCov_metricTrace_normSq_le
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (r + 2)) (k : ℕ) (x : M) :
    normSq0S (I := I) g x (r + k)
        (iterCov (I := I) g r (metricTraceFirstTwoField (I := I) g A) k x) ≤
      (Module.finrank ℝ E : ℝ) ^ ((r + k) + 2) *
        normSq0S (I := I) g x (r + 2 + k) (iterCov (I := I) g (r + 2) A k x) := by
  classical
  obtain ⟨e, he⟩ := exists_iterCov_metricTrace (I := I) g A k
  rw [he]
  have htrace := trace_normSq_rank_le (I := I) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e
      (iterCov (I := I) g (r + 2) A k) x)
  rw [Tensor0SField.domDomCongr_apply] at htrace
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hperm := normSq0S_domDomCongr (I := I) g x basis hinv e
    (iterCov (I := I) g (r + 2) A k x)
  rw [metricTraceFirstTwoField_apply]
  exact htrace.trans_eq
    (congrArg (fun z => (Module.finrank ℝ E : ℝ) ^ ((r + k) + 2) * z) hperm)

theorem iterCov_zeroTensor_one_eq_duSec
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 0)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) f)
    (hA : ∀ y, A y Fin.elim0 = f y) :
    iterCov (I := I) g 0 A 1 = duSec (I := I) f hf := by
  apply Tensor0SBundle.totalNabla0SRealizes_unique (iterCov_realizes (I := I) g A 0)
  change TotalNabla0SRealizes (I := I) 0 (leviCivitaConnectionOfMetric (I := I) g)
    A (duSec (I := I) f hf)
  intro X x slots
  have hslots : slots = Fin.elim0 := funext fun i => Fin.elim0 i
  subst slots
  have hcons : Fin.cons (X x) (Fin.elim0 : Fin 0 → TangentSpace I x) =
      fun _ : Fin 1 => X x := by
    funext i
    fin_cases i
    rfl
  rw [hcons, duSec_apply, differential1FormFun_apply_eq_mvfderiv]
  let V : Fin 0 → ContMDiffSection I E (∞ : WithTop ℕ∞)
    (TangentSpace I : M → Type _) := fun i => i.elim0
  have heval : (fun p => A p (fun a => V a p)) = f := by
    funext p
    exact (congrArg (A p) (Subsingleton.elim _ _)).trans (hA p)
  have hempty : (fun a => V a x) = (Fin.elim0 : Fin 0 → TangentSpace I x) :=
    Subsingleton.elim _ _
  have hnabla := nabla0SFun_eval_smooth_slots (I := I)
    (leviCivitaConnectionOfMetric (I := I) g) X V A x
  simpa only [hempty, heval, Finset.univ_eq_empty, Finset.sum_empty, sub_zero] using
    hnabla.symm

theorem iterCov_zeroTensor_two_eq_hessianSec
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 0)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) f)
    (hA : ∀ y, A y Fin.elim0 = f y) :
    iterCov (I := I) g 0 A 2 =
      hessianSec (I := I) (leviCivitaConnectionOfMetric (I := I) g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g) f hf := by
  rw [iterCov_succ, iterCov_zeroTensor_one_eq_duSec (I := I) g A f hf hA]
  rfl

variable [NeZero (Module.finrank ℝ E)]

theorem abs_laplacian_scalar_le_second_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) :
    |laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x| ≤
      (Module.finrank ℝ E : ℝ) ^ 6 *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x) := by
  classical
  let g := S.base.metric t
  let Ric := metricRicci (I := I) g
  let A := metricTraceFirstTwoField (I := I) g Ric
  let f := metricScalarAt (I := I) g
  have hA : ∀ y, A y Fin.elim0 = f y := by
    intro y
    dsimp only [A, Ric, f]
    rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
      traceFirstTwo_elim0, metricRicci_apply, metricScalarAt_def]
  have hf : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) f := by
    let V : Fin 0 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := fun i => i.elim0
    have heval : (fun p => A p (fun a => V a p)) = f := by
      funext p
      exact (congrArg (A p) (Subsingleton.elim _ _)).trans (hA p)
    intro y
    rw [← heval]
    exact tensor0SField_eval_smooth_slots_contMDiffAt (I := I) A V y
  let Hess := hessianSec (I := I) (leviCivitaConnectionOfMetric (I := I) g)
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g) f hf
  have hHess : iterCov (I := I) g 0 A 2 = Hess :=
    iterCov_zeroTensor_two_eq_hessianSec (I := I) g A f hf hA
  have htrace : laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x =
      metricTracePair0SAt (I := I) g (Hess x) := by
    change laplacian (I := I) (leviCivitaConnectionOfMetric (I := I) g) g f x =
      metricTracePair0SAt (I := I) g (Hess x)
    have h := scalarLap_smooth (I := I) (leviCivitaConnectionOfMetric (I := I) g)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g)
      g (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) f hf (x := x)
    simpa only [ScalarLaplacianRealizesTraceAt, traceFirstTwo_elim0] using h
  have hscalarBound := iterCov_metricTrace_normSq_le (I := I) g Ric 2 x
  change normSq0S (I := I) g x 2 (iterCov (I := I) g 0 A 2 x) ≤
    (Module.finrank ℝ E : ℝ) ^ 4 *
      normSq0S (I := I) g x 4 (iterCov (I := I) g 2 Ric 2 x) at hscalarBound
  rw [hHess] at hscalarBound
  have hricBound := ricTower_normSq_le (I := I) S t 2 x
  change normSq0S (I := I) g x 4 (iterCov (I := I) g 2 Ric 2 x) ≤
    (Module.finrank ℝ E : ℝ) ^ 6 *
      nablaKRm04NormSqIntrinsic (I := I) S 2 t x at hricBound
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hlap := metricTracePair0SAt_sq_le_card_mul_normSq0S (I := I)
    g basis _ hinv (Hess x)
  have hrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  rw [Fintype.card_fin, hrank, ← htrace] at hlap
  have hn : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
  have hn2 : (Module.finrank ℝ E : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by
    nlinarith
  have hHessnonneg := normSq0S_nonneg (I := I) g x 2 (Hess x)
  have hsquared : laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ 12 * nablaKRm04NormSqIntrinsic (I := I) S 2 t x := by
    calc
      _ ≤ (Module.finrank ℝ E : ℝ) * normSq0S (I := I) g x 2 (Hess x) := hlap
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * normSq0S (I := I) g x 2 (Hess x) :=
        mul_le_mul_of_nonneg_right hn2 hHessnonneg
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
          ((Module.finrank ℝ E : ℝ) ^ 4 *
            normSq0S (I := I) g x 4 (iterCov (I := I) g 2 Ric 2 x)) :=
        mul_le_mul_of_nonneg_left hscalarBound (sq_nonneg _)
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
          ((Module.finrank ℝ E : ℝ) ^ 4 *
            ((Module.finrank ℝ E : ℝ) ^ 6 * nablaKRm04NormSqIntrinsic (I := I) S 2 t x)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hricBound (by positivity)) (sq_nonneg _)
      _ = _ := by ring
  calc
    _ = Real.sqrt (laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 12 *
        nablaKRm04NormSqIntrinsic (I := I) S 2 t x) := Real.sqrt_le_sqrt hsquared
    _ = _ := by
      have hpow : (Module.finrank ℝ E : ℝ) ^ 12 = ((Module.finrank ℝ E : ℝ) ^ 6) ^ 2 :=
        by ring
      rw [hpow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

theorem scalarLaplacianCurvatureJetBound [I.Boundaryless] :
    ScalarLaplacianCurvatureJetBound.{u, uE, uH} I ((Module.finrank ℝ E : ℝ) ^ 6) := by
  intro M _ _ _ _ _ _ _ D S _ t _ x
  exact abs_laplacian_scalar_le_second_curvature S t x

theorem goodPointBoundsOn_of_modelBound [I.Boundaryless] {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, uE, uH} I kappa) :
    ∃ CStar : ℝ, 0 ≤ CStar ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M] [SigmaCompactSpace M]
        [VectorBundle ℝ E (TangentSpace I : M → Type _)]
        {T : ℝ} {hT : (0 : ℝ) < T}
        (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
        IsSolutionOn (I := I) S → ∀ (x : M) (t eps : ℝ), 0 < eps → eps ≤ 1 / 4 →
          IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t →
            (∀ v : TangentSpace I x,
                |scalarDifferential (I := I) S t x v| ≤
                  2 * CStar * (S.scalar t x * Real.sqrt (S.scalar t x)) *
                    Real.sqrt ((S.base.metric t).inner x v v)) ∧
              |deriv (fun tau : ℝ => S.scalar tau x) t| ≤ CStar * S.scalar t x ^ 2 :=
  goodPointBoundsOn_of_modelCurvatureBound I (by positivity) hmod
    witnessSourceBallCapture (localShiUniformConstant I) scalarLaplacianCurvatureJetBound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
