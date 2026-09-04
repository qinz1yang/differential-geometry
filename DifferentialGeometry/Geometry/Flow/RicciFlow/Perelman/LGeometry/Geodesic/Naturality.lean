import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.Pullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set Function Filter
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe uM uN uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N]
variable {D : RealTimeInterval}

private lemma infty_ne_zero_nat : (∞ : WithTop ℕ∞) ≠ 0 := by decide

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I ∞ N] [T2Space M] [T2Space N]
  [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem mfderiv_apply_symm_apply
    (Phi : M ≃ₘ⟮I, I⟯ N) (x : M) (Y : TangentSpace I (Phi x)) :
    mfderiv I I (Phi : M → N) x
        (mfderiv I I (Phi.symm : N → M) (Phi x) Y) = Y := by
  rw [← mfderiv_symm_apply (I := I) Phi x Y]
  rw [← Phi.mfderivToContinuousLinearEquiv_coe infty_ne_zero_nat]
  exact (Phi.mfderivToContinuousLinearEquiv infty_ne_zero_nat x).apply_symm_apply Y

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I ∞ N] [T2Space M] [T2Space N]
  [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem mfderiv_symm_apply_apply
    (Phi : M ≃ₘ⟮I, I⟯ N) (x : M) (X : TangentSpace I x) :
    mfderiv I I (Phi.symm : N → M) (Phi x)
        (mfderiv I I (Phi : M → N) x X) = X := by
  rw [← mfderiv_symm_apply (I := I) Phi x]
  rw [← Phi.mfderivToContinuousLinearEquiv_coe infty_ne_zero_nat]
  exact (Phi.mfderivToContinuousLinearEquiv infty_ne_zero_nat x).symm_apply_apply X

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I ∞ N]
  [T2Space M] [T2Space N] [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem lVelocity_pull
    (Phi : M ≃ₘ⟮I, I⟯ N) (alpha : Real → M) (s : Real) :
    lVelocity (I := I) (fun r => Phi (alpha r)) s =
      mfderiv I I (Phi : M → N) (alpha s) (lVelocity (I := I) alpha s) := by
  by_cases halpha : MDifferentiableAt 𝓘(Real, Real) I alpha s
  · change mfderiv 𝓘(Real, Real) I ((Phi : M → N) ∘ alpha) s 1 =
      mfderiv I I (Phi : M → N) (alpha s)
        (mfderiv 𝓘(Real, Real) I alpha s 1)
    exact mfderiv_comp_apply (I := 𝓘(Real, Real)) (I' := I) (I'' := I)
      (x := s) (f := alpha) (g := (Phi : M → N))
      (Phi.contMDiff.mdifferentiableAt infty_ne_zero_nat) halpha (1 : Real)
  · have hmap : ¬MDifferentiableAt 𝓘(Real, Real) I
        (fun r => Phi (alpha r)) s := by
      intro h
      have hback := (Phi.symm.contMDiff.mdifferentiableAt infty_ne_zero_nat).comp s h
      have heq : (Phi.symm : N → M) ∘ (fun r => Phi (alpha r)) = alpha := by
        funext r
        exact Phi.symm_apply_apply (alpha r)
      rw [heq] at hback
      exact halpha hback
    simp only [lVelocity, mfderiv_zero_of_not_mdifferentiableAt halpha,
      mfderiv_zero_of_not_mdifferentiableAt hmap]
    change (0 : E) = mfderiv I I (Phi : M → N) (alpha s) (0 : E)
    exact (map_zero _).symm

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
omit [SigmaCompactSpace N] in
theorem lRegAccel_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T s : Real) (x : M) (A : TangentSpace I x) :
    mfderiv I I (Phi : M → N) x
        (lRegAccel (solutionOnPullback (I := I) S Phi) T s x A) =
      lRegAccel S T s (Phi x) (mfderiv I I (Phi : M → N) x A) := by
  let SP := solutionOnPullback (I := I) S Phi
  let t := T - s ^ 2
  let g := S.base.metric t
  let Yback : TangentSpace I (Phi x) → TangentSpace I x :=
    fun Y => mfderiv I I (Phi.symm : N → M) (Phi x) Y
  apply (metricFlatEquiv (I := I) g (Phi x)).injective
  ext Y
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply]
  have hY : mfderiv I I (Phi : M → N) x (Yback Y) = Y :=
    mfderiv_apply_symm_apply (I := I) Phi x Y
  have hscalar : SP.scalar t = S.scalar t ∘ (Phi : M → N) := by
    funext y
    exact scalar_pullback (I := I) S Phi t y
  have hgrad := gradientFun_pullback (I := I) g Phi (S.scalar t) x
    ((scalarSmoothOfSol (I := I) S t).contMDiffAt.mdifferentiableAt (by simp))
  have hgradMap :
      mfderiv I I (Phi : M → N) x
          (gradientFun (I := I) (Diffeomorph.pullbackMetric (I := I) g Phi)
            (SP.scalar t) x) =
        gradientFun (I := I) g (S.scalar t) (Phi x) := by
    rw [hscalar, hgrad]
    rw [← Phi.mfderivToContinuousLinearEquiv_coe infty_ne_zero_nat]
    exact (Phi.mfderivToContinuousLinearEquiv infty_ne_zero_nat x).apply_symm_apply _
  have hric :
      SP.ricciAt t x (vec2 (Yback Y) A) =
        S.ricciAt t (Phi x)
          (vec2 Y (mfderiv I I (Phi : M → N) x A)) := by
    change metricRicci (I := I)
        (Diffeomorph.pullbackMetric (I := I) g Phi) x (vec2 (Yback Y) A) = _
    rw [metricRicci_pullback_eval (I := I) g Phi]
    congr 1
    funext q
    fin_cases q
    · exact hY
    · rfl
  calc
    g.inner (Phi x)
        (mfderiv I I (Phi : M → N) x
          (lRegAccel SP T s x A)) Y =
      g.inner (Phi x) Y
        (mfderiv I I (Phi : M → N) x
          (lRegAccel SP T s x A)) := g.symm _ _ _
    _ = (SP.base.metric t).inner x
        (Yback Y) (lRegAccel SP T s x A) := by
          rw [show SP.base.metric t = Diffeomorph.pullbackMetric (I := I) g Phi from rfl,
            Diffeomorph.pullbackMetric_inner, hY]
    _ = 2 * s ^ 2 * (SP.base.metric t).inner x
          (gradientFun (I := I) (SP.base.metric t) (SP.scalar t) x) (Yback Y) -
        4 * s * SP.ricciAt t x (vec2 (Yback Y) A) :=
      by simpa only [t] using lRegAccel_inner SP T s x A (Yback Y)
    _ = 2 * s ^ 2 * g.inner (Phi x)
          (gradientFun (I := I) g (S.scalar t) (Phi x)) Y -
        4 * s * S.ricciAt t (Phi x)
          (vec2 Y (mfderiv I I (Phi : M → N) x A)) := by
      rw [show SP.base.metric t = Diffeomorph.pullbackMetric (I := I) g Phi from rfl,
        Diffeomorph.pullbackMetric_inner, hgradMap, hY, hric]
    _ = g.inner (Phi x)
        Y (lRegAccel S T s (Phi x) (mfderiv I I (Phi : M → N) x A)) := by
      simpa only [t, g] using (lRegAccel_inner S T s (Phi x)
        (mfderiv I I (Phi : M → N) x A) Y).symm
    _ = g.inner (Phi x)
        (lRegAccel S T s (Phi x) (mfderiv I I (Phi : M → N) x A)) Y :=
      g.symm _ _ _

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace N] in
theorem isLRegCurve_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (alpha : Real → M) (J : Set Real) (x : M)
    (Z : TangentSpace I x) (halpha :
      IsLRegCurveOn (solutionOnPullback (I := I) S Phi) T alpha J x Z) :
    IsLRegCurveOn S T (fun s => Phi (alpha s)) J (Phi x)
      (mfderiv I I (Phi : M → N) x Z) := by
  refine ⟨?_, ?_, ?_⟩
  · change Phi (alpha 0) = Phi x
    rw [halpha.1]
  · rw [lVelocity_pull (I := I), halpha.2.1, halpha.1]
    exact map_nsmul (mfderiv I I (Phi : M → N) x) 2 Z
  · intro s hs
    obtain ⟨ht, hmd, hvel, hacc⟩ := halpha.2.2 s hs
    refine ⟨ht, (Phi.contMDiff.mdifferentiableAt infty_ne_zero_nat).comp s hmd, ?_, ?_⟩
    · have hmap := chartRep_map_diff (I := I) Phi alpha
        (fun r => lVelocity (I := I) alpha r) s hmd hvel
      have heq :
          (fun r => lVelocity (I := I) (fun q => Phi (alpha q)) r) =
            fun r => mfderiv I I (Phi : M → N) (alpha r)
              (lVelocity (I := I) alpha r) := by
        funext r
        exact lVelocity_pull (I := I) Phi alpha r
      rw [heq]
      exact hmap
    · have hnat := covAlong_natMDiff (I := I)
        (S.base.metric (T - s ^ 2)) Phi alpha
        (fun r => lVelocity (I := I) alpha r) s hmd hvel
      have hvelEq :
          (fun r => mfderiv I I (Phi : M → N) (alpha r)
            (lVelocity (I := I) alpha r)) =
            fun r => lVelocity (I := I) (fun q => Phi (alpha q)) r := by
        funext r
        exact (lVelocity_pull (I := I) Phi alpha r).symm
      have hacc' :
          covDerivAlong (I := I)
              (Diffeomorph.pullbackMetric (I := I) (S.base.metric (T - s ^ 2)) Phi)
              alpha (fun r => lVelocity (I := I) alpha r) s =
            lRegAccel (solutionOnPullback (I := I) S Phi) T s (alpha s)
              (lVelocity (I := I) alpha s) := hacc
      rw [← hvelEq, ← hnat, hacc', lRegAccel_pull, lVelocity_pull]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless] in
private theorem solution_pull_inv
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N) :
    solutionOnPullback (I := I) (solutionOnPullback (I := I) S Phi) Phi.symm = S := by
  cases S with
  | mk base =>
      cases base with
      | mk metric =>
          unfold solutionOnPullback
          congr 2
          funext t
          change Diffeomorph.pullbackMetric
              (Diffeomorph.pullbackMetric (metric t) Phi) Phi.symm = metric t
          rw [Diffeomorph.pullbackMetric_trans, Phi.symm_trans_self,
            Diffeomorph.pullbackMetric_refl]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
theorem lRegDomain_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (x : M) (Z : TangentSpace I x) :
    lRegDomain (solutionOnPullback (I := I) S Phi) T x Z =
      lRegDomain S T (Phi x) (mfderiv I I (Phi : M → N) x Z) := by
  ext s
  constructor
  · rintro ⟨alpha, J, hJopen, hJconn, h0J, hsJ, halpha⟩
    exact ⟨fun r => Phi (alpha r), J, hJopen, hJconn, h0J, hsJ,
      isLRegCurve_pull (I := I) S Phi T alpha J x Z halpha⟩
  · rintro ⟨beta, J, hJopen, hJconn, h0J, hsJ, hbeta⟩
    have hdouble :
        solutionOnPullback (I := I) (solutionOnPullback (I := I) S Phi) Phi.symm = S :=
      solution_pull_inv (I := I) S Phi
    have hbeta' : IsLRegCurveOn
        (solutionOnPullback (I := I) (solutionOnPullback (I := I) S Phi) Phi.symm)
        T beta J (Phi x) (mfderiv I I (Phi : M → N) x Z) := by
      rw [hdouble]
      exact hbeta
    have hback := isLRegCurve_pull (I := I)
      (solutionOnPullback (I := I) S Phi) Phi.symm T beta J (Phi x)
      (mfderiv I I (Phi : M → N) x Z) hbeta'
    have hZ := mfderiv_symm_apply_apply (I := I) Phi x Z
    refine ⟨fun r => Phi.symm (beta r), J, hJopen, hJconn, h0J, hsJ, ?_⟩
    convert hback using 1 <;> simp only [Phi.symm_apply_apply, hZ]

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_pull
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Phi : M ≃ₘ⟮I, I⟯ N) (T : Real) (x : M) (Z : TangentSpace I x) (s : Real) :
    lRegCurve S T (Phi x) (mfderiv I I (Phi : M → N) x Z) s =
      Phi (lRegCurve (solutionOnPullback (I := I) S Phi) T x Z s) := by
  by_cases hs : s ∈ lRegDomain (solutionOnPullback (I := I) S Phi) T x Z
  · obtain ⟨J, hJopen, hJconn, h0J, hsJ, hchosen⟩ :=
      lRegChosen_spec (solutionOnPullback (I := I) S Phi) T x Z hs
    have hmap := isLRegCurve_pull (I := I) S Phi T
      (lRegChosen (solutionOnPullback (I := I) S Phi) T x Z hs) J x Z hchosen
    have heq := lRegCurve_eqOn S hS T hJopen hJconn h0J hmap hsJ
    rw [heq, lRegCurve_of_mem hs]
  · have ht : s ∉ lRegDomain S T (Phi x)
        (mfderiv I I (Phi : M → N) x Z) := by
      rw [← lRegDomain_pull (I := I) S Phi T x Z]
      exact hs
    rw [lRegCurve_of_not_mem hs, lRegCurve_of_not_mem ht]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
theorem lExpDomain_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (x : M) (Z : TangentSpace I x) :
    lExpDomain (solutionOnPullback (I := I) S Phi) T x Z =
      lExpDomain S T (Phi x) (mfderiv I I (Phi : M → N) x Z) := by
  ext tau
  simp only [lExpDomain, mem_ofPred_eq, and_congr_right_iff]
  intro _
  rw [lRegDomain_pull (I := I) S Phi T x Z]

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExp_pull
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Phi : M ≃ₘ⟮I, I⟯ N) (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real) :
    lExp S T (Phi x) (mfderiv I I (Phi : M → N) x Z) tau =
      Phi (lExp (solutionOnPullback (I := I) S Phi) T x Z tau) := by
  exact lRegCurve_pull (I := I) S hS Phi T x Z (Real.sqrt tau)

end DifferentialGeometry.PDE.RicciFlow.Perelman
