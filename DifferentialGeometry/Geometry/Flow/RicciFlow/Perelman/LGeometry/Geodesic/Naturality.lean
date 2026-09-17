import DifferentialGeometry.Topology.Manifold.Diffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Basic
import DifferentialGeometry.Geometry.Operator.Pullback
import DifferentialGeometry.Geometry.Curvature.RicciPullback

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
  change (mfderiv 𝓘(Real, Real) I (Phi ∘ alpha) s) (1 : Real) = _
  rw [Phi.mfderiv_comp (by decide)]
  rfl

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
omit [SigmaCompactSpace N] in
theorem lRegularizedAccel_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T s : Real) (x : M) (A : TangentSpace I x) :
    mfderiv I I (Phi : M → N) x
        (lRegularizedAccel (solutionOnPullback (I := I) S Phi) T s x A) =
      lRegularizedAccel S T s (Phi x) (mfderiv I I (Phi : M → N) x A) := by
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
    ((scalarSmoothOfSolution (I := I) S t).contMDiffAt.mdifferentiableAt (by simp))
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
          (lRegularizedAccel SP T s x A)) Y =
      g.inner (Phi x) Y
        (mfderiv I I (Phi : M → N) x
          (lRegularizedAccel SP T s x A)) := g.symm _ _ _
    _ = (SP.base.metric t).inner x
        (Yback Y) (lRegularizedAccel SP T s x A) := by
          rw [show SP.base.metric t = Diffeomorph.pullbackMetric (I := I) g Phi from rfl,
            Diffeomorph.pullbackMetric_inner, hY]
    _ = 2 * s ^ 2 * (SP.base.metric t).inner x
          (gradientFun (I := I) (SP.base.metric t) (SP.scalar t) x) (Yback Y) -
        4 * s * SP.ricciAt t x (vec2 (Yback Y) A) :=
      by simpa only [t] using lRegularizedAccel_inner SP T s x A (Yback Y)
    _ = 2 * s ^ 2 * g.inner (Phi x)
          (gradientFun (I := I) g (S.scalar t) (Phi x)) Y -
        4 * s * S.ricciAt t (Phi x)
          (vec2 Y (mfderiv I I (Phi : M → N) x A)) := by
      rw [show SP.base.metric t = Diffeomorph.pullbackMetric (I := I) g Phi from rfl,
        Diffeomorph.pullbackMetric_inner, hgradMap, hY, hric]
    _ = g.inner (Phi x)
        Y (lRegularizedAccel S T s (Phi x) (mfderiv I I (Phi : M → N) x A)) := by
      simpa only [t, g] using (lRegularizedAccel_inner S T s (Phi x)
        (mfderiv I I (Phi : M → N) x A) Y).symm
    _ = g.inner (Phi x)
        (lRegularizedAccel S T s (Phi x) (mfderiv I I (Phi : M → N) x A)) Y :=
      g.symm _ _ _

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace N] in
theorem isLRegularizedCurve_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (alpha : Real → M) (J : Set Real) (x : M)
    (Z : TangentSpace I x) (halpha :
      IsLRegularizedCurveOn (solutionOnPullback (I := I) S Phi) T alpha J x Z) :
    IsLRegularizedCurveOn S T (fun s => Phi (alpha s)) J (Phi x)
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
            lRegularizedAccel (solutionOnPullback (I := I) S Phi) T s (alpha s)
              (lVelocity (I := I) alpha s) := hacc
      rw [← hvelEq, ← hnat, hacc', lRegularizedAccel_pull, lVelocity_pull]

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
theorem lRegularizedDomain_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (x : M) (Z : TangentSpace I x) :
    lRegularizedDomain (solutionOnPullback (I := I) S Phi) T x Z =
      lRegularizedDomain S T (Phi x) (mfderiv I I (Phi : M → N) x Z) := by
  ext s
  constructor
  · rintro ⟨alpha, J, hJopen, hJconn, h0J, hsJ, halpha⟩
    exact ⟨fun r => Phi (alpha r), J, hJopen, hJconn, h0J, hsJ,
      isLRegularizedCurve_pull (I := I) S Phi T alpha J x Z halpha⟩
  · rintro ⟨beta, J, hJopen, hJconn, h0J, hsJ, hbeta⟩
    have hdouble :
        solutionOnPullback (I := I) (solutionOnPullback (I := I) S Phi) Phi.symm = S :=
      solution_pull_inv (I := I) S Phi
    have hbeta' : IsLRegularizedCurveOn
        (solutionOnPullback (I := I) (solutionOnPullback (I := I) S Phi) Phi.symm)
        T beta J (Phi x) (mfderiv I I (Phi : M → N) x Z) := by
      rw [hdouble]
      exact hbeta
    have hback := isLRegularizedCurve_pull (I := I)
      (solutionOnPullback (I := I) S Phi) Phi.symm T beta J (Phi x)
      (mfderiv I I (Phi : M → N) x Z) hbeta'
    have hZ := mfderiv_symm_apply_apply (I := I) Phi x Z
    refine ⟨fun r => Phi.symm (beta r), J, hJopen, hJconn, h0J, hsJ, ?_⟩
    convert hback using 1 <;> simp only [Phi.symm_apply_apply, hZ]

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegularizedCurve_pull
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Phi : M ≃ₘ⟮I, I⟯ N) (T : Real) (x : M) (Z : TangentSpace I x) (s : Real) :
    lRegularizedCurve S T (Phi x) (mfderiv I I (Phi : M → N) x Z) s =
      Phi (lRegularizedCurve (solutionOnPullback (I := I) S Phi) T x Z s) := by
  by_cases hs : s ∈ lRegularizedDomain (solutionOnPullback (I := I) S Phi) T x Z
  · obtain ⟨J, hJopen, hJconn, h0J, hsJ, hchosen⟩ :=
      lRegularizedChosen_spec (solutionOnPullback (I := I) S Phi) T x Z hs
    have hmap := isLRegularizedCurve_pull (I := I) S Phi T
      (lRegularizedChosen (solutionOnPullback (I := I) S Phi) T x Z hs) J x Z hchosen
    have heq := lRegularizedCurve_eqOn S hS T hJopen hJconn h0J hmap hsJ
    rw [heq, lRegularizedCurve_of_mem hs]
  · have ht : s ∉ lRegularizedDomain S T (Phi x)
        (mfderiv I I (Phi : M → N) x Z) := by
      rw [← lRegularizedDomain_pull (I := I) S Phi T x Z]
      exact hs
    rw [lRegularizedCurve_of_not_mem hs, lRegularizedCurve_of_not_mem ht]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
theorem lExpDomain_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (x : M) (Z : TangentSpace I x) :
    lExpDomain (solutionOnPullback (I := I) S Phi) T x Z =
      lExpDomain S T (Phi x) (mfderiv I I (Phi : M → N) x Z) := by
  ext tau
  simp only [lExpDomain, mem_ofPred_eq, and_congr_right_iff]
  intro _
  rw [lRegularizedDomain_pull (I := I) S Phi T x Z]

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExp_pull
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Phi : M ≃ₘ⟮I, I⟯ N) (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real) :
    lExp S T (Phi x) (mfderiv I I (Phi : M → N) x Z) tau =
      Phi (lExp (solutionOnPullback (I := I) S Phi) T x Z tau) := by
  exact lRegularizedCurve_pull (I := I) S hS Phi T x Z (Real.sqrt tau)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
section

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  {D : RealTimeInterval}

theorem lRegularizedAccel_pullback
    (S : SolutionOn (I := J) (M := N) D) (Φ : M ≃ₘ⟮I, J⟯ N)
    (T s : ℝ) (x : M) (v : TangentSpace I x) :
    mfderiv I J Φ x (lRegularizedAccel (S.pullback Φ) T s x v) =
      lRegularizedAccel S T s (Φ x) (mfderiv I J Φ x v) := by
  let instCompleteF : CompleteSpace F := FiniteDimensional.complete ℝ F
  let g := S.base.metric (T - s ^ 2)
  have hscalar : (S.pullback Φ).scalar (T - s ^ 2) =
      S.scalar (T - s ^ 2) ∘ (Φ : M → N) := by
    funext y
    exact S.pullback_scalar Φ (T - s ^ 2) y
  have hgrad : mfderiv I J Φ x
      (gradientFun (Diffeomorph.pullbackMetricCross g Φ)
        ((S.pullback Φ).scalar (T - s ^ 2)) x) =
      gradientFun g (S.scalar (T - s ^ 2)) (Φ x) := by
    rw [hscalar, gradientFun_pullbackCross g Φ (S.scalar (T - s ^ 2)) x
      ((scalarSmoothOfSolution S (T - s ^ 2)).contMDiffAt.mdifferentiableAt (by simp))]
    rw [← Φ.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (Φ.mfderivToContinuousLinearEquiv (by simp) x).apply_symm_apply _
  change mfderiv I J Φ x
      ((2 * s ^ 2) • gradientFun (Diffeomorph.pullbackMetricCross g Φ)
        ((S.pullback Φ).scalar (T - s ^ 2)) x -
        (4 * s) • ricciSharp (Diffeomorph.pullbackMetricCross g Φ) x v) =
      (2 * s ^ 2) • gradientFun g (S.scalar (T - s ^ 2)) (Φ x) -
        (4 * s) • ricciSharp g (Φ x) (mfderiv I J Φ x v)
  rw [map_sub, map_smul, map_smul, hgrad, ricciSharp_pullbackMetricCross]

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

end
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  {D : RealTimeInterval}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [I.Boundaryless] [J.Boundaryless]
  [IsManifold I ∞ M] [IsManifold J ∞ N] [T2Space M] [T2Space N] in
theorem lVelocity_comp_diffeomorph (Φ : M ≃ₘ⟮I, J⟯ N) (alpha : ℝ → M) (s : ℝ) :
    lVelocity (I := J) (Φ ∘ alpha) s =
      mfderiv I J Φ (alpha s) (lVelocity (I := I) alpha s) := by
  change (mfderiv 𝓘(ℝ, ℝ) J (Φ ∘ alpha) s) 1 = _
  rw [Φ.mfderiv_comp (by decide)]
  rfl

theorem IsLRegularizedGeodesicOn.comp_diffeomorph
    (S : SolutionOn (I := J) (M := N) D) (Φ : M ≃ₘ⟮I, J⟯ N)
    {T : ℝ} {alpha : ℝ → M} {K : Set ℝ}
    (h : IsLRegularizedGeodesicOn (S.pullback Φ) T alpha K) :
    IsLRegularizedGeodesicOn S T (Φ ∘ alpha) K := by
  intro s hs
  obtain ⟨ht, hmd, hvel, hacc⟩ := h s hs
  refine ⟨ht, (Φ.contMDiff.mdifferentiableAt (by decide)).comp s hmd, ?_, ?_⟩
  · have hmap := chartRep_map_diff Φ alpha
      (fun r => lVelocity (I := I) alpha r) s hmd hvel
    simpa only [← lVelocity_comp_diffeomorph, Function.comp_def] using hmap
  · have hnat := covDerivAlong_pullback (S.base.metric (T - s ^ 2)) Φ alpha
      (fun r => lVelocity (I := I) alpha r) s hmd hvel
    change covDerivAlong
      (Diffeomorph.pullbackMetricCross (S.base.metric (T - s ^ 2)) Φ) alpha
      (fun r => lVelocity (I := I) alpha r) s = _ at hacc
    rw [hacc, lRegularizedAccel_pullback] at hnat
    simpa only [← lVelocity_comp_diffeomorph, Function.comp_def] using hnat.symm


theorem isLRegularizedGeodesicOn_pullback_iff
    (S : SolutionOn (I := J) (M := N) D) (Φ : M ≃ₘ⟮I, J⟯ N)
    {T : ℝ} {alpha : ℝ → M} {K : Set ℝ} :
    IsLRegularizedGeodesicOn (S.pullback Φ) T alpha K ↔
      IsLRegularizedGeodesicOn S T (Φ ∘ alpha) K := by
  constructor
  · exact IsLRegularizedGeodesicOn.comp_diffeomorph S Φ
  · intro h
    have hsource : IsLRegularizedGeodesicOn
        ((S.pullback Φ).pullback Φ.symm) T (Φ ∘ alpha) K := by
      simpa only [SolutionOn.pullback_symm] using h
    have h' := IsLRegularizedGeodesicOn.comp_diffeomorph (S.pullback Φ) Φ.symm hsource
    have heq : Φ.symm ∘ (Φ ∘ alpha) = alpha := by
      funext s
      exact Φ.symm_apply_apply (alpha s)
    rw [heq] at h'
    exact h'

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
