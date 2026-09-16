import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.EndomorphismScalarization
import DifferentialGeometry.Analysis.Spectral.LowerKyFan
import DifferentialGeometry.Geometry.Connection.NormalSection

noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped Manifold ContDiff Topology InnerProductSpace BigOperators

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]

theorem nonempty_parabolicUpperSupportAt_lowerKyFanSum_of_evolution
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun y : M => V y →L[ℝ] V y)⟯)
    (hAsymm : ∀ q y, (A q y).toLinearMap.IsSymmetric)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ F)
    (x : M) (hx : I.IsInteriorPoint x)
    (X : ℝ → (y : M) → TangentSpace I y)
    (reaction : V x →L[ℝ] V x) (hreaction : reaction.IsPositive)
    (hGconn : G.connection t = LeviCivita (G.metric t))
    (hAt : DifferentiableAt ℝ (fun q => A q x) t)
    (hevolution : deriv (fun q => A q x) t =
      rawBundleEndomorphismConnLap (G.metric t) cov (fun y => A t y) x +
        HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y => A t y) x (X t x) + reaction) :
    let _ : ∀ y, FiniteDimensional ℝ (V y) :=
      fun y => VectorBundle.finiteDimensional ℝ F V y
    Nonempty (ParabolicUpperSupportAt G T X
      (fun q y => (hAsymm q y).lowerKyFanSum k) t x) := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) :=
    fun y => VectorBundle.finiteDimensional ℝ F V y
  have hkx : k ≤ Module.finrank ℝ (V x) := by
    rw [VectorBundle.finrank_eq ℝ F V x]
    exact hk
  obtain ⟨v₀, eigenvalue, hv₀, heigen, hsum⟩ :=
    (hAsymm t x).exists_eigenframe_lowerKyFanSum_eq hkx
  obtain ⟨U, hU, hxU, v, hvOrth, hvx, hvNormal⟩ :=
    exists_orthonormal_normal_sections cov hcov x v₀ hv₀
  let trace : ℝ → M → ℝ := fun q y =>
    ∑ i, inner ℝ (A q y (v i y)) (v i y)
  have htrace_eq : trace t x = (hAsymm t x).lowerKyFanSum k := by
    dsimp only [trace]
    calc
      ∑ i, inner ℝ (A t x (v i x)) (v i x) = ∑ i, eigenvalue i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hvx i]
        change inner ℝ ((A t x).toLinearMap (v₀ i)) (v₀ i) = _
        rw [heigen i, inner_smul_left]
        simp [hv₀.norm_eq_one]
      _ = _ := hsum
  have htrace_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (trace t) := by
    dsimp only [trace]
    exact ContMDiff.sum (fun i _ =>
      (ContMDiff.clm_bundle_apply (b := id) (A t).contMDiff
        (v i).contMDiff).inner_bundle (v i).contMDiff)
  have hunit (i : Fin k) : ∀ᶠ y in 𝓝 x, inner ℝ (v i y) (v i y) = 1 := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    simpa [orthonormal_iff_ite] using
      (orthonormal_iff_ite.mp (hvOrth y hy) i i)
  refine ⟨{
    upperSupport := trace
    eq_at := htrace_eq
    upper_nhds := ?_
    time_diff := ?_
    space_diff_nhds := Filter.Eventually.of_forall (fun y =>
      htrace_smooth.mdifferentiableAt (by simp))
    grad_diff := (gradientFun_smooth (G.metric t) htrace_smooth).mdifferentiableAt
      (by simp)
    operator_nonneg := ?_ }⟩
  · have hsupport : ∀ᶠ p : ℝ × M in 𝓝 (t, x),
        (hAsymm p.1 p.2).lowerKyFanSum k ≤ trace p.1 p.2 := by
      filter_upwards [continuousAt_snd.eventually (hU.mem_nhds hxU)] with p hp
      exact (hAsymm p.1 p.2).lowerKyFanSum_le_frame
        (by rw [VectorBundle.finrank_eq ℝ F V p.2]; exact hk) (hvOrth p.2 hp)
    exact hsupport.filter_mono inf_le_left
  · apply DifferentiableAt.differentiableWithinAt
    exact DifferentiableAt.fun_sum fun i _ =>
      (hAt.clm_apply (differentiableAt_const (c := v i x))).inner ℝ
        (differentiableAt_const (c := v i x))
  · have hop := parabolicOperatorWithDrift_sum_inner_endomorphism_apply_of_normal_eigenframe
      G cov hcov hT ht A v x hx X eigenvalue hGconn hAt (hAsymm t x)
      (fun i => by rw [hvx i]; exact heigen i) hvNormal hunit
    have hresidual : deriv (fun q => A q x) t -
        rawBundleEndomorphismConnLap (G.metric t) cov (fun y => A t y) x -
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V cov cov (fun y => A t y) x (X t x) = reaction := by
      rw [hevolution]
      abel
    rw [hop, hresidual]
    exact Finset.sum_nonneg fun i _ => hreaction.inner_nonneg_left (v i x)

end DifferentialGeometry.Analysis.Parabolic
