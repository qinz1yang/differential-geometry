import DifferentialGeometry.Geometry.Connection.TensorNabla.FixedChart.FiniteMetricRegularity
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.JetCongruence

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem tensor0SModelInChart_metricCovariantDerivative_eventuallyEq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : (p : M) → Tensor0SSpace s I p) (x : M)
    (hx : Set.range I ∈ 𝓝 (extChartAt I x x))
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) 1
      (fun p => (⟨p, A p⟩ : TotalSpace (Tensor0SModel s ℝ E)
        (fun q => Tensor0SSpace s I q))) x) :
    tensor0SModelInChart (s + 1) x (metricCovariantDerivative g s A)
      =ᶠ[𝓝 (extChartAt I x x)]
        (fun y => totalCovDerivTensor0SModelAt s
          (fderiv ℝ (tensor0SModelInChart s x A) y)
          (connectionEndomorphismInChartL (leviCivitaConnectionOfMetric g) x y)
          (tensor0SModelInChart s x A y)) := by
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp hA
  have hnear' : ∀ᶠ y in 𝓝 (extChartAt I x x),
      ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) 1
        (fun p => (⟨p, A p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) ((extChartAt I x).symm y) := by
    apply (continuousAt_extChartAt_symm (I := I) x).tendsto.eventually
    simpa only [extChartAt_to_inv] using hnear
  have htarget : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) := by
    simpa only [nhdsWithin_eq_nhds.mpr hx] using
      extChartAt_target_mem_nhdsWithin (I := I) x
  filter_upwards [htarget, hnear', eventually_mem_nhds_iff.mpr hx] with y hy hAy hIy
  rw [tensor0SModelInChart_metricCovariantDerivative g s A x hy hAy,
    fderivWithin_of_mem_nhds hIy]

/-- One actual covariant derivative preserves the remaining coordinate jets:
jets through order `n + 1` of finite-regularity raw tensors determine all
coordinate jets through order `n` of their covariant derivatives. -/
theorem iteratedFDeriv_metricCovariantDerivative_eq_of_coordinate_jets
    (g : SmoothRiemannianMetric I M) (n s : ℕ)
    (A B : (p : M) → Tensor0SSpace s I p) (x : M)
    (hx : Set.range I ∈ 𝓝 (extChartAt I x x))
    (hA : ContDiffAt ℝ (n + 1) (tensor0SModelInChart s x A) (extChartAt I x x))
    (hB : ContDiffAt ℝ (n + 1) (tensor0SModelInChart s x B) (extChartAt I x x))
    (hjets : ∀ j ≤ n + 1,
      iteratedFDeriv ℝ j (tensor0SModelInChart s x A) (extChartAt I x x) =
        iteratedFDeriv ℝ j (tensor0SModelInChart s x B) (extChartAt I x x))
    (k : ℕ) (hk : k ≤ n) :
    iteratedFDeriv ℝ k
        (tensor0SModelInChart (s + 1) x (metricCovariantDerivative g s A))
        (extChartAt I x x) =
      iteratedFDeriv ℝ k
        (tensor0SModelInChart (s + 1) x (metricCovariantDerivative g s B))
        (extChartAt I x x) := by
  let Γ := connectionEndomorphismInChartL (leviCivitaConnectionOfMetric g) x
  let Φ : E × Tensor0SModel s ℝ E × (E →L[ℝ] Tensor0SModel s ℝ E) →
      Tensor0SModel (s + 1) ℝ E :=
    fun z => totalCovDerivTensor0SModelAt s z.2.2 (Γ z.1) z.2.1
  have hΓ : ContDiffAt ℝ n Γ (extChartAt I x x) :=
    ((connectionEndomorphismInChartL_contDiffWithinAt (leviCivitaConnectionOfMetric g)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally g) x
      (mem_extChartAt_target (I := I) x)).of_le (by simp)).contDiffAt hx
  have hΦ : ContDiffAt ℝ n Φ
      (extChartAt I x x, tensor0SModelInChart s x A (extChartAt I x x),
        fderiv ℝ (tensor0SModelInChart s x A) (extChartAt I x x)) := by
    rw [← contDiffWithinAt_univ]
    exact contDiffWithinAt_totalCovDerivTensor0SModelAt s
      contDiffWithinAt_snd.snd
      (hΓ.comp
        (extChartAt I x x, tensor0SModelInChart s x A (extChartAt I x x),
          fderiv ℝ (tensor0SModelInChart s x A) (extChartAt I x x))
        contDiffAt_fst).contDiffWithinAt
      contDiffWithinAt_snd.fst
  have hAone := (contMDiffAt_tensor0S_iff_contDiffWithinAt_model 1 s A x).mpr
    ((hA.of_le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))).contDiffWithinAt)
  have hBone := (contMDiffAt_tensor0S_iff_contDiffWithinAt_model 1 s B x).mpr
    ((hB.of_le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))).contDiffWithinAt)
  have hAgerm := tensor0SModelInChart_metricCovariantDerivative_eventuallyEq g s A x hx hAone
  have hBgerm := tensor0SModelInChart_metricCovariantDerivative_eventuallyEq g s B x hx hBone
  calc
    _ = iteratedFDeriv ℝ k
        (fun y => Φ (y, tensor0SModelInChart s x A y,
          fderiv ℝ (tensor0SModelInChart s x A) y)) (extChartAt I x x) :=
      (hAgerm.iteratedFDeriv ℝ k).self_of_nhds
    _ = iteratedFDeriv ℝ k
        (fun y => Φ (y, tensor0SModelInChart s x B y,
          fderiv ℝ (tensor0SModelInChart s x B) y)) (extChartAt I x x) :=
      DifferentialGeometry.Analysis.iteratedFDeriv_comp_value_fderiv_eq_of_eq_jets
        hA hB hΦ hjets k hk
    _ = _ := (hBgerm.iteratedFDeriv ℝ k).self_of_nhds.symm

/-- Finite coordinate jets of raw tensors determine their actual iterated
covariant derivatives through that same finite order, under one fixed smooth
metric. The coordinate interior condition is local to the selected point. -/
theorem iteratedMetricCovariantDerivative_eq_of_coordinate_jets
    (g : SmoothRiemannianMetric I M) (N s : ℕ)
    (A B : (p : M) → Tensor0SSpace s I p) (x : M)
    (hx : Set.range I ∈ 𝓝 (extChartAt I x x))
    (hA : ContDiffAt ℝ N (tensor0SModelInChart s x A) (extChartAt I x x))
    (hB : ContDiffAt ℝ N (tensor0SModelInChart s x B) (extChartAt I x x))
    (hjets : ∀ j ≤ N,
      iteratedFDeriv ℝ j (tensor0SModelInChart s x A) (extChartAt I x x) =
        iteratedFDeriv ℝ j (tensor0SModelInChart s x B) (extChartAt I x x))
    (k : ℕ) (hk : k ≤ N) :
    iteratedMetricCovariantDerivative g s A k x =
      iteratedMetricCovariantDerivative g s B k x := by
  have hAsec := (contMDiffAt_tensor0S_iff_contDiffWithinAt_model N s A x).mpr
    hA.contDiffWithinAt
  have hBsec := (contMDiffAt_tensor0S_iff_contDiffWithinAt_model N s B x).mpr
    hB.contDiffWithinAt
  have hregular (C : (p : M) → Tensor0SSpace s I p)
      (hC : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) N
        (fun p => (⟨p, C p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) x)
      (i : ℕ) (hi : i ≤ N) :
      ContDiffAt ℝ (N - i)
        (tensor0SModelInChart (s + i) x (iteratedMetricCovariantDerivative g s C i))
        (extChartAt I x x) :=
    ((contMDiffAt_tensor0S_iff_contDiffWithinAt_model (N - i) (s + i)
      (iteratedMetricCovariantDerivative g s C i) x).mp
        (contMDiffAt_iteratedMetricCovariantDerivative g N s C x hC i hi)).contDiffAt hx
  have hiter : ∀ i ≤ N, ∀ j ≤ N - i,
      iteratedFDeriv ℝ j
          (tensor0SModelInChart (s + i) x (iteratedMetricCovariantDerivative g s A i))
          (extChartAt I x x) =
        iteratedFDeriv ℝ j
          (tensor0SModelInChart (s + i) x (iteratedMetricCovariantDerivative g s B i))
          (extChartAt I x x) := by
    intro i
    induction i with
    | zero =>
      intro _ j hj
      exact hjets j hj
    | succ i ih =>
      intro hi j hj
      have hi' : i ≤ N := by omega
      have horder : N - i = (N - (i + 1)) + 1 := by omega
      have hAi := hregular A hAsec i hi'
      have hBi := hregular B hBsec i hi'
      have hji := ih hi'
      change ContDiffAt ℝ ((N - i : ℕ) : WithTop ℕ∞)
        (tensor0SModelInChart (s + i) x (iteratedMetricCovariantDerivative g s A i))
        (extChartAt I x x) at hAi
      change ContDiffAt ℝ ((N - i : ℕ) : WithTop ℕ∞)
        (tensor0SModelInChart (s + i) x (iteratedMetricCovariantDerivative g s B i))
        (extChartAt I x x) at hBi
      rw [horder] at hAi hBi hji
      exact iteratedFDeriv_metricCovariantDerivative_eq_of_coordinate_jets g
        (N - (i + 1)) (s + i)
        (iteratedMetricCovariantDerivative g s A i)
        (iteratedMetricCovariantDerivative g s B i) x hx hAi hBi hji j hj
  have hzero := congrArg (fun T => T (fun i : Fin 0 => Fin.elim0 i))
    (hiter k hk 0 (Nat.zero_le _))
  have hvalue :
      tensor0SModelAt (s + k) x x (iteratedMetricCovariantDerivative g s A k x) =
        tensor0SModelAt (s + k) x x (iteratedMetricCovariantDerivative g s B k x) := by
    simpa only [iteratedFDeriv_zero_apply,
      tensor0SModelInChart_center_eq_tensor0SModelAt] using hzero
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + k)
  let e := trivializationAt (Tensor0SModel (s + k) ℝ E)
    (fun p : M => Tensor0SSpace (s + k) I p) x
  have hxbase : x ∈ e.baseSet :=
    mem_baseSet_trivializationAt (Tensor0SModel (s + k) ℝ E)
      (fun p : M => Tensor0SSpace (s + k) I p) x
  have hrecover (T : Tensor0SSpace (s + k) I x) :
      e.symm x (tensor0SModelAt (s + k) x x T) = T :=
    e.symm_apply_apply_mk hxbase T
  exact (hrecover _).symm.trans ((congrArg (e.symm x) hvalue).trans (hrecover _))

end DifferentialGeometry.Geometry.Connection
