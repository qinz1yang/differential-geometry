import DifferentialGeometry.Geometry.Connection.TensorNabla.FixedChart.RawMetricDerivative
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

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

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Finite regularity of a raw tensor section is equivalent to finite regularity
of its full coefficients in the preferred chart, within the model range. -/
theorem contMDiffAt_tensor0S_iff_contDiffWithinAt_model
    (n s : ℕ) (A : (p : M) → Tensor0SSpace s I p) (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) n
        (fun p => (⟨p, A p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) x ↔
      ContDiffWithinAt ℝ n (tensor0SModelInChart s x A)
        (Set.range I) (extChartAt I x x) := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  let e := trivializationAt (Tensor0SModel s ℝ E) (fun p => Tensor0SSpace s I p) x
  have hx : x ∈ e.baseSet :=
    mem_baseSet_trivializationAt (Tensor0SModel s ℝ E) (fun p => Tensor0SSpace s I p) x
  rw [e.contMDiffAt_section_iff hx, contMDiffAt_iff_source,
    contMDiffWithinAt_iff_contDiffWithinAt]
  rfl

/-- The complete connection coefficient, including its direction argument, is
smooth in a fixed chart wherever the inverse chart is defined. -/
theorem connectionEndomorphismInChartL_contDiffWithinAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffWithinAt ℝ ∞ (connectionEndomorphismInChartL cov x₀)
      (Set.range I) y := by
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) M :=
    IsManifold.of_le (n := ∞) (by simp)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1 + 1) M :=
    IsManifold.of_le (n := ∞) (by simp)
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have hp : (extChartAt I x₀).symm y ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt I x₀).map_target hy
  refine contDiffWithinAt_clm_apply.mpr fun u => ?_
  refine contDiffWithinAt_clm_apply.mpr fun v => ?_
  let σ : (p : M) → TangentSpace I p := tangentConstInChart (I := I) x₀ v
  let X : (p : M) → TangentSpace I p := tangentConstInChart (I := I) x₀ u
  let W : (p : M) → TangentSpace I p := fun p => (cov σ p) (X p)
  have hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (∞ + 1)
      (fun p => (⟨p, σ p⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      e.baseSet := by
    simpa only [e, σ] using
      (tangentConstInChart_contMDiffOn_baseSet (I := I) (n := ∞ + 1) x₀ v)
  have hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun p => (⟨p, X p⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      e.baseSet := by
    simpa only [e, X] using
      (tangentConstInChart_contMDiffOn_baseSet (I := I) (n := ∞) x₀ u)
  have hcovσ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p => (⟨p, cov σ p⟩ : TotalSpace (E →L[ℝ] E)
        (fun q => TangentSpace I q →L[ℝ] TangentSpace I q))) e.baseSet :=
    (hcov e.open_baseSet).contMDiff hσ
  have hW : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun p => (⟨p, W p⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      ((extChartAt I x₀).symm y) :=
    (hcovσ.clm_bundle_apply hX).contMDiffAt (e.open_baseSet.mem_nhds hp)
  have hcoord : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun p => (e ⟨p, W p⟩).2) ((extChartAt I x₀).symm y) :=
    (e.contMDiffAt_section_iff hp).mp hW
  have hcomp := hcoord.comp_contMDiffWithinAt (x := y)
    (contMDiffWithinAt_extChartAt_symm_range (I := I) (n := ∞) x₀ hy)
  have heq : ∀ z ∈ (extChartAt I x₀).target,
      connectionEndomorphismInChartL cov x₀ z u v =
        (e ⟨(extChartAt I x₀).symm z, W ((extChartAt I x₀).symm z)⟩).2 := by
    intro z hz
    have hpz : (extChartAt I x₀).symm z ∈ e.baseSet := by
      simpa only [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using
        (extChartAt I x₀).map_target hz
    rw [connectionEndomorphismInChartL_apply_of_mem cov x₀ hz]
    exact e.continuousLinearMapAt_apply_of_mem ℝ hpz _
  apply hcomp.contDiffWithinAt.congr_of_eventuallyEq ?_ (heq y hy)
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hy] with z hz
  exact heq z hz

/-- The algebraic total covariant derivative preserves the regularity of its
derivative, connection, and tensor arguments. -/
theorem contDiffWithinAt_totalCovDerivTensor0SModelAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : ℕ) {n : WithTop ℕ∞} {S : Set F} {x : F}
    {D : F → E →L[ℝ] Tensor0SModel s ℝ E}
    {Γ : F → E →L[ℝ] E →L[ℝ] E} {A : F → Tensor0SModel s ℝ E}
    (hD : ContDiffWithinAt ℝ n D S x)
    (hΓ : ContDiffWithinAt ℝ n Γ S x)
    (hA : ContDiffWithinAt ℝ n A S x) :
    ContDiffWithinAt ℝ n (fun y => totalCovDerivTensor0SModelAt s (D y) (Γ y) (A y))
      S x := by
  let c : Tensor0SModel (s + 1) ℝ E ≃L[ℝ] (E →L[ℝ] Tensor0SModel s ℝ E) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E) ℝ).toContinuousLinearEquiv
  have hcurried : ContDiffWithinAt ℝ n
      (fun y => c (totalCovDerivTensor0SModelAt s (D y) (Γ y) (A y))) S x := by
    refine contDiffWithinAt_clm_apply.mpr fun v => ?_
    change ContDiffWithinAt ℝ n
      (fun y => covariantDerivTensor0SModelAt s (D y v) (Γ y v) (A y)) S x
    have hcorrection := (hΓ.clm_apply (contDiffWithinAt_const (c := v))).continuousLinearMap_comp
      (lieDerivCorrectionOpL (𝕜 := ℝ) (E := E) s)
    simpa only [Function.comp_apply, covariantDerivTensor0SModelAt, lieDeriv_correctionOpL_apply,
      lieDeriv_correctionL_apply] using
      (hD.clm_apply (contDiffWithinAt_const (c := v))).sub (hcorrection.clm_apply hA)
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
    c.symm.contDiff.comp_contDiffWithinAt hcurried

/-- One actual metric covariant derivative loses exactly one finite derivative
of a raw tensor section. The statement also applies at boundary points. -/
theorem contMDiffAt_metricCovariantDerivative [T2Space M]
    (g : SmoothRiemannianMetric I M) (n s : ℕ)
    (A : (p : M) → Tensor0SSpace s I p) (x : M)
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) (n + 1)
      (fun p => (⟨p, A p⟩ : TotalSpace (Tensor0SModel s ℝ E)
        (fun q => Tensor0SSpace s I q))) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) n
      (fun p => (⟨p, metricCovariantDerivative g s A p⟩ :
        TotalSpace (Tensor0SModel (s + 1) ℝ E)
          (fun q => Tensor0SSpace (s + 1) I q))) x := by
  have hmodel := (contMDiffAt_tensor0S_iff_contDiffWithinAt_model (n + 1) s A x).mp hA
  have hΓ : ContDiffWithinAt ℝ n
      (connectionEndomorphismInChartL (leviCivitaConnectionOfMetric g) x)
      (Set.range I) (extChartAt I x x) :=
    (connectionEndomorphismInChartL_contDiffWithinAt (leviCivitaConnectionOfMetric g)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally g) x
      (mem_extChartAt_target (I := I) x)).of_le (by simp)
  have hD : ContDiffWithinAt ℝ n
      (fderivWithin ℝ (tensor0SModelInChart s x A) (Set.range I))
      (Set.range I) (extChartAt I x x) :=
    hmodel.fderivWithin_right I.uniqueDiffOn (by simp)
      (extChartAt_target_subset_range x (mem_extChartAt_target (I := I) x))
  have hformula := contDiffWithinAt_totalCovDerivTensor0SModelAt s hD hΓ
    (hmodel.of_le (by exact_mod_cast Nat.le_succ n))
  have hAone : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) 1
      (fun p => (⟨p, A p⟩ : TotalSpace (Tensor0SModel s ℝ E)
        (fun q => Tensor0SSpace s I q))) x :=
    hA.of_le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp hAone
  have hnear' : ∀ᶠ y in 𝓝[Set.range I] (extChartAt I x x),
      ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) 1
        (fun p => (⟨p, A p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) ((extChartAt I x).symm y) := by
    have h := ((continuousAt_extChartAt_symm (I := I) x).continuousWithinAt
      (s := Set.range I)).tendsto
    apply h.eventually
    simpa only [extChartAt_to_inv] using hnear
  apply (contMDiffAt_tensor0S_iff_contDiffWithinAt_model n (s + 1)
    (metricCovariantDerivative g s A) x).mpr
  apply hformula.congr_of_eventuallyEq
  · filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x, hnear'] with y hy hAy
    exact tensor0SModelInChart_metricCovariantDerivative g s A x hy hAy
  · apply tensor0SModelInChart_metricCovariantDerivative g s A x
      (mem_extChartAt_target (I := I) x)
    simpa only [extChartAt_to_inv] using hAone

/-- Through finite order `N`, each actual covariant derivative retains the
remaining `N - k` derivatives of the original raw tensor section. -/
theorem contMDiffAt_iteratedMetricCovariantDerivative [T2Space M]
    (g : SmoothRiemannianMetric I M) (N s : ℕ)
    (A : (p : M) → Tensor0SSpace s I p) (x : M)
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) N
      (fun p => (⟨p, A p⟩ : TotalSpace (Tensor0SModel s ℝ E)
        (fun q => Tensor0SSpace s I q))) x)
    (k : ℕ) (hk : k ≤ N) :
    ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel (s + k) ℝ E)) (N - k)
      (fun p => (⟨p, iteratedMetricCovariantDerivative g s A k p⟩ :
        TotalSpace (Tensor0SModel (s + k) ℝ E)
          (fun q => Tensor0SSpace (s + k) I q))) x := by
  induction k with
  | zero =>
    simpa only [Nat.cast_zero, tsub_zero, Nat.add_zero,
      iteratedMetricCovariantDerivative] using hA
  | succ k ih =>
    have hprev := ih (by omega)
    change ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel (s + k) ℝ E))
      ((N - k : ℕ) : WithTop ℕ∞)
      (fun p => (⟨p, iteratedMetricCovariantDerivative g s A k p⟩ :
        TotalSpace (Tensor0SModel (s + k) ℝ E)
          (fun q => Tensor0SSpace (s + k) I q))) x at hprev
    have horder : N - k = (N - (k + 1)) + 1 := by omega
    rw [horder] at hprev
    exact contMDiffAt_metricCovariantDerivative g (N - (k + 1)) (s + k)
      (iteratedMetricCovariantDerivative g s A k) x hprev

end DifferentialGeometry.Geometry.Connection
