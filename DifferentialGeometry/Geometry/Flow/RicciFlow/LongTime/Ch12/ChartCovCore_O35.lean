import DifferentialGeometry.Geometry.Connection.TensorNabla.FixedChart.FiniteMetricRegularity

/-!
# CH12-O35 chartCov core: the fixed-chart derivative formula for `∇`

In a fixed chart `c` (boundaryless model), on `V = target ∩ symm⁻¹ W` where the tensor field is
smooth, the model representative `f_j := tensor0SModelInChart (s+j) c (∇^j T)` satisfies
`D f_j = curryLeft (f_{j+1}) + B(Γ, f_j)` with `Γ` the Levi-Civita connection endomorphism in the
chart and `B` the (continuous bilinear) Lie-derivative correction.  This is the common core of
both directions of `[FROZEN] CH12-O35 chartCov`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Lie-derivative correction as a continuous bilinear map `(Γ, α) ↦ (X ↦ corr(Γ X) α)`. -/
def corrBilin_O35 (σ : ℕ) :
    (E →L[ℝ] E →L[ℝ] E) →L[ℝ] Tensor0SModel σ ℝ E →L[ℝ] (E →L[ℝ] Tensor0SModel σ ℝ E) :=
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  (ContinuousLinearMap.flipₗᵢ ℝ E (Tensor0SModel σ ℝ E)
      (Tensor0SModel σ ℝ E)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E)
      (Tensor0SModel σ ℝ E →L[ℝ] Tensor0SModel σ ℝ E) (lieDerivCorrectionOpL σ))

theorem corrBilin_O35_apply (σ : ℕ) (Γ : E →L[ℝ] E →L[ℝ] E) (α : Tensor0SModel σ ℝ E) (X : E) :
    haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
    corrBilin_O35 (E := E) σ Γ α X = lieDerivCorrection σ (Γ X) α := by
  simp [corrBilin_O35]

/-- `Dα = curryLeft (totalCov Dα Γ α) + B(Γ, α)` (pointwise algebra). -/
theorem eq_curry_totalCov_add_O35 (σ : ℕ) (Dα : E →L[ℝ] Tensor0SModel σ ℝ E)
    (Γ : E →L[ℝ] E →L[ℝ] E) (α : Tensor0SModel σ ℝ E) :
    haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Dα = continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (σ + 1) => E) ℝ
        (totalCovDerivTensor0SModelAt σ Dα Γ α) + corrBilin_O35 (E := E) σ Γ α := by
  ext X slots
  simp only [add_apply, continuousMultilinearCurryLeftEquiv_apply,
    totalCovDeriv_tensor0SModelAt_apply_cons, corrBilin_O35_apply,
    covariantDeriv_tensor0SModelAt_apply, sub_apply]
  ring

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Model regularity in a fixed chart (public copy of a private library lemma, boundaryless). -/
theorem contDiffAt_tensor0SModelInChart_O35 (n s : ℕ)
    (A : (p : M) → Tensor0SSpace s I p) (c : M) {y : E} (hy : y ∈ (extChartAt I c).target)
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) n
      (fun p => (⟨p, A p⟩ : TotalSpace (Tensor0SModel s ℝ E)
        (fun q => Tensor0SSpace s I q))) ((extChartAt I c).symm y)) :
    ContDiffAt ℝ n (tensor0SModelInChart s c A) y := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  let e := trivializationAt (Tensor0SModel s ℝ E) (fun p => Tensor0SSpace s I p) c
  have hp : (extChartAt I c).symm y ∈ e.baseSet := by
    change (extChartAt I c).symm y ∈
      (trivializationAt E (TangentSpace I : M → Type _) c).baseSet
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt I c).map_target hy
  have hcoord : ContMDiffAt I 𝓘(ℝ, Tensor0SModel s ℝ E) n
      (fun p => (e ⟨p, A p⟩).2) ((extChartAt I c).symm y) :=
    (e.contMDiffAt_section_iff hp).mp hA
  have hcomp := hcoord.comp_contMDiffWithinAt (x := y)
    (contMDiffWithinAt_extChartAt_symm_range (I := I) (n := n) c hy)
  have hw : ContDiffWithinAt ℝ n (tensor0SModelInChart s c A) (Set.range I) y := by
    change ContDiffWithinAt ℝ n
      ((fun p : M => (e ⟨p, A p⟩).2) ∘ (extChartAt I c).symm) (Set.range I) y
    exact hcomp.contDiffWithinAt
  rwa [I.range_eq_univ, contDiffWithinAt_univ] at hw

omit [FiniteDimensional ℝ E] in
theorem natCast_add_sub_O35 (n j : ℕ) :
    ((n + j : ℕ) : WithTop ℕ∞) - (j : WithTop ℕ∞) = (n : WithTop ℕ∞) := by
  change (((n + j : ℕ) : ℕ∞) : WithTop ℕ∞) - (((j : ℕ) : ℕ∞) : WithTop ℕ∞) =
    (((n : ℕ) : ℕ∞) : WithTop ℕ∞)
  rw [← WithTop.coe_sub, ← ENat.natCast_sub, Nat.add_sub_cancel]

variable [T2Space M]

/-- All covariant derivatives of a field smooth on `W` have smooth chart representatives on
`target ∩ symm⁻¹ W`. -/
theorem contDiffAt_iter_model_O35 (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : (p : M) → Tensor0SSpace s I p) (c : M) {W : Set M} (hW : IsOpen W)
    (hT : ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
        (fun p => (⟨p, T p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) W)
    {y : E} (hy : y ∈ (extChartAt I c).target) (hyW : (extChartAt I c).symm y ∈ W) (j : ℕ) :
    ContDiffAt ℝ ∞ (tensor0SModelInChart (s + j) c (iteratedMetricCovariantDerivative g s T j)) y := by
  rw [contDiffAt_infty]
  intro n
  have hA := (hT.contMDiffAt (hW.mem_nhds hyW)).of_le
    (show ((n + j : ℕ) : WithTop ℕ∞) ≤ ∞ from by exact_mod_cast le_top)
  have h := contMDiffAt_iteratedMetricCovariantDerivative g (n + j) s T _ hA j (by omega)
  rw [natCast_add_sub_O35] at h
  exact contDiffAt_tensor0SModelInChart_O35 n (s + j) _ c hy h

/-- **Fixed-chart derivative formula** for the iterated covariant derivatives. -/
theorem fderiv_iter_model_O35 (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : (p : M) → Tensor0SSpace s I p) (c : M) {W : Set M} (hW : IsOpen W)
    (hT : ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
        (fun p => (⟨p, T p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) W)
    {y : E} (hy : y ∈ (extChartAt I c).target) (hyW : (extChartAt I c).symm y ∈ W) (j : ℕ) :
    haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
    fderiv ℝ (tensor0SModelInChart (s + j) c (iteratedMetricCovariantDerivative g s T j)) y =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + j + 1) => E) ℝ
          (tensor0SModelInChart (s + (j + 1)) c (iteratedMetricCovariantDerivative g s T (j + 1)) y) +
        corrBilin_O35 (E := E) (s + j) (connectionEndomorphismInChartL (leviCivitaConnectionOfMetric g) c y)
          (tensor0SModelInChart (s + j) c (iteratedMetricCovariantDerivative g s T j) y) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hA := (hT.contMDiffAt (hW.mem_nhds hyW)).of_le
    (show ((1 + j : ℕ) : WithTop ℕ∞) ≤ ∞ from by exact_mod_cast le_top)
  have h1 := contMDiffAt_iteratedMetricCovariantDerivative g (1 + j) s T _ hA j (by omega)
  rw [natCast_add_sub_O35] at h1
  have hf := tensor0SModelInChart_metricCovariantDerivative g (s + j)
    (iteratedMetricCovariantDerivative g s T j) c hy (by exact_mod_cast h1)
  rw [I.range_eq_univ, fderivWithin_univ] at hf
  change _ = continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + j + 1) => E) ℝ
      (tensor0SModelInChart (s + j + 1) c
        (metricCovariantDerivative g (s + j) (iteratedMetricCovariantDerivative g s T j)) y) + _
  rw [hf]
  exact eq_curry_totalCov_add_O35 _ _ _ _

end GC.LongTime.Ch12
