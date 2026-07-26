import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Parametrized evaluation of Riemannian volume

This file starts the Integration-layer API for evaluating the Riemannian volume
measure through a supplied coordinate parametrization.  The main downstream
consumer is the volume-comparison lane, where the parametrization will be the
normal-coordinate partial diffeomorphism.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal Matrix

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The Gram matrix pulled back by a `C¹` coordinate parametrization.

Mathematically, at a source point `w` this is the matrix
`g_{Ψ w}(dΨ_w e_i, dΨ_w e_j)` in the fixed model basis of `E`.  The regularity
needed for interpreting `mfderiv` on the source is the `C¹` data carried by
`Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1`.  The volume-comparison lane consumes
this at `Ψ := expMapDiffeo g x`; the same object is also the density input for
polar and entropy integrals. -/
def paramGramMatrix (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) :
    E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun w => Matrix.of fun i j =>
    g.inner (Ψ w)
      (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
      (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j))

set_option linter.unusedSectionVars false in
/-- Pointwise unfolding of the pulled-back parametrization Gram matrix.

This is the direct API for consumers that need to compare the parametrized
density with a canonical chart density.  It uses only the `C¹` derivative of
the parametrization and is consumed by V0a/V1a rewriting. -/
@[simp] lemma paramGramMatrix_apply
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    (w : E) (i j : Fin (Module.finrank ℝ E)) :
    paramGramMatrix (I := I) g Ψ w i j =
      g.inner (Ψ w)
        (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
        (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j)) := rfl

/-- The Riemannian density of a coordinate parametrization.

This is `sqrt(det paramGramMatrix)`.  It is mathematically positive on the
source of the partial diffeomorphism because `dΨ` is an isomorphism there, and
continuous on the source from the `C¹` parametrization and the smooth metric.
The V1 normal-chart formula, V2 polar transfer, and entropy integral estimates
consume this scalar density. -/
def paramDensity (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) : E → ℝ :=
  fun w => Real.sqrt (paramGramMatrix (I := I) g Ψ w).det

set_option linter.unusedSectionVars false in
/-- Pointwise unfolding of the parametrization density.

This exposes the `sqrt(det Gram)` normal form used by the V0 transformation
law and by the V1 normal-coordinate specialization. -/
@[simp] lemma paramDensity_apply
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    (w : E) :
    paramDensity (I := I) g Ψ w =
      Real.sqrt (paramGramMatrix (I := I) g Ψ w).det := rfl

/-- The differential of a parametrizing partial diffeomorphism is a continuous
linear equivalence at every source point.

This is true because a `C¹` partial diffeomorphism is a local diffeomorphism on
its open source.  V0a uses the equivalence to identify the pulled-back Gram
with a congruence of the canonical chart Gram, and V1a uses it to get positivity
of the normal-coordinate density. -/
noncomputable def paramDerivEquiv
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source) :
    E ≃L[ℝ] TangentSpace I (Ψ w) :=
  (PartialDiffeomorph.isLocalDiffeomorphAt
    (I := 𝓘(ℝ, E)) (J := I) (n := 1) Ψ hw).mfderivToContinuousLinearEquiv
      (by norm_num)

set_option linter.unusedSectionVars false in
/-- The parametrization differential has trivial kernel on the source.

This is the linear-algebra form of local invertibility needed to prove that
the pulled-back Gram matrix is positive definite; it only uses the `C¹`
partial-diffeomorphism structure of `Ψ`. -/
lemma paramDeriv_ker
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source) :
    (mfderiv 𝓘(ℝ, E) I Ψ w).ker = ⊥ := by
  have hlocal :=
    PartialDiffeomorph.isLocalDiffeomorphAt
      (I := 𝓘(ℝ, E)) (J := I) (n := 1) Ψ hw
  apply LinearMap.ker_eq_bot.mpr
  intro v hv
  apply (hlocal.mfderivToContinuousLinearEquiv (by norm_num)).injective

/-- The model-space representative of a parametrization in the canonical chart
centered at `x₀`.

This is the Euclidean map whose Jacobian appears in the V0a change-of-variables
step: for `Ψ := expMapDiffeo g x`, it is the normal parametrization written in
the canonical chart at `x₀`.  Only `C¹` regularity of `Ψ` is needed. -/
def paramChartMap (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) : E → E :=
  fun w => extChartAt I x₀ (Ψ w)

/-- The Jacobian matrix of `paramChartMap` in the fixed model basis.

This is the matrix `D(extChartAt x₀ ∘ Ψ)_w` used in the V0a Gram transformation
law and in the V0b Euclidean change-of-variables formula.  V1a consumes the
specialization where `Ψ` is the normal-coordinate exponential diffeomorphism. -/
def paramJacobianMatrix (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) (w : E) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
    (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).toLinearMap

set_option linter.unusedSectionVars false in
/-- Entrywise unfolding of the parametrized Jacobian matrix.

The `(k,i)` entry is the `k`-th coordinate, in the fixed model basis, of
`D(extChartAt x₀ ∘ Ψ)_w(e_i)`.  This is the coefficient form used by the V0a
Gram pullback proof. -/
@[simp] lemma paramJacobianMatrix_apply
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) (w : E)
    (k i : Fin (Module.finrank ℝ E)) :
    paramJacobianMatrix (I := I) x₀ Ψ w k i =
      (chartModelBasis E).repr
        ((fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w)
          ((chartModelBasis E) i)) k := by
  simp [paramJacobianMatrix, LinearMap.toMatrix_apply]

set_option linter.unusedSectionVars false in
/-- The parametrization derivative decomposes in the canonical chart basis.

At a source point whose image lies in the canonical chart at `x₀`, the derivative
`dΨ_w(e_i)` is obtained by applying the inverse chart derivative to
`D(extChartAt x₀ ∘ Ψ)_w(e_i)`.  Expanding the latter in the fixed model basis
gives this coefficient formula.  This is the missing bridge needed before the
V0a Gram transformation can reuse the existing chart-density algebra. -/
lemma paramDeriv_chartBasis_eq_sum
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source)
    (hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i) =
      ∑ k, paramJacobianMatrix (I := I) x₀ Ψ w k i •
        chartBasisVecFiber (I := I) x₀ k (Ψ w) := by
  have hxchart : Ψ w ∈ (chartAt H x₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) x₀] using hx
  have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hxchart
  have hΨdiff : MDifferentiableAt 𝓘(ℝ, E) I Ψ w :=
    (Ψ.contMDiffOn_toFun.mdifferentiableOn one_ne_zero w hw).mdifferentiableAt
      (Ψ.open_source.mem_nhds hw)
  have hchartdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) (Ψ w) :=
    mdifferentiableAt_extChartAt (I := I) (x := x₀) (y := Ψ w) hxchart
  have hchain :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (paramChartMap (I := I) x₀ Ψ) w =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (Ψ w)).comp
          (mfderiv 𝓘(ℝ, E) I Ψ w) := by
    simpa [paramChartMap, Function.comp_def] using
      (mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E))
        (g := extChartAt I x₀) (f := Ψ) (x := w) hchartdiff hΨdiff)
  have hchain_f :
      fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (Ψ w)).comp
          (mfderiv 𝓘(ℝ, E) I Ψ w) := by
    simpa [mfderiv_eq_fderiv] using hchain
  set T₀ : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) x₀
  apply (T₀.continuousLinearEquivAt ℝ (Ψ w) hx).injective
  have hrepr :
      (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) ((chartModelBasis E) i) =
        ∑ k, paramJacobianMatrix (I := I) x₀ Ψ w k i •
          (chartModelBasis E) k := by
    simpa [paramJacobianMatrix_apply] using
      (((chartModelBasis E).sum_repr
        ((fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w)
          ((chartModelBasis E) i))).symm)
  calc
    T₀.continuousLinearEquivAt ℝ (Ψ w) hx
        (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
        = (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) ((chartModelBasis E) i) := by
          rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) T₀ hx]
          rw [TangentBundle.continuousLinearMapAt_trivializationAt
            (I := I) (x₀ := x₀) (x := Ψ w) hxchart]
          rw [hchain_f]
          rfl
    _ = ∑ k, paramJacobianMatrix (I := I) x₀ Ψ w k i •
          (chartModelBasis E) k := hrepr
    _ = T₀.continuousLinearEquivAt ℝ (Ψ w) hx
          (∑ k, paramJacobianMatrix (I := I) x₀ Ψ w k i •
            chartBasisVecFiber (I := I) x₀ k (Ψ w)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [map_smul]
          have hbasis :
              chartBasisVecFiber (I := I) x₀ k (Ψ w) =
                (T₀.continuousLinearEquivAt ℝ (Ψ w) hx).symm
                  ((chartModelBasis E) k) := by
            change T₀.symm (Ψ w) ((chartModelBasis E) k) =
              (T₀.continuousLinearEquivAt ℝ (Ψ w) hx).symm ((chartModelBasis E) k)
            rfl
          rw [hbasis]
          rw [ContinuousLinearEquiv.apply_symm_apply]

set_option linter.unusedSectionVars false in
/-- Entrywise V0a Gram transformation law.

On the overlap where the parametrization lands in the canonical chart at `x₀`,
the pulled-back parametrization Gram matrix is the chart Gram matrix evaluated
on the Jacobian columns of `extChartAt x₀ ∘ Ψ`.  This is the coefficient form
used by the matrix and density versions consumed by V1a, V2a, and entropy
integrals. -/
lemma paramGramMatrix_pullback_eq_sum
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source)
    (hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    paramGramMatrix (I := I) g Ψ w i j =
      ∑ k, ∑ l,
        paramJacobianMatrix (I := I) x₀ Ψ w k i *
        paramJacobianMatrix (I := I) x₀ Ψ w l j *
        chartGramMatrix g x₀ (Ψ w) k l := by
  rw [paramGramMatrix_apply]
  rw [paramDeriv_chartBasis_eq_sum (I := I) x₀ Ψ hw hx i]
  rw [paramDeriv_chartBasis_eq_sum (I := I) x₀ Ψ hw hx j]
  have hL :
      g.inner (Ψ w)
          (∑ k, paramJacobianMatrix (I := I) x₀ Ψ w k i •
            chartBasisVecFiber (I := I) x₀ k (Ψ w))
        = ∑ k, paramJacobianMatrix (I := I) x₀ Ψ w k i •
            g.inner (Ψ w) (chartBasisVecFiber (I := I) x₀ k (Ψ w)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  rw [hL]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [ContinuousLinearMap.smul_apply]
  have hR :
      g.inner (Ψ w) (chartBasisVecFiber (I := I) x₀ k (Ψ w))
          (∑ l, paramJacobianMatrix (I := I) x₀ Ψ w l j •
            chartBasisVecFiber (I := I) x₀ l (Ψ w))
        = ∑ l, paramJacobianMatrix (I := I) x₀ Ψ w l j *
            g.inner (Ψ w) (chartBasisVecFiber (I := I) x₀ k (Ψ w))
              (chartBasisVecFiber (I := I) x₀ l (Ψ w)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]
    rw [smul_eq_mul]
  rw [hR, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [chartGramMatrix_apply]
  ring

set_option linter.unusedSectionVars false in
/-- Matrix V0a Gram transformation law.

At a source point whose image lies in the canonical chart at `x₀`, the
parametrized Gram matrix is `Jᵀ * G_x₀ * J`, where `J` is the Fréchet Jacobian
of `extChartAt x₀ ∘ Ψ` in the fixed model basis.  This is the integration-layer
bridge needed before the V0 density identity and V0b change of variables. -/
theorem paramGramMatrix_pullback_eq_mul
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source)
    (hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    paramGramMatrix (I := I) g Ψ w =
      (paramJacobianMatrix (I := I) x₀ Ψ w)ᵀ *
        chartGramMatrix g x₀ (Ψ w) *
        paramJacobianMatrix (I := I) x₀ Ψ w := by
  ext i j
  rw [paramGramMatrix_pullback_eq_sum (I := I) g x₀ Ψ hw hx i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

set_option linter.unusedSectionVars false in
/-- The determinant of the parametrized Jacobian matrix equals the determinant
of the underlying Fréchet derivative.

This identifies the coefficient matrix used in the V0a Gram law with the
Jacobian determinant required by Mathlib's Euclidean change-of-variables
formula in V0b. -/
lemma paramJacobianMatrix_det
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) (w : E) :
    (paramJacobianMatrix (I := I) x₀ Ψ w).det =
      (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det := by
  unfold paramJacobianMatrix
  rw [LinearMap.det_toMatrix]

set_option linter.unusedSectionVars false in
/-- Determinant form of V0a.

On the chart overlap, `det(paramGram)` is the square of the Jacobian determinant
of `extChartAt x₀ ∘ Ψ` times the canonical chart Gram determinant.  This is the
algebraic input for the scalar density identity used by V1a and later polar
integration. -/
lemma paramGramMatrix_det_pullback
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source)
    (hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (paramGramMatrix (I := I) g Ψ w).det =
      ((fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det) ^ 2 *
        (chartGramMatrix g x₀ (Ψ w)).det := by
  rw [paramGramMatrix_pullback_eq_mul (I := I) g x₀ Ψ hw hx]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [paramJacobianMatrix_det (I := I) x₀ Ψ w]
  ring

set_option linter.unusedSectionVars false in
/-- Scalar V0a density transformation law.

Where the parametrization lands in the canonical chart at `x₀`, its density is
the absolute Jacobian of `extChartAt x₀ ∘ Ψ` times the canonical chart density.
This is the exact scalar identity needed by the V0b Jacobian change of
variables, and V1a consumes it at `Ψ := expMapDiffeo g x`. -/
theorem paramDensity_eq_abs_det_mul_chartDensity
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source)
    (hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    paramDensity (I := I) g Ψ w =
      |(fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det| *
        chartDensity g x₀ (Ψ w) := by
  unfold paramDensity chartDensity
  rw [paramGramMatrix_det_pullback (I := I) g x₀ Ψ hw hx]
  rw [Real.sqrt_mul (sq_nonneg _)]
  rw [Real.sqrt_sq_eq_abs]

set_option linter.unusedSectionVars false in
/-- The chart representative of a parametrization is `C¹` on any open set where
the parametrization stays in the chosen chart.

This is the regularity input for continuity of the Jacobian determinant and
hence of the parametrized density on chart-valid pieces. -/
lemma paramChartMap_contDiffOn
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContDiffOn ℝ 1 (paramChartMap (I := I) x₀ Ψ) s := by
  have hΨ : ContMDiffOn 𝓘(ℝ, E) I 1 Ψ s :=
    Ψ.contMDiffOn_toFun.mono hs_source
  have hchart : ContMDiffOn I 𝓘(ℝ, E) 1 (extChartAt I x₀) (chartAt H x₀).source :=
    contMDiffOn_extChartAt (I := I) (x := x₀) (n := 1)
  have hmaps : s ⊆ Ψ ⁻¹' (chartAt H x₀).source := by
    intro w hw
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
      hs_chart w hw
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (extChartAt I x₀ ∘ Ψ) s :=
    hchart.comp hΨ hmaps
  exact contMDiffOn_iff_contDiffOn.mp
    (by simpa [paramChartMap, Function.comp_def] using hcomp)

set_option linter.unusedSectionVars false in
/-- The parametrized Gram matrix is continuous on any open source subset whose
image lies in one canonical chart. -/
lemma paramGram_contOn
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_open : IsOpen s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s,
      Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContinuousOn (paramGramMatrix (I := I) g Ψ) s := by
  have hT : ContDiffOn ℝ 1 (paramChartMap (I := I) x₀ Ψ) s :=
    paramChartMap_contDiffOn (I := I) x₀ Ψ hs_source hs_chart
  have hfderiv : ContinuousOn
      (fun w => fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) s :=
    hT.continuousOn_fderiv_of_isOpen hs_open le_rfl
  have hJ : ∀ k i, ContinuousOn
      (fun w => paramJacobianMatrix (I := I) x₀ Ψ w k i) s := by
    intro k i
    have happ : Continuous
        (fun L : E →L[ℝ] E => L ((chartModelBasis E) i)) :=
      continuous_eval_const _
    have hcoord : Continuous
        (fun v : E => ((chartModelBasis E).coord k).toContinuousLinearMap v) :=
      ((chartModelBasis E).coord k).toContinuousLinearMap.continuous
    simpa only [paramJacobianMatrix_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply] using
      hcoord.comp_continuousOn (happ.comp_continuousOn hfderiv)
  have hΨcont : ContinuousOn Ψ s :=
    (Ψ.contMDiffOn_toFun.mono hs_source).continuousOn
  have hG : ∀ k l, ContinuousOn
      (fun w => chartGramMatrix g x₀ (Ψ w) k l) s := by
    intro k l
    exact (chartGramMatrix_entry_contMDiffOn (I := I) g x₀ k l).continuousOn.comp
      hΨcont hs_chart
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_matrix
  intro i j
  have hsum : ContinuousOn
      (fun w => ∑ k, ∑ l,
        paramJacobianMatrix (I := I) x₀ Ψ w k i *
        paramJacobianMatrix (I := I) x₀ Ψ w l j *
        chartGramMatrix g x₀ (Ψ w) k l) s := by
    refine continuousOn_finset_sum _ fun k _ => ?_
    refine continuousOn_finset_sum _ fun l _ => ?_
    exact ((hJ k i).mul (hJ l j)).mul (hG k l)
  simpa only [Set.restrict_apply] using
    (hsum.congr fun w hw =>
      paramGramMatrix_pullback_eq_sum (I := I) g x₀ Ψ
        (hs_source hw) (hs_chart w hw) i j).restrict

set_option linter.unusedSectionVars false in
/-- The parametrized density is continuous on any open source subset whose image
lies in one canonical chart.

This is the chart-local continuity statement needed for measurable POU
recombination.  The global source-continuity statement should be obtained by
localizing this lemma around each source point. -/
lemma paramDensity_continuousOn_chart
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_open : IsOpen s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContinuousOn (paramDensity (I := I) g Ψ) s := by
  have hT : ContDiffOn ℝ 1 (paramChartMap (I := I) x₀ Ψ) s :=
    paramChartMap_contDiffOn (I := I) x₀ Ψ hs_source hs_chart
  have hfderiv : ContinuousOn (fun w => fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) s :=
    hT.continuousOn_fderiv_of_isOpen hs_open le_rfl
  have hdet : ContinuousOn
      (fun w => |(fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det|) s :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn hfderiv).abs
  have hΨcont : ContinuousOn Ψ s :=
    (Ψ.contMDiffOn_toFun.mono hs_source).continuousOn
  have hchartDensity : ContinuousOn (fun w => chartDensity g x₀ (Ψ w)) s :=
    (chartDensity_continuousOn (I := I) g x₀).comp hΨcont hs_chart
  have hR : ContinuousOn
      (fun w => |(fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det| *
        chartDensity g x₀ (Ψ w)) s :=
    hdet.mul hchartDensity
  exact hR.congr (fun w hw =>
    paramDensity_eq_abs_det_mul_chartDensity (I := I) g x₀ Ψ
      (hs_source hw) (hs_chart w hw))

set_option linter.unusedSectionVars false in
/-- The parametrized density is continuous on the full source of a partial
diffeomorphism. -/
lemma paramDensity_contOn
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) :
    ContinuousOn (paramDensity (I := I) g Ψ) Ψ.source := by
  rw [continuousOn_iff_continuous_restrict, continuous_iff_continuousAt]
  intro w
  let x₀ : M := Ψ w
  let U : Set E := Ψ.source ∩ Ψ ⁻¹' (chartAt H x₀).source
  have hΨcont : ContinuousOn Ψ Ψ.source :=
    Ψ.contMDiffOn_toFun.continuousOn
  have hUopen : IsOpen U := by
    dsimp only [U]
    exact hΨcont.isOpen_inter_preimage Ψ.open_source (chartAt H x₀).open_source
  have hU_source : U ⊆ Ψ.source := by
    dsimp only [U]
    exact Set.inter_subset_left
  have hU_chart : ∀ z ∈ U,
      Ψ z ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    intro z hz
    dsimp only [U] at hz
    simpa only [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hz.2
  have hwU : (w : E) ∈ U := by
    refine ⟨w.2, ?_⟩
    simpa only [x₀] using mem_chart_source H (Ψ w)
  have hcontU : ContinuousOn (paramDensity (I := I) g Ψ) U :=
    paramDensity_continuousOn_chart (I := I) g x₀ Ψ
      hUopen hU_source hU_chart
  exact (hcontU.continuousAt (hUopen.mem_nhds hwU)).comp
    continuous_subtype_val.continuousAt

set_option linter.unusedSectionVars false in
/-- Measurability form of chart-local continuity of the parametrized density. -/
lemma aemeasurable_ofReal_paramDensity_on_chart
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s) (hs_open : IsOpen s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    AEMeasurable (fun w => ENNReal.ofReal (paramDensity (I := I) g Ψ w))
      ((modelHaar (E := E)).restrict s) := by
  have hcont : ContinuousOn (paramDensity (I := I) g Ψ) s :=
    paramDensity_continuousOn_chart (I := I) g x₀ Ψ hs_open hs_source hs_chart
  exact ENNReal.measurable_ofReal.comp_aemeasurable (hcont.aemeasurable hs_meas)

set_option linter.unusedSectionVars false in
/-- The chart representative of a parametrization has the expected Fréchet
derivative within any set.

This is the `HasFDerivWithinAt` input required by Mathlib's Euclidean
change-of-variables theorem in V0b.  It uses only `C¹` regularity of the
partial diffeomorphism on its source and smoothness of the canonical chart. -/
lemma paramChartMap_hasFDerivWithinAt
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} {w : E} (hw : w ∈ Ψ.source)
    (hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    HasFDerivWithinAt (paramChartMap (I := I) x₀ Ψ)
      (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) s w := by
  have hxchart : Ψ w ∈ (chartAt H x₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) x₀] using hx
  have hΨdiff : MDifferentiableAt 𝓘(ℝ, E) I Ψ w :=
    (Ψ.contMDiffOn_toFun.mdifferentiableOn one_ne_zero w hw).mdifferentiableAt
      (Ψ.open_source.mem_nhds hw)
  have hchartdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) (Ψ w) :=
    mdifferentiableAt_extChartAt (I := I) (x := x₀) (y := Ψ w) hxchart
  have hTdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (paramChartMap (I := I) x₀ Ψ) w := by
    simpa [paramChartMap, Function.comp_def] using hchartdiff.comp w hΨdiff
  exact hTdiff.differentiableAt.hasFDerivAt.hasFDerivWithinAt

set_option linter.unusedSectionVars false in
/-- The chart representative of a parametrization is injective on chart-valid
subsets of the source.

The proof uses injectivity of the canonical chart on its source and injectivity
of the partial diffeomorphism on its source.  This is the `InjOn` input for the
V0b Jacobian change of variables. -/
lemma paramChartMap_injOn
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    Set.InjOn (paramChartMap (I := I) x₀ Ψ) s := by
  intro u hu v hv huv
  have hu_chart : Ψ u ∈ (chartAt H x₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) x₀] using
      hs_chart u hu
  have hv_chart : Ψ v ∈ (chartAt H x₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) x₀] using
      hs_chart v hv
  have hu_ext : Ψ u ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hu_chart
  have hv_ext : Ψ v ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hv_chart
  have hΨuv : Ψ u = Ψ v :=
    (extChartAt I x₀).injOn hu_ext hv_ext huv
  exact Ψ.toPartialEquiv.injOn (hs_source hu) (hs_source hv) hΨuv

set_option linter.unusedSectionVars false in
/-- The image of a measurable source subset under the chart representative of
a parametrization is measurable.

This is the measurability companion to `paramChartMap_injOn`: Mathlib's
Jacobian API supplies it from differentiability within the source set and
injectivity.  V0b uses this image as the Euclidean integration domain. -/
lemma measurableSet_image_paramChartMap
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MeasurableSet ((paramChartMap (I := I) x₀ Ψ) '' s) := by
  have hf' : ∀ w ∈ s, HasFDerivWithinAt (paramChartMap (I := I) x₀ Ψ)
      (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) s w := by
    intro w hw
    exact paramChartMap_hasFDerivWithinAt (I := I) x₀ Ψ
      (hs_source hw) (hs_chart w hw)
  exact MeasureTheory.measurable_image_of_fderivWithin hs_meas hf'
    (paramChartMap_injOn (I := I) x₀ Ψ hs_source hs_chart)

set_option linter.unusedSectionVars false in
/-- The parametrized image is measurable when it lies in one canonical chart.

The proof first shows measurability of the Euclidean image
`(extChartAt x₀ ∘ Ψ) '' s`, then maps it back through the inverse chart.  The
`T2Space` assumption is exactly the codomain separation hypothesis needed by
the Lusin-Souslin image theorem for continuous injective maps. -/
lemma measurableSet_image_param
    [T2Space M]
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MeasurableSet (Ψ '' s) := by
  set V : Set E := (paramChartMap (I := I) x₀ Ψ) '' s with hV_def
  have hV_meas : MeasurableSet V := by
    rw [hV_def]
    exact measurableSet_image_paramChartMap (I := I) x₀ Ψ hs_meas hs_source hs_chart
  have hV_target : V ⊆ (extChartAt I x₀).target := by
    rw [hV_def]
    rintro y ⟨w, hw, rfl⟩
    have hxchart : Ψ w ∈ (chartAt H x₀).source := by
      simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
        hs_chart w hw
    have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hxchart
    exact (extChartAt I x₀).map_source hxsrc
  have hsymm_cont : ContinuousOn (extChartAt I x₀).symm V :=
    (continuousOn_extChartAt_symm (I := I) x₀).mono hV_target
  have hsymm_inj : Set.InjOn (extChartAt I x₀).symm V := by
    intro y hy z hz hyz
    rw [← (extChartAt I x₀).right_inv (hV_target hy), hyz,
      (extChartAt I x₀).right_inv (hV_target hz)]
  have hsymm_image :
      MeasurableSet ((extChartAt I x₀).symm '' V) :=
    hV_meas.image_of_continuousOn_injOn hsymm_cont hsymm_inj
  convert hsymm_image using 1
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨paramChartMap (I := I) x₀ Ψ w, ?_, ?_⟩
    · rw [hV_def]
      exact ⟨w, hw, rfl⟩
    · have hxchart : Ψ w ∈ (chartAt H x₀).source := by
        simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
          hs_chart w hw
      have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        exact hxchart
      simpa [paramChartMap] using (extChartAt I x₀).left_inv hxsrc
  · rintro ⟨y, hyV, rfl⟩
    rw [hV_def] at hyV
    rcases hyV with ⟨w, hw, rfl⟩
    refine ⟨w, hw, ?_⟩
    have hxchart : Ψ w ∈ (chartAt H x₀).source := by
      simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
        hs_chart w hw
    have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hxchart
    simpa [paramChartMap] using ((extChartAt I x₀).left_inv hxsrc).symm

set_option linter.unusedSectionVars false in
/-- The image of a measurable source subset under a parametrizing partial
diffeomorphism is measurable.

This is the global Borel-image input for the final V0 formula.  It uses the
same Lusin-Souslin image theorem as the chart-contained version, but applies it
directly to `Ψ` on the measurable subset of its open source. -/
lemma measurableSet_image_param_global
    [T2Space M]
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source) :
    MeasurableSet (Ψ '' s) := by
  have hcont : ContinuousOn Ψ s :=
    (Ψ.contMDiffOn_toFun.mono hs_source).continuousOn
  have hinj : Set.InjOn Ψ s := by
    intro u hu v hv huv
    exact Ψ.toPartialEquiv.injOn (hs_source hu) (hs_source hv) huv
  exact hs_meas.image_of_continuousOn_injOn hcont hinj

set_option linter.unusedSectionVars false in
/-- The inverse image of a measurable target subset under a parametrizing
partial diffeomorphism is measurable in the model space.

This is the measurability input for the set-form V0 corollary: it turns a
measurable target set `A ⊆ Ψ.target` into the source set `Ψ.symm '' A` to which
`riemannianVolumeMeasure_image_param_eq` applies. -/
lemma measurableSet_symm_image_param
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_target : A ⊆ Ψ.target) :
    MeasurableSet (Ψ.symm '' A) := by
  have hsrc_meas : MeasurableSet Ψ.source := Ψ.open_source.measurableSet
  have hcont : Continuous (fun w : Ψ.source => Ψ (w : E)) :=
    continuousOn_iff_continuous_restrict.mp Ψ.contMDiffOn_toFun.continuousOn
  have hpre_sub :
      MeasurableSet {w : Ψ.source | Ψ (w : E) ∈ A} :=
    hcont.measurable hA_meas
  have hpre :
      MeasurableSet (Ψ.source ∩ Ψ ⁻¹' A) := by
    convert hsrc_meas.subtype_image hpre_sub using 1
    ext w
    constructor
    · rintro ⟨hwsrc, hwA⟩
      exact ⟨⟨w, hwsrc⟩, hwA, rfl⟩
    · rintro ⟨w', hwA, hw_eq⟩
      rw [← hw_eq]
      exact ⟨w'.2, hwA⟩
  convert hpre using 1
  ext w
  constructor
  · rintro ⟨x, hxA, rfl⟩
    exact ⟨Ψ.toPartialEquiv.map_target (hA_target hxA), by
      change Ψ.toPartialEquiv (Ψ.toPartialEquiv.symm x) ∈ A
      rw [Ψ.toPartialEquiv.right_inv (hA_target hxA)]
      exact hxA⟩
  · rintro ⟨hwsrc, hwA⟩
    exact ⟨Ψ w, hwA, by
      change Ψ.toPartialEquiv.symm (Ψ.toPartialEquiv w) = w
      exact Ψ.toPartialEquiv.left_inv hwsrc⟩

set_option linter.unusedSectionVars false in
/-- The source piece whose parametrized image lies in the chart at `x₀` is
measurable.

This is the standard chart-piece domain used in the POU recombination:
`s ∩ Ψ ⁻¹' (chartAt H x₀).source`. -/
lemma measurableSet_param_chartPiece
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source) :
    MeasurableSet (s ∩ Ψ ⁻¹' (chartAt H x₀).source) := by
  have hΨcont : ContinuousOn Ψ Ψ.source :=
    Ψ.contMDiffOn_toFun.continuousOn
  have hopen : IsOpen (Ψ.source ∩ Ψ ⁻¹' (chartAt H x₀).source) :=
    hΨcont.isOpen_inter_preimage Ψ.open_source (chartAt H x₀).open_source
  have heq :
      s ∩ Ψ ⁻¹' (chartAt H x₀).source =
        s ∩ (Ψ.source ∩ Ψ ⁻¹' (chartAt H x₀).source) := by
    ext w
    constructor
    · rintro ⟨hw, hchart⟩
      exact ⟨hw, hs_source hw, hchart⟩
    · rintro ⟨hw, _, hchart⟩
      exact ⟨hw, hchart⟩
  rw [heq]
  exact hs_meas.inter hopen.measurableSet

set_option linter.unusedSectionVars false in
/-- The parametrized density is a.e.-measurable on an arbitrary measurable
chart piece `s ∩ Ψ ⁻¹' (chartAt H x₀).source`.

The proof obtains continuity on the open chart-valid set
`Ψ.source ∩ Ψ ⁻¹' (chartAt H x₀).source`, then restricts it to the measurable
piece.  This is the density-side measurability input for the POU
recombination route. -/
lemma aemeasurable_ofReal_paramDensity_on_chartPiece
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source) :
    AEMeasurable (fun w => ENNReal.ofReal (paramDensity (I := I) g Ψ w))
      ((modelHaar (E := E)).restrict (s ∩ Ψ ⁻¹' (chartAt H x₀).source)) := by
  set U : Set E := Ψ.source ∩ Ψ ⁻¹' (chartAt H x₀).source with hU_def
  have hΨcont : ContinuousOn Ψ Ψ.source :=
    Ψ.contMDiffOn_toFun.continuousOn
  have hUopen : IsOpen U := by
    rw [hU_def]
    exact hΨcont.isOpen_inter_preimage Ψ.open_source (chartAt H x₀).open_source
  have hU_source : U ⊆ Ψ.source := by
    rw [hU_def]
    exact Set.inter_subset_left
  have hU_chart :
      ∀ w ∈ U, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    intro w hw
    rw [hU_def] at hw
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hw.2
  have hcontU : ContinuousOn (paramDensity (I := I) g Ψ) U :=
    paramDensity_continuousOn_chart (I := I) g x₀ Ψ hUopen hU_source hU_chart
  have hpiece_meas : MeasurableSet (s ∩ Ψ ⁻¹' (chartAt H x₀).source) :=
    measurableSet_param_chartPiece (I := I) x₀ Ψ hs_meas hs_source
  have hpiece_sub : s ∩ Ψ ⁻¹' (chartAt H x₀).source ⊆ U := by
    intro w hw
    rw [hU_def]
    exact ⟨hs_source hw.1, hw.2⟩
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    ((hcontU.mono hpiece_sub).aemeasurable hpiece_meas)

set_option linter.unusedSectionVars false in
/-- A partition-of-unity weight pulled back by the parametrization is
a.e.-measurable on a chart piece. -/
lemma aemeasurable_ofReal_pou_param_on_chartPiece
    (ρ : SmoothPartitionOfUnity M I M univ) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source) :
    AEMeasurable (fun w => ENNReal.ofReal (ρ x₀ (Ψ w)))
      ((modelHaar (E := E)).restrict (s ∩ Ψ ⁻¹' (chartAt H x₀).source)) := by
  set S : Set E := s ∩ Ψ ⁻¹' (chartAt H x₀).source with hS_def
  have hS_meas : MeasurableSet S := by
    rw [hS_def]
    exact measurableSet_param_chartPiece (I := I) x₀ Ψ hs_meas hs_source
  have hΨcont_source : ContinuousOn Ψ Ψ.source :=
    Ψ.contMDiffOn_toFun.continuousOn
  have hS_sub_source : S ⊆ Ψ.source := by
    rw [hS_def]
    exact fun w hw => hs_source hw.1
  have hΨ_aem : AEMeasurable Ψ ((modelHaar (E := E)).restrict S) :=
    (hΨcont_source.mono hS_sub_source).aemeasurable hS_meas
  exact (measurable_ofReal_pou_weight (I := I) ρ x₀).comp_aemeasurable hΨ_aem

set_option linter.unusedSectionVars false in
/-- The parameter-side product of the parametrized density with a pulled-back
POU weight is a.e.-measurable on a chart piece. -/
lemma aemeasurable_paramDensity_mul_pou_on_chartPiece
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source) :
    AEMeasurable
      (fun w =>
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
          ENNReal.ofReal (ρ x₀ (Ψ w)))
      ((modelHaar (E := E)).restrict (s ∩ Ψ ⁻¹' (chartAt H x₀).source)) := by
  exact (aemeasurable_ofReal_paramDensity_on_chartPiece (I := I) g x₀ Ψ
    hs_meas hs_source).mul
    (aemeasurable_ofReal_pou_param_on_chartPiece (I := I) ρ x₀ Ψ
      hs_meas hs_source)

set_option linter.unusedSectionVars false in
/-- The chart-piece weighted parameter integrand, extended by zero off the
chart-valid piece, is a.e.-measurable for the model Haar measure. -/
lemma aemeasurable_paramDensity_mul_pou_indicator_chartPiece
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source) :
    AEMeasurable
      ((s ∩ Ψ ⁻¹' (chartAt H x₀).source).indicator
        (fun w =>
          ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
            ENNReal.ofReal (ρ x₀ (Ψ w))))
      (modelHaar (E := E)) := by
  have hS_meas : MeasurableSet (s ∩ Ψ ⁻¹' (chartAt H x₀).source) :=
    measurableSet_param_chartPiece (I := I) x₀ Ψ hs_meas hs_source
  exact (aemeasurable_indicator_iff hS_meas).mpr
    (aemeasurable_paramDensity_mul_pou_on_chartPiece (I := I) g ρ x₀ Ψ
      hs_meas hs_source)

set_option linter.unusedSectionVars false in
/-- A POU weight subordinate to the chart atlas vanishes outside its chart
source. -/
lemma pou_weight_eq_zero_of_notMem_chart
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    {α x : M} (hx : x ∉ (chartAt H α).source) :
    ρ α x = 0 := by
  by_contra hne
  exact hx (hρ α (subset_tsupport _ hne))

set_option linter.unusedSectionVars false in
/-- V0b, chart-image form: Euclidean change of variables for a parametrization
written in a canonical chart.

For a measurable subset of the parametrization source whose image lies in the
canonical chart at `x₀`, integrating the canonical chart density over
`(extChartAt x₀ ∘ Ψ) '' s` is the same as integrating the parametrized density
over `s`.  This is the local Jacobian-change-of-variables step consumed by the
V0 recombination proof and, after specialization, by V1a normal coordinates. -/
theorem lintegral_image_paramChartMap_chartDensity_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∫⁻ y in (paramChartMap (I := I) x₀ Ψ) '' s,
        ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y))
        ∂(modelHaar (E := E)) =
      ∫⁻ w in s, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
  have hf' : ∀ w ∈ s, HasFDerivWithinAt (paramChartMap (I := I) x₀ Ψ)
      (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) s w := by
    intro w hw
    exact paramChartMap_hasFDerivWithinAt (I := I) x₀ Ψ
      (hs_source hw) (hs_chart w hw)
  have hinj : Set.InjOn (paramChartMap (I := I) x₀ Ψ) s :=
    paramChartMap_injOn (I := I) x₀ Ψ hs_source hs_chart
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := modelHaar (E := E)) hs_meas hf' hinj
    (g := fun y : E =>
      ENNReal.ofReal
        (chartDensity g x₀ ((extChartAt I x₀).symm y)))]
  refine MeasureTheory.setLIntegral_congr_fun hs_meas ?_
  intro w hw
  have hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    hs_chart w hw
  have hxchart : Ψ w ∈ (chartAt H x₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) x₀] using hx
  have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hxchart
  have hsymm :
      (extChartAt I x₀).symm (paramChartMap (I := I) x₀ Ψ w) = Ψ w := by
    simpa [paramChartMap] using (extChartAt I x₀).left_inv hxsrc
  change ENNReal.ofReal |(fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det| *
      ENNReal.ofReal
        (chartDensity g x₀ ((extChartAt I x₀).symm
          (paramChartMap (I := I) x₀ Ψ w))) =
    ENNReal.ofReal (paramDensity (I := I) g Ψ w)
  rw [hsymm]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  rw [← paramDensity_eq_abs_det_mul_chartDensity (I := I) g x₀ Ψ (hs_source hw) hx]

set_option linter.unusedSectionVars false in
/-- Weighted V0b, chart-image form.

This is the change-of-variables formula needed for the POU recombination step:
an arbitrary nonnegative weight pulled back through the inverse chart becomes
the same weight evaluated on the parametrized point. -/
theorem lintegral_image_paramChartMap_mul_chartDensity_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (F : M → ℝ≥0∞) :
    ∫⁻ y in (paramChartMap (I := I) x₀ Ψ) '' s,
        ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          F ((extChartAt I x₀).symm y)
        ∂(modelHaar (E := E)) =
      ∫⁻ w in s,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) * F (Ψ w)
        ∂(modelHaar (E := E)) := by
  have hf' : ∀ w ∈ s, HasFDerivWithinAt (paramChartMap (I := I) x₀ Ψ)
      (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) s w := by
    intro w hw
    exact paramChartMap_hasFDerivWithinAt (I := I) x₀ Ψ
      (hs_source hw) (hs_chart w hw)
  have hinj : Set.InjOn (paramChartMap (I := I) x₀ Ψ) s :=
    paramChartMap_injOn (I := I) x₀ Ψ hs_source hs_chart
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := modelHaar (E := E)) hs_meas hf' hinj
    (g := fun y : E =>
      ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
        F ((extChartAt I x₀).symm y))]
  refine MeasureTheory.setLIntegral_congr_fun hs_meas ?_
  intro w hw
  have hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    hs_chart w hw
  have hxchart : Ψ w ∈ (chartAt H x₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hx
  have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hxchart
  have hsymm :
      (extChartAt I x₀).symm (paramChartMap (I := I) x₀ Ψ w) = Ψ w := by
    simpa [paramChartMap] using (extChartAt I x₀).left_inv hxsrc
  change ENNReal.ofReal |(fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det| *
      (ENNReal.ofReal
        (chartDensity g x₀ ((extChartAt I x₀).symm
          (paramChartMap (I := I) x₀ Ψ w))) *
        F ((extChartAt I x₀).symm (paramChartMap (I := I) x₀ Ψ w))) =
    ENNReal.ofReal (paramDensity (I := I) g Ψ w) * F (Ψ w)
  rw [hsymm]
  rw [← mul_assoc]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  rw [← paramDensity_eq_abs_det_mul_chartDensity (I := I) g x₀ Ψ (hs_source hw) hx]

set_option linter.unusedSectionVars false in
/-- V0c, chart-local form with an explicit measurability hypothesis on the
parametrized image.

For a measurable source subset whose parametrized image lies in one canonical
chart, the chart-local Riemannian measure of that image is the model-space
integral of the parametrized density.  The extra hypothesis
`MeasurableSet (Ψ '' s)` is intentionally explicit: removing it for arbitrary
measurable `s` is the remaining Borel-image API needed before the global V0d
recombination theorem can be stated without side assumptions. -/
theorem chartLocalMeasure_image_param_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (himage_meas : MeasurableSet (Ψ '' s)) :
    chartLocalMeasure (I := I) g x₀ (Ψ '' s) =
      ∫⁻ w in s, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
  rw [← MeasureTheory.setLIntegral_one
    (μ := chartLocalMeasure (I := I) g x₀) (s := Ψ '' s)]
  rw [chartLocalMeasure_setLintegral_indicator (I := I) g x₀ himage_meas
    (measurable_const : Measurable (fun _ : M => (1 : ℝ≥0∞)))]
  set V : Set E := (paramChartMap (I := I) x₀ Ψ) '' s with hV_def
  have hV_meas : MeasurableSet V := by
    rw [hV_def]
    exact measurableSet_image_paramChartMap (I := I) x₀ Ψ hs_meas hs_source hs_chart
  have hV_target : V ⊆ (extChartAt I x₀).target := by
    rw [hV_def]
    rintro y ⟨w, hw, rfl⟩
    have hxchart : Ψ w ∈ (chartAt H x₀).source := by
      simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
        hs_chart w hw
    have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hxchart
    exact (extChartAt I x₀).map_source hxsrc
  have hmem : ∀ y ∈ (extChartAt I x₀).target,
      (extChartAt I x₀).symm y ∈ Ψ '' s ↔ y ∈ V := by
    intro y hy
    constructor
    · rintro ⟨w, hw, hw_eq⟩
      refine ⟨w, hw, ?_⟩
      rw [paramChartMap, hw_eq, (extChartAt I x₀).right_inv hy]
    · rw [hV_def]
      rintro ⟨w, hw, rfl⟩
      refine ⟨w, hw, ?_⟩
      have hxchart : Ψ w ∈ (chartAt H x₀).source := by
        simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
          hs_chart w hw
      have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        exact hxchart
      simpa [paramChartMap] using ((extChartAt I x₀).left_inv hxsrc).symm
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  have hpt : ∀ y ∈ (extChartAt I x₀).target,
      ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          (Ψ '' s).indicator (fun _ : M => (1 : ℝ≥0∞))
            ((extChartAt I x₀).symm y) =
        V.indicator
          (fun y : E =>
            ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))) y := by
    intro y hy
    by_cases hyV : y ∈ V
    · have hyU : (extChartAt I x₀).symm y ∈ Ψ '' s := (hmem y hy).2 hyV
      rw [Set.indicator_of_mem hyU, Set.indicator_of_mem hyV, mul_one]
    · have hyU : (extChartAt I x₀).symm y ∉ Ψ '' s := by
        intro hU
        exact hyV ((hmem y hy).1 hU)
      rw [Set.indicator_of_notMem hyU, Set.indicator_of_notMem hyV, mul_zero]
  rw [MeasureTheory.setLIntegral_congr_fun htarget_meas hpt]
  rw [MeasureTheory.setLIntegral_indicator hV_meas]
  rw [show V ∩ (extChartAt I x₀).target = V from by
    ext y
    constructor
    · exact fun hy => hy.1
    · intro hy
      exact ⟨hy, hV_target hy⟩]
  rw [hV_def]
  exact lintegral_image_paramChartMap_chartDensity_eq (I := I) g x₀ Ψ
    hs_meas hs_source hs_chart

set_option linter.unusedSectionVars false in
/-- V0c, chart-local form: if the parametrized set lies in one canonical chart,
then its chart-local Riemannian measure is the model-space integral of the
parametrized density. -/
theorem chartLocalMeasure_image_param_eq_t2
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    chartLocalMeasure (I := I) g x₀ (Ψ '' s) =
      ∫⁻ w in s, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) :=
  chartLocalMeasure_image_param_eq (I := I) g x₀ Ψ hs_meas hs_source hs_chart
    (measurableSet_image_param (I := I) x₀ Ψ hs_meas hs_source hs_chart)

set_option linter.unusedSectionVars false in
/-- Weighted V0c, chart-local form.

This is the local formula needed by the global POU recombination: a measurable
nonnegative weight on the manifold pulls back along the parametrization. -/
theorem chartLocalMeasure_lintegral_image_param_eq_t2
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in Ψ '' s, F x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ w in s,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) * F (Ψ w)
        ∂(modelHaar (E := E)) := by
  have himage_meas : MeasurableSet (Ψ '' s) :=
    measurableSet_image_param (I := I) x₀ Ψ hs_meas hs_source hs_chart
  rw [chartLocalMeasure_setLintegral_indicator (I := I) g x₀ himage_meas hF]
  set V : Set E := (paramChartMap (I := I) x₀ Ψ) '' s with hV_def
  have hV_meas : MeasurableSet V := by
    rw [hV_def]
    exact measurableSet_image_paramChartMap (I := I) x₀ Ψ hs_meas hs_source hs_chart
  have hV_target : V ⊆ (extChartAt I x₀).target := by
    rw [hV_def]
    rintro y ⟨w, hw, rfl⟩
    have hxchart : Ψ w ∈ (chartAt H x₀).source := by
      simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
        hs_chart w hw
    have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hxchart
    exact (extChartAt I x₀).map_source hxsrc
  have hmem : ∀ y ∈ (extChartAt I x₀).target,
      (extChartAt I x₀).symm y ∈ Ψ '' s ↔ y ∈ V := by
    intro y hy
    constructor
    · rintro ⟨w, hw, hw_eq⟩
      refine ⟨w, hw, ?_⟩
      rw [paramChartMap, hw_eq, (extChartAt I x₀).right_inv hy]
    · rw [hV_def]
      rintro ⟨w, hw, rfl⟩
      refine ⟨w, hw, ?_⟩
      have hxchart : Ψ w ∈ (chartAt H x₀).source := by
        simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
          hs_chart w hw
      have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        exact hxchart
      simpa [paramChartMap] using ((extChartAt I x₀).left_inv hxsrc).symm
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  have hpt : ∀ y ∈ (extChartAt I x₀).target,
      ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          (Ψ '' s).indicator F ((extChartAt I x₀).symm y) =
        V.indicator
          (fun y : E =>
            ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
              F ((extChartAt I x₀).symm y)) y := by
    intro y hy
    by_cases hyV : y ∈ V
    · have hyU : (extChartAt I x₀).symm y ∈ Ψ '' s := (hmem y hy).2 hyV
      rw [Set.indicator_of_mem hyU, Set.indicator_of_mem hyV]
    · have hyU : (extChartAt I x₀).symm y ∉ Ψ '' s := by
        intro hU
        exact hyV ((hmem y hy).1 hU)
      rw [Set.indicator_of_notMem hyU, Set.indicator_of_notMem hyV, mul_zero]
  rw [MeasureTheory.setLIntegral_congr_fun htarget_meas hpt]
  rw [MeasureTheory.setLIntegral_indicator hV_meas]
  rw [show V ∩ (extChartAt I x₀).target = V from by
    ext y
    constructor
    · exact fun hy => hy.1
    · intro hy
      exact ⟨hy, hV_target hy⟩]
  rw [hV_def]
  exact lintegral_image_paramChartMap_mul_chartDensity_eq (I := I) g x₀ Ψ
    hs_meas hs_source hs_chart F

set_option linter.unusedSectionVars false in
/-- A single POU summand of the global Riemannian measure decomposition,
restricted to a parametrized image, is the corresponding weighted parameter
integral over the chart-valid source piece.

This is the main local recombination step for V0d.  The remaining global step
is to sum this identity over `α` and collapse the POU weights on the
parameter side. -/
theorem riemannianMeasure_param_summand_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} (hB_meas : MeasurableSet B)
    (hB_source : B ⊆ Ψ.source) :
    ∫⁻ x, ENNReal.ofReal (ρ α x) *
        (Ψ '' B).indicator (fun _ : M => (1 : ℝ≥0∞)) x
        ∂(chartLocalMeasure (I := I) g α) =
      ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α).source,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
          ENNReal.ofReal (ρ α (Ψ w)) ∂(modelHaar (E := E)) := by
  set S : Set E := B ∩ Ψ ⁻¹' (chartAt H α).source with hS_def
  have hS_meas : MeasurableSet S := by
    rw [hS_def]
    exact measurableSet_param_chartPiece (I := I) α Ψ hB_meas hB_source
  have hS_source : S ⊆ Ψ.source := by
    rw [hS_def]
    exact fun w hw => hB_source hw.1
  have hS_chart :
      ∀ w ∈ S, Ψ w ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro w hw
    rw [hS_def] at hw
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hw.2
  have hS_image_meas : MeasurableSet (Ψ '' S) :=
    measurableSet_image_param (I := I) α Ψ hS_meas hS_source hS_chart
  have hF_meas : Measurable (fun x : M => ENNReal.ofReal (ρ α x)) :=
    measurable_ofReal_pou_weight (I := I) ρ α
  have hpoint : ∀ x : M,
      ENNReal.ofReal (ρ α x) *
          (Ψ '' B).indicator (fun _ : M => (1 : ℝ≥0∞)) x =
        (Ψ '' S).indicator (fun x : M => ENNReal.ofReal (ρ α x)) x := by
    intro x
    by_cases hxS : x ∈ Ψ '' S
    · have hxB : x ∈ Ψ '' B := by
        rcases hxS with ⟨w, hwS, rfl⟩
        rw [hS_def] at hwS
        exact ⟨w, hwS.1, rfl⟩
      rw [Set.indicator_of_mem hxB, Set.indicator_of_mem hxS, mul_one]
    · by_cases hxB : x ∈ Ψ '' B
      · have hx_not_chart : x ∉ (chartAt H α).source := by
          intro hxchart
          rcases hxB with ⟨w, hwB, rfl⟩
          exact hxS ⟨w, by
            rw [hS_def]
            exact ⟨hwB, hxchart⟩, rfl⟩
        have hρx : ρ α x = 0 :=
          pou_weight_eq_zero_of_notMem_chart (I := I) ρ hρ hx_not_chart
        rw [Set.indicator_of_mem hxB, Set.indicator_of_notMem hxS, hρx,
          ENNReal.ofReal_zero, zero_mul]
      · rw [Set.indicator_of_notMem hxB, Set.indicator_of_notMem hxS, mul_zero]
  calc
    ∫⁻ x, ENNReal.ofReal (ρ α x) *
        (Ψ '' B).indicator (fun _ : M => (1 : ℝ≥0∞)) x
        ∂(chartLocalMeasure (I := I) g α)
        = ∫⁻ x, (Ψ '' S).indicator
            (fun x : M => ENNReal.ofReal (ρ α x)) x
            ∂(chartLocalMeasure (I := I) g α) := by
          exact MeasureTheory.lintegral_congr hpoint
    _ = ∫⁻ x in Ψ '' S, ENNReal.ofReal (ρ α x)
        ∂(chartLocalMeasure (I := I) g α) := by
          rw [MeasureTheory.lintegral_indicator hS_image_meas]
    _ = ∫⁻ w in S,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
          ENNReal.ofReal (ρ α (Ψ w)) ∂(modelHaar (E := E)) := by
          exact chartLocalMeasure_lintegral_image_param_eq_t2
            (I := I) g α Ψ hS_meas hS_source hS_chart hF_meas
    _ = ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α).source,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
          ENNReal.ofReal (ρ α (Ψ w)) ∂(modelHaar (E := E)) := by
          rw [hS_def]

set_option linter.unusedSectionVars false in
/-- If a POU summand is identically zero, then its parameter-side chart-piece
integral is zero. -/
lemma param_pou_piece_zero
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M)
    (hα : Function.support (ρ α) = ∅)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} :
    ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α).source,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
          ENNReal.ofReal (ρ α (Ψ w)) ∂(modelHaar (E := E)) = 0 := by
  have hzero : ∀ w : E, ρ α (Ψ w) = 0 := by
    intro w
    by_contra hne
    have hx : Ψ w ∈ Function.support (ρ α) := hne
    rw [hα] at hx
    exact (Set.notMem_empty _) hx
  simp [hzero]

set_option linter.unusedSectionVars false in
/-- Restrict the parameter-side POU chart-piece sum to the countable support of
the partition of unity. -/
lemma tsum_param_pou_piece_eq_subtype
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} :
    (∑' α : M, ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α).source,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
          ENNReal.ofReal (ρ α (Ψ w)) ∂(modelHaar (E := E))) =
      ∑' α : {α : M | (Function.support (ρ α)).Nonempty},
        ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α.val).source,
          ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
            ENNReal.ofReal (ρ α.val (Ψ w)) ∂(modelHaar (E := E)) := by
  classical
  refine tsum_subtype_eq_of_support_subset
    (s := {α : M | (Function.support (ρ α)).Nonempty}) ?_
  intro α hα
  simp only [Set.mem_setOf_eq]
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  exact hα (param_pou_piece_zero (I := I) g ρ α hne Ψ)

set_option linter.unusedSectionVars false in
/-- Pointwise collapse of the parameter-side POU chart-piece sum. -/
lemma tsum_param_pou_piece_indicator_eq
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} (w : E) :
    (∑' α : {α : M | (Function.support (ρ α)).Nonempty},
        (B ∩ Ψ ⁻¹' (chartAt H α.val).source).indicator
          (fun w =>
            ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
              ENNReal.ofReal (ρ α.val (Ψ w))) w) =
      B.indicator
        (fun w => ENNReal.ofReal (paramDensity (I := I) g Ψ w)) w := by
  classical
  by_cases hwB : w ∈ B
  · rw [Set.indicator_of_mem hwB]
    have hterm :
        (fun α : {α : M | (Function.support (ρ α)).Nonempty} =>
          (B ∩ Ψ ⁻¹' (chartAt H α.val).source).indicator
            (fun w =>
              ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
                ENNReal.ofReal (ρ α.val (Ψ w))) w)
          =
        fun α : {α : M | (Function.support (ρ α)).Nonempty} =>
          ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
            ENNReal.ofReal (ρ α.val (Ψ w)) := by
      funext α
      by_cases hxchart : Ψ w ∈ (chartAt H α.val).source
      · have hmem : w ∈ B ∩ Ψ ⁻¹' (chartAt H α.val).source := ⟨hwB, hxchart⟩
        rw [Set.indicator_of_mem hmem]
      · have hmem : w ∉ B ∩ Ψ ⁻¹' (chartAt H α.val).source := by
          intro hw
          exact hxchart hw.2
        have hρw : ρ α.val (Ψ w) = 0 :=
          pou_weight_eq_zero_of_notMem_chart (I := I) ρ hρ hxchart
        rw [Set.indicator_of_notMem hmem, hρw, ENNReal.ofReal_zero, mul_zero]
    rw [hterm, ENNReal.tsum_mul_left]
    have hfull :
        (∑' α : {α : M | (Function.support (ρ α)).Nonempty},
            ENNReal.ofReal (ρ α.val (Ψ w))) =
          ∑' α : M, ENNReal.ofReal (ρ α (Ψ w)) := by
      symm
      refine tsum_subtype_eq_of_support_subset
        (s := {α : M | (Function.support (ρ α)).Nonempty})
        (f := fun α => ENNReal.ofReal (ρ α (Ψ w))) ?_
      intro α hα
      simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hα
      refine Set.nonempty_iff_ne_empty.mpr ?_
      intro h_empty
      have : ρ α (Ψ w) = 0 := by
        by_contra hne
        have hx : Ψ w ∈ Function.support (ρ α) := hne
        rw [h_empty] at hx
        exact (Set.notMem_empty _) hx
      linarith
    rw [hfull, tsum_ofReal_pou_eq_one (I := I) ρ (Ψ w), mul_one]
  · rw [Set.indicator_of_notMem hwB]
    refine (ENNReal.tsum_eq_zero).mpr ?_
    intro α
    have hmem : w ∉ B ∩ Ψ ⁻¹' (chartAt H α.val).source := by
      intro hw
      exact hwB hw.1
    rw [Set.indicator_of_notMem hmem]

set_option linter.unusedSectionVars false in
/-- Global V0d recombination for an arbitrary chart-subordinate POU: the glued
Riemannian measure of a parametrized measurable source image is the parameter
integral of the parametrized density. -/
theorem riemannianMeasure_image_param_eq
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} (hB_meas : MeasurableSet B)
    (hB_source : B ⊆ Ψ.source) :
    riemannianMeasure (I := I) g ρ (Ψ '' B) =
      ∫⁻ w in B, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
  classical
  have hB_image_meas : MeasurableSet (Ψ '' B) :=
    measurableSet_image_param_global (I := I) Ψ hB_meas hB_source
  have hInd_meas :
      Measurable ((Ψ '' B).indicator (fun _ : M => (1 : ℝ≥0∞))) :=
    (measurable_const).indicator hB_image_meas
  calc
    riemannianMeasure (I := I) g ρ (Ψ '' B)
        = ∫⁻ x, (Ψ '' B).indicator (fun _ : M => (1 : ℝ≥0∞)) x
            ∂(riemannianMeasure (I := I) g ρ) := by
          simpa using
            (MeasureTheory.lintegral_indicator_one
              (μ := riemannianMeasure (I := I) g ρ) hB_image_meas).symm
    _ = ∑' α : M, ∫⁻ x,
          ENNReal.ofReal (ρ α x) *
            (Ψ '' B).indicator (fun _ : M => (1 : ℝ≥0∞)) x
          ∂(chartLocalMeasure (I := I) g α) := by
          rw [riemannianMeasure_lintegral_eq (I := I) g ρ hInd_meas]
    _ = ∑' α : M, ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α).source,
          ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
            ENNReal.ofReal (ρ α (Ψ w)) ∂(modelHaar (E := E)) := by
          refine tsum_congr (fun α => ?_)
          exact riemannianMeasure_param_summand_eq (I := I) g ρ hρ α Ψ
            hB_meas hB_source
    _ = ∑' α : {α : M | (Function.support (ρ α)).Nonempty},
        ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α.val).source,
          ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
            ENNReal.ofReal (ρ α.val (Ψ w)) ∂(modelHaar (E := E)) := by
          exact tsum_param_pou_piece_eq_subtype (I := I) g ρ Ψ
    _ = ∑' α : {α : M | (Function.support (ρ α)).Nonempty},
        ∫⁻ w, (B ∩ Ψ ⁻¹' (chartAt H α.val).source).indicator
          (fun w =>
            ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
              ENNReal.ofReal (ρ α.val (Ψ w))) w
          ∂(modelHaar (E := E)) := by
          refine tsum_congr (fun α => ?_)
          have hS_meas :
              MeasurableSet (B ∩ Ψ ⁻¹' (chartAt H α.val).source) :=
            measurableSet_param_chartPiece (I := I) α.val Ψ hB_meas hB_source
          symm
          rw [MeasureTheory.lintegral_indicator hS_meas]
    _ = ∫⁻ w,
        ∑' α : {α : M | (Function.support (ρ α)).Nonempty},
          (B ∩ Ψ ⁻¹' (chartAt H α.val).source).indicator
            (fun w =>
              ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
                ENNReal.ofReal (ρ α.val (Ψ w))) w
        ∂(modelHaar (E := E)) := by
          haveI hCρ : Countable {α : M | (Function.support (ρ α)).Nonempty} :=
            (countable_nonempty_support_of_pou (I := I) ρ).to_subtype
          symm
          exact MeasureTheory.lintegral_tsum (μ := modelHaar (E := E)) (fun α =>
            aemeasurable_paramDensity_mul_pou_indicator_chartPiece
              (I := I) g ρ α.val Ψ hB_meas hB_source)
    _ = ∫⁻ w, B.indicator
        (fun w => ENNReal.ofReal (paramDensity (I := I) g Ψ w)) w
        ∂(modelHaar (E := E)) := by
          exact MeasureTheory.lintegral_congr
            (fun w => tsum_param_pou_piece_indicator_eq (I := I) g ρ hρ Ψ w)
    _ = ∫⁻ w in B, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
          rw [MeasureTheory.lintegral_indicator hB_meas]

set_option linter.unusedSectionVars false in
/-- Global V0 evaluation formula for the canonical Riemannian volume measure. -/
theorem riemannianVolumeMeasure_image_param_eq
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} (hB_meas : MeasurableSet B)
    (hB_source : B ⊆ Ψ.source) :
    riemannianVolumeMeasure (I := I) (M := M) g (Ψ '' B) =
      ∫⁻ w in B, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
  rw [← riemannianMeasure_eq_riemannianVolumeMeasure (I := I) g
    (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M)]
  exact riemannianMeasure_image_param_eq (I := I) g (chartAtlasPOU I M)
    (chartAtlasPOU_isSubordinate I M) Ψ hB_meas hB_source

set_option linter.unusedSectionVars false in
/-- A pointwise lower bound for a parametrized Riemannian density gives the
corresponding lower bound for the volume of the parametrized image. -/
theorem param_vol_ge
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} (hB_meas : MeasurableSet B)
    (hB_source : B ⊆ Ψ.source)
    {c : ℝ}
    (hdens : ∀ w ∈ B, c ≤ paramDensity (I := I) g Ψ w) :
    ENNReal.ofReal c * (modelHaar (E := E)) B ≤
      riemannianVolumeMeasure (I := I) (M := M) g (Ψ '' B) := by
  rw [riemannianVolumeMeasure_image_param_eq
    (I := I) g Ψ hB_meas hB_source]
  calc
    ENNReal.ofReal c * (modelHaar (E := E)) B =
        ∫⁻ _ in B, ENNReal.ofReal c ∂(modelHaar (E := E)) := by
      rw [MeasureTheory.setLIntegral_const]
    _ ≤ ∫⁻ w in B, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
      refine MeasureTheory.setLIntegral_mono' hB_meas ?_
      intro w hw
      exact ENNReal.ofReal_le_ofReal (hdens w hw)

set_option linter.unusedSectionVars false in
/-- Set-form V0 evaluation formula on a measurable target subset.

If `A` lies in the target of a `C¹` parametrizing partial diffeomorphism, then
the Riemannian volume of `A` is computed by integrating the parametrized density
over the inverse source image `Ψ.symm '' A`.  This is the convenience form
consumed by normal-coordinate V1a and later polar/entropy applications when the
geometric set is already expressed in the manifold. -/
theorem riemannianVolumeMeasure_param_target_eq
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_target : A ⊆ Ψ.target) :
    riemannianVolumeMeasure (I := I) (M := M) g A =
      ∫⁻ w in Ψ.symm '' A, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
  set B : Set E := Ψ.symm '' A with hB_def
  have hB_meas : MeasurableSet B := by
    rw [hB_def]
    exact measurableSet_symm_image_param (I := I) Ψ hA_meas hA_target
  have hB_source : B ⊆ Ψ.source := by
    rw [hB_def]
    rintro w ⟨x, hxA, rfl⟩
    exact Ψ.toPartialEquiv.map_target (hA_target hxA)
  have himage : Ψ '' B = A := by
    rw [hB_def]
    exact PartialEquiv.image_symm_image_of_subset_target Ψ.toPartialEquiv hA_target
  calc
    riemannianVolumeMeasure (I := I) (M := M) g A =
        riemannianVolumeMeasure (I := I) (M := M) g (Ψ '' B) := by
          rw [himage]
    _ = ∫⁻ w in B, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
          exact riemannianVolumeMeasure_image_param_eq (I := I) g Ψ hB_meas hB_source
    _ = ∫⁻ w in Ψ.symm '' A, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
          rw [hB_def]

set_option linter.unusedSectionVars false in
/-- The parametrized Gram matrix is symmetric.

The statement is purely pointwise: it follows from symmetry of the Riemannian
metric and is used in the positive-definite proof for the density consumed by
V1a/V2a. -/
lemma paramGramMatrix_isHermitian
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) (w : E) :
    (paramGramMatrix (I := I) g Ψ w).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show star (paramGramMatrix (I := I) g Ψ w j i) =
    paramGramMatrix (I := I) g Ψ w i j
  simp only [paramGramMatrix_apply, star_trivial]
  exact g.symm (Ψ w)
    (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j))
    (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))

set_option linter.unusedSectionVars false in
/-- The quadratic form of `paramGramMatrix` is the metric norm-square of the
corresponding linear combination of parametrized basis vectors.

This is the same Gram-matrix algebra used for `chartGramMatrix`; it is local to
the source and feeds the positivity proof required before the V0 density can be
used in V1a. -/
lemma paramGramMatrix_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) (w : E)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    star c ⬝ᵥ (paramGramMatrix (I := I) g Ψ w) *ᵥ c =
      g.inner (Ψ w)
        (∑ i, c i • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
        (∑ j, c j • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j)) := by
  have hexpand' :
      g.inner (Ψ w)
          (∑ i, c i • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
          (∑ j, c j • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j))
        = ∑ i, ∑ j, (c i * c j) *
            g.inner (Ψ w)
              (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
              (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j)) := by
    have hL :
        g.inner (Ψ w)
            (∑ i, c i • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
          = ∑ i, c i •
              g.inner (Ψ w)
                (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
    rw [hL]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ContinuousLinearMap.smul_apply]
    have hR :
        g.inner (Ψ w)
            (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
            (∑ j, c j • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j))
          = ∑ j, c j *
              g.inner (Ψ w)
                (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
                (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [map_smul, smul_eq_mul]
    rw [hR, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexpand']
  simp only [dotProduct, Matrix.mulVec, paramGramMatrix_apply, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

set_option linter.unusedSectionVars false in
/-- The pulled-back parametrization Gram matrix is positive definite on
`Ψ.source`.

The proof uses that `dΨ_w` is injective because `Ψ` is a `C¹` partial
diffeomorphism.  This is the positivity input for the parametrized density
used by V1 normal coordinates and later polar/entropy integrations. -/
lemma paramGramMatrix_posDef
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source) :
    (paramGramMatrix (I := I) g Ψ w).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (paramGramMatrix_isHermitian (I := I) g Ψ w) ?_
  intro c hc
  set v : TangentSpace I (Ψ w) :=
    ∑ i, c i • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i) with hv_def
  have heq := paramGramMatrix_dotProduct_mulVec (I := I) g Ψ w c
  rw [heq]
  have hker := paramDeriv_ker (I := I) Ψ hw
  have hli : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i)) := by
    simpa [Function.comp_def] using
      (chartModelBasis E).linearIndependent.map'
        (mfderiv 𝓘(ℝ, E) I Ψ w).toLinearMap hker
  have hvnz : v ≠ 0 := by
    intro hv0
    rw [Fintype.linearIndependent_iff] at hli
    have : c = 0 := funext (hli c hv0)
    exact hc this
  exact g.pos (Ψ w) v hvnz

set_option linter.unusedSectionVars false in
/-- The determinant of `paramGramMatrix` is positive on `Ψ.source`.

This is the determinant form of local invertibility and metric positivity.  It
is the direct scalar input for `paramDensity_pos` and the V0 transformation law. -/
lemma paramGramMatrix_det_pos
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source) :
    0 < (paramGramMatrix (I := I) g Ψ w).det :=
  (paramGramMatrix_posDef (I := I) g Ψ hw).det_pos

set_option linter.unusedSectionVars false in
/-- The parametrization density is strictly positive on the source.

The source hypothesis is the precise scale/domain condition: positivity holds
where the partial diffeomorphism supplies an invertible `C¹` differential.  This
is consumed by V1a at the normal chart, and by V2/polar estimates whenever the
parametrized density is bounded above and below. -/
lemma paramDensity_pos
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source) :
    0 < paramDensity (I := I) g Ψ w :=
  Real.sqrt_pos.mpr (paramGramMatrix_det_pos (I := I) g Ψ hw)

end Measure
end Integral
end DifferentialGeometry
