import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CorrectionContraction
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ContinuationCalculusReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometryFrontier
import DifferentialGeometry.Geometry.Submanifold.IsometricImmersionGauss
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Function Manifold Set Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian.Geodesic (chartChristoffelContraction)

open private gaussDefectModelValue secondFundamentalFormAmbientAt_apply
  from DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise

section ModelCoordinateFormula

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem secondFundamentalFormAmbientAt_modelCoord
    (gN : SmoothRiemannianMetric IN N) (gM : SmoothRiemannianMetric I M)
    (iota : N → M) (x : N) (u v : TangentSpace IN x) :
    tangentSpaceModelContinuousLinearEquiv (I := I) (iota x)
        (secondFundamentalFormAmbientAt gN gM iota x u v) =
      fderiv ℝ (fderiv ℝ (writtenInExtChartAt IN I x iota)) (extChartAt IN x x)
          (tangentSpaceModelContinuousLinearEquiv (I := IN) x u)
          (tangentSpaceModelContinuousLinearEquiv (I := IN) x v) +
        chartChristoffelContraction (I := I) gM (iota x)
          (tangentLinearMapToModel (mfderiv IN I iota x)
            (tangentSpaceModelContinuousLinearEquiv (I := IN) x u))
          (tangentLinearMapToModel (mfderiv IN I iota x)
            (tangentSpaceModelContinuousLinearEquiv (I := IN) x v))
          (extChartAt I (iota x) (iota x)) -
        tangentLinearMapToModel (mfderiv IN I iota x)
          (chartChristoffelContraction (I := IN) gN x
            (tangentSpaceModelContinuousLinearEquiv (I := IN) x u)
            (tangentSpaceModelContinuousLinearEquiv (I := IN) x v)
            (extChartAt IN x x)) := by
  rw [secondFundamentalFormAmbientAt_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp only [gaussDefectModelValue]

end ModelCoordinateFormula

section OpensChart

variable {m : ℕ}

private theorem chartAt_modelSpace_source (y : EuclideanSpace ℝ (Fin m)) :
    (chartAt (EuclideanSpace ℝ (Fin m)) y).source = Set.univ := by
  rw [chartAt_self_eq]
  rfl

private theorem chartAt_modelSpace_apply (y z : EuclideanSpace ℝ (Fin m)) :
    (chartAt (EuclideanSpace ℝ (Fin m)) y) z = z := by
  rw [chartAt_self_eq]
  rfl

private theorem opens_chart_eq (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (x : U) :
    (chartAt (M := U) (EuclideanSpace ℝ (Fin m)) x : OpenPartialHomeomorph U
        (EuclideanSpace ℝ (Fin m))) =
      ((chartAt (EuclideanSpace ℝ (Fin m)) (Subtype.val x)).subtypeRestr ⟨x⟩ :
        OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin m))) :=
  TopologicalSpace.Opens.chartAt_eq

private theorem opens_chart_source_mem (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (x p : U) :
    p ∈ (chartAt (M := U) (EuclideanSpace ℝ (Fin m)) x : OpenPartialHomeomorph U
      (EuclideanSpace ℝ (Fin m))).source := by
  rw [opens_chart_eq U x, OpenPartialHomeomorph.subtypeRestr_source,
    chartAt_modelSpace_source]
  trivial

private theorem opens_chart_apply (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (x p : U) :
    ((chartAt (M := U) (EuclideanSpace ℝ (Fin m)) x : OpenPartialHomeomorph U
      (EuclideanSpace ℝ (Fin m))) p) = (Subtype.val p : EuclideanSpace ℝ (Fin m)) := by
  rw [opens_chart_eq U x, OpenPartialHomeomorph.subtypeRestr_coe]
  exact chartAt_modelSpace_apply (Subtype.val x) (Subtype.val p)

private theorem extChartAt_opens_apply (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (x p : U) :
    extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x p
      = (Subtype.val p : EuclideanSpace ℝ (Fin m)) := by
  rw [extChartAt_coe]
  simpa only [Function.comp_apply, modelWithCornersSelf_coe, id_eq] using
    opens_chart_apply U x p

private theorem extChartAt_opens_symm_apply
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m))) (x p : U) :
    (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x).symm (Subtype.val p) = p := by
  rw [← extChartAt_opens_apply U x p]
  refine (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x).left_inv ?_
  change p ∈ ((chartAt (M := U) (EuclideanSpace ℝ (Fin m)) x).extend
    (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))).source
  rw [OpenPartialHomeomorph.extend_source]
  exact opens_chart_source_mem U x p

end OpensChart

section OpensFormula

variable {m : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem writtenInExtChartAt_opens_eventuallyEq
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M) (x : U) :
    writtenInExtChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) I x (fun y : U => F y)
      =ᶠ[𝓝 (Subtype.val x)]
      (fun q : EuclideanSpace ℝ (Fin m) => extChartAt I (F x) (F q)) := by
  refine Filter.eventuallyEq_of_mem (U.2.mem_nhds x.2) ?_
  intro z hz
  simp only [writtenInExtChartAt, Function.comp_apply]
  rw [extChartAt_opens_symm_apply U x ⟨z, hz⟩]

private theorem writtenInExtChartAt_opensModelSpace
    (F : EuclideanSpace ℝ (Fin m) → M) (x : EuclideanSpace ℝ (Fin m)) :
    writtenInExtChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) I x F
      = fun q : EuclideanSpace ℝ (Fin m) => extChartAt I (F x) (F q) := by
  funext q
  simp only [writtenInExtChartAt, Function.comp_apply]
  rw [show (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x).symm q = q from by
    rw [extChartAt_model_space_eq_id]
    rfl]

end OpensFormula

section CalculusFlip

private theorem fderiv_fderiv_apply_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : V → W} {a : V} (hg : ContDiffAt ℝ 2 g a) (X Y : V) :
    fderiv ℝ (fun q => fderiv ℝ g q Y) a X = (fderiv ℝ (fderiv ℝ g) a) X Y := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) a :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) a) a := hd.hasFDerivAt
  have hu : HasFDerivAt (fun _ : V => Y) (0 : V →L[ℝ] V) a := hasFDerivAt_const Y a
  have h := (hc.clm_apply hu).fderiv
  rw [h]
  simp

end CalculusFlip

section OpensChartFormula

variable {m : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem secondFundamentalFormAmbientAt_modelCoord_opens
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (x : U) (X Y : EuclideanSpace ℝ (Fin m)) :
    (tangentSpaceModelContinuousLinearEquiv (I := I) (F x))
        (secondFundamentalFormAmbientAt (I := I)
          (IN := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) h g (fun y : U => F y) x X Y)
      = fderiv ℝ (fun q => fderiv ℝ ((extChartAt I (F x)) ∘ F) q Y) x X +
        chartChristoffelContraction (I := I) g (F x)
          (fderiv ℝ ((extChartAt I (F x)) ∘ F) x X)
          (fderiv ℝ ((extChartAt I (F x)) ∘ F) x Y)
          (extChartAt I (F x) (F x)) -
        (tangentSpaceModelContinuousLinearEquiv (I := I) (F x))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x
            (chartChristoffelContraction (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) h x X Y
              (Subtype.val x))) := by
  have hAt : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F (Subtype.val x) :=
    hF.contMDiffAt (U.2.mem_nhds x.2)
  have hmd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F (Subtype.val x) :=
    hAt.mdifferentiableAt (by simp)
  have hG2 : ContDiffAt ℝ 2 ((extChartAt I (F x)) ∘ F) (Subtype.val x) := by
    have h := (contMDiffAt_iff.mp hAt).2
    rw [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ] at h
    refine (h.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)).congr_of_eventuallyEq ?_
    filter_upwards with q
    simp only [Function.comp_apply]
    rw [show (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (Subtype.val x)).symm q = q from by
      rw [extChartAt_model_space_eq_id]
      rfl]
  have hwritten := writtenInExtChartAt_opensModelSpace (I := I) F (Subtype.val x)
  have hcomp := writtenInExtChartAt_opens_eventuallyEq (I := I) U F x
  have hdiote (v : EuclideanSpace ℝ (Fin m)) :
      tangentLinearMapToModel
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I (fun y : U => F y) x) v
        = fderiv ℝ ((extChartAt I (F x)) ∘ F) x v := by
    have h1 := tangentLinearMapToModel_mfderiv_eq_fderiv_writtenInExtChartAt (IN :=
      𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I := I) (iota := F) hmd v
    rw [hwritten,
      show extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (Subtype.val x) (Subtype.val x)
        = (Subtype.val x : EuclideanSpace ℝ (Fin m)) from by
        rw [extChartAt_model_space_eq_id]
        rfl] at h1
    rw [DifferentialGeometry.mfderiv_restrict_open F U x]
    exact h1
  rw [secondFundamentalFormAmbientAt_modelCoord (gN := h) (gM := g)
    (iota := fun y : U => F y) (x := x) (u := X) (v := Y)]
  simp only [tangentSpaceModelContinuousLinearEquiv_apply]
  rw [extChartAt_opens_apply U x x]
  rw [hcomp.fderiv.fderiv_eq]
  rw [fderiv_fderiv_apply_eq (g := (extChartAt I (F x)) ∘ F)
    (hG2.of_le (by norm_num)) X Y]
  rw [hdiote X, hdiote Y]
  rw [tangentLinearMapToModel_apply, tangentSpaceModelContinuousLinearEquiv_symm_apply,
    tangentSpaceModelContinuousLinearEquiv_apply,
    DifferentialGeometry.mfderiv_restrict_open F U x]
  rfl

end OpensChartFormula

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion
open DifferentialGeometry.Geometry.Riemannian.Geodesic (chartChristoffelContraction)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem hasAmbientGaussEquation_iff_hasGaussEquation [I.Boundaryless] {m : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (himmersion : IsRiemannianIsometricImmersion h g (fun y : U => F y)) :
    hasAmbientGaussEquation U F g h ↔ himmersion.hasGaussEquation := by
  constructor
  · intro hgauss x X Y Z W
    have h1 := hgauss x X Y Z W
    rw [← mfderiv_restrict_open F U x] at h1
    simp only [] at h1 ⊢
    simp only [
      secondFundamentalFormAt_coe_eq_ambient himmersion x X W,
      secondFundamentalFormAt_coe_eq_ambient himmersion x Y Z,
      secondFundamentalFormAt_coe_eq_ambient himmersion x X Z,
      secondFundamentalFormAt_coe_eq_ambient himmersion x Y W] at h1 ⊢
    exact h1
  · intro hgauss x X Y Z W
    have h1 := hgauss x X Y Z W
    rw [mfderiv_restrict_open F U x] at h1
    simp only [] at h1 ⊢
    simp only [
      secondFundamentalFormAt_coe_eq_ambient himmersion x X W,
      secondFundamentalFormAt_coe_eq_ambient himmersion x Y Z,
      secondFundamentalFormAt_coe_eq_ambient himmersion x X Z,
      secondFundamentalFormAt_coe_eq_ambient himmersion x Y W] at h1 ⊢
    exact h1

omit [CompleteSpace E] in
theorem immersionSecondFundamental_eq_secondFundamentalFormAmbientAt_of_contMDiffOn {m : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U) :
    immersionSecondFundamental_eq_secondFundamentalFormAmbientAt U F g h :=
  immersionSecondFundamental_eq_secondFundamentalFormAmbientAt_of_chartCoord U F hF g h
    (fun x X Y => DifferentialGeometry.Geometry.secondFundamentalFormAmbientAt_modelCoord_opens
      U F hF g h x X Y)

omit [CompleteSpace E] in
theorem immersionSecondFundamental_inner_mfderiv_eq_zero [I.Boundaryless] {m : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (himmersion : IsRiemannianIsometricImmersion h g (fun y : U => F y))
    (x : U) (X Y Z : EuclideanSpace ℝ (Fin m)) :
    g.inner (F x) (immersionSecondFundamental U F g h x X Y)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Z) = 0 := by
  have hchart : immersionSecondFundamental_eq_secondFundamentalFormAmbientAt U F g h :=
    immersionSecondFundamental_eq_secondFundamentalFormAmbientAt_of_chartCoord U F hF g h
      (fun x X Y => DifferentialGeometry.Geometry.secondFundamentalFormAmbientAt_modelCoord_opens
        U F hF g h x X Y)
  rw [hchart x X Y, ← mfderiv_restrict_open F U x]
  exact IsRiemannianIsometricImmersion.secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero
    himmersion x X Y Z

omit [CompleteSpace E] in
theorem isometricImmersionPullbackConnection_of_isRiemannianIsometricImmersion [I.Boundaryless]
    {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (himmersion : IsRiemannianIsometricImmersion h g (fun y : U => F y)) :
    IsometricImmersionPullbackConnection g F U h := by
  refine (isometricImmersionPullbackConnection_iff_secondFundamentalForm_orthogonal g F U h
    (fun x X Y => ?_)).mpr ?_
  · rw [← mfderiv_restrict_open F U x]
    exact (himmersion.inner_map x X Y).symm
  intro x X Y Z
  have h := immersionSecondFundamental_inner_mfderiv_eq_zero U F hF g h himmersion x X Y Z
  simp only [immersionSecondFundamental] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
