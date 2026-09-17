import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Metric.Family.Basic
import DifferentialGeometry.Analysis.Integration.Integral.ParametricIntervalContinuity
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold Topology Interval

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem continuousOn_lVelocity_family
    {alpha : E × Real → M} {V : Set E} {K : Set Real}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I 1 alpha (V ×ˢ K)) :
    ContinuousOn
      (fun q : E × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I)
          (alpha q)
          (lVelocity (I := I) (fun s ↦ alpha (q.1, s)) q.2) :
            TangentBundle I M)) (V ×ˢ K) := by
  let J := 𝓘(Real, E).prod 𝓘(Real, Real)
  let U := V ×ˢ K
  have hUopen : IsOpen U := hVopen.prod hKopen
  have htm :=
    halpha.continuousOn_tangentMapWithin le_rfl hUopen.uniqueMDiffOn
  have hunit : ContMDiff J J.tangent ∞
      (fun q : E × Real ↦
        (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)) :
          TangentBundle J (E × Real))) := by
    have hE : ContMDiff 𝓘(Real, E) 𝓘(Real, E).tangent ∞
        (fun z : E ↦ (TotalSpace.mk' E z (0 : E) : TangentBundle 𝓘(Real, E) E)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : E ↦ (0 : E))).mpr contDiff_const
    have hR : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real).tangent ∞
        (fun r : Real ↦
          (TotalSpace.mk' Real r (1 : Real) : TangentBundle 𝓘(Real, Real) Real)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real ↦ (1 : Real))).mpr contDiff_const
    have hpair := (hE.comp contMDiff_fst).prodMk (hR.comp contMDiff_snd)
    have hsymm : ContMDiff
        (𝓘(Real, E).tangent.prod 𝓘(Real, Real).tangent) J.tangent ∞
        ((equivTangentBundleProd 𝓘(Real, E) E
          𝓘(Real, Real) Real).symm) :=
      contMDiff_equivTangentBundleProd_symm
    change ContMDiff J J.tangent ∞
      ((equivTangentBundleProd 𝓘(Real, E) E
        𝓘(Real, Real) Real).symm ∘ fun q : E × Real ↦
          ((TotalSpace.mk' E q.1 (0 : E) : TangentBundle 𝓘(Real, E) E),
            (TotalSpace.mk' Real q.2 (1 : Real) :
              TangentBundle 𝓘(Real, Real) Real)))
    exact hsymm.comp hpair
  have hcomp : ContinuousOn
      (fun q : E × Real ↦ tangentMapWithin J I alpha U
        (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)))) U :=
    htm.comp hunit.continuous.continuousOn (fun _ hq ↦ hq)
  refine hcomp.congr ?_
  intro q hq
  have hwithin : mfderivWithin J I alpha U q = mfderiv J I alpha q :=
    mfderivWithin_of_isOpen hUopen hq
  have hdiff : MDifferentiableAt J I alpha q :=
    ((halpha q hq).contMDiffAt (hUopen.mem_nhds hq)).mdifferentiableAt (by simp)
  have hsplit := mfderiv_prod_eq_add_apply
    (I := 𝓘(Real, E)) (I' := 𝓘(Real, Real)) (I'' := I)
    (f := alpha) (p := q) (v := ((0 : E), (1 : Real))) hdiff
  have hzero :
      mfderiv 𝓘(Real, E) I (fun z : E ↦ alpha (z, q.2)) q.1 (0 : E) = 0 :=
    (mfderiv 𝓘(Real, E) I (fun z : E ↦ alpha (z, q.2)) q.1).map_zero
  change TotalSpace.mk' E (E := TangentSpace I) (alpha q)
      (lVelocity (I := I) (fun s ↦ alpha (q.1, s)) q.2) =
    tangentMapWithin J I alpha U
      (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)))
  simp only [tangentMapWithin, hwithin]
  refine TotalSpace.ext rfl ?_
  exact heq_of_eq (by
    simpa only [lVelocity, hzero, zero_add] using hsplit.symm)


variable [FiniteDimensional ℝ E] [T2Space M]

theorem continuousOn_lRegularizedLagrangian_family_of_contMDiffOn_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) {alpha : E × ℝ → M} {V : Set E} {K : Set ℝ}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1 alpha (V ×ˢ K))
    (hcarrier : ∀ s ∈ K, T - s ^ 2 ∈ D.carrier) :
    ContinuousOn
      (fun q : E × ℝ => lRegularizedLagrangian S T (fun s => alpha (q.1, s)) q.2)
      (V ×ˢ K) := by
  let P := {q : E × ℝ // q ∈ V ×ˢ K}
  let timeLift : P → {t : ℝ // t ∈ D.carrier} :=
    fun q => ⟨T - q.1.2 ^ 2, hcarrier q.1.2 q.2.2⟩
  let velocityLift : P → TangentBundle I M := fun q =>
    ⟨alpha q.1, lVelocity (I := I) (fun s => alpha (q.1.1, s)) q.1.2⟩
  have htime : Continuous timeLift :=
    (continuous_const.sub ((continuous_snd.comp continuous_subtype_val).pow 2)).subtype_mk _
  have hvel : Continuous velocityLift :=
    (continuousOn_lVelocity_family hVopen hKopen halpha).domRestrict
  have hbase : Continuous (fun q : P => alpha q.1) := halpha.continuousOn.domRestrict
  have hquad := metricTimeBundleQuad_cont_of_metricFamilySmoothOn
    (I := I) (M := M) S.family.metric hS.smoothMetric
    (K := D.carrier) (fun _ ht => ht)
  have hkin0 := hquad.comp (htime.prodMk hvel)
  have hkin : Continuous (fun q : P =>
      (S.base.metric (T - q.1.2 ^ 2)).inner (alpha q.1)
        (lVelocity (I := I) (fun s => alpha (q.1.1, s)) q.1.2)
        (lVelocity (I := I) (fun s => alpha (q.1.1, s)) q.1.2)) := hkin0
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hscalar := hSc.continuous_subtype.comp (htime.prodMk hbase)
  have hlag : Continuous (fun q : P =>
      (1 / 2 : ℝ) *
          (S.base.metric (T - q.1.2 ^ 2)).inner (alpha q.1)
            (lVelocity (I := I) (fun s => alpha (q.1.1, s)) q.1.2)
            (lVelocity (I := I) (fun s => alpha (q.1.1, s)) q.1.2) +
        2 * q.1.2 ^ 2 * S.scalar (T - q.1.2 ^ 2) (alpha q.1)) :=
    (continuous_const.mul hkin).add
      ((continuous_const.mul
        ((continuous_snd.comp continuous_subtype_val).pow 2)).mul hscalar)
  rw [continuousOn_iff_continuous_domRestrict]
  exact hlag

theorem continuousOn_lRegularizedAction_family_of_contMDiffOn_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T a b : ℝ) {alpha : E × ℝ → M} {V : Set E} {K : Set ℝ}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1 alpha (V ×ˢ K))
    (hcarrier : ∀ s ∈ K, T - s ^ 2 ∈ D.carrier) (hslab : [[a, b]] ⊆ K) :
    ContinuousOn (fun A => lRegularizedAction S T (fun s => alpha (A, s)) a b) V := by
  have hlag := continuousOn_lRegularizedLagrangian_family_of_contMDiffOn_one
    S hS T hVopen hKopen halpha hcarrier
  exact intervalIntegral.continuousOn_integral_of_continuousOn_prod hVopen
    (hlag.mono (prod_mono subset_rfl hslab))

end DifferentialGeometry.PDE.RicciFlow.Perelman
