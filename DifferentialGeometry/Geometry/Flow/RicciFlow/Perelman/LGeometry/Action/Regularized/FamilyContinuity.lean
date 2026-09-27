import DifferentialGeometry.Topology.Manifold.CurveEndpointPerturbation
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

variable {F E H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem continuousOn_lVelocity_family
    {alpha : F × Real → M} {V : Set F} {K : Set Real}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn
      (𝓘(Real, F).prod 𝓘(Real, Real)) I 1 alpha (V ×ˢ K)) :
    ContinuousOn
      (fun q : F × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I)
          (alpha q)
          (lVelocity (I := I) (fun s ↦ alpha (q.1, s)) q.2) :
            TangentBundle I M)) (V ×ˢ K) := by
  let J := 𝓘(Real, F).prod 𝓘(Real, Real)
  let U := V ×ˢ K
  have hUopen : IsOpen U := hVopen.prod hKopen
  have htm :=
    halpha.continuousOn_tangentMapWithin le_rfl hUopen.uniqueMDiffOn
  have hunit : ContMDiff J J.tangent ∞
      (fun q : F × Real ↦
        (TotalSpace.mk' (F × Real) q ((0 : F), (1 : Real)) :
          TangentBundle J (F × Real))) := by
    have hF : ContMDiff 𝓘(Real, F) 𝓘(Real, F).tangent ∞
        (fun z : F ↦ (TotalSpace.mk' F z (0 : F) : TangentBundle 𝓘(Real, F) F)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : F ↦ (0 : F))).mpr contDiff_const
    have hR : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real).tangent ∞
        (fun r : Real ↦
          (TotalSpace.mk' Real r (1 : Real) : TangentBundle 𝓘(Real, Real) Real)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real ↦ (1 : Real))).mpr contDiff_const
    have hpair := (hF.comp contMDiff_fst).prodMk (hR.comp contMDiff_snd)
    have hsymm : ContMDiff
        (𝓘(Real, F).tangent.prod 𝓘(Real, Real).tangent) J.tangent ∞
        ((equivTangentBundleProd 𝓘(Real, F) F
          𝓘(Real, Real) Real).symm) :=
      contMDiff_equivTangentBundleProd_symm
    change ContMDiff J J.tangent ∞
      ((equivTangentBundleProd 𝓘(Real, F) F
        𝓘(Real, Real) Real).symm ∘ fun q : F × Real ↦
          ((TotalSpace.mk' F q.1 (0 : F) : TangentBundle 𝓘(Real, F) F),
            (TotalSpace.mk' Real q.2 (1 : Real) :
              TangentBundle 𝓘(Real, Real) Real)))
    exact hsymm.comp hpair
  have hcomp : ContinuousOn
      (fun q : F × Real ↦ tangentMapWithin J I alpha U
        (TotalSpace.mk' (F × Real) q ((0 : F), (1 : Real)))) U :=
    htm.comp hunit.continuous.continuousOn (fun _ hq ↦ hq)
  refine hcomp.congr ?_
  intro q hq
  have hwithin : mfderivWithin J I alpha U q = mfderiv J I alpha q :=
    mfderivWithin_of_isOpen hUopen hq
  have hdiff : MDifferentiableAt J I alpha q :=
    ((halpha q hq).contMDiffAt (hUopen.mem_nhds hq)).mdifferentiableAt (by simp)
  have hsplit := mfderiv_prod_eq_add_apply
    (I := 𝓘(Real, F)) (I' := 𝓘(Real, Real)) (I'' := I)
    (f := alpha) (p := q) (v := ((0 : F), (1 : Real))) hdiff
  have hzero :
      mfderiv 𝓘(Real, F) I (fun z : F ↦ alpha (z, q.2)) q.1 (0 : F) = 0 :=
    (mfderiv 𝓘(Real, F) I (fun z : F ↦ alpha (z, q.2)) q.1).map_zero
  change TotalSpace.mk' E (E := TangentSpace I) (alpha q)
      (lVelocity (I := I) (fun s ↦ alpha (q.1, s)) q.2) =
    tangentMapWithin J I alpha U
      (TotalSpace.mk' (F × Real) q ((0 : F), (1 : Real)))
  simp only [tangentMapWithin, hwithin]
  refine TotalSpace.ext rfl ?_
  exact heq_of_eq (by
    simpa only [lVelocity, hzero, zero_add] using hsplit.symm)


variable [FiniteDimensional ℝ E] [T2Space M]

theorem continuousOn_lRegularizedLagrangian_family_of_contMDiffOn_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) {alpha : F × ℝ → M} {V : Set F} {K J : Set ℝ}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn (𝓘(ℝ, F).prod 𝓘(ℝ, ℝ)) I 1 alpha (V ×ˢ K))
    (hJK : J ⊆ K) (hcarrier : ∀ s ∈ J, T - s ^ 2 ∈ D.carrier) :
    ContinuousOn
      (fun q : F × ℝ => lRegularizedLagrangian S T (fun s => alpha (q.1, s)) q.2)
      (V ×ˢ J) := by
  let P := {q : F × ℝ // q ∈ V ×ˢ J}
  let timeLift : P → {t : ℝ // t ∈ D.carrier} :=
    fun q => ⟨T - q.1.2 ^ 2, hcarrier q.1.2 q.2.2⟩
  let velocityLift : P → TangentBundle I M := fun q =>
    ⟨alpha q.1, lVelocity (I := I) (fun s => alpha (q.1.1, s)) q.1.2⟩
  have htime : Continuous timeLift :=
    (continuous_const.sub ((continuous_snd.comp continuous_subtype_val).pow 2)).subtype_mk _
  have hvel : Continuous velocityLift :=
    ((continuousOn_lVelocity_family hVopen hKopen halpha).mono
      (prod_mono subset_rfl hJK)).domRestrict
  have hbase : Continuous (fun q : P => alpha q.1) :=
    (halpha.continuousOn.mono (prod_mono subset_rfl hJK)).domRestrict
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
    (T a b : ℝ) {alpha : F × ℝ → M} {V : Set F} {K : Set ℝ}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn (𝓘(ℝ, F).prod 𝓘(ℝ, ℝ)) I 1 alpha (V ×ˢ K))
    (hcarrier : ∀ s ∈ [[a, b]], T - s ^ 2 ∈ D.carrier) (hslab : [[a, b]] ⊆ K) :
    ContinuousOn (fun A => lRegularizedAction S T (fun s => alpha (A, s)) a b) V := by
  have hlag := continuousOn_lRegularizedLagrangian_family_of_contMDiffOn_one
    S hS T hVopen hKopen halpha hslab hcarrier
  exact intervalIntegral.continuousOn_integral_of_continuousOn_prod hVopen hlag

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem exists_open_endpoint_family_of_lRegularizedAction_lt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b L : ℝ} (hab : a < b)
    (hcarrier : ∀ t ∈ Icc a b, T - t ^ 2 ∈ D.carrier)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hact : lRegularizedAction S T γ a b < L) :
    ∃ U : Set M, IsOpen U ∧ γ b ∈ U ∧ ∃ α : M → ℝ → M,
      (∀ y ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (α y)) ∧
      (∀ y ∈ U, α y a = γ a) ∧ (∀ y ∈ U, α y b = y) ∧
      (∀ t, α (γ b) t = γ t) ∧
      ∀ y ∈ U, lRegularizedAction S T (α y) a b < L := by
  obtain ⟨V, hV, hqV, β, hβ, hslices, hstart, hend, hcenter⟩ :=
    Geometry.exists_contMDiff_endpoint_perturbation γ hγ hab
  let p := γ b
  let q : E := extChartAt I p p
  have hcont := continuousOn_lRegularizedAction_family_of_contMDiffOn_one S hS T a b
    hV isOpen_univ hβ (by simpa only [uIcc_of_le hab.le] using hcarrier) (subset_univ _)
  have hactq : lRegularizedAction S T (fun t => β (q, t)) a b < L := by
    have heq : (fun t => β (q, t)) = γ := funext hcenter
    rwa [heq]
  have hq : q ∈ V := hqV
  have hparam : ∀ᶠ A in 𝓝 q, lRegularizedAction S T (fun t => β (A, t)) a b < L :=
    ((hcont q hq).continuousAt (hV.mem_nhds hq)).eventually (Iio_mem_nhds hactq)
  have hcoord : ContinuousAt (fun y : M => extChartAt I p y) p := continuousAt_extChartAt p
  have hnear : {y : M | lRegularizedAction S T (fun t => β (extChartAt I p y, t)) a b < L ∧
      extChartAt I p y ∈ V ∧ y ∈ (extChartAt I p).source} ∈ 𝓝 p := by
    filter_upwards [hcoord.tendsto.eventually hparam,
      hcoord.tendsto.eventually (hV.mem_nhds hq),
      (isOpen_extChartAt_source (I := I) p).mem_nhds (mem_extChartAt_source p)] with y hyact hyV hys
    exact ⟨hyact, hyV, hys⟩
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hnear
  let α : M → ℝ → M := fun y t => β (extChartAt I p y, t)
  refine ⟨U, hU, hpU, α, ?_, ?_, ?_, hcenter, ?_⟩
  · intro y hy
    exact hslices _ (hUsub hy).2.1
  · intro y hy
    exact hstart _ (hUsub hy).2.1
  · intro y hy
    exact (hend _ (hUsub hy).2.1).trans ((extChartAt I p).left_inv (hUsub hy).2.2)
  · intro y hy
    exact (hUsub hy).1

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem exists_open_two_endpoint_family_of_lRegularizedAction_lt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b L : ℝ} (hab : a < b)
    (hcarrier : ∀ t ∈ Icc a b, T - t ^ 2 ∈ D.carrier)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hact : lRegularizedAction S T γ a b < L) :
    ∃ U V : Set M, IsOpen U ∧ IsOpen V ∧ γ a ∈ U ∧ γ b ∈ V ∧
      ∃ α : M × M → ℝ → M,
        (∀ x ∈ U, ∀ y ∈ V, ContMDiff 𝓘(ℝ, ℝ) I 1 (α (x, y))) ∧
        (∀ x ∈ U, ∀ y ∈ V, α (x, y) a = x) ∧
        (∀ x ∈ U, ∀ y ∈ V, α (x, y) b = y) ∧
        (∀ t, α (γ a, γ b) t = γ t) ∧
        ∀ x ∈ U, ∀ y ∈ V, lRegularizedAction S T (α (x, y)) a b < L := by
  obtain ⟨A, B, hA, hB, hqa, hqb, β, hβ, hslices, hstart, hend, hcenter⟩ :=
    Geometry.exists_contMDiff_two_endpoint_perturbation γ hγ hab
  let p := γ a
  let q := γ b
  let z : E × E := (extChartAt I p p, extChartAt I q q)
  have hz : z ∈ A ×ˢ B := ⟨hqa, hqb⟩
  have hcont := continuousOn_lRegularizedAction_family_of_contMDiffOn_one S hS T a b
    (hA.prod hB) isOpen_univ hβ (by simpa only [uIcc_of_le hab.le] using hcarrier) (subset_univ _)
  have hcenterAct : lRegularizedAction S T (fun t => β (z, t)) a b < L := by
    have heq : (fun t => β (z, t)) = γ := funext hcenter
    rwa [heq]
  have hparam : ∀ᶠ C in 𝓝 z, lRegularizedAction S T (fun t => β (C, t)) a b < L :=
    ((hcont z hz).continuousAt ((hA.prod hB).mem_nhds hz)).eventually (Iio_mem_nhds hcenterAct)
  let coord : M × M → E × E := fun w => (extChartAt I p w.1, extChartAt I q w.2)
  have hp : ContinuousAt (fun x : M => extChartAt I p x) p := continuousAt_extChartAt p
  have hq : ContinuousAt (fun x : M => extChartAt I q x) q := continuousAt_extChartAt q
  have hfst : ContinuousAt (fun w : M × M => w.1) (p, q) := continuous_fst.continuousAt
  have hsnd : ContinuousAt (fun w : M × M => w.2) (p, q) := continuous_snd.continuousAt
  have hcoord : ContinuousAt coord (p, q) := (hp.comp_of_eq hfst rfl).prodMk (hq.comp_of_eq hsnd rfl)
  have hnear : {w : M × M |
      lRegularizedAction S T (fun t => β (coord w, t)) a b < L ∧
      coord w ∈ A ×ˢ B ∧ w.1 ∈ (extChartAt I p).source ∧ w.2 ∈ (extChartAt I q).source} ∈ 𝓝 (p, q) := by
    filter_upwards [hcoord.tendsto.eventually hparam,
      hcoord.tendsto.eventually ((hA.prod hB).mem_nhds hz),
      continuous_fst.continuousAt.eventually ((isOpen_extChartAt_source (I := I) p).mem_nhds (mem_extChartAt_source p)),
      continuous_snd.continuousAt.eventually ((isOpen_extChartAt_source (I := I) q).mem_nhds (mem_extChartAt_source q))]
      with w hwact hwAB hwA hwB
    exact ⟨hwact, hwAB, hwA, hwB⟩
  obtain ⟨U, hUp, V, hVq, hUV⟩ := mem_nhds_prod_iff.mp hnear
  obtain ⟨U', hU'sub, hU', hpU'⟩ := mem_nhds_iff.mp hUp
  obtain ⟨V', hV'sub, hV', hqV'⟩ := mem_nhds_iff.mp hVq
  let α : M × M → ℝ → M := fun w t => β (coord w, t)
  have hmem (x : M) (hx : x ∈ U') (y : M) (hy : y ∈ V') :
      lRegularizedAction S T (fun t => β (coord (x, y), t)) a b < L ∧
      coord (x, y) ∈ A ×ˢ B ∧ x ∈ (extChartAt I p).source ∧ y ∈ (extChartAt I q).source :=
    hUV (show (x, y) ∈ U ×ˢ V from ⟨hU'sub hx, hV'sub hy⟩)
  refine ⟨U', V', hU', hV', hpU', hqV', α, ?_, ?_, ?_, hcenter, ?_⟩
  · intro x hx y hy
    exact hslices _ (hmem x hx y hy).2.1.1 _ (hmem x hx y hy).2.1.2
  · intro x hx y hy
    exact (hstart _ (hmem x hx y hy).2.1.1 _ (hmem x hx y hy).2.1.2).trans
      ((extChartAt I p).left_inv (hmem x hx y hy).2.2.1)
  · intro x hx y hy
    exact (hend _ (hmem x hx y hy).2.1.1 _ (hmem x hx y hy).2.1.2).trans
      ((extChartAt I q).left_inv (hmem x hx y hy).2.2.2)
  · intro x hx y hy
    exact (hmem x hx y hy).1

end DifferentialGeometry.PDE.RicciFlow.Perelman
