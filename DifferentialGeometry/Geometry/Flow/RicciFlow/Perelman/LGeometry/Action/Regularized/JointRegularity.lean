import DifferentialGeometry.Analysis.Integration.Measure.Parametric.FiniteIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH uP

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace Real P]
variable {D : RealTimeInterval}

omit [FiniteDimensional Real E] [T2Space M] in
private theorem contMDiffOn_lVelocity_family_two
    {alpha : P × Real → M} {V : Set P} {K : Set Real}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn
      (𝓘(Real, P).prod 𝓘(Real, Real)) I 8 alpha (V ×ˢ K)) :
    ContMDiffOn (𝓘(Real, P).prod 𝓘(Real, Real)) I.tangent 2
      (fun q : P × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I)
          (alpha q)
          (lVelocity (I := I) (fun s ↦ alpha (q.1, s)) q.2) :
            TangentBundle I M)) (V ×ˢ K) := by
  let J := 𝓘(Real, P).prod 𝓘(Real, Real)
  let U := V ×ˢ K
  have hUopen : IsOpen U := hVopen.prod hKopen
  have htm :=
    halpha.contMDiffOn_tangentMapWithin (m := 2) (by norm_num) hUopen.uniqueMDiffOn
  have hunit : ContMDiff J J.tangent 2
      (fun q : P × Real ↦
        (TotalSpace.mk' (P × Real) q ((0 : P), (1 : Real)) :
          TangentBundle J (P × Real))) := by
    have hE : ContMDiff 𝓘(Real, P) 𝓘(Real, P).tangent 2
        (fun z : P ↦ (TotalSpace.mk' P z (0 : P) : TangentBundle 𝓘(Real, P) P)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : P ↦ (0 : P))).mpr contDiff_const
    have hR : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real).tangent 2
        (fun r : Real ↦
          (TotalSpace.mk' Real r (1 : Real) : TangentBundle 𝓘(Real, Real) Real)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real ↦ (1 : Real))).mpr contDiff_const
    have hpair := (hE.comp contMDiff_fst).prodMk (hR.comp contMDiff_snd)
    have hsymm : ContMDiff
        (𝓘(Real, P).tangent.prod 𝓘(Real, Real).tangent) J.tangent 2
        ((equivTangentBundleProd 𝓘(Real, P) P
          𝓘(Real, Real) Real).symm) :=
      contMDiff_equivTangentBundleProd_symm
    change ContMDiff J J.tangent 2
      ((equivTangentBundleProd 𝓘(Real, P) P
        𝓘(Real, Real) Real).symm ∘ fun q : P × Real ↦
          ((TotalSpace.mk' P q.1 (0 : P) : TangentBundle 𝓘(Real, P) P),
            (TotalSpace.mk' Real q.2 (1 : Real) :
              TangentBundle 𝓘(Real, Real) Real)))
    exact hsymm.comp hpair
  have hcomp : ContMDiffOn J I.tangent 2
      (fun q : P × Real ↦ tangentMapWithin J I alpha U
        (TotalSpace.mk' (P × Real) q ((0 : P), (1 : Real)))) U :=
    htm.comp (hunit.contMDiffOn (s := U)) (fun _ hq ↦ hq)
  refine hcomp.congr ?_
  intro q hq
  have hwithin : mfderivWithin J I alpha U q = mfderiv J I alpha q :=
    mfderivWithin_of_isOpen hUopen hq
  have hdiff : MDifferentiableAt J I alpha q :=
    ((halpha q hq).contMDiffAt (hUopen.mem_nhds hq)).mdifferentiableAt (by norm_num)
  have hsplit := mfderiv_prod_eq_add_apply
    (I := 𝓘(Real, P)) (I' := 𝓘(Real, Real)) (I'' := I)
    (f := alpha) (p := q) (v := ((0 : P), (1 : Real))) hdiff
  have hzero :
      mfderiv 𝓘(Real, P) I (fun z : P ↦ alpha (z, q.2)) q.1 (0 : P) = 0 :=
    (mfderiv 𝓘(Real, P) I (fun z : P ↦ alpha (z, q.2)) q.1).map_zero
  change TotalSpace.mk' E (E := TangentSpace I) (alpha q)
      (lVelocity (I := I) (fun s ↦ alpha (q.1, s)) q.2) =
    tangentMapWithin J I alpha U
      (TotalSpace.mk' (P × Real) q ((0 : P), (1 : Real)))
  simp only [tangentMapWithin, hwithin]
  refine TotalSpace.ext rfl ?_
  exact heq_of_eq (by
    simpa only [lVelocity, hzero, zero_add] using hsplit.symm)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem contDiffOn_lRegularizedLagrangian_family_two
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) {alpha : P × Real → M} {V : Set P} {K : Set Real}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn
      (𝓘(Real, P).prod 𝓘(Real, Real)) I 8 alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular) :
    ContDiffOn Real 2
      (fun q : P × Real ↦ lRegularizedLagrangian S T (fun s ↦ alpha (q.1, s)) q.2)
      (V ×ˢ K) := by
  let J := 𝓘(Real, P).prod 𝓘(Real, Real)
  intro q hq
  have hopen : IsOpen (V ×ˢ K) := hVopen.prod hKopen
  have hF : ContMDiffAt J I 2 alpha q :=
    ((halpha q hq).contMDiffAt (hopen.mem_nhds hq)).of_le (by norm_num)
  have harg : ContMDiffAt J (𝓘(Real, Real).prod I) 2
      (fun p : P × Real ↦ (T - p.2 ^ 2, alpha p)) q :=
    (contMDiffAt_const.sub (contMDiffAt_snd.pow 2)).prodMk hF
  have h2inf : (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat) :=
    WithTop.coe_le_coe.mpr le_top
  have hmetric₀ := hS.smoothMetric.metricCLMSmoothAt
    (t := T - q.2 ^ 2) (x := alpha q)
    (D.regular_isOpen.mem_nhds (hreg q hq))
  have hmetric : ContMDiffAt J
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) 2
      (fun p ↦ TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun y ↦ TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
        (alpha p) ((S.base.metric (T - p.2 ^ 2)).inner (alpha p))) q := by
    have hc := (hmetric₀.of_le h2inf).comp q harg
    change ContMDiffAt J
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) 2
      (fun p ↦ TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun y ↦ TangentSpace I y →L[Real]
          TangentSpace I y →L[Real] Real)
        (alpha p) ((S.base.metric (T - p.2 ^ 2)).inner (alpha p))) q at hc
    exact hc
  have hvel := (contMDiffOn_lVelocity_family_two hVopen hKopen halpha q hq).contMDiffAt
    (hopen.mem_nhds hq)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := TangentSpace I) (E₂ := TangentSpace I)
    (E₃ := fun _ : M ↦ Real) hmetric hvel hvel
  rw [Bundle.contMDiffAt_totalSpace] at htotal
  have hscalar₀ : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
      (fun p : Real × M ↦ S.scalar p.1 p.2) (T - q.2 ^ 2, alpha q) :=
    ((scalar_joint (I := I) S hS).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds (hreg q hq)) Filter.univ_mem)).of_le h2inf
  have hscalar : ContMDiffAt J 𝓘(Real, Real) 2
      (fun p ↦ S.scalar (T - p.2 ^ 2) (alpha p)) q := hscalar₀.comp q harg
  have hlag : ContMDiffAt J 𝓘(Real, Real) 2
      (fun p : P × Real ↦
        (1 / 2 : Real) *
            (S.base.metric (T - p.2 ^ 2)).inner (alpha p)
              (lVelocity (I := I) (fun s ↦ alpha (p.1, s)) p.2)
              (lVelocity (I := I) (fun s ↦ alpha (p.1, s)) p.2) +
          2 * p.2 ^ 2 * S.scalar (T - p.2 ^ 2) (alpha p)) q :=
    (contMDiffAt_const.mul htotal.2).add
      ((contMDiffAt_const.mul (contMDiffAt_snd.pow 2)).mul hscalar)
  have hlag' : ContDiffAt Real 2
      (fun p : P × Real ↦ lRegularizedLagrangian S T (fun s ↦ alpha (p.1, s)) p.2) q := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    simpa only [J, lRegularizedLagrangian] using hlag
  exact hlag'.contDiffWithinAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- The regularized action of a jointly `C⁸` family is jointly `C²` in its
parameter and upper integration endpoint on any open connected regular clock
window. The integral is oriented, so the statement also includes endpoints below
`a` and the diagonal endpoint `a` itself. -/
theorem contDiffOn_lRegularizedAction_joint
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a : Real) {alpha : P × Real → M} {V : Set P} {K : Set Real}
    (hVopen : IsOpen V) (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (haK : a ∈ K)
    (halpha : ContMDiffOn
      (𝓘(Real, P).prod 𝓘(Real, Real)) I 8 alpha (V ×ˢ K))
    (hreg : ∀ r ∈ K, T - r ^ 2 ∈ D.regular) :
    ContDiffOn Real 2
      (fun p : P × Real ↦ lRegularizedAction S T (fun r ↦ alpha (p.1, r)) a p.2)
      (V ×ˢ K) := by
  let U : Set (P × Real) := V ×ˢ K
  let Q : (P × Real) × Real → P × Real :=
    fun q ↦ (q.1.1, a + (q.1.2 - a) * q.2)
  let Ω : Set ((P × Real) × Real) := Q ⁻¹' (V ×ˢ K)
  let G : (P × Real) × Real → Real := fun q ↦
    (q.1.2 - a) *
      lRegularizedLagrangian S T (fun r ↦ alpha (q.1.1, r))
        (a + (q.1.2 - a) * q.2)
  have hUopen : IsOpen U := hVopen.prod hKopen
  have hQ : ContDiff Real 2 Q := by
    dsimp only [Q]
    exact (contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_const.add
        (((contDiff_snd.comp contDiff_fst).sub contDiff_const).mul contDiff_snd))
  have hΩopen : IsOpen Ω := (hVopen.prod hKopen).preimage hQ.continuous
  have hsub : U ×ˢ Icc (0 : Real) 1 ⊆ Ω := by
    intro q hq
    refine ⟨hq.1.1, ?_⟩
    have hwK : q.1.2 ∈ K := hq.1.2
    rcases le_total a q.1.2 with haw | hwa
    · apply hKconn.ordConnected.out haK hwK
      have hlo := mul_nonneg (sub_nonneg.mpr haw) hq.2.1
      have hhi := mul_le_mul_of_nonneg_left hq.2.2 (sub_nonneg.mpr haw)
      constructor <;> nlinarith
    · apply hKconn.ordConnected.out hwK haK
      have hlo := mul_nonneg (sub_nonneg.mpr hwa) hq.2.1
      have hhi := mul_le_mul_of_nonneg_left hq.2.2 (sub_nonneg.mpr hwa)
      constructor <;> nlinarith
  have hlag : ContDiffOn Real 2
      (fun q : P × Real ↦ lRegularizedLagrangian S T (fun r ↦ alpha (q.1, r)) q.2)
      (V ×ˢ K) :=
    contDiffOn_lRegularizedLagrangian_family_two S hS T hVopen hKopen halpha
      (fun q hq ↦ hreg q.2 hq.2)
  have hG : ContDiffOn Real 2 G Ω := by
    have hcomp := hlag.comp hQ.contDiffOn (fun _ hq ↦ hq)
    have hlen : ContDiff Real 2
        (fun q : (P × Real) × Real ↦ q.1.2 - a) :=
      (contDiff_snd.comp contDiff_fst).sub contDiff_const
    exact hlen.contDiffOn.mul hcomp
  let : MeasureSpace (Icc (0 : Real) 1) := MeasureTheory.Measure.Subtype.measureSpace
  let : IsFiniteMeasure (volume : Measure (Icc (0 : Real) 1)) := {
    measure_univ_lt_top := by
      rw [MeasureTheory.Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
      exact isCompact_Icc.measure_lt_top }
  have hInt : ContDiffOn Real 2
      (fun p : P × Real ↦ ∫ u : Icc (0 : Real) 1, G (p, u)) U :=
    DifferentialGeometry.Integral.Measure.contDiffOn_integral_subtype_of_isCompact
      2 isCompact_Icc (volume : Measure (Icc (0 : Real) 1)) hUopen hΩopen hsub hG
  apply hInt.congr
  intro p _hp
  rw [integral_subtype measurableSet_Icc (fun u : Real ↦ G (p, u)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  change lRegularizedAction S T (fun r ↦ alpha (p.1, r)) a p.2 =
    ∫ u in (0 : Real)..1, (p.2 - a) *
      lRegularizedLagrangian S T (fun r ↦ alpha (p.1, r)) (a + (p.2 - a) * u)
  simp only [lRegularizedAction]
  have hright : a + (p.2 - a) = p.2 := by ring
  simpa only [intervalIntegral.integral_const_mul, smul_eq_mul,
    mul_zero, add_zero, mul_one, hright] using
    (intervalIntegral.smul_integral_comp_add_mul
      (f := fun r : Real ↦ lRegularizedLagrangian S T (fun s ↦ alpha (p.1, s)) r)
      (a := (0 : Real)) (b := 1) (p.2 - a) a).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman
