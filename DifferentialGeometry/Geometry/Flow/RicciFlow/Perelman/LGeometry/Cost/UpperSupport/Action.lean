import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Parametric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.MinimizingFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PrescribedTangentInOpenSet
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.RadialBump
import DifferentialGeometry.Analysis.Calculus.Derivative.ParametricIntervalIntegral
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

omit [FiniteDimensional Real E] [I.Boundaryless] [T2Space M] in
private theorem contMDiffOn_lVelocity_family
    {alpha : E × Real → M} {V : Set E} {K : Set Real}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K)) :
    ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I.tangent ∞
      (fun q : E × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I)
          (alpha q)
          (lVelocity (I := I) (fun s ↦ alpha (q.1, s)) q.2) :
            TangentBundle I M)) (V ×ˢ K) := by
  let J := 𝓘(Real, E).prod 𝓘(Real, Real)
  let U := V ×ˢ K
  have hUopen : IsOpen U := hVopen.prod hKopen
  have htm :=
    halpha.contMDiffOn_tangentMapWithin (m := ∞) le_rfl hUopen.uniqueMDiffOn
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
  have hcomp : ContMDiffOn J I.tangent ∞
      (fun q : E × Real ↦ tangentMapWithin J I alpha U
        (TotalSpace.mk' (E × Real) q ((0 : E), (1 : Real)))) U :=
    htm.comp (hunit.contMDiffOn (s := U)) (fun _ hq ↦ hq)
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] in
private theorem contDiffOn_lRegularizedLagrangian_family
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) {alpha : E × Real → M} {V : Set E} {K : Set Real}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular) :
    ContDiffOn Real ∞
      (fun q : E × Real ↦ lRegularizedLagrangian S T (fun s ↦ alpha (q.1, s)) q.2)
      (V ×ˢ K) := by
  let J := 𝓘(Real, E).prod 𝓘(Real, Real)
  intro q hq
  have hopen : IsOpen (V ×ˢ K) := hVopen.prod hKopen
  have hF : ContMDiffAt J I ∞ alpha q :=
    (halpha q hq).contMDiffAt (hopen.mem_nhds hq)
  have harg : ContMDiffAt J (𝓘(Real, Real).prod I) ∞
      (fun p : E × Real ↦ (T - p.2 ^ 2, alpha p)) q :=
    (contMDiffAt_const.sub (contMDiffAt_snd.pow 2)).prodMk hF
  have hmetric₀ := hS.smoothMetric.metricCLMSmoothAt
    (t := T - q.2 ^ 2) (x := alpha q)
    (D.regular_isOpen.mem_nhds (hreg q hq))
  have hmetric : ContMDiffAt J
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun y ↦ TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
        (alpha p) ((S.base.metric (T - p.2 ^ 2)).inner (alpha p))) q := by
    have hc := hmetric₀.comp q harg
    change ContMDiffAt J
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun y ↦ TangentSpace I y →L[Real]
          TangentSpace I y →L[Real] Real)
        (alpha p) ((S.base.metric (T - p.2 ^ 2)).inner (alpha p))) q at hc
    exact hc
  have hvel := (contMDiffOn_lVelocity_family hVopen hKopen halpha q hq).contMDiffAt
    (hopen.mem_nhds hq)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := TangentSpace I) (E₂ := TangentSpace I)
    (E₃ := fun _ : M ↦ Real) hmetric hvel hvel
  rw [Bundle.contMDiffAt_totalSpace] at htotal
  have hscalar₀ : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M ↦ S.scalar p.1 p.2) (T - q.2 ^ 2, alpha q) :=
    (scalar_joint (I := I) S hS).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds (hreg q hq)) Filter.univ_mem)
  have hscalar : ContMDiffAt J 𝓘(Real, Real) ∞
      (fun p ↦ S.scalar (T - p.2 ^ 2) (alpha p)) q := hscalar₀.comp q harg
  have hlag : ContMDiffAt J 𝓘(Real, Real) ∞
      (fun p : E × Real ↦
        (1 / 2 : Real) *
            (S.base.metric (T - p.2 ^ 2)).inner (alpha p)
              (lVelocity (I := I) (fun s ↦ alpha (p.1, s)) p.2)
              (lVelocity (I := I) (fun s ↦ alpha (p.1, s)) p.2) +
          2 * p.2 ^ 2 * S.scalar (T - p.2 ^ 2) (alpha p)) q :=
    (contMDiffAt_const.mul htotal.2).add
      ((contMDiffAt_const.mul (contMDiffAt_snd.pow 2)).mul hscalar)
  have hlag' : ContDiffAt Real ∞
      (fun p : E × Real ↦ lRegularizedLagrangian S T (fun s ↦ alpha (p.1, s)) p.2) q := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    simpa only [J, lRegularizedLagrangian] using hlag
  exact hlag'.contDiffWithinAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem hasDerivAt_lRegularizedAction_family_eq_boundary
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (hreg : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular)
    (hEuler : ∀ s ∈ uIcc a b,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f 0)
          (fun r : Real ↦ lVelocity (I := I) (f 0) r) s =
        lRegularizedAccel S T s (f 0 s) (lVelocity (I := I) (f 0) s))
    (hfix : ∀ u : Real, f u a = f 0 a) :
    HasDerivAt (fun u : Real ↦ lRegularizedAction S T (f u) a b)
      ((S.base.metric (T - b ^ 2)).inner (f 0 b)
        (lVelocity (I := I) (fun u : Real ↦ f u b) 0)
        (lVelocity (I := I) (f 0) b)) 0 := by
  have hzero : lVelocity (I := I) (fun u : Real ↦ f u a) 0 = 0 := by
    have heq : (fun u : Real ↦ f u a) = fun _ : Real ↦ f 0 a := by
      funext u
      exact hfix u
    rw [heq]
    rw [lVelocity, mfderiv_const]
    rfl
  have heuler : ∀ s ∈ uIcc a b,
      lRegularizedEulerPair S T (f 0) s
        (lVelocity (I := I) (fun u : Real ↦ f u s) 0) = 0 := by
    intro s hs
    simp only [lRegularizedEulerPair]
    rw [hEuler s hs, sub_self, map_zero]
  have hint : (∫ s in a..b,
      lRegularizedEulerPair S T (f 0) s
        (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) = 0 := by
    calc
      (∫ s in a..b,
          lRegularizedEulerPair S T (f 0) s
            (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) =
          ∫ _s in a..b, (0 : Real) := by
            apply intervalIntegral.integral_congr
            intro s hs
            exact heuler s hs
      _ = 0 := by simp only [intervalIntegral.integral_zero]
  have hfirst := lRegularizedAction_first_variation (I := I) S hS T f hf a b hreg
  simpa only [hzero, map_zero, zero_apply, hint,
    sub_zero] using hfirst

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] in
theorem exists_contDiffOn_lRegularizedAction_family
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (haK : a ∈ K) (hbK : b ∈ K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular) :
    ∃ U : Set E, IsOpen U ∧ A0 ∈ U ∧ U ⊆ V ∧
      ContDiffOn Real ∞
        (fun A : E ↦ lRegularizedAction S T (fun s ↦ alpha (A, s)) a b) U := by
  obtain ⟨rho, lo, hi, hloa, hbhi, hrho, hrhoId, _hrhoDeriv, hrhoK⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset
      hKopen hab (hKconn.ordConnected.out haK hbK)
  obtain ⟨eps, heps, hball⟩ := (Metric.isOpen_iff.mp hVopen) A0 hA0V
  let bump : ContDiffBump (0 : E) :=
    { rIn := eps / 2, rOut := eps, rIn_pos := half_pos heps,
      rIn_lt_rOut := half_lt_self heps }
  let phi : E → E := fun A ↦ A0 + bump.radial (A - A0)
  have hphi : ContDiff Real ∞ phi := contDiff_const.add
    (bump.radial_contDiff.comp (contDiff_id.sub contDiff_const))
  have hphiV : ∀ A, phi A ∈ V := by
    intro A
    apply hball
    have h := bump.radial_mapsTo (Set.mem_univ (A - A0))
    rw [Metric.mem_ball] at h ⊢
    simpa only [phi, dist_eq_norm, add_sub_cancel_left, sub_zero] using h
  let G : E → Real → Real := fun A u ↦
    (b - a) * lRegularizedLagrangian S T (fun s ↦ alpha (phi A, s))
      (rho (a + (b - a) * u))
  have hlag := contDiffOn_lRegularizedLagrangian_family S hS T hVopen hKopen halpha hreg
  have hG : ContDiffOn Real ∞ (fun q : E × Real ↦ G q.1 q.2) univ := by
    intro q _
    have hp := hphi.contDiffAt.comp q contDiffAt_fst
    have haff : ContDiffAt Real ∞
        (fun p : E × Real ↦ a + (b - a) * p.2) q :=
      contDiffAt_const.add (contDiffAt_const.mul contDiffAt_snd)
    have ht : ContDiffAt Real ∞
        (fun p : E × Real ↦ rho (a + (b - a) * p.2)) q :=
      hrho.contDiffAt.comp q haff
    have hpair := hp.prodMk ht
    have hm : (phi q.1, rho (a + (b - a) * q.2)) ∈ V ×ˢ K :=
      ⟨hphiV q.1, hrhoK _⟩
    have hc := (hlag.contDiffAt ((hVopen.prod hKopen).mem_nhds hm)).comp q hpair
    change ContDiffWithinAt Real ∞
      (fun x : E × Real ↦ (b - a) *
        ((fun r : E × Real ↦
          lRegularizedLagrangian S T (fun s ↦ alpha (r.1, s)) r.2) ∘
            fun x ↦ (phi x.1, rho (a + (b - a) * x.2))) x)
      Set.univ q
    exact (contDiffAt_const.mul hc).contDiffWithinAt
  let Aact : E → Real := fun A ↦ ∫ u in (0 : Real)..1, G A u
  have hAact : ContDiffOn Real ∞ Aact univ :=
    DifferentialGeometry.Analysis.Calculus.contDiffOn_paramIntervalIntegral G hG
  let U := Metric.ball A0 (eps / 2)
  refine ⟨U, Metric.isOpen_ball, by simpa [U] using half_pos heps,
    fun A hA ↦ hball (Metric.ball_subset_ball (half_le_self heps.le) hA), ?_⟩
  have heq : Set.EqOn Aact
      (fun A : E ↦ lRegularizedAction S T (fun s ↦ alpha (A, s)) a b) U := by
    intro A hAU
    have hrad : bump.radial (A - A0) = A - A0 := by
      apply bump.radial_eq_self
      rw [Metric.mem_closedBall, dist_zero_right]
      simpa only [U, Metric.mem_ball, dist_eq_norm] using
        (Metric.mem_ball.mp hAU).le
    have hphiA : phi A = A := by rw [show phi A = A0 + bump.radial (A-A0) by rfl, hrad]; abel
    have hclamp : Set.EqOn (fun u : Real ↦ rho (a + (b-a)*u))
        (fun u ↦ a + (b-a)*u) (Icc 0 1) := by
      intro u hu
      apply hrhoId
      constructor <;> nlinarith [hu.1, hu.2, hab, hloa, hbhi]
    change Aact A = _
    rw [show Aact A = ∫ u in (0 : Real)..1, G A u by rfl]
    have hcongr : (∫ u in (0 : Real)..1, G A u) =
        ∫ u in (0 : Real)..1, (b-a) *
          lRegularizedLagrangian S T (fun s ↦ alpha (A,s)) (a+(b-a)*u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc (0 : Real) 1 := by
        simpa only [uIcc_of_le zero_le_one] using hu
      simp only [G, hphiA, hclamp hu']
    rw [hcongr]
    simp only [lRegularizedAction]
    have hright : a + (b - a) = b := by ring
    simpa only [intervalIntegral.integral_const_mul, smul_eq_mul,
      mul_zero, add_zero, mul_one, hright] using
      (intervalIntegral.smul_integral_comp_add_mul
      (f := fun s : Real ↦ lRegularizedLagrangian S T (fun r ↦ alpha (A,r)) s)
      (a := (0 : Real)) (b := 1) (b - a) a)
  exact (hAact.mono (fun _ _ ↦ mem_univ _)).congr fun A hA ↦ (heq hA).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hasFDerivAt_lRegularizedAction_family_endpoint
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (haK : a ∈ K) (hbK : b ∈ K)
    (hstart : ∀ A ∈ V, alpha (A, a) = alpha (A0, a))
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular)
    (hEuler : ∀ s ∈ Icc a b,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A0, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun z : Real ↦ alpha (A0, z)) r) s =
        lRegularizedAccel S T s (alpha (A0, s))
          (lVelocity (I := I) (fun r : Real ↦ alpha (A0, r)) s)) :
    HasFDerivAt
      (fun p : E × Real ↦
        lRegularizedAction S T (fun s ↦ alpha (p.1, s)) a p.2)
      (((((S.base.metric (T - b ^ 2)).inner (alpha (A0, b))
              (lVelocity (I := I) (fun s : Real ↦ alpha (A0, s)) b)).comp
            (mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 :
              E →L[Real] TangentSpace I (alpha (A0, b)))).comp
          (ContinuousLinearMap.fst Real E Real)) +
        (lRegularizedLagrangian S T (fun s : Real ↦ alpha (A0, s)) b) •
          ContinuousLinearMap.snd Real E Real) (A0, b) := by
  obtain ⟨W, hWopen, hA0W, hWV, hactW⟩ :=
    exists_contDiffOn_lRegularizedAction_family S hS T a b hab hVopen hA0V hKopen hKconn
      haK hbK halpha hreg
  obtain ⟨rho, lo, hi, hloa, hbhi, hrho, hrhoId, _hrhoDeriv, hrhoK⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset
      hKopen hab (hKconn.ordConnected.out haK hbK)
  let Act : E × Real → Real := fun p ↦
    lRegularizedAction S T (fun s ↦ alpha (p.1, s)) a p.2
  let U : Set (E × Real) := V ×ˢ Ioo a hi
  have hUopen : IsOpen U := hVopen.prod isOpen_Ioo
  have hpU : (A0, b) ∈ U := ⟨hA0V, hab, hbhi⟩
  let G : (E × Real) → Real → Real := fun p u ↦
    (p.2 - a) * lRegularizedLagrangian S T (fun s ↦ alpha (p.1, s))
      (rho (a + (p.2 - a) * u))
  have hlag := contDiffOn_lRegularizedLagrangian_family S hS T hVopen hKopen halpha hreg
  have h1inf : (↑(1 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat) :=
    WithTop.coe_le_coe.mpr le_top
  have hG : ContDiffOn Real 1
      (fun q : (E × Real) × Real ↦ G q.1 q.2) (U ×ˢ univ) := by
    intro q hq
    have hupper : ContDiffAt Real 1
        (fun r : (E × Real) × Real ↦ r.1.2) q :=
      contDiffAt_snd.comp q contDiffAt_fst
    have hlen : ContDiffAt Real 1
        (fun r : (E × Real) × Real ↦ r.1.2 - a) q :=
      hupper.sub contDiffAt_const
    have haff : ContDiffAt Real 1
        (fun r : (E × Real) × Real ↦ a + (r.1.2 - a) * r.2) q :=
      contDiffAt_const.add (hlen.mul contDiffAt_snd)
    have hrhoAt : ContDiffAt Real 1
        (fun r : (E × Real) × Real ↦
          rho (a + (r.1.2 - a) * r.2)) q :=
      (hrho.of_le h1inf).contDiffAt.comp q haff
    have hfirst : ContDiffAt Real 1
        (fun r : (E × Real) × Real ↦ r.1.1) q :=
      contDiffAt_fst.comp q contDiffAt_fst
    have hpair := hfirst.prodMk hrhoAt
    have hpairMem :
        (q.1.1, rho (a + (q.1.2 - a) * q.2)) ∈ V ×ˢ K :=
      ⟨hq.1.1, hrhoK _⟩
    have hlagAt : ContDiffAt Real 1
        (fun r : E × Real ↦
          lRegularizedLagrangian S T (fun s ↦ alpha (r.1, s)) r.2)
        (q.1.1, rho (a + (q.1.2 - a) * q.2)) :=
      (hlag.contDiffAt ((hVopen.prod hKopen).mem_nhds hpairMem)).of_le h1inf
    have hcomp := hlagAt.comp q hpair
    change ContDiffWithinAt Real 1
      (fun x : (E × Real) × Real ↦ (x.1.2 - a) *
        ((fun r : E × Real ↦
          lRegularizedLagrangian S T (fun s ↦ alpha (r.1, s)) r.2) ∘
            fun x ↦ (x.1.1, rho (a + (x.1.2 - a) * x.2))) x)
      (U ×ˢ Set.univ) q
    exact (hlen.mul hcomp).contDiffWithinAt
  have hInt :=
    DifferentialGeometry.Analysis.Calculus.hasFDerivAt_paramInt
      G U hUopen 0 1 univ isOpen_univ
      (by simp only [uIcc_of_le zero_le_one, subset_univ])
      (A0, b) hpU hG
  have hEq : Act =ᶠ[nhds (A0, b)]
      fun p : E × Real ↦ ∫ u in (0 : Real)..1, G p u := by
    filter_upwards [hUopen.mem_nhds hpU] with p hp
    have hpa : 0 < p.2 - a := sub_pos.mpr hp.2.1
    have hclamp : Set.EqOn
        (fun u : Real ↦ rho (a + (p.2 - a) * u))
        (fun u : Real ↦ a + (p.2 - a) * u) (Icc 0 1) := by
      intro u hu
      apply hrhoId
      constructor
      · nlinarith [hu.1, hpa, hloa]
      · nlinarith [hu.2, hpa, hp.2.2]
    have hcongr : (∫ u in (0 : Real)..1, G p u) =
        ∫ u in (0 : Real)..1, (p.2 - a) *
          lRegularizedLagrangian S T (fun s ↦ alpha (p.1, s))
            (a + (p.2 - a) * u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc (0 : Real) 1 := by
        simpa only [uIcc_of_le zero_le_one] using hu
      simp only [G, hclamp hu']
    change lRegularizedAction S T (fun s ↦ alpha (p.1, s)) a p.2 = _
    rw [hcongr]
    simp only [lRegularizedAction]
    have hright : a + (p.2 - a) = p.2 := by ring
    simpa only [intervalIntegral.integral_const_mul, smul_eq_mul,
      mul_zero, add_zero, mul_one, hright] using
      (intervalIntegral.smul_integral_comp_add_mul
        (f := fun s : Real ↦ lRegularizedLagrangian S T (fun r ↦ alpha (p.1, r)) s)
        (a := (0 : Real)) (b := 1) (p.2 - a) a).symm
  have hActDiff : DifferentiableAt Real Act (A0, b) :=
    (hInt.congr_of_eventuallyEq hEq).differentiableAt
  let endMap : E → M := fun A ↦ alpha (A, b)
  let Asp : E → Real := fun A ↦
    lRegularizedAction S T (fun s ↦ alpha (A, s)) a b
  let Lsp : E →L[Real] Real :=
    ((S.base.metric (T - b ^ 2)).inner (alpha (A0, b))
      (lVelocity (I := I) (fun s : Real ↦ alpha (A0, s)) b)).comp
        (mfderiv 𝓘(Real, E) I endMap A0)
  have hAspAt : ContDiffAt Real ∞ Asp A0 :=
    (hactW A0 hA0W).contDiffAt (hWopen.mem_nhds hA0W)
  have hAspDiff : DifferentiableAt Real Asp A0 :=
    hAspAt.differentiableAt (by simp)
  have hAspBase : HasFDerivAt Asp (fderiv Real Asp A0) A0 :=
    hAspDiff.hasFDerivAt
  have hseg : Icc a b ⊆ K :=
    hKconn.ordConnected.out haK hbK
  let gamma : Real → M := fun s ↦ alpha (A0, s)
  have hgammaData : ∀ s ∈ Icc a b,
      T - s ^ 2 ∈ D.regular ∧
        MDifferentiableAt 𝓘(Real, Real) I gamma s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) gamma
            (fun r : Real ↦ lVelocity (I := I) gamma r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
            (fun r : Real ↦ lVelocity (I := I) gamma r) s =
          lRegularizedAccel S T s (gamma s) (lVelocity (I := I) gamma s) := by
    intro s hs
    have hsK : s ∈ K := hseg hs
    have halphaAt : ContMDiffAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (A0, s) :=
      (halpha (A0, s) ⟨hA0V, hsK⟩).contMDiffAt
        ((hVopen.prod hKopen).mem_nhds ⟨hA0V, hsK⟩)
    have hincl : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun r : Real ↦ (A0, r)) s :=
      contMDiffAt_const.prodMk contMDiffAt_id
    have hgammaInf : ContMDiffAt 𝓘(Real, Real) I ∞ gamma s := by
      change ContMDiffAt 𝓘(Real, Real) I ∞
        (alpha ∘ fun r : Real ↦ (A0, r)) s
      exact halphaAt.comp s hincl
    have hgamma2 : ContMDiffAt 𝓘(Real, Real) I 2 gamma s :=
      hgammaInf.of_le (by
        change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
        exact WithTop.coe_le_coe.mpr le_top)
    refine ⟨hreg (A0, s) ⟨hA0V, hsK⟩,
      hgammaInf.mdifferentiableAt (by simp), ?_, ?_⟩
    · change DifferentiableAt Real
        (fun u ↦ (trivializationAt E (TangentSpace I) (gamma s)).continuousLinearMapAt
          Real (gamma u) (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))) s
      exact
        DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.velocity_coord_diff
          (I := I) gamma s hgamma2
    · simpa only [gamma] using hEuler s hs
  have hAspEq : fderiv Real Asp A0 = Lsp := by
    apply ContinuousLinearMap.ext
    intro Y
    obtain ⟨zeta, hzeta, hzetaW, hzeta0, hzetaVelocity⟩ :=
      exists_smooth_curve (I := 𝓘(Real, E)) (M := E)
        A0 Y W hWopen hA0W
    have h8inf : (↑(8 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat) :=
      WithTop.coe_le_coe.mpr le_top
    have hrhoM : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ rho :=
      contMDiff_iff_contDiff.mpr hrho
    let f : Real → Real → M := fun u s ↦ alpha (zeta u, rho s)
    have hpair : ContMDiff
        (𝓘(Real, Real).prod 𝓘(Real, Real))
        (𝓘(Real, E).prod 𝓘(Real, Real)) (8 : Nat)
        (fun p : Real × Real ↦ (zeta p.1, rho p.2)) :=
      ((hzeta.of_le h8inf).comp contMDiff_fst).prodMk
        ((hrhoM.of_le h8inf).comp contMDiff_snd)
    have hpairVK : ∀ p : Real × Real,
        (zeta p.1, rho p.2) ∈ V ×ˢ K :=
      fun p ↦ ⟨hWV (hzetaW p.1), hrhoK p.2⟩
    have hf : IsSmoothVariation (I := I) f := by
      unfold IsSmoothVariation
      rw [← contMDiffOn_univ]
      change ContMDiffOn
        (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
        (alpha ∘ fun p : Real × Real ↦ (zeta p.1, rho p.2)) Set.univ
      exact (halpha.of_le h8inf).comp hpair.contMDiffOn
        (fun p _hp ↦ hpairVK p)
    have haWide : a ∈ Icc lo hi :=
      ⟨hloa.le, (hab.trans hbhi).le⟩
    have hbWide : b ∈ Icc lo hi :=
      ⟨(hloa.trans hab).le, hbhi.le⟩
    have hrhoa : rho a = a := by
      simpa only [id_eq] using hrhoId haWide
    have hrhob : rho b = b := by
      simpa only [id_eq] using hrhoId hbWide
    have hfix : ∀ u : Real, f u a = f 0 a := by
      intro u
      change alpha (zeta u, rho a) = alpha (zeta 0, rho a)
      rw [hrhoa, hzeta0]
      exact hstart (zeta u) (hWV (hzetaW u))
    have hfData : ∀ s ∈ uIcc a b,
        T - s ^ 2 ∈ D.regular ∧
          MDifferentiableAt 𝓘(Real, Real) I (f 0) s ∧
          DifferentiableAt Real
            (chartRepAt (I := I) (f 0)
              (fun r : Real ↦ lVelocity (I := I) (f 0) r) s) s ∧
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f 0)
              (fun r : Real ↦ lVelocity (I := I) (f 0) r) s =
            lRegularizedAccel S T s (f 0 s) (lVelocity (I := I) (f 0) s) := by
      intro s hs
      have hsI : s ∈ Icc a b := by
        simpa only [uIcc_of_le hab.le] using hs
      have hsWide : s ∈ Ioo lo hi :=
        ⟨hloa.trans_le hsI.1, hsI.2.trans_lt hbhi⟩
      have heq : (f 0) =ᶠ[nhds s] gamma := by
        filter_upwards [isOpen_Ioo.mem_nhds hsWide] with r hr
        change alpha (zeta 0, rho r) = alpha (A0, r)
        rw [hzeta0]
        simpa only [id_eq] using congrArg (fun q ↦ alpha (A0, q))
          (hrhoId ⟨hr.1.le, hr.2.le⟩)
      exact lRegularizedData_congr S T s heq (hgammaData s hsI)
    have hfRegularity : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular :=
      fun s hs ↦ (hfData s hs).1
    have hfEuler : ∀ s ∈ uIcc a b,
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f 0)
            (fun r : Real ↦ lVelocity (I := I) (f 0) r) s =
          lRegularizedAccel S T s (f 0 s) (lVelocity (I := I) (f 0) s) :=
      fun s hs ↦ (hfData s hs).2.2.2
    have hfu : ∀ u : Real, Set.EqOn (f u)
        (fun s : Real ↦ alpha (zeta u, s)) (Icc a b) := by
      intro u s hs
      change alpha (zeta u, rho s) = alpha (zeta u, s)
      exact congrArg (fun q ↦ alpha (zeta u, q))
        (by simpa only [id_eq] using
          (hrhoId ⟨hloa.le.trans hs.1, hs.2.trans hbhi.le⟩))
    have hact : (fun u : Real ↦ lRegularizedAction S T (f u) a b) =
        fun u : Real ↦ Asp (zeta u) := by
      funext u
      have heq := lRegularizedAction_congr (I := I) S T (f u)
        (fun s : Real ↦ alpha (zeta u, s)) a b (by
          intro s hs
          apply hfu u
          simpa only [uIcc_of_le hab.le] using
            Set.uIoo_subset_uIcc_self hs)
      simpa only [Asp] using heq
    have hend : (fun u : Real ↦ f u b) =
        fun u : Real ↦ endMap (zeta u) := by
      funext u
      change alpha (zeta u, rho b) = alpha (zeta u, b)
      rw [hrhob]
    have hcentVelocity : lVelocity (I := I) (f 0) b =
        lVelocity (I := I) gamma b := by
      have heq : (f 0) =ᶠ[nhds b] gamma := by
        filter_upwards
            [isOpen_Ioo.mem_nhds ⟨hloa.trans hab, hbhi⟩] with s hs
        change alpha (zeta 0, rho s) = alpha (A0, s)
        rw [hzeta0]
        simpa only [id_eq] using congrArg (fun q ↦ alpha (A0, q))
          (hrhoId ⟨hs.1.le, hs.2.le⟩)
      unfold lVelocity
      rw [heq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
      rfl
    have hendAt : ContMDiffAt 𝓘(Real, E) I ∞ endMap A0 := by
      have halphaAt : ContMDiffAt
          (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (A0, b) :=
        (halpha (A0, b) ⟨hA0V, hbK⟩).contMDiffAt
          ((hVopen.prod hKopen).mem_nhds ⟨hA0V, hbK⟩)
      have hincl : ContMDiffAt 𝓘(Real, E)
          (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
          (fun A : E ↦ (A, b)) A0 :=
        contMDiffAt_id.prodMk contMDiffAt_const
      change ContMDiffAt 𝓘(Real, E) I ∞
        (alpha ∘ fun A : E ↦ (A, b)) A0
      exact halphaAt.comp A0 hincl
    have hzetaMD : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) zeta 0 :=
      hzeta.contMDiffAt.mdifferentiableAt (by norm_num)
    have hendMD : MDifferentiableAt 𝓘(Real, E) I endMap A0 :=
      hendAt.mdifferentiableAt (by simp)
    have hendMD0 : MDifferentiableAt 𝓘(Real, E) I endMap (zeta 0) := by
      simpa only [hzeta0] using hendMD
    have hcompMF := hendMD0.hasMFDerivAt.comp 0 hzetaMD.hasMFDerivAt
    have hendVelocity : lVelocity (I := I) (fun u : Real ↦ f u b) 0 =
        mfderiv 𝓘(Real, E) I endMap A0 Y := by
      unfold lVelocity
      rw [hend]
      change (mfderiv 𝓘(Real, Real) I (endMap ∘ zeta) 0) (1 : Real) =
        mfderiv 𝓘(Real, E) I endMap A0 Y
      rw [hcompMF.mfderiv]
      change mfderiv 𝓘(Real, E) I endMap (zeta 0)
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E) zeta 0 (1 : Real)) =
        mfderiv 𝓘(Real, E) I endMap A0 Y
      rw [hzetaVelocity, hzeta0]
    have hbdry := hasDerivAt_lRegularizedAction_family_eq_boundary
      S hS T f hf a b hfRegularity hfEuler hfix
    have hfb : f 0 b = alpha (A0, b) := by
      change alpha (zeta 0, rho b) = alpha (A0, b)
      rw [hrhob, hzeta0]
    rw [hfb] at hbdry
    have hbdry' : HasDerivAt (fun u : Real ↦ Asp (zeta u))
        ((S.base.metric (T - b ^ 2)).inner (alpha (A0, b))
          (mfderiv 𝓘(Real, E) I endMap A0 Y)
          (lVelocity (I := I) gamma b)) 0 := by
      rw [← hact]
      simpa only [hendVelocity, hcentVelocity, gamma, endMap] using hbdry
    have hzetaF := hzetaMD.hasMFDerivAt.hasFDerivAt
    have hAsp0 : HasFDerivAt Asp (fderiv Real Asp A0) (zeta 0) := by
      simpa only [hzeta0] using hAspBase
    have hlineF := hAsp0.comp 0 hzetaF
    have hline : HasDerivAt (fun u : Real ↦ Asp (zeta u))
        (fderiv Real Asp A0 Y) 0 := by
      have hraw := hlineF.hasDerivAt
      change HasDerivAt (Asp ∘ zeta) (fderiv Real Asp A0 Y) 0
      apply hraw.congr_deriv
      change fderiv Real Asp A0
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E) zeta 0 (1 : Real)) =
          fderiv Real Asp A0 Y
      rw [hzetaVelocity]
    have hval := hline.unique hbdry'
    calc
      fderiv Real Asp A0 Y =
          (S.base.metric (T - b ^ 2)).inner (alpha (A0, b))
            (mfderiv 𝓘(Real, E) I endMap A0 Y)
            (lVelocity (I := I) gamma b) := hval
      _ = (S.base.metric (T - b ^ 2)).inner (alpha (A0, b))
          (lVelocity (I := I) gamma b)
          (mfderiv 𝓘(Real, E) I endMap A0 Y) :=
        (S.base.metric (T - b ^ 2)).symm (alpha (A0, b)) _ _
      _ = Lsp Y := by rfl
  have hAspGiven : HasFDerivAt Asp Lsp A0 := by
    rw [← hAspEq]
    exact hAspBase
  have hbase : HasFDerivAt Act (fderiv Real Act (A0, b)) (A0, b) :=
    hActDiff.hasFDerivAt
  have hins : HasFDerivAt (fun A : E ↦ (A, b))
      ((1 : E →L[Real] E).prod (0 : E →L[Real] Real)) A0 :=
    hasFDerivAt_prodMk_left A0 b
  have hspaceSlice := hbase.comp A0 hins
  have hspace : HasFDerivAt (fun A : E ↦ Act (A, b)) Lsp A0 := by
    simpa only [Act, Asp] using hAspGiven
  have hspaceEq := hspaceSlice.unique hspace
  let lag : Real → Real := fun s ↦
    lRegularizedLagrangian S T (fun r ↦ alpha (A0, r)) s
  have hlagK : ContinuousOn lag K := by
    have hcomp := hlag.continuousOn.comp
      (continuousOn_const.prodMk continuousOn_id)
      (fun s hs ↦ ⟨hA0V, hs⟩)
    change ContinuousOn
      ((fun q : E × Real ↦
        lRegularizedLagrangian S T (fun s ↦ alpha (q.1, s)) q.2) ∘
          fun s : Real ↦ (A0, id s)) K
    exact hcomp
  have hlagI : ContinuousOn lag (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using hlagK.mono hseg
  have hupper : HasDerivAt
      (fun r : Real ↦ ∫ s in a..r, lag s) (lag b) b :=
    intervalIntegral.integral_hasDerivAt_right
      hlagI.intervalIntegrable
      (hlagK.stronglyMeasurableAtFilter hKopen b hbK)
      (hlagK.continuousAt (hKopen.mem_nhds hbK))
  have htime : HasDerivAt (fun r : Real ↦ Act (A0, r)) (lag b) b := by
    simpa only [Act, lRegularizedAction, lag] using hupper
  have htins : HasFDerivAt (fun r : Real ↦ (A0, r))
      (ContinuousLinearMap.inr Real E Real) b :=
    hasFDerivAt_prodMk_right A0 b
  have htimeSlice := (hbase.comp b htins).hasDerivAt
  have htimeEq := htimeSlice.unique htime
  have hfd : fderiv Real Act (A0, b) =
      Lsp.comp (ContinuousLinearMap.fst Real E Real) +
        (lag b) • ContinuousLinearMap.snd Real E Real := by
    apply ContinuousLinearMap.ext
    intro p
    have hspaceVal := congrArg (fun L : E →L[Real] Real ↦ L p.1) hspaceEq
    have hspace0 : fderiv Real Act (A0, b) (p.1, 0) = Lsp p.1 := by
      simpa [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.prod_apply] using hspaceVal
    have htimeVal : fderiv Real Act (A0, b) (0, (1 : Real)) = lag b := by
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply] using htimeEq
    calc
      fderiv Real Act (A0, b) p =
          fderiv Real Act (A0, b) (p.1, 0) +
            fderiv Real Act (A0, b) (0, p.2) := by
        rw [← map_add]
        congr 1
        ext <;> simp
      _ = Lsp p.1 + p.2 * lag b := by
        rw [show (0, p.2) = p.2 • ((0 : E), (1 : Real)) by
          ext <;> simp, map_smul, htimeVal, hspace0]
        simp only [smul_eq_mul]
      _ = (Lsp.comp (ContinuousLinearMap.fst Real E Real) +
          (lag b) • ContinuousLinearMap.snd Real E Real) p := by
        change Lsp p.1 + p.2 * lag b = Lsp p.1 + lag b * p.2
        ring
  have hfinal : HasFDerivAt Act
      (Lsp.comp (ContinuousLinearMap.fst Real E Real) +
        (lag b) • ContinuousLinearMap.snd Real E Real) (A0, b) := by
    rw [← hfd]
    exact hbase
  change HasFDerivAt Act
    (Lsp.comp (ContinuousLinearMap.fst Real E Real) +
      (lag b) • ContinuousLinearMap.snd Real E Real) (A0, b)
  exact hfinal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hasMFDerivAt_lRegularizedAction_endpointBranch
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (haK : a ∈ K) (hbK : b ∈ K)
    (hstart : ∀ A ∈ V, alpha (A, a) = alpha (A0, a))
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular)
    (hEuler : ∀ s ∈ Icc a b,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A0, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun z : Real ↦ alpha (A0, z)) r) s =
        lRegularizedAccel S T s (alpha (A0, s))
          (lVelocity (I := I) (fun r : Real ↦ alpha (A0, r)) s))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B) :
    let hloc := Coordinates.isLocalDiffeomorphAt_parameter_graph_of_slice_mfderiv_injective hVopen hA0V hKopen hbK halpha hinj
    HasMFDerivAt (I.prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (fun q : M × Real ↦
        lRegularizedAction S T
          (fun s : Real ↦ alpha ((hloc.localInverse q).1, s))
          a (hloc.localInverse q).2)
      (alpha (A0, b), b)
      (((S.base.metric (T - b ^ 2)).inner (alpha (A0, b))
            (lVelocity (I := I) (fun s : Real ↦ alpha (A0, s)) b)).comp
          (ContinuousLinearMap.fst Real E Real) +
        (lRegularizedLagrangian S T (fun s : Real ↦ alpha (A0, s)) b -
          (S.base.metric (T - b ^ 2)).inner (alpha (A0, b))
            (lVelocity (I := I) (fun s : Real ↦ alpha (A0, s)) b)
            (lVelocity (I := I) (fun s : Real ↦ alpha (A0, s)) b)) •
          ContinuousLinearMap.snd Real E Real) := by
  let J := 𝓘(Real, E).prod 𝓘(Real, Real)
  let L := I.prod 𝓘(Real, Real)
  let F : E × Real → M × Real := fun p ↦ (alpha p, p.2)
  let q0 : M × Real := (alpha (A0, b), b)
  let hloc := Coordinates.isLocalDiffeomorphAt_parameter_graph_of_slice_mfderiv_injective hVopen hA0V hKopen hbK halpha hinj
  let Act : E × Real → Real := fun p ↦
    lRegularizedAction S T (fun s : Real ↦ alpha (p.1, s)) a p.2
  let g := S.base.metric (T - b ^ 2)
  let Ab : TangentSpace I (alpha (A0, b)) :=
    lVelocity (I := I) (fun s : Real ↦ alpha (A0, s)) b
  let Lb : Real := lRegularizedLagrangian S T (fun s : Real ↦ alpha (A0, s)) b
  let endMap : E → M := fun A ↦ alpha (A, b)
  let dAct : E × Real →L[Real] Real :=
    (((g.inner (alpha (A0, b)) Ab).comp
        (mfderiv 𝓘(Real, E) I endMap A0)).comp
      (ContinuousLinearMap.fst Real E Real)) +
      Lb • ContinuousLinearMap.snd Real E Real
  let dBranch : E × Real →L[Real] Real :=
    (g.inner (alpha (A0, b)) Ab).comp
        (ContinuousLinearMap.fst Real E Real) +
      (Lb - g.inner (alpha (A0, b)) Ab Ab) •
        ContinuousLinearMap.snd Real E Real
  have hAct : HasMFDerivAt J 𝓘(Real, Real) Act (A0, b) dAct := by
    change HasMFDerivAt (𝓘(Real, E).prod 𝓘(Real, Real))
      𝓘(Real, Real)
      (fun p : E × Real ↦
        lRegularizedAction S T (fun s ↦ alpha (p.1, s)) a p.2) (A0, b) _
    exact (hasFDerivAt_lRegularizedAction_family_endpoint
      S hS T a b hab hVopen hA0V hKopen hKconn
      haK hbK hstart halpha hreg hEuler).hasMFDerivAt
  have hq0 : hloc.localInverse q0 = (A0, b) := by
    simpa only [hloc, q0, F] using
      hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hInv : MDifferentiableAt L J hloc.localInverse q0 := by
    simpa only [hloc, q0, F] using
      hloc.localInverse_mdifferentiableAt (by simp)
  have hComp : HasMFDerivAt L 𝓘(Real, Real)
      (fun q : M × Real ↦ Act (hloc.localInverse q)) q0
      (dAct.comp (mfderiv L J hloc.localInverse q0)) := by
    have hAct' : HasMFDerivAt J 𝓘(Real, Real)
        Act (hloc.localInverse q0) dAct := by
      rw [hq0]
      exact hAct
    change HasMFDerivAt L 𝓘(Real, Real)
      (Act ∘ hloc.localInverse) q0
      (dAct.comp (mfderiv L J hloc.localInverse q0))
    exact hAct'.comp q0 hInv.hasMFDerivAt
  have hdBranch :
      dAct.comp (mfderiv L J hloc.localInverse q0) = dBranch := by
    apply ContinuousLinearMap.ext
    intro w
    let v : E × Real := mfderiv L J hloc.localInverse q0 w
    have hright : mfderiv J L F (A0, b) v = w := by
      have hright' :=
        (hloc.mfderivToContinuousLinearEquiv (by simp)).right_inv w
      change mfderiv J L F (A0, b)
        (mfderiv L J hloc.localInverse q0 w) = w at hright'
      exact hright'
    have halphaDiff : MDifferentiableAt J I alpha (A0, b) :=
      ((halpha (A0, b) ⟨hA0V, hbK⟩).contMDiffAt
        ((hVopen.prod hKopen).mem_nhds ⟨hA0V, hbK⟩)).mdifferentiableAt
          (by simp)
    have hsndDiff : MDifferentiableAt J 𝓘(Real, Real)
        (@Prod.snd E Real) (A0, b) := by
      simpa only [J] using
        (mdifferentiableAt_snd : MDifferentiableAt J 𝓘(Real, Real)
          (@Prod.snd E Real) (A0, b))
    have hFderiv : mfderiv J L F (A0, b) =
        (mfderiv J I alpha (A0, b)).prod
          (mfderiv J 𝓘(Real, Real) (@Prod.snd E Real) (A0, b)) := by
      simpa only [F] using mfderiv_prodMk halphaDiff hsndDiff
    have hsndDeriv :=
      (mfderiv_snd : mfderiv
        (𝓘(Real, E).prod 𝓘(Real, Real)) 𝓘(Real, Real)
        (@Prod.snd E Real) (A0, b) =
          ContinuousLinearMap.snd Real
            (TangentSpace 𝓘(Real, E) A0)
            (TangentSpace 𝓘(Real, Real) b))
    rw [hFderiv, hsndDeriv] at hright
    change (mfderiv J I alpha (A0, b) v, v.2) = w at hright
    have halphaVal : mfderiv J I alpha (A0, b) v = w.1 :=
      congrArg Prod.fst hright
    have hv2raw := congrArg Prod.snd hright
    have hv2 : v.2 = w.2 := hv2raw
    have hsplit := mfderiv_prod_eq_add_apply halphaDiff (v := v)
    have htime :
        mfderiv 𝓘(Real, Real) I (fun r : Real ↦ alpha (A0, r)) b v.2 =
          v.2 • Ab := by
      let e := NormedSpace.fromTangentSpace (𝕜 := Real) b
      let v₂ : TangentSpace 𝓘(Real, Real) b := e.symm v.2
      let one₂ : TangentSpace 𝓘(Real, Real) b := e.symm 1
      have hv₂ : v₂ = v.2 • one₂ := by
        apply e.injective
        simp only [v₂, one₂, map_smul, ContinuousLinearEquiv.apply_symm_apply,
          smul_eq_mul, mul_one]
      have hraw := map_smul
        (mfderiv 𝓘(Real, Real) I
          (fun r : Real ↦ alpha (A0, r)) b) v.2 one₂
      rw [← hv₂] at hraw
      change mfderiv 𝓘(Real, Real) I
          (fun r : Real ↦ alpha (A0, r)) b
            (show TangentSpace 𝓘(Real, Real) b from v.2) =
        v.2 • mfderiv 𝓘(Real, Real) I
          (fun r : Real ↦ alpha (A0, r)) b
            (show TangentSpace 𝓘(Real, Real) b from (1 : Real)) at hraw
      change mfderiv 𝓘(Real, Real) I
          (fun r : Real ↦ alpha (A0, r)) b
            (show TangentSpace 𝓘(Real, Real) b from v.2) =
        v.2 • mfderiv 𝓘(Real, Real) I
          (fun r : Real ↦ alpha (A0, r)) b
            (show TangentSpace 𝓘(Real, Real) b from (1 : Real))
      exact hraw
    have hsum :
        mfderiv 𝓘(Real, E) I endMap A0 v.1 + v.2 • Ab = w.1 := by
      rw [← htime]
      change mfderiv 𝓘(Real, E) I
          (fun A : E ↦ alpha (A, b)) A0 v.1 +
        mfderiv 𝓘(Real, Real) I
          (fun r : Real ↦ alpha (A0, r)) b v.2 = w.1
      exact hsplit.symm.trans halphaVal
    have hinner := congrArg (g.inner (alpha (A0, b)) Ab) hsum
    have hspaceInner :
        g.inner (alpha (A0, b)) Ab
            (mfderiv 𝓘(Real, E) I endMap A0 v.1) =
          g.inner (alpha (A0, b)) Ab w.1 -
            v.2 * g.inner (alpha (A0, b)) Ab Ab := by
      apply (eq_sub_iff_add_eq).2
      simpa only [map_add, map_smul, smul_eq_mul] using hinner
    change g.inner (alpha (A0, b)) Ab
          (mfderiv 𝓘(Real, E) I endMap A0 v.1) + Lb * v.2 =
        g.inner (alpha (A0, b)) Ab w.1 +
          (Lb - g.inner (alpha (A0, b)) Ab Ab) * w.2
    rw [hspaceInner, hv2]
    ring
  rw [hdBranch] at hComp
  simpa only [J, L, Act, q0, hloc, dBranch, g, Ab, Lb] using hComp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiffOn_lRegularizedAction_endpointBranch
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (haK : a ∈ K) (hbK : b ∈ K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular)
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B) :
    ∃ U : Set M, IsOpen U ∧ alpha (A0, b) ∈ U ∧
      ∃ F : M → Real,
        ContMDiffOn I 𝓘(Real, Real) ∞ F U ∧
        ∀ y ∈ U, F y = lRegularizedAction S T
          (fun s ↦ alpha
            ((Coordinates.isLocalDiffeomorphAt_slice_of_mfderiv_injective hVopen hA0V hbK halpha hinj).localInverse y, s))
          a b := by
  obtain ⟨W, hWopen, hA0W, hWV, hact⟩ :=
    exists_contDiffOn_lRegularizedAction_family
      S hS T a b hab hVopen hA0V hKopen hKconn
      haK hbK halpha hreg
  let hloc := Coordinates.isLocalDiffeomorphAt_slice_of_mfderiv_injective hVopen hA0V hbK halpha hinj
  let U : Set M := hloc.localInverse.source ∩ hloc.localInverse ⁻¹' W
  have hUopen : IsOpen U :=
    hloc.localInverse_contMDiffOn.continuousOn.isOpen_inter_preimage
      hloc.localInverse_open_source hWopen
  have hinv : hloc.localInverse (alpha (A0, b)) = A0 :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hyU : alpha (A0, b) ∈ U := by
    refine ⟨hloc.localInverse_mem_source, ?_⟩
    change hloc.localInverse (alpha (A0, b)) ∈ W
    rw [hinv]
    exact hA0W
  let F : M → Real := fun y ↦ lRegularizedAction S T
    (fun s ↦ alpha (hloc.localInverse y, s)) a b
  have hactM : ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun A : E ↦ lRegularizedAction S T (fun s ↦ alpha (A, s)) a b) W :=
    contMDiffOn_iff_contDiffOn.mpr hact
  have hinvMD := hloc.localInverse_contMDiffOn.mono
    (inter_subset_left : U ⊆ hloc.localInverse.source)
  have hF : ContMDiffOn I 𝓘(Real, Real) ∞ F U := by
    exact hactM.comp hinvMD (fun _ hy ↦ hy.2)
  refine ⟨U, hUopen, hyU, F, hF, ?_⟩
  intro y _hy
  rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle

universe uM uEM uHM

variable {EM : Type uEM} [NormedAddCommGroup EM]
  [InnerProductSpace Real EM] [FiniteDimensional Real EM]
  [NeZero (Module.finrank Real EM)]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {IM : ModelWithCorners Real EM HM} [IM.Boundaryless]
variable {MM : Type uM} [PseudoMetricSpace MM] [ChartedSpace HM MM]
  [IsManifold IM ∞ MM] [T2Space MM] [SigmaCompactSpace MM]
variable {DM : RealTimeInterval}

omit [NeZero (Module.finrank ℝ EM)] [SigmaCompactSpace MM] in
theorem exists_contMDiffOn_lCost_upper_support
    (S : SolutionOn (I := IM) (M := MM) DM)
    (hS : IsSolutionOn (I := IM) S) (K T : Real) (x : MM)
    {Z : TangentSpace IM x} {tau s0 : Real}
    (hmin : (Z, tau) ∈ lMinDomain (E := EM) (I := IM) S T x)
    (hreg : Icc (T - tau) T ⊆ DM.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : MM,
      normSq0S (I := IM) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (hs00 : 0 < s0) (hs0b : s0 < Real.sqrt tau) :
    ∃ U : Set MM, IsOpen U ∧ lExp S T x Z tau ∈ U ∧
      ∃ F : MM → Real,
        ContMDiffOn IM 𝓘(Real, Real) ∞ F U ∧
          F (lExp S T x Z tau) =
            lCost S T x (lExp S T x Z tau) tau ∧
          ∀ y ∈ U, lCost S T x y tau ≤ F y := by
  let gamma : Real → MM := lRegularizedCurve S T x Z
  let b : Real := Real.sqrt tau
  let x0 : MM := gamma s0
  let A0 : TangentSpace IM x0 := lVelocity (I := IM) gamma s0
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  have hb0 : 0 < b := by
    simpa only [b] using Real.sqrt_pos.2 htau
  have hb2 : b ^ 2 = tau := by
    simpa only [b] using Real.sq_sqrt htau.le
  have hs0b' : s0 < b := by simpa only [b] using hs0b
  obtain ⟨V, hVopen, hA0V, Ktime, hKopen, hKconn, h0K, hs0K,
      hbK, alpha, halpha, hcurves, hinj⟩ :=
    exists_lRegularizedGeodesicFamily_with_injective_endpoint_mfderiv
      (E := EM) (I := IM) S hS K T x hmin hreg hRm
      hs00 hs0b
  have hbdom : b ∈ lRegularizedDomain S T x Z := by
    have hpos : (Z, tau) ∈ lExpPosDom S T x :=
      ((mem_lMinDomain S T x Z tau).1 hmin).1
    simpa only [b] using
      ((mem_lExpPosDom S T x Z tau).1 hpos).2.2
  let J : Set Real := lRegularizedDomain S T x Z
  have hJopen : IsOpen J := by
    simpa only [J] using lRegularizedDomain_isOpen S T x Z
  have hJconn : IsPreconnected J := by
    simpa only [J] using lRegularizedDomain_preconn S T x Z
  have h0J : 0 ∈ J := by
    simpa only [J] using lRegularizedDomain_segment S T x Z hbdom le_rfl hb0.le
  have hs0J : s0 ∈ J := by
    simpa only [J] using
      lRegularizedDomain_segment S T x Z hbdom hs00.le hs0b'.le
  have hbJ : b ∈ J := by simpa only [J] using hbdom
  have hgamma : IsLRegularizedGeodesicOn S T gamma J := by
    intro r hr
    have hrdom : r ∈ lRegularizedDomain S T x Z := by simpa only [J] using hr
    obtain ⟨L, hLopen, hLconn, h0L, hrL, hchosen⟩ :=
      lRegularizedChosen_spec S T x Z hrdom
    have heqOn : Set.EqOn gamma (lRegularizedChosen S T x Z hrdom) L := by
      simpa only [gamma] using
        lRegularizedCurve_eqOn S hS T hLopen hLconn h0L hchosen
    have heq : gamma =ᶠ[nhds r] lRegularizedChosen S T x Z hrdom :=
      heqOn.eventuallyEq_of_mem (hLopen.mem_nhds hrL)
    exact lRegularizedData_congr S T r heq (hchosen.2.2 r hrL)
  have hcenterEq : Set.EqOn (fun r ↦ alpha (A0, r)) gamma
      (Ktime ∩ J) :=
    lRegularizedSolution_eqOn S hS T hKopen hKconn hs0K hJopen hJconn hs0J
      (hcurves A0 hA0V).2.2 hgamma
      (by simpa only [x0] using (hcurves A0 hA0V).1)
      (by simpa only [A0] using (hcurves A0 hA0V).2.1)
  have hsegK : Icc (0 : Real) b ⊆ Ktime :=
    hKconn.ordConnected.out h0K hbK
  have hsegJ : Icc (0 : Real) b ⊆ J :=
    hJconn.ordConnected.out h0J hbJ
  have hcenterEnd : alpha (A0, b) = lExp S T x Z tau := by
    calc
      alpha (A0, b) = gamma b := hcenterEq ⟨hbK, hbJ⟩
      _ = lExp S T x Z tau := by simp only [gamma, b, lExp]
  let hloc := Coordinates.isLocalDiffeomorphAt_slice_of_mfderiv_injective hVopen hA0V hbK halpha hinj
  have hregFamily : ∀ q ∈ V ×ˢ Ktime, T - q.2 ^ 2 ∈ DM.regular := by
    intro q hq
    exact ((hcurves q.1 hq.1).2.2 q.2 hq.2).1
  obtain ⟨U0, hU0open, hzU0, F0, hF0smooth, hF0eq⟩ :=
    exists_contMDiffOn_lRegularizedAction_endpointBranch
      S hS T s0 b hs0b' hVopen hA0V hKopen
      hKconn hs0K hbK halpha hregFamily hinj
  rw [hcenterEnd] at hzU0
  let U : Set MM := U0 ∩
    (hloc.localInverse.source ∩ hloc.localInverse ⁻¹' V)
  have hbranchOpen : IsOpen
      (hloc.localInverse.source ∩ hloc.localInverse ⁻¹' V) :=
    hloc.localInverse_contMDiffOn.continuousOn.isOpen_inter_preimage
      hloc.localInverse_open_source hVopen
  have hUopen : IsOpen U := hU0open.inter hbranchOpen
  have hzSource : lExp S T x Z tau ∈ hloc.localInverse.source := by
    rw [← hcenterEnd]
    exact hloc.localInverse_mem_source
  have hinv0 : hloc.localInverse (lExp S T x Z tau) = A0 := by
    rw [← hcenterEnd]
    exact hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hzU : lExp S T x Z tau ∈ U := by
    refine ⟨hzU0, hzSource, ?_⟩
    change hloc.localInverse (lExp S T x Z tau) ∈ V
    rw [hinv0]
    exact hA0V
  let F : MM → Real := fun y ↦ lRegularizedAction S T gamma 0 s0 + F0 y
  have hFsmooth : ContMDiffOn IM 𝓘(Real, Real) ∞ F U := by
    exact contMDiffOn_const.add
      (hF0smooth.mono fun _ hy ↦ hy.1)
  have hregSq : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ DM.regular := by
    intro s hs
    apply hreg
    rw [← hb2]
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb0.le).2 hs.2
    constructor <;> linarith [sq_nonneg s]
  have hRmSq : ∀ q ∈ Icc (T - b ^ 2) T, ∀ z : MM,
      normSq0S (I := IM) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
    simpa only [hb2] using hRm
  have hgammaC1 : ContMDiffOn 𝓘(Real, Real) IM 1 gamma
      (Icc (0 : Real) b) := by
    simpa only [gamma] using lRegularizedCurve_c1On S hS T x Z hbdom
  have hheadC1 : ContMDiffOn 𝓘(Real, Real) IM 1 gamma
      (Icc (0 : Real) s0) :=
    hgammaC1.mono fun s hs ↦ ⟨hs.1, hs.2.trans hs0b'.le⟩
  have htailC1 : ContMDiffOn 𝓘(Real, Real) IM 1 gamma
      (Icc s0 b) :=
    hgammaC1.mono fun s hs ↦ ⟨hs00.le.trans hs.1, hs.2⟩
  have hheadInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := IM) S hS.smoothMetric
    ⟨hS.scalarCont⟩ T 0 s0 hs00.le gamma hheadC1
    (fun s hs ↦ hregSq s ⟨hs.1, hs.2.trans hs0b'.le⟩)
  have htailInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := IM) S hS.smoothMetric
    ⟨hS.scalarCont⟩ T s0 b hs0b'.le gamma htailC1
    (fun s hs ↦ hregSq s ⟨hs00.le.trans hs.1, hs.2⟩)
  have hactionAdd := lRegularizedAction_add (I := IM) S T gamma 0 s0 b
    hheadInt htailInt
  have htailEq : lRegularizedAction S T (fun r ↦ alpha (A0, r)) s0 b =
      lRegularizedAction S T gamma s0 b := by
    apply lRegularizedAction_congr (I := IM) S T
    intro s hs
    have hs' : s ∈ Ioo s0 b := by
      simpa only [uIoo_of_le hs0b'.le] using hs
    have hsI : s ∈ Icc (0 : Real) b :=
      ⟨hs00.le.trans hs'.1.le, hs'.2.le⟩
    exact hcenterEq ⟨hsegK hsI, hsegJ hsI⟩
  have hfullCost : lRegularizedAction S T gamma 0 b =
      lCost S T x (lExp S T x Z tau) tau := by
    have hvec := (mem_lMinDomain S T x Z tau).1 hmin
    calc
      lRegularizedAction S T gamma 0 b =
          lLength S T (squareRootReparametrization gamma) 0 tau := by
        simpa only [gamma, b] using
          (lLength_squareRootReparametrization_eq_lRegularizedAction (I := IM) S T gamma tau htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau := by
        change lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 tau =
          lCost S T x (lRegularizedCurve S T x Z (Real.sqrt tau)) tau
        exact hvec.2
  have hF0center := hF0eq (lExp S T x Z tau) hzU0
  have hFcenter : F (lExp S T x Z tau) =
      lCost S T x (lExp S T x Z tau) tau := by
    rw [show F (lExp S T x Z tau) =
      lRegularizedAction S T gamma 0 s0 + F0 (lExp S T x Z tau) by rfl,
      hF0center]
    simp only [hinv0]
    rw [htailEq, hactionAdd, hfullCost]
  refine ⟨U, hUopen, hzU, F, hFsmooth, hFcenter, ?_⟩
  intro y hy
  have hy0 : y ∈ U0 := hy.1
  have hySource : y ∈ hloc.localInverse.source := hy.2.1
  have hyV : hloc.localInverse y ∈ V := hy.2.2
  let A : EM := hloc.localInverse y
  let beta : Real → MM := fun s ↦ alpha (A, s)
  have hbetaInf : ContMDiffOn 𝓘(Real, Real) IM ∞ beta
      (Icc s0 b) := by
    have hpair : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, EM).prod 𝓘(Real, Real)) ∞
        (fun s : Real ↦ (A, s)) := contMDiff_const.prodMk contMDiff_id
    apply halpha.comp hpair.contMDiffOn
    intro s hs
    exact ⟨by simpa only [A] using hyV,
      hsegK ⟨hs00.le.trans hs.1, hs.2⟩⟩
  have hbeta : ContMDiffOn 𝓘(Real, Real) IM 1 beta
      (Icc s0 b) := hbetaInf.of_le (by norm_num)
  have hnode : gamma s0 = beta s0 := by
    simpa only [beta, A, x0] using
      ((hcurves (hloc.localInverse y) hyV).1).symm
  have hend : beta b = y := by
    simpa only [beta, A, hloc] using
      hloc.localInverse_right_inv hySource
  have hbdd := lRegularizedCosts_bdd_rm (I := IM) S hS K T 0 b
    (by norm_num) hb0.le (by simpa only [hb2] using hreg) hRmSq x y
  have hle := lCost_le_join_bdd (I := IM) S hS T b hb0 x y
    hs00 hs0b' hbdd hregSq gamma beta hheadC1 hbeta hnode
    (by simpa only [gamma] using lRegularizedCurve_zero S T x Z) hend
  have hF0y := hF0eq y hy0
  change lCost S T x y tau ≤
    lRegularizedAction S T gamma 0 s0 + F0 y
  rw [hF0y]
  simpa only [hloc, A, beta, hb2] using hle

end DifferentialGeometry.PDE.RicciFlow.Perelman
