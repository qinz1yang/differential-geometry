import DifferentialGeometry.Analysis.Calculus.Compactness.ArzelaAscoli
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.H1
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.KineticEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Coercivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.Scalar
import DifferentialGeometry.Geometry.Operator.Family.GramWeakConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Manifold MeasureTheory Set
open scoped ENNReal Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
theorem lAction_subseq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real) (gRef : SmoothRiemannianMetric I M)
    (a b A : Real) (hab : a ≤ b)
    (htime : Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ Set.Icc t0 t1)
    (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Set.Icc a b))
    (hE : ∀ n, IntegrableOn
      (fun s ↦ gRef.inner (alpha n s) (lVelocity (I := I) (alpha n) s)
        (lVelocity (I := I) (alpha n) s)) (Set.Icc a b))
    (hLag : ∀ n, IntervalIntegrable (lRegLagrangian S T (alpha n)) volume a b)
    (hact : ∀ n, lRegAction S T (alpha n) a b ≤ A) :
    ∃ (phi : Nat → Nat) (g : C(Set.Icc a b, M)),
      StrictMono phi ∧
        TendstoUniformly
          (fun n (s : Set.Icc a b) ↦ alpha (phi n) s.1) g atTop := by
  classical
  obtain ⟨c, C, hc, hbudget⟩ :=
    exists_curveEnergy_le_of_lRegAction_le (I := I) S hS T t0 t1 gRef a b A hab htime hback
  let B : Real := (2 / c) * (A - C * (b - a))
  have href (n : Nat) : IntervalIntegrable
      (fun s ↦ gRef.inner (alpha n s) (lVelocity (I := I) (alpha n) s)
        (lVelocity (I := I) (alpha n) s)) volume a b := by
    apply IntegrableOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hE n
  have henergy (n : Nat) :
      curveEnergy (I := I) gRef (alpha n) a b ≤ B := by
    exact hbudget (alpha n) (href n) (hLag n) (hact n)
  have hriedist (n : Nat) {s t : Real}
      (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      riemannianEDistOf (I := I) gRef (alpha n s) (alpha n t) ≤
        ENNReal.ofReal (Real.sqrt (t - s) * Real.sqrt B) := by
    have hsub : Set.Icc s t ⊆ Set.Icc a b := Set.Icc_subset_Icc has htb
    have hsubE :
        curveEnergy (I := I) gRef (alpha n) s t ≤
          curveEnergy (I := I) gRef (alpha n) a b :=
      curveEnergy_mono (I := I) gRef has hst htb (by
        simpa only [lVelocity] using hE n)
    exact edistOf_le_budget (I := I) gRef hst
      ((halpha n).mono hsub)
      (by simpa only [lVelocity] using (hE n).mono_set hsub)
      (hsubE.trans (henergy n))
  let f : Nat → C(Set.Icc a b, M) := fun n ↦
    ⟨fun s ↦ alpha n s.1, (halpha n).continuousOn.domRestrict⟩
  have hmod : Tendsto (fun r : Real ↦ Real.sqrt r * Real.sqrt B) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun r : Real ↦ Real.sqrt r * Real.sqrt B) :=
      Real.continuous_sqrt.mul continuous_const
    simpa only [Real.sqrt_zero, zero_mul] using hcont.tendsto (0 : Real)
  have hunif : UniformEquicontinuous (fun n ↦ (f n : Set.Icc a b → M)) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    let : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨gRef.toRiemannianMetric⟩
    obtain ⟨ρ, hρ, htoDist⟩ := dist_lt_of_riedist (I := I) gRef hε
    obtain ⟨δ, hδ, hmodδ⟩ := Metric.tendsto_nhds_nhds.1 hmod ρ hρ
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy n
    have hsmall : Real.sqrt (dist x y) * Real.sqrt B < ρ := by
      have h := hmodδ (x := dist x y) (by simpa using hxy)
      simpa only [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] using h
    have hofReal :
        ENNReal.ofReal (Real.sqrt (dist x y) * Real.sqrt B) < ENNReal.ofReal ρ :=
      (ENNReal.ofReal_lt_ofReal_iff hρ).2 hsmall
    rcases le_total x.1 y.1 with hxy' | hyx
    · have hriem := hriedist n x.2.1 hxy' y.2.2
      have hriem' := hriem.trans_lt (by
        simpa only [Subtype.dist_eq, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hxy'), neg_sub] using hofReal)
      have hout := htoDist (alpha n x.1) (alpha n y.1) (by
        simpa only [riemannianEDistOf] using hriem')
      with_unfolding_all exact hout
    · have hriem := hriedist n y.2.1 hyx x.2.2
      have hriem' := hriem.trans_lt (by
        simpa only [Subtype.dist_eq, Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr hyx)] using hofReal)
      have hout := htoDist (alpha n y.1) (alpha n x.1) (by
        simpa only [riemannianEDistOf] using hriem')
      rw [dist_comm]
      with_unfolding_all exact hout
  have hequi : Equicontinuous (fun n ↦ (f n : Set.Icc a b → M)) :=
    hunif.equicontinuous
  obtain ⟨phi, g, hphi, hconv⟩ :=
    DifferentialGeometry.Analysis.arzela_subseq_cpt
      (K := Set.univ) isCompact_univ f (fun _ _ ↦ Set.mem_univ _) hequi
  refine ⟨phi, g, hphi, ?_⟩
  with_unfolding_all exact hconv

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
theorem lAction_subseq_fix
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real) (gRef : SmoothRiemannianMetric I M)
    (a b A : Real) (hab : a ≤ b)
    (htime : Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ Set.Icc t0 t1)
    (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Set.Icc a b))
    (hE : ∀ n, IntegrableOn
      (fun s ↦ gRef.inner (alpha n s) (lVelocity (I := I) (alpha n) s)
        (lVelocity (I := I) (alpha n) s)) (Set.Icc a b))
    (hLag : ∀ n, IntervalIntegrable (lRegLagrangian S T (alpha n)) volume a b)
    (hact : ∀ n, lRegAction S T (alpha n) a b ≤ A)
    (x y : M) (hfixa : ∀ n, alpha n a = x)
    (hfixb : ∀ n, alpha n b = y) :
    ∃ (phi : Nat → Nat) (g : C(Set.Icc a b, M)),
      StrictMono phi ∧
        TendstoUniformly
          (fun n (s : Set.Icc a b) ↦ alpha (phi n) s.1) g atTop ∧
        g ⟨a, le_rfl, hab⟩ = x ∧ g ⟨b, hab, le_rfl⟩ = y := by
  obtain ⟨phi, g, hphi, hconv⟩ :=
    lAction_subseq (I := I) S hS T t0 t1 gRef a b A hab htime hback
      alpha halpha hE hLag hact
  refine ⟨phi, g, hphi, hconv, ?_, ?_⟩
  · have hlim := hconv.tendsto_at (⟨a, le_rfl, hab⟩ : Set.Icc a b)
    have hlim' : Tendsto (fun _ : Nat ↦ x) atTop
        (𝓝 (g ⟨a, le_rfl, hab⟩)) := by
      simpa only [hfixa] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds
  · have hlim := hconv.tendsto_at (⟨b, hab, le_rfl⟩ : Set.Icc a b)
    have hlim' : Tendsto (fun _ : Nat ↦ y) atTop
        (𝓝 (g ⟨b, hab, le_rfl⟩)) := by
      simpa only [hfixb] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds

variable {F : Type uE} [NormedAddCommGroup F] [InnerProductSpace Real F]
  [FiniteDimensional Real F]
variable {HF : Type uH} [TopologicalSpace HF]
variable {J : ModelWithCorners Real F HF} [J.Boundaryless]
variable {N : Type u} [UniformSpace N] [ChartedSpace HF N]
  [IsManifold J ∞ N] [CompactSpace N]
variable {D' : RealTimeInterval}

private theorem lChartKin_bound
    (S : SolutionOn (I := J) (M := N) D')
    (hMet : MetricFamilySmoothOn (I := J) (M := N) D' S.family.metric)
    (hSc : ScalarSTContOn (I := J) (M := N) S)
    (T a b : Real) (hab : a ≤ b)
    (p : N) (alpha : Nat → Real → N)
    (u : Nat → timeH1 F (b - a))
    (hsrc : ∀ n, MapsTo (alpha n) (Icc a b) (chartAt HF p).source)
    (hrep : ∀ n, EqOn (u n).toFun
      (fun r ↦ extChartAt J p (alpha n (a + r))) (Icc (0 : Real) (b - a)))
    (hdiff : ∀ n, ∀ᵐ r ∂timeMeasure (b - a),
      MDifferentiableAt (modelWithCornersSelf Real Real) J (alpha n) (a + r))
    {A : Real} (hact : ∀ n, lRegAction S T (alpha n) a b ≤ A)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D'.regular) :
    ∃ B : Real, ∀ n,
      (∫ r in (0 : Real)..b - a, (1 / 2 : Real) * inner Real
        (chartGramOp (I := J) S.family p
          (T - (a + r) ^ 2, (u n).toFun r) ((u n).deriv r))
        ((u n).deriv r)) ≤ B := by
  let kin : Nat → Real := fun n ↦ ∫ s in a..b, (1 / 2 : Real) *
    (S.base.metric (T - s ^ 2)).inner (alpha n s)
      (lVelocity (I := J) (alpha n) s) (lVelocity (I := J) (alpha n) s)
  let pot : Nat → Real := fun n ↦
    ∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)
  have hcont (n : Nat) : ContinuousOn (alpha n) (Icc a b) :=
    curve_cont_local J p (alpha n) (u n) hab (hsrc n) (hrep n)
  have hcarrier : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D'.carrier :=
    fun s hs ↦ D'.regular_subset (hreg s hs)
  have hkinInt (n : Nat) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := J) (alpha n) s)
          (lVelocity (I := J) (alpha n) s)) volume a b :=
    intervalIntegrable_lKinetic_of_chartH1 S hMet T (alpha n) p a b hab (u n)
      (hsrc n) (hrep n) (hdiff n) hreg
  have hpotInt (n : Nat) : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)) volume a b :=
    lScalar_int (I := J) S hSc T a b (alpha n) (by
      simpa only [uIcc_of_le hab] using hcarrier) (by
      simpa only [uIcc_of_le hab] using hcont n)
  have hsplit (n : Nat) :
      lRegAction S T (alpha n) a b = kin n + pot n := by
    simpa only [lRegAction, lRegLagrangian, kin, pot] using
      intervalIntegral.integral_add (hkinInt n) (hpotInt n)
  obtain ⟨C, hC⟩ := exists_uniform_lower_bound_lRegPotential (I := J) S hSc T a b (by
    simpa only [uIcc_of_le hab] using hcarrier)
  have hpotLower (n : Nat) : C * (b - a) ≤ pot n := by
    have hmono := intervalIntegral.integral_mono_on hab
      intervalIntegrable_const (hpotInt n) (fun s hs ↦
        hC s (by simpa only [uIcc_of_le hab] using hs) (alpha n s))
    rw [intervalIntegral.integral_const] at hmono
    simpa only [pot, smul_eq_mul, mul_comm] using hmono
  refine ⟨A - C * (b - a), fun n ↦ ?_⟩
  have hkinBound : kin n ≤ A - C * (b - a) := by
    have ha := hact n
    rw [hsplit n] at ha
    linarith [ha, hpotLower n]
  have heq :
      (∫ r in (0 : Real)..b - a, (1 / 2 : Real) * inner Real
        (chartGramOp (I := J) S.family p
          (T - (a + r) ^ 2, (u n).toFun r) ((u n).deriv r))
        ((u n).deriv r)) = kin n := by
    simpa only [kin, smul_apply, real_inner_smul_left] using
      (lKinetic_eq_chart_integral S T (alpha n) p a b hab (u n)
        (hsrc n) (hrep n) (hdiff n)).symm
  rw [heq]
  exact hkinBound

theorem lChartH1_subseq
    (S : SolutionOn (I := J) (M := N) D')
    (hMet : MetricFamilySmoothOn (I := J) (M := N) D' S.family.metric)
    (hSc : ScalarSTContOn (I := J) (M := N) S)
    (T a b : Real) (hab : a ≤ b)
    (p : N) (alpha : Nat → Real → N)
    (u : Nat → timeH1 F (b - a))
    (hsrc : ∀ n, MapsTo (alpha n) (Icc a b) (chartAt HF p).source)
    (hrep : ∀ n, EqOn (u n).toFun
      (fun r ↦ extChartAt J p (alpha n (a + r))) (Icc (0 : Real) (b - a)))
    (hdiff : ∀ n, ∀ᵐ r ∂timeMeasure (b - a),
      MDifferentiableAt (modelWithCornersSelf Real Real) J (alpha n) (a + r))
    {K : Set F} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt J p).target)
    (huK : ∀ n (r : Icc (0 : Real) (b - a)), (u n).toFun r.1 ∈ K)
    {A : Real} (hact : ∀ n, lRegAction S T (alpha n) a b ≤ A)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D'.regular) :
    ∃ (phi : Nat → Nat) (uLim : timeH1 F (b - a)),
      StrictMono phi ∧
        (∀ z : timeL2 F (b - a),
          Tendsto (fun n ↦ inner Real (u (phi n)).deriv z) atTop
            (nhds (inner Real uLim.deriv z))) ∧
        TendstoUniformly
          (fun n (r : Icc (0 : Real) (b - a)) ↦ (u (phi n)).toFun r.1)
          (fun r ↦ uLim.toFun r.1) atTop := by
  obtain ⟨B, hchart⟩ := lChartKin_bound (J := J) S hMet hSc T a b hab
    p alpha u hsrc hrep hdiff hact hreg
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hτc : ContinuousOn (fun r : Real ↦ T - (a + r) ^ 2)
      (Icc (0 : Real) (b - a)) :=
    (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hτreg : MapsTo (fun r : Real ↦ T - (a + r) ^ 2)
      (Icc (0 : Real) (b - a)) D'.regular := by
    intro r hr
    exact hreg (a + r) ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  exact chartH1_subseq (I := J) hMet p hba
    (fun r : Real ↦ T - (a + r) ^ 2) hτc hτreg hKc hKchart u huK hchart

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
