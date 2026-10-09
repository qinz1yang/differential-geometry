import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.Range
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Topology.FirstExit

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem lagrangian_integrable
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T a b : ℝ) (hab : a ≤ b) (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (lRegularizedLagrangian S T α) volume a b := by
  have hmap : ContinuousOn (fun s : ℝ => (T, s)) (Icc a b) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmaps : MapsTo (fun s : ℝ => (T, s)) (Icc a b)
      {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier} := htime
  have hc : ContinuousOn (lRegularizedLagrangian S T α) (Icc a b) :=
    (lRegularizedLagrangian_continuousOn_carrier (I := I) (M := M) (D := D)
      S hS α hα).comp (f := fun s : ℝ => (T, s)) hmap hmaps
  have hLag : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hc
  exact hLag

private theorem potential_integrable
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T a b : ℝ) (hab : a ≤ b) (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (fun s => 2 * s ^ 2 * S.scalar (T - s ^ 2) (α s)) volume a b := by
  have hc : ContinuousOn (fun s => S.scalar (T - s ^ 2) (α s)) (Icc a b) := by
    have hmap : ContinuousOn (fun s => (T - s ^ 2, α s)) (Icc a b) :=
      ((continuous_const.sub (continuous_id.pow 2)).prodMk hα.continuous).continuousOn
    have hmaps : MapsTo (fun s => (T - s ^ 2, α s)) (Icc a b)
        (D.carrier ×ˢ (univ : Set M)) := fun s hs => ⟨htime s hs, mem_univ _⟩
    exact hS.scalarCont.comp (f := fun s : ℝ => (T - s ^ 2, α s)) hmap hmaps
  exact ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab
    (((continuous_const.mul (continuous_id.pow 2)).continuousOn).mul hc)

private theorem regularized_integrability
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T a b : ℝ) (hab : a ≤ b) (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (lRegularizedSpeedSq S T α) volume a b ∧
      IntervalIntegrable (lRegularizedLagrangian S T α) volume a b := by
  have hLag := lagrangian_integrable S hS T a b hab α hα htime
  have hpot := potential_integrable S hS T a b hab α hα htime
  have hhalf : IntervalIntegrable (fun s => (1 / 2 : ℝ) * lRegularizedSpeedSq S T α s)
      volume a b := by
    convert hLag.sub hpot using 1
    funext s
    unfold lRegularizedLagrangian lRegularizedSpeedSq
    ring
  refine ⟨?_, hLag⟩
  convert hhalf.const_mul 2 using 1
  funext s
  ring

theorem riemannianEDistOf_le_of_lRegularizedAction_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (g : SmoothRiemannianMetric I M) (T a b A C Q : ℝ)
    (hab : a ≤ b) (hQ : 0 ≤ Q) (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier)
    (hmetric : ∀ s ∈ Icc a b, ∀ v : TangentSpace I (α s),
      g.inner (α s) v v ≤ Q * (S.base.metric (T - s ^ 2)).inner (α s) v v)
    (hpot : ∀ s ∈ Icc a b, C ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (α s))
    (hact : lRegularizedAction S T α a b ≤ A) :
    ∀ s ∈ Icc a b, riemannianEDistOf g (α a) (α s) ≤
      ENNReal.ofReal (Real.sqrt (b - a) * Real.sqrt (Q * (2 * (A - C * (b - a))))) := by
  have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn g hα.contMDiffOn
    (a := a) (b := b)
  obtain ⟨hkin, hLag⟩ := regularized_integrability S hS T a b hab α hα htime
  have henergy := lRegularizedEnergy_le S g T α a b A C Q hab hQ hmetric hpot hE hkin hLag hact
  intro s hs
  have hsub : Icc a s ⊆ Icc a b := fun _ ht => ⟨ht.1, ht.2.trans hs.2⟩
  have hd := edistOf_le_budget g hs.1 (hα.contMDiffOn.mono hsub) (hE.mono_set hsub)
    ((curveEnergy_mono g le_rfl hs.1 hs.2 hE).trans henergy)
  refine hd.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (sub_le_sub_right hs.2 a)) (Real.sqrt_nonneg _)

theorem riemannianEDistOf_lt_of_lRegularizedAction_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (g : SmoothRiemannianMetric I M) (T b A C Q r : ℝ)
    (hb : 0 ≤ b) (hQ : 0 ≤ Q)
    (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α)
    (htime : ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ D.carrier)
    (hmetric : ∀ s ∈ Icc 0 b, ∀ z : M,
      riemannianEDistOf g (α 0) z ≤ ENNReal.ofReal r → ∀ v : TangentSpace I z,
      g.inner z v v ≤ Q * (S.base.metric (T - s ^ 2)).inner z v v)
    (hpot : ∀ s ∈ Icc 0 b, C ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (α s))
    (hact : lRegularizedAction S T α 0 b ≤ A)
    (hreach : Real.sqrt b * Real.sqrt (Q * (2 * (A - C * b))) < r) :
    ∀ s ∈ Icc 0 b, riemannianEDistOf g (α 0) (α s) < ENNReal.ofReal r := by
  have hr : 0 < r := (mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg _)).trans_lt hreach
  let K : Set M := {z | riemannianEDistOf g (α 0) z ≤ ENNReal.ofReal r}
  let O : Set M := {z | riemannianEDistOf g (α 0) z < ENNReal.ofReal r}
  have hdcont : Continuous (fun z => riemannianEDistOf g (α 0) z) := by
    unfold riemannianEDistOf
    exact continuous_riemannianEDist g (α 0)
  have hKclosed : IsClosed K := isClosed_le hdcont continuous_const
  have hOopen : IsOpen O := isOpen_lt hdcont continuous_const
  have hOK : O ⊆ K := by
    intro z hz
    exact (show riemannianEDistOf g (α 0) z < ENNReal.ofReal r from hz).le
  have hOi : O ⊆ interior K := interior_maximal hOK hOopen
  have hzero : α 0 ∈ O := by
    change riemannianEDistOf g (α 0) (α 0) < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨hkin, hLag⟩ := regularized_integrability S hS T 0 b hb α hα htime
  have hkinBound : (∫ s in (0 : ℝ)..b, lRegularizedSpeedSq S T α s) ≤
      2 * (A - C * b) := by
    simpa only [sub_zero] using lRegularizedKinetic_le S T α 0 b A C hb hpot hkin hLag hact
  have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn g hα.contMDiffOn
    (a := 0) (b := b)
  have hstrict : ∀ q ∈ Icc 0 b, (∀ s ∈ Icc 0 q, α s ∈ K) → α q ∈ O := by
    intro q hq hstay
    have hsub : Icc 0 q ⊆ Icc 0 b := fun _ hs => ⟨hs.1, hs.2.trans hq.2⟩
    have hkinq : IntervalIntegrable (lRegularizedSpeedSq S T α) volume 0 q :=
      hkin.mono_set (by simpa only [uIcc_of_le hb, uIcc_of_le hq.1] using hsub)
    have hEint : IntervalIntegrable
        (fun s => g.inner (α s) (lVelocity α s) (lVelocity α s)) volume 0 q := by
      apply IntegrableOn.intervalIntegrable
      simpa only [uIcc_of_le hq.1, lVelocity] using hE.mono_set hsub
    have hkinMono : (∫ s in (0 : ℝ)..q, lRegularizedSpeedSq S T α s) ≤
        ∫ s in (0 : ℝ)..b, lRegularizedSpeedSq S T α s := by
      apply intervalIntegral.integral_mono_interval le_rfl hq.1 hq.2
      · exact Filter.Eventually.of_forall (fun s => lRegularizedSpeedSq_nonneg S T α s)
      · exact hkin
    have henergy : curveEnergy g α 0 q ≤ Q * (2 * (A - C * b)) := by
      have hcomp : curveEnergy g α 0 q ≤
          ∫ s in (0 : ℝ)..q, Q * lRegularizedSpeedSq S T α s := by
        unfold curveEnergy
        apply intervalIntegral.integral_mono_on hq.1 hEint (hkinq.const_mul Q)
        intro s hs
        exact hmetric s (hsub hs) (α s) (hstay s hs) (lVelocity α s)
      rw [intervalIntegral.integral_const_mul] at hcomp
      exact hcomp.trans (mul_le_mul_of_nonneg_left (hkinMono.trans hkinBound) hQ)
    have hed := edistOf_le_budget g hq.1 (hα.contMDiffOn.mono hsub)
      (hE.mono_set hsub) henergy
    have hrad : Real.sqrt (q - 0) * Real.sqrt (Q * (2 * (A - C * b))) < r := by
      rw [sub_zero]
      exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hq.2)
        (Real.sqrt_nonneg _)).trans_lt hreach
    exact hed.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hrad)
  have hstay : ∀ s ∈ Icc 0 b, α s ∈ K := by
    intro s hs
    by_contra hsK
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (by
      intro heq
      apply hsK
      rw [← heq]
      exact hOK hzero)
    have hsub : Icc 0 s ⊆ Icc 0 b := fun _ hu => ⟨hu.1, hu.2.trans hs.2⟩
    obtain ⟨q, hq, hprefix, hfront⟩ := DifferentialGeometry.exists_first_exit_frontier
      hKclosed hspos (hα.continuous.continuousOn.mono hsub) (hOi hzero) hsK
    exact hfront.2 (hOi (hstrict q ⟨hq.1.le, hq.2.trans hs.2⟩ hprefix))
  intro s hs
  exact hstrict s hs (fun q hq => hstay q ⟨hq.1, hq.2.trans hs.2⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman
