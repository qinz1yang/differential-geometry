import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedBadPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessRestriction
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RiemannFromRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

section ClosedSources

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

structure ClosedModelHypotheses (S : SolutionOn (I := I3) (M := M) D)
    (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop where
  isSolution : IsSolutionOn S
  complete : ∀ s ∈ D.carrier, RiemannianMetricComplete (S.base.metric s)
  curvature : ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ D.carrier →
    ∃ C : ℝ, ∀ s ∈ Set.Icc a b, ∀ x, FlowMetricBall.rmNormSq S s x ≤ C
  pinching : PhiAlmostNonnegative S D.carrier Phi
  noncollapse : ParabolicallyKappaNoncollapsedBelowScale S (modelNoncollapseFactor * kappa) sigma

omit [T2Space M] [SigmaCompactSpace M] in
theorem closed_bad_point_selection
    (S : SolutionOn (I := I3) (M := M) D) (o : TangentOrientationSection M)
    {eps kappa T K depth : ℝ} (hdepth : 0 ≤ depth)
    (hwindow : Set.Icc 0 T ⊆ D.carrier)
    (hK : ∀ y s, s ∈ Set.Icc 0 T → S.scalar s y ≤ K)
    {xhat : M} {that : ℝ} (hthat : 1 ≤ that) (hthatT : that ≤ T)
    (hQhat : 0 < S.scalar that xhat) (hdepthQ : depth ≤ S.scalar that xhat / 4)
    (hbad : ¬ OrientedWitness S o eps kappa xhat that) :
    ∃ x t, ¬ OrientedWitness S o eps kappa x t ∧
      S.scalar that xhat ≤ S.scalar t x ∧ t ∈ Set.Icc (1 / 2) that ∧
      depth / S.scalar t x ≤ 1 / 4 ∧
      Set.Icc (t - depth / S.scalar t x) t ⊆ D.carrier ∧
      ∀ y s, s ∈ Set.Icc (t - depth / S.scalar t x) t →
        2 * S.scalar t x ≤ S.scalar s y → OrientedWitness S o eps kappa y s := by
  exact exists_closed_window_bad_point S o hdepth hwindow hK hthat hthatT hQhat hdepthQ hbad

def ModelRadiusWorksClosed (eps kappa sigma : ℝ) (Phi : ℝ → ℝ) (r : ℝ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    (o : TangentOrientationSection M) (T : ℝ) (hT : 1 ≤ T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closed 0 T (by linarith))),
    ClosedModelHypotheses S kappa sigma Phi → ∀ x t, t ∈ Set.Icc 1 T →
      r⁻¹ ^ 2 ≤ S.scalar t x → OrientedWitness S o eps kappa x t

end ClosedSources

structure SelectedCountersequence (eps kappa sigma : ℝ) (Phi : ℝ → ℝ)
    extends NormalizedSequence.{u} eps kappa sigma Phi where
  bad : ∀ i, ¬ OrientedWitness (term i).S (orientation i) eps kappa (term i).basepoint 0

section Upstream

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

omit [T2Space M] [SigmaCompactSpace M] in
theorem scalar_timeRestrict (S : SolutionOn (I := I3) (M := M) D) (D' : RealTimeInterval) :
    (S.timeRestrict D').scalar = S.scalar := rfl

def WindowedModelWitness.timeRestrict {S : SolutionOn (I := I3) (M := M) D}
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S x t)
    (D' : RealTimeInterval) (htime : t ∈ D'.carrier)
    (hwindow : Set.Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ D'.carrier) :
    WindowedModelWitness eps kappa (S.timeRestrict D') x t where
  eps_pos := W.eps_pos
  eps_lt_one := W.eps_lt_one
  time_mem := htime
  scalar_pos := W.scalar_pos
  window_mem := hwindow
  model := W.model
  model_ancient := W.model_ancient
  model_scalar_base := W.model_scalar_base
  embedding := W.embedding
  buffered_ball := W.buffered_ball
  base_map := W.base_map
  comparison := W.comparison
  source_capture := W.source_capture

def WindowedModelWitness.ofTimeRestrict {S : SolutionOn (I := I3) (M := M) D}
    {eps kappa : ℝ} {x : M} {t : ℝ} {D' : RealTimeInterval}
    (W : WindowedModelWitness eps kappa (S.timeRestrict D') x t)
    (hsub : D'.carrier ⊆ D.carrier) :
    WindowedModelWitness eps kappa S x t where
  eps_pos := W.eps_pos
  eps_lt_one := W.eps_lt_one
  time_mem := hsub W.time_mem
  scalar_pos := W.scalar_pos
  window_mem := fun _ hu => hsub (W.window_mem hu)
  model := W.model
  model_ancient := W.model_ancient
  model_scalar_base := W.model_scalar_base
  embedding := W.embedding
  buffered_ball := W.buffered_ball
  base_map := W.base_map
  comparison := W.comparison
  source_capture := W.source_capture

private theorem parabolicTime_window_start {tau A s eps Q : ℝ} (hA : 0 < A) (heps : 0 < eps)
    (hQ : 0 < Q) :
    parabolicTime tau A (s - (eps * (A⁻¹ * Q))⁻¹) = parabolicTime tau A s - (eps * Q)⁻¹ := by
  dsimp only [parabolicTime]
  field_simp [hA.ne', heps.ne', hQ.ne']
  ring

def WindowedModelWitness.parabolic {S : SolutionOn (I := I3) (M := M) D}
    {eps kappa : ℝ} {x : M} {tau A : ℝ} (hA : 0 < A) (htau : tau ∈ D.carrier) {s : ℝ}
    (W : WindowedModelWitness eps kappa S x (parabolicTime tau A s)) :
    WindowedModelWitness eps kappa (parabolicSolution S tau A hA htau) x s := by
  have hscalar : 0 < (parabolicSolution S tau A hA htau).scalar s x := by
    rw [parabolicSolution_scalar]
    exact mul_pos (inv_pos.mpr hA) W.scalar_pos
  have hmetric : rescaledMetric (parabolicSolution S tau A hA htau) s
      ((parabolicSolution S tau A hA htau).scalar s x) hscalar =
      rescaledMetric S (parabolicTime tau A s) (S.scalar (parabolicTime tau A s) x) W.scalar_pos := by
    calc rescaledMetric (parabolicSolution S tau A hA htau) s
          ((parabolicSolution S tau A hA htau).scalar s x) hscalar
        = rescaledMetric (parabolicSolution S tau A hA htau) s
            (A⁻¹ * S.scalar (parabolicTime tau A s) x)
            (mul_pos (inv_pos.mpr hA) W.scalar_pos) := by
          congr 1
          exact congrFun (congrFun (parabolicSolution_scalar S tau A hA htau) s) x
      _ = _ := rescaledMetric_paraSolution S tau A hA htau s
          (S.scalar (parabolicTime tau A s) x) W.scalar_pos
  refine
    { eps_pos := W.eps_pos
      eps_lt_one := W.eps_lt_one
      time_mem := W.time_mem
      scalar_pos := hscalar
      window_mem := ?_
      model := W.model
      model_ancient := W.model_ancient
      model_scalar_base := W.model_scalar_base
      embedding := W.embedding
      buffered_ball := W.buffered_ball
      base_map := W.base_map
      comparison := ?_
      source_capture := ?_ }
  · intro u hu
    apply W.window_mem
    have hmono : Monotone (parabolicTime tau A) := fun a b hab =>
      add_le_add_right (div_le_div_of_nonneg_right hab hA.le) tau
    have hstart := parabolicTime_window_start (tau := tau) (s := s) hA W.eps_pos W.scalar_pos
    rw [parabolicSolution_scalar] at hu
    exact ⟨hstart ▸ hmono hu.1, hmono hu.2⟩
  · let _ : TopologicalSpace W.model.M := W.model.topology
    let _ : ChartedSpace ThreeSpace W.model.M := W.model.charted
    let _ : IsManifold I3 ∞ W.model.M := W.model.smooth
    let _ : SigmaCompactSpace W.model.M := W.model.sigmaCompact
    let _ : T2Space W.model.M := W.model.t2
    rw [hmetric]
    exact W.comparison
  · rw [hmetric]
    exact W.source_capture

def WindowedModelWitness.ofParabolic {S : SolutionOn (I := I3) (M := M) D}
    {eps kappa : ℝ} {x : M} {tau A : ℝ} (hA : 0 < A) (htau : tau ∈ D.carrier) {s : ℝ}
    (W : WindowedModelWitness eps kappa (parabolicSolution S tau A hA htau) x s) :
    WindowedModelWitness eps kappa S x (parabolicTime tau A s) := by
  have hscalar : 0 < S.scalar (parabolicTime tau A s) x := by
    have h := W.scalar_pos
    rw [parabolicSolution_scalar] at h
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hA)).mp h
  have hmetric : rescaledMetric (parabolicSolution S tau A hA htau) s
      ((parabolicSolution S tau A hA htau).scalar s x) W.scalar_pos =
      rescaledMetric S (parabolicTime tau A s) (S.scalar (parabolicTime tau A s) x) hscalar := by
    calc rescaledMetric (parabolicSolution S tau A hA htau) s
          ((parabolicSolution S tau A hA htau).scalar s x) W.scalar_pos
        = rescaledMetric (parabolicSolution S tau A hA htau) s
            (A⁻¹ * S.scalar (parabolicTime tau A s) x)
            (mul_pos (inv_pos.mpr hA) hscalar) := by
          congr 1
          exact congrFun (congrFun (parabolicSolution_scalar S tau A hA htau) s) x
      _ = _ := rescaledMetric_paraSolution S tau A hA htau s
          (S.scalar (parabolicTime tau A s) x) hscalar
  refine
    { eps_pos := W.eps_pos
      eps_lt_one := W.eps_lt_one
      time_mem := W.time_mem
      scalar_pos := hscalar
      window_mem := ?_
      model := W.model
      model_ancient := W.model_ancient
      model_scalar_base := W.model_scalar_base
      embedding := W.embedding
      buffered_ball := W.buffered_ball
      base_map := W.base_map
      comparison := ?_
      source_capture := ?_ }
  · intro u hu
    have hmono : Monotone (parabolicBackward tau A) := fun a b hab =>
      mul_le_mul_of_nonneg_left (sub_le_sub_right hab tau) hA.le
    have hstart := parabolicTime_window_start (tau := tau) (s := s) hA W.eps_pos hscalar
    have hleft : parabolicBackward tau A
        (parabolicTime tau A s - (eps * S.scalar (parabolicTime tau A s) x)⁻¹) =
        s - (eps * (A⁻¹ * S.scalar (parabolicTime tau A s) x))⁻¹ := by
      rw [← hstart, parabolicBackward_time hA.ne']
    have hright : parabolicBackward tau A (parabolicTime tau A s) = s := parabolicBackward_time hA.ne'
    have hmem : parabolicBackward tau A u ∈ Set.Icc
        (s - (eps * (parabolicSolution S tau A hA htau).scalar s x)⁻¹) s := by
      rw [parabolicSolution_scalar]
      exact ⟨hleft ▸ hmono hu.1, hright ▸ hmono hu.2⟩
    have hsource : parabolicTime tau A (parabolicBackward tau A u) ∈ D.carrier := W.window_mem hmem
    simpa only [parabolicTime_back hA.ne'] using hsource
  · let _ : TopologicalSpace W.model.M := W.model.topology
    let _ : ChartedSpace ThreeSpace W.model.M := W.model.charted
    let _ : IsManifold I3 ∞ W.model.M := W.model.smooth
    let _ : SigmaCompactSpace W.model.M := W.model.sigmaCompact
    let _ : T2Space W.model.M := W.model.t2
    rw [← hmetric]
    exact W.comparison
  · rw [← hmetric]
    exact W.source_capture

omit [T2Space M] [SigmaCompactSpace M] in
theorem orientedWitness_paraSolution_iff (S : SolutionOn (I := I3) (M := M) D)
    (o : TangentOrientationSection M) {tau A : ℝ} (hA : 0 < A) (htau : tau ∈ D.carrier)
    (s : ℝ) (x : M) (eps kappa : ℝ) :
    OrientedWitness (parabolicSolution S tau A hA htau) o eps kappa x s ↔
      OrientedWitness S o eps kappa x (parabolicTime tau A s) :=
  ⟨fun h => h.elim fun W hW => ⟨W.ofParabolic hA htau, hW⟩,
    fun h => h.elim fun W hW => ⟨W.parabolic hA htau, hW⟩⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem orientedWitness_timeRestrict {S : SolutionOn (I := I3) (M := M) D}
    {o : TangentOrientationSection M} {eps kappa : ℝ} {x : M} {t : ℝ}
    (D' : RealTimeInterval) (htime : t ∈ D'.carrier)
    (hwindow : Set.Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ D'.carrier)
    (h : OrientedWitness S o eps kappa x t) :
    OrientedWitness (S.timeRestrict D') o eps kappa x t :=
  h.elim fun W hW => ⟨W.timeRestrict D' htime hwindow, hW⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem orientedWitness_of_timeRestrict {S : SolutionOn (I := I3) (M := M) D}
    {o : TangentOrientationSection M} {eps kappa : ℝ} {x : M} {t : ℝ}
    {D' : RealTimeInterval} (hsub : D'.carrier ⊆ D.carrier)
    (h : OrientedWitness (S.timeRestrict D') o eps kappa x t) :
    OrientedWitness S o eps kappa x t :=
  h.elim fun W hW => ⟨W.ofTimeRestrict hsub, hW⟩

theorem spatiallyKappaNoncollapsed_timeRestrict {S : SolutionOn (I := I3) (M := M) D}
    {D' : RealTimeInterval} {kappa rho : ℝ} (hsub : D'.carrier ⊆ D.carrier)
    (h : Perelman.SpatiallyKappaNoncollapsedBelowScale S kappa rho) :
    Perelman.SpatiallyKappaNoncollapsedBelowScale (S.timeRestrict D') kappa rho := by
  refine ⟨h.1, ?_⟩
  intro t B hradius
  exact h.2 ⟨(t : ℝ), hsub t.2⟩ ⟨B.center, B.radius, B.radius_pos⟩ hradius

theorem parabolicallyKappaNoncollapsedBelowScale_timeRestrict
    {S : SolutionOn (I := I3) (M := M) D}
    {D' : RealTimeInterval} {kappa rho : ℝ} (hsub : D'.carrier ⊆ D.carrier)
    (h : ParabolicallyKappaNoncollapsedBelowScale S kappa rho) :
    ParabolicallyKappaNoncollapsedBelowScale (S.timeRestrict D') kappa rho := by
  refine ⟨h.1, fun t B hradius hB => ?_⟩
  exact h.2 ⟨(t : ℝ), hsub t.2⟩ ⟨B.center, B.radius, B.radius_pos⟩ hradius
    ⟨hB.1.trans hsub, hB.2⟩

end Upstream

structure ClosedModelCounterexample (eps kappa sigma : ℝ) (Phi : ℝ → ℝ) (r : ℝ) where
  M : Type u
  [topology : TopologicalSpace M]
  [charted : ChartedSpace ThreeSpace M]
  [smooth : IsManifold I3 ∞ M]
  [t2 : T2Space M]
  [sigmaCompact : SigmaCompactSpace M]
  [connected : ConnectedSpace M]
  orientation : TangentOrientationSection M
  T : ℝ
  one_le_T : 1 ≤ T
  S : SolutionOn (I := I3) (M := M)
    (RealTimeInterval.closed 0 T (le_trans zero_le_one one_le_T))
  hyp : ClosedModelHypotheses S kappa sigma Phi
  point : M
  time : ℝ
  time_mem : time ∈ Set.Icc 1 T
  scalar_ge : r⁻¹ ^ 2 ≤ S.scalar time point
  bad : ¬ OrientedWitness S orientation eps kappa point time

attribute [local instance] ClosedModelCounterexample.topology
  ClosedModelCounterexample.charted ClosedModelCounterexample.smooth
  ClosedModelCounterexample.t2 ClosedModelCounterexample.sigmaCompact
  ClosedModelCounterexample.connected

theorem nonempty_closedModelCounterexample {eps kappa sigma r : ℝ} {Phi : ℝ → ℝ}
    (h : ¬ ModelRadiusWorksClosed.{u} eps kappa sigma Phi r) :
    Nonempty (ClosedModelCounterexample.{u} eps kappa sigma Phi r) := by
  by_contra hc
  refine h ?_
  intro N itop ichart ism it2 isc iconn o T hT S hyp x t ht hR
  by_contra hbad
  exact hc ⟨{ M := N, topology := itop, charted := ichart, smooth := ism, t2 := it2
              sigmaCompact := isc, connected := iconn, orientation := o, T := T
              one_le_T := hT, S := S, hyp := hyp, point := x, time := t, time_mem := ht
              scalar_ge := hR, bad := hbad }⟩

private def adapterDepth (small : ℝ) (n : ℕ) : ℝ := max (modelDepth small) (n : ℝ)

private def adapterRadius (eps small : ℝ) (n : ℕ) : ℝ :=
  min (Real.sqrt eps) (1 / (8 * adapterDepth small n + 1))

private theorem adapterDepth_nonneg (small : ℝ) (n : ℕ) : 0 ≤ adapterDepth small n :=
  le_trans (Nat.cast_nonneg n) (le_max_right _ _)

private theorem modelDepth_le_adapterDepth (small : ℝ) (n : ℕ) :
    modelDepth small ≤ adapterDepth small n := le_max_left _ _

private theorem adapterDepth_pos {small : ℝ} (hsmall : 0 < small) (n : ℕ) :
    0 < adapterDepth small n :=
  lt_of_lt_of_le (inv_pos.mpr hsmall) (le_max_left _ _)

private theorem adapterDepth_tendsto (small : ℝ) :
    Filter.Tendsto (adapterDepth small) Filter.atTop Filter.atTop := by
  have hnat : Filter.Tendsto (fun i : ℕ => (i : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun b => ⟨⌈b⌉₊, fun n hn => ?_⟩
    refine le_trans (Nat.le_ceil b) ?_
    exact_mod_cast hn
  exact Filter.tendsto_atTop_mono (fun n => le_max_right _ _) hnat

private theorem adapterRadius_pos {eps : ℝ} (small : ℝ) (heps : 0 < eps) (n : ℕ) :
    0 < adapterRadius eps small n := by
  have hd := adapterDepth_nonneg small n
  exact lt_min (Real.sqrt_pos.mpr heps) (div_pos one_pos (by linarith))

private theorem adapterRadius_le_sqrt (eps small : ℝ) (n : ℕ) :
    adapterRadius eps small n ≤ Real.sqrt eps := min_le_left _ _

private theorem adapterDepth_le_threshold {eps : ℝ} (small : ℝ) (heps : 0 < eps) (n : ℕ) :
    8 * adapterDepth small n + 1 ≤ (adapterRadius eps small n)⁻¹ ^ 2 := by
  have hd := adapterDepth_nonneg small n
  have hA : (0:ℝ) < 8 * adapterDepth small n + 1 := by linarith
  have hr := adapterRadius_pos small heps n
  have hle : adapterRadius eps small n ≤ 1 / (8 * adapterDepth small n + 1) :=
    min_le_right _ _
  have hmul : adapterRadius eps small n * (8 * adapterDepth small n + 1) ≤ 1 :=
    (le_div_iff₀ hA).mp hle
  have hle1 : adapterRadius eps small n ≤ 1 := by
    refine hle.trans ?_
    rw [div_le_one hA]
    linarith
  have hsq : (0:ℝ) < adapterRadius eps small n ^ 2 := pow_pos hr 2
  have hstep : (8 * adapterDepth small n + 1) * adapterRadius eps small n ^ 2 ≤ 1 := by
    nlinarith
  calc 8 * adapterDepth small n + 1 ≤ 1 / adapterRadius eps small n ^ 2 :=
        (le_div_iff₀ hsq).mpr hstep
    _ = (adapterRadius eps small n)⁻¹ ^ 2 := by rw [one_div, inv_pow]

theorem selected_countersequence_of_radius_failure' {eps small kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) (hsmall : 0 < small) (hs : small ≤ eps)
    (failure : ∀ r : ℝ, 0 < r → r ≤ Real.sqrt eps →
      ¬ ModelRadiusWorksClosed.{u} eps kappa sigma Phi r) :
    Nonempty (SelectedCountersequence.{u} small kappa sigma Phi) := by
  classical
  obtain ⟨CE⟩ : Nonempty (∀ n : ℕ,
      ClosedModelCounterexample.{u} eps kappa sigma Phi (adapterRadius eps small n)) :=
    ⟨fun n => Classical.choice (nonempty_closedModelCounterexample
      (failure _ (adapterRadius_pos small heps n) (adapterRadius_le_sqrt eps small n)))⟩
  have hdnn : ∀ n : ℕ, (0:ℝ) ≤ adapterDepth small n := adapterDepth_nonneg small
  have hQhat : ∀ n : ℕ, 8 * adapterDepth small n + 1 ≤
      (CE n).S.scalar (CE n).time (CE n).point := fun n =>
    le_trans (adapterDepth_le_threshold small heps n) (CE n).scalar_ge
  have hQhatpos : ∀ n : ℕ, 0 < (CE n).S.scalar (CE n).time (CE n).point := by
    intro n
    have := hQhat n
    have := hdnn n
    linarith
  have hbadsmall : ∀ n : ℕ,
      ¬ OrientedWitness (CE n).S (CE n).orientation small kappa (CE n).point (CE n).time := by
    intro n hw
    exact (CE n).bad (orientedWitness_mono_closed (CE n).S (CE n).hyp.isSolution
      (CE n).orientation hs heps1 hw)
  have hscalarBound : ∀ n : ℕ, ∃ K : ℝ, ∀ (y : (CE n).M) (s : ℝ),
      s ∈ Set.Icc (0:ℝ) (CE n).T → (CE n).S.scalar s y ≤ K := by
    intro n
    obtain ⟨Cn, hCn⟩ := (CE n).hyp.curvature 0 (CE n).T
      (le_trans zero_le_one (CE n).one_le_T) Set.Subset.rfl
    refine ⟨(Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt Cn, fun y s hs => ?_⟩
    have h1 := scalar_abs_le_rm (I := I3) ((CE n).S.base.metric s) y
    have h2 : DifferentialGeometry.Tensor0SBundle.normSq0S (I := I3)
        ((CE n).S.base.metric s) y 4 (metricRm04At (I := I3) ((CE n).S.base.metric s) y)
        ≤ Cn := hCn s hs y
    have h3 : Module.finrank ℝ (TangentSpace I3 y) = Module.finrank ℝ ThreeSpace := rfl
    have h4 : (0:ℝ) ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 := by positivity
    rw [h3] at h1
    exact le_trans (le_abs_self _)
      (le_trans h1 (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) h4))
  have hselect : ∀ n : ℕ, ∃ (x : (CE n).M) (t : ℝ),
      ¬ OrientedWitness (CE n).S (CE n).orientation small kappa x t ∧
        (CE n).S.scalar (CE n).time (CE n).point ≤ (CE n).S.scalar t x ∧
        t ∈ Set.Icc (1 / 2) (CE n).time ∧
        2 * adapterDepth small n / (CE n).S.scalar t x ≤ 1 / 4 ∧
        Set.Icc (t - 2 * adapterDepth small n / (CE n).S.scalar t x) t ⊆
          Set.Icc (0:ℝ) (CE n).T ∧
        ∀ (y : (CE n).M), ∀ s ∈ Set.Icc
            (t - 2 * adapterDepth small n / (CE n).S.scalar t x) t,
          2 * (CE n).S.scalar t x ≤ (CE n).S.scalar s y →
            OrientedWitness (CE n).S (CE n).orientation small kappa y s := by
    intro n
    obtain ⟨K, hK⟩ := hscalarBound n
    have hdq : 2 * adapterDepth small n ≤
        (CE n).S.scalar (CE n).time (CE n).point / 4 := by
      have h1 := hQhat n
      have h2 := hdnn n
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
      linarith
    exact closed_bad_point_selection (CE n).S (CE n).orientation
      (by linarith [hdnn n]) Set.Subset.rfl hK ((CE n).time_mem).1 ((CE n).time_mem).2
      (hQhatpos n) hdq (hbadsmall n)
  choose xsel tsel hbadsel hQle htmem hratio hwin hgood using hselect
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → ℝ, ∀ n, Q n = (CE n).S.scalar (tsel n) (xsel n) :=
    ⟨fun n => (CE n).S.scalar (tsel n) (xsel n), fun _ => rfl⟩
  have hQpos : ∀ n, 0 < Q n := by
    intro n
    rw [hQ n]
    exact lt_of_lt_of_le (hQhatpos n) (hQle n)
  have hQge : ∀ n, 8 * adapterDepth small n + 1 ≤ Q n := by
    intro n
    rw [hQ n]
    exact le_trans (hQhat n) (hQle n)
  have hwin' : ∀ n, Set.Icc (tsel n - 2 * adapterDepth small n / Q n) (tsel n) ⊆
      Set.Icc (0:ℝ) (CE n).T := by
    intro n
    rw [hQ n]
    exact hwin n
  have hdiv : ∀ n, (0:ℝ) ≤ 2 * adapterDepth small n / Q n := fun n =>
    div_nonneg (by linarith [hdnn n]) (hQpos n).le
  have hlow : ∀ n, (0:ℝ) ≤ tsel n - 2 * adapterDepth small n / Q n := fun n =>
    (hwin' n ⟨le_rfl, by linarith [hdiv n]⟩).1
  have hupp : ∀ n, tsel n ≤ (CE n).T := fun n =>
    (hwin' n ⟨by linarith [hdiv n], le_rfl⟩).2
  have htcar : ∀ n, tsel n ∈
      (RealTimeInterval.closed 0 (CE n).T (le_trans zero_le_one (CE n).one_le_T)).carrier :=
    fun n => hwin' n ⟨by linarith [hdiv n], le_rfl⟩
  have hparaWin : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc (-(2 * adapterDepth small n)) 0 →
      parabolicTime (tsel n) (Q n) s ∈
        Set.Icc (tsel n - 2 * adapterDepth small n / Q n) (tsel n) := by
    intro n s hs
    have h1 : -(2 * adapterDepth small n) / Q n ≤ s / Q n :=
      div_le_div_of_nonneg_right hs.1 (hQpos n).le
    have h2 : s / Q n ≤ 0 / Q n := div_le_div_of_nonneg_right hs.2 (hQpos n).le
    rw [zero_div] at h2
    rw [neg_div] at h1
    exact ⟨by dsimp only [parabolicTime]; linarith, by dsimp only [parabolicTime]; linarith⟩
  have hcarSub : ∀ n : ℕ, ∀ s : ℝ, s ∈ Set.Icc (-(2 * adapterDepth small n)) 0 →
      parabolicTime (tsel n) (Q n) s ∈ Set.Icc (0:ℝ) (CE n).T := fun n s hs =>
    hwin' n (hparaWin n s hs)
  have hregSub : ∀ n : ℕ, ∀ s : ℝ, s ∈ Set.Ioo (-(2 * adapterDepth small n)) 0 →
      parabolicTime (tsel n) (Q n) s ∈ Set.Ioo (0:ℝ) (CE n).T := by
    intro n s hs
    have h1 : -(2 * adapterDepth small n) / Q n < s / Q n :=
      div_lt_div_of_pos_right hs.1 (hQpos n)
    have h2 : s / Q n < 0 / Q n := div_lt_div_of_pos_right hs.2 (hQpos n)
    rw [zero_div] at h2
    rw [neg_div] at h1
    have h3 := hlow n
    have h4 := hupp n
    exact ⟨by dsimp only [parabolicTime]; linarith, by dsimp only [parabolicTime]; linarith⟩
  have hIle : ∀ n : ℕ, -(2 * adapterDepth small n) ≤ 0 := fun n => by linarith [hdnn n]
  have hpara : ∀ n : ℕ, IsSolutionOn
      (parabolicSolution (CE n).S (tsel n) (Q n) (hQpos n) (htcar n)) := fun n =>
    parabolicSolution_isSolutionOn (CE n).S (CE n).hyp.isSolution _ _ _ _
  refine ⟨{
    interval := fun n => RealTimeInterval.closed (-(2 * adapterDepth small n)) 0 (hIle n)
    term := fun n =>
      { M := (CE n).M
        topology := (CE n).topology
        charted := (CE n).charted
        smooth := (CE n).smooth
        sigmaCompact := (CE n).sigmaCompact
        t2 := (CE n).t2
        t2TangentBundle := inferInstance
        basepoint := xsel n
        S := (parabolicSolution (CE n).S (tsel n) (Q n) (hQpos n) (htcar n)).timeRestrict
          (RealTimeInterval.closed (-(2 * adapterDepth small n)) 0 (hIle n))
        isSolution := isSolutionOn_timeRestrict (hpara n) (fun s hs => hcarSub n s hs)
          (fun s hs => hregSub n s hs) }
    depth := adapterDepth small
    scale := Q
    depth_pos := fun n => adapterDepth_pos hsmall n
    depth_buffer := fun n => modelDepth_le_adapterDepth small n
    scale_pos := hQpos
    depth_tendsto := adapterDepth_tendsto small
    scale_tendsto := ?_
    carrier_eq := fun _ => rfl
    regular_eq := fun _ => rfl
    connected := fun n => (CE n).connected
    orientation := fun n => (CE n).orientation
    complete := ?_
    source_bound := ?_
    base_one := ?_
    noncollapse := ?_
    pinching := ?_
    higher_good := ?_
    bad := ?_ }⟩
  · refine Filter.tendsto_atTop_mono (fun n => ?_) (adapterDepth_tendsto small)
    have h1 := hQge n
    have h2 := hdnn n
    linarith
  · intro n s hs
    have hmem := hcarSub n s hs
    have hg := (CE n).hyp.complete (parabolicTime (tsel n) (Q n) s) hmem
    have hscaled : DifferentialGeometry.RiemannianMetricComplete (I := I3)
        (scaleMetric (I := I3) (Q n) (hQpos n)
          ((CE n).S.base.metric (parabolicTime (tsel n) (Q n) s))) :=
      DifferentialGeometry.RiemannianMetricComplete.of_lower hg (hQpos n)
        (fun _ _ => le_rfl)
    exact hscaled.complete
  · intro n
    obtain ⟨Cn, hCn⟩ := (CE n).hyp.curvature 0 (CE n).T
      (le_trans zero_le_one (CE n).one_le_T) Set.Subset.rfl
    refine ⟨(Q n)⁻¹ ^ 2 * Cn, fun s hs y => ?_⟩
    have hpr := parabolicRmNormSq (CE n).S (tsel n) (Q n) (hQpos n) (htcar n) s y
    have hbound := hCn (parabolicTime (tsel n) (Q n) s) (hcarSub n s hs) y
    have hnn : (0:ℝ) ≤ (Q n)⁻¹ ^ 2 := by positivity
    exact le_trans (le_of_eq hpr) (mul_le_mul_of_nonneg_left hbound hnn)
  · intro n
    have hbase : ((parabolicSolution (CE n).S (tsel n) (Q n) (hQpos n) (htcar n)).timeRestrict
        (RealTimeInterval.closed (-(2 * adapterDepth small n)) 0 (hIle n))).scalar 0 (xsel n)
        = 1 := by
      simp only [scalar_timeRestrict, parabolicSolution_scalar, parabolicTime_zero]
      rw [← hQ n]
      exact inv_mul_cancel₀ (ne_of_gt (hQpos n))
    exact hbase
  · intro n
    exact parabolicallyKappaNoncollapsedBelowScale_timeRestrict (fun s hs => hcarSub n s hs)
      (parabolicallyKappaNoncollapsedBelowScale_parabolicSolution (CE n).S (tsel n) (Q n)
        (hQpos n) (htcar n) _ sigma (CE n).hyp.noncollapse)
  · intro n s hs y
    exact phiAlmostNonnegative_paraSolution (CE n).S (hQpos n) (htcar n)
      (CE n).hyp.pinching s (hcarSub n s hs) y
  · intro n s hs y hy
    have hmem2 : s ∈ Set.Icc (-(2 * adapterDepth small n)) 0 :=
      ⟨by linarith [hs.1, hdnn n], hs.2⟩
    have hy' : 2 ≤ (parabolicSolution (CE n).S (tsel n) (Q n) (hQpos n) (htcar n)).scalar s y := hy
    have hne : Q n ≠ 0 := ne_of_gt (hQpos n)
    have hyQ : 2 * Q n ≤ (CE n).S.scalar (parabolicTime (tsel n) (Q n) s) y := by
      rw [parabolicSolution_scalar] at hy'
      have hmul := mul_le_mul_of_nonneg_right hy' (hQpos n).le
      have hcancel : (Q n)⁻¹ * (CE n).S.scalar (parabolicTime (tsel n) (Q n) s) y * Q n =
          (CE n).S.scalar (parabolicTime (tsel n) (Q n) s) y := by
        field_simp
      rw [hcancel] at hmul
      exact hmul
    have hsrc := hgood n y (parabolicTime (tsel n) (Q n) s)
      (by rw [← hQ n]; exact hparaWin n s hmem2) (by rw [← hQ n]; exact hyQ)
    have hres := (orientedWitness_paraSolution_iff (CE n).S (CE n).orientation
      (hQpos n) (htcar n) s y small kappa).mpr hsrc
    refine orientedWitness_timeRestrict _ hmem2 ?_ hres
    intro u hu
    have hRpos : (0:ℝ) < small * 2 := by linarith
    have hRle : small * 2 ≤ small *
        (parabolicSolution (CE n).S (tsel n) (Q n) (hQpos n) (htcar n)).scalar s y := by
      nlinarith [hy']
    have hinvle : (small * (parabolicSolution (CE n).S (tsel n) (Q n) (hQpos n)
        (htcar n)).scalar s y)⁻¹ ≤ (small * 2)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact div_le_div_of_nonneg_left zero_le_one hRpos hRle
    have hhalf : (small * 2)⁻¹ ≤ adapterDepth small n := by
      refine le_trans ?_ (modelDepth_le_adapterDepth small n)
      have hm : modelDepth small = small⁻¹ := rfl
      rw [hm, mul_comm, mul_inv]
      have h2 : (2:ℝ)⁻¹ ≤ 1 := by norm_num
      have hpos : (0:ℝ) < small⁻¹ := inv_pos.mpr hsmall
      nlinarith
    exact ⟨by linarith [hu.1, hs.1], le_trans hu.2 hs.2⟩
  · intro n hcontra
    refine hbadsel n ?_
    have h1 := orientedWitness_of_timeRestrict (fun s hs => hcarSub n s hs) hcontra
    have h2 := (orientedWitness_paraSolution_iff (CE n).S (CE n).orientation
      (hQpos n) (htcar n) 0 (xsel n) small kappa).mp h1
    rwa [parabolicTime_zero] at h2

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
