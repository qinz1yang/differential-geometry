import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCloseness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardFamilyCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessEndpointPerturbation

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

private local instance windowSigmaCompact (V : TopologicalSpace.Opens ThreeSpace) :
    SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) V.isOpen)

section Core

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem scaleMetric_one_eq {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M) :
    scaleMetric 1 one_pos g = g :=
  SmoothRiemannianMetric.ext_inner fun x v w => by rw [scaleMetric_one]

private theorem eventually_orientedWitness_of_strict_standard_witness_endpoint
    {δ Θ D T₀ : ℝ} (hδ : 0 < δ) (hΘ : Θ < 1)
    {Q : ℕ → StandardSolution} {Q' : StandardSolution}
    (hQ : ∀ K : Set (standardCapWindow D), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc 0 Θ,
        metricDerivNormSupOn K p (((Q i).val.metric t).restrictOpen (standardCapWindow D))
          ((Q'.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) < e)
    {T : ℕ → ℝ} (hT0 : ∀ n, 0 ≤ T n)
    (S : ∀ n, SolutionOn (I := I3) (M := standardCapWindow D)
      (RealTimeInterval.closed 0 (T n) (hT0 n)))
    (hS : ∀ n, IsSolutionOn (S n)) (hTΘ : ∀ n, T n ≤ Θ)
    (hclose : ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ τ ∈ Icc 0 (T n), ∀ i ≤ p,
      ∀ v : standardCapWindow D, metricDerivNorm i ((S n).base.metric τ)
        (((Q n).val.metric τ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e)
    (hT : Tendsto T atTop (𝓝 T₀)) {z : ℕ → standardCapWindow D} {z₀ : standardCapWindow D}
    (hz : Tendsto z atTop (𝓝 z₀))
    (hT₀mem : T₀ ∈ Q'.val.domain)
    (W : WindowedModelWitness δ standardModelKappa
      (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem) z₀.val 0)
    (hstrict : ∀ a b, a + 2 * b ≤ modelOrder δ → ∀ s ∈ Icc (-modelDepth δ) 0,
      ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius δ),
        tensor02CovDerivNormWith a (W.comparison.jet b s)
          (W.model.S.base.metric s) (W.model.S.base.metric s) y < δ)
    (hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius δ + 1) ⊆ (standardCapWindow D : Set ThreeSpace))
    (hO : ∀ o : TangentOrientationSection (standardCapWindow D),
      ∃ oN : TangentOrientationSection W.model.M,
        ∀ y ∈ (W.toRestrictOpen hU).embedding.source,
          ∃ hf : Function.Bijective (mfderiv I3 I3 (W.toRestrictOpen hU).embedding y),
            PreservesTangentOrientationAt oN o (W.toRestrictOpen hU).embedding y hf)
    (hmargin : 4 * (δ * (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0
      z₀.val)⁻¹ ≤ T₀) :
    ∀ᶠ n in atTop, ∀ o : TangentOrientationSection (standardCapWindow D),
      OrientedWitness (S n) o δ standardModelKappa (z n) (T n) := by
  have hT₀Θ : T₀ ≤ Θ := le_of_tendsto' hT hTΘ
  have hR := W.scalar_pos
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = 2 * (δ *
      (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0 z₀.val)⁻¹ :=
    ⟨_, rfl⟩
  have hw0 : 0 < (δ * (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0
      z₀.val)⁻¹ := inv_pos.mpr (mul_pos hδ hR)
  have hbT : b < T₀ := by linarith
  have hwb : (δ * (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0
      z₀.val)⁻¹ < b := by linarith
  have hb0 : -b ≤ 0 := by linarith
  have hcarP : (RealTimeInterval.closed (-b) 0 hb0).carrier ⊆
      (parabolicInterval (lifetimeInterval Q'.val.lifetime Q'.val.lifetime_pos) T₀ 1
        hT₀mem).carrier := by
    intro s hs
    have hs' : s ∈ Icc (-b) 0 := hs
    change parabolicTime T₀ 1 s ∈ (lifetimeInterval Q'.val.lifetime Q'.val.lifetime_pos).carrier
    rw [mem_lifetimeInterval_carrier]
    simp only [parabolicTime, div_one]
    exact ⟨by linarith [hs'.1],
      (ENNReal.ofReal_lt_one.mpr (by linarith [hs'.2])).trans_eq Q'.lifetime_eq_one.symm⟩
  have hregP : (RealTimeInterval.closed (-b) 0 hb0).regular ⊆
      (parabolicInterval (lifetimeInterval Q'.val.lifetime Q'.val.lifetime_pos) T₀ 1
        hT₀mem).regular := by
    intro s hs
    have hs' : s ∈ Ioo (-b) 0 := hs
    change parabolicTime T₀ 1 s ∈ (lifetimeInterval Q'.val.lifetime Q'.val.lifetime_pos).regular
    rw [mem_lifetimeInterval_regular]
    simp only [parabolicTime, div_one]
    exact ⟨by linarith [hs'.1],
      (ENNReal.ofReal_lt_one.mpr (by linarith [hs'.2])).trans_eq Q'.lifetime_eq_one.symm⟩
  have hP : IsSolutionOn (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem) :=
    parabolicSolution_isSolutionOn _ Q'.val.isSolutionOn T₀ 1 one_pos hT₀mem
  have hS₀ : IsSolutionOn ((solutionOnRestrictOpen
      (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem)
      (standardCapWindow D)).timeRestrict (RealTimeInterval.closed (-b) 0 hb0)) :=
    isSolutionOn_timeRestrict (isSolutionOn_restrictOpen _ hP _) hcarP hregP
  have hRs : (solutionOnRestrictOpen (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem)
      (standardCapWindow D)).scalar 0 z₀ =
      (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0 z₀.val :=
    scalar_restrictOpen _ _ 0 z₀
  have htime : (0 : ℝ) ∈ (RealTimeInterval.closed (-b) 0 hb0).carrier :=
    show (0 : ℝ) ∈ Icc (-b) 0 from ⟨by linarith, le_rfl⟩
  have hwinR : Icc (0 - (δ * (solutionOnRestrictOpen
      (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem)
      (standardCapWindow D)).scalar 0 z₀)⁻¹) 0 ⊆
        (RealTimeInterval.closed (-b) 0 hb0).carrier := by
    rw [hRs]
    intro u hu
    exact ⟨by linarith [hu.1], hu.2⟩
  have hlow : -b < 0 - (δ * ((solutionOnRestrictOpen
      (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem)
      (standardCapWindow D)).timeRestrict (RealTimeInterval.closed (-b) 0 hb0)).scalar 0
        z₀)⁻¹ := by
    rw [scalar_timeRestrict, hRs]
    linarith
  have hTn : ∀ n, T n ∈ (RealTimeInterval.closed 0 (T n) (hT0 n)).carrier :=
    fun n => show T n ∈ Icc 0 (T n) from ⟨hT0 n, le_rfl⟩
  have hcarS : ∀ n, b ≤ T n → (RealTimeInterval.closed (-b) 0 hb0).carrier ⊆
      (parabolicInterval (RealTimeInterval.closed 0 (T n) (hT0 n)) (T n) 1
        (hTn n)).carrier := by
    intro n hbn s hs
    have hs' : s ∈ Icc (-b) 0 := hs
    change parabolicTime (T n) 1 s ∈ Icc 0 (T n)
    simp only [parabolicTime, div_one]
    exact ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
  have hregS : ∀ n, b ≤ T n → (RealTimeInterval.closed (-b) 0 hb0).regular ⊆
      (parabolicInterval (RealTimeInterval.closed 0 (T n) (hT0 n)) (T n) 1
        (hTn n)).regular := by
    intro n hbn s hs
    have hs' : s ∈ Ioo (-b) 0 := hs
    change parabolicTime (T n) 1 s ∈ Ioo 0 (T n)
    simp only [parabolicTime, div_one]
    exact ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
  let S' : ℕ → SolutionOn (I := I3) (M := standardCapWindow D)
      (RealTimeInterval.closed (-b) 0 hb0) := fun n =>
    if h : b ≤ T n then
      (parabolicSolution (S n) (T n) 1 one_pos (hTn n)).timeRestrict
        (RealTimeInterval.closed (-b) 0 hb0)
    else (solutionOnRestrictOpen (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem)
      (standardCapWindow D)).timeRestrict (RealTimeInterval.closed (-b) 0 hb0)
  have hS'pos : ∀ n, b ≤ T n → S' n =
      (parabolicSolution (S n) (T n) 1 one_pos (hTn n)).timeRestrict
        (RealTimeInterval.closed (-b) 0 hb0) := fun n h => dite_eq_left h
  have hS' : ∀ n, IsSolutionOn (S' n) := by
    intro n
    by_cases h : b ≤ T n
    · rw [hS'pos n h]
      exact isSolutionOn_timeRestrict
        (parabolicSolution_isSolutionOn (S n) (hS n) (T n) 1 one_pos (hTn n))
        (hcarS n h) (hregS n h)
    · rw [show S' n = _ from dite_eq_right h]
      exact hS₀
  have hbev : ∀ᶠ n in atTop, b ≤ T n :=
    (hT.eventually (Ioi_mem_nhds hbT)).mono fun n h => le_of_lt h
  have hL5 := StandardSolution.eventually_shifted_window_metricDerivNormSupOn_lt
    (T₀ := T₀) hΘ (show 0 < T₀ - b by linarith) hQ hTΘ hT
    (g := fun n τ => (S n).base.metric τ) hclose (J := Icc (T₀ - b) T₀) subset_rfl
  have hconv : ∀ K : Set (standardCapWindow D), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
      ∀ᶠ n in atTop, ∀ τ ∈ (RealTimeInterval.closed (-b) 0 hb0).carrier,
        metricDerivNormSupOn K p ((S' n).base.metric τ)
          (((solutionOnRestrictOpen (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem)
            (standardCapWindow D)).timeRestrict (RealTimeInterval.closed (-b) 0 hb0)).base.metric
              τ) (StandardCap.metric.restrictOpen (standardCapWindow D)) < e := by
    intro K hK p e he
    filter_upwards [hL5 K hK p e he, hbev] with n hn hbn τ hτ
    have hτ' : τ ∈ Icc (-b) 0 := hτ
    have e1 : (S' n).base.metric τ =
        (S n).base.metric ((T₀ + τ) + (T n - T₀)) := by
      rw [hS'pos n hbn]
      change scaleMetric 1 one_pos ((S n).base.metric (parabolicTime (T n) 1 τ)) = _
      rw [scaleMetric_one_eq]
      congr 1
      simp only [parabolicTime, div_one]
      ring
    have e2 : ((solutionOnRestrictOpen (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos
        hT₀mem) (standardCapWindow D)).timeRestrict
          (RealTimeInterval.closed (-b) 0 hb0)).base.metric τ =
        (Q'.val.metric (T₀ + τ)).restrictOpen (standardCapWindow D) := by
      change (scaleMetric 1 one_pos (Q'.val.toSolutionOn.base.metric
        (parabolicTime T₀ 1 τ))).restrictOpen _ = _
      rw [scaleMetric_one_eq]
      simp only [parabolicTime, div_one]
      rfl
    rw [e1, e2]
    exact hn (T₀ + τ) ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
  have hscalar := SolutionOn.tendsto_scalar_of_metricDerivNormSupOn
    (StandardCap.metric.restrictOpen (standardCapWindow D)) hconv htime hz
  have hL4 := ((W.toRestrictOpen hU).timeRestrict (RealTimeInterval.closed (-b) 0 hb0) htime
    hwinR).eventually_strict_of_tendsto_flows_endpoint hS₀ hS' hlow (fun _ h => h)
    (fun _ h => h) (W.toRestrictOpen_strict hU hstrict) _ hconv hz hscalar
  filter_upwards [hL4, hbev] with n hn hbn
  intro o
  obtain ⟨W', horient, -⟩ := hn
  obtain ⟨oN'', hO''⟩ := hO o
  obtain ⟨oN', hO'⟩ := horient o oN'' hO''
  have hw : OrientedWitness (S' n) o δ standardModelKappa (z n) 0 := ⟨W', oN', hO'⟩
  rw [hS'pos n hbn] at hw
  have hw3 := (orientedWitness_paraSolution_iff (S n) o one_pos (hTn n) 0 (z n) δ
    standardModelKappa).mp (orientedWitness_of_timeRestrict (hcarS n hbn) hw)
  rwa [parabolicTime_zero] at hw3


private theorem eventually_orientedWitness_of_standard_close_endpoint
    {δ Θ D T₀ Λ r : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hΘ : Θ < 1)
    {Q : ℕ → StandardSolution} {Q' : StandardSolution}
    (hQ : ∀ K : Set (standardCapWindow D), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc 0 Θ,
        metricDerivNormSupOn K p (((Q i).val.metric t).restrictOpen (standardCapWindow D))
          ((Q'.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) < e)
    {T : ℕ → ℝ} (hT0 : ∀ n, 0 ≤ T n)
    (S : ∀ n, SolutionOn (I := I3) (M := standardCapWindow D)
      (RealTimeInterval.closed 0 (T n) (hT0 n)))
    (hS : ∀ n, IsSolutionOn (S n)) (hTΘ : ∀ n, T n ≤ Θ)
    (hclose : ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ τ ∈ Icc 0 (T n), ∀ i ≤ p,
      ∀ v : standardCapWindow D, metricDerivNorm i ((S n).base.metric τ)
        (((Q n).val.metric τ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e)
    (hT : Tendsto T atTop (𝓝 T₀)) {z : ℕ → standardCapWindow D} {z₀ : standardCapWindow D}
    (hz : Tendsto z atTop (𝓝 z₀))
    (hwit : ∀ o : TangentOrientationSection ThreeSpace,
      OrientedWitness Q'.val.toSolutionOn o (δ / 4) standardModelKappa z₀.val T₀)
    (hT₀ : 0 < T₀) (hR1 : 1 ≤ Q'.val.toSolutionOn.scalar T₀ z₀.val) (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ y (v : TangentSpace (𝓡 3) y),
      Λ⁻¹ * StandardCap.metric.inner y v v ≤ (Q'.val.metric T₀).inner y v v)
    (hz₀ : ‖z₀.val‖ ≤ r) (hD : r + 2 * (modelRadius δ + 1) * Real.sqrt Λ ≤ D) :
    ∀ᶠ n in atTop, ∀ o : TangentOrientationSection (standardCapWindow D),
      OrientedWitness (S n) o δ standardModelKappa (z n) (T n) := by
  have hT₀Θ : T₀ ≤ Θ := le_of_tendsto' hT hTΘ
  have hT₀1 : T₀ < 1 := hT₀Θ.trans_lt hΘ
  have hT₀mem : T₀ ∈ Q'.val.domain := by
    refine (mem_lifetimeInterval_carrier _ _ T₀).mpr ⟨hT₀.le, ?_⟩
    rw [Q'.lifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr (by linarith)
  obtain ⟨W, hstrict, hU, hO, hmargin⟩ :=
    StandardSolution.exists_strict_oriented_witness (x := z₀) hδ hδ1 hT₀mem hwit hR1 hΛ1
      hΛ hz₀ hD
  exact eventually_orientedWitness_of_strict_standard_witness_endpoint hδ hΘ hQ hT0 S hS hTΘ
    hclose hT hz hT₀mem W hstrict hU hO hmargin

theorem exists_uniform_orientedWitness_of_standard_close_endpoint {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    ∃ τQ : ℝ, 0 < τQ ∧ ∀ (Θ r : ℝ), Θ < 1 →
    ∃ (D : ℝ) (N : ℕ) (e : ℝ), r < D ∧ 0 < e ∧
    ∀ (Q : StandardSolution) (T : ℝ) (hT : 0 ≤ T), T ≤ Θ →
    ∀ (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 T hT)), IsSolutionOn S →
    (∀ τ ∈ Icc 0 T, ∀ i ≤ N, ∀ v : standardCapWindow D,
      metricDerivNorm i (S.base.metric τ)
        ((Q.val.metric τ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e) →
    ∀ (o : TangentOrientationSection (standardCapWindow D)) (z : standardCapWindow D),
      ‖z.val‖ < r → τQ ≤ T * S.scalar T z →
      OrientedWitness S o δ standardModelKappa z T := by
  obtain ⟨τQ, hτQ1, hage⟩ :=
    StandardSolution.exists_oriented_witness_of_age (ε := δ / 4) (by positivity) (by linarith)
  refine ⟨τQ, by linarith, fun Θ r hΘ => ?_⟩
  have hΘ' : max Θ 0 < 1 := max_lt hΘ one_pos
  have hlt : ENNReal.ofReal (max Θ 0) < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr hΘ'
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab (max Θ 0) (le_max_right _ _) hlt
  obtain ⟨Λ, hΛ1, C, L, -, -, hstd⟩ :=
    standard_metric_bounds_on_shorter_windows (max Θ 0) K (le_max_right _ _) hK
  have hΛ : ∀ (Q : StandardSolution), ∀ t ∈ Icc 0 Θ, ∀ y (v : TangentSpace (𝓡 3) y),
      Λ⁻¹ * StandardCap.metric.inner y v v ≤ (Q.val.metric t).inner y v v := by
    intro Q t ht y v
    have h := (hstd Q.val (max Θ 0) (le_max_right _ _) le_rfl (hlife Q) (hRm Q)).1 t
      ⟨ht.1, ht.2.trans (le_max_left _ _)⟩
    exact (h.2 y (mem_univ y) v).1
  set D := r + 2 * (modelRadius δ + 1) * Real.sqrt Λ with hDdef
  have hrD : r < D := by
    have : 0 < modelRadius δ := inv_pos.mpr (Real.sqrt_pos.mpr hδ)
    have : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr (by linarith)
    rw [hDdef]
    nlinarith
  refine ⟨D, ?_⟩
  by_contra hcon
  have hex : ∀ n : ℕ, ∃ (Q : StandardSolution) (T : ℝ) (hT : 0 ≤ T), T ≤ Θ ∧
      ∃ (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 T hT)), IsSolutionOn S ∧
      (∀ τ ∈ Icc 0 T, ∀ i ≤ n, ∀ v : standardCapWindow D,
        metricDerivNorm i (S.base.metric τ)
          ((Q.val.metric τ).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) v < 1 / ((n : ℝ) + 1)) ∧
      ∃ (o : TangentOrientationSection (standardCapWindow D)) (z : standardCapWindow D),
        ‖z.val‖ < r ∧ τQ ≤ T * S.scalar T z ∧
          ¬ OrientedWitness S o δ standardModelKappa z T := by
    intro n
    by_contra h
    refine hcon ⟨n, 1 / ((n : ℝ) + 1), hrD, by positivity, ?_⟩
    intro Q T hT hTΘ S hS hcl o z hz hag
    by_contra hw
    exact h ⟨Q, T, hT, hTΘ, S, hS, hcl, o, z, hz, hag, hw⟩
  choose Q T hT0 hTΘ S hS hcl o z hz hag hw using hex
  obtain ⟨p, hp, φ, hφ, hlim⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := Θ)).prod
    (isCompact_closedBall (0 : ThreeSpace) r)).tendsto_subseq (x := fun n => (T n, (z n).val))
    fun n => ⟨⟨hT0 n, hTΘ n⟩, mem_closedBall_zero_iff.mpr (hz n).le⟩
  obtain ⟨ρ, hρ, Q', hQ'⟩ := StandardSolution.exists_subseq_tendsto hΘ (Q ∘ φ)
  have hψ : StrictMono (φ ∘ ρ) := hφ.comp hρ
  have hTψ : Tendsto (fun n => T (φ (ρ n))) atTop (𝓝 p.1) :=
    ((continuous_fst.tendsto p).comp hlim).comp hρ.tendsto_atTop
  have hzr : ‖p.2‖ ≤ r := mem_closedBall_zero_iff.mp hp.2
  let z₀ : standardCapWindow D := ⟨p.2, show ‖p.2‖ < D + 1 by linarith⟩
  have hzψ : Tendsto (fun n => z (φ (ρ n))) atTop (𝓝 z₀) :=
    tendsto_subtype_rng.mpr (((continuous_snd.tendsto p).comp hlim).comp hρ.tendsto_atTop)
  have hcloseψ := eventually_forall_metricDerivNorm_lt_of_tendsto
    (g := fun n τ => (S (φ (ρ n))).base.metric τ)
    (h := fun n τ => ((Q (φ (ρ n))).val.metric τ).restrictOpen (standardCapWindow D))
    (A := fun n => Icc 0 (T (φ (ρ n)))) (N := fun n => φ (ρ n))
    (ε := fun n => 1 / (((φ (ρ n) : ℕ) : ℝ) + 1)) hψ.tendsto_atTop
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop)
    fun n => hcl (φ (ρ n))
  have hTmem : ∀ n, T (φ (ρ n)) ∈ Icc 0 Θ := fun n => ⟨hT0 _, hTΘ _⟩
  have hscal := StandardSolution.tendsto_scalar_of_close hΘ (hQ' D) hTmem hTψ
    (g := fun n => (S (φ (ρ n))).base.metric (T (φ (ρ n))))
    (fun p e he => (hcloseψ p e he).mono fun n hn i hi v =>
      hn _ ⟨hT0 _, le_rfl⟩ i hi v) hzψ
  have hagelim : τQ ≤ p.1 * Q'.val.toSolutionOn.scalar p.1 z₀.val :=
    ge_of_tendsto (hTψ.mul hscal) (Eventually.of_forall fun n => hag (φ (ρ n)))
  have hp1 : p.1 ∈ Icc 0 Θ := isClosed_Icc.mem_of_tendsto hTψ (Eventually.of_forall hTmem)
  have hp1lt : p.1 < 1 := hp1.2.trans_lt hΘ
  have hRpos : 0 < Q'.val.toSolutionOn.scalar p.1 z₀.val := by
    by_contra hneg
    have := mul_nonpos_of_nonneg_of_nonpos hp1.1 (le_of_not_gt hneg)
    linarith
  have hT₀ : 0 < p.1 := by
    rcases hp1.1.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hagelim
      linarith
    · exact h0
  have hR1 : 1 ≤ Q'.val.toSolutionOn.scalar p.1 z₀.val := by
    have := mul_le_mul_of_nonneg_right hp1lt.le hRpos.le
    linarith
  have hfin := eventually_orientedWitness_of_standard_close_endpoint hδ hδ1 hΘ (hQ' D)
    (fun n => hT0 (φ (ρ n))) (fun n => S (φ (ρ n))) (fun n => hS _) (fun n => hTΘ _)
    hcloseψ hTψ hzψ (fun o => hage Q' o z₀.val p.1 hp1.1 hp1lt hagelim) hT₀ hR1 hΛ1
    (hΛ Q' p.1 hp1) hzr le_rfl
  obtain ⟨n, hn⟩ := hfin.exists
  exact hw (φ (ρ n)) (hn (o (φ (ρ n))))

end Core

end DifferentialGeometry.PDE.RicciFlow
