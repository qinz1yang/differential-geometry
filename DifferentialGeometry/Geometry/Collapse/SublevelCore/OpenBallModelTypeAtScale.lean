import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallSublevelType
import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointNormalFlowOpenCore
import DifferentialGeometry.Geometry.Collapse.SublevelCore.RadialClausesAtScale
import DifferentialGeometry.Geometry.Collapse.SublevelCore.BufferedMapsAtScale
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirectionsApplications
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.RadialFunctionAtScaleApplications

/-!
# LC57/LC61, noncompact branch, from LC56 at one fixed scale: every open ball is the model

Master207A, A:23106 (LC57) and A:23460 (LC61), the branch of a NONCOMPACT model `(N, g, n)` with
`sec ≥ 0`. The data are LC56's items, unbundled: (1) pointed Gromov–Hausdorff convergence
`(M_i, p_i) → (N, n)` with `p_i = j i n`; (2) actual partial diffeomorphisms `j i : N ⇀ M i` with
the A1 encoding of the exhaustion and `C¹` convergence (per radius, after a shift, of the pullbacks
`pullbackMetricOn`); (3) a supplied LC21 cone package `(C, o)` of `(N, n)`; (4) the separate
curvature bounds `sec_{g_i} ≥ -H_i⁻²` on `B(p_i, H_i)`, `H_i → ∞`.

Conclusion: there is `R₀ > 0` such that for every fixed `R ≥ R₀` one tail has, for every
`ρ ∈ [1/5, 2]`, a diffeomorphism of the OPEN distance ball `B(p_i, ρ R)` (original metric) onto the
model `N` (an open partial diffeomorphism with target everything).

Proof at the fixed scale `R` (rescaled instances supplied by name):
* LC54 with open cores (`exists_point_outward_normalFlow_openCore`): field `V`, coordinate `u`,
  `int {u ≤ T} ≅ N`;
* LC30 at `R` on the model (`exists_point_distance_core_function_at_scale`): `ζ`;
* LC57 (1)–(2) (`exists_scale_eventually_cone_radial_witnesses`): `η_i`;
* GAP A2 (`exists_shifted_buffered_maps_at_scale`): the buffered LC50 data on `B(n, 11R)`;
* GAP B (`radialScaled_field_pairing_le`): the collar pairing of `R • V` at `R⁻² g`;
* `eventually_open_ball_sublevel_type`: `B_R(p_i, ρ) ≅ int {u ≤ ρ'}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Manifold
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type} [m : MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N]
  [ConnectedSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)]
  [IsRiemannianManifold I N] [hNc : CompleteSpace N]
  [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]
  [T2Space (TangentBundle I N)]
  {M : ℕ → Type} [mM : ∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [∀ i, IsRiemannianManifold I (M i)] [hMc : ∀ i, CompleteSpace (M i)]
  [∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

/-- Shifting the index of an eventual statement. -/
theorem eventually_atTop_of_eventually_add_nat {P : ℕ → Prop} (i₀ : ℕ)
    (h : ∀ᶠ k in atTop, P (k + i₀)) : ∀ᶠ i in atTop, P i := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp h
  refine eventually_atTop.mpr ⟨K + i₀, fun i hi => ?_⟩
  have h' := hK (i - i₀) (by omega)
  rwa [Nat.sub_add_cancel (by omega : i₀ ≤ i)] at h'

/-- **LC57/LC61 noncompact branch from LC56 at a fixed scale.** For a complete connected
noncompact model with `sec ≥ 0`, LC56's data (pointed convergence with `p_i = j i n`, the A1
maps, a cone package, separate curvature bounds) give `R₀ > 0` such that for every `R ≥ R₀` one
tail has every open ball `B(p_i, ρ R)`, `ρ ∈ [1/5, 2]`, diffeomorphic to the model `N`. -/
theorem exists_scale_eventually_open_ball_model_type [NoncompactSpace N] {mdim : ℕ}
    (hdim : Module.finrank ℝ E = mdim + 1) (g : SmoothRiemannianMetric I N)
    (hNorm : IsMetricNorm (I := I) (M := N) g) (hsec : ∀ x, SectionalBoundedBelowAt g x 0)
    (n : N) {C : Type} [MetricSpace C] {o : C} (Hc : RadialConeData o)
    (hcone : ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N C (m.rescale R⁻¹ (inv_pos.mpr hR)) _ n o τ))
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i)) (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (hGH : PointedGHConverges (fun i => j i n) n)
    (hC1 : ∀ r : ℝ, 0 < r → ∃ i₀ : ℕ, ∃ hsub : ∀ k,
      ((⟨Metric.ball n r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens N) : Set N) ⊆
        (j (k + i₀)).source,
      ∀ C : Set (⟨Metric.ball n r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens N),
        IsCompact C → MetricCPConvergenceOn C 1
          (fun k => PartialDiffeomorph.pullbackMetricOn (j (k + i₀)) _ (hsub k) (gSeq (k + i₀)))
          (g.restrictOpen _) (g.restrictOpen _))
    (Hb : ℕ → ℝ) (hHb : Tendsto Hb atTop atTop)
    (hsecM : ∀ i, ∀ y ∈ Metric.ball (j i n) (Hb i),
      SectionalBoundedBelowAt (gSeq i) y (-((Hb i)⁻¹ ^ 2))) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
      ∃ Ψ : PartialDiffeomorph I I (M i) N ∞,
        Ψ.source = Metric.ball (j i n) (ρ * R) ∧ Ψ.target = univ := by
  -- LC54 with open cores, in the original metric
  obtain ⟨V, ℓ, hℓ, A₂, hA₂, hVB, hVdir, u, hu, hucpt, -, hsmooth, hdu, hcore⟩ :=
    exists_point_outward_normalFlow_openCore g hNorm
      (fun x => (sectionalBoundedBelowAt_zero_iff g x).mp (hsec x)) n
  set T₀ : ℝ := ℓ + 1 with hT₀def
  obtain ⟨B₀, hB₀⟩ := (hucpt T₀).isBounded.subset_ball n
  -- thresholds: the model cone map for `ζ`, and LC57 (1)–(2) for `η_i`
  set τ : ℝ := radialSmoothingConeError ((1 / 64) / 4) / 2 with hτdef
  have hrs : 0 < radialSmoothingConeError ((1 / 64 : ℝ) / 4) :=
    radialSmoothingConeError_pos (by norm_num)
  have hrs1 : radialSmoothingConeError ((1 / 64 : ℝ) / 4) ≤ 1 / 600 := min_le_left _ _
  obtain ⟨R₁, hR₁⟩ := hcone τ (by positivity) (by linarith)
  have hmetricN := riemannianEDistOf_eq_ofReal_dist g hNorm
  have hmetricM : ∀ i a b, riemannianEDistOf (gSeq i) a b = ENNReal.ofReal (dist a b) :=
    fun i => riemannianEDistOf_eq_ofReal_dist (gSeq i) (hSeqNorm i)
  obtain ⟨R₂, -, hG1⟩ := exists_scale_eventually_cone_radial_witnesses (M := M) gSeq hmetricM
    hGH Hc hcone Hb hHb hsecM (δ := 1 / 2) (ε := ((1 / 64 : ℝ≥0) : ℝ)) (e := 1 / 80)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max (max R₁ R₂) (max (4 / 3 * A₂ + 1) (2 * B₀ + 1)),
    lt_of_lt_of_le (by linarith) (le_max_right _ _ |>.trans' (le_max_left _ _)),
    fun R hRR => ?_⟩
  have hR1 : R₁ ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hRR)
  have hR2 : R₂ ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hRR)
  have hRA : 4 / 3 * A₂ + 1 ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hRR)
  have hRB : 2 * B₀ + 1 ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hRR)
  have hR : 0 < R := by linarith
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  -- `ζ`: LC30 at scale `R` on the model
  have hsecN : ∀ y ∈ Metric.ball n (400 * R),
      SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * R⁻¹ ^ 2)) := fun y _ =>
    (hsec y).mono (by have := sq_nonneg R⁻¹; nlinarith)
  obtain ⟨ζ, hζclose, hζlip, Wζ, hWζ, hcollarW, hζW⟩ :=
    exists_point_distance_core_function_at_scale g hmetricN hR (hR₁ R hR hR1).some Hc hsecN
      (by linarith)
  -- `η_i`: LC57 (1)–(2) at scale `R`, as the core theorems' inputs
  let Q : ∀ i, (M i → ℝ) → Prop := fun i F =>
    letI := (mM i).rescale R⁻¹ (inv_pos.mpr hR)
    let gR : SmoothRiemannianMetric I (M i) :=
      scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (gSeq i)
    (1 / 80 : ℝ) < 1 / 40 ∧ (∀ x, |F x - dist (j i n) x| < 1 / 80) ∧
      LipschitzWith (1 / 64 : ℝ≥0) (fun x => F x - dist (j i n) x) ∧
      ∃ W : Set (M i), IsOpen W ∧ (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ W) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F W ∧
        ∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 →
          (1 - ((1 / 64 : ℝ≥0) : ℝ)) ^ 2 ≤ gR.inner x (gradientFun (I := I) gR F x)
            (gradientFun (I := I) gR F x)
  have hQ : ∀ᶠ i in atTop, ∃ F, Q i F := by
    filter_upwards [hG1 R hR hR2] with i hi
    obtain ⟨-, F, -, hFO, hFclose, -, hFdiff, -, -, hFgrad, -⟩ := hi
    exact ⟨F, core_clauses_of_radial_clauses_at_scale (gSeq i) hR (j i n) (by norm_num)
      (by norm_num) ⟨hFO, hFclose, hFdiff, fun q hq => (hFgrad q hq).1⟩⟩
  let η : ∀ i, M i → ℝ := fun i =>
    @dite _ (∃ F, Q i F) (Classical.propDecidable _) (fun h => h.choose) (fun _ _ => 0)
  have hηQ : ∀ᶠ i in atTop, Q i (η i) := by
    filter_upwards [hQ] with i hi
    have hηi : η i = hi.choose := dite_eq_left hi
    rw [hηi]
    exact hi.choose_spec
  -- the buffered LC50 data at scale `R`
  obtain ⟨i₀, hsub, hU, hsrc, hpull, hconvR, hball⟩ :=
    exists_shifted_buffered_maps_at_scale g gSeq n j hC1 hR
  have hnU : n ∈ Metric.ball n (11 * R) := Metric.mem_ball_self (by positivity)
  have hT₀pos : 0 < T₀ := by rw [hT₀def]; linarith
  refine (fun hstep => ?_) (eventually_open_ball_sublevel_type
    (mN := m.rescale R⁻¹ hRi) (rbN := radialScaledBundle g R⁻¹ hRi)
    (rmN := radialScaledManifold (m := m) g hmetricN R⁻¹ hRi)
    (cN := (m.rescale_completeSpace_iff R⁻¹ hRi).mpr hNc)
    (crN := radialScaledContinuous g R⁻¹ hRi)
    (M := fun k => M (k + i₀)) (mM := fun k => (mM (k + i₀)).rescale R⁻¹ hRi)
    (rbM := fun k => radialScaledBundle (gSeq (k + i₀)) R⁻¹ hRi)
    (rmM := fun k => radialScaledManifold (m := mM (k + i₀)) (gSeq (k + i₀)) (hmetricM (k + i₀))
      R⁻¹ hRi)
    (cM := fun k => ((mM (k + i₀)).rescale_completeSpace_iff R⁻¹ hRi).mpr (hMc (k + i₀)))
    (crM := fun k => radialScaledContinuous (gSeq (k + i₀)) R⁻¹ hRi)
    (T₀ := T₀) (Wu := {x | 0 < u x}) (ε := (1 / 64 : ℝ≥0))
    hdim (scaleMetric (R⁻¹ ^ 2) (pow_pos hRi 2) g) (isMetricNorm_of_riemannianBundle _)
    ⟨Metric.ball n (11 * R), Metric.isOpen_ball⟩ ⟨n, hnU⟩ ?hbuf
    (fun k => scaleMetric (R⁻¹ ^ 2) (pow_pos hRi 2)
      (PartialDiffeomorph.pullbackMetricOn (j (k + i₀)) _ (hsub k) (gSeq (k + i₀))))
    (fun k => scaleMetric (R⁻¹ ^ 2) (pow_pos hRi 2) (gSeq (k + i₀)))
    (fun k => isMetricNorm_of_riemannianBundle _)
    (fun k => (openSubtypePartialDiffeomorph I _ hU).trans (j (k + i₀))) hsrc hpull ?hconv
    ?hεN hζclose hζlip hWζ hcollarW hζW (fun x => R • V x) ?hVB ?hVdir hu hucpt ?hT₀
    (isOpen_lt continuous_const hu) ?hWuT ?huW ?hVW ?huV ?hε (fun k => η (k + i₀))
    (fun _ => 1 / 80) ?hη)
  case hbuf =>
    intro x hx
    apply hball
    have hx' : R⁻¹ * dist x n ≤ 10 := hx
    rw [Metric.mem_closedBall]
    have h10 : dist x n ≤ 10 * R := by
      have := mul_le_mul_of_nonneg_left hx' hR.le
      rwa [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, mul_comm] at this
    exact h10
  case hconv => exact hconvR
  case hεN => rw [Real.coe_toNNReal _ (by norm_num)]
  case hVB =>
    intro x _ _
    change R⁻¹ ^ 2 * g.inner x (R • V x) (R • V x) ≤ 4
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hV := hVB x
    have hR2 : R⁻¹ ^ 2 * (R * (R * g.inner x (V x) (V x))) = g.inner x (V x) (V x) := by
      field_simp
    linarith
  case hVdir =>
    intro x h1 _
    have h1' : 3 / 4 < R⁻¹ * dist n x := h1
    have hd : A₂ ≤ dist n x := by
      have h3 : 3 / 4 * R < dist n x := by
        have := mul_lt_mul_of_pos_left h1' hR
        rwa [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, mul_comm] at this
      linarith
    exact radialScaled_field_pairing_le g hNorm hR n x (V x) (hVdir x hd)
  case hT₀ =>
    intro x hx
    have hb := hB₀ hx
    rw [Metric.mem_ball] at hb
    change R⁻¹ * dist x n < 1 / 2
    have hlt : dist x n < R / 2 := by linarith
    calc R⁻¹ * dist x n < R⁻¹ * (R / 2) := mul_lt_mul_of_pos_left hlt hRi
      _ = 1 / 2 := by field_simp
  case hWuT => exact fun x hx => lt_of_lt_of_le hT₀pos hx
  case huW => exact hsmooth
  case hVW => exact (R • V).contMDiff.contMDiffOn
  case huV =>
    intro x hx
    rw [map_smul, hdu x (by rw [hT₀def] at hx; linarith), smul_eq_mul, mul_one]
    exact hR
  case hε => norm_num
  case hη =>
    filter_upwards [(tendsto_add_atTop_nat i₀).eventually hηQ] with k hk
    exact hk
  obtain ⟨T₁, hT₁, hfin⟩ := hstep
  obtain ⟨Ψb, hΨbs, hΨbt⟩ := hcore ((T₀ + T₁) / 2) (by linarith)
  refine eventually_atTop_of_eventually_add_nat i₀ (P := fun i => ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
    ∃ Ψ : PartialDiffeomorph I I (M i) N ∞,
      Ψ.source = Metric.ball (j i n) (ρ * R) ∧ Ψ.target = univ) ?_
  filter_upwards [hfin] with k hk
  intro ρ hρ
  obtain ⟨Ψ, hΨs, hΨt⟩ := hk ρ hρ ((T₀ + T₁) / 2) ⟨by linarith, by linarith⟩
  have hball' : @Metric.ball (M (k + i₀)) ((mM (k + i₀)).rescale R⁻¹ hRi).toPseudoMetricSpace
      (j (k + i₀) n) ρ = Metric.ball (j (k + i₀) n) (ρ * R) := by
    have h := MetricSpace.rescale_ball (mM (k + i₀)) R⁻¹ hRi (j (k + i₀) n) (ρ * R)
    rwa [show R⁻¹ * (ρ * R) = ρ by field_simp] at h
  refine ⟨Ψ.trans Ψb, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source, hΨs, hΨbs]
    refine (inter_eq_left.mpr fun y hy => ?_).trans hball'
    have hy' : y ∈ Ψ.source := by rw [hΨs]; exact hy
    have h := Ψ.toPartialEquiv.map_source hy'
    rw [hΨt] at h
    exact h
  · apply eq_univ_of_forall
    intro w
    have hw : w ∈ Ψb.target := by rw [hΨbt]; exact mem_univ w
    refine ⟨hw, ?_⟩
    have h := Ψb.toPartialEquiv.map_target hw
    change Ψb.symm w ∈ Ψ.target
    rw [hΨt]
    rw [hΨbs] at h
    exact h

end DifferentialGeometry.Geometry.Collapse
