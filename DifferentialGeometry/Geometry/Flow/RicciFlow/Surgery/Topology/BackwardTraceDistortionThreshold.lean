import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortionTerminal

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace Manifold
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe uM uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [T2Space M] {D : RealTimeInterval}

theorem scalar_le_four_mul_of_gradient_bound (S : SolutionOn (I := I) (M := M) D)
    {Cgrad : ℝ≥0} {qcan N t r : ℝ} {x y : M}
    (hgrad : ∀ w, qcan < S.scalar t w → ∀ v : TangentSpace I w,
      |scalarDifferential (I := I) S t w v| ≤
        Cgrad * S.scalar t w * Real.sqrt (S.scalar t w) *
          Real.sqrt ((S.base.metric t).inner w v v))
    (hN : 0 < N) (hxN : S.scalar t x ≤ N) (hqN : qcan ≤ N)
    (hr : (Cgrad : ℝ) * r * Real.sqrt N ≤ 1 / 4)
    (hy : y ∈ riemannianClosedBallOf (I := I) (S.base.metric t) x r) :
    S.scalar t y ≤ 4 * N := by
  set m := Real.sqrt N with hmdef
  have hm : 0 < m := Real.sqrt_pos.2 hN
  have hmsq : m ^ 2 = N := Real.sq_sqrt hN.le
  have hC : (0 : ℝ) ≤ Cgrad := Cgrad.coe_nonneg
  set r0 := max r 0 with hr0def
  have hr0 : 0 ≤ r0 := le_max_right _ _
  have hy0 : y ∈ riemannianClosedBallOf (I := I) (S.base.metric t) x r0 :=
    riemannianClosedBallOf_mono (I := I) _ _ (le_max_left _ _) hy
  have hr0b : (Cgrad : ℝ) * r0 * m ≤ 1 / 4 := by
    rcases le_total r 0 with h | h
    · rw [hr0def, max_eq_right h]
      norm_num
    · rwa [hr0def, max_eq_left h]
  set η := 1 / (16 * ((Cgrad : ℝ) + 1) * m) with hηdef
  have hη : 0 < η := by positivity
  have hηb : (Cgrad : ℝ) * η * m ≤ 1 / 16 := by
    rw [hηdef, show (Cgrad : ℝ) * (1 / (16 * ((Cgrad : ℝ) + 1) * m)) * m =
      (Cgrad : ℝ) / (16 * ((Cgrad : ℝ) + 1)) by field_simp]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨gam, hgam, hgam0, hgam1, hspeed⟩ :=
    exists_path_lintegral_speed_lt_of_mem_closedBall (I := I) (S.base.metric t) hr0 hη hy0
  have hcont : ContinuousOn (fun sig : ℝ => S.scalar t (gam sig)) (Icc 0 1) :=
    (((scalarSmoothOfSolution (I := I) S t).continuous).comp hgam.continuous).continuousOn
  have hkey : ∀ τ ∈ Icc (0 : ℝ) 1, (fun sig : ℝ => S.scalar t (gam sig)) τ ≤ 4 * N := by
    refine forall_le_of_no_crossing (B := 9 / 4 * N) (by linarith) hcont ?_
    intro uu vv h0u huv hv1 hge hstart hend
    have hsub : Icc uu vv ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc h0u hv1
    have hpos : ∀ w ∈ Icc uu vv, 0 < S.scalar t (gam w) := fun w hw =>
      lt_of_lt_of_le (by positivity) (hge w hw)
    have hqw : ∀ w ∈ Icc uu vv, qcan < S.scalar t (gam w) := fun w hw =>
      lt_of_lt_of_le (by linarith) (hge w hw)
    have hderiv : ∀ w ∈ Icc uu vv,
        HasDerivAt (fun sig : ℝ => (Real.sqrt (S.scalar t (gam sig)))⁻¹)
          (-(1 / (2 * Real.sqrt (S.scalar t (gam w))) *
              scalarDifferential (I := I) S t (gam w)
                (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))) /
              Real.sqrt (S.scalar t (gam w)) ^ 2) w := fun w hw =>
      hasDerivAt_inv_sqrt (hasDerivAt_scalar_comp (I := I) S t hgam w) (hpos w hw)
    have hbdd : ∀ w ∈ Icc uu vv,
        |-(1 / (2 * Real.sqrt (S.scalar t (gam w))) *
            scalarDifferential (I := I) S t (gam w)
              (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))) /
            Real.sqrt (S.scalar t (gam w)) ^ 2| ≤
          (Cgrad : ℝ) / 2 * Real.sqrt ((S.base.metric t).inner (gam w)
            (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
            (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))) := by
      intro w hw
      refine abs_deriv_inv_sqrt_le (hpos w hw) ?_
      have hgd := hgrad (gam w) (hqw w hw) (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
      refine hgd.trans_eq ?_
      ring
    have hbud := abs_sub_le_of_hasDerivAt_of_lintegral_le
      (f := fun sig : ℝ => (Real.sqrt (S.scalar t (gam sig)))⁻¹)
      (a := uu) (b := vv)
      (v := fun w : ℝ => Real.sqrt ((S.base.metric t).inner (gam w)
        (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
        (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))))
      huv hsub (by positivity) (by positivity) hderiv hbdd hspeed.le
    have hstart' : S.scalar t (gam uu) ≤ max (9 / 4 * N) (S.scalar t (gam 0)) := hstart
    rw [hgam0] at hstart'
    have hstart2 : S.scalar t (gam uu) ≤ 9 / 4 * N :=
      hstart'.trans (max_le le_rfl (hxN.trans (by linarith)))
    have hend' : 4 * N ≤ S.scalar t (gam vv) := hend
    have hsu : Real.sqrt (S.scalar t (gam uu)) ≤ 3 / 2 * m := by
      calc Real.sqrt (S.scalar t (gam uu)) ≤ Real.sqrt ((3 / 2 * m) ^ 2) :=
            Real.sqrt_le_sqrt (by rw [mul_pow, hmsq]; linarith)
        _ = 3 / 2 * m := Real.sqrt_sq (by positivity)
    have hsv : 2 * m ≤ Real.sqrt (S.scalar t (gam vv)) := by
      calc 2 * m = Real.sqrt ((2 * m) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (S.scalar t (gam vv)) :=
            Real.sqrt_le_sqrt (by rw [mul_pow, hmsq]; linarith)
    have hA : (3 / 2 * m)⁻¹ ≤ (Real.sqrt (S.scalar t (gam uu)))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.2 (hpos uu (left_mem_Icc.2 huv))) hsu
    have hB : (Real.sqrt (S.scalar t (gam vv)))⁻¹ ≤ (2 * m)⁻¹ :=
      inv_anti₀ (by positivity) hsv
    have hgap : (3 / 2 * m)⁻¹ - (2 * m)⁻¹ ≤ (Cgrad : ℝ) / 2 * (r0 + η) := by
      have := neg_abs_le ((Real.sqrt (S.scalar t (gam vv)))⁻¹ -
        (Real.sqrt (S.scalar t (gam uu)))⁻¹)
      linarith
    have hgapm : (3 / 2 * m)⁻¹ - (2 * m)⁻¹ = 1 / 6 * m⁻¹ := by
      field_simp
      ring
    rw [hgapm] at hgap
    have hmul := mul_le_mul_of_nonneg_right hgap hm.le
    rw [mul_assoc, inv_mul_cancel₀ hm.ne'] at hmul
    nlinarith
  have h1 := hkey 1 ⟨by norm_num, le_rfl⟩
  simp only [hgam1] at h1
  exact h1

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

private theorem scalar_le_four_mul_on_ball_of_gradient_bound (t : Icc (0 : ℝ) H.toHistory.horizon)
    (i : Fin H.eventCount) (hi : H.toHistory.activeStage t = i.castSucc)
    {Cgrad : ℝ≥0} {qcan N r : ℝ}
    (hgrad : ∀ w, qcan < (H.toHistory.event i).incoming.flow.scalar t w →
      ∀ v : TangentSpace I3 w,
        |Perelman.CanonicalNeighborhood.scalarDifferential (H.toHistory.event i).incoming.flow
          t w v| ≤
          Cgrad * (H.toHistory.event i).incoming.flow.scalar t w *
            Real.sqrt ((H.toHistory.event i).incoming.flow.scalar t w) *
            Real.sqrt (((H.toHistory.event i).incoming.flow.base.metric t).inner w v v))
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (hN : 0 < N)
    (hyN : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ N)
    (hqN : qcan ≤ N) (hr : (Cgrad : ℝ) * r * Real.sqrt N ≤ 1 / 4) :
    ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ 4 * N := by
  revert y
  rw [hi]
  intro y hyN x hx
  rw [ObservedHistory.stageMetric_castSucc_apply] at hyN hx ⊢
  have hx' : x ∈ riemannianClosedBallOf ((H.toHistory.event i).incoming.flow.base.metric t) y r :=
    le_of_lt (α := ENNReal) hx
  have : IsManifold I3 1 (H.stage i.castSucc).Carrier := IsManifold.of_le (n := ∞) (by decide)
  exact Perelman.CanonicalNeighborhood.scalar_le_four_mul_of_gradient_bound
    (H.toHistory.event i).incoming.flow hgrad hN hyN hqN hr hx'

private theorem scalar_le_four_mul_on_ball_of_gradient_bound_of_activeStage_eq_last
    (t : Icc (0 : ℝ) H.toHistory.horizon) (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    {Cgrad : ℝ≥0} {qcan N r : ℝ}
    (hgrad : ∀ w, qcan < (H.finalSlab h).flow.scalar t w →
      ∀ v : TangentSpace I3 w,
        |Perelman.CanonicalNeighborhood.scalarDifferential (H.finalSlab h).flow t w v| ≤
          Cgrad * (H.finalSlab h).flow.scalar t w *
            Real.sqrt ((H.finalSlab h).flow.scalar t w) *
            Real.sqrt (((H.finalSlab h).flow.base.metric t).inner w v v))
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (hN : 0 < N)
    (hyN : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ N)
    (hqN : qcan ≤ N) (hr : (Cgrad : ℝ) * r * Real.sqrt N ≤ 1 / 4) :
    ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ 4 * N := by
  revert y
  rw [hlastA]
  intro y hyN x hx
  rw [ObservedHistory.stageMetric_last_of_lt (h := h)] at hyN hx ⊢
  have hx' : x ∈ riemannianClosedBallOf ((H.finalSlab h).flow.base.metric t) y r :=
    le_of_lt (α := ENNReal) hx
  have : IsManifold I3 1 (H.stage (Fin.last H.eventCount)).Carrier :=
    IsManifold.of_le (n := ∞) (by decide)
  exact Perelman.CanonicalNeighborhood.scalar_le_four_mul_of_gradient_bound
    (H.finalSlab h).flow hgrad hN hyN hqN hr hx'

private theorem threshold_constants {Ctime : ℝ≥0} {M c : ℝ} {phi : ℝ → ℝ} (hM : 1 ≤ 4 * M)
    (hc : 0 < c) (hctime : 8 * Ctime * c ^ 2 ≤ 1)
    (hcpinch : 3072 * (1 + phi 1 + phi 0) ^ 2 * c ^ 4 ≤ 1) :
    Ctime * (4 * M) * (c / Real.sqrt M) ^ 2 ≤ 1 / 2 ∧
      (c / Real.sqrt M) ^ 4 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * M)) ^ 2 ≤ 1 ∧
      Ctime * (4 * M) * (c ^ 2 / M) ≤ 1 / 2 ∧ 4 * (4 * M) * (c ^ 2 / M) = 16 * c ^ 2 ∧
      Real.sqrt (8 * (4 * M)) *
          Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * M)) * (c ^ 2 / M)) *
          (c / Real.sqrt M) =
        Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) := by
  have hMpos : 0 < M := by linarith
  have hsq : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have hsqsq : Real.sqrt M ^ 2 = M := Real.sq_sqrt hMpos.le
  have hC : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
  have hr2 : (c / Real.sqrt M) ^ 2 = c ^ 2 / M := by rw [div_pow, hsqsq]
  have hr4 : (c / Real.sqrt M) ^ 4 = c ^ 4 / M ^ 2 := by
    rw [show (c / Real.sqrt M) ^ 4 = ((c / Real.sqrt M) ^ 2) ^ 2 by ring, hr2, div_pow]
    ring
  have htime : Ctime * (4 * M) * (c ^ 2 / M) ≤ 1 / 2 := by
    field_simp
    nlinarith
  refine ⟨by rw [hr2]; exact htime, ?_, htime, by field_simp; ring, ?_⟩
  · rw [hr4]
    have hK : (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * M)) ^ 2 =
        3072 * (1 + phi 1 + phi 0) ^ 2 * M ^ 2 := by
      have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      ring_nf
      rw [h3]
      ring
    rw [hK]
    field_simp
    nlinarith
  · have h32 : Real.sqrt (8 * (4 * M)) = Real.sqrt 32 * Real.sqrt M := by
      rw [show 8 * (4 * M) = 32 * M by ring, Real.sqrt_mul (by norm_num)]
    have harg : 9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * M)) * (c ^ 2 / M) =
        288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2 := by
      field_simp
      ring
    rw [h32, harg]
    field_simp

theorem exists_isParabolicallyRmControlledBall_or_capWindowPoint_of_scalar_le
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime Cgrad : ℝ≥0} {qcan M c Dcap θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (i : Fin H.eventCount)
    (hi : H.toHistory.activeStage t = i.castSucc)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hqM : qcan ≤ M) (hM : 1 ≤ 4 * M)
    (hyM : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ M)
    (hc : 0 < c) (hcgrad : (Cgrad : ℝ) * c ≤ 1 / 4) (hctime : 8 * Ctime * c ^ 2 ≤ 1)
    (hcpinch : 3072 * (1 + phi 1 + phi 0) ^ 2 * c ^ 4 ≤ 1)
    {u : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hu : (u : ℝ) = t - c ^ 2 / M)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan t)
    (hgrad : ∀ w, qcan < (H.toHistory.event i).incoming.flow.scalar t w →
      ∀ v : TangentSpace I3 w,
        |Perelman.CanonicalNeighborhood.scalarDifferential (H.toHistory.event i).incoming.flow
          t w v| ≤
          Cgrad * (H.toHistory.event i).incoming.flow.scalar t w *
            Real.sqrt ((H.toHistory.event i).incoming.flow.scalar t w) *
            Real.sqrt (((H.toHistory.event i).incoming.flow.base.metric t).inner w v v))
    {Dstar : ℝ} (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 16 * c ^ 2 ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd +
      Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) < Dcap) :
    H.toHistory.isParabolicallyRmControlledBall t y (c / Real.sqrt M) ∨
      H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap := by
  by_cases hcw : H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap
  · exact Or.inr hcw
  refine Or.inl ?_
  have hMpos : 0 < M := by linarith
  have hsq : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have htu : (t : ℝ) - u = c ^ 2 / M := by rw [hu]; ring
  obtain ⟨htime, hrM, htime', hθ', hwin'⟩ :=
    threshold_constants (Ctime := Ctime) (phi := phi) hM hc hctime hcpinch
  have hne : H.toHistory.activeStage t ≠ Fin.last H.eventCount := by
    rw [hi]
    exact Fin.castSucc_ne_last i
  have hspace : ∀ w ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
      y (c / Real.sqrt M),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) w ≤ 4 * M :=
    H.scalar_le_four_mul_on_ball_of_gradient_bound t i hi hgrad y hMpos hyM hqM
      (by rw [mul_assoc, div_mul_cancel₀ c hsq.ne']; exact hcgrad)
  have hcur : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t := fun j hj => by
    have : j = i := Fin.castSucc_injective _ (hj.trans hi)
    subst this
    exact hcurrent
  apply H.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace hphi hpinch
    (M := 4 * M) hut (by positivity) (by rw [hu, div_pow, Real.sq_sqrt hMpos.le])
    (fun h => absurd h hne) y hslabs hcur (fun _ h => absurd h hne) hM (by linarith) hspace
    htime hrM
  intro x hx
  by_contra hn
  apply hcw
  apply H.capWindowPoint_of_ball_point_without_trace records hcan hscale hacc hphi hpinch hut i
    hi y x hx (not_nonempty_iff.mp hn) hslabs hcurrent hM (by linarith) hspace
    (hDstar := hDstar) (hDmodel := hDmodel)
  · rw [htu]
    exact htime'
  · rw [htu, hθ']
    exact hθ
  · rw [htu, hwin']
    exact hwin

theorem exists_isParabolicallyRmControlledBall_or_capWindowPoint_of_scalar_le_of_activeStage_eq_last
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime Cgrad : ℝ≥0} {qcan M c Dcap θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hfinalPinch : Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
      (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hqM : qcan ≤ M) (hM : 1 ≤ 4 * M)
    (hyM : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ M)
    (hc : 0 < c) (hcgrad : (Cgrad : ℝ) * c ≤ 1 / 4) (hctime : 8 * Ctime * c ^ 2 ≤ 1)
    (hcpinch : 3072 * (1 + phi 1 + phi 0) ^ 2 * c ^ 4 ≤ 1)
    {u : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hu : (u : ℝ) = t - c ^ 2 / M)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hfinal : ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime
      qcan t)
    (hgrad : ∀ w, qcan < (H.finalSlab h).flow.scalar t w →
      ∀ v : TangentSpace I3 w,
        |Perelman.CanonicalNeighborhood.scalarDifferential (H.finalSlab h).flow t w v| ≤
          Cgrad * (H.finalSlab h).flow.scalar t w *
            Real.sqrt ((H.finalSlab h).flow.scalar t w) *
            Real.sqrt (((H.finalSlab h).flow.base.metric t).inner w v v))
    {Dstar : ℝ} (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 16 * c ^ 2 ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd +
      Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) < Dcap) :
    H.toHistory.isParabolicallyRmControlledBall t y (c / Real.sqrt M) ∨
      H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap := by
  by_cases hcw : H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap
  · exact Or.inr hcw
  refine Or.inl ?_
  have hMpos : 0 < M := by linarith
  have hsq : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have htu : (t : ℝ) - u = c ^ 2 / M := by rw [hu]; ring
  obtain ⟨htime, hrM, htime', hθ', hwin'⟩ :=
    threshold_constants (Ctime := Ctime) (phi := phi) hM hc hctime hcpinch
  have hspace : ∀ w ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
      y (c / Real.sqrt M),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) w ≤ 4 * M :=
    H.scalar_le_four_mul_on_ball_of_gradient_bound_of_activeStage_eq_last t h hlastA hgrad y
      hMpos hyM hqM (by rw [mul_assoc, div_mul_cancel₀ c hsq.ne']; exact hcgrad)
  have hcur : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t := fun j hj =>
    absurd (hj.trans hlastA) (Fin.castSucc_ne_last j)
  apply H.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace hphi hpinch
    (M := 4 * M) hut (by positivity) (by rw [hu, div_pow, Real.sq_sqrt hMpos.le])
    (fun _ => ⟨h, hfinalPinch⟩) y hslabs hcur (fun _ _ => hfinal) hM (by linarith) hspace
    htime hrM
  intro x hx
  by_contra hn
  apply hcw
  apply H.capWindowPoint_of_ball_point_without_trace_of_activeStage_eq_last records hcan hscale
    hacc hphi hpinch hut h hlastA hfinalPinch y x hx (not_nonempty_iff.mp hn) hslabs hfinal hM
    (by linarith) hspace (hDstar := hDstar) (hDmodel := hDmodel)
  · rw [htu]
    exact htime'
  · rw [htu, hθ']
    exact hθ
  · rw [htu, hwin']
    exact hwin

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
