import DifferentialGeometry.Geometry.Metric.Family.QuadraticBounds
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Boundary
import DifferentialGeometry.Geometry.Metric.Comparison.CurveCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierLowerSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1Regularity
import DifferentialGeometry.Analysis.Calculus.PartialDerivative.Parameter
import DifferentialGeometry.Topology.Manifold.CurveIntervalExtension

noncomputable section
open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

omit [I.Boundaryless] [T2Space M] in
private theorem action_lower_on_compact_range
    (S : SolutionOn (I := I) (M := M) D) (T a b C : ℝ) (hab : a ≤ b)
    (Q : Set M) (hpot : ∀ r ∈ Icc a b, ∀ z ∈ Q, C ≤ 2 * r ^ 2 * S.scalar (T - r ^ 2) z)
    (γ : ℝ → M) (hQ : MapsTo γ (Icc a b) Q)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T γ) volume a b) :
    C * (b - a) ≤ lRegularizedAction S T γ a b := by
  have hh := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := C)) hint
    (fun r hr => (hpot r hr (γ r) (hQ hr)).trans (by
      change _ ≤ (1 / 2 : ℝ) * _ + _
      have hkin := metric_inner_self_nonneg (S.base.metric (T - r ^ 2)) (γ r) (lVelocity γ r)
      linarith))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm, lRegularizedAction] using hh

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedMinC1_to_closed_set_of_compact_action_sublevel_of_spatial_derivatives [TopologicalSpace.MetrizableSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b : ℝ} (hab : a < b)
    (U : Set ℝ) (hU : U ⊆ D.carrier)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ U)
    (hreg : ∀ r ∈ Ioo a b, T - r ^ 2 ∈ D.regular)
    (hGramFd : ∀ p : M, ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (fun y : E => chartGramOp (I := I) S.family p (z.1, y)) z.2)
      (U ×ˢ interior (extChartAt I p).target))
    (hScalFd : ∀ p : M, ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) p (S.scalar z.1)) z.2)
      (U ×ˢ interior (extChartAt I p).target))
    (x : M) (A : Set M) (hA : IsClosed A) (α₀ : ℝ → M) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) I 1 α₀)
    (hstart : α₀ a = x) (hend : α₀ b ∈ A)
    (Q : Set M) (hQ : IsCompact Q)
    (hconf : ∀ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α →
      α a = x → α b ∈ A → lRegularizedAction S T α a b ≤ lRegularizedAction S T α₀ a b →
      MapsTo α (Icc a b) Q) :
    ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η a = x ∧ η b ∈ A ∧
      MapsTo η (Icc a b) Q ∧
      ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ a = x → δ b ∈ A →
        lRegularizedAction S T η a b ≤ lRegularizedAction S T δ a b := by
  classical
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  have hcarrier (r : ℝ) (hr : r ∈ Icc a b) : T - r ^ 2 ∈ D.carrier := hU (htime r hr)
  have hint (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α) :
      IntervalIntegrable (lRegularizedLagrangian S T α) volume a b :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier S hS.smoothMetric
      ⟨hS.scalarCont⟩ T a b hab.le α hα.contMDiffOn hcarrier
  obtain ⟨C, hC⟩ := lScalar_lower_compact S ⟨hS.scalarCont⟩ T a b
    (fun r hr => hcarrier r (by simpa only [uIcc_of_le hab.le] using hr)) Q hQ
  have hpot : ∀ r ∈ Icc a b, ∀ z ∈ Q, C ≤ 2 * r ^ 2 * S.scalar (T - r ^ 2) z := by
    simpa only [uIcc_of_le hab.le] using hC
  let A₀ := lRegularizedAction S T α₀ a b
  let costs : Set ℝ := {r | ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧ α a = x ∧ α b ∈ A ∧
    lRegularizedAction S T α a b = r ∧ r ≤ A₀}
  have hseed : A₀ ∈ costs := ⟨α₀, hα₀, hstart, hend, rfl, le_rfl⟩
  have hcosts : costs.Nonempty := ⟨A₀, hseed⟩
  have hbdd : BddBelow costs := by
    refine ⟨C * (b - a), ?_⟩
    rintro r ⟨α, hα, ha, hb, rfl, hact⟩
    exact action_lower_on_compact_range S T a b C hab.le Q hpot α (hconf α hα ha hb hact) (hint α hα)
  have hbelow (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α) (ha : α a = x) (hb : α b ∈ A) :
      sInf costs ≤ lRegularizedAction S T α a b := by
    by_cases hcost : lRegularizedAction S T α a b ≤ A₀
    · exact csInf_le hbdd ⟨α, hα, ha, hb, rfl, hcost⟩
    · exact (csInf_le hbdd hseed).trans (le_of_not_ge hcost)
  obtain ⟨values, _, hlim, hvalues⟩ := exists_seq_tendsto_sInf hcosts hbdd
  choose α hα hαa hαb hval hact using hvalues
  have hαQ (n : ℕ) : MapsTo (α n) (Icc a b) Q :=
    hconf (α n) (hα n) (hαa n) (hαb n) (by rw [hval n]; exact hact n)
  let J : Set ℝ := (fun r : ℝ => T - r ^ 2) '' Icc a b
  have hJ : IsCompact J := isCompact_Icc.image (continuous_const.sub (continuous_id.pow 2))
  have hJD : J ⊆ D.carrier := by rintro _ ⟨r, hr, rfl⟩; exact hcarrier r hr
  let gRef := S.base.metric (T - a ^ 2)
  obtain ⟨c, hc, hmetric⟩ := hS.smoothMetric.metric_lower_on_compact_time hJ hJD hQ gRef
  let B := 2 * (A₀ - C * (b - a)) / c
  have henergy (n : ℕ) : curveEnergy gRef (α n) a b ≤ B := by
    have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn gRef (hα n).contMDiffOn (a := a) (b := b)
    have href : IntervalIntegrable (fun r => gRef.inner (α n r) (lVelocity (α n) r) (lVelocity (α n) r)) volume a b := by
      apply IntegrableOn.intervalIntegrable
      simpa only [uIcc_of_le hab.le, lVelocity] using hE
    have hh := lRegularizedAction_ge_reference_energy_add_constant S T (α n) gRef a b c C hab.le
      (fun r hr => hmetric (T - r ^ 2) ⟨r, hr, rfl⟩ (α n r) (hαQ n hr) (lVelocity (α n) r))
      (fun r hr => hpot r hr (α n r) (hαQ n hr)) href (hint (α n) (hα n))
    rw [intervalIntegral.integral_const_mul] at hh
    change c / 2 * curveEnergy gRef (α n) a b + C * (b - a) ≤ _ at hh
    apply (le_div_iff₀ hc).mpr
    have hactn : lRegularizedAction S T (α n) a b ≤ A₀ := by rw [hval n]; exact hact n
    nlinarith
  obtain ⟨φ, g, hφ, hconv⟩ := exists_strictMono_tendstoUniformly_of_curveEnergy_le
    gRef a b B α (fun n => (hα n).contMDiffOn) henergy Q hQ
      (fun n r => hαQ n r.property)
  have hga : g ⟨a, le_rfl, hab.le⟩ = x := by
    have hlim := hconv.tendsto_at (⟨a, le_rfl, hab.le⟩ : Icc a b)
    have hlim' : Tendsto (fun _ : ℕ => x) atTop (𝓝 (g ⟨a, le_rfl, hab.le⟩)) := by
      simpa only [hαa] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds
  have hgb : g ⟨b, hab.le, le_rfl⟩ ∈ A := by
    apply hA.mem_of_tendsto (hconv.tendsto_at (⟨b, hab.le, le_rfl⟩ : Icc a b))
    exact Eventually.of_forall fun n => hαb (φ n)
  let γ : ℝ → M := IccExtend hab.le g
  have hγ : Continuous γ := (continuous_IccExtend_iff (h := hab.le)).mpr g.continuous
  have hγval (r : Icc a b) : γ r.val = g r := IccExtend_of_mem hab.le g r.property
  have hγa : γ a = x := (hγval ⟨a, le_rfl, hab.le⟩).trans hga
  have hγb : γ b ∈ A := (hγval ⟨b, hab.le, le_rfl⟩).symm ▸ hgb
  have hconvγ : TendstoUniformly (fun n (r : Icc a b) => α (φ n) r.val) (fun r => γ r.val) atTop := by
    simpa only [hγval] using hconv
  obtain ⟨m, t, p, u, htmono, ht0, htlast, hsrc, hrep, _, χ, hχ, hlsc⟩ :=
    exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier
      S hS.smoothMetric ⟨hS.scalarCont⟩ T a b A₀ hab.le (fun n => α (φ n))
      (fun n => (hα (φ n)).contMDiffOn) Q hQ (fun n r hr => hαQ (φ n) hr)
      (fun n => by rw [hval]; exact hact _) γ hconvγ hcarrier
  have hlim' : Tendsto (fun n => lRegularizedAction S T (α (φ (χ n))) a b) atTop (𝓝 (sInf costs)) := by
    have hh := hlim.comp (hφ.comp hχ).tendsto_atTop
    have heq : (fun n => lRegularizedAction S T (α (φ (χ n))) a b) = values ∘ φ ∘ χ := by
      funext n
      exact hval (φ (χ n))
    rw [heq]
    exact hh
  have hupper : lRegularizedAction S T γ a b ≤ sInf costs := by
    simpa only [hlim'.liminf_eq] using hlsc
  have hmin : ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ a = γ a → δ b = γ b →
      lRegularizedAction S T γ a b ≤ lRegularizedAction S T δ a b := by
    intro δ hδ hδa hδb
    exact hupper.trans (hbelow δ hδ (hδa.trans hγa) (hδb.symm ▸ hγb))
  have hc1 := lMinCurve_c1_of_spatial_derivatives S hS T a b hab t htmono ht0 htlast p γ hγ u hsrc hrep
    U hU htime hreg hGramFd hScalFd hmin
  obtain ⟨η, hη, heq⟩ := DifferentialGeometry.Topology.exists_contMDiff_extension_Icc hc1
  have hηa : η a = x := (heq ⟨le_rfl, hab.le⟩).trans hγa
  have hηb : η b ∈ A := (heq ⟨hab.le, le_rfl⟩).symm ▸ hγb
  have hηact : lRegularizedAction S T η a b = lRegularizedAction S T γ a b :=
    lRegularizedAction_congr S T η γ a b (fun r hr => heq (by
      rw [uIoo_of_le hab.le] at hr; exact Ioo_subset_Icc_self hr))
  have hηmin : ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ a = x → δ b ∈ A →
      lRegularizedAction S T η a b ≤ lRegularizedAction S T δ a b := by
    intro δ hδ hδa hδb
    rw [hηact]
    exact hupper.trans (hbelow δ hδ hδa hδb)
  exact ⟨η, hη, hηa, hηb, hconf η hη hηa hηb (hηmin α₀ hα₀ hstart hend), hηmin⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedMinC1_free_endpoint_of_compact_action_sublevel_of_spatial_derivatives [TopologicalSpace.MetrizableSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b : ℝ} (hab : a < b)
    (U : Set ℝ) (hU : U ⊆ D.carrier)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ U)
    (hreg : ∀ r ∈ Ioo a b, T - r ^ 2 ∈ D.regular)
    (hGramFd : ∀ p : M, ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (fun y : E => chartGramOp (I := I) S.family p (z.1, y)) z.2)
      (U ×ˢ interior (extChartAt I p).target))
    (hScalFd : ∀ p : M, ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) p (S.scalar z.1)) z.2)
      (U ×ˢ interior (extChartAt I p).target))
    (x : M) (α₀ : ℝ → M) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) I 1 α₀)
    (hstart : α₀ a = x)
    (Q : Set M) (hQ : IsCompact Q)
    (hconf : ∀ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α →
      α a = x → lRegularizedAction S T α a b ≤ lRegularizedAction S T α₀ a b →
      MapsTo α (Icc a b) Q) :
    ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η a = x ∧
      MapsTo η (Icc a b) Q ∧
      ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ a = x →
        lRegularizedAction S T η a b ≤ lRegularizedAction S T δ a b := by
  obtain ⟨η, hη, hηa, _, hηQ, hmin⟩ :=
    exists_lRegularizedMinC1_to_closed_set_of_compact_action_sublevel_of_spatial_derivatives
      S hS T hab U hU htime hreg hGramFd hScalFd x Set.univ isClosed_univ α₀ hα₀ hstart
      (Set.mem_univ _) Q hQ (fun α hα ha _ hact => hconf α hα ha hact)
  exact ⟨η, hη, hηa, hηQ, fun δ hδ hδa => hmin δ hδ hδa (Set.mem_univ _)⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedMinC1_of_compact_action_sublevel_of_spatial_derivatives [TopologicalSpace.MetrizableSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b : ℝ} (hab : a < b)
    (U : Set ℝ) (hU : U ⊆ D.carrier)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ U)
    (hreg : ∀ r ∈ Ioo a b, T - r ^ 2 ∈ D.regular)
    (hGramFd : ∀ p : M, ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (fun y : E => chartGramOp (I := I) S.family p (z.1, y)) z.2)
      (U ×ˢ interior (extChartAt I p).target))
    (hScalFd : ∀ p : M, ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) p (S.scalar z.1)) z.2)
      (U ×ˢ interior (extChartAt I p).target))
    (x y : M) (α₀ : ℝ → M) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) I 1 α₀)
    (hstart : α₀ a = x) (hend : α₀ b = y)
    (Q : Set M) (hQ : IsCompact Q)
    (hconf : ∀ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α →
      α a = x → α b = y → lRegularizedAction S T α a b ≤ lRegularizedAction S T α₀ a b →
      MapsTo α (Icc a b) Q) :
    ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η a = x ∧ η b = y ∧
      MapsTo η (Icc a b) Q ∧
      ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ a = x → δ b = y →
        lRegularizedAction S T η a b ≤ lRegularizedAction S T δ a b := by
  obtain ⟨η, hη, hηa, hηb, hηQ, hmin⟩ :=
    exists_lRegularizedMinC1_to_closed_set_of_compact_action_sublevel_of_spatial_derivatives
      S hS T hab U hU htime hreg hGramFd hScalFd x {y} isClosed_singleton α₀ hα₀ hstart
      (Set.mem_singleton_iff.mpr hend) Q hQ
      (fun α hα ha hb hact => hconf α hα ha (Set.mem_singleton_iff.mp hb) hact)
  exact ⟨η, hη, hηa, Set.mem_singleton_iff.mp hηb, hηQ,
    fun δ hδ hδa hδb => hmin δ hδ hδa (Set.mem_singleton_iff.mpr hδb)⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedMinC1_of_compact_action_sublevel [TopologicalSpace.MetrizableSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b : ℝ} (hab : a < b)
    (hreg : ∀ r ∈ Icc a b, T - r ^ 2 ∈ D.regular)
    (x y : M) (α₀ : ℝ → M) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) I 1 α₀)
    (hstart : α₀ a = x) (hend : α₀ b = y)
    (Q : Set M) (hQ : IsCompact Q)
    (hconf : ∀ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α →
      α a = x → α b = y → lRegularizedAction S T α a b ≤ lRegularizedAction S T α₀ a b →
      MapsTo α (Icc a b) Q) :
    ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η a = x ∧ η b = y ∧
      MapsTo η (Icc a b) Q ∧
      ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ a = x → δ b = y →
        lRegularizedAction S T η a b ≤ lRegularizedAction S T δ a b := by
  apply exists_lRegularizedMinC1_of_compact_action_sublevel_of_spatial_derivatives S hS T hab
    D.regular D.regular_subset hreg (fun r hr => hreg r (Ioo_subset_Icc_self hr))
    ?_ ?_ x y α₀ hα₀ hstart hend Q hQ hconf
  · intro p
    exact ((chartGramOp_smooth hS.smoothMetric p (K := interior (extChartAt I p).target) Subset.rfl).fderiv_snd
      (G := fun t y => chartGramOp (I := I) S.family p (t, y)) isOpen_interior (m := 0) (by simp)).continuousOn
  · intro p
    exact ((chartScalFun_smooth S hS p).fderiv_snd
      (G := fun t y => DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) p (S.scalar t) y)
      isOpen_interior (m := 0) (by simp)).continuousOn

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [TopologicalSpace.MetrizableSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedMinC1_of_action_lt_frontier_barrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b v μ B r : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbv : b ≤ v)
    (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hreg : ∀ t ∈ Icc a b, T - t ^ 2 ∈ D.regular)
    (x y : M) (α₀ : ℝ → M) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) I 1 α₀)
    (hstart : α₀ a = x) (hend : α₀ b = y)
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    (hxK : x ∈ interior K)
    (hmetric : ∀ t ∈ Ioo a b, ∀ z ∈ K, ∀ w : TangentSpace I z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (hscalar : ∀ t ∈ Ioo a b, ∀ z : M, -B ≤ S.scalar (T - t ^ 2) z)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z)
    (hseed : lRegularizedAction S T α₀ a b < μ * r ^ 2 / (2 * (b - a)) - 2 * B * v ^ 2 * (b - a)) :
    ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η a = x ∧ η b = y ∧
      MapsTo η (Icc a b) K ∧
      ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ a = x → δ b = y →
        lRegularizedAction S T η a b ≤ lRegularizedAction S T δ a b  := by
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  have hconf : ∀ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α → α a = x → α b = y →
      lRegularizedAction S T α a b ≤ lRegularizedAction S T α₀ a b → MapsTo α (Icc a b) K := by
    intro α hα hαa _ hact
    by_contra hnot
    have hint := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
      S hS.smoothMetric ⟨hS.scalarCont⟩ T a b hab.le α hα.contMDiffOn
      (fun t ht => D.regular_subset (hreg t ht))
    have hgap := lRegularizedAction_ge_of_leaves_closed_set S T α ha hbv hμ hB hr g hK.isClosed
      hα.contMDiffOn (hαa.symm ▸ hxK)
      (fun t ht hz => hmetric t ht (α t) hz (lVelocity α t))
      (fun t ht => hscalar t ht (α t)) hint (by simpa only [hαa] using hfront) hnot
    exact (not_lt_of_ge hgap) (hact.trans_lt hseed)
  exact exists_lRegularizedMinC1_of_compact_action_sublevel (I := I) (M := M)
    S hS T hab hreg x y α₀ hα₀ hstart hend K hK hconf

end DifferentialGeometry.PDE.RicciFlow.Perelman


end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [TopologicalSpace.MetrizableSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_compact_ball_lRegularizedMinC1_of_action_lt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {a b v : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbv : b ≤ v)
    (hreg : ∀ t ∈ Icc a b, T - t ^ 2 ∈ D.regular)
    (x : M) (g : SmoothRiemannianMetric I M) {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ r μ : ℝ, 0 < r ∧ 0 < μ ∧ IsCompact (riemannianClosedBallOf g x r) ∧
      riemannianClosedBallOf g x r ⊆ U ∧ ∀ B : ℝ, 0 ≤ B →
      (∀ t ∈ Ioo a b, ∀ z : M, -B ≤ S.scalar (T - t ^ 2) z) →
      ∀ (y : M) (α₀ : ℝ → M), ContMDiff 𝓘(ℝ, ℝ) I 1 α₀ → α₀ a = x → α₀ b = y →
      lRegularizedAction S T α₀ a b < μ * r ^ 2 / (2 * (b - a)) - 2 * B * v ^ 2 * (b - a) →
      ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η a = x ∧ η b = y ∧
        MapsTo η (Icc a b) (riemannianClosedBallOf g x r) ∧
        ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ a = x → δ b = y →
          lRegularizedAction S T η a b ≤ lRegularizedAction S T δ a b  := by
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨r, hr, hK, hKU⟩ := exists_pos_isCompact_riemannianClosedBallOf_subset_of_mem_nhds g x hU
  let J := (fun t : ℝ => T - t ^ 2) '' Icc a b
  have hJ : IsCompact J := isCompact_Icc.image (continuous_const.sub (continuous_id.pow 2))
  have hJD : J ⊆ D.carrier := by rintro _ ⟨t, ht, rfl⟩; exact D.regular_subset (hreg t ht)
  obtain ⟨μ, hμ, hmetric⟩ := hS.smoothMetric.metric_lower_on_compact_time hJ hJD hK g
  refine ⟨r, μ, hr, hμ, hK, hKU, ?_⟩
  intro B hB hscalar y α₀ hα₀ hstart hend hseed
  apply exists_lRegularizedMinC1_of_action_lt_frontier_barrier S hS T ha hab hbv hμ.le hB hr.le
    hreg x y α₀ hα₀ hstart hend g hK (mem_interior_riemannianClosedBallOf g x hr)
    (fun t ht z hz w => hmetric (T - t ^ 2) ⟨t, Ioo_subset_Icc_self ht, rfl⟩ z hz w)
    hscalar ?_ hseed
  intro z hz
  rw [riemannianEDistOf_eq_of_mem_frontier_riemannianClosedBallOf g x hz]

end DifferentialGeometry.PDE.RicciFlow.Perelman
