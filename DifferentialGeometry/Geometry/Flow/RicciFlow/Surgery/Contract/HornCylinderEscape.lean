import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.EndNeckContractReduction
import DifferentialGeometry.Geometry.Metric.Distance.CompactImage

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {D : OneStepIncoming.{u}}

theorem halfNeckCylinder_eq_prod :
    (Set.univ ×ˢ Set.Ici (0 : ℝ) : Set NeckCylinder) = {x : NeckCylinder | 0 ≤ x.2} := by
  ext x
  simp

theorem TerminalCorePresentation.continuousOn_horn {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    ContinuousOn (fun x : NeckCylinder => P.horn c e x) {x : NeckCylinder | 0 ≤ x.2} := by
  have h := (P.horn_smooth c e).continuousOn
  rwa [halfNeckCylinder_eq_prod] at h

theorem TerminalCorePresentation.continuousOn_horn_scalar {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    ContinuousOn (fun x : NeckCylinder => metricScalarAt D.terminal.metric (P.horn c e x))
      {x : NeckCylinder | 0 ≤ x.2} :=
  (metricScalar_smooth D.terminal.metric).continuous.comp_continuousOn
    (P.continuousOn_horn c e)

theorem isCompact_neckCylinder_slab (U : ℝ) :
    IsCompact {x : NeckCylinder | 0 ≤ x.2 ∧ x.2 ≤ U} := by
  have h : IsCompact ((Set.univ : Set (Sphere 2)) ×ˢ Set.Icc (0 : ℝ) U) :=
    isCompact_univ.prod isCompact_Icc
  have hset : ((Set.univ : Set (Sphere 2)) ×ˢ Set.Icc (0 : ℝ) U) =
      {x : NeckCylinder | 0 ≤ x.2 ∧ x.2 ≤ U} := by
    ext x
    simp
  rwa [hset] at h

theorem tendsto_axial_of_tendsto_scalar_atTop {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (f : ℕ → NeckCylinder) (hf : ∀ n, 0 ≤ (f n).2)
    (hR : Tendsto (fun n => metricScalarAt D.terminal.metric (P.horn c e (f n))) atTop atTop) :
    Tendsto (fun n => (f n).2) atTop atTop := by
  rw [tendsto_atTop_atTop] at hR ⊢
  intro U
  have hcont : ContinuousOn
      (fun x : NeckCylinder => metricScalarAt D.terminal.metric (P.horn c e x))
      {x : NeckCylinder | 0 ≤ x.2 ∧ x.2 ≤ U} :=
    (P.continuousOn_horn_scalar c e).mono (fun x hx => hx.1)
  have hbd : BddAbove ((fun x : NeckCylinder =>
      metricScalarAt D.terminal.metric (P.horn c e x)) ''
        {x : NeckCylinder | 0 ≤ x.2 ∧ x.2 ≤ U}) :=
    (isCompact_neckCylinder_slab U).bddAbove_image hcont
  obtain ⟨B, hB⟩ := hbd
  obtain ⟨i, hi⟩ := hR (B + 1)
  refine ⟨i, fun n hn => ?_⟩
  have hbig : B + 1 ≤ metricScalarAt D.terminal.metric (P.horn c e (f n)) := hi n hn
  by_contra hlt
  have hmem : f n ∈ {x : NeckCylinder | 0 ≤ x.2 ∧ x.2 ≤ U} :=
    ⟨hf n, le_of_lt (not_le.mp hlt)⟩
  have hle : metricScalarAt D.terminal.metric (P.horn c e (f n)) ≤ B :=
    hB (Set.mem_image_of_mem _ hmem)
  linarith

theorem TerminalCorePresentation.tendsto_axial_of_tendsto_scalar_atTop {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (p : ℕ → HalfNeckCylinder)
    (hR : Tendsto (fun n : ℕ => metricScalarAt D.terminal.metric (P.horn c e (p n).1)) atTop atTop) :
    Tendsto (fun n : ℕ => (p n).1.2) atTop atTop :=
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tendsto_axial_of_tendsto_scalar_atTop
    P c e (fun n : ℕ => (p n).1) (fun n : ℕ => (p n).2) hR

theorem TerminalCorePresentation.exists_horn_scalar_gt {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c) (B : ℝ) :
    ∃ p : HalfNeckCylinder, B < metricScalarAt D.terminal.metric (P.horn c e p.1) := by
  obtain ⟨uL, hu⟩ := P.horn_scalar_diverges c e B
  refine ⟨⟨(DifferentialGeometry.Topology.sphereTwoNorth, max uL 0 + 1), ?_⟩, ?_⟩
  · exact le_trans (le_max_right uL 0) (le_add_of_nonneg_right zero_le_one)
  · exact hu _ _ (le_trans (le_max_left uL 0) (le_add_of_nonneg_right zero_le_one))

theorem not_tendsto_scalar_atTop_of_axial_bounded {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (f : ℕ → NeckCylinder) (hf_nonneg : ∀ n, 0 ≤ (f n).2) (U : ℝ)
    (hf_le : ∀ n, (f n).2 ≤ U) :
    ¬ Tendsto (fun n => metricScalarAt D.terminal.metric (P.horn c e (f n))) atTop atTop := by
  intro hR
  have hcont : ContinuousOn
      (fun x : NeckCylinder => metricScalarAt D.terminal.metric (P.horn c e x))
      {x : NeckCylinder | 0 ≤ x.2 ∧ x.2 ≤ U} :=
    (P.continuousOn_horn_scalar c e).mono (fun x hx => hx.1)
  obtain ⟨B, hB⟩ := (isCompact_neckCylinder_slab U).bddAbove_image hcont
  obtain ⟨i, hi⟩ := tendsto_atTop_atTop.mp hR (B + 1)
  have hmem : f i ∈ {x : NeckCylinder | 0 ≤ x.2 ∧ x.2 ≤ U} := ⟨hf_nonneg i, hf_le i⟩
  have hle : metricScalarAt D.terminal.metric (P.horn c e (f i)) ≤ B :=
    hB (Set.mem_image_of_mem _ hmem)
  linarith [hi i le_rfl]

theorem TerminalCorePresentation.not_bddAbove_horn_scalar {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    ¬ BddAbove (Set.range fun p : HalfNeckCylinder =>
      metricScalarAt D.terminal.metric (P.horn c e p.1)) := by
  intro h
  obtain ⟨B, hB⟩ := h
  obtain ⟨p, hp⟩ := P.exists_horn_scalar_gt c e B
  exact absurd (hB ⟨p, rfl⟩) (not_le.mpr hp)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

set_option autoImplicit false
noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u
variable {D : OneStepIncoming.{u}} {eps Lambda : ℝ} (P : TerminalCorePresentation D eps Lambda)

theorem exists_horn_point_outside_compact
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (K : Set D.slab.terminalRegularOpen) (hK : IsCompact K) (y : Sphere 2) (T : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ T < t ∧ P.horn c e (y, t) ∉ K := by
  have hpre : IsCompact ((fun p : HalfNeckCylinder => P.horn c e p.val) ⁻¹' K) :=
    (P.horn_proper c e).isCompact_preimage hK
  obtain ⟨B, hB⟩ := hpre.bddAbove_image continuous_subtype_val.snd.continuousOn
  let t := max (max B T) 0 + 1
  have ht : 0 ≤ t := by dsimp only [t]; linarith [le_max_right (max B T) 0]
  have hBt : B < t := by
    dsimp only [t]
    linarith [le_max_left B T, le_max_left (max B T) 0]
  have hTt : T < t := by
    dsimp only [t]
    linarith [le_max_right B T, le_max_left (max B T) 0]
  refine ⟨t, ht, hTt, ?_⟩
  intro hmem
  exact hBt.not_ge (hB ⟨⟨(y, t), ht⟩, hmem, rfl⟩)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_horn_point_distance_gt_of_isCompact_closedBall
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (y : Sphere 2) {s : ℝ} (hs : 0 ≤ s) (R T : ℝ)
    (hcompact : IsCompact (riemannianClosedBallOf D.terminal.metric (P.horn c e (y, s)) R)) :
    ∃ t : ℝ, 0 ≤ t ∧ T < t ∧
      ENNReal.ofReal R < riemannianEDistOf D.terminal.metric
        (P.horn c e (y, s)) (P.horn c e (y, t)) ∧
      riemannianEDistOf D.terminal.metric (P.horn c e (y, s)) (P.horn c e (y, t)) ≠ ⊤ := by
  obtain ⟨t, ht, hT, hout⟩ := P.exists_horn_point_outside_compact c e _ hcompact y T
  refine ⟨t, ht, hT, lt_of_not_ge hout, ?_⟩
  let : RiemannianBundle (fun x : D.slab.terminalRegularOpen => TangentSpace ThreeModel x) :=
    ⟨D.terminal.metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace
      (fun x : D.slab.terminalRegularOpen => TangentSpace ThreeModel x) :=
    ⟨D.terminal.metric.inner, D.terminal.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace D.slab.terminalRegularOpen :=
    PseudoEMetricSpace.ofRiemannianMetric ThreeModel D.slab.terminalRegularOpen
  let f : ℝ≥0 → D.slab.terminalRegularOpen := fun u => P.horn c e (y, u)
  have hf : Continuous f :=
    (P.horn_proper c e).continuous.comp
      ((continuous_const.prodMk NNReal.continuous_coe).subtype_mk (fun u => u.property))
  exact (EMetric.edist_lt_top_of_continuous_of_preconnected hf ⟨s, hs⟩ ⟨t, ht⟩).ne

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
