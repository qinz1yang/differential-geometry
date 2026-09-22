import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalCutRetention
import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornComponents
import DifferentialGeometry.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem exists_horn_first_scalar_level
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {Q : ℝ} (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q) :
    ∃ t : ℝ, 0 < t ∧ ∃ y : Sphere 2,
      metricScalarAt D.terminal.metric (P.horn c e (y, t)) = Q ∧
      (∀ s ∈ Ico 0 t, ∀ z : Sphere 2,
        metricScalarAt D.terminal.metric (P.horn c e (z, s)) < Q) ∧
      ∀ z : Sphere 2, metricScalarAt D.terminal.metric (P.horn c e (z, t)) ≤ Q := by
  obtain ⟨r, hr⟩ := P.horn_scalar_diverges c e Q
  let T := max r 1
  have hT : 0 ≤ T := zero_le_one.trans (le_max_right _ _)
  have hcont : ContinuousOn
      (fun p : ℝ × Sphere 2 => metricScalarAt D.terminal.metric (P.horn c e (p.2, p.1)))
      (Icc 0 T ×ˢ univ) := by
    apply (metricScalar_smooth D.terminal.metric).continuous.comp_continuousOn
    exact (P.horn_smooth c e).continuousOn.comp continuous_swap.continuousOn
      (fun p hp => ⟨mem_univ _, hp.1.1⟩)
  have hstart : ∀ y : Sphere 2, metricScalarAt D.terminal.metric (P.horn c e (y, 0)) < Q :=
    fun y => (P.horn_base_scalar c e y).trans_lt hQ
  have hend : ∃ y : Sphere 2, Q ≤ metricScalarAt D.terminal.metric (P.horn c e (y, T)) :=
    ⟨DifferentialGeometry.Geometry.Neck.spherePoint,
      (hr DifferentialGeometry.Geometry.Neck.spherePoint T (le_max_left _ _)).le⟩
  obtain ⟨t, ht, y, heq, hbefore, hlevel⟩ :=
    hcont.exists_first_level_of_compact hT hstart hend
  exact ⟨t, ht.1, y, heq, hbefore, hlevel⟩

theorem exists_neck_at_horn_first_scalar_level
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {Q : ℝ} (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q) :
    ∃ t : ℝ, 0 < t ∧ ∃ y : Sphere 2, ∃ δ : ℝ, ∃ k : ℕ,
      ∃ N : NormalizedNeck D.terminal.metric δ k,
        N.center = P.horn c e (y, t) ∧ N.scale = Q ∧
        δ ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k ∧
        (∀ s ∈ Ico 0 t, ∀ z : Sphere 2,
          metricScalarAt D.terminal.metric (P.horn c e (z, s)) < Q) ∧
        ∀ z : Sphere 2, metricScalarAt D.terminal.metric (P.horn c e (z, t)) ≤ Q := by
  obtain ⟨t, ht, y, heq, hbefore, hlevel⟩ := P.exists_horn_first_scalar_level c e hQ
  have hsub : P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) ⊆
      range (fun p : HalfNeckCylinder => P.horn c e p.val) := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp.2.le⟩, rfl⟩
  have hin : P.horn c e (y, t) ∈
      interior (range (fun p : HalfNeckCylinder => P.horn c e p.val)) :=
    interior_maximal hsub (P.isOpen_positive_horn c e) ⟨(y, t), ⟨mem_univ _, ht⟩, rfl⟩
  obtain ⟨δ, k, N, hcenter, hδ, hk⟩ := P.horn_spatial_neck c e _ hin
  refine ⟨t, ht, y, δ, k, N, hcenter, ?_, hδ, hk, hbefore, hlevel⟩
  rw [N.scale_scalar, hcenter, heq]

theorem exists_neck_family_at_first_scalar_level
    {Q : ℝ} (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q) :
    ∃ (t : ∀ c, P.hornIndex c → ℝ) (y : ∀ c, P.hornIndex c → Sphere 2)
      (δ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
      (N : ∀ c e, NormalizedNeck D.terminal.metric (δ c e) (k c e)),
      ∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y c e, t c e) ∧
        (N c e).scale = Q ∧ δ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e ∧
        (∀ s ∈ Ico 0 (t c e), ∀ z : Sphere 2,
          metricScalarAt D.terminal.metric (P.horn c e (z, s)) < Q) ∧
        ∀ z : Sphere 2, metricScalarAt D.terminal.metric (P.horn c e (z, t c e)) ≤ Q := by
  classical
  choose t ht y δ k N hcenter hscale hδ hk hbefore hlevel using
    fun c e => P.exists_neck_at_horn_first_scalar_level c e hQ
  exact ⟨t, y, δ, k, N, fun c e =>
    ⟨ht c e, hcenter c e, hscale c e, hδ c e, hk c e, hbefore c e, hlevel c e⟩⟩

theorem exists_neck_family_with_truncated_scalar_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ Q : ℝ, max K (Λ * (P.coreRadius ^ 2)⁻¹) < Q →
      ∃ (t : ∀ c, P.hornIndex c → ℝ) (y : ∀ c, P.hornIndex c → Sphere 2)
        (δ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
        (N : ∀ c e, NormalizedNeck D.terminal.metric (δ c e) (k c e)),
        (∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y c e, t c e) ∧
          (N c e).scale = Q ∧ δ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e) ∧
        ∀ x ∈ P.truncatedRegion t, metricScalarAt D.terminal.metric x ≤ Q := by
  have hcore : IsCompact (⋃ c ∈ P.component, P.core c) :=
    P.component_finite.isCompact_biUnion (fun c hc => P.core_isCompact c hc)
  obtain ⟨K₀, hK₀⟩ := (hcore.image (metricScalar_smooth D.terminal.metric).continuous).bddAbove
  let K := max K₀ 1
  refine ⟨K, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro Q hQ
  obtain ⟨t, y, δ, k, N, hN⟩ :=
    P.exists_neck_family_at_first_scalar_level ((le_max_right _ _).trans_lt hQ)
  refine ⟨t, y, δ, k, N, fun c e =>
    ⟨(hN c e).1, (hN c e).2.1, (hN c e).2.2.1, (hN c e).2.2.2.1,
      (hN c e).2.2.2.2.1⟩, ?_⟩
  intro x hx
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
  rcases hxc with hxc | hxc
  · have hb : metricScalarAt D.terminal.metric x ≤ K₀ :=
      hK₀ ⟨x, mem_iUnion₂.mpr ⟨c, hc, hxc⟩, rfl⟩
    exact (hb.trans (le_max_left _ _)).trans ((le_max_left _ _).trans hQ.le)
  · obtain ⟨e, p, hp, hpx⟩ := mem_iUnion.mp hxc
    have hbound : metricScalarAt D.terminal.metric (P.horn c e p) ≤ Q := by
      rcases hp.2.2.eq_or_lt with heq | hlt
      · exact (congrArg (fun u => metricScalarAt D.terminal.metric (P.horn c e (p.1, u)))
          heq).trans_le ((hN c e).2.2.2.2.2.2 p.1)
      · exact ((hN c e).2.2.2.2.2.1 p.2 ⟨hp.2.1, hlt⟩ p.1).le
    exact hpx ▸ hbound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
