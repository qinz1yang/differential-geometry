import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornComponents
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set Function Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
universe u
variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem exists_horn_scalar_eq
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (y : Sphere 2) {Q : ℝ} (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q) :
    ∃ t : ℝ, 0 < t ∧ metricScalarAt D.terminal.metric (P.horn c e (y, t)) = Q := by
  obtain ⟨r, hr⟩ := P.horn_scalar_diverges c e Q
  let T := max r 1
  have hT : 0 ≤ T := le_trans zero_le_one (le_max_right r 1)
  have hhi : Q ≤ metricScalarAt D.terminal.metric (P.horn c e (y, T)) :=
    (hr y T (le_max_left r 1)).le
  have hlo : metricScalarAt D.terminal.metric (P.horn c e (y, 0)) < Q :=
    (P.horn_base_scalar c e y).trans_lt hQ
  have hcont : ContinuousOn (fun t : ℝ => metricScalarAt D.terminal.metric (P.horn c e (y, t))) (Icc 0 T) := by
    apply (metricScalar_smooth D.terminal.metric).continuous.comp_continuousOn
    exact (P.horn_smooth c e).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨mem_univ _, ht.1⟩)
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hT hcont ⟨hlo.le, hhi⟩
  refine ⟨t, lt_of_le_of_ne ht.1 ?_, heq⟩
  intro he
  rw [← he] at heq
  exact hlo.ne heq

theorem exists_neck_scale_eq
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (y : Sphere 2) {Q : ℝ} (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q) :
    ∃ t : ℝ, 0 < t ∧ ∃ (δ : ℝ) (k : ℕ) (N : NormalizedNeck D.terminal.metric δ k),
      N.center = P.horn c e (y, t) ∧ N.scale = Q ∧ δ ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k := by
  obtain ⟨t, ht, hscalar⟩ := P.exists_horn_scalar_eq c e y hQ
  have hopen := P.isOpen_positive_horn c e
  have hsub : P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) ⊆
      range (fun p : HalfNeckCylinder => P.horn c e p.val) := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp.2.le⟩, rfl⟩
  have hin : P.horn c e (y, t) ∈ interior (range (fun p : HalfNeckCylinder => P.horn c e p.val)) :=
    interior_maximal hsub hopen ⟨(y, t), ⟨mem_univ _, ht⟩, rfl⟩
  obtain ⟨δ, k, N, hcenter, hδε, hk⟩ := P.horn_spatial_neck c e _ hin
  refine ⟨t, ht, δ, k, N, hcenter, ?_, hδε, hk⟩
  rw [N.scale_scalar, hcenter]
  exact hscalar

theorem exists_neck_family_scale_eq (y : Sphere 2) {Q : ℝ}
    (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q) :
    ∃ (t : ∀ c, P.hornIndex c → ℝ) (δ : ∀ c, P.hornIndex c → ℝ)
      (k : ∀ c, P.hornIndex c → ℕ)
      (N : ∀ c e, NormalizedNeck D.terminal.metric (δ c e) (k c e)),
      ∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y, t c e) ∧
        (N c e).scale = Q ∧ δ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e := by
  classical
  choose t ht δ k N hc hs hδ hk using fun c e => P.exists_neck_scale_eq c e y hQ
  exact ⟨t, δ, k, N, fun c e => ⟨ht c e, hc c e, hs c e, hδ c e, hk c e⟩⟩

theorem exists_neck_family_scale_eq_and_scalar_lower (y : Sphere 2) {Q : ℝ}
    (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q) (hε : ε ≤ 1 / 8646) :
    ∃ (t : ∀ c, P.hornIndex c → ℝ) (δ : ∀ c, P.hornIndex c → ℝ)
      (k : ∀ c, P.hornIndex c → ℕ)
      (N : ∀ c e, NormalizedNeck D.terminal.metric (δ c e) (k c e)),
      ∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y, t c e) ∧
        (N c e).scale = Q ∧ δ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e ∧
        ∀ x : neckBuffer (δ c e), x ∈ neckClosedTest (δ c e) →
          Q / 2 ≤ metricScalarAt D.terminal.metric ((N c e).chart x) := by
  obtain ⟨t, δ, k, N, hN⟩ := P.exists_neck_family_scale_eq y hQ
  refine ⟨t, δ, k, N, ?_⟩
  intro c e
  obtain ⟨ht, hc, hs, hδ, hk⟩ := hN c e
  refine ⟨ht, hc, hs, hδ, hk, ?_⟩
  intro x hx
  have hε1 : 1 ≤ ε⁻¹ := ((one_lt_inv₀ P.epsilon_pos).mpr (by linarith : ε < 1)).le
  have hfloor : 1 ≤ ⌊ε⁻¹⌋₊ := Nat.le_floor (by exact_mod_cast hε1)
  have hk2 : 2 ≤ k c e := by omega
  have hδhalf : δ c e ≤ 1 / 2 := by linarith
  have hratio := (N c e).abs_scalar_ratio_sub_one_le hk2 hδhalf x hx
  rw [hs] at hratio
  have hQpos : 0 < Q := hs ▸ (N c e).scale_pos
  have hbound : (1 / 2 : ℝ) ≤ metricScalarAt D.terminal.metric ((N c e).chart x) / Q := by
    have hlo := (abs_le.mp hratio).1
    linarith
  have h := (le_div_iff₀ hQpos).mp hbound
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
