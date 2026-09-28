import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowPointTimeSlack
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTimeWindowContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SliverForwardComparison

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem RetainedCoreHistory.exists_crossing_bad_point_terminal
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    {p : CutoffParameters} (records : ∀ i, GeometricCutoffRecord H.toHistory i p)
    {ε C1 C2 qcan τmin θ Dcap θcap ζ ζ' ς : ℝ} {Ctime Cgrad : ℝ≥0}
    (hζ : 0 < ζ) (hζ' : 0 < ζ') (hς : 0 < ς) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s)
    (hext : ∃ η₀ : ℝ, 0 < η₀ ∧ t₀ + η₀ < s ∧
      G.DerivativeBoundBefore (2 * Ctime) (2 * qcan) (t₀ + η₀))
    (hfail : ¬ ∃ η : ℝ, 0 < η ∧ G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
      fun y t => G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ ∧
        ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap) :
    ∃ η : ℝ, 0 < η ∧ t₀ + η < s ∧
      G.DerivativeBoundBefore (2 * Ctime) (2 * qcan) (t₀ + η) ∧
      (∀ t ∈ Icc t₀ (t₀ + η), ∀ x : (H.stage (Fin.last H.eventCount)).Carrier,
        G.flow.scalar t x * η ≤ ζ ∧ |G.flow.scalar t x - G.flow.scalar t₀ x| ≤ ζ' ∧
        ∀ v : TangentSpace ThreeModel x,
          (G.flow.base.metric t).inner x v v ≤
            Real.exp 1 * (G.flow.base.metric t₀).inner x v v ∧
          (G.flow.base.metric t₀).inner x v v ≤
            Real.exp 1 * (G.flow.base.metric t).inner x v v) ∧
      (∃ S : ℝ, 0 < S ∧ (∀ i b, ((records i).static b).neck.scale ≤ S) ∧ S * η ≤ ς) ∧
      ∃ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
        H.time (Fin.last H.eventCount) < t ∧ t₀ ≤ t ∧ t < t₀ + η ∧
        qcan < G.flow.scalar t y ∧
        G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ ∧
        ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap ∧
        ¬ ((τmin ≤ G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) →
              ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε) ∧
            |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤
              Ctime * G.flow.scalar t y ^ 2 ∧
            ∀ v : TangentSpace I3 y,
              |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
                Cgrad * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
                  Real.sqrt ((G.flow.base.metric t).inner y v v)) := by
  obtain ⟨η₀, hη₀, -, hder⟩ := hext
  obtain ⟨K₀, hK₀⟩ := G.exists_forall_Icc_riemannNorm_le (b := t₀) ht₀.2
  have hK : ∀ x, G.riemannNorm t₀ x ≤ max K₀ 1 :=
    fun x => (hK₀ t₀ ⟨ht₀.1, le_rfl⟩ x).trans (le_max_left _ _)
  obtain ⟨η₁, hη₁, -, hη₁s, hsl⟩ :=
    G.exists_sliver_forward_comparison (lt_max_of_lt_right one_pos) hζ ht₀ hK
  obtain ⟨δ, hδ, -, hclose⟩ := G.exists_forall_Icc_scalar_riemannNorm_metric_close ht₀ hζ'
  obtain ⟨S, hS, hSle⟩ := H.exists_forall_neck_scale_le records
  set η : ℝ := min (min η₀ η₁) (min δ (ς / S)) with hηdef
  have hηη₀ : η ≤ η₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hηη₁ : η ≤ η₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hηδ : η ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hηS : η ≤ ς / S := (min_le_right _ _).trans (min_le_right _ _)
  have hηpos : 0 < η := lt_min (lt_min hη₀ hη₁) (lt_min hδ (div_pos hς hS))
  refine ⟨η, hηpos, by linarith, G.derivativeBoundBefore_mono (by linarith) hder,
    fun t ht x => ?_, ⟨S, hS, hSle, ?_⟩, ?_⟩
  · have ht₁ : t ∈ Icc t₀ (t₀ + η₁) := ⟨ht.1, ht.2.trans (by linarith)⟩
    obtain ⟨-, hR, hmet, -⟩ := hsl t ht₁
    refine ⟨?_, ?_, fun v => hmet x v⟩
    · obtain ⟨-, hRη⟩ := hR x
      rcases le_total 0 (G.flow.scalar t x) with h0 | h0
      · exact (mul_le_mul_of_nonneg_left hηη₁ h0).trans hRη
      · exact (mul_nonpos_of_nonpos_of_nonneg h0 hηpos.le).trans hζ.le
    · have hmax : max (H.time (Fin.last H.eventCount)) (t₀ - δ) ≤ t₀ :=
        max_le ht₀.1 (by linarith)
      exact (hclose t ⟨hmax.trans ht.1, by linarith [ht.2]⟩ t₀ ⟨hmax, by linarith⟩ x).1
  · have := (le_div_iff₀ hS).mp hηS
    linarith
  · have hnot : ¬ G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
        fun y t => G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ ∧
          ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap :=
      fun hb => hfail ⟨η, hηpos, hb⟩
    simp only [OrientedThreeStage.IncomingSlab.CanonicalBoundsOn, not_forall, exists_prop] at hnot
    obtain ⟨y, t, hat, ht0, htη, -, hR, ⟨hθ, hcwp⟩, hbad⟩ := hnot
    exact ⟨y, t, hat, ht0, htη, hR, hθ, hcwp, hbad⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
