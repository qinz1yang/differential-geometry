import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabStartDerivativeBounds

set_option autoImplicit false
noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- The scalar time-derivative coefficient at a slab start is chosen before the
initial stage and metric. Those data affect the scalar threshold, while the
selected cap records and actual regular crossings supply the later-stage bound. -/
theorem exists_uniform_slice_bounds_at_slab_start :
    ∃ Cs : ℝ≥0, ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
      ∀ Ctime : ℝ≥0, Cs ≤ Ctime →
      ∃ (Rs qs : ℝ) (ms : ℕ), 0 < qs ∧ ∀ qcan : ℝ, qs ≤ qcan →
      ∃ (δs ρs εs : ℝ), 0 < δs ∧ 0 < ρs ∧ 0 < εs ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εs → Rs ≤ p₀.modelRadius → ms ≤ p₀.modelOrder →
        δbound ≤ δs → ρbound ≤ ρs →
      ∀ H : RetainedCoreHistory.{u}, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
        p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
        H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
        Gk.flow.base.metric (H.time k) = H.initialMetric k →
        H.EventSlabsDerivative Ctime qcan k →
        (∀ y : (H.stage k).Carrier, ContinuousWithinAt (fun z : ℝ × (H.stage k).Carrier =>
          derivWithin (fun v => Gk.flow.scalar v z.2) (Ici z.1) z.1)
            (Ici (H.time k) ×ˢ univ) (H.time k, y)) ∧
        ∀ y : (H.stage k).Carrier, qcan < Gk.flow.scalar (H.time k) y →
          |derivWithin (fun v => Gk.flow.scalar v y) (Ici (H.time k)) (H.time k)| ≤
            Ctime * Gk.flow.scalar (H.time k) y ^ 2 := by
  obtain ⟨ε₀, Ccap, hε₀, hCcap, hcap⟩ := exists_abs_derivWithin_Ici_scalar_le_at_cap_slab_start.{u}
  refine ⟨⟨Ccap, hCcap⟩, ?_⟩
  intro P₀ g₀
  obtain ⟨Q₀, hQ₀, hinit⟩ := exists_scalar_lt_at_initial_slab_start P₀ g₀
  refine fun Ctime hCt => ⟨StandardCap.transitionEnd + 1, Q₀, 4, hQ₀,
    fun qcan hq => ⟨1, 1, ε₀, one_pos, one_pos, hε₀, ?_⟩⟩
  intro p₀ δbound ρbound hε hRs hms _ _ H ⟨A⟩ _ p records hrec k s Gk hGk hder
  obtain ⟨-, hD, hmo, hacc, -, hcan, -, -⟩ := hrec
  refine ⟨Gk.continuousWithinAt_derivWithin_Ici_scalar_at_start, fun y hy => ?_⟩
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
  · exact absurd (hinit H.toHistory A Gk hGk y) (not_lt.mpr (hq.trans hy.le))
  · by_cases hc : y ∈ (H.toHistory.event j).capRegion
    · have hRD : StandardCap.transitionEnd < p.modelRadius := by
        rw [hD]
        linarith
      refine (hcap (records j) (hacc ▸ hε) (hmo ▸ hms) hRD (hcan j) Gk hGk y hc).trans ?_
      exact mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hCt) (sq_nonneg _)
    · obtain ⟨p', hp'⟩ := (H.toHistory.event j).exists_regularCrossing_of_not_mem_capRegion
        (records j).old_eq_retained hc
      exact (H.toHistory.event j).abs_derivWithin_Ici_scalar_le_at_slab_start_of_regularCrossing
        Gk (hGk.trans (H.event_output j).symm) hp' (hder j Fin.castSucc_lt_succ) hy


end RetainedCoreHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
