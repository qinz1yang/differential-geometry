import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCurvatureJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalarEvolutionRate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapScalarLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialScalarDerivativeBounds

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_scalar_lt_at_initial_slab_start (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ H : ObservedHistory.{u}, InitialIdentification P₀ g₀ H →
      ∀ {s : ℝ} (G : (H.stage 0).IncomingSlab (H.time 0) s),
      G.flow.base.metric (H.time 0) = H.initialMetric 0 →
      ∀ y : (H.stage 0).Carrier, G.flow.scalar (H.time 0) y < Q₀ := by
  obtain ⟨τ, Qb, hτ, hQb, hbound⟩ :=
    OrientedThreeStage.exists_uniform_initial_scalar_bound_of_isometry.{u, u} P₀ g₀
  refine ⟨Qb, hQb, fun H A s G hG y => ?_⟩
  have key : ∀ {a : ℝ}, a = 0 → ∀ F : (H.stage 0).IncomingSlab a s,
      F.flow.base.metric a = H.initialMetric 0 → F.flow.scalar a y < Qb := by
    intro a ha F hF
    subst ha
    refine hbound F A.map (fun x v w => ?_) 0 ⟨le_rfl, hτ.le⟩ F.lt y
    rw [hF]
    exact A.metric_eq x v w
  exact key H.time_zero G hG

theorem exists_abs_derivWithin_Ici_scalar_le_at_cap_slab_start :
    ∃ ε₀ Ccap : ℝ, 0 < ε₀ ∧ 0 ≤ Ccap ∧
      ∀ {H : ObservedHistory.{u}} {j : Fin H.eventCount} {p : CutoffParameters}
        (R : GeometricCutoffRecord H j p), p.modelAccuracy ≤ ε₀ → 4 ≤ p.modelOrder →
        StandardCap.transitionEnd < p.modelRadius → (∀ b, (R.static b).hasCanonicalWindow) →
      ∀ {s' : ℝ} (G : (H.stage j.succ).IncomingSlab (H.time j.succ) s'),
        G.flow.base.metric (H.time j.succ) = H.initialMetric j.succ →
      ∀ y ∈ (H.event j).capRegion,
        |derivWithin (fun v => G.flow.scalar v y) (Ici (H.time j.succ)) (H.time j.succ)| ≤
          Ccap * G.flow.scalar (H.time j.succ) y ^ 2 := by
  obtain ⟨ε₀, c, B, hε₀, hc, hB, hcap⟩ := exists_presentedStaticCap_window_curvature_bounds.{u}
  set c' : ℝ := min c 1 with hc'def
  have hc' : 0 < c' := lt_min hc one_pos
  have hc'1 : c' ≤ 1 := min_le_right _ _
  set K : ℝ := B / c' ^ 4 with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨ε₀, (Module.finrank ℝ ThreeSpace : ℝ) ^ 6 * Real.sqrt K +
    2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 4 * K, hε₀, by positivity, ?_⟩
  intro H j p R hε hm hD hcan s' G hG y hy
  have hGo : G.flow.base.metric (H.time j.succ) = (H.event j).outputMetric :=
    hG.trans (H.event_output j).symm
  obtain ⟨b, z, hz⟩ := hy
  have hb := (H.event j).retainedBoundary_of_presentation_cap_eq_inl hz
  obtain ⟨-, -, -, -, -, -, -, hwin⟩ := hcan ⟨b, hb⟩
  obtain ⟨x, hxT, hxw⟩ := hwin z
  have hyx : y = (R.static ⟨b, hb⟩).window x :=
    (Sum.inl_injective (hz.symm.trans ((R.static ⟨b, hb⟩).cap_eq z))).trans hxw.symm
  subst hyx
  obtain ⟨hRc, hJ⟩ := hcap (R.static ⟨b, hb⟩) hε hm x (hxT.trans_lt hD)
  set Qs := (R.static ⟨b, hb⟩).neck.scale with hQs
  have hQ := (R.static ⟨b, hb⟩).neck.scale_pos
  have hscalar : G.flow.scalar (H.time j.succ) ((R.static ⟨b, hb⟩).window x) =
      metricScalarAt (H.event j).outputMetric ((R.static ⟨b, hb⟩).window x) := by
    change metricScalarAt (G.flow.base.metric (H.time j.succ)) _ = _
    rw [hGo]
  set Rs := metricScalarAt (H.event j).outputMetric ((R.static ⟨b, hb⟩).window x)
  have hcQ : c' * Qs ≤ Rs := (mul_le_mul_of_nonneg_right (min_le_left _ _) hQ.le).trans hRc
  have hRs : 0 ≤ Rs := (by positivity : (0 : ℝ) ≤ c' * Qs).trans hcQ
  have hjet : ∀ i ≤ 2, curvDerivNormSq i (G.flow.base.metric (H.time j.succ))
      ((R.static ⟨b, hb⟩).window x) ≤ K * G.flow.scalar (H.time j.succ)
        ((R.static ⟨b, hb⟩).window x) ^ (i + 2) := by
    intro i hi
    rw [hscalar, hGo]
    have hpow : c' ^ 4 * Qs ^ (i + 2) ≤ Rs ^ (i + 2) := by
      have h4 : c' ^ 4 ≤ c' ^ (i + 2) := pow_le_pow_of_le_one hc'.le hc'1 (by omega)
      calc c' ^ 4 * Qs ^ (i + 2) ≤ c' ^ (i + 2) * Qs ^ (i + 2) :=
            mul_le_mul_of_nonneg_right h4 (pow_nonneg hQ.le _)
        _ = (c' * Qs) ^ (i + 2) := (mul_pow _ _ _).symm
        _ ≤ Rs ^ (i + 2) := pow_le_pow_left₀ (by positivity) hcQ _
    calc curvDerivNormSq i (H.event j).outputMetric ((R.static ⟨b, hb⟩).window x)
        ≤ B * Qs ^ (i + 2) := hJ i hi
      _ = K * (c' ^ 4 * Qs ^ (i + 2)) := by rw [hKdef]; field_simp
      _ ≤ K * Rs ^ (i + 2) := mul_le_mul_of_nonneg_left hpow hK
  exact G.abs_derivWithin_Ici_scalar_le_at_start_of_curvature_jets hK (hjet 0 (by norm_num))
    (hjet 2 le_rfl)

namespace RetainedCoreHistory

theorem exists_slice_bounds_at_slab_start (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ Cs : ℝ≥0, ∀ Ctime : ℝ≥0, Cs ≤ Ctime →
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
  obtain ⟨Q₀, hQ₀, hinit⟩ := exists_scalar_lt_at_initial_slab_start P₀ g₀
  obtain ⟨ε₀, Ccap, hε₀, hCcap, hcap⟩ := exists_abs_derivWithin_Ici_scalar_le_at_cap_slab_start.{u}
  refine ⟨⟨Ccap, hCcap⟩, fun Ctime hCt => ⟨StandardCap.transitionEnd + 1, Q₀, 4, hQ₀,
    fun qcan hq => ⟨1, 1, ε₀, one_pos, one_pos, hε₀, ?_⟩⟩⟩
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
