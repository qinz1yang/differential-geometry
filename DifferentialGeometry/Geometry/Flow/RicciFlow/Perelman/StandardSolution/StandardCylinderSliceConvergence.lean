import DifferentialGeometry.Geometry.Metric.Convergence.Time
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderIdentification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderClosedLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCrossConvergence

set_option autoImplicit false
noncomputable section
open Set Filter Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Q := cylinderReferenceCopy.Q
private abbrev C := Metric.sphere (0 : E3) 1 × ℝ
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : TopologicalSpace cylinderPointedReference.M := cylinderPointedReference.topology
private local instance : ChartedSpace E3 cylinderPointedReference.M := cylinderPointedReference.charted
private local instance : T2Space cylinderPointedReference.M := cylinderPointedReference.t2
private local instance : IsManifold (𝓡 3) ∞ cylinderPointedReference.M := cylinderPointedReference.smooth
private local instance : SigmaCompactSpace cylinderPointedReference.M := cylinderPointedReference.sigmaCompact

theorem exists_standard_cylinder_metric_subsequence_at_tendsto_time
    {τ t : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (S : ℕ → StandardSolution) (x : ℕ → E3) (time : ℕ → ℝ)
    (htime : ∀ n, time n ∈ Icc 0 τ)
    (hlim : Tendsto time atTop (𝓝 t))
    (hescape : Tendsto (fun n => (riemannianEDistOf ((S n).val.metric 0) 0 (x n)).toReal)
      atTop atTop) :
    ∃ (ψ : ℕ → ℕ) (G : ℕ → SmoothRiemannianMetric IC C)
      (F : ℕ → PartialDiffeomorph IC (𝓡 3) C E3 ∞),
      StrictMono ψ ∧
      MetricCInfConvergenceOnCompacts G (shrinkingCylinderMetric (E := E3) t)
        (roundCylinderMetric (E := E3) (n := 2)) ∧
      (∀ n z, F n z = (‖x (ψ n)‖ + z.2) • pointedInitialRotation (x (ψ n)) z.1.val) ∧
      ∀ K : Set C, IsCompact K → ∀ᶠ n in atTop,
        ∃ U : Set C, IsOpen U ∧ K ⊆ U ∧ U ⊆ (F n).source ∧
          ∀ z ∈ U, ∀ v w : TangentSpace IC z,
            (G n).inner z v w = ((S (ψ n)).val.metric (time (ψ n))).inner (F n z)
              (mfderiv IC (𝓡 3) (F n) z v) (mfderiv IC (𝓡 3) (F n) z w) := by
  have hlt : ENNReal.ofReal τ < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hτ1
  have ht : t ∈ Icc 0 τ := isClosed_Icc.mem_of_tendsto hlim (Eventually.of_forall htime)
  obtain ⟨φ, hφ, Φ, hcharts, bf, co, hinit, hmono, hcharts', hzero, hpull, hcomplete,
    hjets, hgram, hpde, hsolutions, hconverge, htimeBound⟩ :=
      exists_standard_cylinder_closed_limit τ hτ hlt S x hescape
  let hsrc := standardClosedPointedMaps_sourceSigma Φ
  let htgt := standardClosedPointedMaps_targetSigma Φ
  let e : C ≃ₘ⟮IC, 𝓡 3⟯ cylinderPointedReference.M := cylinderReferenceCopy.equiv
  let ψ := φ ∘ co.φ
  let g := fun n => gSeqExt Φ cylinderReferenceMetric bf hsrc htgt (co.φ n) (time (ψ n))
  let G := fun n => Diffeomorph.pullbackMetricCross (g n) e
  let F : ℕ → PartialDiffeomorph IC (𝓡 3) C E3 ∞ := fun n => e.toPartialDiffeomorph.trans (Φ.partialDiffeomorph (co.φ n))
  have hF (n : ℕ) (z : C) : F n z = Φ.map (co.φ n) (e z) := rfl
  have hid := standard_cylinder_closed_limit_eq_shrinking Φ hsrc htgt hinit bf co hzero
    hgram hpde t ht (ht.2.trans_lt hτ1)
  refine ⟨ψ, G, F, hmono, ?_, ?_, ?_⟩
  · intro K hK p
    have hKe : IsCompact (e '' K) := hK.image e.continuous
    obtain ⟨L, hL, hLip⟩ := htimeBound (e '' K) hKe p
    have hc : MetricCPConvergenceOn (e '' K) p g (co.gInf t) cylinderReferenceMetric := by
      apply metric_cp_convergence_at_tendsto_time (e '' K) p (Icc 0 τ)
        (fun n r => gSeqExt Φ cylinderReferenceMetric bf hsrc htgt (co.φ n) r)
        co.gInf cylinderReferenceMetric (fun n => time (ψ n))
        (fun n => htime (ψ n)) (hlim.comp hmono.tendsto_atTop)
      · intro epsilon hepsilon
        exact co.convergencePt (e '' K) hKe p epsilon hepsilon
      · intro r hr j hj z hz
        exact hLip r hr t ht j hj z hz
    have hp := Perelman.KappaSolutions.metricCPConvOn_pullbackCross
      K p g (co.gInf t) cylinderReferenceMetric e hc
    have hR : Diffeomorph.pullbackMetricCross cylinderReferenceMetric e =
        roundCylinderMetric (E := E3) (n := 2) := pullback_cylinderReferenceMetric
    erw [hid, hR] at hp
    exact hp
  · intro n z
    obtain ⟨hfit, heq⟩ := hcharts (co.φ n)
    have hh : Φ.map (co.φ n) = cylinderReferenceInitialMap
        (pointedInitialRotation (x (ψ n))) ‖x (ψ n)‖ ((co.φ n : ℝ) + 1) hfit :=
      congrArg (fun P : PartialDiffeomorph (𝓡 3) (𝓡 3) cylinderPointedReference.M E3 ∞ =>
        (P : cylinderPointedReference.M → E3)) heq
    erw [hF, hh, cylinderReferenceInitialMap_apply]
    dsimp only [e]
    erw [cylinderReferenceCopy.equiv.symm_apply_apply, initialPolarDiffeomorph_apply]
  · intro K hK
    have hl := co.strictMono.tendsto_atTop.eventually
      (Perelman.KappaSolutions.eventually_gSeqExt_eq_pullback
        Φ cylinderReferenceMetric bf hsrc htgt (e '' K) (hK.image e.continuous))
    filter_upwards [hl] with n hn
    obtain ⟨U, hU, hKU, hUs, hmet⟩ := hn
    refine ⟨e ⁻¹' U, hU.preimage e.continuous,
      (fun z hz => hKU (mem_image_of_mem e hz)), ?_, ?_⟩
    · intro z hz
      exact ⟨mem_univ z, hUs hz⟩
    · intro z hz v w
      have hd (a : TangentSpace IC z) : mfderiv IC (𝓡 3) (F n) z a =
          mfderiv (𝓡 3) (𝓡 3) (Φ.map (co.φ n)) (e z)
            (mfderiv IC (𝓡 3) e z a) := by
        change mfderiv IC (𝓡 3) (Φ.map (co.φ n) ∘ e) z a = _
        exact mfderiv_comp_apply z
          ((Φ.partialDiffeomorph (co.φ n)).mdifferentiableAt (by simp) (hUs hz))
          (e.contMDiff.mdifferentiableAt (by simp)) a
      change (Diffeomorph.pullbackMetricCross (g n) e).inner z v w = _
      erw [Diffeomorph.pullbackMetricCross_inner, hF, hd, hd]
      exact hmet (time (ψ n)) (e z) hz
        (mfderiv IC (𝓡 3) e z v) (mfderiv IC (𝓡 3) e z w)

end DifferentialGeometry.PDE.RicciFlow
