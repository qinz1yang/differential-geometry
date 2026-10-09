import DifferentialGeometry.Analysis.Integration.Measure.OrbitHaar
import DifferentialGeometry.Analysis.Integration.Measure.FundamentalDomain
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoostContinuity
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometryVolume
import DifferentialGeometry.Geometry.Metric.Isometry.Compactness
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

noncomputable section

open MeasureTheory
open scoped Manifold NNReal ENNReal

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

private local instance : MeasurableSpace (Hyperboloid E) := borel (Hyperboloid E)
private local instance : BorelSpace (Hyperboloid E) := ⟨rfl⟩

theorem exists_pos_map_haar_apply_symm_eq_smul_riemannianVolumeMeasure
    (Φ : (Hyperboloid E ≃ᵢ Hyperboloid E) ≃ₜ* G)
    (μG : Measure G) [Measure.IsHaarMeasure μG] :
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map (fun g : G => Φ.symm g (origin : Hyperboloid E)) μG =
        c • Integral.Measure.riemannianVolumeMeasure
          𝓘(ℝ, E) (Hyperboloid E) riemannianMetric := by
  let _ : MulAction G (Hyperboloid E) :=
    MulAction.compHom (Hyperboloid E) Φ.symm.toMonoidHom
  let _ : ContinuousSMul G (Hyperboloid E) := ⟨by
    change Continuous (fun z : G × Hyperboloid E => Φ.symm z.1 z.2)
    exact continuous_eval.comp ((Φ.symm.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  let K := MulAction.stabilizer G (origin : Hyperboloid E)
  have hKset : (K : Set G) = Φ ''
      {f : Hyperboloid E ≃ᵢ Hyperboloid E | dist (f origin) origin ≤ 0} := by
    ext g
    constructor
    · intro hg
      refine ⟨Φ.symm g, ?_, Φ.apply_symm_apply g⟩
      have hg' : Φ.symm g (origin : Hyperboloid E) = origin := hg
      simp only [Set.mem_ofPred_eq, hg', dist_self, le_refl]
    · rintro ⟨f, hf, rfl⟩
      change Φ.symm (Φ f) (origin : Hyperboloid E) = origin
      rw [Φ.symm_apply_apply]
      exact dist_le_zero.mp hf
  have hK : IsCompact (K : Set G) := by
    rw [hKset]
    exact (IsometryEquiv.isCompact_setOf_dist_apply_le (origin : Hyperboloid E) 0).image
      Φ.continuous
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μ := Integral.Measure.riemannianVolumeMeasure
    𝓘(ℝ, E) (Hyperboloid E) (riemannianMetric (E := E))
  let _ : SigmaFinite μ := Integral.Measure.riemannianVolumeMeasure_sigmaFinite riemannianMetric
  let _ : IsFiniteMeasureOnCompacts μ :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasureOnCompacts riemannianMetric
  let _ : Measure.IsOpenPosMeasure μ :=
    Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure riemannianMetric
  let _ : SMulInvariantMeasure G (Hyperboloid E) μ := ⟨by
    intro g S hS
    exact (measurePreserving_isometryEquiv (Φ.symm g)).measure_preimage hS.nullMeasurableSet⟩
  let s : Hyperboloid E → G := fun x => Φ (boost x)
  have hs : ∀ x : Hyperboloid E, s x • origin = x := by
    intro x
    change Φ.symm (Φ (boost x)) origin = x
    rw [Φ.symm_apply_apply, boost_origin]
  have hc : Continuous s := Φ.continuous.comp continuous_boost
  exact MulAction.exists_pos_map_haar_orbit_eq_smul origin s hs hc μG μ

theorem hasFundamentalDomain_and_covolume_ne_top_map_of_fundamental_domain
    (Φ : (Hyperboloid E ≃ᵢ Hyperboloid E) ≃ₜ* G)
    (μG : Measure G) [Measure.IsHaarMeasure μG]
    (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E)) [Countable Γ]
    {D : Set (Hyperboloid E)} (hD : MeasurableSet D)
    (hrep : ∀ x : Hyperboloid E, ∃! γ : Γ, γ • x ∈ D)
    (hfin : Integral.Measure.riemannianVolumeMeasure
      𝓘(ℝ, E) (Hyperboloid E) riemannianMetric D ≠ ⊤) :
    HasFundamentalDomain (Γ.map Φ.toMonoidHom) G μG ∧
      covolume (Γ.map Φ.toMonoidHom) G μG ≠ ⊤ := by
  let Λ := Γ.map Φ.toMonoidHom
  let ψ : Γ ≃* Λ := Φ.toMulEquiv.subgroupMap Γ
  let _ : Countable Λ := Countable.of_equiv Γ ψ.toEquiv
  let _ : MulAction Λ (Hyperboloid E) :=
    MulAction.compHom (Hyperboloid E) (Φ.symm.toMonoidHom.comp Λ.subtype)
  have hact (γ : Γ) (x : Hyperboloid E) : ψ γ • x = γ • x := by
    change Φ.symm (Φ (γ : Hyperboloid E ≃ᵢ Hyperboloid E)) x =
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E) x
    rw [Φ.symm_apply_apply]
  have hrepΛ (x : Hyperboloid E) : ∃! a : Λ, a • x ∈ D := by
    obtain ⟨γ, hγ, hγunique⟩ := hrep x
    refine ⟨ψ γ, ?_, ?_⟩
    · change ψ γ • x ∈ D
      rwa [hact]
    · intro a ha
      obtain ⟨δ, rfl⟩ := ψ.surjective a
      apply congrArg ψ
      exact hγunique δ (by rwa [hact] at ha)
  let p : G → Hyperboloid E := fun a => Φ.symm a origin
  have hp : Measurable p := ((continuous_eval_const origin).comp Φ.symm.continuous).measurable
  have hequiv (a : Λ) (g : G) : p (a • g) = a • p g := by
    change Φ.symm ((a : G) * g) origin = Φ.symm (a : G) (Φ.symm g origin)
    rw [map_mul]
    rfl
  obtain ⟨c, _, hc⟩ := exists_pos_map_haar_apply_symm_eq_smul_riemannianVolumeMeasure Φ μG
  exact MeasureTheory.hasFundamentalDomain_and_covolume_ne_top_of_map_eq_smul μG
    (Integral.Measure.riemannianVolumeMeasure 𝓘(ℝ, E) (Hyperboloid E) riemannianMetric)
    hp hequiv (c : ℝ≥0∞) ENNReal.coe_ne_top hc hD hrepΛ hfin

end DifferentialGeometry.Hyperboloid
