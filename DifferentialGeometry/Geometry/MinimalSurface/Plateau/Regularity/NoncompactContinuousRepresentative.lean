import DifferentialGeometry.Analysis.Integration.Measure.MetricTargetRepresentative
import DifferentialGeometry.Topology.MetricSpace.TruncatedDistance
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProbeEnergy
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.UniformCampanato
import DifferentialGeometry.Analysis.Integration.Measure.ContinuousRepresentative
import DifferentialGeometry.Geometry.Metric.Completeness.ConnectedComponent
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Component
import Mathlib.Geometry.Manifold.Metrizable

section

set_option autoImplicit false
noncomputable section

open Bundle Set Filter MeasureTheory Metric Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
  [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_continuous_representative_of_minimizing_sequence_in_complete_target
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (ι : X → M) (hι : ∀ x y, edist x y = riemannianEDistOf g (ι x) (ι y))
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M)) (v : ℂ → X)
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (ι (v z)))) :
    ∃ V : EuclideanSpace ℝ (Fin 2) → X,
      ContinuousOn V (ball 0 1) ∧
      V =ᵐ[volume.restrict (ball 0 1)] (fun x => v (Complex.orthonormalBasisOneI.repr.symm x)) := by
  classical
  let : Nonempty X := ⟨v 0⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  obtain ⟨N, B, θ, _, hB, hθ, hθ1, hprobe⟩ :=
    exists_memW1pWitness_bounded_probe_dyadic_energy_of_minimizing_sequence
      g hregular γ u (ι ∘ v) hu hmin hae
  obtain ⟨α, hα, _, hHolder⟩ :=
    Analysis.Sobolev.Euclidean.exists_uniform_local_holder_representative_of_dyadic_energy_bound
      hθ.le hθ1
  obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq X
  let P : ℕ → M → ℝ := fun i p => (min (riemannianEDistOf g p (ι (a i))) 1).toReal
  have hPLip (i : ℕ) : LipschitzWith 1 (P i) := EMetric.lipschitzWith_truncated_edist (ι (a i))
  have hPBound (i : ℕ) (p : M) : ‖P i p‖ ≤ (1 : ℝ) := EMetric.norm_truncated_edist_le_one p _
  have hPX (i : ℕ) (x : X) : P i (ι x) = min (dist x (a i)) 1 := by
    change (min (riemannianEDistOf g (ι x) (ι (a i))) 1).toReal = _
    rw [← hι, ENNReal.toReal_min (edist_ne_top _ _) (by simp),
      ENNReal.toReal_one, ← dist_edist]
  have hexists (i : ℕ) : ∃ hw : DeGiorgi.MemW1pWitness 2
      (fun x => P i (ι (v (e x)))) (ball 0 1),
      ∀ (b : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R → ‖b‖ + R < 1 → ∀ k : ℕ,
        (∫ x in ball b (R / 2 ^ (N + k)), ‖hw.weakGrad x‖ ^ 2) ≤ θ ^ k * (2 * B) := by
    obtain ⟨hw, hbound⟩ := hprobe (P i) 1 1 (hPLip i).continuous (hPBound i) (hPLip i)
    refine ⟨hw, ?_⟩
    intro b R hR hbr k
    have hh := hbound b R hR hbr k
    norm_num only [NNReal.coe_one, one_pow, mul_one] at hh
    exact hh.trans_eq (by ring)
  choose hw hdec using hexists
  apply MeasureTheory.exists_continuousOn_ae_eq_of_locally_continuousOn_ae_eq volume
  intro x₀ hx₀
  have hxnorm : ‖x₀‖ < 1 := mem_ball_zero_iff.mp hx₀
  obtain ⟨r, H, hr, hH, hball, hHrep⟩ := hHolder N (2 * B) (by positivity) x₀ hxnorm
  have hscalar (i : ℕ) : ∃ w : EuclideanSpace ℝ (Fin 2) → ℝ,
      w =ᵐ[volume.restrict (ball x₀ r)] (fun x => P i (ι (v (e x)))) ∧
      ∀ x ∈ ball x₀ (r / 2), ∀ y ∈ ball x₀ (r / 2),
        |w x - w y| ≤ H * ‖x - y‖ ^ α := by
    obtain ⟨w, hwae, _, hwh⟩ := hHrep _ (hw i) (hdec i)
    exact ⟨w, hwae, fun x hx y hy => by simpa only [Real.norm_eq_abs] using hwh x hx y hy⟩
  choose w hwae hwh using hscalar
  let Ω := ball x₀ (r / 2)
  have hsmall : Ω ⊆ ball x₀ r := ball_subset_ball (by linarith)
  have hwae' (i : ℕ) : w i =ᵐ[volume.restrict Ω] (fun x => min (dist (v (e x)) (a i)) 1) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsmall (hwae i)] with x hx
    exact hx.trans (hPX i (v (e x)))
  have hω : Tendsto (fun s : ℝ => H * s ^ α) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℝ => s ^ α) 0 :=
      (continuousAt_id.rpow_const (Or.inr hα.le))
    simpa only [Real.zero_rpow hα.ne', mul_zero] using hc.tendsto.const_mul H
  obtain ⟨F, hF, hFae⟩ :=
    DifferentialGeometry.Topology.exists_continuousOn_ae_eq_of_truncated_distance_modulus_on_open
      (μ := volume) isOpen_ball ha (fun x => v (e x)) w hwae' hω
      (fun i x hx y hy => by simpa only [dist_eq_norm] using hwh i x hx y hy)
  exact ⟨Ω, F, isOpen_ball, mem_ball_self (half_pos hr), hsmall.trans hball, hF, hFae⟩

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Set Filter MeasureTheory Metric Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_continuous_component_representative_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (v : ℂ → connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z : M))) :
    ∃ V : ℂ → connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0),
      ContinuousOn V (ball (0 : ℂ) 1) ∧ V =ᵐ[volume.restrict (ball (0 : ℂ) 1)] v := by
  let C := connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)
  let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
  let : ConnectedSpace C := connectedComponentOpen_connectedSpace (I := 𝓘(ℝ, E)) (γ 0)
  let : SigmaCompactSpace C := sigmaCompactSpace_connectedComponent_of_riemannianMetric g (γ 0)
  let : IsManifold 𝓘(ℝ, E) 1 C := IsManifold.of_le (I := 𝓘(ℝ, E)) (M := C) (n := ∞) (by decide)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : C → Type _) := ⟨gC.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : C → Type _) :=
    ⟨gC.inner, gC.contMDiff.continuous, fun _ _ _ => rfl⟩
  let eC : EMetricSpace C := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) C
  let : EMetricSpace C := eC
  let : CompleteSpace C := hg.restrict_connectedComponent g (γ 0)
  let mC : MetricSpace C := EMetricSpace.toMetricSpace
    (fun x y : C => DifferentialGeometry.Analysis.edist_ne_top_of_preconnected x y)
  let : MetricSpace C := mC
  have hsep : TopologicalSpace.SeparableSpace C := inferInstance
  let : TopologicalSpace.SeparableSpace C := hsep
  have hdist (x y : C) : edist x y = riemannianEDistOf g (x : M) (y : M) :=
    Metric.edistOf_restrictOpen_connCompOpen g (γ 0) x y
  obtain ⟨W, hW, hWae⟩ :=
    exists_continuous_representative_of_minimizing_sequence_in_complete_target
      g hregular (Subtype.val : C → M) hdist γ u v hu hmin hae
  let e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  have hmap : MapsTo e (ball (0 : ℂ) 1) (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    intro z hz
    simpa only [mem_ball_zero_iff, e.norm_map] using hz
  refine ⟨W ∘ e, hW.comp e.continuous.continuousOn hmap, ?_⟩
  have hpre : e ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 2)) 1 = ball (0 : ℂ) 1 := by
    ext z
    simp only [mem_preimage, mem_ball_zero_iff, e.norm_map]
  have he := e.measurePreserving.restrict_preimage
    (s := ball (0 : EuclideanSpace ℝ (Fin 2)) 1) measurableSet_ball
  rw [hpre] at he
  have hh := he.quasiMeasurePreserving.ae hWae
  filter_upwards [hh] with z hz
  simpa only [Function.comp_apply, e, LinearIsometryEquiv.symm_apply_apply] using hz

end DifferentialGeometry.Geometry

end

end
