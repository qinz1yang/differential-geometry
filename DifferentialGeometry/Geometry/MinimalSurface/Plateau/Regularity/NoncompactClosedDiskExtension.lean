import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundedProbeEnergy
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.UniformTruncatedCampanato
import DifferentialGeometry.Topology.MetricSpace.TruncatedDistance
import Mathlib.Topology.UniformSpace.UniformEmbedding
import DifferentialGeometry.Geometry.Metric.Completeness.ConnectedComponent
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.TargetBoundaryIdentity

section

noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
  [MetricSpace X]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem uniformContinuousOn_minimizing_target_representative
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (ι : X → M) (hι : ∀ x y, edist x y = riemannianEDistOf g (ι x) (ι y))
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) =
      γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3)
    (v : ℂ → X) (hvc : ContinuousOn v (ball (0 : ℂ) 1))
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (ι (v z)))) :
    UniformContinuousOn v (ball (0 : ℂ) 1) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hedist (a b : M) : edist a b = riemannianEDistOf g a b := rfl
  let e := Complex.orthonormalBasisOneI.repr.symm
  obtain ⟨p, δ, A, hp, _, hδ, hδ8, hA, hprobe⟩ :=
    exists_bounded_probe_truncated_ball_power_bound g hregular γ hγ u hu hmin
      ψ hψ htrace hthird htwothird (ι ∘ v) hae
  obtain ⟨H, hH, hholder⟩ :=
    Analysis.Sobolev.Euclidean.exists_uniform_holder_bound_of_truncated_weak_gradient_power
      (A := 2 * A) (p := p) (δ := δ) (by positivity) hp (by linarith)
  have hpair (x y : ℂ) (hx : x ∈ ball (0 : ℂ) 1) (hy : y ∈ ball (0 : ℂ) 1)
      (hxy : dist x y < δ / 2) : min (dist (v x) (v y)) 1 ≤ H * (dist x y) ^ (p / 2) := by
    let P : M → ℝ := fun z => (min (edist z (ι (v x))) 1).toReal
    have hP : LipschitzWith 1 P := EMetric.lipschitzWith_truncated_edist _
    obtain ⟨hw, hgrad⟩ := hprobe P 1 1 hP.continuous
      (fun z => EMetric.norm_truncated_edist_le_one _ _) (fun z w => by
        simpa only [ENNReal.coe_one, one_mul, hedist] using hP z w)
    let f : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => min (dist (v (e z)) (v x)) 1
    have hPexact (z : EuclideanSpace ℝ (Fin 2)) : P (ι (v (e z))) = f z := by
      change (min (edist (ι (v (e z))) (ι (v x))) 1).toReal = _
      rw [hedist]
      rw [← hι, ENNReal.toReal_min (edist_ne_top _ _) (by simp), ENNReal.toReal_one,
        ← dist_edist]
    have hsame : (fun z => P (ι (v (e z)))) = f := funext hPexact
    have hve : ContinuousOn (v ∘ e) (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      hvc.comp e.continuous.continuousOn (fun z hz => by
        simpa only [mem_ball_zero_iff, e.norm_map] using hz)
    have hdist : ContinuousOn (fun z => dist (v (e z)) (v x))
        (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      continuous_dist.comp_continuousOn (hve.prodMk continuousOn_const)
    have hf : ContinuousOn f (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      continuous_min.comp_continuousOn (hdist.prodMk (continuousOn_const (c := (1 : ℝ))))
    have hx' : e.symm x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      simpa only [mem_ball_zero_iff, e.symm.norm_map] using hx
    have hy' : e.symm y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      simpa only [mem_ball_zero_iff, e.symm.norm_map] using hy
    have hgrad' : ∀ c ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
        ∀ s : ℝ, 0 < s → s ≤ δ →
        (∫ z in ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ ball c s,
          ‖hw.weakGrad z‖ ^ 2) ≤ (2 * A) * s ^ p := by
      intro c hc s hs hsδ
      simpa only [NNReal.coe_one, one_pow, mul_one, mul_assoc] using hgrad c hc s hs hsδ
    have hh := hholder (fun z => P (ι (v (e z)))) hw (hsame.symm ▸ hf) hgrad'
      (e.symm x) hx' (e.symm y) hy' (by simpa only [e.symm.isometry.dist_eq] using hxy)
    simp only [hPexact] at hh
    simpa only [f, e.apply_symm_apply, dist_self, min_eq_left zero_le_one,
      zero_sub, abs_neg, abs_of_nonneg (le_min dist_nonneg zero_le_one),
      e.symm.isometry.dist_eq, dist_comm (v y) (v x)] using hh
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  have hzero : Tendsto (fun r : ℝ => H * r ^ (p / 2)) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun r : ℝ => H * r ^ (p / 2)) 0 := continuousAt_const.mul
      (Real.continuousAt_rpow_const 0 (p / 2) (Or.inr (half_pos hp).le))
    simpa only [Real.zero_rpow (half_pos hp).ne', mul_zero] using hc.tendsto
  obtain ⟨η, hη, hηbound⟩ := Metric.mem_nhds_iff.mp (hzero (Iio_mem_nhds (lt_min hε zero_lt_one)))
  refine ⟨min η (δ / 2), lt_min hη (half_pos hδ), ?_⟩
  intro x hx y hy hxy
  have hnear : dist x y ∈ ball (0 : ℝ) η := by
    simpa only [mem_ball, dist_zero_right, Real.norm_of_nonneg dist_nonneg] using
      hxy.trans_le (min_le_left _ _)
  have hmin : min (dist (v x) (v y)) 1 < min ε 1 :=
    (hpair x y hx hy (hxy.trans_le (min_le_right _ _))).trans_lt (hηbound hnear)
  have hd : dist (v x) (v y) < min ε 1 := by
    rcases min_lt_iff.mp hmin with hd | hn
    · exact hd
    · exact False.elim ((not_lt_of_ge (min_le_right ε 1)) hn)
  exact hd.trans_le (min_le_left ε 1)

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
  [MetricSpace X] [CompleteSpace X]

theorem exists_closed_disk_minimizing_target_representative
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (ι : X → M) (hι : ∀ x y, edist x y = riemannianEDistOf g (ι x) (ι y))
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) =
      γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3)
    (v : ℂ → X) (hvc : ContinuousOn v (ball (0 : ℂ) 1))
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (ι (v z)))) :
    ∃ q : C(closedDisk, X), UniformContinuous q ∧
      (∀ z (hz : z ∈ ball (0 : ℂ) 1), q ⟨z, ball_subset_closedBall hz⟩ = v z) ∧
      IsCompact (range q) ∧ MapsTo v (ball (0 : ℂ) 1) (range q) := by
  have hv := uniformContinuousOn_minimizing_target_representative g hregular ι hι γ hγ u hu hmin
    ψ hψ htrace hthird htwothird v hvc hae
  let D : Set ℂ := ball 0 1
  let i : D → closedDisk := Set.inclusion ball_subset_closedBall
  have hi : Isometry i := fun _ _ => rfl
  have hdense : DenseRange i := (denseRange_inclusion_iff ball_subset_closedBall).mpr (by
    rw [closure_ball (0 : ℂ) one_ne_zero])
  let q₀ := (hi.isUniformInducing.isDenseInducing hdense).extend (fun z : D => v z)
  have hq : UniformContinuous q₀ :=
    uniformContinuous_uniformly_extend hi.isUniformInducing hdense hv.restrict
  have heq (z : D) : q₀ (i z) = v z :=
    uniformly_extend_of_ind hi.isUniformInducing hdense hv.restrict z
  let q : C(closedDisk, X) := ⟨q₀, hq.continuous⟩
  refine ⟨q, hq, (fun z hz => heq ⟨z, hz⟩), isCompact_range q.continuous, ?_⟩
  intro z hz
  exact ⟨i ⟨z, hz⟩, heq ⟨z, hz⟩⟩

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_closed_disk_component_limit_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) =
      γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3)
    (v : ℂ → connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))
    (hvc : ContinuousOn v (ball (0 : ℂ) 1))
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z : M))) :
    ∃ q : C(closedDisk, connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)),
      (∀ z (hz : z ∈ ball (0 : ℂ) 1), q ⟨z, ball_subset_closedBall hz⟩ = v z) ∧
      IsCompact (range q) ∧ MapsTo v (ball (0 : ℂ) 1) (range q) := by
  let C := connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)
  let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
  let : ConnectedSpace C := connectedComponentOpen_connectedSpace (I := 𝓘(ℝ, E)) (γ 0)
  let : IsManifold 𝓘(ℝ, E) 1 C :=
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := C) (n := ∞) (by decide)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : C → Type _) := ⟨gC.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : C → Type _) :=
    ⟨gC.inner, gC.contMDiff.continuous, fun _ _ _ => rfl⟩
  let eC : EMetricSpace C := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) C
  let : EMetricSpace C := eC
  let : CompleteSpace C := hg.restrict_connectedComponent g (γ 0)
  let mC : MetricSpace C := EMetricSpace.toMetricSpace
    (fun x y : C => DifferentialGeometry.Analysis.edist_ne_top_of_preconnected x y)
  let : MetricSpace C := mC
  have hdist (x y : C) : edist x y = riemannianEDistOf g (x : M) (y : M) :=
    Metric.edistOf_restrictOpen_connCompOpen g (γ 0) x y
  obtain ⟨q, _, hq, hcompact, hrange⟩ := exists_closed_disk_minimizing_target_representative
    g hregular (Subtype.val : C → M) hdist γ hγ u hu hmin ψ hψ htrace hthird htwothird v hvc hae
  exact ⟨q, hq, hcompact, hrange⟩

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_closed_disk_component_limit_with_trace_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) =
      γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3)
    (v : ℂ → connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))
    (hvc : ContinuousOn v (ball (0 : ℂ) 1))
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z : M)))
    (η : C(loopCircle, connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)))
    (hboundary : ∀ θ : loopCircle,
      Tendsto (fun n => u n (diskBoundary θ)) atTop (𝓝 (η θ : M))) :
    ∃ q : C(closedDisk, connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)),
      (∀ z (hz : z ∈ ball (0 : ℂ) 1), q ⟨z, ball_subset_closedBall hz⟩ = v z) ∧
      diskTrace q = η ∧ IsCompact (range q) ∧ MapsTo v (ball (0 : ℂ) 1) (range q) := by
  let C := connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)
  let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
  let : ConnectedSpace C := connectedComponentOpen_connectedSpace (I := 𝓘(ℝ, E)) (γ 0)
  let : IsManifold 𝓘(ℝ, E) 1 C :=
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := C) (n := ∞) (by decide)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : C → Type _) := ⟨gC.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : C → Type _) :=
    ⟨gC.inner, gC.contMDiff.continuous, fun _ _ _ => rfl⟩
  let eC : EMetricSpace C := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) C
  let : EMetricSpace C := eC
  let : CompleteSpace C := hg.restrict_connectedComponent g (γ 0)
  let mC : MetricSpace C := EMetricSpace.toMetricSpace
    (fun x y : C => DifferentialGeometry.Analysis.edist_ne_top_of_preconnected x y)
  let : MetricSpace C := mC
  have hdist (x y : C) : edist x y = riemannianEDistOf g (x : M) (y : M) :=
    Metric.edistOf_restrictOpen_connCompOpen g (γ 0) x y
  obtain ⟨q, _, hq, hcompact, hrange⟩ := exists_closed_disk_minimizing_target_representative
    g hregular (Subtype.val : C → M) hdist γ hγ u hu hmin ψ hψ htrace hthird htwothird v hvc hae
  have haeQ : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 ((diskExtension q z : C) : M)) := by
    filter_upwards [hae, ae_restrict_mem measurableSet_ball] with z hz hzD
    have heq : diskExtension q z = v z :=
      (diskExtension_coe q ⟨z, ball_subset_closedBall hzD⟩).trans (hq z hzD)
    rwa [heq]
  obtain ⟨B, hB⟩ := hmin.bddAbove_range
  have htraceQ := diskTrace_eq_of_intrinsic_energy_bounded_ae_limit g
    (Subtype.val : C → M) hdist u q η (fun n => (hu n).2) haeQ hboundary
      (fun n => hB (mem_range_self n))
  exact ⟨q, hq, htraceQ, hcompact, hrange⟩

end DifferentialGeometry.Geometry

end

end
