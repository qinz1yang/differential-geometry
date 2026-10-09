import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundaryPower
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.TruncatedCampanato
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.EmbeddedSequence
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.BoundaryApproach
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.BoundaryConvergence
import DifferentialGeometry.Analysis.Integration.Measure.ContinuousRepresentative
import DifferentialGeometry.Topology.LoopSpace.PolarAnnulus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.ContinuousMap.Compact

noncomputable section

open Manifold Set Metric Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι

theorem uniformContinuousOn_representative_of_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (γ : freeLoop M) {KΓ J : ℝ≥0}
    (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (hInv : AntilipschitzWith J (fun θ : loopCircle => Φ (γ θ)))
    {U : Set F} {η : ℝ} (hη : 0 < η)
    (hηU : ∀ p ∈ range Φ, closedBall p η ⊆ U)
    (T : F → F) (LT : ℝ≥0) (hT : Differentiable ℝ T)
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hmap : MapsTo T U (range Φ))
    (hfix : ∀ y ∈ range Φ, T y = y)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) = γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3)
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (ball (0 : V) 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (ball (0 : V) 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict (ball (0 : V) 1)]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (ball (0 : V) 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (ball (0 : V) 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (v : V → F) (hvc : ContinuousOn v (ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (ball (0 : V) 1)] w) :
    UniformContinuousOn v (ball (0 : V) 1) := by
  obtain ⟨α, C, R₀, hα, _, _, hR₀, _, hpower⟩ :=
    exists_uniform_weak_gradient_power_bound_on_truncated_balls
      g hΦ hN hr hΦN hleft γ hΓ hInv hη hηU T LT hT hLT hmap hfix
      u hu hmin ψ hψ htrace hthird htwothird w hs hw hrep hL2 hae hweak
  let hv (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => v x i) (ball (0 : V) 1) :=
    (hw i).congr (hvw.symm.mono fun x hx => congrArg (fun z : F => z i) hx)
  exact Sobolev.Euclidean.uniformContinuousOn_of_weak_gradient_power_bound_on_truncated_balls
    (C := C) hv hvc hα hR₀ (fun x hx s hs hsR => hpower x hx s ⟨hs, hsR⟩)

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Filter MeasureTheory ContinuousMap
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_closed_disk_extension_of_uniformContinuousOn_embedded_limit
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (v : V → F) (hv : UniformContinuousOn v (Metric.ball (0 : V) 1))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (v x)))
    (τ : C(loopCircle, loopCircle))
    (htrace : Tendsto (fun n => diskTrace (u n)) atTop (𝓝 (γ.comp τ))) :
    ∃ (q : C(closedDisk, M)) (qF : C(closedDisk, F)),
      (∀ z, Φ (q z) = qF z) ∧
      (∀ z (hz : z ∈ Metric.ball (0 : ℂ) 1),
        qF ⟨z, Metric.ball_subset_closedBall hz⟩ = v (Complex.orthonormalBasisOneI.repr z) ∧
        q ⟨z, Metric.ball_subset_closedBall hz⟩ = r (v (Complex.orthonormalBasisOneI.repr z))) ∧
      diskTrace q = γ.comp τ := by
  obtain ⟨Ku, _, B, _, hLip, _, _, _, _, henergy, _, _, _⟩ :=
    exists_embedded_minimizing_sequence_bounds g hΦ hN hr hΦN hleft u hu hmin
  have hΦclosed : IsClosed (range Φ) := (isCompact_range hΦ.continuous).isClosed
  have hvKae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), v x ∈ range Φ :=
    hae.mono fun x hx => hΦclosed.mem_of_tendsto hx
      (Eventually.of_forall fun n => mem_range_self _)
  have hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ) :=
    MeasureTheory.ContinuousOn.mapsTo_of_ae_mem_closed volume Metric.isOpen_ball
      hΦclosed hv.continuousOn hvKae
  let e := Complex.orthonormalBasisOneI.repr
  let vc : ℂ → F := v ∘ e
  let θ : ℂ → loopCircle := fun z =>
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (radialDirection z)
  let η : ℂ → F := fun z => Φ (γ (τ (θ z)))
  have hemap : MapsTo e (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : V) 1) := by
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right, e.norm_map] using hz
  have hvc : UniformContinuousOn vc (Metric.ball (0 : ℂ) 1) :=
    hv.comp e.isometry.uniformContinuous.uniformContinuousOn hemap
  have haeC : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      Tendsto (fun n => Φ (diskExtension (u n) z)) atTop (𝓝 (vc z)) := by
    have hq := e.measurePreserving.quasiMeasurePreserving.restrict hemap
    have hh := hq.ae hae
    simpa only [e, vc, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply] using hh
  let P : C(M, F) := ⟨Φ, hΦ.continuous⟩
  have htr : Tendsto (fun n => diskTrace (P.comp (u n))) atTop
      (𝓝 (P.comp (γ.comp τ))) := ((continuous_postcomp P).tendsto (γ.comp τ)).comp htrace
  have hboundary (z : ℂ) (hz : ‖z‖ = 1) :
      Tendsto (fun n => Φ (diskExtension (u n) z)) atTop (𝓝 (η z)) := by
    let c : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
    have hc : radialDirection z = c := radialDirection_unit c
    have hh := tendstoUniformly_diskExtension_boundary_of_tendsto_diskTrace htr
      (fun _ : Unit => c)
    have hpoint := hh.tendsto_at ()
    change Tendsto (fun n => Φ (u n (diskRetraction z))) atTop
      (𝓝 (Φ (γ (τ ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm c))))) at hpoint
    simpa only [diskExtension, η, θ, hc, Function.comp_apply] using hpoint
  have hη : ContinuousOn η (Metric.sphere (0 : ℂ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hrad : Continuous (fun z : Metric.sphere (0 : ℂ) 1 => radialDirection z) := by
      have hc : Continuous (fun z : Metric.sphere (0 : ℂ) 1 =>
          (⟨(z : ℂ), z.property⟩ : Circle)) := continuous_subtype_val.subtype_mk _
      have heq : (fun z : Metric.sphere (0 : ℂ) 1 => radialDirection z) =
          (fun z : Metric.sphere (0 : ℂ) 1 => (⟨(z : ℂ), z.property⟩ : Circle)) := by
        funext z
        exact radialDirection_unit ⟨z, z.property⟩
      rw [heq]
      exact hc
    exact hΦ.continuous.comp (γ.continuous.comp (τ.continuous.comp
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous.comp hrad)))
  obtain ⟨qF, _, hqFv, hqFη, hqFK⟩ :=
    Analysis.exists_continuous_disk_extension_of_lipschitz_sequence_energy_bound
      (fun n => Φ ∘ diskExtension (u n)) vc η Ku hLip hvc haeC hboundary hη henergy
  have hqrange : range qF ⊆ range Φ :=
    hqFK (range Φ) (isCompact_range hΦ.continuous).isClosed (hvK.comp hemap)
  have hrc : ContinuousOn r (range Φ) := hr.continuousOn.mono hΦN
  let q : C(closedDisk, M) :=
    ⟨r ∘ qF, hrc.comp_continuous qF.continuous (fun z => hqrange (mem_range_self z))⟩
  have hΦq (z : closedDisk) : Φ (q z) = qF z := by
    obtain ⟨m, hm⟩ := hqrange (mem_range_self z)
    change Φ (r (qF z)) = qF z
    rw [← hm, hleft]
  refine ⟨q, qF, hΦq, ?_, ?_⟩
  · intro z hz
    refine ⟨hqFv z hz, ?_⟩
    change r (qF ⟨z, Metric.ball_subset_closedBall hz⟩) = _
    rw [hqFv z hz]
    rfl
  · ext t
    have hz : (diskBoundary t : ℂ) ∈ Metric.sphere (0 : ℂ) 1 :=
      (AddCircle.toCircle t).property
    have hval := hqFη (diskBoundary t : ℂ) hz
    have hθ : θ (diskBoundary t : ℂ) = t := by
      rw [show (diskBoundary t : ℂ) = (AddCircle.toCircle t : ℂ) by rfl]
      dsimp only [θ]
      rw [radialDirection_unit, ← AddCircle.homeomorphCircle_apply one_ne_zero,
        Homeomorph.symm_apply_apply]
    change r (qF (diskBoundary t)) = γ (τ t)
    have hval' : qF (diskBoundary t) = η (diskBoundary t : ℂ) := hval
    rw [hval']
    dsimp only [η]
    rw [hθ, hleft]

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Metric Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι

theorem exists_closed_disk_extension_of_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (γ : freeLoop M) {KΓ J : ℝ≥0}
    (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (hInv : AntilipschitzWith J (fun θ : loopCircle => Φ (γ θ)))
    {U : Set F} {η : ℝ} (hη : 0 < η)
    (hηU : ∀ p ∈ range Φ, closedBall p η ⊆ U)
    (T : F → F) (LT : ℝ≥0) (hT : Differentiable ℝ T)
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hmap : MapsTo T U (range Φ))
    (hfix : ∀ y ∈ range Φ, T y = y)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) = γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3)
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (ball (0 : V) 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (ball (0 : V) 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict (ball (0 : V) 1)]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (ball (0 : V) 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (ball (0 : V) 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (v : V → F) (hvc : ContinuousOn v (ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (ball (0 : V) 1)] w)
    (τ : C(loopCircle, loopCircle))
    (htraceLimit : Tendsto (fun n => diskTrace (u n)) atTop (𝓝 (γ.comp τ))) :
    ∃ (q : C(closedDisk, M)) (qF : C(closedDisk, F)),
      (∀ z, Φ (q z) = qF z) ∧
      (∀ z (hz : z ∈ ball (0 : ℂ) 1),
        qF ⟨z, ball_subset_closedBall hz⟩ = v (Complex.orthonormalBasisOneI.repr z) ∧
        q ⟨z, ball_subset_closedBall hz⟩ = r (v (Complex.orthonormalBasisOneI.repr z))) ∧
      diskTrace q = γ.comp τ := by
  have huc := uniformContinuousOn_representative_of_disk_energy_minimizing_sequence
    g hΦ hN hr hΦN hleft γ hΓ hInv hη hηU T LT hT hLT hmap hfix
    u hu hmin ψ hψ htrace hthird htwothird w hs hw hrep hL2 hae hweak v hvc hvw
  have haev : ∀ᵐ x ∂volume.restrict (ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (v x)) := by
    filter_upwards [hae, hvw] with x hx hxv
    rwa [hxv]
  exact exists_closed_disk_extension_of_uniformContinuousOn_embedded_limit
    g (hΦ.of_le (by simp)) hN (hr.of_le (by simp)) hΦN hleft u hu hmin v huc haev τ htraceLimit

end DifferentialGeometry.Geometry

end
