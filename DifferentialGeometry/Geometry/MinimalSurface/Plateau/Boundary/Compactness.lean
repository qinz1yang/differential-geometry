import DifferentialGeometry.Topology.Manifold.Embedding.CompactNeighborhood
import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone.Closure
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Topology.LoopSpace.HomeomorphismLift
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.CompactConvergence
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.BoundaryCompactness
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Composition
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction

noncomputable section

open Set Filter Function ContinuousMap
open scoped Topology
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

private theorem DiskWeakJordanTrace.of_forall_of_tendsto
    {M A : Type*} [TopologicalSpace M] [T2Space M]
    {γ : freeLoop M} (hγ : Topology.IsEmbedding γ)
    {l : Filter A} [l.NeBot] {u : A → C(closedDisk, M)} {v : C(closedDisk, M)}
    (hu : ∀ a, DiskWeakJordanTrace γ (u a)) (hlim : Tendsto u l (𝓝 v)) :
    DiskWeakJordanTrace γ v := by
  classical
  choose σ hσ htrace using hu
  have htraceLim : Tendsto (fun a => diskTrace (u a)) l (𝓝 (diskTrace v)) :=
    (continuous_precomp diskBoundary).tendsto _ |>.comp hlim
  have hrange (t : loopCircle) : diskTrace v t ∈ range γ := by
    apply (isCompact_range γ.continuous).isClosed.mem_of_tendsto
      ((continuous_eval_const t).tendsto _ |>.comp htraceLim)
    exact Eventually.of_forall fun a =>
      ⟨σ a t, (congrArg (fun f : freeLoop M => f t) (htrace a)).symm⟩
  let τ : C(loopCircle, loopCircle) :=
    ⟨fun t => hγ.toHomeomorph.symm ⟨diskTrace v t, hrange t⟩,
      hγ.toHomeomorph.symm.continuous.comp ((diskTrace v).continuous.subtype_mk _)⟩
  have hτ : diskTrace v = γ.comp τ := by
    ext t
    exact congrArg Subtype.val (hγ.toHomeomorph.apply_symm_apply
      ⟨diskTrace v t, hrange t⟩) |>.symm
  have hσlim : Tendsto σ l (𝓝 τ) := by
    apply (isEmbedding_postcomp γ hγ).isInducing.tendsto_nhds_iff.mpr
    simpa only [Function.comp_def, ← htrace, ← hτ] using htraceLim
  exact ⟨τ, IsWeaklyMonotoneOnce.of_tendsto (Eventually.of_forall hσ) hσlim, hτ⟩

theorem isClosed_diskWeakJordanTrace
    {M : Type*} [TopologicalSpace M] [T2Space M]
    {γ : freeLoop M} (hγ : Topology.IsEmbedding γ) :
    IsClosed {u : C(closedDisk, M) | DiskWeakJordanTrace γ u} := by
  apply isClosed_iff_forall_filter.mpr
  intro u l hl hset hlim
  let S := {u : C(closedDisk, M) | DiskWeakJordanTrace γ u}
  let : l.NeBot := hl
  let : (comap ((↑) : S → C(closedDisk, M)) l).NeBot :=
    comap_coe_neBot_of_le_principal hset
  apply DiskWeakJordanTrace.of_forall_of_tendsto (l := comap ((↑) : S → C(closedDisk, M)) l)
    hγ (fun v : S => v.property)
  exact (tendsto_id.mono_right hlim).comp tendsto_comap

theorem DiskWeakJordanTrace.of_tendsto
    {M A : Type*} [TopologicalSpace M] [T2Space M]
    {γ : freeLoop M} (hγ : Topology.IsEmbedding γ)
    {l : Filter A} [l.NeBot] {u : A → C(closedDisk, M)} {v : C(closedDisk, M)}
    (hu : ∀ᶠ a in l, DiskWeakJordanTrace γ (u a)) (hlim : Tendsto u l (𝓝 v)) :
    DiskWeakJordanTrace γ v :=
  (isClosed_diskWeakJordanTrace hγ).mem_of_tendsto hlim hu

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold MeasureTheory Set ContinuousMap Filter
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

theorem exists_subseq_tendsto_diskTrace_of_normalized_energy_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) (hγ : _root_.Topology.IsEmbedding γ)
    (u : ℕ → C(closedDisk, M))
    (hLip : ∀ n, ∃ K : ℝ≥0, ∀ x y,
      riemannianEDistOf g (u n x) (u n y) ≤ (K : ℝ≥0∞) * edist x y)
    {B : ℝ} (henergy : ∀ n, riemannianDiskEnergy g (u n) ≤ B)
    (σ : ℕ → C(loopCircle, loopCircle)) (hσ : ∀ n, IsWeaklyMonotoneOnce (σ n))
    (htrace : ∀ n, diskTrace (u n) = γ.comp (σ n))
    (h0 : ∀ n, σ n 0 = 0)
    (h1 : ∀ n, σ n ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle))
    (h2 : ∀ n, σ n ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle)) :
    ∃ (τ : C(loopCircle, loopCircle)) (φ : ℕ → ℕ),
      StrictMono φ ∧ IsWeaklyMonotoneOnce τ ∧
      τ 0 = 0 ∧ τ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle) ∧
      τ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle) ∧
      Tendsto (σ ∘ φ) atTop (𝓝 τ) ∧
      Tendsto (fun n => diskTrace (u (φ n))) atTop (𝓝 (γ.comp τ)) := by
  obtain ⟨d, Φ, hΦ, hΦc, hΦγ⟩ :=
    exists_contMDiff_compactly_supported_euclidean_embedding_comp (I := 𝓘(ℝ, E)) γ hγ
  obtain ⟨C, _, hC⟩ := exists_integral_norm_fderiv_comp_diskExtension_sq_le_of_hasCompactSupport
    g (hΦ.of_le (by simp)) hΦc
  choose K hK using hLip
  let f : ℕ → ℂ → EuclideanSpace ℝ (Fin d) := fun n => Φ ∘ diskExtension (u n)
  let Γ : C(loopCircle, EuclideanSpace ℝ (Fin d)) := ⟨Φ ∘ γ, hΦ.continuous.comp γ.continuous⟩
  have hf (n : ℕ) : LipschitzWith (C * K n) (f n) := (hC (u n) (K n) (hK n)).1
  have hbound (n : ℕ) :
      (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2) ≤
        4 * (C : ℝ) ^ 2 * B := by
    exact ((hC (u n) (K n) (hK n)).2.2).trans
      (mul_le_mul_of_nonneg_left (henergy n) (by positivity))
  have hboundary (n : ℕ) (t : ℝ) :
      f n (circleMap 0 1 (2 * Real.pi * t)) = Γ (σ n (t : loopCircle)) := by
    have he : circleMap 0 1 (2 * Real.pi * t) =
        (diskBoundary (t : loopCircle) : ℂ) := by
      rw [diskBoundary_coe]
      simp [circleMap]
    change Φ (diskExtension (u n) (circleMap 0 1 (2 * Real.pi * t))) =
      Φ (γ (σ n (t : loopCircle)))
    rw [he, diskExtension_coe]
    exact congrArg Φ (congrArg (fun v : freeLoop M => v (t : loopCircle)) (htrace n))
  obtain ⟨τ, φ, hφ, hτ, ht0, ht1, ht2, hlim, _⟩ :=
    exists_subseq_tendsto_normalized_boundary_of_energy_bound Γ
      hΦγ f (fun n => C * K n) hf hbound
      σ hσ h0 h1 h2 hboundary
  refine ⟨τ, φ, hφ, hτ, ht0, ht1, ht2, hlim, ?_⟩
  have hlim' := ((continuous_postcomp γ).tendsto τ).comp hlim
  change Tendsto (fun n => γ.comp (σ (φ n))) atTop (𝓝 (γ.comp τ)) at hlim'
  simpa only [htrace] using hlim'

end DifferentialGeometry.Geometry

end
