import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorArbitraryKRegularity
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedData
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevEmbedding
import DifferentialGeometry.Geometry.LocalChartConsistency

/-!
# A compactly-supported smooth representative of the eigenvector chart component

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, an eigenbasis index `i`, a chart center `α : M`, and a
component multi-index `P₀`, the eigenvector chart component
`eigenvectorChartComponentFun g r s h_atlas i α P₀ : EuclN → ℝ` — the chart
`P₀`-component of a resolvent eigenvector of the connection Laplacian `Δ_∇` —
has been shown to lie in the iterated Euclidean Sobolev space `MemWkp k 2` on
the whole chart target, for *every* order `k`
(`eigenvector_chartComponent_memWkp_arbitrary`). It also vanishes almost
everywhere off the compact partition-of-unity kernel `chartPouKernel α`.

This module ships a **compactly-supported smooth representative** of the chart
component:

    `eigenvectorChartComponent_exists_smooth_representative` :
      there is `u_smooth : EuclN → ℝ`, smooth on the chart target, compactly
      supported with `tsupport u_smooth ⊆ chartTargetEuclid α`, and almost
      everywhere equal — for the Lebesgue measure restricted to the chart
      target — to `eigenvectorChartComponentFun g r s h_atlas i α P₀`.

## Route

* The iterated-Sobolev embedding `contDiffOn_of_forall_memWkp_two` turns the
  family `∀ k, MemWkp k 2 …` into a `C^∞` representative `u_smooth₀` on the
  open chart target, almost everywhere equal to the chart component.
* A smooth cutoff `η` — equal to `1` on a neighbourhood of the compact kernel
  `chartPouKernel α` and compactly supported strictly inside the chart target
  (`exists_smooth_cutoff_with_neighborhood`) — localises `u_smooth₀` to a
  compactly-supported smooth function `η · u_smooth₀`.
* The product `η · u_smooth₀` still agrees almost everywhere with the chart
  component: on the kernel `η = 1`, so the product equals `u_smooth₀`, which is
  a.e. the chart component; off the kernel the chart component is a.e. zero, and
  `u_smooth₀` — being a.e. equal to it — is a.e. zero too, hence so is the
  product.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.EuclideanIteratedEmbedding

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## The compactly-supported smooth representative

The chart component is smoothened by the iterated-Sobolev embedding and then
localised by a smooth cutoff adapted to the compact partition-of-unity kernel.
-/

/-- **A compactly-supported smooth representative of the eigenvector chart
component.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, an eigenbasis index `i`, a chart center `α : M`, and a
component multi-index `P₀`, the eigenvector chart component
`eigenvectorChartComponentFun g r s h_atlas i α P₀` has a representative
`u_smooth : EuclN → ℝ` that is `C^∞` on the Euclidean chart target, has compact
support contained in the chart target, and agrees with the chart component
almost everywhere for the Lebesgue measure restricted to the chart target.

The chart component lies in every iterated Euclidean Sobolev space on the chart
target (`eigenvector_chartComponent_memWkp_arbitrary`); the iterated-Sobolev
embedding `contDiffOn_of_forall_memWkp_two` produces a `C^∞` representative on
the open chart target. The chart component also vanishes almost everywhere off
the compact partition-of-unity kernel `chartPouKernel α`; a smooth cutoff equal
to `1` on a neighbourhood of that kernel and compactly supported strictly inside
the chart target localises the representative to compact support without
disturbing the almost-everywhere identity. -/
theorem eigenvectorChartComponent_exists_smooth_representative
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ u_smooth : EuclN → ℝ,
      ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth
        (chartTargetEuclid (I := I) (M := M) α) ∧
      HasCompactSupport u_smooth ∧
      tsupport u_smooth ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      u_smooth =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  -- Abbreviations for the chart target, the chart component and the kernel.
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set u : EuclN → ℝ :=
    eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀
    with hu_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hΩ_open : IsOpen Ω :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_subset_Ω : K ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- `u ∈ MemWkp k 2` on the chart target for every order `k`.
  have hu_memWkp : ∀ k : ℕ,
      MemWkp (d := Module.finrank ℝ E) k 2 u Ω := fun k =>
    eigenvector_chartComponent_memWkp_arbitrary g r s h_atlas i k α P₀
  -- The iterated-Sobolev embedding: a `C^∞` representative `u₀` on the
  -- open chart target, almost everywhere equal to `u`.
  obtain ⟨u₀, hu₀_cdiff, hu_ae_u₀⟩ :=
    contDiffOn_of_forall_memWkp_two (d := Module.finrank ℝ E) hΩ_open hu_memWkp
  -- A smooth cutoff `η`, equal to `1` on a neighbourhood of the compact kernel
  -- `K` and compactly supported strictly inside the chart target `Ω`.
  obtain ⟨δ, η, hδ_pos, _hδ_subset, hη_cdiff, hη_cpt, _hη_range,
      hη_one_cthick, hη_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hK_compact hΩ_open hK_subset_Ω
  -- The cutoff is `1` on the kernel itself.
  have hη_one_K : ∀ y ∈ K, η y = 1 := fun y hy =>
    hη_one_cthick y (Metric.self_subset_cthickening _ hy)
  -- The localised representative.
  set u_smooth : EuclN → ℝ := fun y => η y * u₀ y with hu_smooth_def
  -- `u_smooth` is `C^∞` on the chart target: a product of two `C^∞` functions.
  have hu_smooth_cdiff : ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth Ω :=
    (hη_cdiff.contDiffOn).mul hu₀_cdiff
  -- `u_smooth` has compact support: its support sits inside that of `η`.
  have hu_smooth_cpt : HasCompactSupport u_smooth :=
    HasCompactSupport.mul_right hη_cpt
  -- `tsupport u_smooth ⊆ tsupport η ⊆ Ω`.
  have hu_smooth_tsupp : tsupport u_smooth ⊆ Ω :=
    (tsupport_mul_subset_left).trans hη_tsupp
  refine ⟨u_smooth, hu_smooth_cdiff, hu_smooth_cpt, hu_smooth_tsupp, ?_⟩
  -- The almost-everywhere identity `u_smooth =ᵐ u`, equivalently `u =ᵐ u_smooth`.
  -- The chart component is a.e. zero off the kernel.
  have hu_ae_zero :
      u =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)]
        (fun _ : EuclN => (0 : ℝ)) :=
    eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
      g r s h_atlas i α P₀
  -- `u₀ =ᵐ u` on `Ω` (the embedding), hence on the open subset `Ω \ K`.
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hΩK_open : IsOpen (Ω \ K) := hΩ_open.sdiff hK_closed
  have hΩK_subset : Ω \ K ⊆ Ω := Set.diff_subset
  have hu₀_ae_u_ΩK : u₀ =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)] u :=
    Filter.EventuallyEq.symm
      (ae_restrict_of_ae_restrict_of_subset hΩK_subset hu_ae_u₀)
  -- Off the kernel: `u₀ =ᵐ u =ᵐ 0`, hence `u_smooth = η · u₀ =ᵐ 0`.
  have hu_smooth_ae_zero_ΩK :
      u_smooth =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)]
        (fun _ : EuclN => (0 : ℝ)) := by
    have hu₀_ae_zero_ΩK :
        u₀ =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)]
          (fun _ : EuclN => (0 : ℝ)) := hu₀_ae_u_ΩK.trans hu_ae_zero
    filter_upwards [hu₀_ae_zero_ΩK] with y hy
    simp [hu_smooth_def, hy]
  -- `u =ᵐ u_smooth` on `Ω \ K`: both are a.e. zero there.
  have hu_ae_u_smooth_ΩK :
      u =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)] u_smooth :=
    hu_ae_zero.trans hu_smooth_ae_zero_ΩK.symm
  -- On the kernel: `η = 1`, so `u_smooth = u₀ =ᵐ u`.
  have hK_meas : MeasurableSet K := hK_closed.measurableSet
  have hu₀_ae_u_K : u₀ =ᵐ[(volume : Measure EuclN).restrict K] u :=
    Filter.EventuallyEq.symm
      (ae_restrict_of_ae_restrict_of_subset hK_subset_Ω hu_ae_u₀)
  have hu_smooth_ae_u₀_K :
      u_smooth =ᵐ[(volume : Measure EuclN).restrict K] u₀ := by
    refine (ae_restrict_iff' hK_meas).mpr ?_
    exact Filter.Eventually.of_forall fun y hy => by
      simp [hu_smooth_def, hη_one_K y hy]
  have hu_ae_u_smooth_K :
      u =ᵐ[(volume : Measure EuclN).restrict K] u_smooth :=
    (hu₀_ae_u_K.symm).trans hu_smooth_ae_u₀_K.symm
  -- Patch the two a.e. identities over `Ω = K ∪ (Ω \ K)`.
  have hΩ_eq : Ω = K ∪ (Ω \ K) := by
    rw [Set.union_diff_cancel hK_subset_Ω]
  have hu_ae_u_smooth :
      u =ᵐ[(volume : Measure EuclN).restrict Ω] u_smooth := by
    rw [hΩ_eq]
    exact (MeasureTheory.ae_restrict_union_iff K (Ω \ K)
      (fun x => u x = u_smooth x)).mpr ⟨hu_ae_u_smooth_K, hu_ae_u_smooth_ΩK⟩
  exact hu_ae_u_smooth.symm

/-- Chart-locality-free twin of
`eigenvectorChartComponent_exists_smooth_representative`. -/
theorem eigenvectorChartComponent_exists_smooth_representative_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ u_smooth : EuclN → ℝ,
      ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth
        (chartTargetEuclid (I := I) (M := M) α) ∧
      HasCompactSupport u_smooth ∧
      tsupport u_smooth ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      u_smooth =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
          g r s i α P₀ := by
  classical
  -- Abbreviations for the chart target, the chart component and the kernel.
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set u : EuclN → ℝ :=
    eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀
    with hu_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hΩ_open : IsOpen Ω :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_subset_Ω : K ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- `u ∈ MemWkp k 2` on the chart target for every order `k`.
  have hu_memWkp : ∀ k : ℕ,
      MemWkp (d := Module.finrank ℝ E) k 2 u Ω := fun k =>
    eigenvector_chartComponent_memWkp_arbitrary_unconditional g r s i k α P₀
  -- The iterated-Sobolev embedding: a `C^∞` representative `u₀` on the
  -- open chart target, almost everywhere equal to `u`.
  obtain ⟨u₀, hu₀_cdiff, hu_ae_u₀⟩ :=
    contDiffOn_of_forall_memWkp_two (d := Module.finrank ℝ E) hΩ_open hu_memWkp
  -- A smooth cutoff `η`, equal to `1` on a neighbourhood of the compact kernel
  -- `K` and compactly supported strictly inside the chart target `Ω`.
  obtain ⟨δ, η, hδ_pos, _hδ_subset, hη_cdiff, hη_cpt, _hη_range,
      hη_one_cthick, hη_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hK_compact hΩ_open hK_subset_Ω
  -- The cutoff is `1` on the kernel itself.
  have hη_one_K : ∀ y ∈ K, η y = 1 := fun y hy =>
    hη_one_cthick y (Metric.self_subset_cthickening _ hy)
  -- The localised representative.
  set u_smooth : EuclN → ℝ := fun y => η y * u₀ y with hu_smooth_def
  -- `u_smooth` is `C^∞` on the chart target: a product of two `C^∞` functions.
  have hu_smooth_cdiff : ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth Ω :=
    (hη_cdiff.contDiffOn).mul hu₀_cdiff
  -- `u_smooth` has compact support: its support sits inside that of `η`.
  have hu_smooth_cpt : HasCompactSupport u_smooth :=
    HasCompactSupport.mul_right hη_cpt
  -- `tsupport u_smooth ⊆ tsupport η ⊆ Ω`.
  have hu_smooth_tsupp : tsupport u_smooth ⊆ Ω :=
    (tsupport_mul_subset_left).trans hη_tsupp
  refine ⟨u_smooth, hu_smooth_cdiff, hu_smooth_cpt, hu_smooth_tsupp, ?_⟩
  -- The almost-everywhere identity `u_smooth =ᵐ u`, equivalently `u =ᵐ u_smooth`.
  -- The chart component is a.e. zero off the kernel.
  have hu_ae_zero :
      u =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)]
        (fun _ : EuclN => (0 : ℝ)) :=
    eigenvectorChartComponentFun_ofCompact_ae_zero_off_chartPouKernel
      g r s i α P₀
  -- `u₀ =ᵐ u` on `Ω` (the embedding), hence on the open subset `Ω \ K`.
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hΩK_open : IsOpen (Ω \ K) := hΩ_open.sdiff hK_closed
  have hΩK_subset : Ω \ K ⊆ Ω := Set.diff_subset
  have hu₀_ae_u_ΩK : u₀ =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)] u :=
    Filter.EventuallyEq.symm
      (ae_restrict_of_ae_restrict_of_subset hΩK_subset hu_ae_u₀)
  -- Off the kernel: `u₀ =ᵐ u =ᵐ 0`, hence `u_smooth = η · u₀ =ᵐ 0`.
  have hu_smooth_ae_zero_ΩK :
      u_smooth =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)]
        (fun _ : EuclN => (0 : ℝ)) := by
    have hu₀_ae_zero_ΩK :
        u₀ =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)]
          (fun _ : EuclN => (0 : ℝ)) := hu₀_ae_u_ΩK.trans hu_ae_zero
    filter_upwards [hu₀_ae_zero_ΩK] with y hy
    simp [hu_smooth_def, hy]
  -- `u =ᵐ u_smooth` on `Ω \ K`: both are a.e. zero there.
  have hu_ae_u_smooth_ΩK :
      u =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)] u_smooth :=
    hu_ae_zero.trans hu_smooth_ae_zero_ΩK.symm
  -- On the kernel: `η = 1`, so `u_smooth = u₀ =ᵐ u`.
  have hK_meas : MeasurableSet K := hK_closed.measurableSet
  have hu₀_ae_u_K : u₀ =ᵐ[(volume : Measure EuclN).restrict K] u :=
    Filter.EventuallyEq.symm
      (ae_restrict_of_ae_restrict_of_subset hK_subset_Ω hu_ae_u₀)
  have hu_smooth_ae_u₀_K :
      u_smooth =ᵐ[(volume : Measure EuclN).restrict K] u₀ := by
    refine (ae_restrict_iff' hK_meas).mpr ?_
    exact Filter.Eventually.of_forall fun y hy => by
      simp [hu_smooth_def, hη_one_K y hy]
  have hu_ae_u_smooth_K :
      u =ᵐ[(volume : Measure EuclN).restrict K] u_smooth :=
    (hu₀_ae_u_K.symm).trans hu_smooth_ae_u₀_K.symm
  -- Patch the two a.e. identities over `Ω = K ∪ (Ω \ K)`.
  have hΩ_eq : Ω = K ∪ (Ω \ K) := by
    rw [Set.union_diff_cancel hK_subset_Ω]
  have hu_ae_u_smooth :
      u =ᵐ[(volume : Measure EuclN).restrict Ω] u_smooth := by
    rw [hΩ_eq]
    exact (MeasureTheory.ae_restrict_union_iff K (Ω \ K)
      (fun x => u x = u_smooth x)).mpr ⟨hu_ae_u_smooth_K, hu_ae_u_smooth_ΩK⟩
  exact hu_ae_u_smooth.symm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
