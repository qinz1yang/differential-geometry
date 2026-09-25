import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.DiffeomorphRows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Geometry.Curvature CheegerGromovCompactness

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle
private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

theorem exists_pointed_convergence_of_cylindrical_local_pullbacks
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel} (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (e : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M)
    {v : ℝ} (hv : v ≤ 0) (f : ℕ → ℕ)
    (eps : ℕ → ℝ) (heps : ∀ i, 0 < eps i) (hepslim : Tendsto eps atTop (𝓝 0))
    (hp : ∀ i, e.symm P.basepoint ∈ neckBuffer (eps i))
    (psi : ∀ i, neckBuffer (eps i) → (X.obj (f i)).M)
    (hpsi : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (psi i))
    (hinj : ∀ i, Function.Injective (psi i))
    (hbase : ∀ i, psi i ⟨e.symm P.basepoint, hp i⟩ = (X.obj (f i)).basepoint)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (Gm : ∀ n, ℕ → SmoothRiemannianMetric NeckCylinderModel (neckBuffer (δ n)))
    (hconv : ∀ n, MetricCInfConvergenceOnCompacts (Gm n)
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n))))
    (hmetric : ∀ n, ∀ᶠ i in atTop, ∃ hni : eps i ≤ δ n,
      ∀ (z : neckBuffer (δ n)) (a b : TangentSpace NeckCylinderModel z),
        (Gm n i).inner z a b = (X.obj (f i)).metric.inner
          (psi i (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le (heps i) hni) z))
          (mfderiv NeckCylinderModel ThreeModel
            (fun w : neckBuffer (δ n) => psi i (TopologicalSpace.Opens.inclusion
              (neckBuffer_le_of_le (heps i) hni) w)) z a)
          (mfderiv NeckCylinderModel ThreeModel
            (fun w : neckBuffer (δ n) => psi i (TopologicalSpace.Opens.inclusion
              (neckBuffer_le_of_le (heps i) hni) w)) z b)) :
    let Pτ : PointedRiemannianManifold ThreeModel := { P with
      metric := Diffeomorph.pullbackMetricCross (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) e.symm}
    RiemannianMetricComplete Pτ.metric ∧
      (∀ y : Pτ.M, metricScalarAt Pτ.metric y = (1 - v)⁻¹) ∧
      (∀ y : Pτ.M, metricScalarAt Pτ.metric y ≤ 1) ∧
      Diffeomorph.pullbackMetricCross Pτ.metric e =
        (scaleMetric (2 * (1 - v)) (mul_pos (by norm_num) (by linarith))
          (Geometry.roundMetric (E := ThreeSpace) (n := 2))).prod (euclideanMetric (E := ℝ)) ∧
      ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ maps : PointedRiemannianConvergenceMaps X Pτ (f ∘ k),
        (∀ i (z : neckBuffer (eps (k i))), maps.map i (e z) = psi (k i) z) ∧
        (∀ i, maps.source i ⊆ e.symm ⁻¹' neckBuffer (eps (k i))) ∧
        (∀ i, IsCompact (closure (maps.source i))) ∧ (∀ i, IsConnected (maps.source i)) ∧
        ∃ C : MetricConvergenceData maps,
          ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData maps i := by
  intro Pτ
  let _ : PreconnectedSpace (Sphere 2) := Subtype.preconnectedSpace
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  let _ : PreconnectedSpace P.M := e.surjective.denseRange.preconnectedSpace e.continuous
  have hv1 : v < 1 := hv.trans_lt zero_lt_one
  have hc : RiemannianMetricComplete Pτ.metric :=
    RiemannianMetricComplete.pullbackCross _ e.symm
      (PDE.RicciFlow.shrinkingCylinderMetric_complete (E := ThreeSpace) v)
  have hscalar (y : Pτ.M) : metricScalarAt Pτ.metric y = (1 - v)⁻¹ := by
    change metricScalarAt (Diffeomorph.pullbackMetricCross _ e.symm) y = _
    rw [metricScalar_cross,
      PDE.RicciFlow.shrinkingCylinderMetric_scalar hv1]
  have hbound (y : Pτ.M) : metricScalarAt Pτ.metric y ≤ 1 := by
    rw [hscalar]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hproduct : Diffeomorph.pullbackMetricCross Pτ.metric e =
      (scaleMetric (2 * (1 - v)) (mul_pos (by norm_num) (by linarith))
        (Geometry.roundMetric (E := ThreeSpace) (n := 2))).prod (euclideanMetric (E := ℝ)) := by
    change Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross _ e.symm) e = _
    rw [show Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross
        (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) e.symm) e =
        PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v from
      Diffeomorph.pullbackMetricCross_symm_eq_iff.mpr rfl]
    exact PDE.RicciFlow.shrinkingCylinderMetric_eq_prod hv1
  refine ⟨hc, hscalar, hbound, hproduct, ?_⟩
  have hexhaust_general {η : ℕ → ℝ} (hη : ∀ i, 0 < η i) (hηlim : Tendsto η atTop (𝓝 0))
      (K : Set NeckCylinder) (hK : IsCompact K) : ∀ᶠ i in atTop, K ⊆ neckBuffer (η i) := by
    obtain ⟨A, hA⟩ := hK.bddAbove_image (continuous_abs.comp continuous_snd).continuousOn
    have hpA : 0 < (|A| + 1)⁻¹ := by positivity
    filter_upwards [hηlim.eventually_lt_const hpA] with i hi
    have hwidth : |A| + 1 < (η i)⁻¹ := by
      simpa only [inv_inv] using (inv_lt_inv₀ hpA (hη i)).mpr hi
    intro z hz
    have hzA : |z.2| ≤ A := hA (mem_image_of_mem (fun z : NeckCylinder => |z.2|) hz)
    change -(η i)⁻¹ - 1 < z.2 ∧ z.2 < (η i)⁻¹ + 1
    constructor <;> linarith [le_abs_self A, le_abs_self z.2, neg_le_abs z.2]
  have hexhaust := hexhaust_general heps hepslim
  apply exists_pointed_convergence_of_local_pullbacks_along_diffeomorph
    (P := Pτ) e.symm (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) rfl f
      (fun i => neckBuffer (eps i)) hp psi hpsi hinj hbase hexhaust
  intro K hK
  obtain ⟨n, hn⟩ := (hexhaust_general hδ hδlim K hK).exists
  let _ : SigmaCompactSpace (neckBuffer (δ n)) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer (δ n)).isOpen)
  refine ⟨neckBuffer (δ n), hn, Gm n,
    (hconv n).change_reference _, ?_⟩
  exact (hmetric n).mono fun i hi => by
    obtain ⟨hni, hh⟩ := hi
    exact ⟨neckBuffer_le_of_le (heps i) hni, hh⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
