import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterTransferLocal_S35
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.CompactExtension
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCovariantJets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorTransfer
import DifferentialGeometry.Geometry.Curvature.NegativeSectionalStability
import DifferentialGeometry.Geometry.Curvature.Bounds.MetricPerturbation

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

/-- (S41 bridge 1) A partial diffeomorphism with source `B.domain i t` extending the buffered map
(copy of the private `exists_partialDiffeomorph_of_injective_localDiffeomorph_on_opens`). -/
theorem bufferedMap_partialDiffeo_S41 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (i : Fin B.count) (t : ℝ) (ht : B.start ≤ t) (z : (B.model i).Carrier)
    (hz : z ∈ B.domain i t) :
    ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) (B.model i).Carrier
        (postStage F.observation t).Carrier ∞,
      Φ.source = (B.domain i t : Set (B.model i).Carrier) ∧
      ∀ x ∈ (B.domain i t : Set (B.model i).Carrier), Φ x = B.map i t ht x := by
  obtain ⟨hf, hinj⟩ := bufferedMap_localDiffeo_S35 B i t ht
  let p : B.domain i t := ⟨z, hz⟩
  let V := hf.image
  let e : Diffeomorph (𝓡 3) (𝓡 3) (B.domain i t) V ∞ :=
    DifferentialGeometry.Topology.diffeomorphRangeOfInjective hf hinj
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) (B.domain i t) ⟨p⟩
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) V ⟨e p⟩
  let Φ := (iU.symm.trans e.toPartialDiffeomorph).trans iV
  have hsrc : Φ.source = (B.domain i t : Set (B.model i).Carrier) := by
    ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (univ : Set (B.domain i t))) ∧
      e (iU.symm x) ∈ (univ : Set V)) ↔ x ∈ B.domain i t
    simp only [mem_univ, and_true, iU,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  refine ⟨Φ, hsrc, fun x hx => ?_⟩
  change (e (iU.symm x) : (postStage F.observation t).Carrier) = _
  rw [show iU.symm x = (⟨x, hx⟩ : B.domain i t) from
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply (𝓡 3) (B.domain i t)
      ⟨p⟩ hx]
  rfl

/-- (S41 bridge 2) A smooth metric `q` on the model realizing the pullback germ of `gb` at `z`;
sectional lower bounds of `q` at `z` and of `gb` at `φ z` agree. -/
theorem bufferedMap_pullbackGerm_S41 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (i : Fin B.count) (t : ℝ) (ht : B.start ≤ t)
    (gb : SmoothRiemannianMetric (𝓡 3) (postStage F.observation t).Carrier)
    (z : (B.model i).Carrier) (hz : z ∈ B.domain i t) :
    ∃ q : SmoothRiemannianMetric (𝓡 3) (B.model i).Carrier,
      (∀ᶠ w in 𝓝 z, q.inner w = localPullInner gb (B.map i t ht) w) ∧
      ∀ κ : ℝ, SectionalBoundedBelowAt q z κ ↔
        SectionalBoundedBelowAt gb (B.map i t ht z) κ := by
  obtain ⟨Φ, hsrc, hΦ⟩ := bufferedMap_partialDiffeo_S41 B i t ht z hz
  have hzΦ : z ∈ Φ.source := by rw [hsrc]; exact hz
  have hK : ({Φ z} : Set (postStage F.observation t).Carrier) ⊆ Φ.symm.source := by
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact Φ.map_source' hzΦ
  obtain ⟨q, U, hKU, _, hmetric, _⟩ :=
    Φ.symm.exists_metric_preserving_on_neighborhood_of_is_compact
      gb (B.model i).metric isCompact_singleton hK
  let O : TopologicalSpace.Opens (B.model i).Carrier :=
    ⟨Φ.source ∩ (Φ : (B.model i).Carrier → (postStage F.observation t).Carrier) ⁻¹' U,
      Φ.toOpenPartialHomeomorph.isOpen_inter_preimage U.isOpen⟩
  have hzO : z ∈ O := ⟨hzΦ, hKU (by simp)⟩
  have hiso : ∀ x ∈ (O : Set (B.model i).Carrier), ∀ a b : TangentSpace (𝓡 3) x,
      q.inner x a b = gb.inner (Φ x) (mfderiv (𝓡 3) (𝓡 3) Φ x a) (mfderiv (𝓡 3) (𝓡 3) Φ x b) := by
    intro x hx a b
    have hxsource : x ∈ Φ.source := hx.1
    have hxd : MDifferentiableAt (𝓡 3) (𝓡 3) Φ x :=
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds hxsource)).mdifferentiableAt (by simp)
    have hyd : MDifferentiableAt (𝓡 3) (𝓡 3) Φ.symm (Φ x) :=
      (Φ.contMDiffOn_invFun.contMDiffAt
        (Φ.open_target.mem_nhds (Φ.map_source' hxsource))).mdifferentiableAt (by simp)
    have heq : (Φ.symm : (postStage F.observation t).Carrier → (B.model i).Carrier) ∘ Φ
        =ᶠ[𝓝 x] id := by
      filter_upwards [Φ.open_source.mem_nhds hxsource] with y hy
      exact Φ.left_inv' hy
    have hinverse (v : TangentSpace (𝓡 3) x) :
        mfderiv (𝓡 3) (𝓡 3) Φ.symm (Φ x) (mfderiv (𝓡 3) (𝓡 3) Φ x v) = v := by
      have hc := mfderiv_comp_apply x hyd hxd v
      rw [heq.mfderiv_eq, mfderiv_id] at hc
      exact hc.symm
    have hg := hmetric (Φ x) hx.2 (mfderiv (𝓡 3) (𝓡 3) Φ x a) (mfderiv (𝓡 3) (𝓡 3) Φ x b)
    rw [hinverse a, hinverse b] at hg
    exact (congrArg (fun y : (B.model i).Carrier => q.inner y a b)
      (Φ.left_inv' hxsource)).symm.trans hg.symm
  refine ⟨q, ?_, fun κ => ?_⟩
  · filter_upwards [O.isOpen.mem_nhds hzO, (B.domain i t).isOpen.mem_nhds hz] with w hwO hwU
    have hev : (Φ : (B.model i).Carrier → _) =ᶠ[𝓝 w] B.map i t ht := by
      filter_upwards [(B.domain i t).isOpen.mem_nhds hwU] with y hy using hΦ y hy
    ext a b
    rw [hiso w hwO a b, localPullInner_apply, hev.mfderiv_eq, hΦ w hwU]
    rfl
  · have h := sectionalBoundedBelowAt_iff_of_isometricOnOpen_BDRY1 q gb Φ O.isOpen
      (fun _ hx => hx.1) hiso hzO (κ := κ)
    rwa [hΦ z hz] at h

/-- `localPullInner` of a scaled metric. -/
theorem localPullInner_scaleMetric_S41 {M N : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (c : ℝ) (hc : 0 < c) (G : SmoothRiemannianMetric (𝓡 3) N) (f : M → N) (x : M) :
    localPullInner (I := 𝓡 3) (J := 𝓡 3) (scaleMetric c hc G) f x =
      c • localPullInner (I := 𝓡 3) (J := 𝓡 3) G f x := by
  ext a b
  simp only [localPullInner_apply, scaleMetric_inner, smul_apply, smul_eq_mul]

end GC.LongTime.Ch12
