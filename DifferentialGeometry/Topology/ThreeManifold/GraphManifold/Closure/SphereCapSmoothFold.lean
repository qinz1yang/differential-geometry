import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapAtlas
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapHalfFold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryOrientation
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
Actual smooth capping folds and full-rank differentials, including each spherical zero layer.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

section LocalParameter

variable {E F G H K L M P N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace L]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {Z : ModelWithCorners ℝ G L}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace P] [ChartedSpace K P]
  [TopologicalSpace N] [ChartedSpace L N]

private theorem sphereCapLocalParameter_smooth
    (e : PartialDiffeomorph I J M P ∞) (f : P → N)
    (hf : ContMDiffOn I Z ∞ (f ∘ e) e.source) {x : P} (hx : x ∈ e.target) :
    ContMDiffAt J Z ∞ f x := by
  have hp := e.toOpenPartialHomeomorph.map_target hx
  have hs := (hf.contMDiffAt (e.open_source.mem_nhds hp)).comp x
    (e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds hx))
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hx] with y hy
  exact congrArg f (e.toOpenPartialHomeomorph.right_inv hy).symm

private theorem sphereCapLocalParameter_bijective
    (e : PartialDiffeomorph I J M P ∞) (f : P → N)
    (hf : ContMDiffOn I Z ∞ (f ∘ e) e.source)
    (hb : ∀ p ∈ e.source, Bijective (mfderiv I Z (f ∘ e) p))
    {x : P} (hx : x ∈ e.target) : Bijective (mfderiv J Z f x) := by
  let p := e.symm x
  have hp : p ∈ e.source := e.toOpenPartialHomeomorph.map_target hx
  have he : e p = x := e.toOpenPartialHomeomorph.right_inv hx
  have hs := sphereCapLocalParameter_smooth e f hf hx
  have hf' : MDifferentiableAt J Z f (e p) := by
    rw [he]
    exact hs.mdifferentiableAt (by simp)
  have hc := mfderiv_comp p hf' (e.mdifferentiableAt (by simp) hp)
  have hd : Bijective ((mfderiv J Z f x).comp (mfderiv I J e p)) := by
    rw [← he, ← hc]
    exact hb p hp
  have heB : Bijective (mfderiv I J e p) :=
    (carrierSurgeryPatchTangentEquiv e hp).bijective
  constructor
  · intro v w hvw
    obtain ⟨a, ha⟩ := heB.surjective v
    obtain ⟨b, hb⟩ := heB.surjective w
    have hab : a = b := hd.injective (by
      change mfderiv J Z f x (mfderiv I J e p a) =
        mfderiv J Z f x (mfderiv I J e p b)
      rw [ha, hb]
      exact hvw)
    exact ha.symm.trans ((congrArg (mfderiv I J e p) hab).trans hb)
  · intro v
    obtain ⟨a, ha⟩ := hd.surjective v
    exact ⟨mfderiv I J e p a, ha⟩

end LocalParameter

section HalfFold

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
  {J : ModelWithCorners ℝ E H}

private theorem sphereCapHalfFold_smooth
    (e : PartialDiffeomorph sphereSignedCollarModel J (ClosureSphere.{u} × ℝ) N ∞)
    (he : e.source = sphereSignedCollarSource) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ContMDiffOn sphereHalfCollarModel J ∞ (e ∘ sphereCapHalfSignedCoordinate σ)
      sphereHalfCollarSource := by
  apply e.contMDiffOn.comp (sphereCapHalfSignedCoordinate_contMDiff σ).contMDiffOn
  intro p hp
  rw [he]
  exact sphereCapHalfSignedCoordinate_mem hσ hp

private theorem sphereCapHalfFold_bijective
    (e : PartialDiffeomorph sphereSignedCollarModel J (ClosureSphere.{u} × ℝ) N ∞)
    (he : e.source = sphereSignedCollarSource) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {p : ClosureSphere.{u} × EuclideanHalfSpace 1} (hp : p ∈ sphereHalfCollarSource) :
    Bijective (mfderiv sphereHalfCollarModel J (e ∘ sphereCapHalfSignedCoordinate σ) p) := by
  have hz : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have ht : sphereCapHalfSignedCoordinate σ p ∈ e.source :=
    he.symm ▸ sphereCapHalfSignedCoordinate_mem hσ hp
  rw [mfderiv_comp p (e.mdifferentiableAt (by simp) ht)
    ((sphereCapHalfSignedCoordinate_contMDiff σ).mdifferentiableAt (by simp))]
  exact (carrierSurgeryPatchTangentEquiv e ht).bijective.comp
    (sphereCapHalfSignedCoordinate_bijective hz p)

end HalfFold

namespace MixedBoundaryCertificate

local instance sphereCapFoldBallCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

local instance sphereCapFoldLiftedBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ULift.{u} sphereCapBallOpen) :=
  uliftChartedSpace (EuclideanHalfSpace 3) sphereCapBallOpen

local instance sphereCapFoldBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)
  [ChartedSpace (EuclideanHalfSpace 3) B.SphereCapQuotient]
  (hA : ∀ a : B.SphereCapPatchIndex,
    ContMDiffOn (B.sphereCapPatchModel a) (𝓡∂ 3) ∞
      (B.sphereCapPatch a) (B.sphereCapPatch a).source ∧
    ContMDiffOn (𝓡∂ 3) (B.sphereCapPatchModel a) ∞
      (B.sphereCapPatch a).symm (B.sphereCapPatch a).target)

include hA

private theorem sphereCapCoreHalf_eq (i : Fin B.sphereCount)
    {p : ClosureSphere.{u} × EuclideanHalfSpace 1} (hp : p ∈ sphereHalfCollarSource) :
    B.sphereCapCore (B.sphere i p) =
      B.sphereCapPatchDiffeomorph hA (.inr (.inr i)) (sphereCapHalfSignedCoordinate 1 p) := by
  change B.sphereCapCore (B.sphere i p) =
    B.sphereCapSignedSeam i (p.1, 1 * p.2.val 0)
  rw [one_mul, B.sphereCapSignedSeam_positive i p.1 (p.2.val 0) p.2.property hp]
  rw [halfPoint_eq_self p.2 p.2.property rfl]

private theorem sphereCapBallHalf_eq (i : Fin B.sphereCount)
    {p : ClosureSphere.{u} × EuclideanHalfSpace 1} (hp : p ∈ sphereHalfCollarSource) :
    B.sphereCapBall i (sphereCapBallCollar.{u} p) =
      B.sphereCapPatchDiffeomorph hA (.inr (.inr i)) (sphereCapHalfSignedCoordinate (-1) p) := by
  change B.sphereCapBall i (sphereCapBallCollar.{u} p) =
    B.sphereCapSignedSeam i (p.1, -1 * p.2.val 0)
  rw [neg_one_mul, B.sphereCapSignedSeam_negative i p.1 (-p.2.val 0)
    (neg_nonpos.mpr p.2.property) (by linarith [show p.2.val 0 < 1 from hp])]
  congr 1
  exact congrArg (fun y => sphereCapBallCollar.{u} (p.1, y))
    (halfPoint_eq_self p.2 (by simpa using p.2.property) (by simp)).symm

theorem sphereCapCoreHalf_smooth (i : Fin B.sphereCount) :
    ContMDiffOn sphereHalfCollarModel (𝓡∂ 3) ∞
      (B.sphereCapCore ∘ B.sphere i) sphereHalfCollarSource := by
  let e := B.sphereCapPatchDiffeomorph hA (.inr (.inr i))
  have he : e.source = sphereSignedCollarSource := B.sphereCapSignedSeam_source i
  exact (sphereCapHalfFold_smooth e he (Or.inl rfl)).congr
    (fun p hp => B.sphereCapCoreHalf_eq hA i hp)

theorem sphereCapBallHalf_smooth (i : Fin B.sphereCount) :
    ContMDiffOn sphereHalfCollarModel (𝓡∂ 3) ∞
      (B.sphereCapBall i ∘ sphereCapBallCollar.{u}) sphereHalfCollarSource := by
  let e := B.sphereCapPatchDiffeomorph hA (.inr (.inr i))
  have he : e.source = sphereSignedCollarSource := B.sphereCapSignedSeam_source i
  exact (sphereCapHalfFold_smooth e he (Or.inr rfl)).congr
    (fun p hp => B.sphereCapBallHalf_eq hA i hp)

theorem sphereCapCoreHalf_bijective (i : Fin B.sphereCount)
    {p : ClosureSphere.{u} × EuclideanHalfSpace 1} (hp : p ∈ sphereHalfCollarSource) :
    Bijective (mfderiv sphereHalfCollarModel (𝓡∂ 3) (B.sphereCapCore ∘ B.sphere i) p) := by
  let e := B.sphereCapPatchDiffeomorph hA (.inr (.inr i))
  have he : e.source = sphereSignedCollarSource := B.sphereCapSignedSeam_source i
  have hfun : (B.sphereCapCore ∘ B.sphere i) =ᶠ[𝓝 p]
      (e ∘ sphereCapHalfSignedCoordinate 1) := by
    have hopen : IsOpen (sphereHalfCollarSource :
        Set (ClosureSphere.{u} × EuclideanHalfSpace 1)) := by
      change IsOpen {q : ClosureSphere.{u} × EuclideanHalfSpace 1 | q.2.val 0 < 1}
      exact isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact B.sphereCapCoreHalf_eq hA i hq
  rw [hfun.mfderiv_eq]
  exact sphereCapHalfFold_bijective e he (Or.inl rfl) hp

theorem sphereCapBallHalf_bijective (i : Fin B.sphereCount)
    {p : ClosureSphere.{u} × EuclideanHalfSpace 1} (hp : p ∈ sphereHalfCollarSource) :
    Bijective (mfderiv sphereHalfCollarModel (𝓡∂ 3)
      (B.sphereCapBall i ∘ sphereCapBallCollar.{u}) p) := by
  let e := B.sphereCapPatchDiffeomorph hA (.inr (.inr i))
  have he : e.source = sphereSignedCollarSource := B.sphereCapSignedSeam_source i
  have hfun : (B.sphereCapBall i ∘ sphereCapBallCollar.{u}) =ᶠ[𝓝 p]
      (e ∘ sphereCapHalfSignedCoordinate (-1)) := by
    have hopen : IsOpen (sphereHalfCollarSource :
        Set (ClosureSphere.{u} × EuclideanHalfSpace 1)) := by
      change IsOpen {q : ClosureSphere.{u} × EuclideanHalfSpace 1 | q.2.val 0 < 1}
      exact isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact B.sphereCapBallHalf_eq hA i hq
  rw [hfun.mfderiv_eq]
  exact sphereCapHalfFold_bijective e he (Or.inr rfl) hp

private def sphereCapCoreLocalDiffeomorph (x : C.Carrier) (hx : x ∈ B.sphereCapCoreOpen) :
    PartialDiffeomorph C.model (𝓡∂ 3) C.Carrier B.SphereCapQuotient ∞ :=
  (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph C.model
    B.sphereCapCoreOpen ⟨⟨x, hx⟩⟩).symm.trans
      (B.sphereCapPatchDiffeomorph hA (.inl ⟨x, hx⟩))

private theorem sphereCapCoreLocalDiffeomorph_mem (x : C.Carrier)
    (hx : x ∈ B.sphereCapCoreOpen) :
    x ∈ (B.sphereCapCoreLocalDiffeomorph hA x hx).source := by
  change x ∈ (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph C.model
    B.sphereCapCoreOpen ⟨⟨x, hx⟩⟩).target ∧ _ ∈ univ
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
  exact ⟨hx, mem_univ _⟩

private theorem sphereCapCoreLocalDiffeomorph_eq (x : C.Carrier)
    (hx : x ∈ B.sphereCapCoreOpen) {y : C.Carrier} (hy : y ∈ B.sphereCapCoreOpen) :
    B.sphereCapCoreLocalDiffeomorph hA x hx y = B.sphereCapCore y := by
  let e := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph C.model
    B.sphereCapCoreOpen ⟨⟨x, hx⟩⟩
  have hyt : y ∈ e.target := by
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    exact hy
  change B.sphereCapCore (e.symm y).val = B.sphereCapCore y
  exact congrArg B.sphereCapCore (e.toOpenPartialHomeomorph.right_inv hyt)

private theorem sphereCapCoreLocalDiffeomorph_eventuallyEq (x : C.Carrier)
    (hx : x ∈ B.sphereCapCoreOpen) :
    B.sphereCapCore =ᶠ[𝓝 x] B.sphereCapCoreLocalDiffeomorph hA x hx := by
  filter_upwards [B.sphereCapCoreOpen.isOpen.mem_nhds hx] with y hy
  exact (B.sphereCapCoreLocalDiffeomorph_eq hA x hx hy).symm

theorem sphereCapCore_smooth : ContMDiff C.model (𝓡∂ 3) ∞ B.sphereCapCore := by
  intro x
  by_cases hx : x ∈ B.sphereCapCoreOpen
  · let e := B.sphereCapCoreLocalDiffeomorph hA x hx
    have hxe : x ∈ e.source := B.sphereCapCoreLocalDiffeomorph_mem hA x hx
    exact (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hxe)).congr_of_eventuallyEq
      (B.sphereCapCoreLocalDiffeomorph_eventuallyEq hA x hx)
  · have hxS : x ∈ B.sphereImage := by simpa [sphereCapCoreOpen] using hx
    obtain ⟨i, z, hz⟩ := mem_iUnion.mp hxS
    have hp : (z, halfZero) ∈ (B.sphere i).source := by
      rw [B.sphere_source]
      change (0 : ℝ) < 1
      exact zero_lt_one
    have ht : x ∈ (B.sphere i).target := hz ▸ (B.sphere i).map_source' hp
    apply sphereCapLocalParameter_smooth (B.sphere i) B.sphereCapCore ?_ ht
    rw [B.sphere_source]
    exact B.sphereCapCoreHalf_smooth hA i

theorem sphereCapCore_mfderiv_bijective (x : C.Carrier) :
    Bijective (mfderiv C.model (𝓡∂ 3) B.sphereCapCore x) := by
  by_cases hx : x ∈ B.sphereCapCoreOpen
  · let e := B.sphereCapCoreLocalDiffeomorph hA x hx
    have hxe : x ∈ e.source := B.sphereCapCoreLocalDiffeomorph_mem hA x hx
    rw [(B.sphereCapCoreLocalDiffeomorph_eventuallyEq hA x hx).mfderiv_eq]
    exact (carrierSurgeryPatchTangentEquiv e hxe).bijective
  · have hxS : x ∈ B.sphereImage := by simpa [sphereCapCoreOpen] using hx
    obtain ⟨i, z, hz⟩ := mem_iUnion.mp hxS
    have hp : (z, halfZero) ∈ (B.sphere i).source := by
      rw [B.sphere_source]
      change (0 : ℝ) < 1
      exact zero_lt_one
    have ht : x ∈ (B.sphere i).target := hz ▸ (B.sphere i).map_source' hp
    apply sphereCapLocalParameter_bijective (B.sphere i) B.sphereCapCore ?_ ?_ ht
    · rw [B.sphere_source]
      exact B.sphereCapCoreHalf_smooth hA i
    · intro p hp
      exact B.sphereCapCoreHalf_bijective hA i ((B.sphere_source i).subset hp)

private theorem sphereCapBallPatch_source (i : Fin B.sphereCount) :
    (B.sphereCapPatchDiffeomorph hA (.inr (.inl i))).source = univ := by
  simp only [sphereCapPatchDiffeomorph, sphereCapPatch, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ]

private def sphereCapBallLocalDiffeomorph (i : Fin B.sphereCount) (x : ClosedCell 3)
    (hx : x ∈ sphereCapBallOpen) :
    PartialDiffeomorph (𝓡∂ 3) (𝓡∂ 3) (ClosedCell 3) B.SphereCapQuotient ∞ :=
  (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡∂ 3)
    sphereCapBallOpen ⟨⟨x, hx⟩⟩).symm.trans
      ((uliftDiffeomorph (𝓡∂ 3) sphereCapBallOpen).toPartialDiffeomorph.trans
        (B.sphereCapPatchDiffeomorph hA (.inr (.inl i))))

private theorem sphereCapBallLocalDiffeomorph_mem (i : Fin B.sphereCount) (x : ClosedCell 3)
    (hx : x ∈ sphereCapBallOpen) :
    x ∈ (B.sphereCapBallLocalDiffeomorph hA i x hx).source := by
  change x ∈ (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡∂ 3)
    sphereCapBallOpen ⟨⟨x, hx⟩⟩).target ∧ _ ∈ _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
  refine ⟨hx, ?_⟩
  change _ ∈ univ ∧ _ ∈ (B.sphereCapPatchDiffeomorph hA (.inr (.inl i))).source
  rw [B.sphereCapBallPatch_source hA i]
  exact ⟨mem_univ _, mem_univ _⟩

private theorem sphereCapBallLocalDiffeomorph_eq (i : Fin B.sphereCount) (x : ClosedCell 3)
    (hx : x ∈ sphereCapBallOpen) {y : ClosedCell 3} (hy : y ∈ sphereCapBallOpen) :
    B.sphereCapBallLocalDiffeomorph hA i x hx y = B.sphereCapBall i y := by
  let e := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡∂ 3)
    sphereCapBallOpen ⟨⟨x, hx⟩⟩
  have hyt : y ∈ e.target := by
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    exact hy
  change B.sphereCapBall i (e.symm y).val = B.sphereCapBall i y
  exact congrArg (B.sphereCapBall i) (e.toOpenPartialHomeomorph.right_inv hyt)

private theorem sphereCapBallLocalDiffeomorph_eventuallyEq (i : Fin B.sphereCount)
    (x : ClosedCell 3) (hx : x ∈ sphereCapBallOpen) :
    B.sphereCapBall i =ᶠ[𝓝 x] B.sphereCapBallLocalDiffeomorph hA i x hx := by
  filter_upwards [sphereCapBallOpen.isOpen.mem_nhds hx] with y hy
  exact (B.sphereCapBallLocalDiffeomorph_eq hA i x hx hy).symm

omit hA in
private theorem sphereCapBallCollar_target_of_not_open (x : ClosedCell 3)
    (hx : x ∉ sphereCapBallOpen) : x ∈ sphereCapBallCollar.{u}.target := by
  have hn : ‖x.val‖ = 1 := by
    have hb : ‖x.val‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using x.property
    exact le_antisymm hb (le_of_not_gt hx)
  let z : ClosureSphere.{u} := ULift.up ⟨x.val, by
    simpa [Metric.mem_sphere, dist_zero_right] using hn⟩
  have he : closureSphereToBall z = x := rfl
  have hs : (z, halfZero) ∈ sphereCapBallCollar.source := by
    rw [sphereCapBallCollar_source]
    change (0 : ℝ) < 1
    exact zero_lt_one
  have ht := sphereCapBallCollar.toOpenPartialHomeomorph.map_source hs
  change sphereCapBallCollar.{u} (z, halfZero) ∈ sphereCapBallCollar.target at ht
  rwa [sphereCapBallCollar_zero z, he] at ht

theorem sphereCapBall_smooth (i : Fin B.sphereCount) :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (B.sphereCapBall i) := by
  intro x
  by_cases hx : x ∈ sphereCapBallOpen
  · let e := B.sphereCapBallLocalDiffeomorph hA i x hx
    have hxe : x ∈ e.source := B.sphereCapBallLocalDiffeomorph_mem hA i x hx
    exact (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hxe)).congr_of_eventuallyEq
      (B.sphereCapBallLocalDiffeomorph_eventuallyEq hA i x hx)
  · have ht := sphereCapBallCollar_target_of_not_open.{u} x hx
    apply sphereCapLocalParameter_smooth sphereCapBallCollar.{u} (B.sphereCapBall i) ?_ ht
    rw [sphereCapBallCollar_source]
    exact B.sphereCapBallHalf_smooth hA i

theorem sphereCapBall_mfderiv_bijective (i : Fin B.sphereCount) (x : ClosedCell 3) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapBall i) x) := by
  by_cases hx : x ∈ sphereCapBallOpen
  · let e := B.sphereCapBallLocalDiffeomorph hA i x hx
    have hxe : x ∈ e.source := B.sphereCapBallLocalDiffeomorph_mem hA i x hx
    rw [(B.sphereCapBallLocalDiffeomorph_eventuallyEq hA i x hx).mfderiv_eq]
    exact (carrierSurgeryPatchTangentEquiv e hxe).bijective
  · have ht := sphereCapBallCollar_target_of_not_open.{u} x hx
    apply sphereCapLocalParameter_bijective sphereCapBallCollar.{u} (B.sphereCapBall i) ?_ ?_ ht
    · rw [sphereCapBallCollar_source]
      exact B.sphereCapBallHalf_smooth hA i
    · intro p hp
      exact B.sphereCapBallHalf_bijective hA i (sphereCapBallCollar_source.subset hp)

end MixedBoundaryCertificate

end GC.GraphManifold
