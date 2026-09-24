import DifferentialGeometry.Geometry.HarmonicMap.BoundaryRegularity
import DifferentialGeometry.Geometry.HarmonicMap.ConformalSource
import DifferentialGeometry.Analysis.Complex.DiskBoundaryChart
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Instances.AddCircle.Real

noncomputable section
open Set Filter Metric Manifold
open scoped Topology ContDiff Manifold
namespace DifferentialGeometry.Geometry

private theorem exists_regular_addCircle_parametrization
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {T : ℝ} (hT : 0 < T) {γ : AddCircle T → M} (θ : ℝ)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun s : ℝ => γ (s : AddCircle T)))
    (hv : mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γ (s : AddCircle T)) θ (1 : ℝ) ≠ 0) :
    ∃ p : OpenPartialHomeomorph ℝ (AddCircle T), (0 : ℝ) ∈ p.source ∧ p 0 = (θ : AddCircle T) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (γ ∘ p) p.source ∧
      mfderiv 𝓘(ℝ, ℝ) I (γ ∘ p) 0 (1 : ℝ) ≠ 0 := by
  let : Fact (0 < T) := ⟨hT⟩
  let a := (Homeomorph.addLeft θ).toOpenPartialHomeomorph
  let p := a.trans (AddCircle.openPartialHomeomorphCoe T (θ - T / 2))
  have hp (s : ℝ) : p s = ((θ + s : ℝ) : AddCircle T) := rfl
  have hp0 : (0 : ℝ) ∈ p.source := by
    change 0 ∈ a.source ∧ a 0 ∈ Ioo (θ - T / 2) (θ - T / 2 + T)
    refine ⟨mem_univ _, ?_⟩
    change θ + 0 ∈ Ioo _ _
    constructor <;> linarith
  have hpc : ContMDiff 𝓘(ℝ, ℝ) I ∞ (γ ∘ p) :=
    hc.comp ((contDiff_const.add contDiff_id).contMDiff)
  refine ⟨p, hp0, by rw [hp]; simp, hpc.contMDiffOn, ?_⟩
  have ha : HasFDerivAt (fun s : ℝ => θ + s) (ContinuousLinearMap.id ℝ ℝ) 0 := by
    simpa using! (hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_add θ
  have hd := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I) 0
    (hc.mdifferentiable (by simp) (θ + 0))
    (mdifferentiableAt_iff_differentiableAt.mpr ha.differentiableAt)
  have he := congrArg (fun D : ℝ →L[ℝ] E => D 1) hd
  rw [mfderiv_eq_fderiv, ha.fderiv] at he
  change mfderiv 𝓘(ℝ, ℝ) I (γ ∘ p) 0 (1 : ℝ) = _ at he
  rw [he]
  change mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γ (s : AddCircle T)) (θ + 0) (1 : ℝ) ≠ 0
  convert! hv using 1
  simp
  congr 2
  simp

private theorem contMDiffWithinAt_of_comp_diskBoundaryChart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {U : ℂ → M} {p : ℂ} (hp : ‖p‖ = 1) {ρ : ℝ} (hρ : 0 < ρ)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ (U ∘ Complex.diskBoundaryChart p hp)
      {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im}) :
    ContMDiffWithinAt 𝓘(ℝ, ℂ) I ∞ U (Metric.closedBall (0 : ℂ) 1) p := by
  let ψ := Complex.diskBoundaryChart p hp
  have h0 : (0 : ℂ) ∈ ψ.source := by simp [ψ, Complex.diskBoundaryChart_source]
  have hψ0 : ψ 0 = p := Complex.diskBoundaryChart_zero p hp
  have hpT : p ∈ ψ.target := hψ0 ▸ ψ.toOpenPartialHomeomorph.map_source h0
  have hinv : ψ.symm p = 0 := by
    rw [← hψ0]
    exact ψ.toPartialEquiv.left_inv h0
  have hright {w : ℂ} (hw : w ∈ ψ.target) : ψ (ψ.symm w) = w :=
    ψ.toPartialEquiv.right_inv hw
  have hinorm : ‖ψ.symm p‖ < ρ := by rw [hinv, norm_zero]; exact hρ
  have hi : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ.symm p :=
    ψ.contMDiffOn_invFun.contMDiffAt (ψ.open_target.mem_nhds hpT)
  let A : Set ℂ := {w | w ∈ Metric.closedBall (0 : ℂ) 1 ∧ w ∈ ψ.target ∧ ‖ψ.symm w‖ < ρ}
  have hA : A ∈ 𝓝[Metric.closedBall (0 : ℂ) 1] p := by
    have hb : {w | ‖ψ.symm w‖ < ρ} ∈ 𝓝 p :=
      (hi.continuousAt.norm).preimage_mem_nhds (isOpen_Iio.mem_nhds hinorm)
    exact inter_mem self_mem_nhdsWithin (inter_mem
      (mem_nhdsWithin_of_mem_nhds (ψ.open_target.mem_nhds hpT)) (mem_nhdsWithin_of_mem_nhds hb))
  have hm : MapsTo ψ.symm A {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} := by
    intro w hw
    refine ⟨hw.2.2.le, ?_⟩
    apply (Complex.norm_diskBoundaryChart_le_one_iff p hp
      (ψ.toOpenPartialHomeomorph.map_target hw.2.1)).mp
    change ‖ψ (ψ.symm w)‖ ≤ 1
    rw [hright hw.2.1]
    exact mem_closedBall_zero_iff.mp hw.1
  have hreg : ContMDiffWithinAt 𝓘(ℝ, ℂ) I ∞ (U ∘ ψ) {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im}
      (ψ.symm p) := by
    rw [hinv]
    exact hU 0 (by simp [hρ.le])
  have heq : EqOn U ((U ∘ ψ) ∘ ψ.symm) A := by
    intro w hw
    dsimp only [Function.comp_apply]
    rw [hright hw.2.1]
  have hpA : p ∈ A := ⟨by simp [Metric.mem_closedBall, hp], hpT, hinorm⟩
  exact ((hreg.comp p hi.contMDiffWithinAt hm).congr heq (heq hpA)).mono_of_mem_nhdsWithin hA

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

theorem contMDiffOn_closedDisk_of_embedded_loop
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) {γ : AddCircle T → M}
    (hγ : Topology.IsEmbedding γ)
    (hγc : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun s : ℝ => γ (s : AddCircle T)))
    (hγv : ∀ θ : ℝ, mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γ (s : AddCircle T)) θ (1 : ℝ) ≠ 0)
    {U : ℂ → M} (hU : ContinuousOn U (Metric.closedBall (0 : ℂ) 1))
    (hUi : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ U (Metric.ball (0 : ℂ) 1))
    (htrace : ∀ z : ℂ, ‖z‖ = 1 → U z ∈ range γ)
    (ho : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) = 0)
    (he : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) =
        g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I))
    (hH : ∀ z ∈ Metric.ball (0 : ℂ) 1, planarTension g U z = 0) :
    ContMDiffOn 𝓘(ℝ, ℂ) I ∞ U (Metric.closedBall (0 : ℂ) 1) := by
  intro p hp
  have hpn : ‖p‖ ≤ 1 := mem_closedBall_zero_iff.mp hp
  rcases lt_or_eq_of_le hpn with hpi | hpb
  · exact (hUi.contMDiffAt (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hpi))).contMDiffWithinAt
  let ψ := Complex.diskBoundaryChart p hpb
  let V := U ∘ ψ
  let K : Set ℂ := {z | ‖z‖ ≤ 1 ∧ 0 ≤ z.im}
  let S : Set ℂ := {z | ‖z‖ < 1 ∧ 0 < z.im}
  have hKsrc : K ⊆ ψ.source := by
    intro z hz
    change z ≠ -Complex.I
    intro hzi
    have hi := hz.2
    rw [hzi] at hi
    norm_num at hi
  have hSK : S ⊆ K := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hmap : MapsTo ψ K (Metric.closedBall (0 : ℂ) 1) := fun z hz =>
    mem_closedBall_zero_iff.mpr ((Complex.norm_diskBoundaryChart_le_one_iff p hpb (hKsrc hz)).mpr hz.2)
  have hmapi : MapsTo ψ S (Metric.ball (0 : ℂ) 1) := fun z hz =>
    mem_ball_zero_iff.mpr ((Complex.norm_diskBoundaryChart_lt_one_iff p hpb (hKsrc (hSK hz))).mpr hz.2)
  have hV : ContinuousOn V K := hU.comp (ψ.contMDiffOn_toFun.continuousOn.mono hKsrc) hmap
  have hVi : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ V S :=
    hUi.comp (ψ.contMDiffOn_toFun.mono (hSK.trans hKsrc)) hmapi
  have hψanalytic (z : ℂ) (hz : z ∈ ψ.source) : AnalyticAt ℂ ψ z := by
    have hd : DifferentiableOn ℂ ψ ψ.source := fun w hw =>
      (Complex.hasDerivAt_diskBoundaryChart p hpb hw).differentiableAt.differentiableWithinAt
    exact hd.analyticAt (ψ.open_source.mem_nhds hz)
  have hU2 (z : ℂ) (hz : z ∈ S) : ContMDiffAt 𝓘(ℝ, ℂ) I 2 U (ψ z) :=
    (hUi.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contMDiffAt
      (Metric.isOpen_ball.mem_nhds (hmapi hz))
  have hconf (z : ℂ) (hz : z ∈ S) := conformal_mfderiv_comp_complex g
    ((hU2 z hz).mdifferentiableAt (by norm_num)) (hψanalytic z (hKsrc (hSK hz))).differentiableAt
    (ho _ (hmapi hz)) (he _ (hmapi hz))
  have hVH (z : ℂ) (hz : z ∈ S) : planarTension g V z = 0 := by
    rw [planarTension_comp_holomorphic g (hU2 z hz) (hψanalytic z (hKsrc (hSK hz))), hH _ (hmapi hz), smul_zero]
  obtain ⟨c, hc⟩ := htrace p hpb
  obtain ⟨θ, hθ⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨q, hq0, hqθ, hqc, hqv⟩ := exists_regular_addCircle_parametrization hT θ hγc (hγv θ)
  have hV0 : V 0 = γ (q 0) := by
    change U (Complex.diskBoundaryChart p hpb 0) = _
    rw [Complex.diskBoundaryChart_zero, hqθ, hθ, hc]
  have hVtrace (x : ℝ) (hx : |x| ≤ 1) : V x ∈ range γ := by
    have hxK : (x : ℂ) ∈ K := by simpa [K] using hx
    apply htrace
    exact (Complex.norm_diskBoundaryChart_eq_one_iff p hpb (hKsrc hxK)).mpr (by simp)
  obtain ⟨ρ, hρ, _, hreg⟩ := exists_contMDiffOn_halfDisk_of_embedded_curve g hγ q hq0 hqc hqv
    (by norm_num : (0 : ℝ) < 1) hV0 hV hVi hVtrace
    (fun z hz => (hconf z hz).1) (fun z hz => (hconf z hz).2) hVH
  exact contMDiffWithinAt_of_comp_diskBoundaryChart hpb hρ hreg

end DifferentialGeometry.Geometry
