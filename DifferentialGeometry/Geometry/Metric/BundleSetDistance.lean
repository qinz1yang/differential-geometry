import DifferentialGeometry.Geometry.Connection.ParallelTransport.LocalTrivialization
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace Bundle

variable {M F : Type*} {V : M → Type*} [∀ x, PseudoMetricSpace (V x)]

def fiberInfDist (K : Set (TotalSpace F V)) (z : TotalSpace F V) : ℝ :=
  Metric.infDist z.2 {v : V z.proj | (⟨z.proj, v⟩ : TotalSpace F V) ∈ K}

end Bundle

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I 1 F V]
  [ContMDiffVectorBundle ∞ F V I]

theorem IsParallelSet.continuous_fiberInfDist
    {cov : CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : cov.IsParallelSet K) (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmetric : cov.IsMetricCompatible) : Continuous (fiberInfDist K) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  obtain ⟨U, hx₀, Q, _, _, hQi, hQK⟩ :=
    hmetric.exists_local_isometric_trivialization hcov z₀.proj
  let W := TopologicalSpace.Opens.comap
    ⟨(TotalSpace.proj : TotalSpace F V → M), FiberBundle.continuous_proj F V⟩ U
  have hlocal : Continuous (fun z : W => fiberInfDist K z.val) := by
    have h := (Metric.continuous_infDist_pt
      {v : V z₀.proj | (⟨z₀.proj, v⟩ : TotalSpace F V) ∈ K}).comp hQi.continuous
    apply h.congr
    intro z
    dsimp only [Function.comp_apply, fiberInfDist]
    rw [← hQK K hK ⟨z.val.proj, z.property⟩]
    have h := Metric.infDist_image (Q ⟨z.val.proj, z.property⟩).isometry
      (x := (Q ⟨z.val.proj, z.property⟩).symm z.val.2)
      (t := {v : V z₀.proj | (⟨z₀.proj, v⟩ : TotalSpace F V) ∈ K})
    simpa only [LinearIsometryEquiv.apply_symm_apply] using h.symm
  have hwithin : ContinuousWithinAt (fiberInfDist K) W z₀ :=
    (continuousWithinAt_iff_continuousAt_domRestrict (fiberInfDist K)
      (show z₀ ∈ W from hx₀)).mpr hlocal.continuousAt
  exact hwithin.continuousAt (W.isOpen.mem_nhds hx₀)

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

theorem IsParallelSet.isClosed_of_fiber
    {cov : CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : cov.IsParallelSet K) (hcov : ContMDiffCovariantDerivative cov ∞)
    (hclosed : ∀ x : M, IsClosed {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K}) :
    IsClosed K := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro z₀ hz₀
  obtain ⟨U, hx₀, Q, _, _, hQi, hQK⟩ :=
    cov.exists_local_parallel_trivialization hcov z₀.proj
  let W := TopologicalSpace.Opens.comap
    ⟨(TotalSpace.proj : TotalSpace F V → M), FiberBundle.continuous_proj F V⟩ U
  have hlocal : IsClosed ((Subtype.val : W → TotalSpace F V) ⁻¹' K) := by
    convert (hclosed z₀.proj).preimage hQi.continuous using 1
    ext z
    change z.val ∈ K ↔
      (⟨z₀.proj, (Q ⟨z.val.proj, z.property⟩).symm z.val.2⟩ : TotalSpace F V) ∈ K
    let x : U := ⟨z.val.proj, z.property⟩
    have hmap := hQK K hK x
    constructor
    · intro hz
      have hz' : z.val.2 ∈ Q x '' {v : V z₀.proj | (⟨z₀.proj, v⟩ : TotalSpace F V) ∈ K} := by
        rw [hmap]
        exact hz
      obtain ⟨v, hv, he⟩ := hz'
      have he' : v = (Q x).symm z.val.2 := by
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using congrArg (Q x).symm he
      change (⟨z₀.proj, (Q x).symm z.val.2⟩ : TotalSpace F V) ∈ K
      rw [← he']
      exact hv
    · intro hv
      have hz' : z.val.2 ∈ Q x '' {v : V z₀.proj | (⟨z₀.proj, v⟩ : TotalSpace F V) ∈ K} :=
        ⟨_, hv, (Q x).apply_symm_apply z.val.2⟩
      rw [hmap] at hz'
      exact hz'
  refine ⟨Subtype.val '' ((Subtype.val : W → TotalSpace F V) ⁻¹' Kᶜ), ?_, ?_, ?_⟩
  · rintro z ⟨w, hw, rfl⟩
    exact hw
  · exact W.isOpen.isOpenMap_subtype_val _ hlocal.isOpen_compl
  · exact ⟨⟨z₀, hx₀⟩, hz₀, rfl⟩

end CovariantDerivative
