import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

section
open Filter Module Set
open scoped Topology

universe u v w

namespace Poincare.Topology

open Classical in
private theorem basis_orientation_eventually_eq
    {X : Type u} [TopologicalSpace X] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : X → Basis ι ℝ E) (x : X)
    (hb : ∀ i, ContinuousAt (fun y => b y i) x) :
    ∀ᶠ y in 𝓝 x, (b y).orientation = (b x).orientation := by
  classical
  let : FiniteDimensional ℝ E := (b x).finiteDimensional_of_finite
  have hmatrix : ContinuousAt (fun y => (b x).toMatrix (b y)) x := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    change ContinuousAt (fun y => (b x).coord i (b y j)) x
    exact ((b x).coord i).continuous_of_finiteDimensional.continuousAt.comp (hb j)
  have hdet : ContinuousAt (fun y => (b x).det (b y)) x := by
    simpa only [Basis.det_apply, Function.comp_def, id_eq] using
      continuous_id.matrix_det.continuousAt.comp hmatrix
  have hpos : 0 < (b x).det (b x) := by rw [Basis.det_self]; exact zero_lt_one
  filter_upwards [hdet.eventually (Ioi_mem_nhds hpos)] with y hy
  exact ((b x).orientation_eq_iff_det_pos (b y)).mpr hy |>.symm

end Poincare.Topology

end

section
open Bundle Filter Module Set
open scoped Manifold Topology

universe u v w

namespace Poincare.Topology

open Classical in
private theorem local_frame_tangent_orientation_eq_on_nhds
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (s : ι → (x : M) → TangentSpace 𝓘(ℝ, E) x) (U : Set M)
    (hs : IsLocalFrameOn 𝓘(ℝ, E) E 0 s U) (hU : IsOpen U) (p : M) (hp : p ∈ U) :
    ∃ (V : Set M) (hVU : V ⊆ U) (hVs : V ⊆ (chartAt E p).source),
      IsOpen V ∧ p ∈ V ∧ ∀ (x : M) (hx : x ∈ V),
        Orientation.map _
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              hVs hx)).toLinearEquiv (hs.toBasisAt (hVU hx)).orientation =
          Orientation.map _
            ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ p
              (by simpa only [TangentBundle.trivializationAt_baseSet] using
                mem_chart_source E p)).toLinearEquiv (hs.toBasisAt hp).orientation := by
  let T := U ∩ (chartAt E p).source
  have hT : IsOpen T := hU.inter (chartAt E p).open_source
  have hpT : p ∈ T := ⟨hp, mem_chart_source E p⟩
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  let A (x : M) (hx : x ∈ T) : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E :=
    e.continuousLinearEquivAt ℝ x
      (by simpa only [e, TangentBundle.trivializationAt_baseSet] using hx.2)
  let b₀ := (hs.toBasisAt hp).map (A p hpT).toLinearEquiv
  let b (x : M) : Basis ι ℝ E :=
    if hx : x ∈ T then (hs.toBasisAt hx.1).map (A x hx).toLinearEquiv else b₀
  have hb (i : ι) : ContinuousAt (fun x => b x i) p := by
    have hc := (FiberBundle.continuousAt_section E p).mp
      (hs.contMDiffAt hU hp i).continuousAt
    apply hc.congr_of_eventuallyEq
    filter_upwards [hT.mem_nhds hpT] with x hx
    simp only [b, dif_pos hx, Basis.map_apply, IsLocalFrameOn.toBasisAt_coe]
    rfl
  have hlocal := basis_orientation_eventually_eq b p hb
  have hmem : ∀ᶠ x in 𝓝 p, x ∈ T := hT.mem_nhds hpT
  obtain ⟨V, hV, hVo, hpV⟩ := eventually_nhds_iff.mp (hmem.and hlocal)
  refine ⟨V, fun x hx => (hV x hx).1.1, fun x hx => (hV x hx).1.2, hVo, hpV, ?_⟩
  intro x hx
  have heq := (hV x hx).2
  simpa only [b, dif_pos (hV x hx).1, dif_pos hpT, Basis.orientation_map, A, e] using heq

open Classical in
theorem tangent_orientation_locality_of_local_frames
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) ι)
    (hframes : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ s : ι → (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ∃ hs : IsLocalFrameOn 𝓘(ℝ, E) E 0 s U,
          ∀ (x : M) (hx : x ∈ U), (hs.toBasisAt hx).orientation = o x) :
    ∀ p : M, ∃ (U : Set M) (hUs : U ⊆ (chartAt E p).source),
      IsOpen U ∧ p ∈ U ∧ ∀ (x : M) (hx : x ∈ U),
        Orientation.map _
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              hUs hx)).toLinearEquiv (o x) =
          Orientation.map _
            ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ p
              (by simpa only [TangentBundle.trivializationAt_baseSet] using
                mem_chart_source E p)).toLinearEquiv (o p) := by
  intro p
  obtain ⟨U, hU, hp, s, hs, ho⟩ := hframes p
  obtain ⟨V, hVU, hVs, hV, hpV, hlocal⟩ :=
    local_frame_tangent_orientation_eq_on_nhds s U hs hU p hp
  refine ⟨V, hVs, hV, hpV, ?_⟩
  intro x hx
  simpa only [ho x (hVU hx), ho p hp] using hlocal x hx

end Poincare.Topology

end
