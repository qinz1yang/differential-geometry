import DifferentialGeometry.Topology.Embedding.Retraction
import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace Manifold.IsSmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {f : M → N}

theorem contMDiff_tangentSection_iff
    (hf : IsSmoothEmbedding I J ∞ f) (V : (x : M) → TangentSpace I x) :
    ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ↔
      ContMDiff I J.tangent ∞
        (fun x => (⟨f x, mfderiv I J f x (V x)⟩ : TangentBundle J N)) := by
  constructor
  · intro hV
    exact (hf.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp hV
  · intro hV x
    classical
    obtain ⟨U, hxU, r, hr, _, hfix⟩ := hf.exists_contMDiff_local_retraction x
    let R : N → M := Subtype.val.extend r (fun _ => x)
    have hR (q : U) : R q = r q :=
      Subtype.val_injective.extend_apply r (fun _ => x) q
    have hRU : ContMDiff J I ∞ (fun q : U => R q) := hr.congr hR
    have hRat (y : N) (hy : y ∈ U) : ContMDiffAt J I ∞ R y :=
      contMDiffAt_subtype_iff.mp (hRU ⟨y, hy⟩)
    have hRf (y : M) (hy : f y ∈ U) : R (f y) = y := (hR ⟨f y, hy⟩).trans (hfix y hy)
    have hnear (y : M) (hy : f y ∈ U) : ∀ᶠ z in 𝓝 y, f z ∈ U :=
      hf.contMDiff.continuous.continuousAt.preimage_mem_nhds (U.isOpen.mem_nhds hy)
    have hgraph : (fun y => (⟨y, V y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
        tangentMap J I R ∘
          (fun y => (⟨f y, mfderiv I J f y (V y)⟩ : TangentBundle J N)) := by
      filter_upwards [hnear x hxU] with y hy
      have heq : (R ∘ f) =ᶠ[𝓝 y] id := (hnear y hy).mono fun z hz => hRf z hz
      have hd : (mfderiv J I R (f y)).comp (mfderiv I J f y) =
          ContinuousLinearMap.id ℝ E := by
        rw [← mfderiv_comp y ((hRat (f y) hy).mdifferentiableAt (by simp))
          (hf.contMDiff.mdifferentiableAt (by simp)), heq.mfderiv_eq, mfderiv_id]
        rfl
      apply TotalSpace.ext
      · exact (hRf y hy).symm
      · apply heq_of_eq
        change V y = (mfderiv J I R (f y)).comp (mfderiv I J f y) (V y)
        rw [hd]
        rfl
    have hTR := DifferentialGeometry.VectorField.contMDiffAt_tangentMap
      (p := (⟨f x, mfderiv I J f x (V x)⟩ : TangentBundle J N))
      (hRat (f x) hxU) (m := ∞) (by simp)
    exact (hTR.comp x (hV x)).congr_of_eventuallyEq hgraph

theorem exists_contMDiff_tangent_lift
    (hf : IsSmoothEmbedding I J ∞ f) (W : (x : M) → TangentSpace J (f x))
    (hW : ContMDiff I J.tangent ∞ (fun x => (⟨f x, W x⟩ : TangentBundle J N)))
    (hrange : ∀ x, W x ∈ (mfderiv I J f x).range) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      ∀ x, mfderiv I J f x (V x) = W x := by
  choose V hV using hrange
  refine ⟨V, (hf.contMDiff_tangentSection_iff V).mpr ?_, hV⟩
  exact hW.congr fun x => congrArg (fun w => (⟨f x, w⟩ : TangentBundle J N)) (hV x)

end Manifold.IsSmoothEmbedding
