import DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_smooth_metric_agrees_on_neighborhood_of_is_closed
    (R : SmoothRiemannianMetric I M) (U : Opens M)
    (gU : SmoothRiemannianMetric I U) {K : Set M}
    (hK : IsClosed K) (hKU : K ⊆ (U : Set M)) :
    ∃ (g : SmoothRiemannianMetric I M) (V : Opens M),
      K ⊆ (V : Set M) ∧ ∃ hVU : (V : Set M) ⊆ (U : Set M),
        (∀ (x : M) (hx : x ∈ V) (v w : TangentSpace I x),
          g.inner x v w = gU.inner ⟨x, hVU hx⟩ v w) ∧
        (∀ (x : M), x ∉ U → ∀ v w : TangentSpace I x,
          g.inner x v w = R.inner x v w) := by
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let _ : LocallyCompactSpace U := ChartedSpace.locallyCompactSpace H U
  let _ : SecondCountableTopology U := inferInstance
  let _ : SigmaCompactSpace U := inferInstance
  let _ : NormalSpace M := inferInstance
  obtain ⟨W, hWopen, hKW, hWcl⟩ :=
    normal_exists_closure_subset hK U.isOpen hKU
  obtain ⟨χ, hχone, hχzero, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := I) (M := M)
      (n := (⊤ : ℕ∞)) hK (hKW.trans hWopen.interior_eq.ge)
  have hχsupport : tsupport (χ : M → ℝ) ⊆ (U : Set M) := by
    apply (closure_mono ?_).trans hWcl
    intro x hx
    by_contra hxW
    exact hx (hχzero x hxW)
  obtain ⟨V, hVopen, hKV, hVone⟩ := mem_nhdsSet_iff_exists.mp hχone
  let O : Opens M := ⟨V ∩ U, hVopen.inter U.isOpen⟩
  have hKO : K ⊆ (O : Set M) := fun x hx => ⟨hKV hx, hKU hx⟩
  have hOU : (O : Set M) ⊆ (U : Set M) := inter_subset_right
  let g := R.bumpExtendOpen U gU χ χ.contMDiff hχrange hχsupport
  refine ⟨g, O, hKO, hOU, ?_, ?_⟩
  · intro x hx v w
    exact bumpExtendOpen_eq_gU_on R U gU χ χ.contMDiff hχrange hχsupport O
      (fun y hy => hVone hy.1) hOU x hx v w
  · intro x hx v w
    exact bumpExtendOpen_inner_of_notMem_tsupport R U gU χ χ.contMDiff hχrange hχsupport
      x (fun h => hx (hχsupport h)) v w

theorem exists_smooth_metric_agrees_on_neighborhood_of_is_compact
    (R : SmoothRiemannianMetric I M) (U : Opens M)
    (gU : SmoothRiemannianMetric I U) {K : Set M}
    (hK : IsCompact K) (hKU : K ⊆ (U : Set M)) :
    ∃ (g : SmoothRiemannianMetric I M) (V : Opens M),
      K ⊆ (V : Set M) ∧ ∃ hVU : (V : Set M) ⊆ (U : Set M),
        (∀ (x : M) (hx : x ∈ V) (v w : TangentSpace I x),
          g.inner x v w = gU.inner ⟨x, hVU hx⟩ v w) ∧
        (∀ (x : M), x ∉ U → ∀ v w : TangentSpace I x,
          g.inner x v w = R.inner x v w) :=
  exists_smooth_metric_agrees_on_neighborhood_of_is_closed R U gU hK.isClosed hKU

end DifferentialGeometry
