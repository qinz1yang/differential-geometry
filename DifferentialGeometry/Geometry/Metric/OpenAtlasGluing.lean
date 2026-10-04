import DifferentialGeometry.Geometry.Metric.FiniteChartGluing
import DifferentialGeometry.Topology.Manifold.OpenCoverAtlas

set_option autoImplicit false

noncomputable section
open Bundle Manifold Set
open scoped ContDiff Topology

namespace DifferentialGeometry.Geometry.Metric

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M]

private theorem transition_derivative [ChartedSpace E M]
    (e d : OpenPartialHomeomorph M E)
    (he : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E))
    (hd : d.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E))
    {x : M} (hx : x ∈ e.source) (hxd : x ∈ d.source) :
    (fderiv ℝ (e.symm.trans d) (e x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) d x := by
  have hconvert : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e.symm.trans d) (e x) =
      fderiv ℝ (e.symm.trans d) (e x) := by
    exact (mfderiv_eq_fderiv (f := (e.symm.trans d)) (x := e x)).trans (by ext v; rfl)
  rw [← hconvert]
  change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (d ∘ e.symm) (e x)).comp _ = _
  have hd' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) d (e.symm (e x)) := by
    simpa only [e.left_inv hx] using hd.mdifferentiableAt hxd
  rw [mfderiv_comp (e x) hd' (he.mdifferentiableAt_symm (e.map_source hx))]
  ext v
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) d (e.symm (e x))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) d x v
  have hi := DFunLike.congr_fun (he.symm_comp_deriv hx) v
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v) = v at hi
  rw [hi]
  exact congrArg (fun y : M => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) d y v) (e.left_inv hx)

theorem exists_unique_contMDiffMetric_of_open_atlas
    [FiniteDimensional ℝ E] {ι : Type*}
    (e : ι → OpenPartialHomeomorph M E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source) (p : ℕ)
    (htrans : ∀ i j, ContDiffOn ℝ ((p + 1 : ℕ) : ℕ∞ω) ((e i).symm.trans (e j))
      ((e i).symm.trans (e j)).source)
    (B : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hregular : ∀ i, ContDiffOn ℝ (p : ℕ∞ω) (B i) (e i).target)
    (hsymm : ∀ i x, x ∈ (e i).target → ∀ v w, B i x v w = B i x w v)
    (hpos : ∀ i x, x ∈ (e i).target → ∀ v, v ≠ 0 → 0 < B i x v v)
    (hcompat : ∀ i j u, u ∈ ((e i).symm.trans (e j)).source →
      B i u = (B j (((e i).symm.trans (e j)) u)).bilinearComp
        (fderiv ℝ ((e i).symm.trans (e j)) u)
        (fderiv ℝ ((e i).symm.trans (e j)) u)) :
    letI := DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover e hcover
    letI := DifferentialGeometry.Topology.Manifold.isManifold_chartedSpaceOfOpenCover
      e hcover htrans
    letI : IsManifold 𝓘(ℝ, E) 1 M := IsManifold.of_le (n := ((p + 1 : ℕ) : ℕ∞ω))
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le p))
    ∃! G : ContMDiffRiemannianMetric 𝓘(ℝ, E) (p : ℕ∞ω) E
        (TangentSpace 𝓘(ℝ, E) : M → Type _),
      ∀ i x, x ∈ (e i).source → ∀ v w : E,
        G.inner x v w = B i (e i x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e i) x v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e i) x w) := by
  let := DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover e hcover
  let := DifferentialGeometry.Topology.Manifold.isManifold_chartedSpaceOfOpenCover
    e hcover htrans
  let : IsManifold 𝓘(ℝ, E) 1 M := IsManifold.of_le (n := ((p + 1 : ℕ) : ℕ∞ω))
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le p))
  have he (i : ι) : e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ((p + 1 : ℕ) : ℕ∞ω) M :=
    IsManifold.subset_maximalAtlas (Set.mem_range_self i)
  let c (i : ι) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ((p + 1 : ℕ) : ℕ∞ω) := {
    (e i).toPartialEquiv with
    open_source := (e i).open_source
    open_target := (e i).open_target
    contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas (he i)
    contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas (he i) }
  have hn : ((p + 1 : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  have hd (i : ι) : (e i).MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(c i).mdifferentiableOn hn, (c i).symm.mdifferentiableOn hn⟩
  apply exists_unique_contMDiffMetric_of_compatible_charts p c B hcover
    hregular hsymm hpos
  intro i j x hi hj v w
  have hmem : e i x ∈ ((e i).symm.trans (e j)).source := by
    refine ⟨(e i).map_source hi, ?_⟩
    change (e i).symm (e i x) ∈ (e j).source
    rwa [(e i).left_inv hi]
  change B i (e i x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e i) x v)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e i) x w) = _
  rw [hcompat i j _ hmem]
  change B j (e j ((e i).symm (e i x)))
    (((fderiv ℝ ((e i).symm.trans (e j)) (e i x)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e i) x)) v)
    (((fderiv ℝ ((e i).symm.trans (e j)) (e i x)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e i) x)) w) = _
  rw [(e i).left_inv hi, transition_derivative (e i) (e j) (hd i) (hd j) hi hj]
  rfl

end DifferentialGeometry.Geometry.Metric
