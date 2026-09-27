import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Height
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.FlowEmbedding
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.UniformInwardFlow
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.StripNeighborhood
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Shrinking
import Mathlib.Geometry.Manifold.Instances.Icc

open Set Function Filter Manifold
open scoped Topology ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar


theorem exists_smooth_unit_height_boundary_strip
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] (hK : IsCompact ((𝓡∂ (n + 1)).boundary M))
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
      0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p))
    (N : TopologicalSpace.Opens M) (hKN : (𝓡∂ (n + 1)).boundary M ⊆ N)
    {r : M → ℝ} (hr : MDifferentiable (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r)
    (hrzero : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M, r p = 0)
    (hunit : ∀ y ∈ N, (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r y) (V y) = (1 : ℝ)) :
    ∃ (ε : ℝ) (hε : 0 < ε),
      let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
      ∃ c : BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) ε → M,
        Topology.IsClosedEmbedding c ∧
        ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
          (𝓡∂ (n + 1)) ∞ c ∧
        (∀ p, c (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
        (∀ q, r (c q) = (q.2 : ℝ)) ∧
        (∀ p (t : Icc (0 : ℝ) ε), 0 < (t : ℝ) → (𝓡∂ (n + 1)).IsInteriorPoint (c (p, t))) ∧
        ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
          IsOpen (c '' {q | (q.2 : ℝ) < δ}) ∧
          (𝓡∂ (n + 1)).boundary M ⊆ c '' {q | (q.2 : ℝ) < δ} := by
  obtain ⟨U,hKU,ε,hε,F,hF,hzero,hcurve,hi,_⟩ :=
    exists_uniform_boundary_flow_of_inward hV hpos hK
  let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  obtain ⟨η,hη,hηε,Y,_,_,d,hd,hheight⟩ :=
    exists_boundary_flow_collar_diffeomorph_height hK hV hpos hKU hF hzero hcurve hi N hKN hr hrzero hunit
  let τ : ℝ := η/2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτη : τ < η := by dsimp [τ]; linarith
  have hτε : τ ≤ ε := hτη.le.trans hηε.le
  have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) ε := Icc_subset_Icc le_rfl hτε
  have hcurve' : ∀ y ∈ U, IsMIntegralCurveOn (fun t => F (y,t)) V (Icc (0 : ℝ) τ) :=
    fun y hy => (hcurve y hy).mono hsub
  have hi' : ∀ y ∈ U, ∀ t ∈ Ioc (0 : ℝ) τ, (𝓡∂ (n+1)).IsInteriorPoint (F (y,t)) :=
    fun y hy t ht => hi y hy t ⟨ht.1,ht.2.trans hτε⟩
  refine ⟨τ,hτ,?_⟩
  let : Fact ((0 : ℝ) < τ) := ⟨hτ⟩
  let I := 𝓡∂ (n + 1)
  let B := BoundaryManifold I M
  let c : B × Icc (0 : ℝ) τ → M := fun q => F ((q.1 : M), (q.2 : ℝ))
  have hc : ContMDiff ((HasSmoothBoundary.boundaryModel I).prod (𝓡∂ 1)) I ∞ c := by
    exact hF.comp_contMDiff
      ((boundaryInclusion_contMDiff (I := I) (M := M)).prodMap
        (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := τ)))
      (fun q => ⟨hKU q.1.2, hsub q.2.2⟩)
  have hcinj : Injective c := boundary_flow_injective hV hKU hzero hcurve' hi'
  let : CompactSpace B := isCompact_iff_compactSpace.mp hK
  have hemb := hc.continuous.isClosedEmbedding hcinj
  have hrange : ∀ p : B, range c ∈ 𝓝 (c (p, ⟨0, ⟨le_rfl, hτ.le⟩⟩)) := by
    intro p
    have hpflow := boundary_flow_image_mem_nhds p.2 hV (hpos p)
      U.isOpen (hKU p.2) hτ hzero hcurve' hi'
    have hpzero : c (p, ⟨0, ⟨le_rfl, hτ.le⟩⟩) = (p : M) := hzero p (hKU p.2)
    rw [hpzero]
    apply mem_of_superset hpflow
    rintro y ⟨q, _, hq, t, ht, hty⟩
    exact ⟨(⟨q, hq⟩, ⟨t, ht.1, ht.2.le⟩), hty⟩
  obtain ⟨δ, hδ, hδε, hopen, hzimage⟩ := exists_open_shorter_strip hτ hemb.isEmbedding hrange
  refine ⟨c, hemb, hc, ?_, ?_, ?_, δ, hδ, hδε, hopen, ?_⟩
  · intro p
    exact hzero p (hKU p.2)
  · intro q
    let q' : {q : B × Icc (0 : ℝ) ε | (q.2 : ℝ) < η} :=
      ⟨(q.1,⟨q.2.val,hsub q.2.property⟩),q.2.property.2.trans_lt hτη⟩
    have he : (d q' : M) = c q := hd q'
    exact (congrArg r he).symm.trans (hheight q')
  · intro p t ht
    exact hi' p (hKU p.2) t ⟨ht,t.2.2⟩
  · intro p hp
    have hh := hzimage ⟨p, hp⟩
    have hezero : c (⟨p, hp⟩, ⟨0, ⟨le_rfl, hτ.le⟩⟩) = p := hzero p (hKU hp)
    rwa [hezero] at hh

end DifferentialGeometry.Manifold.BoundaryCollar
