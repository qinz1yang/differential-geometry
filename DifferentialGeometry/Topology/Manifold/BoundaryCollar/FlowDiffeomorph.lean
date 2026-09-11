import DifferentialGeometry.Topology.Manifold.BoundaryCollar.FlowInverse
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.FlowEmbedding
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.ProductLift
import Mathlib.Geometry.Manifold.Diffeomorph

open Set Function Filter Manifold Topology TopologicalSpace
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar

theorem exists_boundary_flow_diffeomorph
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] (hK : IsCompact ((𝓡∂ (n + 1)).boundary M))
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
      0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p))
    {U : Opens M} (hKU : (𝓡∂ (n + 1)).boundary M ⊆ U)
    {ε : ℝ} [Fact ((0 : ℝ) < ε)] {F : M × ℝ → M}
    (hF : ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (n + 1)) ∞ F
      ((U : Set M) ×ˢ Icc (0 : ℝ) ε))
    (hzero : ∀ q ∈ U, F (q, 0) = q)
    (hcurve : ∀ q ∈ U, IsMIntegralCurveOn (fun t => F (q, t)) V (Icc (0 : ℝ) ε))
    (hi : ∀ q ∈ U, ∀ t ∈ Ioc (0 : ℝ) ε, (𝓡∂ (n + 1)).IsInteriorPoint (F (q, t))) :
    ∃ W : Opens M, (𝓡∂ (n + 1)).boundary M ⊆ W ∧
      ∃ Ω : Opens (BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) ε),
        (∀ p, (p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩) ∈ Ω) ∧
        ∃ e : Diffeomorph ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
          (𝓡∂ (n + 1)) Ω W ∞,
          ∀ q : Ω, (e q : M) = F ((q.val.1 : M), (q.val.2 : ℝ)) := by
  classical
  have hε : 0 < ε := Fact.out
  let I := 𝓡∂ (n + 1)
  let B := BoundaryManifold I M
  let J := (HasSmoothBoundary.boundaryModel I).prod (𝓡∂ 1)
  let c : B × Icc (0 : ℝ) ε → M := fun q => F ((q.1 : M), (q.2 : ℝ))
  have hc : ContMDiff J I ∞ c := hF.comp_contMDiff
    ((boundaryInclusion_contMDiff (I := I) (M := M)).prodMap
      (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := ε)))
    (fun q => ⟨hKU q.1.2, q.2.2⟩)
  have hcinj : Injective c := boundary_flow_injective hV hKU hzero hcurve hi
  let : CompactSpace B := isCompact_iff_compactSpace.mp hK
  have hemb := hc.continuous.isClosedEmbedding hcinj
  have hlocal (p : B) := exists_smooth_boundary_flow_rightInverse p.2 hV (hpos p)
    U.isOpen (hKU p.2) hε hzero hcurve hi
  choose O hpO R hR hright using hlocal
  let W : Opens M := ⟨⋃ p : B, (O p : Set M), isOpen_iUnion (fun p => (O p).isOpen)⟩
  have hKW : I.boundary M ⊆ W := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpO ⟨p, hp⟩⟩
  have hWrange : (W : Set M) ⊆ range c := by
    intro y hy
    obtain ⟨p, hyp⟩ := mem_iUnion.mp hy
    have hh := hright p y hyp
    refine ⟨(⟨(R p y).1, hh.2.1⟩, ⟨(R p y).2, hh.2.2.1.1, hh.2.2.1.2.le⟩), ?_⟩
    exact hh.2.2.2
  let Ω : Opens (B × Icc (0 : ℝ) ε) := ⟨c ⁻¹' W, W.isOpen.preimage hc.continuous⟩
  let e : Ω ≃ₜ W := hemb.isEmbedding.homeomorphOfSubsetRange hWrange
  have heq (q : Ω) : (e q : M) = c q.val := rfl
  have hinverse (y : W) : c (e.symm y).val = y.val := by
    rw [← heq, e.apply_symm_apply]
  have he : ContMDiff J I ∞ e := by
    apply (ContMDiff.subtypeVal_comp_iff W e).mp
    exact hc.comp contMDiff_subtype_val
  have hinv : ContMDiff I J ∞ e.symm := by
    apply (ContMDiff.subtypeVal_comp_iff Ω e.symm).mp
    intro y
    apply (contMDiffAt_boundary_product_iff (I := I) le_rfl).mpr
    obtain ⟨p, hyp⟩ := mem_iUnion.mp y.property
    have hRy : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞ (R p) y.val :=
      (hR p y.val hyp).contMDiffAt ((O p).isOpen.mem_nhds hyp)
    have hs := hRy.comp y (contMDiff_subtype_val (U := W)).contMDiffAt
    apply hs.congr_of_eventuallyEq
    have hevent : ∀ᶠ z : W in 𝓝 y, z.val ∈ O p :=
      continuous_subtype_val.continuousAt.eventually ((O p).isOpen.mem_nhds hyp)
    filter_upwards [hevent] with z hz
    have hh := hright p z.val hz
    let q : B × Icc (0 : ℝ) ε :=
      (⟨(R p z.val).1, hh.2.1⟩, ⟨(R p z.val).2, hh.2.2.1.1, hh.2.2.1.2.le⟩)
    have hq : (e.symm z).val = q := hcinj ((hinverse z).trans hh.2.2.2.symm)
    change (((e.symm z).val.1 : M), ((e.symm z).val.2 : ℝ)) = R p z.val
    rw [hq]
  refine ⟨W, hKW, Ω, ?_, ⟨e.toEquiv, he, hinv⟩, ?_⟩
  · intro p
    change c (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) ∈ W
    have hz : c (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) = p.val := hzero p.val (hKU p.2)
    rw [hz]
    exact hKW p.2
  · exact heq

end DifferentialGeometry.Manifold.BoundaryCollar
