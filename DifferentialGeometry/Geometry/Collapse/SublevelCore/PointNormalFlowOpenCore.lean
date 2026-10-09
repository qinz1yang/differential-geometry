import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointNormalFlowRadius
import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenDiscCoreType

/-!
# LC54 with its open cores: the interior of every radius core is the whole manifold

Master207A, LC54 (A:22850) as used in LC61 (A:23460): LC54's soul radius `u` (the fibre radius
`‖(e.symm ·).2‖` of the actual normal-flow diffeomorphism `e : νS ≃ N`) has, for every `T > 0`, an
open partial diffeomorphism of `N` with source `int {u ≤ T}` and target all of `N`
(`int {‖·‖ ≤ T} ≃ νS` by `exists_partialDiffeomorph_discCore_interior`, then `e`). The statement is
bundle-free: the normal bundle appears only inside the proof, so the package can be used in a
context with rescaled metric instances (the fibre norms of `νS` depend on the ambient Riemannian
bundle instance).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology.VectorBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

/-- **LC54 with open cores, bundle-free.** For a complete noncompact `M` with `sec ≥ 0` and a point
`p`: LC54's smooth field `V` (`|V| ≤ 2`, pairing `≤ -1/4` with every inward unit minimizing
direction beyond `A₂`), and a proper continuous coordinate `u ≥ 0`, smooth where positive, with
`du(V) = 1` beyond `ℓ`, such that for every `T > 0` the interior of `{u ≤ T}` is diffeomorphic to
`M` (an open partial diffeomorphism of `M` with that source and target everything). -/
theorem exists_point_outward_normalFlow_openCore [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ V : Cₛ^∞⟮I; E, TangentSpace I⟯, ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ A₂ : ℝ, 0 < A₂ ∧
      (∀ q, g.inner q (V q) (V q) ≤ 4) ∧
      (∀ q, A₂ ≤ dist p q → ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm p q,
        g.inner q (V q) w ≤ -(1 / 4)) ∧
      ∃ u : M → ℝ, Continuous u ∧ (∀ T, IsCompact {x | u x ≤ T}) ∧ (∀ x, 0 ≤ u x) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u {x | 0 < u x} ∧
        (∀ x, ℓ < u x → mvfderiv (I := I) u x (V x) = 1) ∧
        ∀ T : ℝ, 0 < T → ∃ Ψ : PartialDiffeomorph I I M M ∞,
          Ψ.source = interior {x | u x ≤ T} ∧ Ψ.target = univ := by
  obtain ⟨S, hconv, hB, -, hScomp, V, ϕ, ℓ, hℓ, A₂, hA₂, hVB, -, -, hVdir, u, hu, hucpt, hu0, -,
    hsmooth, hdu, hdata⟩ := exists_point_outward_normalFlow_radius g hEnorm hsec p
  refine ⟨V, ℓ, hℓ, A₂, hA₂, hVB, hVdir, u, hu, hucpt, hu0, hsmooth, hdu, fun T hT => ?_⟩
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  let _ := normalBundle_isContMDiffRiemannianBundle g hEnorm hconv hB
  obtain ⟨e, -, -, hue⟩ := hdata
  obtain ⟨Ψ, hΨs, hΨt⟩ := exists_partialDiffeomorph_discCore_interior e hT
  have hset : {x | ‖(e.symm x).2‖ ≤ T} = {x | u x ≤ T} := by
    ext x
    simp only [mem_ofPred_eq, hue x]
  refine ⟨Ψ.trans e.toPartialDiffeomorph, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source, hΨs, hset]
    exact inter_eq_left.mpr fun x _ => mem_univ _
  · apply eq_univ_of_forall
    intro y
    refine ⟨mem_univ y, ?_⟩
    change e.symm y ∈ Ψ.target
    rw [hΨt]
    exact mem_univ _

end DifferentialGeometry.Geometry.Collapse
