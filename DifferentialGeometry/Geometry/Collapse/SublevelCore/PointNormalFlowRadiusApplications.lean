import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointNormalFlowRadius

/-!
# Consumers of the normal-flow radius data

* `point_outward_normalFlow_kernel_u_inputs`: LC54's soul radius supplies, for every level
  `T₀ > ℓ`, exactly the `u`-hypotheses of the LC55 kernel `point_distance_core_isotopy`
  (continuity, compact sublevels, an open `Wu ⊇ {T₀ ≤ u}` on which `u` and `V` are smooth, and
  `du(V) > 0` on `{T₀ ≤ u}`).
* `normalFlow_unitDisc_core_diffeomorph_nonempty`: with the soul's normal bundle as a smooth
  Riemannian bundle (fibre inner product `g`), X84's disc-core transport gives an actual
  diffeomorphism of manifolds with boundary `D(νS) ≅ {x | ‖(e.symm x).2‖ ≤ T}` for every
  diffeomorphism `e : νS ≃ M` and every `T > 0`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology.VectorBundle DifferentialGeometry.Topology.Morse

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

/-- **LC54 supplies the LC55 kernel's `u`-hypotheses.** -/
theorem point_outward_normalFlow_kernel_u_inputs [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ S : Set M, IsCompact S ∧ ∃ V : Cₛ^∞⟮I; E, TangentSpace I⟯, ∃ ℓ : ℝ, 0 < ℓ ∧
      ∃ u : M → ℝ, Continuous u ∧ (∀ T, IsCompact {x | u x ≤ T}) ∧ (∀ q ∈ S, u q = 0) ∧
        ∀ T₀, ℓ < T₀ → ∃ Wu : Set M, IsOpen Wu ∧ {x | T₀ ≤ u x} ⊆ Wu ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u Wu ∧
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) Wu ∧
          ∀ x, T₀ ≤ u x → 0 < mvfderiv (I := I) u x (V x) := by
  obtain ⟨S, -, -, -, hScomp, V, -, ℓ, hℓ, -, -, -, -, -, -, u, hu, hucpt, -, hzero, hsmooth,
    hdu, -⟩ := exists_point_outward_normalFlow_radius g hEnorm hsec p
  refine ⟨S, hScomp, V, ℓ, hℓ, u, hu, hucpt, hzero, fun T₀ hT₀ => ?_⟩
  refine ⟨{x | 0 < u x}, isOpen_lt continuous_const hu, fun x hx => ?_, hsmooth,
    V.contMDiff.contMDiffOn, fun x hx => ?_⟩
  · change 0 < u x
    have hx' : T₀ ≤ u x := hx
    linarith
  · rw [hdu x (by linarith)]
    exact one_pos

/-- **`D(νS) ≅ {‖(e.symm ·).2‖ ≤ T}` as manifolds with boundary.** For the soul's normal bundle
(a smooth Riemannian bundle, `normalBundle_isContMDiffRiemannianBundle`) and ANY diffeomorphism
`e : νS ≃ M`, X84's `unitDiscCoreDiffeomorph` is an actual diffeomorphism from the unit disc
bundle onto the radius-`T` disc core of `e`. -/
theorem normalFlow_unitDisc_core_diffeomorph_nonempty (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {S : Set M} (hconv : IsTotallyConvex g S)
    (hB : relBoundary I S = ∅) {T : ℝ} (hT : 0 < T) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    let _ := normalBundle_isContMDiff g hEnorm hconv hB
    let _ := normalBundle_isContMDiffRiemannianBundle g hEnorm hconv hB
    ∀ e : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
        (normalBundleFiber g S) ≃ₘ⟮
          (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
            𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
      let _ := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ))
        (V := normalBundleFiber g S) (normalBundle_totalSpace_finrank (I := I) S) 1 one_pos
      let _ := discCoreChartedSpace e (normalBundle_totalSpace_finrank (I := I) S) T hT
      Nonempty (Diffeomorph (morseModelWithCornersHalfSpace (Module.finrank ℝ E - 1))
        (morseModelWithCornersHalfSpace (Module.finrank ℝ E - 1))
        {z : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
          (normalBundleFiber g S) // ‖z.2‖ ≤ 1}
        {x : M // ‖(e.symm x).2‖ ≤ T} ∞) := by
  intro hS _ _ a _ _ _ _ _ e _ _
  exact ⟨unitDiscCoreDiffeomorph e (normalBundle_totalSpace_finrank (I := I) S) T hT⟩

end DifferentialGeometry.Geometry.Collapse
