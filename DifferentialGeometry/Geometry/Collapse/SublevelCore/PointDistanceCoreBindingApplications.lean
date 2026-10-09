import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointDistanceCoreBinding

/-!
# Consumer of the LC55 binding: `D ≅ D(νS)` as manifolds with boundary

For LC54's normal-flow diffeomorphism and the normalized-scale LC55 inputs, every core
`D = {ζ ≤ 1}` is, for `ρ ∈ (T₀, T₁)`, the disc core `{‖(e'.symm ·).2‖ ≤ ρ}` of a diffeomorphism
`e' : νS ≃ M`, and X84's `unitDiscCoreDiffeomorph e'` is an actual diffeomorphism of manifolds with
boundary from the unit disc bundle `D(νS)` onto that disc core.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Topology
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

/-- **LC55's core is diffeomorphic to `D(νS)`** (normalized scale). -/
theorem point_distance_core_unitDisc_diffeomorph
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    {S : Set M} (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅) (hScomp : IsCompact S)
    (V : Cₛ^∞⟮I; E, TangentSpace I⟯) (ϕ : Flow ℝ M) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hIntegral : ∀ q, IsMIntegralCurve (fun t => ϕ t q) V)
    (hVB : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → g.inner x (V x) (V x) ≤ 4)
    (hVdir : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
      ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm p x, g.inner x (V x) w ≤ -(1 / 4))
    {ζ : M → ℝ} {ε : ℝ≥0} (hε : (ε : ℝ) ≤ 1 / 64)
    (hclose : ∀ x, |ζ x - dist p x| < 1 / 80)
    (hlip : LipschitzWith ε (fun x => ζ x - dist p x))
    {Wζ : Set M} (hWζ : IsOpen Wζ)
    (hcollarW : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → x ∈ Wζ)
    (hζW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ Wζ) {T₀ : ℝ} (hℓT₀ : ℓ < T₀) :
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
      (∀ z, e z = normalFlowMap (I := I) g hEnorm S ϕ ℓ z) →
      {x | ‖(e.symm x).2‖ ≤ T₀} ⊆ Metric.ball p (1 / 2) →
      ∃ T₁ : ℝ, T₀ < T₁ ∧ ∀ ρ ∈ Ioo T₀ T₁, ∃ hρ : 0 < ρ,
        ∃ e' : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
            (normalBundleFiber g S) ≃ₘ⟮
              (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
                𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
          {x | ζ x ≤ 1} = {x | ‖(e'.symm x).2‖ ≤ ρ} ∧
          let _ := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ))
            (V := normalBundleFiber g S) (normalBundle_totalSpace_finrank (I := I) S) 1 one_pos
          let _ := discCoreChartedSpace e' (normalBundle_totalSpace_finrank (I := I) S) ρ hρ
          Nonempty (Diffeomorph (morseModelWithCornersHalfSpace (Module.finrank ℝ E - 1))
            (morseModelWithCornersHalfSpace (Module.finrank ℝ E - 1))
            {z : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
              (normalBundleFiber g S) // ‖z.2‖ ≤ 1}
            {x : M // ‖(e'.symm x).2‖ ≤ ρ} ∞) := by
  intro hS _ _ a _ _ _ _ _ e he hT₀
  obtain ⟨-, -, -, -, -, T₁, hT₁, hiso⟩ :=
    point_distance_core_normalFlow_discCore g hEnorm p hconv hB hScomp V ϕ hℓ hIntegral hVB hVdir
      hε hclose hlip hWζ hcollarW hζW hℓT₀ e he hT₀
  refine ⟨T₁, hT₁, fun ρ hρ => ?_⟩
  obtain ⟨-, -, -, -, -, -, e', -, hD⟩ := hiso ρ hρ
  have hρpos : 0 < ρ := (hℓ.trans_lt hℓT₀).trans hρ.1
  exact ⟨hρpos, e', hD,
    ⟨unitDiscCoreDiffeomorph e' (normalBundle_totalSpace_finrank (I := I) S) ρ hρpos⟩⟩

end DifferentialGeometry.Geometry.Collapse
