import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskTensionTrace
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Measure.Area.Positivity

set_option autoImplicit false

noncomputable section

open Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The scalar trace of the actual induced second fundamental form in the
original complex coordinates agrees with every induced orthonormal basis.
The determinant is positive by immersion; no normality or conformality is needed. -/
theorem normal_scalar_secondFundamentalForm_disk_trace_eq_sum_orthonormal
    (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (z : N) (ν : TangentSpace 𝓘(ℝ, E) (U z))
    (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z))
    (hb : ∀ i j,
      (g.pullback (fun q : N => U q) hU hi).inner z (b i) (b j) =
        if i = j then 1 else 0) :
    let f : N → M := fun q => U q
    let gN := g.pullback f hU hi
    let II := secondFundamentalFormAmbientAt gN g f z
    let A := g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1)
    let B := g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I)
    let C := g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)
    let h11 := g.inner (U z) ν (II (1 : ℂ) (1 : ℂ))
    let h12 := g.inner (U z) ν (II (1 : ℂ) Complex.I)
    let h22 := g.inner (U z) ν (II Complex.I Complex.I)
    0 < A * C - B ^ 2 ∧
      (C * h11 + A * h22 - 2 * B * h12) / (A * C - B ^ 2) =
        ∑ i : Fin 2, g.inner (U z) ν (II (b i) (b i)) := by
  classical
  let f : N → M := fun q => U q
  let gN := g.pullback f hU hi
  let II : TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ]
      TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] TangentSpace 𝓘(ℝ, E) (U z) :=
    secondFundamentalFormAmbientAt gN g f z
  let A := g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1)
  let B := g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I)
  let C := g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)
  change 0 < A * C - B ^ 2 ∧
    (C * g.inner (U z) ν (II (1 : ℂ) (1 : ℂ)) + A * g.inner (U z) ν (II Complex.I Complex.I) -
      2 * B * g.inner (U z) ν (II (1 : ℂ) Complex.I)) / (A * C - B ^ 2) =
        ∑ i : Fin 2, g.inner (U z) ν (II (b i) (b i))
  have hdf : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f z : ℂ →L[ℝ] E) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z :=
    DifferentialGeometry.mfderiv_restrict_open U N z
  have hinjU : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
    rw [← hdf]
    exact hi z
  have hdet : 0 < A * C - B ^ 2 :=
    Real.sqrt_pos.mp (riemannianAreaDensity_pos_of_injective_mfderiv g hinjU)
  refine ⟨hdet, ?_⟩
  have hmetric (v w : ℂ) : gN.inner z v w =
      g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z w) := by
    exact congrArg (fun L : ℂ →L[ℝ] E => g.inner (U z) (L v) (L w)) hdf
  have h00 : gN.inner z (1 : ℂ) (1 : ℂ) = A := hmetric 1 1
  have h01 : gN.inner z (1 : ℂ) Complex.I = B := hmetric 1 Complex.I
  have h10 : gN.inner z Complex.I (1 : ℂ) = B :=
    (gN.symm z Complex.I (1 : ℂ)).trans h01
  have h11 : gN.inner z Complex.I Complex.I = C := hmetric Complex.I Complex.I
  let c : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z) := Complex.basisOneI
  have hc0 : c 0 = (1 : ℂ) := by
    change Complex.basisOneI 0 = (1 : ℂ)
    exact congrFun Complex.coe_basisOneI 0
  have hc1 : c 1 = Complex.I := by
    change Complex.basisOneI 1 = Complex.I
    exact congrFun Complex.coe_basisOneI 1
  let q : Fin 2 → Fin 2 → ℝ := fun i j =>
    if i = 0 then
      (if j = 0 then C / (A * C - B ^ 2) else -B / (A * C - B ^ 2))
    else if j = 0 then -B / (A * C - B ^ 2) else A / (A * C - B ^ 2)
  have hq00 : q 0 0 = C / (A * C - B ^ 2) := rfl
  have hq01 : q 0 1 = -B / (A * C - B ^ 2) := rfl
  have hq10 : q 1 0 = -B / (A * C - B ^ 2) := rfl
  have hq11 : q 1 1 = A / (A * C - B ^ 2) := rfl
  have hcancel : (A * C - B ^ 2) * (A * C - B ^ 2)⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hdet)
  have hq : MetricInverseInBasis gN z c q := by
    intro i j
    fin_cases i <;> fin_cases j <;> constructor <;>
      simp [Fin.sum_univ_two, hq00, hq01, hq10, hq11,
        hc0, hc1, h00, h01, h10, h11] <;>
      ring_nf at hcancel ⊢ <;> linarith only [hcancel]
  let Hν : TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ]
      TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (TangentSpace 𝓘(ℝ, ℂ) z)
      (TangentSpace 𝓘(ℝ, E) (U z)) ℝ (g.inner (U z) ν)).comp II
  let T : Tensor0SSpace (𝕜 := ℝ) (E := ℂ) (H := ℂ)
      (I := 𝓘(ℝ, ℂ)) (M := N) 2 z :=
    (((continuousMultilinearCurryFin1 ℝ (TangentSpace 𝓘(ℝ, ℂ) z) ℝ).symm.toContinuousLinearMap).comp
      Hν).uncurryLeft
  have hT (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
      T (vec2 (I := 𝓘(ℝ, ℂ)) v w) = g.inner (U z) ν (II v w) := by
    change ((continuousMultilinearCurryFin1 ℝ (TangentSpace 𝓘(ℝ, ℂ) z) ℝ).symm
      (Hν v)) (fun i : Fin 1 => vec2 (I := 𝓘(ℝ, ℂ)) v w i.succ) = _
    have htail : (fun i : Fin 1 => vec2 (I := 𝓘(ℝ, ℂ)) v w i.succ) = fun _ => w := by
      funext i
      fin_cases i
      rfl
    rw [htail]
    rfl
  have htraceb : metricTracePair0SAt gN T =
      ∑ i : Fin 2, g.inner (U z) ν (II (b i) (b i)) := by
    rw [metricTracePair0SAt_eq_sum_basis gN b _
      (metricInverseInBasis_of_orthonormal gN b hb)]
    simp [hT, identityInvMetric, diagonalInvMetric]
  have htracec := metricTracePair0SAt_eq_sum_basis gN c q hq T
  have hsymm : II Complex.I (1 : ℂ) = II (1 : ℂ) Complex.I :=
    secondFundamentalFormAmbientAt_symmetric gN g
      (hU.contMDiffAt.of_le (by simp)) Complex.I (1 : ℂ)
  rw [← htraceb, htracec]
  simp only [Fin.sum_univ_two, hq00, hq01, hq10, hq11, hT, hc0, hc1, hsymm]
  ring

end DifferentialGeometry.Geometry
