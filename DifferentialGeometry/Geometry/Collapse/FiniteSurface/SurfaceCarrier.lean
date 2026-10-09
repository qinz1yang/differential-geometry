import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceFactor
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.ClosedSurfaceType
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.FactorCurvature
import DifferentialGeometry.Topology.Manifold.LinearModelChange
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.DerivativeOrders

/-!
# LFR17 on the LFR16 surface factor, modulo the orientation

The surface factor `Z` of an exact line splitting of a nonnegatively curved 3-manifold (LFR16) has
a smooth carrier `S` modelled on `𝓡 2` (`EuclideanSpace ℝ (Fin 2)`), `C^{k+2}`-diffeomorphic to
`Z`, carrying the pulled-back `C^{k+1}` metric `κ` of nonnegative curvature; `S` is compact and
connected. For EVERY orientation of `S`, LFR17 (`Collapse.finiteSurface_sphere_or_flat_torus`)
applies: `S` is diffeomorphic to the round `S²`, or to `ℝ²/ℤ²` with `κ` flat
(`surfaceFactor_smoothCarrier`).

What is NOT here: an orientation of `S` itself, i.e. the finite-order orientation of the factor
induced by an orientation of `N` and the ordered normal factor (risk U4; see
build-logs/resume/sheet-F7-LFR11b.md §6, §8).

Route: model change `Fin 2 → ℝ ⇝ 𝓡 2` (`LinearModelChange`), the induced metric pulled back by
that diffeomorphism, the smooth carrier `exists_smoothCarrier_metric_with_derivative_orders`
(which transports sectional curvature), and tier T4 (`inducedMetric_sectionalCurvature_nonneg`)
through the cross-model naturality `sectionalCurvature_eq_of_partialDiffeomorph_pullback_cross`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting DifferentialGeometry.Manifold
  DifferentialGeometry.Topology.Manifold

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "P" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

local instance nezero_finrank_euclidean_three_carrier_F7LFR11b :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

theorem finrank_splittingSurfaceModel_eq :
    Module.finrank ℝ P = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
  rw [Module.finrank_fin_fun, finrank_euclidean_three_sub_one, finrank_euclideanSpace_fin]

/-- The linear identification of the regular-zero model `Fin 2 → ℝ` with `𝓡 2`. -/
def splittingSurfaceModelEquiv : P ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearEquiv.ofFinrankEq finrank_splittingSurfaceModel_eq

theorem withTop_natCast_add_two (k : ℕ) : (((k : ℕ∞) : ℕ∞ω) + 2) = ((k + 2 : ℕ) : ℕ∞ω) := by
  push_cast
  rfl

theorem withTop_natCast_add_one (k : ℕ) : (((k : ℕ∞) : ℕ∞ω) + 1) = ((k + 1 : ℕ) : ℕ∞ω) := by
  push_cast
  rfl

universe u

/-- The induced metric re-indexed at natural order `k + 1`. -/
def inducedMetricNat {N W : Type u} [MetricSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [CompleteSpace N] [MetricSpace W] {k : ℕ}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hk : 2 ≤ (k : ℕ∞))
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI := splittingFactorChartedSpace G hk hnorm e
    letI := splittingFactor_isManifold_one G hk hnorm e
    ContMDiffRiemannianMetric 𝓘(ℝ, P) ((k + 1 : ℕ) : ℕ∞ω) P
      (TangentSpace 𝓘(ℝ, P) : {x : N // (e x).fst = 0} → Type _) :=
  letI := splittingFactorChartedSpace G hk hnorm e
  letI := splittingFactor_isManifold_one G hk hnorm e
  { inducedMetric G hk hnorm e with
    contMDiff := withTop_natCast_add_one k ▸ (inducedMetric G hk hnorm e).contMDiff }

theorem inducedMetricNat_inner {N W : Type u} [MetricSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [CompleteSpace N] [MetricSpace W] {k : ℕ}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hk : 2 ≤ (k : ℕ∞))
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI := splittingFactorChartedSpace G hk hnorm e
    letI := splittingFactor_isManifold_one G hk hnorm e
    ∀ z, (inducedMetricNat G hk hnorm e).inner z = (inducedMetric G hk hnorm e).inner z :=
  fun _ => rfl

/-- **LFR17 on the LFR16 surface factor, for every orientation of its smooth carrier.** -/
theorem surfaceFactor_smoothCarrier {N W : Type u} [MetricSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [CompleteSpace N] [ConnectedSpace N]
    [SecondCountableTopology N] [MetricSpace W] [CompactSpace W] {k : ℕ}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hk : 2 ≤ (k : ℕ∞))
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    {D : ℝ} (hD : ∀ a b : W, dist a b ≤ D) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI := splittingFactorChartedSpace G hk hnorm e
    letI := splittingFactor_isManifold_one G hk hnorm e
    ∃ (S : Type u) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S),
      CompactSpace S ∧ ConnectedSpace S ∧
      ∃ φ : S ≃ₜ {x : N // (e x).fst = 0},
        ContMDiff (𝓡 2) 𝓘(ℝ, P) ((k + 2 : ℕ) : ℕ∞ω) φ ∧
        ContMDiff 𝓘(ℝ, P) (𝓡 2) ((k + 2 : ℕ) : ℕ∞ω) φ.symm ∧
        ∃ κ : ContMDiffRiemannianMetric (𝓡 2) ((k + 1 : ℕ) : ℕ∞ω) E2
            (TangentSpace (𝓡 2) : S → Type _),
          (∀ (x : S) (v w : TangentSpace (𝓡 2) x),
            κ.inner x v w = (inducedMetric G hk hnorm e).inner (φ x)
              (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x v) (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x w)) ∧
          (∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w) ∧
          (Nonempty (ManifoldOrientation (𝓡 2) S 2) →
            Nonempty (S ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
              (Nonempty (S ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) ∧
                ∀ (x : S) (v w : TangentSpace (𝓡 2) x), κ.sectionalCurvature x v w = 0)) := by
  let _ := splittingFactorChartedSpace G hk hnorm e
  let _ := splittingFactor_isManifold_one G hk hnorm e
  let Z := {x : N // (e x).fst = 0}
  let _ : IsManifold 𝓘(ℝ, P) ((k + 2 : ℕ) : ℕ∞ω) Z :=
    withTop_natCast_add_two k ▸ splittingFactor_isManifold G hk hnorm e
  let L := splittingSurfaceModelEquiv
  let ZE := LinearModelChange Z L
  let _ : IsManifold (𝓡 2) ((k + 2 : ℕ) : ℕ∞ω) ZE := LinearModelChange.isManifold L
  let φ₀ : Diffeomorph (𝓡 2) 𝓘(ℝ, P) ZE Z ((k + 2 : ℕ) : ℕ∞ω) :=
    LinearModelChange.diffeomorph L
  let h' := inducedMetricNat G hk hnorm e
  obtain ⟨hE, hEinner⟩ := exists_finite_order_pullback_metric_of_diffeomorph (k + 1) (k + 2)
    (k + 1) le_rfl le_rfl h' φ₀
  let _ : LocallyCompactSpace ZE := ChartedSpace.locallyCompactSpace E2 ZE
  let _ : TopologicalSpace.MetrizableSpace ZE :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable ZE
  let _ : MetricSpace ZE := TopologicalSpace.metrizableSpaceMetric ZE
  obtain ⟨s, A, -, -, ⟨f, -, -⟩, -⟩ :=
    exists_smoothCarrier_metric_with_derivative_orders (E := E2) (X := ZE) (K := k + 1)
      (by exact_mod_cast (show 3 ≤ k + 1 by have := hk; norm_cast at this; omega)) hE
  let S := SmoothCarrier A
  have hk2 : 2 ≤ k := by exact_mod_cast hk
  obtain ⟨-, hcZ, hconnZ, -⟩ := surfaceFactor_of_exactSplitting G hk hnorm hsec hD e
  let Φ : Diffeomorph (𝓡 2) 𝓘(ℝ, P) S Z ((k + 2 : ℕ) : ℕ∞ω) := f.trans φ₀
  have hS : IsManifold (𝓡 2) ((k + 1 + 1 : ℕ) : ℕ∞ω) S :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  obtain ⟨κ, hκ⟩ := exists_finite_order_pullback_metric_of_diffeomorph (k + 1) (k + 2) (k + 1)
    le_rfl le_rfl h' Φ
  have h3Z : IsManifold 𝓘(ℝ, P) 3 Z := IsManifold.of_le (n := ((k + 2 : ℕ) : ℕ∞ω))
    (by exact_mod_cast (show 3 ≤ k + 2 by omega))
  have hn2 : (2 : ℕ∞ω) ≤ ((k + 1 : ℕ) : ℕ∞ω) := by exact_mod_cast (show 2 ≤ k + 1 by omega)
  have hsecS : ∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w := by
    intro x v w
    rw [sectionalCurvature_eq_of_partialDiffeomorph_pullback_cross κ h' hn2 hn2
      (DifferentialGeometry.PartialDiffeomorph.ofLE Φ.toPartialDiffeomorph
        (by exact_mod_cast (show 3 ≤ k + 2 by omega)))
      (fun q _ v' w' => hκ q v' w') (mem_univ x) v w]
    exact inducedMetric_sectionalCurvature_nonneg G hk hnorm e hsec _ _ _
  have hinner : ∀ (x : S) (v w : TangentSpace (𝓡 2) x),
      κ.inner x v w = (inducedMetric G hk hnorm e).inner (Φ.toHomeomorph x)
        (mfderiv (𝓡 2) 𝓘(ℝ, P) Φ.toHomeomorph x v)
        (mfderiv (𝓡 2) 𝓘(ℝ, P) Φ.toHomeomorph x w) := by
    intro x v w
    rw [hκ, inducedMetricNat_inner G hk hnorm e]
    rfl
  have hcS : CompactSpace S := Φ.toHomeomorph.symm.compactSpace
  have hconnS : ConnectedSpace S :=
    Φ.toHomeomorph.symm.surjective.connectedSpace Φ.toHomeomorph.symm.continuous
  exact ⟨S, inferInstance, inferInstance, inferInstance, hcS, hconnS, Φ.toHomeomorph,
    Φ.contMDiff, Φ.symm.contMDiff, κ, hinner, hsecS,
    fun ⟨o⟩ => finiteSurface_sphere_or_flat_torus o hn2 κ hsecS⟩

end DifferentialGeometry.Geometry.Collapse
