import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Linearity
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.ConnectionDifference
import DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.MetricDerivative

set_option autoImplicit false
noncomputable section
open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Geometry.Connection

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private def ricciVariationContraction {y : M}
    (NRy : Tensor0SSpace (𝕜 := ℝ) (I := I) 3 y)
    (u w v : TangentSpace I y) : ℝ :=
  -NRy (vec3 u w v) - NRy (vec3 w u v) + NRy (vec3 v u w)

private theorem ricciVariationContraction_trace_eq_zero
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx ℝ (TangentSpace I x)) (gInv : Idx → Idx → ℝ)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv) (v : TangentSpace I x) :
    ∑ i, ∑ j, gInv i j * ricciVariationContraction (I := I)
      (metricNablaRic (I := I) g x) (basis i) (basis j) v = 0 := by
  classical
  obtain ⟨nRm, hsecond, hsymm, hric, hscalar⟩ :=
    exists_levi_civita_bianchi_trace_identities (I := I) g basis gInv hinv
  have hinvSymm := hinv.symmetric (I := I) g x basis gInv
  have hc := contracted_bianchi_of_second (I := I) basis gInv nRm _ _
    (contractOfSecond (I := I) basis gInv nRm _ _ hsymm hric hscalar hinvSymm) hsecond v
  have hs := hscalar v
  change (∑ i, ∑ j, gInv i j * metricNablaRic (I := I) g x
      (vec3 (basis i) (basis j) v)) = _ at hc
  change _ = ∑ i, ∑ j, gInv i j * metricNablaRic (I := I) g x
      (vec3 v (basis i) (basis j)) at hs
  have hswap : (∑ i, ∑ j, gInv i j * metricNablaRic (I := I) g x
      (vec3 (basis j) (basis i) v)) = ∑ i, ∑ j, gInv i j * metricNablaRic (I := I) g x
      (vec3 (basis i) (basis j) v) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hinvSymm i j]
  simp only [ricciVariationContraction, mul_add, mul_sub, mul_neg,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hswap]
  linarith

theorem metricTracePair0SAt_connectionDifferenceOutput_leviCivitaVariation_eq_zero_of_ricci_deriv
    [BoundarylessManifold I M]
    (g : ℝ → SmoothRiemannianMetric I M) (c t : ℝ)
    (hderiv : ∀ y v w, HasDerivAt (fun s => (g s).inner y v w)
      (c * metricRicci (I := I) (g t) y (vec2 v w)) t)
    (hsmooth : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ y,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)) (t, y))
    (x : M) (α : Tensor0SSpace (I := I) 1 x) :
    metricTracePair0SAt (I := I) (g t)
      (connectionDifferenceOutput (I := I) (leviCivitaVariation g t x) α) = 0 := by
  classical
  let basis := Module.finBasis ℝ (TangentSpace I x)
  let B := basisInvMetric (I := I) (g t) x basis
  have hB := basisInvMetric_isInverse (I := I) (g t) x basis
  rw [metricTracePair0SAt_eq_sum_basis (g t) basis B hB]
  have hA (i j) : connectionDifferenceOutput (I := I)
      (leviCivitaVariation g t x) α (vec2 (basis i) (basis j)) =
        α (fun _ : Fin 1 => (leviCivitaVariation g t x (basis j) (basis i))) := by
    change Tensor0SSpace.eval (connectionDifferenceOutput (I := I)
      (leviCivitaVariation g t x) α) (vec2 (basis i) (basis j)) = _
    rw [connectionDifferenceOutput_apply]
    rfl
  simp only [hA]
  have hzero : ∑ i, ∑ j, B i j • leviCivitaVariation g t x (basis j) (basis i) = 0 := by
    apply metricFlatLinear_injective (g t) x
    ext v
    change (g t).inner x
      (∑ i, ∑ j, B i j • leviCivitaVariation g t x (basis j) (basis i)) v =
      (g t).inner x 0 v
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, map_zero, zero_apply]
    let h : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2 :=
      c • metricRicci (I := I) (g t)
    have he (i j) : (g t).inner x (leviCivitaVariation g t x (basis j) (basis i)) v =
        (-c / 2) * ricciVariationContraction (I := I)
          (metricNablaRic (I := I) (g t) x) (basis i) (basis j) v := by
      have hk := leviCivita_variation_koszul g h t hderiv hsmooth x
        (basis i) (basis j) v
      simp only [h, totalNabla0SFun_smul, Tensor0SSpace.smul_apply, smul_eq_mul] at hk
      have hslots (a b d : TangentSpace I x) : Fin.cons a (vec2 b d) = vec3 a b d := by
        funext k
        fin_cases k <;> rfl
      simp only [hslots] at hk
      unfold ricciVariationContraction
      change 2 * (g t).inner x (leviCivitaVariation g t x (basis j) (basis i)) v =
        c * metricNablaRic (I := I) (g t) x (vec3 (basis i) (basis j) v) +
        c * metricNablaRic (I := I) (g t) x (vec3 (basis j) (basis i) v) -
        c * metricNablaRic (I := I) (g t) x (vec3 v (basis i) (basis j)) at hk
      linarith
    simp only [he]
    have hc := ricciVariationContraction_trace_eq_zero (g t) basis B hB v
    calc
      _ = (-c / 2) * ∑ i, ∑ j, B i j * ricciVariationContraction (I := I)
          (metricNablaRic (I := I) (g t) x) (basis i) (basis j) v := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [hc, mul_zero]
  have hα := congrArg (cotangentToDual (I := I) α) hzero
  simpa only [map_sum, map_smul, smul_eq_mul, map_zero, cotangentToDual_apply] using hα

end DifferentialGeometry.Geometry.Connection

end
