import DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteShortening
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem tendsto_equal_arm_distance_of_angle_pi {ι : Type*} {l : Filter ι}
    {d theta : ι → ℝ} {r : ℝ} (hr : 0 < r)
    (hd : ∀ᶠ i in l, 0 ≤ d i ∧ d i ≤ 2 * r)
    (htheta : Tendsto theta l (𝓝 Real.pi))
    (hcompare : ∀ᶠ i in l, theta i ≤ comparisonAngle r r (d i)) :
    Tendsto d l (𝓝 (2 * r)) := by
  have hangle : Tendsto (fun i => comparisonAngle r r (d i)) l (𝓝 Real.pi) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' htheta tendsto_const_nhds hcompare
      (Filter.Eventually.of_forall fun i => (comparisonAngle_mem_Icc r r (d i)).2)
  have hcos : Tendsto (fun i => Real.cos (comparisonAngle r r (d i))) l (𝓝 (-1)) := by
    simpa only [Real.cos_pi, Function.comp_def] using
      Real.continuous_cos.continuousAt.tendsto.comp hangle
  have hformula : ∀ᶠ i in l,
      d i ^ 2 = 2 * r ^ 2 * (1 - Real.cos (comparisonAngle r r (d i))) := by
    filter_upwards [hd] with i hi
    have hlower : |r - r| ≤ d i := by simpa only [sub_self, abs_zero] using hi.1
    have hupper : d i ≤ r + r := by linarith [hi.2]
    have hcosine := cos_comparisonAngle hr hr hlower hupper
    have hden : 2 * r * r ≠ 0 := by positivity
    have hid := (div_eq_iff hden).mp hcosine.symm
    nlinarith
  have hprod : Tendsto
      (fun i => 2 * r ^ 2 * (1 - Real.cos (comparisonAngle r r (d i))))
      l (𝓝 ((2 * r) ^ 2)) := by
    have hlimit := (tendsto_const_nhds :
      Tendsto (fun _ : ι => 2 * r ^ 2) l (𝓝 (2 * r ^ 2))).mul
        ((tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℝ)) l (𝓝 1)).sub hcos)
    have heq : 2 * r ^ 2 * (1 - (-1)) = (2 * r) ^ 2 := by ring
    simpa only [heq] using hlimit
  have hsq : Tendsto (fun i => d i ^ 2) l (𝓝 ((2 * r) ^ 2)) :=
    hprod.congr' (hformula.mono fun _ hi => hi.symm)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have heq : (fun i => Real.sqrt (d i ^ 2)) =ᶠ[l] d :=
    hd.mono fun i hi => Real.sqrt_sq hi.1
  have hrnonneg : 0 ≤ 2 * r := by positivity
  simpa only [Real.sqrt_sq hrnonneg] using hsqrt.congr' heq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [ConnectedSpace M]

theorem tendsto_rescaled_intrinsic_opposite_arms
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (o : ℕ → M) (u v : ∀ i, TangentSpace I (o i)) (a b lam : ℕ → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hlam : ∀ i, 0 < lam i)
    (hu : ∀ i, g.inner (o i) (u i) (u i) = 1)
    (hv : ∀ i, g.inner (o i) (v i) (v i) = 1)
    (hminA : ∀ i, (riemannianEDist I (o i)
      (intrinsicGeodesic (I := I) g hEnorm (o i) (u i) (a i))).toReal = a i)
    (hminB : ∀ i, (riemannianEDist I (o i)
      (intrinsicGeodesic (I := I) g hEnorm (o i) (v i) (b i))).toReal = b i)
    (hfarA : Tendsto (fun i => lam i * a i) atTop atTop)
    (hfarB : Tendsto (fun i => lam i * b i) atTop atTop)
    (hangle : Tendsto (fun i => comparisonAngle (a i) (b i)
      (riemannianEDist I
        (intrinsicGeodesic (I := I) g hEnorm (o i) (u i) (a i))
        (intrinsicGeodesic (I := I) g hEnorm (o i) (v i) (b i))).toReal)
      atTop (𝓝 Real.pi))
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun i => lam i * (riemannianEDist I
      (intrinsicGeodesic (I := I) g hEnorm (o i) (u i) (r / lam i))
      (intrinsicGeodesic (I := I) g hEnorm (o i) (v i) (r / lam i))).toReal)
      atTop (𝓝 (2 * r)) := by
  let d : ℕ → ℝ := fun i => lam i * (riemannianEDist I
    (intrinsicGeodesic (I := I) g hEnorm (o i) (u i) (r / lam i))
    (intrinsicGeodesic (I := I) g hEnorm (o i) (v i) (r / lam i))).toReal
  let theta : ℕ → ℝ := fun i => comparisonAngle (a i) (b i)
    (riemannianEDist I
      (intrinsicGeodesic (I := I) g hEnorm (o i) (u i) (a i))
      (intrinsicGeodesic (I := I) g hEnorm (o i) (v i) (b i))).toReal
  have hlarge : ∀ᶠ i in atTop, r / lam i ≤ a i ∧ r / lam i ≤ b i := by
    filter_upwards [hfarA (eventually_ge_atTop r), hfarB (eventually_ge_atTop r)]
      with i hiA hiB
    change r ≤ lam i * a i at hiA
    change r ≤ lam i * b i at hiB
    constructor
    · apply (div_le_iff₀ (hlam i)).2
      simpa only [mul_comm] using hiA
    · apply (div_le_iff₀ (hlam i)).2
      simpa only [mul_comm] using hiB
  have htri (x y z : M) : (riemannianEDist I x z).toReal ≤
      (riemannianEDist I x y).toReal + (riemannianEDist I y z).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨riemannianEDist_ne_top (I := I) x y,
        riemannianEDist_ne_top (I := I) y z⟩)
      (riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z))
    simpa only [ENNReal.toReal_add (riemannianEDist_ne_top (I := I) x y)
      (riemannianEDist_ne_top (I := I) y z)] using h
  have hbounds : ∀ᶠ i in atTop, 0 ≤ d i ∧ d i ≤ 2 * r := by
    filter_upwards [hlarge] with i hi
    have hrad : 0 < r / lam i := div_pos hr (hlam i)
    have hradA := unit_intrinsic_subsegment_dist (I := I) g hEnorm (o i) (u i)
      (hu i) (a i) (r / lam i) (ha i) hrad.le hi.1 (hminA i)
    have hradB := unit_intrinsic_subsegment_dist (I := I) g hEnorm (o i) (v i)
      (hv i) (b i) (r / lam i) (hb i) hrad.le hi.2 (hminB i)
    constructor
    · exact mul_nonneg (hlam i).le ENNReal.toReal_nonneg
    · have h := htri
        (intrinsicGeodesic (I := I) g hEnorm (o i) (u i) (r / lam i)) (o i)
        (intrinsicGeodesic (I := I) g hEnorm (o i) (v i) (r / lam i))
      rw [riemannianEDist_comm (I := I)
        (x := intrinsicGeodesic (I := I) g hEnorm (o i) (u i) (r / lam i))
        (y := o i), hradA, hradB] at h
      change lam i * _ ≤ 2 * r
      calc
        _ ≤ lam i * (r / lam i + r / lam i) :=
          mul_le_mul_of_nonneg_left h (hlam i).le
        _ = 2 * r := by
          field_simp [(hlam i).ne']
          ring
  have hcompare : ∀ᶠ i in atTop, theta i ≤ comparisonAngle r r (d i) := by
    filter_upwards [hlarge] with i hi
    have hrad : 0 < r / lam i := div_pos hr (hlam i)
    have h := complete_comparisonAngle_shortening (I := I) g hEnorm hsec
      (o i) (u i) (v i) (r / lam i) (a i) (r / lam i) (b i)
      hrad hi.1 hrad hi.2 (hu i) (hv i) (hminA i) (hminB i)
    have hscale := comparisonAngle_scale (r / lam i) (r / lam i)
      (riemannianEDist I
        (intrinsicGeodesic (I := I) g hEnorm (o i) (u i) (r / lam i))
        (intrinsicGeodesic (I := I) g hEnorm (o i) (v i) (r / lam i))).toReal
      (hlam i)
    have hcancel : lam i * (r / lam i) = r := by field_simp [(hlam i).ne']
    rw [hcancel] at hscale
    exact h.trans_eq hscale.symm
  exact tendsto_equal_arm_distance_of_angle_pi hr hbounds hangle hcompare

end DifferentialGeometry.Geometry.Comparison.Toponogov
