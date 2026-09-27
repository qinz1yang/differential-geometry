import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.TerminalRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.IntrinsicDerivation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarGradient
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarLaplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.TerminalSlope

noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
private local instance : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)

theorem abs_deriv_scalar_le_of_curvature_jets
    (hS : IsSolutionOn S) {t B₀ B₂ : ℝ} (ht : t ∈ D.regular) (x : M)
    (hzero : curvDerivNormSq 0 (S.base.metric t) x ≤ B₀)
    (hsecond : curvDerivNormSq 2 (S.base.metric t) x ≤ B₂) :
    |deriv (fun s => S.scalar s x) t| ≤ (Module.finrank ℝ E : ℝ) ^ 6 * Real.sqrt B₂ + 2 * (Module.finrank ℝ E : ℝ) ^ 4 * B₀ := by
  by_cases hdim : Module.finrank ℝ E = 0
  · have hscalar : (fun s => S.scalar s x) = fun _ => (0 : ℝ) := by
      funext s
      exact metricScalarAt_eq_zero_of_finrank_eq_zero (S.base.metric s) hdim x
    simp only [hscalar, deriv_const, abs_zero, hdim, Nat.cast_zero,
      zero_pow (by decide : 6 ≠ 0), zero_pow (by decide : 4 ≠ 0), zero_mul, mul_zero, add_zero, le_refl]
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    have hd := (scalar_curvature_evolution S hS ⟨t, ht⟩ x).hasDerivAt (D.regular_mem_nhds ht)
    have hlap := abs_laplacian_scalar_le_second_curvature S t x
    have hric := ricTower_normSq_le S t 0 x
    have hric0 := normSq0S_nonneg (I := I) (S.family.metric t) x 2 (S.ricci t x)
    have htwo : Real.sqrt (nablaKRm04NormSqIntrinsic S 2 t x) ≤ Real.sqrt B₂ := by
      rw [← curvNormSq_eq]
      exact Real.sqrt_le_sqrt hsecond
    have hzero' : nablaKRm04NormSqIntrinsic S 0 t x ≤ B₀ := by
      rw [← curvNormSq_eq]
      exact hzero
    have hric' : normSq0S (S.family.metric t) x 2 (S.ricci t x) ≤ (Module.finrank ℝ E : ℝ) ^ 4 * B₀ :=
      hric.trans (mul_le_mul_of_nonneg_left hzero' (by positivity))
    rw [hd.deriv]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hric0)]
    have hla := hlap.trans (mul_le_mul_of_nonneg_left htwo (by positivity : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 6))
    linarith

omit [I.Boundaryless] in
theorem abs_scalarDifferential_le_of_curvature_jet
    {t B : ℝ} (x : M) (hfirst : curvDerivNormSq 1 (S.base.metric t) x ≤ B)
    (v : TangentSpace I x) :
    |scalarDifferential S t x v| ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B *
      Real.sqrt ((S.base.metric t).inner x v v) := by
  have hg := scalar_gradient_abs_le_nabla_rm (S.base.metric t) x v
  rw [DifferentialGeometry.Geometry.Operator.inner_gradientFun] at hg
  change |scalarDifferential S t x v| ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
    Real.sqrt (nablaKRm04NormSqIntrinsic S 1 t x) * Real.sqrt ((S.base.metric t).inner x v v) at hg
  have hroot : Real.sqrt (nablaKRm04NormSqIntrinsic S 1 t x) ≤ Real.sqrt B := by
    rw [← curvNormSq_eq]
    exact Real.sqrt_le_sqrt hfirst
  exact hg.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hroot (by positivity)) (Real.sqrt_nonneg _))

theorem abs_derivWithin_scalar_le_on_Ioc_of_curvature_jets
    (hS : IsSolutionOn S) {a b B : ℝ} (hB : 0 ≤ B)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (U : Set M)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ U, curvDerivNormSq 0 (S.base.metric t) x ≤ B)
    (hsecond : ∀ t ∈ Icc a b, ∀ x ∈ U, curvDerivNormSq 2 (S.base.metric t) x ≤ B) :
    ∀ t ∈ Ioc a b, ∀ x ∈ U,
      |derivWithin (fun s => S.scalar s x) (Iic t) t| ≤
        (Module.finrank ℝ E : ℝ) ^ 6 * Real.sqrt B + 2 * (Module.finrank ℝ E : ℝ) ^ 4 * B := by
  intro t ht x hx
  apply abs_derivWithin_Iic_le_of_interior_bound (fun s => S.scalar s x)
    (a := a) (b := t) ht.1 (by positivity)
  · intro s hs
    exact (hS.scalarTime hs (fun v hv => hcarrier ⟨hv.1, hv.2.trans ht.2⟩) x).continuousWithinAt
  · intro s hs
    exact (hS.scalarTime (D.regular_subset (hregular ⟨hs.1, hs.2.trans_le ht.2⟩))
      (fun _ h => h) x).differentiableAt (D.regular_mem_nhds (hregular ⟨hs.1, hs.2.trans_le ht.2⟩))
  · intro s hs
    exact abs_deriv_scalar_le_of_curvature_jets S hS (hregular ⟨hs.1, hs.2.trans_le ht.2⟩) x
      (hzero s ⟨hs.1.le, hs.2.le.trans ht.2⟩ x hx)
      (hsecond s ⟨hs.1.le, hs.2.le.trans ht.2⟩ x hx)

theorem exists_relative_scalar_derivative_bounds_of_curvature_jets
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : RealTimeInterval)
      (S : SolutionOn (I := I) (M := M) D), IsSolutionOn S →
      ∀ (a b : ℝ), Icc a b ⊆ D.carrier → Ioo a b ⊆ D.regular →
      ∀ U : Set M,
      (∀ j ≤ 2, ∀ t ∈ Icc a b, ∀ x ∈ U, curvDerivNormSq j (S.base.metric t) x ≤ B) →
      (∀ t ∈ Icc a b, ∀ x ∈ U, 1 / 2 ≤ S.scalar t x → ∀ v : TangentSpace I x,
        |scalarDifferential S t x v| ≤ C * S.scalar t x * Real.sqrt (S.scalar t x) *
          Real.sqrt ((S.base.metric t).inner x v v)) ∧
      (∀ t ∈ Ioc a b, ∀ x ∈ U, 1 / 2 ≤ S.scalar t x →
        |derivWithin (fun s => S.scalar s x) (Iic t) t| ≤ C * S.scalar t x ^ 2) := by
  let A := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B
  let T := (Module.finrank ℝ E : ℝ) ^ 6 * Real.sqrt B + 2 * (Module.finrank ℝ E : ℝ) ^ 4 * B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let C := max (4 * A) (4 * T) + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_left (4*A) (4*T)]
  have hCA : 4 * A ≤ C := by dsimp [C]; linarith [le_max_left (4*A) (4*T)]
  have hCT : 4 * T ≤ C := by dsimp [C]; linarith [le_max_right (4*A) (4*T)]
  refine ⟨C, hC, ?_⟩
  intro D S hS a b hcarrier hregular U hjets
  constructor
  · intro t ht x hx hR v
    have hroot : 1 / 2 ≤ Real.sqrt (S.scalar t x) := by
      have hs := Real.sq_sqrt (by linarith : 0 ≤ S.scalar t x)
      nlinarith [Real.sqrt_nonneg (S.scalar t x)]
    have hprod : 1 / 4 ≤ S.scalar t x * Real.sqrt (S.scalar t x) := by nlinarith
    have hc : A ≤ C * S.scalar t x * Real.sqrt (S.scalar t x) := by
      nlinarith [mul_le_mul_of_nonneg_left hprod hC.le]
    exact (abs_scalarDifferential_le_of_curvature_jet S x
      (hjets 1 (by norm_num) t ht x hx) v).trans
        (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))
  · intro t ht x hx hR
    have hb := abs_derivWithin_scalar_le_on_Ioc_of_curvature_jets S hS hB hcarrier hregular U
      (hjets 0 (by norm_num)) (hjets 2 le_rfl) t ht x hx
    have hsq : 1 / 4 ≤ S.scalar t x ^ 2 := by nlinarith
    exact hb.trans (by dsimp [T] at hCT ⊢; nlinarith [mul_le_mul_of_nonneg_left hsq hC.le])

end DifferentialGeometry.PDE.RicciFlow

end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem abs_derivWithin_scalar_le_of_terminal_curvature_jets
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b B : ℝ} (hab : a < b) (hB : 0 ≤ B)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular) (x : M)
    (hzero : curvDerivNormSq 0 (S.base.metric b) x ≤ B)
    (hsecond : curvDerivNormSq 2 (S.base.metric b) x ≤ B) :
    |derivWithin (fun t => S.scalar t x) (Iic b) b| ≤
      (Module.finrank ℝ E : ℝ) ^ 6 * Real.sqrt (B + 1) +
        2 * (Module.finrank ℝ E : ℝ) ^ 4 * (B + 1) := by
  have hnear (k : ℕ) (hk : curvDerivNormSq k (S.base.metric b) x ≤ B) :
      ∀ᶠ t in 𝓝[≤] b, curvDerivNormSq k (S.base.metric t) x < B + 1 := by
    have hc := solution_nablaKRm04NormSqIntrinsic_continuousWithinAt_terminal
      S hS hab hcarrier hregular k x
    have hh : nablaKRm04NormSqIntrinsic S k b x < B + 1 := by
      rw [← curvNormSq_eq]
      linarith
    simpa only [← curvNormSq_eq] using hc.eventually (Iio_mem_nhds hh)
  obtain ⟨c, hcb, hc⟩ := (mem_nhdsLE_iff_exists_Ioc_subset).mp ((hnear 0 hzero).and (hnear 2 hsecond))
  have hmax : max a c < b := max_lt hab hcb
  apply Perelman.CanonicalNeighborhood.abs_derivWithin_Iic_le_of_interior_bound
    (fun t => S.scalar t x) hmax (by positivity)
  · intro t ht
    exact (hS.scalarTime ht
      (fun _ hv => hcarrier ⟨(le_max_left a c).trans hv.1, hv.2⟩) x).continuousWithinAt
  · intro t ht
    exact (hS.scalarTime (D.regular_subset (hregular ⟨(le_max_left a c).trans_lt ht.1, ht.2⟩))
      (fun _ h => h) x).differentiableAt
        (D.regular_mem_nhds (hregular ⟨(le_max_left a c).trans_lt ht.1, ht.2⟩))
  · intro t ht
    have hj := hc ⟨(le_max_right a c).trans_lt ht.1, ht.2.le⟩
    exact abs_deriv_scalar_le_of_curvature_jets S hS
      (hregular ⟨(le_max_left a c).trans_lt ht.1, ht.2⟩) x hj.1.le hj.2.le

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_relative_scalar_derivative_bounds_of_terminal_curvature_jets
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M],
      ∀ (D : RealTimeInterval) (S : SolutionOn (I := I) (M := M) D), IsSolutionOn S →
      ∀ (a b : ℝ), a < b → Icc a b ⊆ D.carrier → Ioo a b ⊆ D.regular →
      ∀ x : M, (∀ j ≤ 2, curvDerivNormSq j (S.base.metric b) x ≤ B) →
      1 / 2 ≤ S.scalar b x →
      (∀ v : TangentSpace I x,
        |Perelman.CanonicalNeighborhood.scalarDifferential S b x v| ≤ C * S.scalar b x * Real.sqrt (S.scalar b x) *
          Real.sqrt ((S.base.metric b).inner x v v)) ∧
      (|derivWithin (fun s => S.scalar s x) (Iic b) b| ≤ C * S.scalar b x ^ 2) := by
  let A := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B
  let T := (Module.finrank ℝ E : ℝ) ^ 6 * Real.sqrt (B + 1) + 2 * (Module.finrank ℝ E : ℝ) ^ 4 * (B + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let C := max (4 * A) (4 * T) + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_left (4*A) (4*T)]
  have hCA : 4 * A ≤ C := by dsimp [C]; linarith [le_max_left (4*A) (4*T)]
  have hCT : 4 * T ≤ C := by dsimp [C]; linarith [le_max_right (4*A) (4*T)]
  refine ⟨C, hC, ?_⟩
  intro H M _ I _ _ _ _ _ _ D S hS a b hab hcarrier hregular x hjets hR
  constructor
  · intro v
    have hroot : 1 / 2 ≤ Real.sqrt (S.scalar b x) := by
      have hs := Real.sq_sqrt (by linarith : 0 ≤ S.scalar b x)
      nlinarith [Real.sqrt_nonneg (S.scalar b x)]
    have hprod : 1 / 4 ≤ S.scalar b x * Real.sqrt (S.scalar b x) := by nlinarith
    have hc : A ≤ C * S.scalar b x * Real.sqrt (S.scalar b x) := by
      nlinarith [mul_le_mul_of_nonneg_left hprod hC.le]
    exact (abs_scalarDifferential_le_of_curvature_jet S x
      (hjets 1 (by norm_num)) v).trans
        (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))
  · have hb := abs_derivWithin_scalar_le_of_terminal_curvature_jets S hS hab hB hcarrier hregular x
      (hjets 0 (by norm_num)) (hjets 2 le_rfl)
    have hsq : 1 / 4 ≤ S.scalar b x ^ 2 := by nlinarith
    exact hb.trans (by dsimp [T] at hCT ⊢; nlinarith [mul_le_mul_of_nonneg_left hsq hC.le])

end DifferentialGeometry.PDE.RicciFlow

end
end
