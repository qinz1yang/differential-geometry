import DifferentialGeometry.Analysis.ODE.QuadraticBackwardBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.sigmaCompact PointedFlowData.t2

theorem eventually_scalar_le_on_backward_interval_of_tendstoUniformlyOn
    {ι X : Type*} {l : Filter ι} {K : Set X}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : ι → PointedFlowData.{u, uE, uH} (I := I) D)
    (f : ∀ i, X → (F i).M) {q : ι → ℝ} {σ b : ℝ} {C : ℝ≥0}
    (hC : 0 < C)
    (hslab : Icc (b - (6 * C * max σ 1)⁻¹) b ⊆ D.carrier)
    (hconv : TendstoUniformlyOn (fun i x => (F i).S.scalar b (f i x)) (fun _ => σ) l K)
    (hq : ∀ᶠ i in l, q i ≤ max σ 1)
    (hb : ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Ioo (b - (6 * C * max σ 1)⁻¹) b,
      q i < (F i).S.scalar t (f i x) →
      |derivWithin (fun s => (F i).S.scalar s (f i x)) (Iic t) t| ≤
        C * (F i).S.scalar t (f i x) ^ 2) :
    0 < (6 * C * max σ 1)⁻¹ ∧
      ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Icc (b - (6 * C * max σ 1)⁻¹) b,
        (F i).S.scalar t (f i x) ≤ 2 * max σ 1 := by
  apply DifferentialGeometry.Analysis.ODE.eventually_le_two_mul_on_backward_interval_of_tendstoUniformlyOn
    (r' := fun i t x => derivWithin (fun s => (F i).S.scalar s (f i x)) (Iic t) t)
    hC hconv hq _ _ hb
  · exact Filter.Eventually.of_forall fun i x hx => fun t ht =>
      ((F i).isSolution.scalarTime ht hslab (f i x)).continuousWithinAt
  · apply Filter.Eventually.of_forall
    intro i x hx t ht hqt
    have hderiv := ((F i).isSolution.scalarTime (K := Ioo (b - (6 * C * max σ 1)⁻¹) b)
      ht (Ioo_subset_Icc_self.trans hslab) (f i x)).differentiableAt (Ioo_mem_nhds ht.1 ht.2)
    have hwithin := hderiv.hasDerivAt.hasDerivWithinAt (s := Iic t)
    rw [hwithin.derivWithin (uniqueDiffWithinAt_Iic t)]
    exact hderiv.hasDerivAt

theorem eventually_riemannNorm_le_on_backward_interval_of_tendstoUniformlyOn_scalar
    {ι X : Type*} {l : Filter ι} {K : Set X}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : ι → PointedFlowData.{u, uE, uH} (I := I) D)
    (f : ∀ i, X → (F i).M) {q : ι → ℝ} {σ b : ℝ} {C : ℝ≥0}
    (hC : 0 < C) (hdim : Module.finrank ℝ E = 3)
    (hslab : Icc (b - (6 * C * max σ 1)⁻¹) b ⊆ D.carrier)
    (hconv : TendstoUniformlyOn (fun i x => (F i).S.scalar b (f i x)) (fun _ => σ) l K)
    (hq : ∀ᶠ i in l, q i ≤ max σ 1)
    (hb : ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Ioo (b - (6 * C * max σ 1)⁻¹) b,
      q i < (F i).S.scalar t (f i x) →
      |derivWithin (fun s => (F i).S.scalar s (f i x)) (Iic t) t| ≤
        C * (F i).S.scalar t (f i x) ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ᶠ i in l,
      PhiAlmostNonnegative (F i).S (Icc (b - (6 * C * max σ 1)⁻¹) b) Phi) :
    0 < (6 * C * max σ 1)⁻¹ ∧
      ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Icc (b - (6 * C * max σ 1)⁻¹) b,
        Real.sqrt ((F i).rmNormSq t (f i x)) ≤
          4 * Real.sqrt 3 * (max σ 1 / 2 + Phi (2 * max σ 1) + Phi 0) := by
  obtain ⟨heps, hscalar⟩ :=
    eventually_scalar_le_on_backward_interval_of_tendstoUniformlyOn F f hC hslab hconv hq hb
  refine ⟨heps, ?_⟩
  filter_upwards [hscalar, hpinch] with i hi hpi
  intro x hx t ht
  have hQ : 0 < max σ 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hbridge : RmNormBoundOn (F i).S (2 * Real.sqrt 3) :=
    fun t y basis horth _ ha =>
      sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le (F i).S t y basis horth ha
  have hs : (F i).S.scalar t (f i x) ≤ 4 * (max σ 1 / 2) := by
    have hh := hi x hx t ht
    linarith
  have hn := sqrt_rmNormSq_le_of_scalar_le (by positivity : 0 ≤ 2 * Real.sqrt 3)
    hbridge hPhi hpi hdim ht (f i x) (by positivity : 0 < max σ 1 / 2) hs
  have heq : 4 * (max σ 1 / 2) = 2 * max σ 1 := by ring
  rw [heq] at hn
  exact hn.trans_eq (by ring)

theorem eventually_riemannNorm_le_on_backward_interval_of_rescaled_pinching
    {ι X : Type*} {l : Filter ι} {K : Set X}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : ι → PointedFlowData.{u, uE, uH} (I := I) D)
    (f : ∀ i, X → (F i).M) {q scale : ι → ℝ} {σ b : ℝ} {C : ℝ≥0}
    (hC : 0 < C) (hdim : Module.finrank ℝ E = 3)
    (hslab : Icc (b - (6 * C * max σ 1)⁻¹) b ⊆ D.carrier)
    (hconv : TendstoUniformlyOn (fun i x => (F i).S.scalar b (f i x)) (fun _ => σ) l K)
    (hq : ∀ᶠ i in l, q i ≤ max σ 1)
    (hb : ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Ioo (b - (6 * C * max σ 1)⁻¹) b,
      q i < (F i).S.scalar t (f i x) →
      |derivWithin (fun s => (F i).S.scalar s (f i x)) (Iic t) t| ≤
        C * (F i).S.scalar t (f i x) ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hscale : ∀ᶠ i in l, 1 ≤ scale i)
    (hpinch : ∀ᶠ i in l,
      PhiAlmostNonnegative (F i).S (Icc (b - (6 * C * max σ 1)⁻¹) b)
        (rescalePinchingFunction (scale i) Phi)) :
    0 < (6 * C * max σ 1)⁻¹ ∧
      ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Icc (b - (6 * C * max σ 1)⁻¹) b,
        Real.sqrt ((F i).rmNormSq t (f i x)) ≤
          4 * Real.sqrt 3 * (max σ 1 / 2 + Phi (2 * max σ 1) + Phi 0) := by
  apply eventually_riemannNorm_le_on_backward_interval_of_tendstoUniformlyOn_scalar
    F f hC hdim hslab hconv hq hb hPhi
  filter_upwards [hscale, hpinch] with i his hip
  apply (phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt
    (F i).S _ Phi hdim).mpr
  have heigen := (phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt
    (F i).S _ (rescalePinchingFunction (scale i) Phi) hdim).mp hip
  intro t ht x
  exact (neg_le_neg (hPhi.rescale_le his ((F i).S.scalar t x))).trans (heigen t ht x)

theorem eventually_riemannNorm_le_on_backward_interval_of_rescaling_tendsto_atTop
    {ι X : Type*} {l : Filter ι} {K : Set X}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : ι → PointedFlowData.{u, uE, uH} (I := I) D)
    (f : ∀ i, X → (F i).M) {q scale : ι → ℝ} {σ b : ℝ} {C : ℝ≥0}
    (hσ : σ ≤ 1) (hdim : Module.finrank ℝ E = 3)
    (hslab : Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b ⊆ D.carrier)
    (hconv : TendstoUniformlyOn (fun i x => (F i).S.scalar b (f i x)) (fun _ => σ) l K)
    (hq : ∀ᶠ i in l, q i ≤ 1)
    (hb : ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Ioo (b - (12 * ((C : ℝ) + 1))⁻¹) b,
      q i < (F i).S.scalar t (f i x) →
      |derivWithin (fun s => (F i).S.scalar s (f i x)) (Iic t) t| ≤
        C * (F i).S.scalar t (f i x) ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hscale : Tendsto scale l atTop)
    (hpinch : ∀ᶠ i in l,
      PhiAlmostNonnegative (F i).S (Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b)
        (rescalePinchingFunction (scale i) Phi)) :
    0 < (12 * ((C : ℝ) + 1))⁻¹ ∧
      ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b,
        Real.sqrt ((F i).rmNormSq t (f i x)) ≤ 12 * Real.sqrt 3 := by
  have hden : 0 < 12 * ((C : ℝ) + 1) := by positivity
  refine ⟨inv_pos.mpr hden, ?_⟩
  have htime : 6 * (C : ℝ) * (12 * ((C : ℝ) + 1))⁻¹ * max (1 : ℝ) 1 ≤ 1 := by
    rw [max_self, mul_one, ← div_eq_mul_inv]
    apply (div_le_one hden).mpr
    linarith [C.coe_nonneg]
  have hscalar : ∀ᶠ i in l, ∀ x ∈ K,
      ∀ t ∈ Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b, (F i).S.scalar t (f i x) ≤ 2 := by
    have hr := DifferentialGeometry.Analysis.ODE.eventually_le_two_mul_of_tendstoUniformlyOn_of_quadratic_deriv_bound
      (r' := fun i t x => derivWithin (fun s => (F i).S.scalar s (f i x)) (Iic t) t)
      htime hconv (fun _ _ => hσ) (by simpa only [max_self] using hq) ?_ ?_ hb
    · simpa only [max_self, mul_one] using hr
    · exact Filter.Eventually.of_forall fun i x hx => fun t ht =>
        ((F i).isSolution.scalarTime ht hslab (f i x)).continuousWithinAt
    · apply Filter.Eventually.of_forall
      intro i x hx t ht hqt
      have hderiv := ((F i).isSolution.scalarTime
        (K := Ioo (b - (12 * ((C : ℝ) + 1))⁻¹) b)
        ht (Ioo_subset_Icc_self.trans hslab) (f i x)).differentiableAt (Ioo_mem_nhds ht.1 ht.2)
      have hwithin := hderiv.hasDerivAt.hasDerivWithinAt (s := Iic t)
      rw [hwithin.derivWithin (uniqueDiffWithinAt_Iic t)]
      exact hderiv.hasDerivAt
  obtain ⟨Q0, hQ0, hsmall⟩ := exists_forall_rescalePinchingFunction_le hPhi
    (B := 2) (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hscalar, hpinch, hscale.eventually (eventually_ge_atTop Q0)] with i hsi hpi hQi
  intro x hx t ht
  have hQipos : 0 < scale i := hQ0.trans_le hQi
  have hbridge : RmNormBoundOn (F i).S (2 * Real.sqrt 3) :=
    fun t y basis horth _ ha =>
      sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le (F i).S t y basis horth ha
  have hs : (F i).S.scalar t (f i x) ≤ 4 * (1 / 2 : ℝ) := by
    have hh := hsi x hx t ht
    linarith
  have hn := sqrt_rmNormSq_le_of_scalar_le (by positivity : 0 ≤ 2 * Real.sqrt 3)
    hbridge (hPhi.rescale hQipos) hpi hdim ht (f i x) (by norm_num : 0 < (1 / 2 : ℝ)) hs
  have hzero := hsmall (scale i) hQi 0 (by constructor <;> norm_num)
  have htwo := hsmall (scale i) hQi 2 (by constructor <;> norm_num)
  norm_num only [show (4 : ℝ) * (1 / 2) = 2 by norm_num] at hn
  apply hn.trans
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

end DifferentialGeometry.CheegerGromovCompactness
