import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureBound

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem scalar_le_two_mul_initial_of_time_sub_le
    {q A : ℝ} {C : ℝ≥0} (hA : 0 < A) (hqA : q ≤ A)
    (x : P.Carrier)
    (hbound : ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (hinit : G.flow.scalar a x ≤ A) {t : ℝ} (ht : t ∈ Ico a s)
    (htime : 2 * C * A * (t - a) ≤ 1) : G.flow.scalar t x ≤ 2 * A := by
  have hlip := G.lipschitzOnWith_inv_max_scalar_at hA x
    (fun r hr hAr => hbound r hr (hqA.trans_lt hAr))
  have hh := hlip.dist_le_mul t ht a ⟨le_rfl,G.lt⟩
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1), max_eq_left hinit] at hh
  have hhalf : C * (t - a) ≤ (2 * A)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have htwo : A⁻¹ = 2 * (2 * A)⁻¹ := by field_simp
  have hlow : (2 * A)⁻¹ ≤ (max A (G.flow.scalar t x))⁻¹ := by
    have hab := (abs_le.mp hh).1
    rw [htwo] at hab
    linarith
  exact (le_max_right _ _).trans
    ((inv_le_inv₀ (by positivity) (hA.trans_le (le_max_left _ _))).mp hlow)

theorem TerminalLimitMetric.scalar_le_two_mul_initial_of_time_sub_le
    (L : G.TerminalLimitMetric) {q A : ℝ} {C : ℝ≥0} (hA : 0 < A) (hqA : q ≤ A)
    (x : G.terminalRegularOpen)
    (hbound : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2)
    (hinit : G.flow.scalar a x.val ≤ A)
    (htime : 2 * C * A * (s - a) ≤ 1) : metricScalarAt L.metric x ≤ 2 * A := by
  apply le_of_tendsto (L.tendsto_metricScalarAt x)
  filter_upwards [Ioo_mem_nhdsLT G.lt] with t ht
  apply G.scalar_le_two_mul_initial_of_time_sub_le hA hqA x.val hbound hinit ⟨ht.1.le,ht.2⟩
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le a) (by positivity)).trans htime


theorem curvature_bound_of_initial_scalar_bound
    {q A a₀ : ℝ} {C : ℝ≥0} (hA : 0 < A) (hqA : q ≤ A) (ha₀ : 0 < a₀)
    (K : Set P.Carrier)
    (hbound : ∀ x ∈ K, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (hinit : ∀ x ∈ K, G.flow.scalar a x ≤ A)
    (hpinch : ∀ t ∈ Ico a s, ∀ x ∈ K,
      InFixedHamiltonIveyRegion (G.flow.base.metric t) a₀ x)
    {b : ℝ} (hbs : b < s)
    (htime : 2 * C * A * (b - a) ≤ 1) :
    ∀ t ∈ Icc a b, ∀ x ∈ K,
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S (G.flow.base.metric t) x 4
        (metricRm04 (G.flow.base.metric t) x)) ≤
        2 * Real.sqrt 3 * (A + max (2 * A) (Real.exp 4 / a₀)) := by
  intro t ht x hx
  have htc : t ∈ Ico a s := ⟨ht.1, ht.2.trans_lt hbs⟩
  have hscalar : G.flow.scalar t x ≤ 2 * A :=
    G.scalar_le_two_mul_initial_of_time_sub_le hA hqA x (hbound x hx) (hinit x hx) htc
      ((mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) (by positivity)).trans htime)
  have hr := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion (G.flow.base.metric t) x ha₀ le_rfl
    (hpinch t htc x hx) hscalar
  have hA2 : max (2 * A) 0 = 2 * A := max_eq_left (by positivity)
  have heq : (2 * A) / 2 = A := by ring
  rw [hA2, heq] at hr
  exact hr

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

theorem exists_uniform_curvature_bound_of_normalized_initial_scalar_bound
    (B P : ℝ) (hB : 0 < B) (hP : 0 < P) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {X : OrientedThreeStage.{u}} {a s : ℝ} (G : X.IncomingSlab a s)
        (Ω : Set X.Carrier) (Q q τ : ℝ) (C : ℝ≥0) (h : ℝ → ℝ),
        0 < Q → q ≤ B * Q →
        (∀ x ∈ Ω, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
          |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
        (∀ x ∈ Ω, G.flow.scalar a x ≤ B * Q) →
        (∀ t ∈ Ico a s, ∀ x ∈ Ω,
          InFixedHamiltonIveyRegion (G.flow.base.metric t) (h t) x) →
        (∀ t ∈ Ico a s, P ≤ h t * Q) →
        2 * C * B * τ ≤ 1 →
        ∀ b : ℝ, b < s → b - a ≤ τ / Q →
          ∀ t ∈ Icc a b, ∀ x ∈ Ω,
            Real.sqrt (normSq0S (G.flow.base.metric t) x 4
              (metricRm04 (G.flow.base.metric t) x)) ≤ K * Q := by
  let K := 2 * Real.sqrt 3 * (B + max (2 * B) (Real.exp 4 / P))
  have hK : 0 < K := by
    have hm : 0 < max (2 * B) (Real.exp 4 / P) :=
      (div_pos (Real.exp_pos _) hP).trans_le (le_max_right _ _)
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro X a s G Ω Q q τ C h hQ hq hbound hinit hpinch hparameter hbudget b hbs htime t ht x hx
  have htc : t ∈ Ico a s := ⟨ht.1, ht.2.trans_lt hbs⟩
  have htime' : 2 * C * (B * Q) * (t - a) ≤ 1 := by
    have hta : t - a ≤ τ / Q := (sub_le_sub_right ht.2 a).trans htime
    have hmul := mul_le_mul_of_nonneg_left hta
      (show 0 ≤ 2 * (C : ℝ) * (B * Q) by positivity)
    have he : 2 * (C : ℝ) * (B * Q) * (τ / Q) = 2 * C * B * τ := by
      field_simp
    exact (hmul.trans_eq he).trans hbudget
  have hscalar := G.scalar_le_two_mul_initial_of_time_sub_le (mul_pos hB hQ) hq x
    (hbound x hx) (hinit x hx) htc htime'
  have hr := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion (G.flow.base.metric t) x
    (div_pos hP hQ) ((div_le_iff₀ hQ).mpr (hparameter t htc))
    (hpinch t htc x hx) hscalar
  have hm : max (2 * (B * Q)) 0 = 2 * (B * Q) := max_eq_left (by positivity)
  have he : Real.exp 4 / (P / Q) = (Real.exp 4 / P) * Q := by field_simp
  rw [hm, he, show 2 * (B * Q) = (2 * B) * Q by ring,
    ← max_mul_of_nonneg _ _ hQ.le] at hr
  change Real.sqrt (normSq0S (G.flow.base.metric t) x 4
    (metricRm04At (G.flow.base.metric t) x)) ≤ K * Q
  exact hr.trans_eq (by dsimp only [K]; ring)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem exists_curvature_bound_of_initial_scalar_bound
    {q A : ℝ} {C : ℝ≥0} (hA : 0 < A) (hqA : q ≤ A)
    (K : Set P.Carrier)
    (hbound : ∀ x ∈ K, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (hinit : ∀ x ∈ K, G.flow.scalar a x ≤ A)
    (htime : 2 * C * A * (s - a) ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ∀ t ∈ Ico a s, G.riemannNorm t x ≤ B := by
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  obtain ⟨C3, hC3, hbridge⟩ := exists_rmNormLeOfCurvatureOperatorBounds.{u} ThreeModel
  refine ⟨2 * C3 * (A + Phi (4 * A) + Phi 0), ?_, ?_⟩
  · have := hPhi.pos (4 * A)
    have := hPhi.pos 0
    positivity
  · intro x hx t ht
    have hscalar := G.scalar_le_two_mul_initial_of_time_sub_le hA hqA x
      (hbound x hx) (hinit x hx) ht
      ((mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le a) (by positivity)).trans htime)
    exact sqrt_rmNormSq_le_of_scalar_le hC3 (hbridge P.Carrier G.flow)
      hPhi hpinch (by simp [ThreeSpace]) ht x hA (by linarith)

theorem subset_terminalRegularRegion_of_initial_scalar_bound
    {q A : ℝ} {C : ℝ≥0} (hA : 0 < A) (hqA : q ≤ A)
    {U : Set P.Carrier} (hU : IsOpen U)
    (hbound : ∀ x ∈ U, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (hinit : ∀ x ∈ U, G.flow.scalar a x ≤ A)
    (htime : 2 * C * A * (s - a) ≤ 1) :
    U ⊆ G.terminalRegularRegion := by
  obtain ⟨B, hB, hcurv⟩ :=
    G.exists_curvature_bound_of_initial_scalar_bound hA hqA U hbound hinit htime
  intro x hx
  exact ⟨U, hU, hx, a, ⟨le_rfl, G.lt⟩, B, hB, hcurv⟩

theorem mem_terminalRegularRegion_of_initial_scalar_bound
    {q A : ℝ} {C : ℝ≥0} (hA : 0 < A) (hqA : q ≤ A)
    {U : Set P.Carrier} (hU : IsOpen U)
    (hbound : ∀ y ∈ U, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    {x : P.Carrier} (hx : x ∈ U) (hinit : G.flow.scalar a x ≤ A)
    (htime : 4 * C * A * (s - a) ≤ 1) :
    x ∈ G.terminalRegularRegion := by
  let V : Set P.Carrier := U ∩ {y | G.flow.scalar a y < 2 * A}
  have hV : IsOpen V :=
    hU.inter (isOpen_lt (scalarSmoothOfSolution G.flow a).continuous continuous_const)
  apply G.subset_terminalRegularRegion_of_initial_scalar_bound
    (A := 2 * A) (by positivity) (by linarith : q ≤ 2 * A) hV
    (fun y hy => hbound y hy.1) (fun y hy => hy.2.le)
    (by nlinarith) ⟨hx, by change G.flow.scalar a x < 2 * A; linarith⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem curvature_bound_of_initial_scalar_bound_of_initial_fixedHamiltonIveyRegion
    {q A a₀ : ℝ} {C : ℝ≥0} (hA : 0 < A) (hqA : q ≤ A) (ha₀ : 0 < a₀)
    (K : Set P.Carrier)
    (hbound : ∀ x ∈ K, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (hinit : ∀ x ∈ K, G.flow.scalar a x ≤ A)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (G.flow.base.metric a) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ G.flow.scalar a x)
    (htime : 2 * C * A * (s - a) ≤ 1) :
    ∀ t ∈ Ico a s, ∀ x ∈ K, G.riemannNorm t x ≤
      2 * Real.sqrt 3 * (A + max (2 * A) (Real.exp 4 / a₀)) := by
  have hpinch := G.fixedHamiltonIveyRegion_and_scalar_lower ha₀ hfixed hlower
  intro t ht x hx
  have hscalar := G.scalar_le_two_mul_initial_of_time_sub_le hA hqA x
    (hbound x hx) (hinit x hx) ht
    ((mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le a) (by positivity)).trans htime)
  have hr := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion (G.flow.base.metric t) x ha₀
    (by linarith [ht.1] : a₀ ≤ a₀ + t - a) (hpinch t ht x).1 hscalar
  have hA2 : max (2 * A) 0 = 2 * A := max_eq_left (by positivity)
  have heq : (2 * A) / 2 = A := by ring
  rw [hA2, heq] at hr
  exact hr

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
end

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem exists_curvature_bound_of_scalar_bound_at_time
    {q A τ : ℝ} {C : ℝ≥0} (hA : 0 < A) (hqA : q ≤ A)
    (K : Set P.Carrier)
    (hbound : ∀ x ∈ K, ∀ t ∈ Ioo τ s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (hτ : τ ∈ Ico a s) (hscalar : ∀ x ∈ K, G.flow.scalar τ x ≤ A)
    (htime : 2 * C * A * (s - τ) ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ∀ t ∈ Ico τ s, G.riemannNorm t x ≤ B := by
  let J : P.IncomingSlab τ s :=
    { lt := hτ.2
      flow := G.flow.timeRestrict _
      equation := isSolutionOn_timeRestrict G.equation
        (fun _ ht => ⟨hτ.1.trans ht.1, ht.2⟩)
        (fun _ ht => ⟨hτ.1.trans_lt ht.1, ht.2⟩)
      smoothUpTo := by
        intro x t ht
        obtain ⟨U, hU, hx, hsub, V, hV, htV, F, hF, heq⟩ :=
          G.smoothUpTo x t ⟨hτ.1.trans ht.1, ht.2⟩
        exact ⟨U, hU, hx, hsub, V, hV, htV, F, hF,
          fun v hv y hy i j => heq v ⟨hv.1, hτ.1.trans hv.2.1, hv.2.2⟩ y hy i j⟩ }
  exact J.exists_curvature_bound_of_initial_scalar_bound hA hqA K hbound hscalar htime

theorem subset_terminalRegularRegion_of_scalar_bound_at_time
    {q A τ : ℝ} {C : ℝ≥0} (hA : 0 < A) (hqA : q ≤ A)
    {U : Set P.Carrier} (hU : IsOpen U)
    (hbound : ∀ x ∈ U, ∀ t ∈ Ioo τ s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (hτ : τ ∈ Ico a s) (hscalar : ∀ x ∈ U, G.flow.scalar τ x ≤ A)
    (htime : 2 * C * A * (s - τ) ≤ 1) :
    U ⊆ G.terminalRegularRegion := by
  obtain ⟨B, hB, hcurv⟩ :=
    G.exists_curvature_bound_of_scalar_bound_at_time hA hqA U hbound hτ hscalar htime
  intro x hx
  exact ⟨U, hU, hx, τ, hτ, B, hB, hcurv⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
end

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
universe u

theorem TerminalLimitMetric.riemannNorm_extendedMetric_le_of_scalar_bound_at_time
    {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    {q Q a₀ τ : ℝ} {C : ℝ≥0} (hQ : 0 < Q) (hqQ : q ≤ Q) (ha₀ : 0 < a₀)
    (hτ : τ ∈ Ico a s)
    (hbound : ∀ t ∈ Ioo τ s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2)
    (hscalar : G.flow.scalar τ x.val ≤ Q)
    (hpinch : ∀ t ∈ Ico τ s,
      InFixedHamiltonIveyRegion (G.flow.base.metric t) a₀ x.val)
    (htime : 2 * C * (s - τ) * Q ≤ 1) :
    ∀ t ∈ Icc τ s,
      Real.sqrt (normSq0S (L.extendedMetric t) x 4
        (metricRm04At (L.extendedMetric t) x)) ≤
        2 * Real.sqrt 3 * (Q + max (2 * Q) (Real.exp 4 / a₀)) := by
  let J : P.IncomingSlab τ s :=
    { lt := hτ.2
      flow := G.flow.timeRestrict _
      equation := isSolutionOn_timeRestrict G.equation
        (fun _ ht => ⟨hτ.1.trans ht.1, ht.2⟩)
        (fun _ ht => ⟨hτ.1.trans_lt ht.1, ht.2⟩)
      smoothUpTo := by
        intro y t ht
        obtain ⟨U, hU, hy, hsub, V, hV, htV, F, hF, heq⟩ :=
          G.smoothUpTo y t ⟨hτ.1.trans ht.1, ht.2⟩
        exact ⟨U, hU, hy, hsub, V, hV, htV, F, hF,
          fun v hv z hz i j => heq v ⟨hv.1, hτ.1.trans hv.2.1, hv.2.2⟩ z hz i j⟩ }
  have hpast (t : ℝ) (ht : t ∈ Ico τ s) :
      G.riemannNorm t x.val ≤
        2 * Real.sqrt 3 * (Q + max (2 * Q) (Real.exp 4 / a₀)) := by
    have htime' : 2 * C * Q * (t - τ) ≤ 1 := by
      have hb := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le τ)
          (by positivity : 0 ≤ 2 * (C : ℝ))) hQ.le
      nlinarith [hb]
    have hs : G.flow.scalar t x.val ≤ 2 * Q :=
      J.scalar_le_two_mul_initial_of_time_sub_le hQ hqQ x.val hbound hscalar ht htime'
    have hr := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion (G.flow.base.metric t) x.val
      ha₀ le_rfl (hpinch t ht) hs
    rw [max_eq_left (by positivity : 0 ≤ 2 * Q), show 2 * Q / 2 = Q by ring] at hr
    exact hr
  intro t ht
  rcases lt_or_eq_of_le ht.2 with hts | rfl
  · rw [L.extendedMetric_before hts, rmNormSq_restrictOpen]
    exact hpast t ⟨ht.1, hts⟩
  · rw [L.extendedMetric_terminal]
    apply le_of_tendsto (L.tendsto_riemannNorm x)
    filter_upwards [Ioo_mem_nhdsLT hτ.2] with t ht
    exact hpast t ⟨ht.1.le, ht.2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
end
