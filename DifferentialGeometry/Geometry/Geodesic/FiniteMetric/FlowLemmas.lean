import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Homogeneity

/-!
# Small lemmas on the finite-order geodesic flow and normal charts

Domain shift of the flow (`mem_geodesicFlowDomain_geodesicFlow_iff`), quadratic homogeneity of a
metric (`inner_smul_self_smul`), existence of unit vectors (`exists_inner_self_eq_one`), and
injectivity of `τ ↦ exp_x (τ v)` on unit vectors inside a normal chart (`eq_of_expMap_smul_eq`).
Used by CM2 (segments are geodesics, Hopf–Rinow). Lane CM-H, 2026-10-04.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

variable [T2Space M] {g} in
/-- Restarting the flow at time `t` translates its domain by `-t`. -/
theorem mem_geodesicFlowDomain_geodesicFlow_iff (hr : 1 ≤ r) {p : TangentBundle I M}
    {t s : ℝ} (ht : (p, t) ∈ g.geodesicFlowDomain) :
    (g.geodesicFlow p t, s) ∈ g.geodesicFlowDomain ↔ (p, t + s) ∈ g.geodesicFlowDomain :=
  TauCeti.mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff
    (g.contMDiff_geodesicSpray.of_le (by exact_mod_cast hr)) ht

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Quadratic homogeneity of the metric. -/
theorem inner_smul_self_smul (x : M) (a : ℝ) (v : TangentSpace I x) :
    g.inner x (a • v) (a • v) = a ^ 2 * g.inner x v v := by
  rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- A unit vector for `g` exists in every tangent space. -/
theorem exists_inner_self_eq_one [NeZero (Module.finrank ℝ E)] (x : M) :
    ∃ u : E, g.inner x u u = 1 := by
  have : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have hpos : 0 < g.inner x e e := g.pos x e he
  refine ⟨(Real.sqrt (g.inner x e e))⁻¹ • e,
    (inner_smul_self_smul g x (Real.sqrt (g.inner x e e))⁻¹ e).trans ?_⟩
  rw [inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

omit [I.Boundaryless] in
/-- Injectivity of the radial exponential map inside a normal chart. -/
theorem eq_of_expMap_smul_eq {x : M} {ρ : ℝ} (e : OpenPartialHomeomorph E M)
    (hsrc : e.source = {v : E | g.inner x v v < ρ ^ 2})
    (hexp : ∀ v ∈ e.source, (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
        e v = g.expMap (⟨x, v⟩ : TangentBundle I M))
    {τ : ℝ} (hτ : 0 < τ) (hτρ : τ < ρ) {w u : E} (hw : g.inner x w w = 1)
    (hu : g.inner x u u = 1)
    (heq : g.expMap (⟨x, τ • w⟩ : TangentBundle I M) = g.expMap (⟨x, τ • u⟩ : TangentBundle I M)) :
    w = u := by
  have hmem : ∀ v : E, g.inner x v v = 1 → τ • v ∈ e.source := by
    intro v hv
    rw [hsrc, mem_ofPred_eq]
    refine (inner_smul_self_smul g x τ v).trans_lt ?_
    rw [hv, mul_one]
    exact pow_lt_pow_left₀ hτρ hτ.le (by norm_num)
  have hinj := e.injOn (hmem w hw) (hmem u hu)
    (by rw [(hexp _ (hmem w hw)).2, (hexp _ (hmem u hu)).2, heq])
  exact smul_right_injective E hτ.ne' hinj

end Bundle.ContMDiffRiemannianMetric
