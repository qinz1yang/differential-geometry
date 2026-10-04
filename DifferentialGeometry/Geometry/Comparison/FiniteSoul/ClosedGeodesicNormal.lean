import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftJacobi
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalLineBundle
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.ChartMetric
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness

/-!
# The unit normal of a closed geodesic: periodicity and holonomy (S-TUBE, D3)

Package CM-S (finite soul), lane CMS-T. Let `γ t = π φ_t(p)` be a closed unit geodesic of period
`ℓ` (`φ_ℓ(p) = p`) of a `C^(r+1)` metric on a surface and `ν` a continuous unit normal along `γ`.

* `geodesicFlow_add_int_mul`: `φ_{t + nℓ}(p) = φ_t(p)` (complete flow).
* `exists_unitNormal_holonomy`: `ν (t + ℓ) = σ • ν t` for one sign `σ ∈ ℤˣ` (in a 2-dimensional
  `(T_{γ t} M, g)` the unit normals to `γ'(t)` are `± ν t`, and the sign `g(ν (t+ℓ), ν t)` is
  continuous, hence constant).
* `unitNormal_add_int_mul`: `ν (t + nℓ) = σ^n • ν t`.
* `transverseShift_add_int_mul`: the transverse shift `α(t, h) = exp_{γ t}(h ν t)` satisfies
  `α(t + nℓ, h) = α(t, σ^n h)`.
* `closedGeodesicTubeMap`: the map `NormalCover σ → M`, `(s, h) ↦ α(ℓ s, h)` (period normalised to
  `1`), invariant under the deck action (`closedGeodesicTubeMap_smul`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **Periodicity of a closed orbit of the complete geodesic flow.** -/
theorem geodesicFlow_add_int_mul
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (hdom : g.geodesicFlowDomain = univ) {p : TangentBundle I M} {ℓ : ℝ}
    (hper : g.geodesicFlow p ℓ = p) (t : ℝ) (n : ℤ) :
    g.geodesicFlow p (t + n * ℓ) = g.geodesicFlow p t := by
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  have h1 : ∀ s, g.geodesicFlow p (s + ℓ) = g.geodesicFlow p s := fun s => by
    rw [show s + ℓ = ℓ + s from add_comm s ℓ, g.geodesicFlow_add hr (hmem _) (hmem _), hper]
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have e : t + (((k : ℤ) + 1 : ℤ) : ℝ) * ℓ = (t + ((k : ℤ) : ℝ) * ℓ) + ℓ := by push_cast; ring
    rw [e, h1, ih]
  | pred k ih =>
    have e : t + ((-(k : ℤ) : ℤ) : ℝ) * ℓ = (t + ((-(k : ℤ) - 1 : ℤ) : ℝ) * ℓ) + ℓ := by
      push_cast; ring
    rw [← ih, e, h1]

/-- **The holonomy sign of a continuous unit normal** along a closed unit geodesic of a surface. -/
theorem exists_unitNormal_holonomy
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (hdom : g.geodesicFlowDomain = univ) (hdim : Module.finrank ℝ E = 2)
    (p : TangentBundle I M) {ℓ : ℝ} (hunit : g.inner p.proj p.snd p.snd = 1)
    (hper : g.geodesicFlow p ℓ = p) {ν : ℝ → E}
    (hν : Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)))
    (hνunit : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1)
    (hνperp : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0) :
    ∃ σ : ℤˣ, ∀ t, ν (t + ℓ) = ((σ : ℤ) : ℝ) • ν t := by
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  have hP : ∀ t, g.geodesicFlow p (t + ℓ) = g.geodesicFlow p t := fun t => by
    simpa using geodesicFlow_add_int_mul g hr hdom hper t 1
  have hspeed : ∀ t, g.inner (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd
      (g.geodesicFlow p t).snd = 1 := fun t => by
    rw [g.inner_geodesicFlow_eq hr p t (hmem _), hunit]
  set c : ℝ → ℝ := fun t => g.inner (g.geodesicFlow p t).proj (ν (t + ℓ)) (ν t) with hc
  -- the representation `ν (t + ℓ) = c t • ν t`
  have hrep : ∀ t, ν (t + ℓ) = c t • ν t := by
    intro t
    have hX : g.inner (g.geodesicFlow p t).proj (ν (t + ℓ)) (g.geodesicFlow p t).snd = 0 := by
      have h := hνperp (t + ℓ)
      rwa [hP t] at h
    exact eq_smul_of_orthonormal_dim_two hdim (B := (g.inner (g.geodesicFlow p t).proj :
      E →L[ℝ] E →L[ℝ] ℝ)) (fun u v => g.symm _ u v) (hspeed t) (hνunit t) (hνperp t) hX
  have hsq : ∀ t, c t * c t = 1 := by
    intro t
    have h := hνunit (t + ℓ)
    rw [hP t, hrep t] at h
    have h1 := hνunit t
    set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (g.geodesicFlow p t).proj with hB
    change B (c t • ν t) (c t • ν t) = 1 at h
    change B (ν t) (ν t) = 1 at h1
    simp only [map_smul, smul_apply, smul_eq_mul, h1, mul_one] at h
    exact h
  -- continuity of `c`
  have hshift : Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν (t + ℓ)⟩ :
      TangentBundle I M)) := by
    have h := hν.comp (continuous_id.add continuous_const : Continuous fun t : ℝ => t + ℓ)
    refine h.congr fun t => ?_
    change (⟨(g.geodesicFlow p (t + ℓ)).proj, ν (t + ℓ)⟩ : TangentBundle I M) = _
    rw [hP t]
  have hcc : Continuous c := continuousOn_univ.mp
    (DifferentialGeometry.Geometry.Collapse.continuousOn_finiteInner_of_bundle (g := g)
      (b := fun t => (g.geodesicFlow p t).proj) hshift.continuousOn hν.continuousOn)
  -- `c` is constant
  have hconst : ∀ t, c t = c 0 := by
    intro t
    by_contra hne
    have h0 : c 0 = 1 ∨ c 0 = -1 := by
      have := hsq 0
      rcases mul_self_eq_one_iff.mp this with h | h <;> simp [h]
    have ht : c t = 1 ∨ c t = -1 := by
      have := hsq t
      rcases mul_self_eq_one_iff.mp this with h | h <;> simp [h]
    have hmem0 : (0 : ℝ) ∈ uIcc (c 0) (c t) := by
      rcases h0 with h0 | h0 <;> rcases ht with ht | ht
      · exact absurd (ht.trans h0.symm) hne
      · rw [h0, ht, uIcc_of_ge (by norm_num)]; norm_num
      · rw [h0, ht, uIcc_of_le (by norm_num)]; norm_num
      · exact absurd (ht.trans h0.symm) hne
    obtain ⟨s, -, hs⟩ := intermediate_value_uIcc (a := 0) (b := t) hcc.continuousOn hmem0
    have := hsq s
    rw [hs, zero_mul] at this
    exact zero_ne_one this
  rcases mul_self_eq_one_iff.mp (hsq 0) with h0 | h0
  · refine ⟨1, fun t => ?_⟩
    rw [hrep t, hconst t, h0]
    simp
  · refine ⟨-1, fun t => ?_⟩
    rw [hrep t, hconst t, h0]
    simp

omit [FiniteDimensional ℝ E] in
/-- `ν (t + n ℓ) = σ^n • ν t`. -/
theorem unitNormal_add_int_mul {ν : ℝ → E} {ℓ : ℝ} {σ : ℤˣ}
    (hσ : ∀ t, ν (t + ℓ) = ((σ : ℤ) : ℝ) • ν t) (t : ℝ) (n : ℤ) :
    ν (t + n * ℓ) = holonomyPow σ n • ν t := by
  have hσσ : ((σ : ℤ) : ℝ) * ((σ : ℤ) : ℝ) = 1 := by
    have := holonomyPow_mul_self σ 1
    rwa [holonomyPow_one] at this
  have hinv : holonomyPow σ (-1) = ((σ : ℤ) : ℝ) := by
    unfold holonomyPow
    rcases Int.units_eq_one_or σ with hs | hs <;> rw [hs] <;> simp
  induction n using Int.induction_on with
  | zero => simp [holonomyPow_zero]
  | succ k ih =>
    have e : t + (((k : ℤ) + 1 : ℤ) : ℝ) * ℓ = (t + ((k : ℤ) : ℝ) * ℓ) + ℓ := by push_cast; ring
    rw [e, hσ, ih, smul_smul, holonomyPow_add, holonomyPow_one, mul_comm]
  | pred k ih =>
    have e : t + ((-(k : ℤ) : ℤ) : ℝ) * ℓ = (t + ((-(k : ℤ) - 1 : ℤ) : ℝ) * ℓ) + ℓ := by
      push_cast; ring
    have h := hσ (t + ((-(k : ℤ) - 1 : ℤ) : ℝ) * ℓ)
    rw [← e, ih] at h
    have h' : ν (t + ((-(k : ℤ) - 1 : ℤ) : ℝ) * ℓ) = ((σ : ℤ) : ℝ) • holonomyPow σ (-k) • ν t := by
      rw [h, smul_smul, hσσ, one_smul]
    rw [h', smul_smul, show (-(k : ℤ) - 1) = -k + -1 by ring, holonomyPow_add, hinv, mul_comm]

/-- **Quasi-periodicity of the transverse shift**: `α(t + n ℓ, h) = α(t, σ^n h)`. -/
theorem transverseShift_add_int_mul
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (hdom : g.geodesicFlowDomain = univ) {p : TangentBundle I M} {ℓ : ℝ}
    (hper : g.geodesicFlow p ℓ = p) {ν : ℝ → E} {σ : ℤˣ}
    (hσ : ∀ t, ν (t + ℓ) = ((σ : ℤ) : ℝ) • ν t) (t h : ℝ) (n : ℤ) :
    transverseShift g p ν (t + n * ℓ, h) = transverseShift g p ν (t, holonomyPow σ n * h) := by
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  unfold transverseShift
  simp only
  rw [geodesicFlow_add_int_mul g hr hdom hper t n, unitNormal_add_int_mul hσ t n]
  have h := g.geodesicFlow_smul_eq hr (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)
    (holonomyPow σ n) h (hmem _)
  have h2 := congrArg Bundle.TotalSpace.proj h
  exact h2

/-- **The tube map** of a closed geodesic in normalised time: `(s, h) ↦ exp_{γ(ℓ s)}(h ν(ℓ s))`. -/
def closedGeodesicTubeMap {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : TangentBundle I M)
    (ℓ : ℝ) (ν : ℝ → E) (σ : ℤˣ) (z : NormalCover σ) : M :=
  transverseShift g p ν (ℓ * NormalCover.time σ z, NormalCover.fiber σ z)

/-- The tube map is invariant under the deck action. -/
theorem closedGeodesicTubeMap_smul
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (hdom : g.geodesicFlowDomain = univ) {p : TangentBundle I M} {ℓ : ℝ}
    (hper : g.geodesicFlow p ℓ = p) {ν : ℝ → E} {σ : ℤˣ}
    (hσ : ∀ t, ν (t + ℓ) = ((σ : ℤ) : ℝ) • ν t) (k : Multiplicative ℤ) (z : NormalCover σ) :
    closedGeodesicTubeMap g p ℓ ν σ (k • z) = closedGeodesicTubeMap g p ℓ ν σ z := by
  unfold closedGeodesicTubeMap
  rw [NormalCover.smul_def, NormalCover.time_mk, NormalCover.fiber_mk,
    show ℓ * (NormalCover.time σ z + ((Multiplicative.toAdd k : ℤ) : ℝ)) =
      ℓ * NormalCover.time σ z + ((Multiplicative.toAdd k : ℤ) : ℝ) * ℓ by ring,
    transverseShift_add_int_mul g hr hdom hper hσ, ← mul_assoc, holonomyPow_mul_self, one_mul]

end DifferentialGeometry.Geometry.FiniteSoul
