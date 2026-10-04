import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftGauss
import DifferentialGeometry.Geometry.Curvature.Surface.GeodesicParallelCoordinates
import DifferentialGeometry.Geometry.Curvature.Surface.PeriodicGaussBonnetBinding
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic

/-!
# The scalar Jacobi equation of the transverse shift (S-SHIFT2, dimension two)

Let `ξ` be a continuous unit normal along the unit geodesic `γ t = π φ_t(p)` of a `C^(r+1)` metric,
`r ≥ 3`, on a surface, on an open set `J` of times, and `α(t, h) = π φ_h(γ t, ξ t)`. In linear
coordinates `y ↦ (t, h)` the pulled-back coefficient field `α*g` is `G dt² + dh²` (Gauss lemma and
speed conservation), it is `C²` (since `α ∈ C^r`, `r ≥ 3`), and `α` is a local `C³` diffeomorphism
where `G > 0` (inverse function theorem). SF-B's divergence identity in the local form
`hasDerivAt_deriv_sqrt_of_geodesicParallel`, together with SF-B2's chart curvature along a local
diffeomorphism, gives the scalar Jacobi equation `j'' = -K j` for `j = √G(t₀, ·)` at every point where
`G > 0` (`transverseShift_jacobi`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- The transverse shift is `C^r` on `J × ℝ` when the normal field is `C^r` along `J`. -/
theorem contMDiffAt_transverseShift (hr : 1 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) {ξ : ℝ → E} {z : ℝ × ℝ}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) z.1) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I r (transverseShift g p ξ) z := by
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  have h1 : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent r
      (fun z : ℝ × ℝ => (⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M)) z :=
    ContMDiffAt.comp (x := z) (f := Prod.fst) hV (contDiff_fst.contMDiff.contMDiffAt)
  have hin : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) r
      (fun z : ℝ × ℝ => ((⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M), z.2)) z :=
    h1.prodMk (contDiff_snd.contMDiff.contMDiffAt)
  have hfl := ((g.contMDiffOn_geodesicFlow hr).contMDiffAt
    ((g.isOpen_geodesicFlowDomain hr).mem_nhds (hmem _))).comp z hin
  exact (Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt.comp z hfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- The two partial velocities of a differentiable two-parameter map. -/
theorem mfderiv_apply_eq_slice {F : ℝ × ℝ → M} {z : ℝ × ℝ}
    (hF : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I F z) :
    (@Eq E (mfderiv 𝓘(ℝ, ℝ × ℝ) I F z ((1 : ℝ), (0 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s => F (s, z.2)) z.1 1)) ∧
    (@Eq E (mfderiv 𝓘(ℝ, ℝ × ℝ) I F z ((0 : ℝ), (1 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s => F (z.1, s)) z.2 1)) := by
  have hs1 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun s : ℝ => (s, z.2)) z.1
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((1 : ℝ), (0 : ℝ))) := by
    have h := ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)).hasFDerivAt
    exact h.hasMFDerivAt
  have hs2 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun s : ℝ => (z.1, s)) z.2
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((0 : ℝ), (1 : ℝ))) := by
    have h := ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)).hasFDerivAt
    exact h.hasMFDerivAt
  have hc1 := hF.hasMFDerivAt.comp z.1 hs1
  have hc2 := hF.hasMFDerivAt.comp z.2 hs2
  constructor
  · change _ = mfderiv 𝓘(ℝ, ℝ) I (F ∘ fun s : ℝ => (s, z.2)) z.1 1
    rw [hc1.mfderiv]
    change _ = mfderiv 𝓘(ℝ, ℝ × ℝ) I F z (((1 : ℝ →L[ℝ] ℝ) 1) • ((1 : ℝ), (0 : ℝ)))
    rw [one_apply_eq_self, one_smul]
  · change _ = mfderiv 𝓘(ℝ, ℝ) I (F ∘ fun s : ℝ => (z.1, s)) z.2 1
    rw [hc2.mfderiv]
    change _ = mfderiv 𝓘(ℝ, ℝ × ℝ) I F z (((1 : ℝ →L[ℝ] ℝ) 1) • ((0 : ℝ), (1 : ℝ)))
    rw [one_apply_eq_self, one_smul]

/-- The `h`-velocity of the transverse shift is the flow velocity. -/
theorem mfderiv_transverseShift_snd (hr : 1 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) (ξ : ℝ → E) (z : ℝ × ℝ) :
    @Eq E (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (z.1, s)) z.2 1)
      (g.geodesicFlow (⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M) z.2).snd := by
  have hm := (g.hasMFDerivAt_geodesicFlow_proj hr
    (p := (⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M)) (t := z.2)
    (by rw [hdom]; exact mem_univ _)).mfderiv
  change mfderiv 𝓘(ℝ, ℝ) I (fun s => (g.geodesicFlow
    (⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M) s).proj) z.2 1 = _
  rw [hm]
  change ((1 : ℝ →L[ℝ] ℝ) 1) • (g.geodesicFlow
    (⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M) z.2).snd = _
  rw [one_apply_eq_self, one_smul]

omit [FiniteDimensional ℝ E] in
private theorem quadratic_of_orthonormal_snd (B : E →L[ℝ] E →L[ℝ] ℝ) {v₁ v₂ : E}
    (h12 : B v₁ v₂ = 0) (h21 : B v₂ v₁ = 0) (h22 : B v₂ v₂ = 1) (a c : ℝ) :
    B (a • v₁ + c • v₂) (a • v₁ + c • v₂) = a ^ 2 * B v₁ v₁ + c ^ 2 := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, h12, h21, h22]
  ring

private theorem hasDerivAt_of_comp_const_add {j : ℝ → ℝ} {h₀ d : ℝ}
    (hj : HasDerivAt (fun s => j (h₀ + s)) d 0) : HasDerivAt j d h₀ := by
  have h := HasDerivAt.comp_sub_const (x := h₀) (a := h₀) (by rwa [sub_self])
  simpa using h

section Coordinates

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (bE : Module.Basis (Fin 2) ℝ F)

/-- The linear coordinates `y ↦ (t, h)` of a basis indexed by `Fin 2`. -/
def finTwoCoords : F →L[ℝ] ℝ × ℝ :=
  LinearMap.toContinuousLinearMap ((bE.coord 0).prod (bE.coord 1))

theorem finTwoCoords_apply (y : F) : finTwoCoords bE y = (bE.repr y 0, bE.repr y 1) := rfl

theorem finTwoCoords_basis_zero : finTwoCoords bE (bE 0) = ((1 : ℝ), (0 : ℝ)) := by
  rw [finTwoCoords_apply, bE.repr_self]; simp

theorem finTwoCoords_basis_one : finTwoCoords bE (bE 1) = ((0 : ℝ), (1 : ℝ)) := by
  rw [finTwoCoords_apply, bE.repr_self]; simp

theorem finTwoCoords_smul_add (t h : ℝ) : finTwoCoords bE (t • bE 0 + h • bE 1) = (t, h) := by
  rw [map_add, map_smul, map_smul, finTwoCoords_basis_zero, finTwoCoords_basis_one]
  simp

omit [FiniteDimensional ℝ F] in
theorem finTwoCoords_repr (y : F) : bE.repr y 0 • bE 0 + bE.repr y 1 • bE 1 = y := by
  have h := bE.sum_repr y
  rw [Fin.sum_univ_two] at h
  exact h

end Coordinates

/-- The transverse shift read in the linear coordinates of `bE`. -/
def shiftChart {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : TangentBundle I M)
    (ξ : ℝ → E) (bE : Module.Basis (Fin 2) ℝ E) (y : E) : M :=
  transverseShift g p ξ (finTwoCoords bE y)

/-- The coefficient field `α*g` of the transverse shift in the linear coordinates of `bE`. -/
def shiftCoeff {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : TangentBundle I M)
    (ξ : ℝ → E) (bE : Module.Basis (Fin 2) ℝ E) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (g.inner (shiftChart g p ξ bE y) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (E := E) (F := E)
    (E' := E) (F' := E) (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) y : E →L[ℝ] E)
    (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) y : E →L[ℝ] E)

variable (bE : Module.Basis (Fin 2) ℝ E)

theorem contMDiffOn_shiftChart (hr : 1 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) {ξ : ℝ → E} {J : Set ℝ}
    (hV : ∀ t ∈ J, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t) :
    ContMDiffOn 𝓘(ℝ, E) I r (shiftChart g p ξ bE) (finTwoCoords bE ⁻¹' (J ×ˢ univ)) :=
  fun y hy => ((contMDiffAt_transverseShift g hr hdom p (hV _ hy.1)).comp y
    ((finTwoCoords bE).contDiff.contMDiff.contMDiffAt)).contMDiffWithinAt

theorem contDiffOn_shiftCoeff (hr : 3 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) {ξ : ℝ → E} {J : Set ℝ} (hJ : IsOpen J)
    (hV : ∀ t ∈ J, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t) :
    ContDiffOn ℝ 2 (shiftCoeff g p ξ bE) (finTwoCoords bE ⁻¹' (J ×ˢ univ)) := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have h3r : ((3 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
  have hn : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 :=
    calc (2 : ℕ∞ω) ≤ ((3 : ℕ∞) : ℕ∞ω) := by norm_num
      _ ≤ (r : ℕ∞ω) := h3r
      _ ≤ (r : ℕ∞ω) + 1 := le_self_add
  have h3 : ContMDiffOn 𝓘(ℝ, E) I 3 (shiftChart g p ξ bE) (finTwoCoords bE ⁻¹' (J ×ˢ univ)) :=
    (contMDiffOn_shiftChart g bE hr1 hdom p hV).of_le (by
      calc (3 : ℕ∞ω) = ((3 : ℕ∞) : ℕ∞ω) := by norm_num
        _ ≤ (r : ℕ∞ω) := h3r)
  exact g.contDiffOn_pullback_inner (r := 2) (s := 3) hn (by norm_num)
    ((hJ.prod isOpen_univ).preimage (finTwoCoords bE).continuous) h3

/-- The differential of the coordinate chart on the basis vectors. -/
theorem mfderiv_shiftChart (hr : 1 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) {ξ : ℝ → E} {J : Set ℝ}
    (hV : ∀ t ∈ J, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t)
    {y : E} (hy : y ∈ finTwoCoords bE ⁻¹' (J ×ˢ univ)) :
    @Eq E (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) y (bE 0))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, (finTwoCoords bE y).2))
        (finTwoCoords bE y).1 1) ∧
    @Eq E (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) y (bE 1))
      (g.geodesicFlow (⟨(g.geodesicFlow p (finTwoCoords bE y).1).proj,
        ξ (finTwoCoords bE y).1⟩ : TangentBundle I M) (finTwoCoords bE y).2).snd := by
  have hαd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (transverseShift g p ξ) (finTwoCoords bE y) :=
    (contMDiffAt_transverseShift g hr hdom p (hV _ hy.1)).mdifferentiableAt
      (by exact_mod_cast (zero_lt_one.trans_le hr).ne')
  have hder : ∀ v : E, @Eq E (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) y v)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I (transverseShift g p ξ) (finTwoCoords bE y) (finTwoCoords bE v)) := by
    intro v
    have hL := ((finTwoCoords bE).hasFDerivAt (x := y)).hasMFDerivAt
    have hc := hαd.hasMFDerivAt.comp y hL
    change mfderiv 𝓘(ℝ, E) I (transverseShift g p ξ ∘ finTwoCoords bE) y v = _
    rw [hc.mfderiv]
    rfl
  refine ⟨(hder (bE 0)).trans ?_, (hder (bE 1)).trans ?_⟩
  · rw [finTwoCoords_basis_zero]
    exact (mfderiv_apply_eq_slice hαd).1
  · rw [finTwoCoords_basis_one]
    exact (mfderiv_apply_eq_slice hαd).2.trans
      (mfderiv_transverseShift_snd g hr hdom p ξ (finTwoCoords bE y))

/-- **The coefficient field is `G dt² + dh²`.** -/
theorem shiftCoeff_structure (hr : 2 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) {ξ : ℝ → E} {J : Set ℝ} (hJ : IsOpen J)
    (hV : ∀ t ∈ J, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t)
    (hunit : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1)
    (hperp : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0)
    {y : E} (hy : y ∈ finTwoCoords bE ⁻¹' (J ×ˢ univ)) :
    shiftCoeff g p ξ bE y (bE 0) (bE 0) = transverseSpeedSq g p ξ (finTwoCoords bE y) ∧
    shiftCoeff g p ξ bE y (bE 0) (bE 1) = 0 ∧ shiftCoeff g p ξ bE y (bE 1) (bE 1) = 1 := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  obtain ⟨hdt, hdh⟩ := mfderiv_shiftChart g bE hr1 hdom p hV hy
  refine ⟨?_, ?_, ?_⟩
  · change g.inner (shiftChart g p ξ bE y) (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) y (bE 0))
      (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) y (bE 0)) = _
    rw [hdt]
    rfl
  · change g.inner (shiftChart g p ξ bE y) (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) y (bE 0))
      (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) y (bE 1)) = 0
    rw [hdt, hdh]
    exact (g.symm _ _ _).trans (inner_transverseShift_gauss g hr hdom p (hV _ hy.1)
      (eventually_of_mem (hJ.mem_nhds hy.1) hunit) (hperp _ hy.1) (finTwoCoords bE y).2)
  · change g.inner (shiftChart g p ξ bE y) (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) y (bE 1))
      (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) y (bE 1)) = 1
    rw [hdh]
    exact (g.inner_geodesicFlow_eq hr1 _ _ (hmem _)).trans (hunit _ hy.1)

/-- Where `G > 0` the coefficient field is positive. -/
theorem shiftCoeff_pos (hr : 2 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) {ξ : ℝ → E} {J : Set ℝ} (hJ : IsOpen J)
    (hV : ∀ t ∈ J, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t)
    (hunit : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1)
    (hperp : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0)
    {y : E} (hy : y ∈ finTwoCoords bE ⁻¹' (J ×ˢ univ))
    (hG : 0 < transverseSpeedSq g p ξ (finTwoCoords bE y)) (v : E) (hv : v ≠ 0) :
    0 < shiftCoeff g p ξ bE y v v := by
  obtain ⟨h11, h12, h22⟩ := shiftCoeff_structure g bE hr hdom p hJ hV hunit hperp hy
  have h21 : shiftCoeff g p ξ bE y (bE 1) (bE 0) = 0 := (g.symm _ _ _).trans h12
  obtain ⟨a, c, hv'⟩ : ∃ a c : ℝ, v = a • bE 0 + c • bE 1 := ⟨_, _, (finTwoCoords_repr bE v).symm⟩
  rw [hv', quadratic_of_orthonormal_snd _ h12 h21 h22, h11]
  by_cases ha : a = 0
  · have hc : c ≠ 0 := by
      intro hc
      apply hv
      rw [hv', ha, hc, zero_smul, zero_smul, add_zero]
    rw [ha]
    positivity
  · have : 0 < a ^ 2 * transverseSpeedSq g p ξ (finTwoCoords bE y) :=
      mul_pos (lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))) hG
    positivity

/-- **Curvature in the coordinates of the transverse shift.** Where `G > 0`, the coordinate chart is a
local `C³` diffeomorphism, and the coefficient curvature of `α*g` is the sectional curvature of `g` on
`(∂ₜα, ∂ₕα)`. -/
theorem coefficientSectional_shiftCoeff (hr : 3 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) {ξ : ℝ → E} {J : Set ℝ} (hJ : IsOpen J)
    (hV : ∀ t ∈ J, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t)
    (hunit : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1)
    (hperp : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0)
    {t₀ h₀ : ℝ} (ht₀ : t₀ ∈ J) (hG : 0 < transverseSpeedSq g p ξ (t₀, h₀)) :
    DifferentialGeometry.Analysis.coefficientSectional (shiftCoeff g p ξ bE)
        (t₀ • bE 0 + h₀ • bE 1) (bE 0) (bE 1) =
      g.sectionalCurvature (transverseShift g p ξ (t₀, h₀))
        (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, h₀)) t₀ 1)
        (g.geodesicFlow (⟨(g.geodesicFlow p t₀).proj, ξ t₀⟩ : TangentBundle I M) h₀).snd := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have h3r : ((3 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
  have hn : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 :=
    calc (2 : ℕ∞ω) ≤ ((3 : ℕ∞) : ℕ∞ω) := by norm_num
      _ ≤ (r : ℕ∞ω) := h3r
      _ ≤ (r : ℕ∞ω) + 1 := le_self_add
  have hLy₀ := finTwoCoords_smul_add bE t₀ h₀
  have hU₀ : IsOpen (finTwoCoords bE ⁻¹' (J ×ˢ univ)) :=
    (hJ.prod isOpen_univ).preimage (finTwoCoords bE).continuous
  have hy₀ : t₀ • bE 0 + h₀ • bE 1 ∈ finTwoCoords bE ⁻¹' (J ×ˢ univ) := by
    change finTwoCoords bE (t₀ • bE 0 + h₀ • bE 1) ∈ J ×ˢ univ
    rw [hLy₀]; exact ⟨ht₀, mem_univ _⟩
  have hc := contMDiffOn_shiftChart g bE hr1 hdom p hV
  have hmd : MDifferentiableAt 𝓘(ℝ, E) I (shiftChart g p ξ bE) (t₀ • bE 0 + h₀ • bE 1) :=
    ((hc _ hy₀).contMDiffAt (hU₀.mem_nhds hy₀)).mdifferentiableAt
      (by exact_mod_cast (zero_lt_one.trans_le hr1).ne')
  have hGy : 0 < transverseSpeedSq g p ξ (finTwoCoords bE (t₀ • bE 0 + h₀ • bE 1)) := by
    rw [hLy₀]; exact hG
  have hinj : Function.Injective
      (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) (t₀ • bE 0 + h₀ • bE 1)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    have h := shiftCoeff_pos g bE hr2 hdom p hJ hV hunit hperp hy₀ hGy v hne
    change 0 < g.inner _ (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) (t₀ • bE 0 + h₀ • bE 1) v)
      (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) (t₀ • bE 0 + h₀ • bE 1) v) at h
    rw [hv, map_zero] at h
    exact lt_irrefl _ h
  have hinv' : (mfderiv 𝓘(ℝ, E) I (shiftChart g p ξ bE) (t₀ • bE 0 + h₀ • bE 1)).IsInvertible := by
    have hsurj := LinearMap.injective_iff_surjective.mp hinj
    exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, by ext v; rfl⟩
  have hinv : (fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, E) I (t₀ • bE 0 + h₀ • bE 1)
      (shiftChart g p ξ bE)) (extChartAt 𝓘(ℝ, E) (t₀ • bE 0 + h₀ • bE 1)
        (t₀ • bE 0 + h₀ • bE 1))).IsInvertible := by
    rwa [hmd.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ] at hinv'
  have h3 : ContMDiffOn 𝓘(ℝ, E) I 3 (shiftChart g p ξ bE) (finTwoCoords bE ⁻¹' (J ×ˢ univ)) :=
    hc.of_le (by
      calc (3 : ℕ∞ω) = ((3 : ℕ∞) : ℕ∞ω) := by norm_num
        _ ≤ (r : ℕ∞ω) := h3r)
  obtain ⟨Φ, hy₀Φ, -, heqΦ⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn (n := 3)
      (by norm_num) (by simp) hU₀ hy₀ h3 hinv
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, E) I 3 (shiftChart g p ξ bE) (t₀ • bE 0 + h₀ • bE 1) :=
    ⟨Φ, hy₀Φ, heqΦ⟩
  have hsec := g.sectionalCurvature_comp_eq_coefficientSectional hn le_rfl hloc (bE 0) (bE 1)
  obtain ⟨hdt, hdh⟩ := mfderiv_shiftChart g bE hr1 hdom p hV hy₀
  rw [hLy₀] at hdt hdh
  have hKc : ∀ (x x' : M) (a a' c c' : E), x = x' → a = a' → c = c' →
      g.sectionalCurvature x a c = g.sectionalCurvature x' a' c' := by
    rintro x x' a a' c c' rfl rfl rfl
    rfl
  refine hsec.symm.trans (hKc _ _ _ _ _ _ ?_ hdt hdh)
  change transverseShift g p ξ (finTwoCoords bE (t₀ • bE 0 + h₀ • bE 1)) = _
  rw [hLy₀]

/-- **The scalar Jacobi equation of the transverse shift (dimension two).** At every `(t₀, h₀)`,
`t₀ ∈ J`, where the transverse speed `G` is positive, `j = √G(t₀, ·)` satisfies
`j''(h₀) = -K j(h₀)`, `K` the sectional curvature on the plane `(∂ₜα, ∂ₕα)`. Also `G(t₀, ·)` is
continuous. -/
theorem transverseShift_jacobi (hr : 3 ≤ r) (hdim : Module.finrank ℝ E = 2)
    (hdom : g.geodesicFlowDomain = univ) (p : TangentBundle I M)
    (hp : g.inner p.proj p.snd p.snd = 1) {ξ : ℝ → E} {J : Set ℝ} (hJ : IsOpen J)
    (hcont : ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) J)
    (hunit : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1)
    (hperp : ∀ t ∈ J, g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    Continuous (fun h => transverseSpeedSq g p ξ (t₀, h)) ∧
    ∀ h₀, 0 < transverseSpeedSq g p ξ (t₀, h₀) →
      HasDerivAt (fun h => Real.sqrt (transverseSpeedSq g p ξ (t₀, h)))
        (deriv (fun h => Real.sqrt (transverseSpeedSq g p ξ (t₀, h))) h₀) h₀ ∧
      HasDerivAt (deriv (fun h => Real.sqrt (transverseSpeedSq g p ξ (t₀, h))))
        (-(g.sectionalCurvature (transverseShift g p ξ (t₀, h₀))
            (mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, h₀)) t₀ 1)
            (g.geodesicFlow (⟨(g.geodesicFlow p t₀).proj, ξ t₀⟩ : TangentBundle I M) h₀).snd *
          Real.sqrt (transverseSpeedSq g p ξ (t₀, h₀)))) h₀ := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hV : ∀ t ∈ J, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t := fun t ht =>
    contMDiffAt_unitNormal_dim_two g hr1 hdim p (fun t => by rw [hdom]; exact mem_univ _) hp hJ
      hcont hunit hperp ht
  let bE : Module.Basis (Fin 2) ℝ E := Module.finBasisOfFinrankEq ℝ E hdim
  have hU₀ : IsOpen (finTwoCoords bE ⁻¹' (J ×ˢ univ)) :=
    (hJ.prod isOpen_univ).preimage (finTwoCoords bE).continuous
  have hline : ∀ h : ℝ, t₀ • bE 0 + h • bE 1 ∈ finTwoCoords bE ⁻¹' (J ×ˢ univ) := fun h => by
    change finTwoCoords bE (t₀ • bE 0 + h • bE 1) ∈ J ×ˢ univ
    rw [finTwoCoords_smul_add]; exact ⟨ht₀, mem_univ _⟩
  have hbc := contDiffOn_shiftCoeff g bE hr hdom p hJ hV
  have hGline : ∀ h : ℝ, transverseSpeedSq g p ξ (t₀, h) =
      shiftCoeff g p ξ bE (t₀ • bE 0 + h • bE 1) (bE 0) (bE 0) := fun h => by
    rw [(shiftCoeff_structure g bE hr2 hdom p hJ hV hunit hperp (hline h)).1,
      finTwoCoords_smul_add]
  have hb11c : ContinuousOn (fun y => shiftCoeff g p ξ bE y (bE 0) (bE 0))
      (finTwoCoords bE ⁻¹' (J ×ˢ univ)) :=
    (hbc.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hlinec : Continuous fun h : ℝ => t₀ • bE 0 + h • bE 1 :=
    continuous_const.add (continuous_id.smul continuous_const)
  refine ⟨(hb11c.comp_continuous hlinec hline).congr fun h => (hGline h).symm, ?_⟩
  intro h₀ hG₀
  -- the open set where `G > 0`
  have hU₁ : IsOpen ((finTwoCoords bE ⁻¹' (J ×ˢ univ)) ∩
      (fun y => shiftCoeff g p ξ bE y (bE 0) (bE 0)) ⁻¹' Ioi 0) :=
    hb11c.isOpen_inter_preimage hU₀ isOpen_Ioi
  have hy₀U₁ : t₀ • bE 0 + h₀ • bE 1 ∈ (finTwoCoords bE ⁻¹' (J ×ˢ univ)) ∩
      (fun y => shiftCoeff g p ξ bE y (bE 0) (bE 0)) ⁻¹' Ioi 0 :=
    ⟨hline h₀, by simp only [mem_preimage, mem_Ioi]; rw [← hGline]; exact hG₀⟩
  have hpos : ∀ y ∈ (finTwoCoords bE ⁻¹' (J ×ˢ univ)) ∩
      (fun y => shiftCoeff g p ξ bE y (bE 0) (bE 0)) ⁻¹' Ioi 0, ∀ v, v ≠ 0 →
        0 < shiftCoeff g p ξ bE y v v := by
    intro y hy v hv
    have hG : 0 < transverseSpeedSq g p ξ (finTwoCoords bE y) := by
      rw [← (shiftCoeff_structure g bE hr2 hdom p hJ hV hunit hperp hy.1).1]; exact hy.2
    exact shiftCoeff_pos g bE hr2 hdom p hJ hV hunit hperp hy.1 hG v hv
  have hli : LinearIndependent ℝ ![bE 0, bE 1] := by
    have heq : ![bE 0, bE 1] = ⇑bE := by
      ext i
      fin_cases i <;> rfl
    rw [heq]
    exact bE.linearIndependent
  obtain ⟨hφd, hφ''⟩ := DifferentialGeometry.Analysis.hasDerivAt_deriv_sqrt_of_geodesicParallel
    hdim hU₁ (hbc.mono inter_subset_left) (fun y _ u v => g.symm _ _ _) hpos hli
    (fun y hy => (shiftCoeff_structure g bE hr2 hdom p hJ hV hunit hperp hy.1).2.1)
    (fun y hy => (shiftCoeff_structure g bE hr2 hdom p hJ hV hunit hperp hy.1).2.2) hy₀U₁
  -- the `v₂`-line through `y₀` is the `h`-line through `(t₀, h₀)`
  have hφeq : (fun s : ℝ => Real.sqrt (shiftCoeff g p ξ bE (t₀ • bE 0 + h₀ • bE 1 + s • bE 1)
      (bE 0) (bE 0))) = fun s => Real.sqrt (transverseSpeedSq g p ξ (t₀, h₀ + s)) := by
    funext s
    have hpt : t₀ • bE 0 + h₀ • bE 1 + s • bE 1 = t₀ • bE 0 + (h₀ + s) • bE 1 := by
      rw [add_smul]; abel
    rw [hpt, ← hGline]
  rw [hφeq] at hφd hφ''
  have hdφ : deriv (fun s : ℝ => Real.sqrt (transverseSpeedSq g p ξ (t₀, h₀ + s))) =
      fun s => deriv (fun h => Real.sqrt (transverseSpeedSq g p ξ (t₀, h))) (h₀ + s) := by
    funext s
    exact deriv_comp_const_add (f := fun h => Real.sqrt (transverseSpeedSq g p ξ (t₀, h)))
      (a := h₀) (x := s)
  rw [hdφ] at hφ''
  have hj₁ := (hasDerivAt_of_comp_const_add
    (j := fun h => Real.sqrt (transverseSpeedSq g p ξ (t₀, h))) hφd.self_of_nhds)
  refine ⟨hj₁.differentiableAt.hasDerivAt, ?_⟩
  have hj₂ := hasDerivAt_of_comp_const_add
    (j := deriv (fun h => Real.sqrt (transverseSpeedSq g p ξ (t₀, h)))) hφ''
  rw [coefficientSectional_shiftCoeff g bE hr hdom p hJ hV hunit hperp ht₀ hG₀, ← hGline] at hj₂
  exact hj₂

end DifferentialGeometry.Geometry.FiniteSoul
