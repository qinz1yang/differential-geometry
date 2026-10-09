import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicSubmanifold
import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# BASE-1b: the circle carrier of a simple closed geodesic (lane CMS3-CARRIER, group G1)

Frozen interface `soulBase_closedGeodesic` (D-CMS3 §9, review §10: correct). For a closed unit
geodesic `γ t = π Φ_t p` of least period `ℓ` of a complete `C^{r+1}` metric (`r ≥ 2`), the map
`b : AddCircle 1 → M`, `b t = γ (ℓ t)`, is `C^{r−1}`, injective, has the trace of `γ` as range, and
has a global left inverse `R : M → AddCircle 1` that is `C^{r−1}` at every point of the trace.

Route (no tube is needed):
* `exists_local_leftInverse_curve`: a `C^n` curve with nonzero velocity at `t₀` has, near `γ t₀`, a
  real `C^n` left inverse `ρ` (`ρ (γ t) = t` near `t₀`): `ρ = t₀ + h⁻¹ ∘ λ ∘ (φ − c₀)` with `φ` the
  chart at `γ t₀`, `λ` a functional with `λ (γ' t₀) = 1`, and `h τ = λ (φ (γ (t₀ + τ)) − c₀)`
  (one-dimensional inverse function theorem, `h' 0 = 1`);
* `exists_leftInverse_addCircle_of_local`: local left inverses of an injective continuous
  `b : AddCircle 1 → M` are glued by `F = Σ φ_i · exp (2π i ρ_i)` (smooth bump functions `φ_i`) and
  `R = arg F / 2π`; near a point of the trace `R` is the class of the smooth real function
  `σ + arg (F · e^{−2π i σ}) / 2π`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

section LocalInverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Local left inverse of an immersed curve.** A `C^n` curve (`1 ≤ n`) whose velocity at `t₀` is
nonzero has, on an open neighbourhood `U` of `γ t₀`, a real `C^n` function `ρ` with `ρ (γ t) = t`
for `t` near `t₀`. -/
theorem exists_local_leftInverse_curve {n : ℕ∞} (hn : 1 ≤ n) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) {t₀ : ℝ} {v : E}
    (hv : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight v)) (hv0 : v ≠ 0) :
    ∃ η > 0, ∃ U : Set M, IsOpen U ∧ γ t₀ ∈ U ∧ ∃ ρ : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) n ρ U ∧ ∀ t ∈ Ioo (t₀ - η) (t₀ + η), ρ (γ t) = t := by
  have hn' : (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hn
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := (zero_lt_one.trans_le hn').ne'
  set x₀ : M := γ t₀ with hx₀
  set φ := extChartAt I x₀ with hφ
  -- the chart representative of the curve
  set O : Set ℝ := γ ⁻¹' (chartAt H x₀).source with hO
  have hOo : IsOpen O := (chartAt H x₀).open_source.preimage hγ.continuous
  have ht₀O : t₀ ∈ O := mem_chart_source H x₀
  set c : ℝ → E := fun t => φ (γ t) with hc
  have hcO : ContDiffOn ℝ n c O := by
    have h1 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) n (fun t => φ (γ t)) O :=
      (contMDiffOn_extChartAt (n := (n : WithTop ℕ∞))).comp hγ.contMDiffOn (fun t ht => ht)
    exact contMDiffOn_iff_contDiffOn.mp h1
  have hcder : HasDerivAt c v t₀ := by
    have hφd : HasMFDerivAt I 𝓘(ℝ, E) φ x₀ (mfderiv I 𝓘(ℝ, E) φ x₀) :=
      (mdifferentiableAt_extChartAt (mem_chart_source H x₀)).hasMFDerivAt
    have hcomp := hφd.comp t₀ hv
    rw [mfderiv_extChartAt_self] at hcomp
    have hF : HasFDerivAt c ((ContinuousLinearMap.id ℝ E).comp ((1 : ℝ →L[ℝ] ℝ).smulRight v))
        t₀ := hasMFDerivAt_iff_hasFDerivAt.mp hcomp
    rw [ContinuousLinearMap.id_comp] at hF
    exact hasDerivAt_iff_hasFDerivAt.mpr hF
  -- a functional with `λ v = 1`
  obtain ⟨L, hL⟩ := SeparatingDual.exists_eq_one (R := ℝ) hv0
  -- the scalar function `h`
  set O' : Set ℝ := (fun τ => t₀ + τ) ⁻¹' O with hO'
  have hO'o : IsOpen O' := hOo.preimage (continuous_const.add continuous_id)
  have h0O' : (0 : ℝ) ∈ O' := by simpa [hO'] using ht₀O
  set h : ℝ → ℝ := fun τ => L (c (t₀ + τ) - c t₀) with hh
  have hhO' : ContDiffOn ℝ n h O' := by
    have hshift : ContDiffOn ℝ n (fun τ => c (t₀ + τ)) O' :=
      hcO.comp (contDiff_const.add contDiff_id).contDiffOn (fun τ hτ => hτ)
    exact L.contDiff.comp_contDiffOn (hshift.sub contDiffOn_const)
  have hh0 : h 0 = 0 := by simp [hh]
  have hhder0 : HasDerivAt h 1 0 := by
    have h1 : HasDerivAt (fun τ => c (t₀ + τ)) v 0 :=
      HasDerivAt.comp_const_add t₀ 0 (by rw [add_zero]; exact hcder)
    have h2 : HasDerivAt h (L v) 0 :=
      L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h1.sub_const (c t₀))
    rwa [hL] at h2
  have hhcd : ∀ τ ∈ O', ContDiffAt ℝ n h τ := fun τ hτ =>
    (hhO' τ hτ).contDiffAt (hO'o.mem_nhds hτ)
  have hstrict : HasStrictDerivAt h 1 0 := by
    have := (hhcd 0 h0O').hasStrictDerivAt hn0
    rwa [hhder0.deriv] at this
  have hstrictF : HasStrictFDerivAt h
      ((ContinuousLinearEquiv.refl ℝ ℝ : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) 0 := by
    have h1 := hstrict.hasStrictFDerivAt
    have h2 : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) = ContinuousLinearMap.id ℝ ℝ := by
      ext; simp
    rw [h2] at h1
    exact h1
  set Φ := hstrictF.toOpenPartialHomeomorph h with hΦ
  have hΦcoe : (Φ : ℝ → ℝ) = h := rfl
  have h0src : (0 : ℝ) ∈ Φ.source := hstrictF.mem_toOpenPartialHomeomorph_source
  -- where the derivative of `h` stays nonzero
  have hderc : ContinuousOn (deriv h) O' := hhO'.continuousOn_deriv_of_isOpen hO'o hn'
  set W : Set ℝ := Φ.source ∩ (O' ∩ {τ | deriv h τ ≠ 0}) with hW
  have hWo : IsOpen W :=
    Φ.open_source.inter (hderc.isOpen_inter_preimage hO'o isOpen_compl_singleton)
  have h0W : (0 : ℝ) ∈ W := ⟨h0src, h0O', show deriv h 0 ≠ 0 by
    rw [hhder0.deriv]; exact one_ne_zero⟩
  have hWsub : W ⊆ Φ.source := inter_subset_left
  set T : Set ℝ := Φ '' W with hT
  have hTo : IsOpen T := Φ.isOpen_image_of_subset_source hWo hWsub
  have hsymm : ∀ a ∈ T, ContDiffAt ℝ n Φ.symm a := by
    rintro a ⟨τ, hτW, rfl⟩
    have hτs : Φ.symm (Φ τ) = τ := Φ.left_inv hτW.1
    have hdiff : DifferentiableAt ℝ h τ :=
      (hhcd τ hτW.2.1).differentiableAt hn0
    refine Φ.contDiffAt_symm_deriv (f₀' := deriv h τ) hτW.2.2
      (Φ.map_source hτW.1) ?_ ?_
    · rw [hτs]; exact hdiff.hasDerivAt
    · rw [hτs]; exact hhcd τ hτW.2.1
  -- the left inverse
  refine ⟨?_, ?_, {y | y ∈ (chartAt H x₀).source ∧ L (φ y - c t₀) ∈ T}, ?_, ?_,
    fun y => t₀ + Φ.symm (L (φ y - c t₀)), ?_, ?_⟩
  · exact Classical.choose (Metric.isOpen_iff.mp (Φ.open_source.inter hO'o) 0 ⟨h0src, h0O'⟩)
  · exact (Classical.choose_spec
      (Metric.isOpen_iff.mp (Φ.open_source.inter hO'o) 0 ⟨h0src, h0O'⟩)).1
  · have h1 : ContinuousOn φ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I)]; exact continuousOn_extChartAt x₀
    have hcont : ContinuousOn (fun y => L (φ y - c t₀)) (chartAt H x₀).source :=
      L.continuous.comp_continuousOn (h1.sub continuousOn_const)
    exact hcont.isOpen_inter_preimage (chartAt H x₀).open_source hTo
  · refine ⟨mem_chart_source H x₀, ?_⟩
    have : L (φ x₀ - c t₀) = Φ 0 := by rw [hΦcoe, hh0]; simp [hc, hx₀]
    rw [this]
    exact mem_image_of_mem _ h0W
  · intro y hy
    have hyc : ContMDiffAt I 𝓘(ℝ, E) n φ y :=
      (contMDiffOn_extChartAt (n := (n : WithTop ℕ∞))).contMDiffAt
        ((chartAt H x₀).open_source.mem_nhds hy.1)
    have hinner : ContMDiffAt I 𝓘(ℝ, ℝ) n (fun y => L (φ y - c t₀)) y :=
      L.contDiff.contMDiff.contMDiffAt.comp y (hyc.sub contMDiffAt_const)
    have hs := (hsymm _ hy.2).contMDiffAt.comp y hinner
    exact (contMDiffAt_const.add hs).contMDiffWithinAt
  · intro t ht
    set η := Classical.choose
      (Metric.isOpen_iff.mp (Φ.open_source.inter hO'o) 0 ⟨h0src, h0O'⟩) with hη
    have hball := (Classical.choose_spec
      (Metric.isOpen_iff.mp (Φ.open_source.inter hO'o) 0 ⟨h0src, h0O'⟩)).2
    have hmem : t - t₀ ∈ Φ.source ∩ O' := by
      apply hball
      rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have hcalc : L (φ (γ t) - c t₀) = Φ (t - t₀) := by
      rw [hΦcoe]
      simp only [hh, hc]
      congr 2
      ring_nf
    change t₀ + Φ.symm (L (φ (γ t) - c t₀)) = t
    rw [hcalc, Φ.left_inv hmem.1]
    ring

end LocalInverse

section Gluing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- Adding an integer does not change the class in `AddCircle 1`. -/
theorem coe_add_int_addCircle (a : ℝ) (k : ℤ) :
    (((a + k : ℝ)) : AddCircle (1 : ℝ)) = (a : AddCircle (1 : ℝ)) := by
  rw [AddCircle.coe_add]
  have hk : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨k, by simp⟩
  rw [hk, add_zero]

/-- Two reals with the same class in `AddCircle 1` differ by an integer. -/
theorem exists_int_of_coe_eq_addCircle {a b : ℝ}
    (h : (a : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ))) : ∃ k : ℤ, b = a + k := by
  have h' : ((b - a : ℝ) : AddCircle (1 : ℝ)) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h'
  refine ⟨k, ?_⟩
  have : (k : ℝ) = b - a := by simpa using hk
  linarith

/-- `exp (2π i t)` depends only on the class of `t` in `AddCircle 1`. -/
theorem cexp_two_pi_mul_I_eq_of_coe_eq {a b : ℝ}
    (h : (a : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ))) :
    Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * b : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨k, rfl⟩ := exists_int_of_coe_eq_addCircle h
  have : (((2 * Real.pi * (a + k) : ℝ) : ℂ) * Complex.I) =
      ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The argument of `exp (2π i σ)`, divided by `2π`, has the class of `σ`. -/
theorem coe_arg_cexp_div_two_pi (σ : ℝ) :
    ((Complex.arg (Complex.exp (((2 * Real.pi * σ : ℝ) : ℂ) * Complex.I)) / (2 * Real.pi) : ℝ) :
      AddCircle (1 : ℝ)) = (σ : AddCircle (1 : ℝ)) := by
  rw [Complex.arg_exp]
  have him : ((((2 * Real.pi * σ : ℝ) : ℂ) * Complex.I).im) = 2 * Real.pi * σ := by simp
  rw [him]
  have hdecomp := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (-Real.pi) (2 * Real.pi * σ)
  have hpi : (2 * Real.pi) ≠ 0 := Real.two_pi_pos.ne'
  have heq : toIocMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * σ) / (2 * Real.pi) =
      σ + ((-(toIocDiv Real.two_pi_pos (-Real.pi) (2 * Real.pi * σ)) : ℤ) : ℝ) := by
    rw [zsmul_eq_mul] at hdecomp
    field_simp
    push_cast
    linarith
  rw [heq, coe_add_int_addCircle]

/-- The class of `arg w / 2π` changes by the angle of a unimodular factor. -/
theorem coe_arg_mul_cexp_div_two_pi {w : ℂ} (hw : w ≠ 0) (σ : ℝ) :
    ((σ + Complex.arg (w * Complex.exp (((-(2 * Real.pi * σ)) : ℝ) * Complex.I)) /
      (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) =
      ((Complex.arg w / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) := by
  set u : ℂ := Complex.exp (((-(2 * Real.pi * σ)) : ℝ) * Complex.I) with hu
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hangle := Complex.arg_mul_coe_angle hw hu0
  have huarg : (Complex.arg u : Real.Angle) = ((-(2 * Real.pi * σ) : ℝ) : Real.Angle) := by
    rw [hu, Complex.arg_exp]
    have him : (((((-(2 * Real.pi * σ)) : ℝ) : ℂ) * Complex.I).im) = -(2 * Real.pi * σ) := by
      simp
    rw [him, Real.Angle.coe_toIocMod]
  rw [huarg, ← Real.Angle.coe_add] at hangle
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hangle
  have hpi : (2 * Real.pi) ≠ 0 := Real.two_pi_pos.ne'
  have heq : σ + Complex.arg (w * u) / (2 * Real.pi) =
      Complex.arg w / (2 * Real.pi) + (k : ℝ) := by
    field_simp
    linarith
  rw [heq, coe_add_int_addCircle]

/-- **Gluing local left inverses of a circle.** If an injective continuous `b : AddCircle 1 → M`
has, near every point of its image, a real `C^n` function `ρ` with `ρ (b z') ≡ z'`, then it has a
global left inverse `R : M → AddCircle 1` that is `C^n` at every point of its image (injectivity
of `b` follows from the local property). -/
theorem exists_leftInverse_addCircle_of_local {n : ℕ∞} {b : AddCircle (1 : ℝ) → M}
    (hb : Continuous b)
    (hloc : ∀ z : AddCircle (1 : ℝ), ∃ U : Set M, IsOpen U ∧ b z ∈ U ∧ ∃ ρ : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) n ρ U ∧
        ∀ z' : AddCircle (1 : ℝ), b z' ∈ U → ((ρ (b z') : ℝ) : AddCircle (1 : ℝ)) = z') :
    ∃ R : M → AddCircle (1 : ℝ), (∀ s, R (b s) = s) ∧
      ∀ s, ContMDiffAt I 𝓘(ℝ, ℝ) n R (b s) := by
  classical
  choose U hUo hzU ρ hρ hρinv using hloc
  have hbump : ∀ z : AddCircle (1 : ℝ), ∃ f : SmoothBumpFunction I (b z), tsupport ⇑f ⊆ U z :=
    fun z => by
      obtain ⟨f, -, hf⟩ :=
        (SmoothBumpFunction.nhds_basis_tsupport (I := I) (b z)).mem_iff.mp
          ((hUo z).mem_nhds (hzU z))
      exact ⟨f, hf⟩
  choose f hf using hbump
  have hf1 : ∀ z, f z (b z) = 1 := fun z => (f z).eventuallyEq_one.eq_of_nhds
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun z : AddCircle (1 : ℝ) => b ⁻¹' support (f z))
    (fun z => (f z).continuous.isOpen_support.preimage hb)
    (fun s _ => mem_iUnion.mpr ⟨s, by
      change f s (b s) ≠ 0
      rw [hf1]; exact one_ne_zero⟩)
  set G : AddCircle (1 : ℝ) → M → ℂ := fun z y =>
    Complex.exp (((2 * Real.pi * ρ z y : ℝ) : ℂ) * Complex.I) with hG
  set F : M → ℂ := fun y => ∑ z ∈ t, (f z y : ℝ) • G z y with hF
  have hsum_pos : ∀ s, 0 < ∑ z ∈ t, f z (b s) := by
    intro s
    obtain ⟨z, hzt, hz⟩ := mem_iUnion₂.mp (ht (mem_univ s))
    have hz' : f z (b s) ≠ 0 := hz
    refine Finset.sum_pos' (fun i _ => (f i).nonneg) ⟨z, hzt, ?_⟩
    exact lt_of_le_of_ne (f z).nonneg (Ne.symm hz')
  have hFb : ∀ σ : ℝ, F (b σ) = (∑ z ∈ t, f z (b σ) : ℝ) •
      Complex.exp (((2 * Real.pi * σ : ℝ) : ℂ) * Complex.I) := by
    intro σ
    rw [hF, Finset.sum_smul]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hfz : f z (b σ) = 0
    · rw [hfz, zero_smul, zero_smul]
    · have hmem : b σ ∈ U z := hf z (subset_tsupport _ hfz)
      have hcl := hρinv z (σ : AddCircle (1 : ℝ)) hmem
      change (f z (b σ) : ℝ) • Complex.exp (((2 * Real.pi * ρ z (b σ) : ℝ) : ℂ) * Complex.I) = _
      rw [cexp_two_pi_mul_I_eq_of_coe_eq hcl]
  set R : M → AddCircle (1 : ℝ) := fun y =>
    ((Complex.arg (F y) / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) with hR
  have hRb : ∀ s, R (b s) = s := by
    intro s
    induction s using QuotientAddGroup.induction_on with
    | H σ =>
      change ((Complex.arg (F (b σ)) / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) = σ
      rw [hFb σ, Complex.real_smul, Complex.arg_real_mul _ (hsum_pos σ)]
      exact coe_arg_cexp_div_two_pi σ
  refine ⟨R, hRb, fun s => ?_⟩
  obtain ⟨σ, rfl⟩ := QuotientAddGroup.mk_surjective s
  set x : M := b σ with hx
  -- smoothness of `F` at `x`
  have hexp : ContDiff ℝ ∞ (fun τ : ℝ => Complex.exp (((2 * Real.pi * τ : ℝ) : ℂ) * Complex.I)) := by
    have h1 : ContDiff ℝ ∞ (fun τ : ℝ => ((2 * Real.pi * τ : ℝ) : ℂ) * Complex.I) :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const
    exact (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).comp h1
  have hFs : ContMDiffAt I 𝓘(ℝ, ℂ) n F x := by
    refine contMDiffAt_finsetSum fun z _ => ?_
    by_cases hxz : x ∈ U z
    · have hρx : ContMDiffAt I 𝓘(ℝ, ℝ) n (ρ z) x := (hρ z).contMDiffAt ((hUo z).mem_nhds hxz)
      have hGx : ContMDiffAt I 𝓘(ℝ, ℂ) n (G z) x :=
        (hexp.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffAt.comp x hρx
      exact ((f z).contMDiffAt.of_le (by exact_mod_cast le_top)).smul hGx
    · have hxt : x ∉ tsupport ⇑(f z) := fun h => hxz (hf z h)
      have hev : (fun y => (f z y : ℝ) • G z y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxt] with y hy
        rw [hy, Pi.zero_apply, zero_smul]
      exact contMDiffAt_const.congr_of_eventuallyEq hev
  -- the local real lift of `R`
  set u : ℂ := Complex.exp ((((-(2 * Real.pi * σ)) : ℝ) : ℂ) * Complex.I) with hu
  have hwx : F x * u = ((∑ z ∈ t, f z x : ℝ) : ℂ) := by
    rw [hx, hFb σ, Complex.real_smul, mul_assoc, hu, ← Complex.exp_add]
    have : (((2 * Real.pi * σ : ℝ) : ℂ) * Complex.I) +
        ((((-(2 * Real.pi * σ)) : ℝ) : ℂ) * Complex.I) = 0 := by push_cast; ring
    rw [this, Complex.exp_zero, mul_one]
  have hslit : F x * u ∈ Complex.slitPlane := by
    rw [hwx]
    exact Complex.ofReal_mem_slitPlane.mpr (hsum_pos σ)
  have harg : ContDiffAt ℝ n Complex.arg (F x * u) := by
    have hlog : ContDiffAt ℝ n Complex.log (F x * u) :=
      (Complex.contDiffAt_log hslit).restrict_scalars ℝ
    have h1 : ContDiffAt ℝ n (fun w : ℂ => (Complex.log w).im) (F x * u) :=
      Complex.imCLM.contDiff.contDiffAt.comp _ hlog
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
    exact (Complex.log_im w).symm
  have hlift : ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun y => σ + Complex.arg (F y * u) / (2 * Real.pi)) x := by
    have hmulu : ContDiff ℝ ∞ (fun w : ℂ => w * u) := contDiff_id.mul contDiff_const
    have hw : ContMDiffAt I 𝓘(ℝ, ℂ) n (fun y => F y * u) x :=
      (hmulu.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffAt.comp x hFs
    have h2 : ContMDiffAt I 𝓘(ℝ, ℝ) n (fun y => Complex.arg (F y * u)) x :=
      harg.contMDiffAt.comp x hw
    exact contMDiffAt_const.add (h2.div_const _)
  have hFx0 : F x ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hwx
    exact (hsum_pos σ).ne' (by exact_mod_cast hwx.symm)
  have hev : R =ᶠ[𝓝 x] fun y =>
      ((σ + Complex.arg (F y * u) / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) := by
    filter_upwards [hFs.continuousAt.eventually_ne hFx0] with y hy
    exact (coe_arg_mul_cexp_div_two_pi hy σ).symm
  exact ((AddCircle.contMDiff_coe.of_le (by exact_mod_cast le_top)).contMDiffAt.comp x
    hlift).congr_of_eventuallyEq hev

end Gluing

section Descent

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- A map out of `AddCircle 1` is `C^n` as soon as its periodic lift is. -/
theorem contMDiff_addCircle_of_comp_coe {n : ℕ∞} {f : AddCircle (1 : ℝ) → N}
    (hf : ContMDiff 𝓘(ℝ, ℝ) J n (fun t : ℝ => f (t : AddCircle (1 : ℝ)))) :
    ContMDiff 𝓘(ℝ, ℝ) J n f := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hlocal := AddCircle.isLocalDiffeomorph_coe x
  have hsmooth : ContMDiffAt 𝓘(ℝ, ℝ) J n
      ((fun t : ℝ => f (t : AddCircle (1 : ℝ))) ∘ hlocal.localInverse)
      (x : AddCircle (1 : ℝ)) :=
    hf.contMDiffAt.comp _ (hlocal.contMDiffAt_localInverse.of_le (by exact_mod_cast le_top))
  apply hsmooth.congr_of_eventuallyEq
  have h := hlocal.localInverse_eventuallyEq_right.fun_comp f
  simpa only [Function.comp_def, id_eq] using h.symm

end Descent

section BaseCircle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- `2 ≤ r` gives `1 ≤ r - 1` in `ℕ∞`. -/
theorem soulCarrier_one_le_sub_one {k : ℕ∞} (hk : 2 ≤ k) : 1 ≤ k - 1 := by
  induction k using ENat.recTopCoe with
  | top => simp
  | coe m =>
    have hm : 2 ≤ m := by exact_mod_cast hk
    rw [← ENat.natCast_one, ← ENat.natCast_sub]
    exact_mod_cast (by omega : 1 ≤ m - 1)

/-- **BASE-1b** (`2 ≤ r`). The circle carrier `AddCircle 1` of a simple closed geodesic, with the base
contract. -/
theorem soulBase_closedGeodesic
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ) (hunit : g.inner p.proj p.snd p.snd = 1)
    (hper : g.geodesicFlow p ℓ = p) (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) :
    ∃ b : AddCircle (1 : ℝ) → M,
      (∀ t : ℝ, b (t : AddCircle (1 : ℝ)) = (g.geodesicFlow p (ℓ * t)).proj) ∧
      ContMDiff 𝓘(ℝ, ℝ) I ((r - 1 : ℕ∞) : ℕ∞ω) b ∧ Injective b ∧
      range b = range (fun t => (g.geodesicFlow p t).proj) ∧
      ∃ R : M → AddCircle (1 : ℝ), (∀ s, R (b s) = s) ∧
        ∀ x ∈ range (fun t => (g.geodesicFlow p t).proj),
          ContMDiffAt I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) R x := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hP := periodic_geodesicFlow_of_closed g hr1 hD hper
  set γ : ℝ → M := fun t => (g.geodesicFlow p (ℓ * t)).proj with hγdef
  have hγper : Function.Periodic γ 1 := fun t => by
    change (g.geodesicFlow p (ℓ * (t + 1))).proj = (g.geodesicFlow p (ℓ * t)).proj
    rw [mul_add, mul_one]
    exact congrArg Bundle.TotalSpace.proj (hP (ℓ * t))
  set b : AddCircle (1 : ℝ) → M := hγper.lift with hbdef
  have hbcoe : ∀ t : ℝ, b (t : AddCircle (1 : ℝ)) = γ t := fun t => rfl
  set n : ℕ∞ := r - 1 with hn
  have hn1 : 1 ≤ n := soulCarrier_one_le_sub_one hr
  have hγs : ContMDiff 𝓘(ℝ, ℝ) I n γ := by
    have h1 := (contMDiff_proj_geodesicFlow_of_complete g hr hnorm p).of_le
      (show ((n : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) by exact_mod_cast tsub_le_self)
    exact h1.comp (contDiff_const.mul contDiff_id).contMDiff
  have hbs : ContMDiff 𝓘(ℝ, ℝ) I n b := contMDiff_addCircle_of_comp_coe hγs
  have hbinj : Injective b := by
    intro z₁ z₂ h
    induction z₁ using QuotientAddGroup.induction_on with
    | H s =>
    induction z₂ using QuotientAddGroup.induction_on with
    | H t =>
    change γ s = γ t at h
    obtain ⟨k, hk⟩ := (proj_geodesicFlow_eq_iff_of_closed g hr hnorm hℓ hper hinj).1 h
    have hst : s = t + k := by
      have : ℓ * (s - t) = ℓ * k := by linarith
      have := mul_left_cancel₀ hℓ.ne' this
      linarith
    change ((s : ℝ) : AddCircle (1 : ℝ)) = ((t : ℝ) : AddCircle (1 : ℝ))
    rw [hst, coe_add_int_addCircle]
  have hrange : range b = range (fun t => (g.geodesicFlow p t).proj) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      induction z using QuotientAddGroup.induction_on with
      | H t => exact ⟨ℓ * t, rfl⟩
    · rintro ⟨τ, rfl⟩
      refine ⟨((τ / ℓ : ℝ) : AddCircle (1 : ℝ)), ?_⟩
      change (g.geodesicFlow p (ℓ * (τ / ℓ))).proj = _
      rw [mul_div_cancel₀ τ hℓ.ne']
  have hbcont : Continuous b := hbs.continuous
  have hemb := hbcont.isClosedEmbedding hbinj
  -- local left inverses along the circle
  have hloc : ∀ z : AddCircle (1 : ℝ), ∃ U : Set M, IsOpen U ∧ b z ∈ U ∧ ∃ ρ : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) n ρ U ∧
        ∀ z' : AddCircle (1 : ℝ), b z' ∈ U → ((ρ (b z') : ℝ) : AddCircle (1 : ℝ)) = z' := by
    intro z
    obtain ⟨t₀, rfl⟩ := QuotientAddGroup.mk_surjective z
    set V : E := (g.geodesicFlow p (ℓ * t₀)).snd with hV
    have hVd := hasMFDerivAt_proj_geodesicFlow_of_complete g hr hnorm p (ℓ * t₀)
    have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => ℓ * t) t₀
        ((1 : ℝ →L[ℝ] ℝ).smulRight ℓ) := by
      have := ((hasDerivAt_id t₀).const_mul ℓ)
      simp only [mul_one] at this
      exact (hasDerivAt_iff_hasFDerivAt.mp this).hasMFDerivAt
    have hvel : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight (ℓ • V)) := by
      have hc := hVd.comp t₀ hlin
      have hderiv_eq : ((((1 : ℝ →L[ℝ] ℝ).smulRight V).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight ℓ)) : ℝ →L[ℝ] E) = (1 : ℝ →L[ℝ] ℝ).smulRight (ℓ • V) := by
        ext; simp
      exact hc.congr_mfderiv hderiv_eq
    have hV0 : ℓ • V ≠ 0 := by
      refine smul_ne_zero hℓ.ne' ?_
      intro h0
      have h1 := inner_snd_geodesicFlow_eq_one g hr hnorm hunit (ℓ * t₀)
      rw [← hV, h0] at h1
      exact zero_ne_one ((ContinuousLinearMap.map_zero₂ _ _).symm.trans h1)
    obtain ⟨η, hη, U₁, hU₁, hxU₁, ρ, hρ, hρinv⟩ :=
      exists_local_leftInverse_curve hn1 hγs hvel hV0
    have hOopen : IsOpen ((fun t : ℝ => (t : AddCircle (1 : ℝ))) '' Ioo (t₀ - η) (t₀ + η)) :=
      QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
    obtain ⟨V', hV'o, hV'pre⟩ := hemb.isInducing.isOpen_iff.mp hOopen
    refine ⟨U₁ ∩ V', hU₁.inter hV'o, ⟨hxU₁, ?_⟩, ρ, hρ.mono inter_subset_left, ?_⟩
    · change (t₀ : AddCircle (1 : ℝ)) ∈ b ⁻¹' V'
      rw [hV'pre]
      exact mem_image_of_mem _ ⟨by linarith, by linarith⟩
    · intro z' hz'
      have hz'O : z' ∈ b ⁻¹' V' := hz'.2
      rw [hV'pre] at hz'O
      obtain ⟨t', ht', rfl⟩ := hz'O
      rw [hbcoe t', hρinv t' ht']
  obtain ⟨R, hRb, hRs⟩ := exists_leftInverse_addCircle_of_local hbcont hloc
  refine ⟨b, hbcoe, hbs, hbinj, hrange, R, hRb, ?_⟩
  rintro x hx
  rw [← hrange] at hx
  obtain ⟨z, rfl⟩ := hx
  exact hRs z

end BaseCircle

end DifferentialGeometry.Geometry.FiniteSoul
