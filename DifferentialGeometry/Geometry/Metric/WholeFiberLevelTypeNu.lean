import DifferentialGeometry.Geometry.Metric.WholeFiberLevelType
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# GAF07's fibre type with the source measured by a pointwise norm (`R_i⁻²g`)

Blueprint `master207B.tex`, GAF07 (B:6111–6137): the original coordinate `η_i` has a right inverse
of bounded norm and `‖Dg_i − Dη_i‖ < c₃`, both "with source norm in `R_i⁻²g`" — a Riemannian norm on
each tangent space, not the model-space norm of the charts. `WholeFiberLevelType.lean` states the
straight-line argument with the model-space operator norm; this module states it for an arbitrary
pointwise gauge `ν y : E → ℝ` (for instance `ν y v = √(R⁻²g_y(v, v))`), with a right inverse
`ν(R w) ≤ K‖w‖` and `‖Dg v − Dη v‖ ≤ c ν(v)`, `cK < 1`. Only these two inequalities enter the
perturbation argument, so nothing about `ν` (not even a norm property) is needed.

* `surjective_of_right_inverse_perturbation_nu_GAFC`: the linear algebra.
* `straightLine_slice_regular_nu_GAFC`: every slice of `h_τ = (1 − τ)η + τg` is a submersion.
* `nonempty_homeomorph_level_of_straightLine_nu_GAFC`: FC34a — the whole level `{g = a}` is
  homeomorphic to `{η = a}` (`‖a‖ < 4ℓ`, `‖g − η‖ < 1/800`, `{‖η‖ ≤ 4.01ℓ}` compact).
* `nonempty_homeomorph_level_on_open_GAFC`: the same on an open subset `U` of a manifold `M`
  (`η, g` smooth on `U`, the hypotheses on `U`), stated with subsets of `M`.
-/

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold

namespace GC.MetricGeometry

/-- A perturbation of an operator with a right inverse stays surjective, measured by a pointwise
gauge `ν` on the source: `ν(R w) ≤ K‖w‖`, `‖T' v − T v‖ ≤ c ν(v)`, `cK < 1`. -/
theorem surjective_of_right_inverse_perturbation_nu_GAFC {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (T T' : E →L[ℝ] F) (R : F →L[ℝ] E) (hTR : T.comp R = ContinuousLinearMap.id ℝ F)
    (ν : E → ℝ) {c K : ℝ} (hR : ∀ w, ν (R w) ≤ K * ‖w‖) (hd : ∀ v, ‖T' v - T v‖ ≤ c * ν v)
    (hc : 0 ≤ c) (hcK : c * K < 1) : Surjective T' := by
  let S : F →L[ℝ] F := T'.comp R
  have hinj : Injective (S : F →ₗ[ℝ] F) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : T' (R v) = 0 := hv
    have hTv : T (R v) = v := by
      have h := congrArg (fun A : F →L[ℝ] F => A v) hTR
      simpa using h
    have h1 : ‖v‖ ≤ c * ν (R v) := by
      have h := hd (R v)
      rwa [hv', hTv, zero_sub, norm_neg] at h
    have h2 : c * ν (R v) ≤ c * (K * ‖v‖) := mul_le_mul_of_nonneg_left (hR v) hc
    by_contra hne
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hne
    have h3 : c * K * ‖v‖ < 1 * ‖v‖ := mul_lt_mul_of_pos_right hcK hpos
    have h4 : c * (K * ‖v‖) = c * K * ‖v‖ := by ring
    linarith
  have hsurj : Surjective (S : F →ₗ[ℝ] F) := LinearMap.injective_iff_surjective.mp hinj
  intro y
  obtain ⟨w, hw⟩ := hsurj y
  exact ⟨R w, hw⟩

variable {E F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Y] [ChartedSpace H Y]

/-- Every slice of the straight-line family is a submersion, with the source gauge `ν`. -/
theorem straightLine_slice_regular_nu_GAFC [FiniteDimensional ℝ F] {η g : Y → F}
    (hη : ContMDiff I 𝓘(ℝ, F) ∞ η) (hg : ContMDiff I 𝓘(ℝ, F) ∞ g) (ν : Y → E → ℝ) {c K : ℝ}
    (hc : 0 ≤ c) (hcK : c * K < 1)
    (hright : ∀ y, ∃ R : F →L[ℝ] E,
      (mfderiv I 𝓘(ℝ, F) η y : E →L[ℝ] F).comp R = ContinuousLinearMap.id ℝ F ∧
        ∀ w, ν y (R w) ≤ K * ‖w‖)
    (hDg : ∀ y (v : E), ‖(show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) g y) v -
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) η y) v‖ ≤ c * ν y v) :
    ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y : Y,
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => (1 - τ) • η z + τ • g z) y) := by
  intro τ hτ y
  have hηd : HasMFDerivAt I 𝓘(ℝ, F) η y (mfderiv I 𝓘(ℝ, F) η y) :=
    (hη.mdifferentiableAt (by simp)).hasMFDerivAt
  have hgd : HasMFDerivAt I 𝓘(ℝ, F) g y (mfderiv I 𝓘(ℝ, F) g y) :=
    (hg.mdifferentiableAt (by simp)).hasMFDerivAt
  have hd := (hηd.const_smul (1 - τ)).add (hgd.const_smul τ)
  rw [show (fun z => (1 - τ) • η z + τ • g z) = (1 - τ) • η + τ • g from rfl, hd.mfderiv]
  obtain ⟨R, hR, hRn⟩ := hright y
  set Dη : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) η y
  set Dg : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) g y
  refine surjective_of_right_inverse_perturbation_nu_GAFC Dη ((1 - τ) • Dη + τ • Dg) R hR (ν y)
    hRn (fun v => ?_) hc hcK
  have hdiff : ((1 - τ) • Dη + τ • Dg) v - Dη v = τ • (Dg v - Dη v) := by
    have hap : ((1 - τ) • Dη + τ • Dg) v = (1 - τ) • Dη v + τ • Dg v := rfl
    rw [hap, sub_smul, one_smul, smul_sub]
    abel
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
  have h1 := hDg y v
  have h0 : 0 ≤ ‖Dg v - Dη v‖ := norm_nonneg _
  calc τ * ‖Dg v - Dη v‖ ≤ 1 * ‖Dg v - Dη v‖ := mul_le_mul_of_nonneg_right hτ.2 h0
    _ ≤ c * ν y v := by rw [one_mul]; exact h1

variable [IsManifold I ∞ Y] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless]
  [T2Space Y] [SigmaCompactSpace Y]

/-- **GAF07 fibre type, gauge form**: with `‖g − η‖ < 1/800`, a right inverse of `Dη` with
`ν(R w) ≤ K‖w‖`, `‖Dg v − Dη v‖ ≤ cν(v)`, `cK < 1`, `‖a‖ < 4ℓ` and `{‖η‖ ≤ 4.01ℓ}` compact, the
WHOLE adjusted level `{g = a}` is homeomorphic (FC34a: diffeomorphic) to the original level
`{η = a}`. -/
theorem nonempty_homeomorph_level_of_straightLine_nu_GAFC {η g : Y → F}
    (hη : ContMDiff I 𝓘(ℝ, F) ∞ η) (hg : ContMDiff I 𝓘(ℝ, F) ∞ g) {a : F} {ℓ : ℝ}
    (hℓ : 1 ≤ ℓ) (ha : ‖a‖ < 4 * ℓ) (hgη : ∀ y, ‖g y - η y‖ < 1 / 800) (ν : Y → E → ℝ)
    {c K : ℝ} (hc : 0 ≤ c) (hcK : c * K < 1)
    (hright : ∀ y, ∃ R : F →L[ℝ] E,
      (mfderiv I 𝓘(ℝ, F) η y : E →L[ℝ] F).comp R = ContinuousLinearMap.id ℝ F ∧
        ∀ w, ν y (R w) ≤ K * ‖w‖)
    (hDg : ∀ y (v : E), ‖(show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) g y) v -
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) η y) v‖ ≤ c * ν y v)
    (hQ : IsCompact {y | ‖η y‖ ≤ 401 / 100 * ℓ}) :
    Nonempty ({y | η y = a} ≃ₜ {y | g y = a}) := by
  let h : Y × ℝ → F := fun x => (1 - x.2) • η x.1 + x.2 • g x.1
  have hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h := contMDiff_straightLine hη hg
  have hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y) :=
    fun τ hτ y _ => straightLine_slice_regular_nu_GAFC hη hg ν hc hcK hright hDg τ hτ y
  have hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → y ∈ {y | ‖η y‖ ≤ 401 / 100 * ℓ} :=
    fun τ hτ y hy => (norm_lt_of_level_of_straight_line hτ hℓ ha (hgη y) hy).le
  let _ := regularFiberChartedSpace (fun y => h (y, 0)) a (contMDiff_familySlice hh 0)
    (hreg 0 (left_mem_Icc.mpr zero_le_one))
  let _ := regularFiberChartedSpace (fun y => h (y, 1)) a (contMDiff_familySlice hh 1)
    (hreg 1 (right_mem_Icc.mpr zero_le_one))
  obtain ⟨φ⟩ := nonempty_diffeomorph_levelSet_of_compact_transport h hh a hreg hQ hloc
  have h0 : {y | h (y, 0) = a} = {y | η y = a} := by
    ext y
    change (1 - 0 : ℝ) • η y + (0 : ℝ) • g y = a ↔ η y = a
    rw [sub_zero, one_smul, zero_smul, add_zero]
  have h1 : {y | h (y, 1) = a} = {y | g y = a} := by
    ext y
    change (1 - 1 : ℝ) • η y + (1 : ℝ) • g y = a ↔ g y = a
    rw [sub_self, zero_smul, one_smul, zero_add]
  exact ⟨((Homeomorph.setCongr h0).symm.trans φ.toHomeomorph).trans (Homeomorph.setCongr h1)⟩

section Open

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- A level set inside an open set `U`, as a subset of `M` and as a level set of the restriction to
the open subtype `U`. -/
def levelOpenHomeomorph_GAFC (U : TopologicalSpace.Opens M) (f : M → F) (a : F) :
    {y | y ∈ U ∧ f y = a} ≃ₜ {y : U | f y = a} where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun y := ⟨y.1.1, y.1.2, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

variable [FiniteDimensional ℝ F] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [LocallyCompactSpace M] [SecondCountableTopology M]

/-- **GAF07 fibre type on an open set, gauge form**: for `η, g` smooth on an open `U ⊆ M` with the
hypotheses of `nonempty_homeomorph_level_of_straightLine_nu_GAFC` on `U` and the slab
`{y ∈ U | ‖η y‖ ≤ 4.01ℓ}` compact, the whole adjusted level `{y ∈ U | g y = a}` is homeomorphic to
the original level `{y ∈ U | η y = a}`. -/
theorem nonempty_homeomorph_level_on_open_GAFC {U : Set M} (hU : IsOpen U) {η g : M → F}
    (hη : ContMDiffOn I 𝓘(ℝ, F) ∞ η U) (hg : ContMDiffOn I 𝓘(ℝ, F) ∞ g U) {a : F} {ℓ : ℝ}
    (hℓ : 1 ≤ ℓ) (ha : ‖a‖ < 4 * ℓ) (hgη : ∀ y ∈ U, ‖g y - η y‖ < 1 / 800) (ν : M → E → ℝ)
    {c K : ℝ} (hc : 0 ≤ c) (hcK : c * K < 1)
    (hright : ∀ y ∈ U, ∃ R : F →L[ℝ] E,
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) η y).comp R = ContinuousLinearMap.id ℝ F ∧
        ∀ w, ν y (R w) ≤ K * ‖w‖)
    (hDg : ∀ y ∈ U, ∀ v : E, ‖(show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) g y) v -
      (show E →L[ℝ] F from mfderiv I 𝓘(ℝ, F) η y) v‖ ≤ c * ν y v)
    (hQ : IsCompact {y | y ∈ U ∧ ‖η y‖ ≤ 401 / 100 * ℓ}) :
    Nonempty ({y | y ∈ U ∧ η y = a} ≃ₜ {y | y ∈ U ∧ g y = a}) := by
  let V : TopologicalSpace.Opens M := ⟨U, hU⟩
  have : LocallyCompactSpace V := hU.locallyCompactSpace
  have hηV : ContMDiff I 𝓘(ℝ, F) ∞ (fun y : V => η y) :=
    hη.comp_contMDiff (contMDiff_subtype_val (I := I)) (fun y => y.2)
  have hgV : ContMDiff I 𝓘(ℝ, F) ∞ (fun y : V => g y) :=
    hg.comp_contMDiff (contMDiff_subtype_val (I := I)) (fun y => y.2)
  have hder : ∀ (f : M → F) (y : V),
      mfderiv I 𝓘(ℝ, F) (fun z : V => f z) y = mfderiv I 𝓘(ℝ, F) f y :=
    fun f y => DifferentialGeometry.mfderiv_restrict_open f V y
  have hQV : IsCompact {y : V | ‖η y‖ ≤ 401 / 100 * ℓ} := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hQ using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hxη⟩
      exact ⟨⟨x, hx⟩, hxη, rfl⟩
  obtain ⟨φ⟩ := nonempty_homeomorph_level_of_straightLine_nu_GAFC hηV hgV hℓ ha
    (fun y => hgη y y.2) (fun y => ν y) hc hcK
    (fun y => by
      obtain ⟨R, hR, hRw⟩ := hright y y.2
      refine ⟨R, ?_, hRw⟩
      rw [hder]
      exact hR)
    (fun y v => by
      rw [hder, hder]
      exact hDg y y.2 v) hQV
  exact ⟨((levelOpenHomeomorph_GAFC V η a).trans φ).trans
    (levelOpenHomeomorph_GAFC V g a).symm⟩

end Open

end GC.MetricGeometry
