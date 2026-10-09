import DifferentialGeometry.Topology.Ehresmann.SurfaceIntervalProductEFE
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The circle branch of a slim bundle: a loop of the base gives a circle-valued submersion

Lane S-ZSP04, group G18 (ZSP04 `SlimModel.overCircle`, draft 74 D74-10 / S1). Blueprint
`master207B.tex` ZSP04 (B:6531–6595): "on a circle component [of `D₃`] it gives the actual surface
mapping torus". The tree's circle model of a slim piece is `SlimModel.overCircle`: a smooth
submersion `p : piece → S¹` with an actual embedded fibre over `1` on a piece without boundary.
The monodromy is NOT forced away (no product structure is asserted).

`exists_loop_circle_submersion_ZSP35` (kernel, for any `ProperSmoothSurfaceSubmersion_EFE`): for a
smooth `1`-periodic immersion `γ : ℝ → H` injective on `[0, 1)` whose range is relatively open in
the base `Bs`, the open compact set `O = f⁻¹(range γ)` carries a circle-valued map `p` (total
function, junk off `O`) that is smooth on `O`, has surjective differential at every point of `O`,
and records the base position: `p x = e^{2π i t} ↔ f x = γ t`. Route: near `x₀ ∈ O` pick a chart `i`
of the graph atlas whose region contains `f x₀`; `a = κ_i ∘ γ` has `a' ≠ 0` (from `γ' ≠ 0` and
`γ = ψ_i ∘ a`), hence a smooth local inverse `e`; near `x₀`, `p = exp(2π e(κ_i ∘ f))` (a compact
window argument shows that the points of `range γ` near `γ t₀` are `γ s` with `s` near `t₀`), and
`d(κ_i ∘ f)` is onto by the submersion clause.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Ehresmann

section Analysis

/-- A `1`-periodic function injective on `[0, 1)`: equal values differ by an integer. -/
theorem periodic_eq_int_ZSP35 {α : Type*} {φ : ℝ → α} (hper : Periodic φ 1)
    (hinj : InjOn φ (Ico 0 1)) {t t' : ℝ} (h : φ t = φ t') : ∃ n : ℤ, t = t' + n := by
  refine ⟨⌊t - t'⌋, ?_⟩
  have hs : φ (t' + ⌊t - t'⌋) = φ t' := by
    have := hper.int_mul ⌊t - t'⌋ t'
    simpa using this
  have hf := Int.floor_le (t - t')
  have hl := Int.lt_floor_add_one (t - t')
  have h1 : t ∈ Ico (t' + ⌊t - t'⌋) (t' + ⌊t - t'⌋ + 1) :=
    ⟨by linarith, by linarith⟩
  have h2 : (t' + ⌊t - t'⌋) ∈ Ico (t' + ⌊t - t'⌋) (t' + ⌊t - t'⌋ + 1) :=
    ⟨le_rfl, by linarith⟩
  have := injOn_Ico_of_periodic_EFE hper hinj (t' + ⌊t - t'⌋) h1 h2 (h.trans hs.symm)
  linarith

/-- `Circle.exp (2π t) = Circle.exp (2π t')` iff `t − t'` is an integer. -/
theorem circleExp_eq_iff_ZSP35 {t t' : ℝ} :
    Circle.exp (2 * Real.pi * t) = Circle.exp (2 * Real.pi * t') ↔ ∃ n : ℤ, t = t' + n := by
  rw [Circle.exp_eq_exp]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    apply mul_left_cancel₀ hpi
    linarith
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]; ring⟩

/-- The compact window: the points of `range γ` near `γ t₀` are `γ s` with `s` near `t₀`. -/
theorem exists_window_ZSP35 {H : Type*} [TopologicalSpace H] [T2Space H] {γ : ℝ → H}
    (hc : Continuous γ) (hper : Periodic γ 1) (hinj : InjOn γ (Ico 0 1)) (t₀ δ : ℝ)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    ∃ V : Set H, IsOpen V ∧ γ t₀ ∈ V ∧ ∀ y ∈ V, y ∈ range γ → ∃ s, |s - t₀| < δ ∧ γ s = y := by
  have hA : IsCompact (γ '' Icc (t₀ + δ) (t₀ + 1 - δ)) :=
    isCompact_Icc.image hc
  refine ⟨(γ '' Icc (t₀ + δ) (t₀ + 1 - δ))ᶜ, hA.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨s, hs, hst⟩
    have := injOn_Ico_of_periodic_EFE hper hinj t₀ ⟨by linarith [hs.1], by linarith [hs.2]⟩
      ⟨le_rfl, by linarith⟩ hst
    linarith [hs.1]
  · rintro y hy ⟨s, rfl⟩
    set n : ℤ := ⌊s - t₀ + 1 / 2⌋ with hn
    have hfl := Int.floor_le (s - t₀ + 1 / 2)
    have hlt := Int.lt_floor_add_one (s - t₀ + 1 / 2)
    have hs' : γ (s - n) = γ s := by
      have := hper.sub_int_mul_eq (x := s) n
      simpa using this
    by_cases hcase : |s - n - t₀| < δ
    · exact ⟨s - n, hcase, hs'⟩
    · exfalso
      apply hy
      rcases le_or_gt 0 (s - n - t₀) with hpos | hneg
      · refine ⟨s - n, ⟨?_, ?_⟩, hs'⟩
        · rw [abs_of_nonneg hpos] at hcase
          linarith
        · linarith
      · refine ⟨s - n + 1, ⟨?_, ?_⟩, ?_⟩
        · linarith
        · rw [abs_of_neg hneg] at hcase
          linarith
        · have := hper.sub_int_mul_eq (x := s) (n - 1)
          rw [← hs']
          have h2 : γ (s - n + 1) = γ (s - ((n - 1 : ℤ) : ℝ) * 1) := by
            congr 1
            push_cast
            ring
          rw [h2, this, hs']

/-- The real inverse function theorem in the form used here: a smooth function with nonvanishing
derivative has a smooth local left inverse with nonvanishing derivative. -/
theorem exists_local_inverse_ZSP35 {a : ℝ → ℝ} {t₀ : ℝ} (ha : ContDiffAt ℝ ∞ a t₀)
    (hne : deriv a t₀ ≠ 0) :
    ∃ e : ℝ → ℝ, ContDiffAt ℝ ∞ e (a t₀) ∧ (∀ᶠ t in 𝓝 t₀, e (a t) = t) ∧
      deriv e (a t₀) ≠ 0 := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by decide
  let i : ℝ ≃L[ℝ] ℝ := .unitsEquivAut ℝ (.mk0 _ hne)
  have hfd : HasStrictFDerivAt a i.toContinuousLinearMap t₀ := ha.hasStrictDerivAt hn
  have hf' : HasFDerivAt a (i : ℝ →L[ℝ] ℝ) t₀ := hfd.hasFDerivAt
  refine ⟨ha.localInverse hf' hn, ha.to_localInverse hf' hn,
    (ha.hasStrictFDerivAt' hf' hn).eventually_left_inverse, ?_⟩
  set e := ha.localInverse hf' hn with he
  have hed : DifferentiableAt ℝ e (a t₀) := (ha.to_localInverse hf' hn).differentiableAt hn
  have had : DifferentiableAt ℝ a t₀ := ha.differentiableAt hn
  have hev : (∀ᶠ t in 𝓝 t₀, e (a t) = t) := (ha.hasStrictFDerivAt' hf' hn).eventually_left_inverse
  have hcomp : deriv (e ∘ a) t₀ = 1 := by
    have : (e ∘ a) =ᶠ[𝓝 t₀] id := hev
    rw [this.deriv_eq]
    simp
  rw [deriv_comp t₀ hed had] at hcomp
  intro h0
  rw [h0, zero_mul] at hcomp
  exact zero_ne_one hcomp

end Analysis

section CircleExp

/-- The differential of `s ↦ e^{2π i s}` is bijective (copy of the private lemma of
`Topology/Manifold/AddCircle.lean`). -/
theorem bijective_mfderiv_circleExp_ZSP35 [Fact (Module.finrank ℝ ℂ = 1 + 1)] (t : ℝ) :
    Function.Bijective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t) := by
  set w : Metric.sphere (0 : ℂ) 1 := Circle.exp (2 * Real.pi * t) with hw
  set A := mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ)) w with hA
  set B := mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
    (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t with hB
  set c : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) *
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I) with hcdef
  have hderiv : HasDerivAt
      (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) c t := by
    rw [hcdef]
    have hR : HasDerivAt (fun s : ℝ => 2 * Real.pi * s) (2 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
    exact ((hR.ofReal_comp).mul_const Complex.I).cexp
  have hc : c ≠ 0 := by
    rw [hcdef]
    exact mul_ne_zero (Complex.exp_ne_zero _)
      (mul_ne_zero (by exact_mod_cast (by positivity : (2 : ℝ) * Real.pi ≠ 0))
        Complex.I_ne_zero)
  have hCval : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) t
      = ContinuousLinearMap.toSpanSingleton ℝ c := by
    exact hderiv.hasFDerivAt.hasMFDerivAt.mfderiv
  have hspan : Function.Injective (ContinuousLinearMap.toSpanSingleton ℝ c) := by
    intro x y hxy
    rw [ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.toSpanSingleton_apply] at hxy
    have h : (x - y) • c = 0 := by rw [sub_smul, hxy, sub_self]
    rcases smul_eq_zero.mp h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hc
  have hCwide : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) t) := by
    intro x y hxy
    exact hspan (by rw [← hCval]; exact hxy)
  have hclosure : (fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ)) ∘
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1))
      = fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) := by
    funext s
    rfl
  have hgw : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ)
      (fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ)) w :=
    (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ∞)).mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hft : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1)
      (fun s : ℝ => (Circle.exp (2 * Real.pi * s) : Metric.sphere (0 : ℂ) 1)) t :=
    ((contMDiff_circleExp.comp ((contDiff_const.mul contDiff_id).contMDiff) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞
        (fun s : ℝ => (Circle.exp (2 * Real.pi * s) :
          Metric.sphere (0 : ℂ) 1)))).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hchain : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) t = A.comp B := by
    rw [← hclosure, hA, hB]
    exact mfderiv_comp t hgw hft
  have hBinj : Function.Injective B := fun x y hxy => by
    apply hCwide
    rw [hchain]
    exact congrArg A hxy
  have hfin : Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℝ) t)
      = Module.finrank ℝ (TangentSpace (𝓡 1) w) :=
    (Module.finrank_self ℝ).trans
      ((finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 1)).trans (Fintype.card_fin 1)).symm
  exact ⟨hBinj, (@LinearMap.injective_iff_surjective_of_finrank_eq_finrank ℝ
    (TangentSpace 𝓘(ℝ, ℝ) t) _ _ _ (TangentSpace (𝓡 1) w) _ _
    (inferInstanceAs (FiniteDimensional ℝ ℝ))
    (inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 1))))
    hfin (f := B.toLinearMap)).mp hBinj⟩

end CircleExp

section Differential

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- The differential of `x ↦ e^{2π i e(g x)}` is onto when `dg` is onto and `e' ≠ 0`. -/
theorem surjective_mfderiv_exp_comp_ZSP35 {g : M → ℝ} {e : ℝ → ℝ} {x : M}
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) (hsg : Surjective (mfderiv I 𝓘(ℝ, ℝ) g x))
    (he : DifferentiableAt ℝ e (g x)) (hde : deriv e (g x) ≠ 0) :
    Surjective (mfderiv I (𝓡 1) (fun y => Circle.exp (2 * Real.pi * e (g y))) x) := by
  let _ := (Complex.finrank_real_complex_fact : Fact (Module.finrank ℝ ℂ = 1 + 1))
  have hE : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) (fun s : ℝ => Circle.exp (2 * Real.pi * s))
      (e (g x)) :=
    ((contMDiff_circleExp.comp ((contDiff_const.mul contDiff_id).contMDiff) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (fun s : ℝ => Circle.exp (2 * Real.pi * s)))).mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)
  have heg : MDifferentiableAt I 𝓘(ℝ, ℝ) (e ∘ g) x :=
    (he.mdifferentiableAt).comp x hg
  have h1 := mfderiv_comp (I := I) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓡 1) x hE heg
  have h2 := mfderiv_comp (I := I) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ)) x
    (he.mdifferentiableAt) hg
  have hExp : Surjective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun s : ℝ => Circle.exp (2 * Real.pi * s))
      (e (g x))) := (bijective_mfderiv_circleExp_ZSP35 (e (g x))).2
  have hEe : Surjective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) e (g x)) := by
    rw [mfderiv_eq_fderiv]
    intro w
    let w' : ℝ := w
    refine ⟨w' / deriv e (g x), ?_⟩
    change (fderiv ℝ e (g x)) (w' / deriv e (g x)) = w'
    rw [fderiv_eq_smul_deriv, smul_eq_mul]
    field_simp
  change Surjective (mfderiv I (𝓡 1) ((fun s : ℝ => Circle.exp (2 * Real.pi * s)) ∘ (e ∘ g)) x)
  rw [h1, h2]
  exact hExp.comp (hEe.comp hsg)

end Differential

section Main

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}

/-- **A loop of the base gives a circle-valued submersion over its preimage** (S1, draft 74
D74-10; the form of `SlimModel.overCircle`): for a smooth `1`-periodic immersion `γ` of the base
`Bs`, injective on `[0, 1)`, whose range is relatively open in `Bs`, the preimage
`O = f⁻¹(range γ)` of a proper smooth submersion is open and compact, and there is `p : M → S¹`
(junk off `O`) smooth on `O`, with surjective differential at every point of `O`, such that
`p x = e^{2π i t} ↔ f x = γ t`. -/
theorem exists_loop_circle_submersion_ZSP35
    (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs) {γ : ℝ → H}
    (hs : ContDiff ℝ ∞ γ) (hper : Periodic γ 1) (hinj : InjOn γ (Ico 0 1))
    (hd : ∀ t, deriv γ t ≠ 0) (hrel : ∃ G : Set H, IsOpen G ∧ G ∩ Bs = range γ) :
    IsOpen (P.toFun ⁻¹' range γ) ∧ IsCompact (P.toFun ⁻¹' range γ) ∧
      ∃ p : M → Circle, ContMDiffOn I (𝓡 1) ∞ p (P.toFun ⁻¹' range γ) ∧
        (∀ x ∈ P.toFun ⁻¹' range γ, Surjective (mfderiv I (𝓡 1) p x)) ∧
        ∀ x ∈ P.toFun ⁻¹' range γ, ∀ t : ℝ,
          p x = Circle.exp (2 * Real.pi * t) ↔ P.toFun x = γ t := by
  classical
  obtain ⟨G, hG, hGB⟩ := hrel
  have hsub : range γ ⊆ Bs := fun y hy => (hGB.symm ▸ hy : y ∈ G ∩ Bs).2
  have hOopen : IsOpen (P.toFun ⁻¹' range γ) := by
    have : P.toFun ⁻¹' range γ = P.toFun ⁻¹' (G ∩ Bs) := by rw [hGB]
    rw [this, preimage_inter]
    exact (hG.preimage P.smooth.continuous).inter P.isOpen_source
  have hOc : IsCompact (P.toFun ⁻¹' range γ) :=
    P.proper _ (hper.compact_of_continuous one_ne_zero hs.continuous) hsub
  refine ⟨hOopen, hOc, ?_⟩
  let p : M → Circle := fun x => if h : x ∈ P.toFun ⁻¹' range γ then
    Circle.exp (2 * Real.pi * Classical.choose (show ∃ t, γ t = P.toFun x from h)) else 1
  have hspec : ∀ x, x ∈ P.toFun ⁻¹' range γ → ∀ t, γ t = P.toFun x →
      p x = Circle.exp (2 * Real.pi * t) := by
    intro x hx t ht
    have hp : p x = Circle.exp (2 * Real.pi *
        Classical.choose (show ∃ t, γ t = P.toFun x from hx)) := by
      simp only [p, hx, ↓reduceDIte]
    rw [hp]
    have hc := Classical.choose_spec (show ∃ t, γ t = P.toFun x from hx)
    exact circleExp_eq_iff_ZSP35.mpr (periodic_eq_int_ZSP35 hper hinj (hc.trans ht.symm))
  have hiff : ∀ x, x ∈ P.toFun ⁻¹' range γ → ∀ t : ℝ,
      p x = Circle.exp (2 * Real.pi * t) ↔ P.toFun x = γ t := by
    intro x hx t
    obtain ⟨s, hsx⟩ := hx
    rw [hspec x ⟨s, hsx⟩ s hsx, circleExp_eq_iff_ZSP35, ← hsx]
    constructor
    · rintro ⟨n, hn⟩
      rw [hn]
      simpa using hper.int_mul n t
    · intro h
      exact periodic_eq_int_ZSP35 hper hinj h
  have hlocal : ∀ x₀, x₀ ∈ P.toFun ⁻¹' range γ → ∃ q : M → Circle,
      ContMDiffAt I (𝓡 1) ∞ q x₀ ∧ p =ᶠ[𝓝 x₀] q ∧ Surjective (mfderiv I (𝓡 1) q x₀) := by
    intro x₀ hx₀
    obtain ⟨t₀, ht₀⟩ := hx₀
    have hfB : P.toFun x₀ ∈ Bs := hsub ⟨t₀, ht₀⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (P.region_cover hfB)
    set κ := P.atlas.coord i with hκ
    set a : ℝ → ℝ := fun t => κ (γ t) with ha_def
    have ha : ContDiff ℝ ∞ a := κ.contDiff.comp hs
    have hW₀ : IsOpen (γ ⁻¹' P.region i) := (P.isOpen_region i).preimage hs.continuous
    have ht₀W : t₀ ∈ γ ⁻¹' P.region i := by
      change γ t₀ ∈ P.region i
      rw [ht₀]
      exact hi
    have hpar : ∀ t ∈ γ ⁻¹' P.region i, γ t = P.atlas.param i (a t) := by
      intro t ht
      obtain ⟨b, hb, hbt⟩ := P.region_piece i ⟨ht, hsub ⟨t, rfl⟩⟩
      have hab : a t = b := by
        change κ (γ t) = b
        rw [← hbt]
        exact P.atlas.coord_param i b hb
      rw [hab, hbt]
    have hat₀ : a t₀ ∈ P.atlas.dom i := by
      obtain ⟨b, hb, hbt⟩ := P.region_piece i ⟨ht₀W, hsub ⟨t₀, rfl⟩⟩
      have hab : a t₀ = b := by
        change κ (γ t₀) = b
        rw [← hbt]
        exact P.atlas.coord_param i b hb
      rw [hab]
      exact hb
    have hdp : DifferentiableAt ℝ (P.atlas.param i) (a t₀) :=
      (((P.atlas.param_smooth i).contDiffAt
        ((P.atlas.isOpen_dom i).mem_nhds hat₀)).differentiableAt (by decide))
    have hadiff : HasDerivAt a (deriv a t₀) t₀ :=
      ((ha.differentiable (by decide)) t₀).hasDerivAt
    have hscomp := hdp.hasDerivAt.scomp t₀ hadiff
    have hγev : γ =ᶠ[𝓝 t₀] (P.atlas.param i) ∘ a :=
      Filter.eventually_of_mem (hW₀.mem_nhds ht₀W) hpar
    have hγd : HasDerivAt γ (deriv a t₀ • deriv (P.atlas.param i) (a t₀)) t₀ :=
      hscomp.congr_of_eventuallyEq hγev
    have hne : deriv a t₀ ≠ 0 := by
      intro h0
      apply hd t₀
      rw [hγd.deriv, h0, zero_smul]
    obtain ⟨e, he, hev, hde⟩ := exists_local_inverse_ZSP35 ha.contDiffAt hne
    obtain ⟨ε, hε, hεt⟩ := Metric.eventually_nhds_iff.mp hev
    set δ : ℝ := min ε (1 / 4) with hδ
    have hδpos : 0 < δ := lt_min hε (by norm_num)
    obtain ⟨V, hV, hγV, hVwin⟩ := exists_window_ZSP35 hs.continuous hper hinj t₀ δ hδpos
      (min_le_right _ _)
    set g : M → ℝ := fun x => κ (P.toFun x) with hg_def
    have hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := κ.contDiff.comp_contMDiff P.smooth
    have hga : g x₀ = a t₀ := by
      change κ (P.toFun x₀) = κ (γ t₀)
      rw [ht₀]
    have hex : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (fun s : ℝ => Circle.exp (2 * Real.pi * s)) :=
      contMDiff_circleExp.comp ((contDiff_const.mul contDiff_id).contMDiff)
    have heg : ContDiffAt ℝ ∞ e (g x₀) := hga ▸ he
    refine ⟨fun x => Circle.exp (2 * Real.pi * e (g x)), ?_, ?_, ?_⟩
    · exact (hex.contMDiffAt).comp x₀ (heg.comp_contMDiffAt hg.contMDiffAt)
    · have hN : (P.toFun ⁻¹' range γ) ∩ P.toFun ⁻¹' V ∈ 𝓝 x₀ := by
        refine (hOopen.inter (hV.preimage P.smooth.continuous)).mem_nhds ⟨⟨t₀, ht₀⟩, ?_⟩
        change P.toFun x₀ ∈ V
        rw [← ht₀]
        exact hγV
      refine Filter.eventually_of_mem hN fun x hx => ?_
      obtain ⟨s, hsδ, hsx⟩ := hVwin (P.toFun x) hx.2 hx.1
      have hes : e (a s) = s := hεt (by
        rw [Real.dist_eq]
        exact lt_of_lt_of_le hsδ (min_le_left _ _))
      have hgx : g x = a s := by
        change κ (P.toFun x) = κ (γ s)
        rw [hsx]
      change p x = Circle.exp (2 * Real.pi * e (g x))
      rw [hgx, hes]
      exact hspec x hx.1 s hsx
    · refine surjective_mfderiv_exp_comp_ZSP35 (hg.contMDiffAt.mdifferentiableAt (by decide))
        ?_ (heg.differentiableAt (by decide)) (by rw [hga]; exact hde)
      exact P.submersion i x₀ ⟨hi, hfB⟩
  refine ⟨p, ?_, ?_, hiff⟩
  · intro x hx
    obtain ⟨q, hq, hpq, -⟩ := hlocal x hx
    exact (hq.congr_of_eventuallyEq hpq).contMDiffWithinAt
  · intro x hx
    obtain ⟨q, -, hpq, hsq⟩ := hlocal x hx
    have h1 : mfderiv I (𝓡 1) p x = mfderiv I (𝓡 1) q x := hpq.mfderiv_eq
    rw [h1]
    exact hsq

end Main

end DifferentialGeometry.Topology.Ehresmann
