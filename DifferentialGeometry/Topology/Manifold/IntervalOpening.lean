import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Manifold

private def intervalOpening (b c x : ℝ) : ℝ :=
  x + expNegInvGlue (x - b) / (c - x)

private theorem intervalOpening_eq_self {b c x : ℝ} (hx : x ≤ b) :
    intervalOpening b c x = x := by
  rw [intervalOpening, expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr hx), zero_div, add_zero]

private theorem contDiffOn_intervalOpening (b c : ℝ) :
    ContDiffOn ℝ ∞ (intervalOpening b c) (Iio c) := by
  exact contDiffOn_id.add
    ((expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn.div
      (contDiffOn_const.sub contDiffOn_id) (fun x hx => (sub_pos.mpr hx).ne'))

private theorem hasDerivAt_intervalOpening (b c : ℝ) {x : ℝ} (hx : x < c) :
    HasDerivAt (intervalOpening b c)
      (1 + ((x - b)⁻¹ ^ 2 * expNegInvGlue (x - b) * (c - x) +
        expNegInvGlue (x - b)) / (c - x) ^ 2) x := by
  have he : HasDerivAt expNegInvGlue ((x - b)⁻¹ ^ 2 * expNegInvGlue (x - b)) (x - b) := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 (x - b)
  have hd := (hasDerivAt_id x).add
    ((he.comp x ((hasDerivAt_id x).sub_const b)).div
      ((hasDerivAt_id x).const_sub c) (sub_pos.mpr hx).ne')
  simp only [id_eq, Function.comp_apply] at hd
  convert hd using 1 <;> first | rfl | ring

private theorem deriv_intervalOpening_pos (b c : ℝ) {x : ℝ} (hx : x < c) :
    0 < deriv (intervalOpening b c) x := by
  rw [(hasDerivAt_intervalOpening b c hx).deriv]
  have he := expNegInvGlue.nonneg (x - b)
  have hcx : 0 < c - x := sub_pos.mpr hx
  positivity

private theorem strictMonoOn_intervalOpening (b c : ℝ) :
    StrictMonoOn (intervalOpening b c) (Iio c) := by
  apply strictMonoOn_of_deriv_pos (convex_Iio c) (contDiffOn_intervalOpening b c).continuousOn
  intro x hx
  exact deriv_intervalOpening_pos b c (by simpa only [interior_Iio, mem_Iio] using hx)

private theorem tendsto_intervalOpening_atBot (b c : ℝ) :
    Tendsto (intervalOpening b c) atBot atBot := by
  apply tendsto_id.congr'
  filter_upwards [eventually_le_atBot b] with x hx
  exact (intervalOpening_eq_self hx).symm

private theorem tendsto_intervalOpening_atTop {b c : ℝ} (hbc : b < c) :
    Tendsto (intervalOpening b c) (𝓝[<] c) atTop := by
  have hden : Tendsto (fun x : ℝ => c - x) (𝓝[<] c) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds.sub nhdsWithin_le_nhds :
        Tendsto (fun x : ℝ => c - x) (𝓝[<] c) (𝓝 (c - c)))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (mem_Iio.mp hx)
  have hnum : Tendsto (fun x : ℝ => expNegInvGlue (x - b))
      (𝓝[<] c) (𝓝 (expNegInvGlue (c - b))) :=
    ((expNegInvGlue.contDiff (n := ⊤)).continuous.comp (continuous_id.sub continuous_const)).continuousAt
      |>.tendsto.mono_left nhdsWithin_le_nhds
  have hquot := hnum.pos_mul_atTop (expNegInvGlue.pos_of_pos (sub_pos.mpr hbc))
    (tendsto_inv_nhdsGT_zero.comp hden)
  have hid : Tendsto (fun x : ℝ => x) (𝓝[<] c) (𝓝 c) := nhdsWithin_le_nhds
  change Tendsto (fun x : ℝ => x + expNegInvGlue (x - b) / (c - x)) (𝓝[<] c) atTop
  simpa only [div_eq_mul_inv, Function.comp_apply] using
    hid.add_atTop hquot

private theorem surjOn_intervalOpening {b c : ℝ} (hbc : b < c) :
    SurjOn (intervalOpening b c) (Iio c) univ := by
  intro y hy
  exact isPreconnected_Iio.intermediate_value_Iii (l₁ := atBot) (l₂ := 𝓝[<] c)
    (le_principal_iff.mpr (eventually_lt_atBot c)) inf_le_right
    (contDiffOn_intervalOpening b c).continuousOn
    (tendsto_intervalOpening_atBot b c) (tendsto_intervalOpening_atTop hbc) hy

theorem exists_diffeomorph_Iio_real_eq_self {b c : ℝ} (hbc : b < c) :
    let U : TopologicalSpace.Opens ℝ := ⟨Iio c, isOpen_Iio⟩
    ∃ f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) U ℝ ∞,
      StrictMono f ∧ (∀ x : U, (x : ℝ) ≤ b → f x = x) ∧
        (∀ y : ℝ, y ≤ b → (f.symm y : ℝ) = y) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Iio c, isOpen_Iio⟩
  let : OrderTopology U := inferInstanceAs (OrderTopology (Iio c))
  let F : U → ℝ := fun x => intervalOpening b c x
  have hm : StrictMono F := fun x y hxy =>
    strictMonoOn_intervalOpening b c x.property y.property hxy
  have hs : Function.Surjective F := by
    intro y
    obtain ⟨x, hx, hxy⟩ := surjOn_intervalOpening hbc (mem_univ y)
    exact ⟨⟨x, hx⟩, hxy⟩
  let e : U ≃o ℝ := OrderIso.ofSurjective (OrderEmbedding.ofStrictMono F hm) hs
  let p : OpenPartialHomeomorph ℝ ℝ :=
    { toFun := intervalOpening b c
      invFun := fun y => (e.symm y : ℝ)
      source := Iio c
      target := univ
      map_source' := fun _ _ => mem_univ _
      map_target' := fun y _ => (e.symm y).property
      left_inv' := fun x hx => congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
      right_inv' := fun y _ => e.apply_symm_apply y
      open_source := isOpen_Iio
      open_target := isOpen_univ
      continuousOn_toFun := (contDiffOn_intervalOpening b c).continuousOn
      continuousOn_invFun :=
        (continuous_subtype_val.comp e.toHomeomorph.symm.continuous).continuousOn }
  have hi : ContDiff ℝ ∞ (fun y => (e.symm y : ℝ)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    have hx : (e.symm y : ℝ) < c := (e.symm y).property
    exact p.contDiffAt_symm_deriv (deriv_intervalOpening_pos b c hx).ne'
      (mem_univ y) (hasDerivAt_intervalOpening b c hx).differentiableAt.hasDerivAt
      ((contDiffOn_intervalOpening b c).contDiffAt (Iio_mem_nhds hx))
  let f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) U ℝ ∞ :=
    { toEquiv := e.toEquiv
      contMDiff_toFun := (contDiffOn_intervalOpening b c).contMDiffOn.comp_contMDiff
        contMDiff_subtype_val (fun x => x.property)
      contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff U e.symm).mp hi.contMDiff }
  refine ⟨f, hm, ?_, ?_⟩
  · intro x hx
    exact intervalOpening_eq_self hx
  · intro y hy
    have hfix : f ⟨y, hy.trans_lt hbc⟩ = y := intervalOpening_eq_self hy
    exact congrArg Subtype.val ((f.symm_apply_apply ⟨y, hy.trans_lt hbc⟩).symm.trans
      (congrArg f.symm hfix)) |>.symm

theorem exists_diffeomorph_Ioo_Ioi_eq_self {a b c : ℝ} (hab : a ≤ b) (hbc : b < c) :
    let U : TopologicalSpace.Opens ℝ := ⟨Ioo a c, isOpen_Ioo⟩
    let V : TopologicalSpace.Opens ℝ := ⟨Ioi a, isOpen_Ioi⟩
    ∃ f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) U V ∞,
      StrictMono f ∧ (∀ x : U, (x : ℝ) ≤ b → (f x : ℝ) = x) ∧
        (∀ y : V, (y : ℝ) ≤ b → (f.symm y : ℝ) = y) := by
  let L : TopologicalSpace.Opens ℝ := ⟨Iio c, isOpen_Iio⟩
  let U : TopologicalSpace.Opens ℝ := ⟨Ioo a c, isOpen_Ioo⟩
  let V : TopologicalSpace.Opens ℝ := ⟨Ioi a, isOpen_Ioi⟩
  obtain ⟨f, hm, hfix, hifix⟩ := exists_diffeomorph_Iio_real_eq_self hbc
  have ha : f ⟨a, hab.trans_lt hbc⟩ = a := hfix _ hab
  have hUL : U ≤ L := fun _ hx => hx.2
  have himage (x : U) : a < f ⟨x, x.property.2⟩ := by
    calc
      a = f ⟨a, hab.trans_lt hbc⟩ := ha.symm
      _ < f ⟨x, x.property.2⟩ := hm x.property.1
  have hinv (y : V) : a < (f.symm y : ℝ) := by
    have h : f ⟨a, hab.trans_lt hbc⟩ < f (f.symm y) := by
      rw [ha, f.apply_symm_apply]
      exact y.property
    exact hm.lt_iff_lt.mp h
  let g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) U V ∞ :=
    { toFun := fun x => ⟨f ⟨x, x.property.2⟩, himage x⟩
      invFun := fun y => ⟨f.symm y, hinv y, (f.symm y).property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change (f.symm (f ⟨x.val, x.property.2⟩) : ℝ) = x.val
        exact congrArg (fun z : L => (z : ℝ)) (f.symm_apply_apply ⟨x.val, x.property.2⟩)
      right_inv := by
        intro y
        apply Subtype.ext
        exact f.apply_symm_apply y.val
      contMDiff_toFun := by
        apply (ContMDiff.subtypeVal_comp_iff V _).mp
        exact f.contMDiff.comp (contMDiff_inclusion hUL)
      contMDiff_invFun := by
        apply (ContMDiff.subtypeVal_comp_iff U _).mp
        exact (contMDiff_subtype_val (U := L)).comp
          (f.symm.contMDiff.comp (contMDiff_subtype_val (U := V))) }
  exact ⟨g, (fun x y hxy => hm hxy), (fun x hx => hfix _ hx),
    (fun y hy => hifix _ hy)⟩

end DifferentialGeometry.Manifold
