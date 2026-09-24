import DifferentialGeometry.Topology.Compactness.ExtremaConvergence
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.Viscosity

private theorem square_second_derivative_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : E → ℝ} {x : E} (hq : ContDiffAt ℝ 2 q x)
    (hq0 : q x = 0) (hqD : fderiv ℝ q x = 0) :
    fderiv ℝ (fderiv ℝ (fun y => q y ^ 2)) x = 0 := by
  have hqd : DifferentiableAt ℝ q x := hq.differentiableAt (by norm_num)
  have hqdd : DifferentiableAt ℝ (fderiv ℝ q) x :=
    (hq.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y => q y ^ 2) =ᶠ[𝓝 x]
      fun y => q y • fderiv ℝ q y + q y • fderiv ℝ q y := by
    filter_upwards [hq.eventually (by norm_num)] with y hy
    have hyd := hy.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    simpa only [pow_two] using (hyd.hasFDerivAt.fun_mul hyd.hasFDerivAt).fderiv
  rw [heq.fderiv_eq]
  have hd := hqd.hasFDerivAt.fun_smul hqdd.hasFDerivAt
  have hz : HasFDerivAt (fun y => q y • fderiv ℝ q y)
      (0 : E →L[ℝ] (E →L[ℝ] ℝ)) x := by
    simpa only [hq0, hqD, zero_smul, ContinuousLinearMap.smulRight_zero, add_zero] using hd
  simpa only [add_zero] using (hz.fun_add hz).fderiv

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {l : Filter ι} [l.NeBot]
  {U : Set E} {F : ι → E → ℝ} {f : E → ℝ}
  {Hn : ι → E → ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ}
  {H : E → ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ}

theorem upper_test_le_of_tendstoLocallyUniformlyOn
    (hU : IsOpen U) (hF : ∀ᶠ i in l, ContinuousOn (F i) U)
    (hconv : TendstoLocallyUniformlyOn F f l U)
    (hH : ContinuousOn (fun z : E × ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) =>
      H z.1 z.2.1 z.2.2.1 z.2.2.2) (U ×ˢ univ))
    (hHconv : TendstoLocallyUniformlyOn
      (fun i (z : E × ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ)) => Hn i z.1 z.2.1 z.2.2.1 z.2.2.2)
      (fun z => H z.1 z.2.1 z.2.2.1 z.2.2.2) l (U ×ˢ univ))
    (hsub : ∀ᶠ i in l, ∀ x, x ∈ U → ∀ phi : E → ℝ, ContDiffAt ℝ 2 phi x →
      IsLocalMax (fun y => F i y - phi y) x →
        Hn i x (F i x) (fderiv ℝ phi x) (fderiv ℝ (fderiv ℝ phi) x) ≤ 0)
    {x : E} (hx : x ∈ U) (phi : E → ℝ) (hphi : ContDiffAt ℝ 2 phi x)
    (hmax : IsLocalMax (fun y => f y - phi y) x) :
    H x (f x) (fderiv ℝ phi x) (fderiv ℝ (fderiv ℝ phi) x) ≤ 0 := by
  let _ : ProperSpace E := FiniteDimensional.proper ℝ E
  have hn : ∀ᶠ y in 𝓝 x,
      y ∈ U ∧ f y - phi y ≤ f x - phi x ∧ ContDiffAt ℝ 2 phi y :=
    (show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hx).and
      (hmax.and (hphi.eventually (by norm_num)))
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  let K := Metric.closedBall x r
  have hK : IsCompact K := isCompact_closedBall x r
  have hxK : K ∈ 𝓝 x := Metric.closedBall_mem_nhds x hr
  have hKU : K ⊆ U := fun y hy => (hrsub hy).1
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFunL.trans (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ E))).symm
  let q : E → ℝ := fun y => ‖e (y - x)‖ ^ 2
  let psi : E → ℝ := fun y => phi y + q y ^ 2
  have hq : ContDiff ℝ 2 q :=
    (contDiff_norm_sq ℝ).comp (e.contDiff.comp (contDiff_id.sub contDiff_const))
  have hpen : ContDiff ℝ 2 (fun y => q y ^ 2) := hq.pow 2
  have hpsi (y : E) (hy : y ∈ K) : ContDiffAt ℝ 2 psi y :=
    (hrsub hy).2.2.add hpen.contDiffAt
  have hstrict : ∀ y ∈ K, y ≠ x → f y - psi y < f x - psi x := by
    intro y hy hyx
    have hne : e (y - x) ≠ 0 := by
      intro he
      apply hyx
      exact sub_eq_zero.mp (e.injective (he.trans e.map_zero.symm))
    have hpos : 0 < ‖e (y - x)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
    have hle := (hrsub hy).2.1
    have hpos2 : 0 < q y ^ 2 := sq_pos_of_pos hpos
    dsimp only [psi, q] at *
    simp only [sub_self, map_zero, norm_zero, zero_pow two_ne_zero, add_zero]
    linarith
  have hcompact := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hconv.mono hKU)
  have hpsiC : ContinuousOn psi K := fun y hy => (hpsi y hy).continuousAt.continuousWithinAt
  have hconst : TendstoUniformlyOn (fun _ : ι => psi) psi l K := by
    intro V hV
    exact Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hV)
  obtain ⟨z, hz, hzmax, hzlocal⟩ := hK.exists_tendsto_isLocalMax_of_tendstoUniformlyOn hxK
    (hF.mono fun _ hi => (hi.mono hKU).sub hpsiC) hstrict
    (hcompact.sub hconst)
  have hqD : HasFDerivAt q (0 : E →L[ℝ] ℝ) x := by
    have heD := e.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x)
    have hh := (hasStrictFDerivAt_norm_sq (e (x - x))).hasFDerivAt.comp x
      (f := fun y => e (y - x)) heD
    simpa only [Function.comp_def, sub_self, map_zero,
      smul_zero, ContinuousLinearMap.zero_comp] using hh
  have hq0 : q x = 0 := by simp only [q, sub_self, map_zero, norm_zero, zero_pow two_ne_zero]
  have hpenD : HasFDerivAt (fun y => q y ^ 2) (0 : E →L[ℝ] ℝ) x := by
    simpa only [pow_two, hq0, zero_smul, add_zero] using hqD.fun_mul hqD
  have hpenDD : fderiv ℝ (fderiv ℝ (fun y => q y ^ 2)) x = 0 :=
    square_second_derivative_eq_zero hq.contDiffAt hq0 hqD.fderiv
  have hderiv : fderiv ℝ psi x = fderiv ℝ phi x := by
    have h : HasFDerivAt psi (fderiv ℝ phi x + 0) x :=
      (hphi.differentiableAt (by norm_num)).hasFDerivAt.add hpenD
    simpa only [add_zero] using h.fderiv
  have hsecond : fderiv ℝ (fderiv ℝ psi) x = fderiv ℝ (fderiv ℝ phi) x := by
    have heq : fderiv ℝ psi =ᶠ[𝓝 x]
        fun y => fderiv ℝ phi y + fderiv ℝ (fun z => q z ^ 2) y := by
      filter_upwards [hphi.eventually (by norm_num)] with y hy
      exact fderiv_fun_add (hy.differentiableAt (by norm_num))
        (hpen.differentiable (by norm_num) y)
    rw [heq.fderiv_eq, fderiv_fun_add
      ((hphi.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num))
      ((hpen.contDiffAt.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)),
      hpenDD, add_zero]
  have hgrad : Tendsto (fun i => fderiv ℝ psi (z i)) l (𝓝 (fderiv ℝ phi x)) := by
    rw [← hderiv]
    exact ((hphi.add hpen.contDiffAt).continuousAt_fderiv (by norm_num)).tendsto.comp hz
  have hhess : Tendsto (fun i => fderiv ℝ (fderiv ℝ psi) (z i)) l
      (𝓝 (fderiv ℝ (fderiv ℝ phi) x)) := by
    rw [← hsecond]
    exact (((hphi.add hpen.contDiffAt).fderiv_right
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuousAt_fderiv (by norm_num)).tendsto.comp hz
  have hzU : Tendsto z l (𝓝[U] x) := tendsto_nhdsWithin_iff.mpr
    ⟨hz, hzmax.mono (fun _ hi => hKU hi.1)⟩
  have hf : ContinuousOn f U := hconv.continuousOn hF.frequently
  have hvalue : Tendsto (fun i => F i (z i)) l (𝓝 (f x)) := hconv.tendsto_comp (hf x hx) hx hzU
  have hjets : Tendsto (fun i => (z i, F i (z i), fderiv ℝ psi (z i), fderiv ℝ (fderiv ℝ psi) (z i))) l
      (𝓝[U ×ˢ univ] (x, f x, fderiv ℝ phi x, fderiv ℝ (fderiv ℝ phi) x)) := tendsto_nhdsWithin_iff.mpr
    ⟨hz.prodMk_nhds (hvalue.prodMk_nhds (hgrad.prodMk_nhds hhess)),
      hzmax.mono (fun _ hi => ⟨hKU hi.1, mem_univ _⟩)⟩
  have hlimit := hHconv.tendsto_comp (hH (x, f x, fderiv ℝ phi x, fderiv ℝ (fderiv ℝ phi) x) ⟨hx, mem_univ _⟩)
    ⟨hx, mem_univ _⟩ hjets
  apply le_of_tendsto hlimit
  filter_upwards [hzlocal, hsub, hzmax] with i hi hsubi hzi
  exact hsubi (z i) (hKU hzi.1) psi (hpsi _ hzi.1) hi

theorem lower_test_ge_of_tendstoLocallyUniformlyOn
    (hU : IsOpen U) (hF : ∀ᶠ i in l, ContinuousOn (F i) U)
    (hconv : TendstoLocallyUniformlyOn F f l U)
    (hH : ContinuousOn (fun z : E × ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) =>
      H z.1 z.2.1 z.2.2.1 z.2.2.2) (U ×ˢ univ))
    (hHconv : TendstoLocallyUniformlyOn
      (fun i (z : E × ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ)) => Hn i z.1 z.2.1 z.2.2.1 z.2.2.2)
      (fun z => H z.1 z.2.1 z.2.2.1 z.2.2.2) l (U ×ˢ univ))
    (hsuper : ∀ᶠ i in l, ∀ x, x ∈ U → ∀ phi : E → ℝ, ContDiffAt ℝ 2 phi x →
      IsLocalMin (fun y => F i y - phi y) x →
        0 ≤ Hn i x (F i x) (fderiv ℝ phi x) (fderiv ℝ (fderiv ℝ phi) x))
    {x : E} (hx : x ∈ U) (phi : E → ℝ) (hphi : ContDiffAt ℝ 2 phi x)
    (hmin : IsLocalMin (fun y => f y - phi y) x) :
    0 ≤ H x (f x) (fderiv ℝ phi x) (fderiv ℝ (fderiv ℝ phi) x) := by
  let _ : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let J : E × ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) →
      E × ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) :=
    fun z => (z.1, -z.2.1, -z.2.2.1, -z.2.2.2)
  have hJ : Continuous J := by
    dsimp only [J]
    fun_prop
  have hJU : MapsTo J (U ×ˢ univ) (U ×ˢ univ) := fun _ hz => ⟨hz.1, mem_univ _⟩
  have hneg (psi : E → ℝ) (y : E) :
      fderiv ℝ (fderiv ℝ (-psi)) y = -fderiv ℝ (fderiv ℝ psi) y := by
    have heq : fderiv ℝ (-psi) = -fderiv ℝ psi :=
      funext fun z => fderiv_neg (𝕜 := ℝ) (f := psi) (x := z)
    rw [heq, fderiv_neg]
  have htest : ∀ᶠ i in l, ∀ y, y ∈ U → ∀ psi : E → ℝ, ContDiffAt ℝ 2 psi y →
      IsLocalMax (fun z => -F i z - psi z) y →
        -Hn i y (-(-F i y)) (-fderiv ℝ psi y) (-fderiv ℝ (fderiv ℝ psi) y) ≤ 0 := by
    filter_upwards [hsuper] with i hsuperi
    intro y hy psi hpsi hmax
    have hlocal : IsLocalMin (fun z => F i z - (-psi) z) y := by
      filter_upwards [hmax] with z hz
      dsimp only [Pi.neg_apply]
      linarith
    have h := hsuperi y hy (-psi) hpsi.neg hlocal
    rw [fderiv_neg, hneg] at h
    simpa only [neg_neg] using neg_nonpos.mpr h
  have hlocal : IsLocalMax (fun y => -f y - (-phi) y) x := by
    filter_upwards [hmin] with y hy
    dsimp only [Pi.neg_apply]
    linarith
  have h := upper_test_le_of_tendstoLocallyUniformlyOn
    (Hn := fun i y r p A => -Hn i y (-r) (-p) (-A))
    (H := fun y r p A => -H y (-r) (-p) (-A)) hU (hF.mono fun _ hi => hi.neg) hconv.neg
    (hH.comp hJ.continuousOn hJU).neg (hHconv.comp J hJU hJ.continuousOn).neg
    htest hx (-phi) hphi.neg hlocal
  simpa only [J, Function.comp_apply, Pi.neg_apply, fderiv_neg, fderiv_fun_neg, hneg, neg_neg, neg_nonpos] using h

end DifferentialGeometry.Analysis.Viscosity
