import DifferentialGeometry.Topology.Morse.CriticalPoints
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

open Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem fderiv_fderiv_comp_at_critical
    {f : F → ℝ} {φ : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (hcrit : fderiv ℝ f (φ x) = 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ φ)) x u v =
      fderiv ℝ (fderiv ℝ f) (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) := by
  have hdφ := hφ.differentiableAt (by norm_num)
  have heq : fderiv ℝ (f ∘ φ) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ f (φ y)).comp (fderiv ℝ φ y) := by
    filter_upwards [hφ.eventually (by norm_num),
      hφ.continuousAt.preimage_mem_nhds (hf.eventually (by norm_num))] with y hy hfy
    change ContDiffAt ℝ 2 f (φ y) at hfy
    exact fderiv_comp y (hfy.differentiableAt (by norm_num))
      (hy.differentiableAt (by norm_num))
  rw [heq.fderiv_eq]
  have hdDf := (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
    (by norm_num)
  have hdDφ := (hφ.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
    (by norm_num)
  have hdA : DifferentiableAt ℝ (fun y => fderiv ℝ f (φ y)) x := hdDf.comp x hdφ
  rw [fderiv_clm_comp hdA hdDφ]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
    fderiv_fun_comp x hdDf hdφ, hcrit, ContinuousLinearMap.zero_comp,
    zero_add]

theorem isNondegenerateCriticalPointAt_model_comp_iff
    {f : F → ℝ} {φ : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (hbij : Function.Bijective (fderiv ℝ φ x)) :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (f ∘ φ) x ↔
      IsNondegenerateCriticalPointAt 𝓘(ℝ, F) f (φ x) := by
  rw [isNondegenerateCriticalPointAt_model_iff (hf.comp x hφ),
    isNondegenerateCriticalPointAt_model_iff hf]
  have hcrit : fderiv ℝ (f ∘ φ) x = 0 ↔ fderiv ℝ f (φ x) = 0 := by
    rw [fderiv_comp x (hf.differentiableAt (by norm_num)) (hφ.differentiableAt (by norm_num))]
    constructor
    · intro h
      ext v
      obtain ⟨u, rfl⟩ := hbij.2 v
      exact congrArg (fun L => L u) h
    · intro h
      rw [h, ContinuousLinearMap.zero_comp]
  rw [hcrit]
  refine and_congr_right fun hx => ?_
  constructor
  · intro h u v huv
    obtain ⟨u', rfl⟩ := hbij.2 u
    obtain ⟨v', rfl⟩ := hbij.2 v
    apply congrArg (fderiv ℝ φ x)
    apply h
    ext w
    rw [fderiv_fderiv_comp_at_critical hf hφ hx,
      fderiv_fderiv_comp_at_critical hf hφ hx, huv]
  · intro h u v huv
    apply hbij.1
    apply h
    ext w
    obtain ⟨w', rfl⟩ := hbij.2 w
    simpa only [fderiv_fderiv_comp_at_critical hf hφ hx] using
      congrArg (fun L => L w') huv

theorem isNondegenerateCriticalPointAt_model_comp_localDiffeomorph_iff
    {f : F → ℝ} {φ : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (φ x))
    (hφ : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) 2 φ x) :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (f ∘ φ) x ↔
      IsNondegenerateCriticalPointAt 𝓘(ℝ, F) f (φ x) := by
  apply isNondegenerateCriticalPointAt_model_comp_iff hf
  · exact contMDiffAt_iff_contDiffAt.mp hφ.contMDiffAt
  · have hbij := (hφ.mfderivToContinuousLinearEquiv (by norm_num)).bijective
    change Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) φ x) at hbij
    rw [mfderiv_eq_fderiv] at hbij
    exact hbij

section Manifold

open Manifold Set

variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

private theorem isNondegenerateCriticalPointAt_iff_model_chart
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) :
    IsNondegenerateCriticalPointAt I f x ↔
      IsNondegenerateCriticalPointAt 𝓘(ℝ, E)
        (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  let : IsManifold I 1 M := IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hx := mem_extChartAt_source (I := I) x
  have hxt := (extChartAt I x).map_source hx
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I x).symm (extChartAt I x x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt ((isOpen_extChartAt_target x).mem_nhds hxt)
  have hDsymm : mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm (extChartAt I x x) =
      ContinuousLinearMap.id ℝ E := by
    have hh := mfderivWithin_range_extChartAt_symm (I := I) (x := x)
    rw [I.range_eq_univ, mfderivWithin_univ] at hh
    exact hh
  have hsurj : Function.Surjective
      (mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm (extChartAt I x x)) := by
    rw [hDsymm]
    exact Function.surjective_id
  have hf' : MDifferentiableAt I 𝓘(ℝ, ℝ) f
      ((extChartAt I x).symm (extChartAt I x x)) := by
    simpa only [(extChartAt I x).left_inv hx] using hf.mdifferentiableAt (by norm_num)
  have hc := isCriticalPointAt_comp_iff (hsymm.mdifferentiableAt (by norm_num)) hf' hsurj
  simp only [(extChartAt I x).left_inv hx] at hc
  unfold IsNondegenerateCriticalPointAt
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    id_eq, Function.comp_def]
  exact and_congr_left fun _ => hc.symm

theorem isNondegenerateCriticalPointAt_comp_model_iff
    {g : F → ℝ} {φ : M → F} {x : M}
    (hg : ContDiffAt ℝ 2 g (φ x)) (hφ : ContMDiffAt I 𝓘(ℝ, F) 2 φ x)
    (hbij : Function.Bijective (mfderiv I 𝓘(ℝ, F) φ x)) :
    IsNondegenerateCriticalPointAt I (g ∘ φ) x ↔
      IsNondegenerateCriticalPointAt 𝓘(ℝ, F) g (φ x) := by
  let : IsManifold I 1 M := IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hx := mem_extChartAt_source (I := I) x
  have hxt := (extChartAt I x).map_source hx
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I x).symm (extChartAt I x x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt ((isOpen_extChartAt_target x).mem_nhds hxt)
  have hφ' : ContMDiffAt I 𝓘(ℝ, F) 2 φ
      ((extChartAt I x).symm (extChartAt I x x)) := by
    simpa only [(extChartAt I x).left_inv hx] using hφ
  have hψ : ContDiffAt ℝ 2 (φ ∘ (extChartAt I x).symm) (extChartAt I x x) :=
    contMDiffAt_iff_contDiffAt.mp (hφ'.comp _ hsymm)
  have hDsymm : mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm (extChartAt I x x) =
      ContinuousLinearMap.id ℝ E := by
    have hh := mfderivWithin_range_extChartAt_symm (I := I) (x := x)
    rw [I.range_eq_univ, mfderivWithin_univ] at hh
    exact hh
  have hψder : fderiv ℝ (φ ∘ (extChartAt I x).symm) (extChartAt I x x) =
      mfderiv I 𝓘(ℝ, F) φ x := by
    have hh := mfderiv_comp (extChartAt I x x) (hφ'.mdifferentiableAt (by norm_num))
      (hsymm.mdifferentiableAt (by norm_num))
    rw [mfderiv_eq_fderiv, (extChartAt I x).left_inv hx, hDsymm] at hh
    have hh' : fderiv ℝ (φ ∘ (extChartAt I x).symm) (extChartAt I x x) =
        (mfderiv I 𝓘(ℝ, F) φ x : E →L[ℝ] F).comp (ContinuousLinearMap.id ℝ E) := hh
    ext v
    exact congrArg (fun L => L v) hh'
  have hg' : ContDiffAt ℝ 2 g ((φ ∘ (extChartAt I x).symm) (extChartAt I x x)) := by
    simpa only [Function.comp_apply, (extChartAt I x).left_inv hx] using hg
  rw [isNondegenerateCriticalPointAt_iff_model_chart (hg.contMDiffAt.comp x hφ)]
  change IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (g ∘ (φ ∘ (extChartAt I x).symm))
    (extChartAt I x x) ↔ _
  have hb : Function.Bijective (fderiv ℝ (φ ∘ (extChartAt I x).symm) (extChartAt I x x)) := by
    rw [hψder]
    exact hbij
  have h := isNondegenerateCriticalPointAt_model_comp_iff hg' hψ hb
  simpa only [Function.comp_apply, (extChartAt I x).left_inv hx] using h

omit [IsManifold I 2 M] in
theorem isNondegenerateCriticalPointAt_congr_of_eventuallyEq
    {f g : M → ℝ} {x : M} (hfg : f =ᶠ[𝓝 x] g) :
    IsNondegenerateCriticalPointAt I f x ↔ IsNondegenerateCriticalPointAt I g x := by
  have hx := mem_extChartAt_source (I := I) x
  have hxt := (extChartAt I x).map_source hx
  have hs : ContinuousAt (extChartAt I x).symm (extChartAt I x x) :=
    (continuousOn_extChartAt_symm x).continuousAt ((isOpen_extChartAt_target x).mem_nhds hxt)
  have hfg' : (f ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)]
      (g ∘ (extChartAt I x).symm) := by
    have hh : f =ᶠ[𝓝 ((extChartAt I x).symm (extChartAt I x x))] g := by
      simpa only [(extChartAt I x).left_inv hx] using hfg
    exact hh.comp_tendsto hs
  have hD := (hfg'.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have hB : chartHessianBilinAt (f ∘ (extChartAt I x).symm) (extChartAt I x x) =
      chartHessianBilinAt (g ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    ext u v
    exact congrArg (fun L => L u v) hD
  change chartHessianBilinAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x) =
    chartHessianBilinAt (fun y => g ((extChartAt I x).symm y)) (extChartAt I x x) at hB
  unfold IsNondegenerateCriticalPointAt
  constructor
  · rintro ⟨hc, hn⟩
    refine ⟨hfg.mfderiv_eq.symm.trans hc, ?_⟩
    change (QuadraticMap.associated (R := ℝ)
      (chartHessianBilinAt (fun y => g ((extChartAt I x).symm y))
        (extChartAt I x x)).toQuadraticMap).SeparatingLeft
    rw [← hB]
    exact hn
  · rintro ⟨hc, hn⟩
    refine ⟨hfg.mfderiv_eq.trans hc, ?_⟩
    change (QuadraticMap.associated (R := ℝ)
      (chartHessianBilinAt (fun y => f ((extChartAt I x).symm y))
        (extChartAt I x x)).toQuadraticMap).SeparatingLeft
    rw [hB]
    exact hn

theorem isNondegenerateCriticalPointAt_iff_fixed_chart
    {f : M → ℝ} {p x : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x)
    (hx : x ∈ (extChartAt I p).source) :
    IsNondegenerateCriticalPointAt I f x ↔
      IsNondegenerateCriticalPointAt 𝓘(ℝ, E)
        (f ∘ (extChartAt I p).symm) (extChartAt I p x) := by
  let : IsManifold I 1 M := IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hxt := (extChartAt I p).map_source hx
  have hs : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I p).symm (extChartAt I p x) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt ((isOpen_extChartAt_target p).mem_nhds hxt)
  have hf' : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f ((extChartAt I p).symm (extChartAt I p x)) := by
    simpa only [(extChartAt I p).left_inv hx] using hf
  have hg : ContDiffAt ℝ 2 (f ∘ (extChartAt I p).symm) (extChartAt I p x) :=
    contMDiffAt_iff_contDiffAt.mp (hf'.comp _ hs)
  have he : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I p) x :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hx)
  have heinv := isInvertible_mfderiv_extChartAt (I := I) hx
  have heq : f =ᶠ[𝓝 x] (f ∘ (extChartAt I p).symm) ∘ (extChartAt I p) :=
    Filter.eventuallyEq_of_mem ((isOpen_extChartAt_source p).mem_nhds hx)
      (fun y hy => congrArg f ((extChartAt I p).left_inv hy).symm)
  exact (isNondegenerateCriticalPointAt_congr_of_eventuallyEq heq).trans
    (isNondegenerateCriticalPointAt_comp_model_iff hg he ⟨heinv.injective, heinv.surjective⟩)

omit [IsManifold I 2 M] in
theorem isCriticalPointAt_iff_fixed_chart [IsManifold I 1 M]
    {f : M → ℝ} {p x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (extChartAt I p).source) :
    IsCriticalPointAt I f x ↔
      IsCriticalPointAt 𝓘(ℝ, E) (f ∘ (extChartAt I p).symm) (extChartAt I p x) := by
  let e := extChartAt I p
  have hxt : e x ∈ e.target := e.map_source hx
  have hes : MDifferentiableAt 𝓘(ℝ, E) I e.symm (e x) :=
    (mdifferentiableOn_extChartAt_symm (I := I) (x := p) (e x) hxt).mdifferentiableAt
      ((isOpen_extChartAt_target p).mem_nhds hxt)
  have hf' : MDifferentiableAt I 𝓘(ℝ, ℝ) f (e.symm (e x)) := by
    simpa only [e.left_inv hx] using hf
  have hsurj : Function.Surjective (mfderiv 𝓘(ℝ, E) I e.symm (e x)) := by
    have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) hx
    rw [I.range_eq_univ, mfderivWithin_univ] at hcomp
    intro v
    refine ⟨mfderiv I 𝓘(ℝ, E) e x v, ?_⟩
    exact DFunLike.congr_fun hcomp v
  have h := isCriticalPointAt_comp_iff hes hf' hsurj
  simpa only [e.left_inv hx] using h.symm

omit [I.Boundaryless] [IsManifold I 2 M] in
private theorem mfderiv_add_const (f : M → ℝ) (c : ℝ) (x : M) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y => f y + c) x = mfderiv I 𝓘(ℝ, ℝ) f x := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · have hg : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => f y + c) x :=
      hf.add (mdifferentiableAt_const (c := c))
    simp only [mfderiv, hf, hg, ↓reduceIte, writtenInExtChartAt,
      extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.comp_def, id_eq]
    change fderivWithin ℝ (fun y => f ((extChartAt I x).symm y) + c) (Set.range I)
      (extChartAt I x x) = fderivWithin ℝ (fun y => f ((extChartAt I x).symm y))
      (Set.range I) (extChartAt I x x)
    exact fderivWithin_add_const c
  · have hg : ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => f y + c) x := by
      intro hg
      have hh := hg.sub (mdifferentiableAt_const (c := c))
      have heq : ((fun y => f y + c) - (fun _ : M => c)) = f := by
        funext y
        exact add_sub_cancel_right (f y) c
      rw [heq] at hh
      exact hf hh
    rw [mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hg]
    rfl

omit [I.Boundaryless] [IsManifold I 2 M] in
theorem isCriticalPointAt_add_const_iff (f : M → ℝ) (c : ℝ) (x : M) :
    IsCriticalPointAt I (fun y => f y + c) x ↔ IsCriticalPointAt I f x := by
  unfold IsCriticalPointAt
  rw [mfderiv_add_const]
  rfl

omit [I.Boundaryless] [IsManifold I 2 M] in
theorem isNondegenerateCriticalPointAt_add_const_iff (f : M → ℝ) (c : ℝ) (x : M) :
    IsNondegenerateCriticalPointAt I (fun y => f y + c) x ↔
      IsNondegenerateCriticalPointAt I f x := by
  have hD : fderiv ℝ (fun y => f ((extChartAt I x).symm y) + c) =
      fderiv ℝ (fun y => f ((extChartAt I x).symm y)) := by
    funext y
    exact fderiv_add_const c
  have hH : chartHessianAt (fun y => f ((extChartAt I x).symm y) + c) (extChartAt I x x) =
      chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x) := by
    apply congrArg LinearMap.BilinMap.toQuadraticMap
    ext u v
    change fderiv ℝ (fderiv ℝ (fun y => f ((extChartAt I x).symm y) + c))
      (extChartAt I x x) u v = _
    rw [hD]
    rfl
  unfold IsNondegenerateCriticalPointAt
  rw [isCriticalPointAt_add_const_iff, hH]

omit [I.Boundaryless] [IsManifold I 2 M] in
theorem isCriticalPointAt_congr_of_eventuallyEq
    {f g : M → ℝ} {x : M} (hfg : f =ᶠ[𝓝 x] g) :
    IsCriticalPointAt I f x ↔ IsCriticalPointAt I g x := by
  unfold IsCriticalPointAt
  rw [hfg.mfderiv_eq]
  rfl

omit [I.Boundaryless] [IsManifold I 2 M] in
theorem isCriticalPointAt_add_of_eventuallyEq_const
    {f h : M → ℝ} {x : M} {c : ℝ} (hh : h =ᶠ[𝓝 x] fun _ => c) :
    IsCriticalPointAt I (fun y => f y + h y) x ↔ IsCriticalPointAt I f x := by
  have heq : (fun y => f y + h y) =ᶠ[𝓝 x] (fun y => f y + c) := by
    filter_upwards [hh] with y hy
    rw [hy]
  exact (isCriticalPointAt_congr_of_eventuallyEq heq).trans
    (isCriticalPointAt_add_const_iff f c x)

omit [IsManifold I 2 M] in
theorem isNondegenerateCriticalPointAt_add_of_eventuallyEq_const
    {f h : M → ℝ} {x : M} {c : ℝ} (hh : h =ᶠ[𝓝 x] fun _ => c) :
    IsNondegenerateCriticalPointAt I (fun y => f y + h y) x ↔
      IsNondegenerateCriticalPointAt I f x := by
  have heq : (fun y => f y + h y) =ᶠ[𝓝 x] (fun y => f y + c) := by
    filter_upwards [hh] with y hy
    rw [hy]
  exact (isNondegenerateCriticalPointAt_congr_of_eventuallyEq heq).trans
    (isNondegenerateCriticalPointAt_add_const_iff f c x)


end Manifold

end DifferentialGeometry.Topology.Morse
