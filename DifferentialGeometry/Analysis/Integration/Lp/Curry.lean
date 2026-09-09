import DifferentialGeometry.Analysis.Integration.Lp.Product
import Mathlib.MeasureTheory.Measure.SeparableMeasure

noncomputable section
open Filter Set
open scoped ENNReal Topology
namespace MeasureTheory
variable {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [NormedAddCommGroup E] {μ : Measure A} {ν : Measure B} [SFinite ν]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

open Classical in
private def slice (f : Lp E p (μ.prod ν)) (a : A) : Lp E p ν :=
  if h : MemLp (fun b => f (a, b)) p ν then h.toLp (fun b => f (a, b)) else 0

private theorem measurable_of_edist
    {X Y : Type*} [MeasurableSpace X] [PseudoEMetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    {f : X → Y} (hf : ∀ y, Measurable (fun x => edist (f x) y)) : Measurable f := by
  let S : Set (Set Y) := {s | ∃ y r, s = Metric.eball y r}
  have hS : TopologicalSpace.IsTopologicalBasis S := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨y, r, rfl⟩
      exact Metric.isOpen_eball
    · intro y s hy hs
      obtain ⟨r, hr, hrs⟩ := EMetric.isOpen_iff.mp hs y hy
      exact ⟨Metric.eball y r, ⟨y, r, rfl⟩, Metric.mem_eball_self hr, hrs⟩
  rw [‹BorelSpace Y›.measurable_eq, hS.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro _ ⟨y, r, rfl⟩
  exact measurableSet_lt (hf y) measurable_const

private theorem measurable_eLpNorm_slice (hp : p ≠ ⊤) {F : A × B → E}
    (hF : StronglyMeasurable F) :
    Measurable (fun a => eLpNorm (fun b => F (a, b)) p ν) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  exact (hF.enorm.pow_const p.toReal).lintegral_prod_right'.pow_const _

private theorem measurableSet_memLp_slice (hp : p ≠ ⊤) (f : Lp E p (μ.prod ν)) :
    MeasurableSet {a | MemLp (fun b => f (a, b)) p ν} := by
  have hsm (a : A) : StronglyMeasurable (fun b => f (a, b)) :=
    (Lp.stronglyMeasurable f).comp_measurable (measurable_const.prodMk measurable_id)
  have heq : {a | MemLp (fun b => f (a, b)) p ν} =
      {a | eLpNorm (fun b => f (a, b)) p ν < ⊤} := by
    ext a
    exact ⟨fun h => h.2, fun h => ⟨(hsm a).aestronglyMeasurable, h⟩⟩
  rw [heq]
  exact measurableSet_lt (measurable_eLpNorm_slice hp (Lp.stronglyMeasurable f)) measurable_const

omit [SFinite ν] [Fact (1 ≤ p)] in
open Classical in
private theorem edist_slice (f : Lp E p (μ.prod ν)) (g : Lp E p ν) (a : A) :
    edist (slice f a) g =
      if MemLp (fun b => f (a, b)) p ν then eLpNorm (fun b => f (a, b) - g b) p ν
      else edist (0 : Lp E p ν) g := by
  classical
  by_cases ha : MemLp (fun b => f (a, b)) p ν
  · simp only [slice, dif_pos ha, if_pos ha]
    have hg : (Lp.memLp g).toLp (fun b => g b) = g := Lp.toLp_coeFn g (Lp.memLp g)
    conv_lhs => rhs; rw [← hg]
    exact Lp.edist_toLp_toLp _ _ ha (Lp.memLp g)
  · simp only [slice, dif_neg ha, if_neg ha]

private theorem measurable_slice (hp : p ≠ ⊤) (f : Lp E p (μ.prod ν))
    [MeasurableSpace (Lp E p ν)] [BorelSpace (Lp E p ν)]
    [_root_.SecondCountableTopology (Lp E p ν)] : Measurable (slice f) := by
  classical
  apply measurable_of_edist
  intro g
  have hd : Measurable (fun a => eLpNorm (fun b => f (a, b) - g b) p ν) :=
    measurable_eLpNorm_slice (E := E) (F := fun z => f z - g z.2) hp
      ((Lp.stronglyMeasurable f).sub
        ((Lp.stronglyMeasurable g).comp_measurable measurable_snd))
  have heq : (fun a => edist (slice f a) g) = fun a =>
      if MemLp (fun b => f (a, b)) p ν then eLpNorm (fun b => f (a, b) - g b) p ν
      else edist (0 : Lp E p ν) g := by
    funext a
    exact edist_slice f g a
  rw [heq]
  exact Measurable.ite (measurableSet_memLp_slice hp f) hd measurable_const

omit [Fact (1 ≤ p)] in
private theorem slice_coeFn (hp : p ≠ ⊤) (f : Lp E p (μ.prod ν)) :
    ∀ᵐ a ∂μ, (slice f a : B → E) =ᵐ[ν] fun b => f (a, b) := by
  filter_upwards [(Lp.memLp f).prodMk_left hp] with a ha
  simpa only [slice, dif_pos ha] using ha.coeFn_toLp

private theorem memLp_slice (hp : p ≠ ⊤) (f : Lp E p (μ.prod ν))
    (hf : AEStronglyMeasurable (slice f) μ) : MemLp (slice f) p μ := by
  refine ⟨hf, ?_⟩
  have heq : (fun a => ‖slice f a‖ₑ) =ᵐ[μ] fun a => eLpNorm (fun b => f (a, b)) p ν := by
    filter_upwards [(Lp.memLp f).prodMk_left hp] with a ha
    simp only [slice, dif_pos ha, Lp.enorm_toLp]
  rw [← eLpNorm_enorm]
  rw [eLpNorm_congr_ae heq, eLpNorm_eLpNorm hp (Lp.stronglyMeasurable f).enorm.aemeasurable]
  exact (Lp.memLp f).2

private theorem norm_curry (hp : p ≠ ⊤) (f : Lp E p (μ.prod ν))
    (hf : MemLp (slice f) p μ) : ‖hf.toLp (slice f)‖ = ‖f‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  congr 1
  have heq : (fun a => ‖slice f a‖ₑ) =ᵐ[μ] fun a => eLpNorm (fun b => f (a, b)) p ν := by
    filter_upwards [(Lp.memLp f).prodMk_left hp] with a ha
    simp only [slice, dif_pos ha, Lp.enorm_toLp]
  rw [← eLpNorm_enorm, eLpNorm_congr_ae heq,
    eLpNorm_eLpNorm hp (Lp.stronglyMeasurable f).enorm.aemeasurable]

variable [_root_.SecondCountableTopology (Lp E p ν)]

theorem Lp.exists_curry (hp : p ≠ ⊤) (f : Lp E p (μ.prod ν)) :
    ∃ g : Lp (Lp E p ν) p μ,
      (∀ᵐ a ∂μ, (g a : B → E) =ᵐ[ν] fun b => f (a, b)) ∧ ‖g‖ = ‖f‖ := by
  let : MeasurableSpace (Lp E p ν) := borel (Lp E p ν)
  let : BorelSpace (Lp E p ν) := ⟨rfl⟩
  have hmem := memLp_slice hp f (measurable_slice hp f).stronglyMeasurable.aestronglyMeasurable
  refine ⟨hmem.toLp (slice f), ?_, norm_curry hp f hmem⟩
  filter_upwards [hmem.coeFn_toLp, slice_coeFn hp f] with a ha hs
  rw [ha]
  exact hs

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]

theorem Lp.uncurry_surjective (hp : p ≠ ⊤) :
    Function.Surjective (Lp.uncurry (E := E) (μ := μ) (ν := ν) 𝕜 hp) := by
  intro f
  obtain ⟨g, hg, _⟩ := Lp.exists_curry hp f
  refine ⟨g, Lp.ext_curry ?_⟩
  filter_upwards [Lp.uncurry_coeFn (𝕜 := 𝕜) hp g, hg] with a ha hb
  exact ha.trans hb

variable (𝕜) in
def Lp.curry (hp : p ≠ ⊤) : Lp E p (μ.prod ν) ≃ₗᵢ[𝕜] Lp (Lp E p ν) p μ :=
  (LinearIsometryEquiv.ofSurjective (Lp.uncurry 𝕜 hp) (Lp.uncurry_surjective hp)).symm

@[simp]
theorem Lp.uncurry_curry (hp : p ≠ ⊤) (f : Lp E p (μ.prod ν)) :
    Lp.uncurry 𝕜 hp (Lp.curry 𝕜 hp f) = f :=
  (LinearIsometryEquiv.ofSurjective (Lp.uncurry 𝕜 hp)
    (Lp.uncurry_surjective hp)).apply_symm_apply f

@[simp]
theorem Lp.curry_uncurry (hp : p ≠ ⊤) (f : Lp (Lp E p ν) p μ) :
    Lp.curry 𝕜 hp (Lp.uncurry 𝕜 hp f) = f :=
  (LinearIsometryEquiv.ofSurjective (Lp.uncurry 𝕜 hp)
    (Lp.uncurry_surjective hp)).symm_apply_apply f

theorem Lp.curry_coeFn (hp : p ≠ ⊤) (f : Lp E p (μ.prod ν)) :
    ∀ᵐ a ∂μ, (Lp.curry 𝕜 hp f a : B → E) =ᵐ[ν] fun b => f (a, b) := by
  have h := Lp.uncurry_coeFn (𝕜 := 𝕜) hp (Lp.curry 𝕜 hp f)
  rw [Lp.uncurry_curry] at h
  exact h.mono fun _ ha => ha.symm

end MeasureTheory
