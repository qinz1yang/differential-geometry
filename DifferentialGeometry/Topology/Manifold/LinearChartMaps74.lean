import DifferentialGeometry.Topology.Manifold.LinearChartSubmanifold
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# Maps into a subset in chart form: smoothness and submersion from the ambient map

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G30 (kernel), supplement to `LinearChartSubmanifold` (G11).
A subset `W ⊆ H` of a normed space in chart form (linear charts `κ`) carries the chart structure
`linearChartedSpace_R74`; here the charts are only used through the property

  `hlin : ∀ y, ∃ κ : H →L[ℝ] E, ∀ y' ∈ (chartAt E y).source, chartAt E y y' = κ y'`

which holds for `linearChartedSpace_R74` (`linearChartedSpace_R74_chartAt_apply`).

* `contMDiff_into_linear_R74`: a continuous map `f : N → W` whose composite with the inclusion
  `W → H` is smooth is smooth into `W` (the coordinate expression is `κ ∘ ι ∘ f`, linear after a
  smooth map);
* `surjective_mfderiv_of_val_ne_zero_R74`: if `W` is one-dimensional and the differential of
  `ι ∘ f` at `x` is nonzero, the differential of `f` at `x` is surjective (`dι ∘ df ≠ 0` forces
  `df ≠ 0`, and a nonzero linear map into a line is onto).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- The charts of `linearChartedSpace_R74` are linear: `chartAt y` is `κ ∘ val` on its source. -/
theorem linearChartedSpace_R74_chartAt_apply {ι : Type*} (W : Set H) (κ : ι → H →L[ℝ] E)
    (φ : ι → E → H) (O : ι → Set H) (r : ℝ) (hO : ∀ i, IsOpen (O i))
    (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) (y y' : W) :
    letI := linearChartedSpace_R74 W κ φ O r hO hφs hφ hκ hcov
    chartAt E y y' = κ (linearChartIdx_R74 W O hcov y) (y' : H) :=
  rfl

/-- The charts of `linearChartedSpace_R74` are linear (the hypothesis form `hlin`). -/
theorem linearChartedSpace_R74_hlin {ι : Type*} (W : Set H) (κ : ι → H →L[ℝ] E)
    (φ : ι → E → H) (O : ι → Set H) (r : ℝ) (hO : ∀ i, IsOpen (O i))
    (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) :
    letI := linearChartedSpace_R74 W κ φ O r hO hφs hφ hκ hcov
    ∀ y : W, ∃ κ' : H →L[ℝ] E, ∀ y' ∈ (chartAt E y).source, chartAt E y y' = κ' (y' : H) :=
  fun y => ⟨κ (linearChartIdx_R74 W O hcov y), fun _ _ => rfl⟩

variable {W : Set H} [ChartedSpace E W]

/-- **Smoothness into a subset in chart form**: a continuous map whose composite with the
inclusion is smooth is smooth. -/
theorem contMDiff_into_linear_R74
    (hlin : ∀ y : W, ∃ κ : H →L[ℝ] E, ∀ y' ∈ (chartAt E y).source, chartAt E y y' = κ (y' : H))
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {I : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] {f : N → W}
    (hc : Continuous f) (hf : ContMDiff I 𝓘(ℝ, H) ∞ fun x => (f x : H)) :
    ContMDiff I 𝓘(ℝ, E) ∞ f := by
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨hc.continuousAt, ?_⟩
  obtain ⟨κ, hκ⟩ := hlin (f x)
  have hnhds : f ⁻¹' (chartAt E (f x)).source ∈ 𝓝 x :=
    hc.continuousAt.preimage_mem_nhds
      ((chartAt E (f x)).open_source.mem_nhds (mem_chart_source E (f x)))
  have hev : (extChartAt 𝓘(ℝ, E) (f x)) ∘ f =ᶠ[𝓝 x] fun z => κ (f z : H) := by
    filter_upwards [hnhds] with z hz
    change chartAt E (f x) (f z) = κ (f z : H)
    exact hκ (f z) hz
  exact (κ.contDiff.contMDiff.contMDiffAt.comp x (hf x)).congr_of_eventuallyEq hev

/-- **Submersion from the ambient differential** (one-dimensional `W`): if the differential of
`ι ∘ f` at `x` is nonzero, the differential of `f` at `x` is surjective. -/
theorem surjective_mfderiv_of_val_ne_zero_R74
    (hval : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ (Subtype.val : W → H)) (hE : Module.finrank ℝ E = 1)
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {I : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] {f : N → W}
    (hf : ContMDiff I 𝓘(ℝ, E) ∞ f) (x : N)
    (h : mfderiv I 𝓘(ℝ, H) (fun z => (f z : H)) x ≠ 0) :
    Function.Surjective (mfderiv I 𝓘(ℝ, E) f x) := by
  by_cases hz : ∀ v, mfderiv I 𝓘(ℝ, E) f x v = 0
  · exfalso
    apply h
    have hcomp : mfderiv I 𝓘(ℝ, H) (fun z => (f z : H)) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) (Subtype.val : W → H) (f x)).comp
          (mfderiv I 𝓘(ℝ, E) f x) :=
      mfderiv_comp x (hval.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
    rw [hcomp]
    ext v
    simp [hz v]
  · push Not at hz
    obtain ⟨v, hv⟩ := hz
    intro e
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (mfderiv I 𝓘(ℝ, E) f x v) hv).mp hE e
    exact ⟨c • v, by rw [map_smul]; exact hc⟩

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold

section Derivative

variable {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {I : ModelWithCorners ℝ EN HN} {Mf : Type*} [TopologicalSpace Mf] [ChartedSpace HN Mf]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The differential of a map composed with the inclusion of an open set is the differential of
the map (the inclusion has the identity as differential). -/
theorem mfderiv_comp_subtype_val_R74 (U : TopologicalSpace.Opens Mf) {f : Mf → V} {g : U → V}
    (hg : ∀ z : U, g z = f z) (x : U) (hf : MDifferentiableAt I 𝓘(ℝ, V) f (x : Mf)) :
    mfderiv I 𝓘(ℝ, V) g x = mfderiv I 𝓘(ℝ, V) f (x : Mf) := by
  have hgf : g = f ∘ (Subtype.val : U → Mf) := funext hg
  have hv : MDifferentiableAt I I (Subtype.val : U → Mf) x :=
    (contMDiff_subtype_val (I := I) (U := U) (n := ∞)).mdifferentiableAt (by simp)
  rw [hgf, mfderiv_comp x hf hv, DifferentialGeometry.mfderiv_subtype_val]
  rfl

variable {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {J : ModelWithCorners ℝ EX HX} {Xs : Type*} [TopologicalSpace Xs] [ChartedSpace HX Xs]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F]

/-- **A zero ambient differential kills a surjective chart coordinate**: if `π` has zero
differential at `ψ p` and `ψ` is differentiable at `p`, then `q ↦ κ (π (ψ q))` has a
non-surjective differential at `p` for every continuous linear `κ` into a nontrivial space. -/
theorem not_surjective_mfderiv_of_zero_R74 {ψ : Xs → Mf} {pr : Mf → V} (κ : V →L[ℝ] F)
    (p : Xs) {f : Xs → F} (hf : ∀ q, f q = κ (pr (ψ q))) (hψ : MDifferentiableAt J I ψ p)
    (hπ : MDifferentiableAt I 𝓘(ℝ, V) pr (ψ p))
    (h0 : mfderiv I 𝓘(ℝ, V) pr (ψ p) = 0) :
    ¬ Function.Surjective (mfderiv J 𝓘(ℝ, F) f p) := by
  have hff : f = fun q => κ (pr (ψ q)) := funext hf
  subst hff
  have hκ : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, F) κ (pr (ψ p)) :=
    κ.differentiableAt.mdifferentiableAt
  have hπψ : MDifferentiableAt J 𝓘(ℝ, V) (pr ∘ ψ) p := hπ.comp p hψ
  have h1 : mfderiv J 𝓘(ℝ, F) (κ ∘ (pr ∘ ψ)) p =
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) κ (pr (ψ p))).comp (mfderiv J 𝓘(ℝ, V) (pr ∘ ψ) p) :=
    mfderiv_comp p hκ hπψ
  have h2 : mfderiv J 𝓘(ℝ, V) (pr ∘ ψ) p =
      (mfderiv I 𝓘(ℝ, V) pr (ψ p)).comp (mfderiv J I ψ p) :=
    mfderiv_comp p hπ hψ
  have h3 : mfderiv J 𝓘(ℝ, F) (fun q => κ (pr (ψ q))) p = 0 := by
    change mfderiv J 𝓘(ℝ, F) (κ ∘ (pr ∘ ψ)) p = 0
    rw [h1, h2, h0]
    ext v
    simp
  intro hs
  rw [h3] at hs
  obtain ⟨w, hw⟩ := exists_ne (0 : F)
  obtain ⟨v, hv⟩ := hs w
  exact hw (by
    have : (0 : TangentSpace 𝓘(ℝ, F) (κ (pr (ψ p)))) = w := by simpa using hv
    exact this.symm)

end Derivative

end DifferentialGeometry.Topology.Manifold
