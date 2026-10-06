import DifferentialGeometry.Topology.Manifold.LinearChartMaps74

/-!
# Submersions into a subset in chart form from a chart-coordinate submersion (equal dimension)

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G31 (kernel), companion of `LinearChartMaps74`. For a map
`f : N → W` into a subset `W ⊆ H` in chart form whose model is `E` (so `T_y W = E` and
`dim T_y W = dim E`): if `κ ∘ ι ∘ f` is a submersion at `x` for a continuous linear
`κ : H →L[ℝ] E` (a chart coordinate of some marked piece), then `f` is a submersion at `x`.
`d(κ ∘ ι) : E → E` is an endomorphism of a finite-dimensional space that is onto (it is the left
factor of an onto composite), hence injective, hence `df` is onto.

* `surjective_mfderiv_of_comp_surjective_R74`: `d(g ∘ ψ)` onto ⟹ `dg` onto;
* `surjective_mfderiv_of_coord_surjective_R74`: the statement above.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {I : ModelWithCorners ℝ EN HN} {Mf : Type*} [TopologicalSpace Mf] [ChartedSpace HN Mf]
  {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {J : ModelWithCorners ℝ EX HX} {Xs : Type*} [TopologicalSpace Xs] [ChartedSpace HX Xs]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If the differential of `g ∘ ψ` at `p` is onto, so is the differential of `g` at `ψ p`. -/
theorem surjective_mfderiv_of_comp_surjective_R74 {ψ : Xs → Mf} {g : Mf → F} (p : Xs)
    {f : Xs → F} (hfg : ∀ q, f q = g (ψ q)) (hψ : MDifferentiableAt J I ψ p)
    (hg : MDifferentiableAt I 𝓘(ℝ, F) g (ψ p))
    (h : Function.Surjective (mfderiv J 𝓘(ℝ, F) f p)) :
    Function.Surjective (mfderiv I 𝓘(ℝ, F) g (ψ p)) := by
  have hff : f = g ∘ ψ := funext hfg
  subst hff
  have hcomp : mfderiv J 𝓘(ℝ, F) (g ∘ ψ) p =
      (mfderiv I 𝓘(ℝ, F) g (ψ p)).comp (mfderiv J I ψ p) := mfderiv_comp p hg hψ
  have h' : Function.Surjective ((mfderiv I 𝓘(ℝ, F) g (ψ p)).comp (mfderiv J I ψ p)) := by
    rw [← hcomp]
    exact h
  exact Function.Surjective.of_comp h'

/-- Surjectivity of the differential transfers along the inclusion of an open set (pointwise
form of `mfderiv_comp_subtype_val_R74`, avoiding the two tangent-space types of `U` and `Mf`). -/
theorem surjective_mfderiv_subtype_val_R74 (U : TopologicalSpace.Opens Mf) {f : Mf → F}
    {g : U → F} (hg : ∀ z : U, g z = f z) (x : U) (hf : MDifferentiableAt I 𝓘(ℝ, F) f (x : Mf))
    (h : Function.Surjective (mfderiv I 𝓘(ℝ, F) f (x : Mf))) :
    Function.Surjective (mfderiv I 𝓘(ℝ, F) g x) := by
  have h0 := mfderiv_comp_subtype_val_R74 (I := I) U hg x hf
  intro t
  obtain ⟨v, hv⟩ := h t
  exact ⟨v, (congrArg (fun L => L v) h0).trans hv⟩

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] {W : Set H} [ChartedSpace E W]

/-- **Submersion into a chart-form subset from a chart-coordinate submersion**: if
`κ ∘ ι ∘ f` has onto differential at `x` (`κ : H →L[ℝ] E` linear, `ι` the inclusion of `W`), so
does `f`. -/
theorem surjective_mfderiv_of_coord_surjective_R74
    (hval : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ (Subtype.val : W → H)) (κ : H →L[ℝ] E)
    {f : Xs → W} (hf : ContMDiff J 𝓘(ℝ, E) ∞ f) (x : Xs)
    (h : Function.Surjective (mfderiv J 𝓘(ℝ, E) (fun z => κ (f z : H)) x)) :
    Function.Surjective (mfderiv J 𝓘(ℝ, E) f x) := by
  have hfd : MDifferentiableAt J 𝓘(ℝ, E) f x := hf.mdifferentiableAt (by simp)
  have hvd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, H) (Subtype.val : W → H) (f x) :=
    hval.mdifferentiableAt (by simp)
  have hkd : MDifferentiableAt 𝓘(ℝ, H) 𝓘(ℝ, E) κ ((f x : W) : H) :=
    κ.differentiableAt.mdifferentiableAt
  have h1 : mfderiv J 𝓘(ℝ, E) (κ ∘ (Subtype.val : W → H) ∘ f) x =
      (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) κ ((f x : W) : H)).comp
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) (Subtype.val : W → H) (f x)).comp
          (mfderiv J 𝓘(ℝ, E) f x)) := by
    have hvf : MDifferentiableAt J 𝓘(ℝ, H) ((Subtype.val : W → H) ∘ f) x := hvd.comp x hfd
    rw [mfderiv_comp x hkd hvf, mfderiv_comp x hvd hfd]
    rfl
  -- the endomorphism `C = dκ ∘ dι` of `E` is onto, hence injective, hence `df` is onto
  let C : E →L[ℝ] E := (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) κ ((f x : W) : H)).comp
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) (Subtype.val : W → H) (f x))
  have hcomp : Function.Surjective (C.comp (mfderiv J 𝓘(ℝ, E) f x)) := by
    have : mfderiv J 𝓘(ℝ, E) (κ ∘ (Subtype.val : W → H) ∘ f) x =
        C.comp (mfderiv J 𝓘(ℝ, E) f x) := h1
    rw [← this]
    exact h
  have hCs : Function.Surjective C := Function.Surjective.of_comp hcomp
  have hCi : Function.Injective C :=
    (LinearMap.injective_iff_surjective (f := (C : E →ₗ[ℝ] E))).mpr hCs
  intro t
  obtain ⟨v, hv⟩ := hcomp (C t)
  exact ⟨v, hCi hv⟩

end DifferentialGeometry.Topology.Manifold
