import DifferentialGeometry.Geometry.Metric.Pullback.FiniteRegularityProof
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity

/-!
# Pullback of a finite-order metric along an immersion (lane CMS3-CARRIER, group G3)

EXIT-51's metric leaf (review §14, disposition D10): for a `C^s` map `f : M → N` with injective
differential and a `C^n` metric `g` on `N`, the form `h_x(v, w) = g_{f x}(df_x v, df_x w)` is a
`C^m` Riemannian metric on `M` whenever `m ≤ n` and `m + 1 ≤ s` (`finiteImmersionPullbackMetric`).
The regularity proof is the tree's diffeomorphism version (`contMDiffAt_finitePullbackInner`), which
only uses that `f` is `C^s`; positivity uses the injectivity of `df`, and boundedness of the unit
ball is coercivity in finite dimension.
-/

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry (contMDiffAt_tangent_symmL_frame
  contMDiffAt_tangent_clm_section_of_symmL_apply)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {n s m : WithTop ℕ∞}

/-- The pulled-back bilinear form `h_x(v, w) = g_{f x}(df_x v, df_x w)` along any map. -/
def finiteImmersionInner (g : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _))
    (f : M → N) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (mfderiv I J f x) :
      (TangentSpace J (f x) →L[ℝ] ℝ) →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)).comp
    ((g.inner (f x)).comp (mfderiv I J f x))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
@[simp] theorem finiteImmersionInner_apply
    (g : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _)) (f : M → N) (x : M)
    (v w : TangentSpace I x) :
    finiteImmersionInner g f x v w = g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) :=
  rfl

/-- The regularity of the pulled-back form along a `C^s` map: `C^m` for `m ≤ n`, `m + 1 ≤ s`. -/
theorem contMDiffAt_finiteImmersionInner
    (g : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _)) {f : M → N}
    (hf : ContMDiff I J s f) (hmn : m ≤ n) (hms : m + 1 ≤ s) (x₀ : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) m
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (finiteImmersionInner (I := I) g f x)) x₀ := by
  have hfm : ContMDiff I J m f := hf.of_le (le_self_add.trans hms)
  have hg : ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) m
      (fun x : M => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun b : N => TangentSpace J b →L[ℝ] TangentSpace J b →L[ℝ] ℝ)
        (f x) (g.inner (f x))) :=
    (g.contMDiff.of_le hmn).comp hfm
  have hT : ContMDiff I.tangent J.tangent m (tangentMap I J f) :=
    hf.contMDiff_tangentMap hms
  have hY : ∀ v : E, ContMDiffAt I (J.prod 𝓘(ℝ, F)) m
      (fun x : M => TotalSpace.mk' F (E := (TangentSpace J : N → Type _)) (f x)
        (mfderiv I J f x
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x v))) x₀ :=
    fun v => (hT _).comp x₀ (contMDiffAt_tangent_symmL_frame x₀ v)
  apply contMDiffAt_tangent_clm_section_of_symmL_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => finiteImmersionInner (I := I) g f x)
  intro v
  apply contMDiffAt_tangent_clm_section_of_symmL_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => finiteImmersionInner (I := I) g f x
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x v))
  intro w
  have h_total := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun b : N => TangentSpace J b)
    (E₂ := fun b : N => TangentSpace J b)
    (E₃ := fun _ : N => ℝ)
    (b := fun x : M => f x)
    (ψ := fun x : M => g.inner (f x))
    (hg x₀) (hY v) (hY w)
  rw [contMDiffAt_totalSpace] at h_total
  rw [contMDiffAt_section]
  exact h_total.2

/-- **Pullback of a `C^n` metric along a `C^s` immersion**: for `m ≤ n` and `m + 1 ≤ s`, a `C^m`
Riemannian metric. -/
def finiteImmersionPullbackMetric
    (g : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _)) (f : M → N)
    (hf : ContMDiff I J s f) (himm : ∀ x, Function.Injective (mfderiv I J f x))
    (hmn : m ≤ n) (hms : m + 1 ≤ s) :
    ContMDiffRiemannianMetric I m E (TangentSpace I : M → Type _) where
  inner x := finiteImmersionInner (I := I) g f x
  symm x v w := by
    simp only [finiteImmersionInner_apply]
    exact g.symm _ _ _
  pos x v hv := g.pos (f x) _ fun h => hv (himm x (h.trans (map_zero _).symm))
  isVonNBounded x := by
    let B : E →L[ℝ] E →L[ℝ] ℝ := finiteImmersionInner (I := I) g f x
    have hp : ∀ v : E, v ≠ 0 → 0 < B v v := fun v hv =>
      g.pos (f x) _ fun h => hv (himm x (h.trans (map_zero _).symm))
    have hc := B.isCoercive_of_posDef hp
    change Bornology.IsVonNBounded ℝ {v : E | B v v < 1}
    exact NormedSpace.isVonNBounded_of_isBounded ℝ
      ((hc.isBounded_le 1).subset (fun v hv => show B v v ≤ 1 from le_of_lt hv))
  contMDiff x₀ := contMDiffAt_finiteImmersionInner g hf hmn hms x₀

@[simp] theorem finiteImmersionPullbackMetric_inner
    (g : ContMDiffRiemannianMetric J n F (TangentSpace J : N → Type _)) (f : M → N)
    (hf : ContMDiff I J s f) (himm : ∀ x, Function.Injective (mfderiv I J f x))
    (hmn : m ≤ n) (hms : m + 1 ≤ s) (x : M) (v w : TangentSpace I x) :
    (finiteImmersionPullbackMetric g f hf himm hmn hms).inner x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) :=
  rfl

end DifferentialGeometry.Geometry.FiniteSoul
