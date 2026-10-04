import DifferentialGeometry.Bundle.ContinuousLinearMapSection.PointwiseSmoothness
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
noncomputable section
open Bundle FiberBundle Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

private theorem contMDiffAt_hom_section_of_local_apply
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
    {n : WithTop ℕ∞}
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I] {x₀ : M}
    (φ : ∀ x : M, TangentSpace I x →L[ℝ] V₂ x)
    (h : ∀ Y : ∀ x : M, TangentSpace I x,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (fun x => TotalSpace.mk' E x (Y x)) x₀ →
      ContMDiffAt I (I.prod 𝓘(ℝ, F₂)) n
        (fun x => TotalSpace.mk' F₂ (E := V₂) x (φ x (Y x))) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) n
      (fun x => TotalSpace.mk' (E →L[ℝ] F₂)
        (E := fun x : M => TangentSpace I x →L[ℝ] V₂ x) x (φ x)) x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_pointwise
  intro v
  let e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀
  let e₂ := trivializationAt F₂ V₂ x₀
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have he₂ : x₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ V₂ x₀
  have hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun x => TotalSpace.mk' E (E := TangentSpace I) x (e₁.symmL ℝ x v)) x₀ := by
    apply (e₁.contMDiffAt_symmL he₁).clm_bundle_apply
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, contMDiffAt_const⟩
  have hφ := (contMDiffAt_section (F := F₂) (E := V₂) x₀).mp
    (h (fun x => e₁.symmL ℝ x v) hY)
  apply hφ.congr_of_eventuallyEq
  filter_upwards [e₂.open_baseSet.mem_nhds he₂] with x hx
  change e₂.continuousLinearMapAt ℝ x (φ x (e₁.symmL ℝ x v)) =
    (e₂ ⟨x, φ x (e₁.symmL ℝ x v)⟩).2
  rw [show ⇑(e₂.continuousLinearMapAt ℝ x) = ⇑(e₂.linearMapAt ℝ x) from rfl,
    e₂.coe_linearMapAt_of_mem hx]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]

private def finitePullbackInner {K : WithTop ℕ∞}
    (g : ContMDiffRiemannianMetric J K F (TangentSpace J : N → Type _))
    (f : M → N) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (mfderiv I J f x)).comp
    ((g.inner (f x)).comp (mfderiv I J f x))

private theorem finitePullbackInner_contMDiff
    {K s r : ℕ}
    [ContMDiffVectorBundle (r : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    (hrK : r ≤ K) (hrs : r + 1 ≤ s)
    (g : ContMDiffRiemannianMetric J (K : WithTop ℕ∞) F (TangentSpace J : N → Type _))
    (f : M → N) (hf : ContMDiff I J (s : WithTop ℕ∞) f) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (r : WithTop ℕ∞)
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          x (finitePullbackInner (I := I) g f x)) := by
  intro x₀
  apply contMDiffAt_hom_section_of_local_apply
  intro Y hY
  apply contMDiffAt_hom_section_of_local_apply
  intro W hW
  have ht : ContMDiff I.tangent J.tangent (r : WithTop ℕ∞) (tangentMap I J f) :=
    hf.contMDiff_tangentMap (by exact_mod_cast hrs)
  have hv := ht.contMDiffAt.comp x₀ hY
  have hw := ht.contMDiffAt.comp x₀ hW
  have hg := (g.contMDiff.of_le (show (r : WithTop ℕ∞) ≤ K by exact_mod_cast hrK)).contMDiffAt.comp x₀
    (hf.of_le (show (r : WithTop ℕ∞) ≤ s by exact_mod_cast (Nat.le_succ r).trans hrs)).contMDiffAt
  have he := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun b : N => TangentSpace J b)
    (E₂ := fun b : N => TangentSpace J b)
    (E₃ := fun _ : N => ℝ)
    (b := f) (ψ := fun x => g.inner (f x))
    (v := fun x => mfderiv I J f x (Y x))
    (w := fun x => mfderiv I J f x (W x)) hg hv hw
  have hs : ContMDiffAt I 𝓘(ℝ, ℝ) (r : WithTop ℕ∞)
      (fun x => g.inner (f x) (mfderiv I J f x (Y x)) (mfderiv I J f x (W x))) x₀ := by
    rw [contMDiffAt_totalSpace] at he
    exact he.2
  rw [contMDiffAt_section]
  apply hs.congr_of_eventuallyEq
  filter_upwards with x
  rfl

namespace Geometry

omit [IsManifold I 1 M] in
theorem exists_finite_order_pullback_metric
    (K s r : ℕ) [IsManifold I ((r + 1 : ℕ) : WithTop ℕ∞) M] (hrK : r ≤ K) (hrs : r + 1 ≤ s)
    (g : ContMDiffRiemannianMetric J (K : WithTop ℕ∞) F (TangentSpace J : N → Type _))
    (f : M → N) (hf : ContMDiff I J (s : WithTop ℕ∞) f)
    (himm : ∀ x, Function.Injective (mfderiv I J f x)) :
    let : IsManifold I 1 M := IsManifold.of_le (n := ((r + 1 : ℕ) : WithTop ℕ∞)) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le r))
    ∃ h : ContMDiffRiemannianMetric I (r : WithTop ℕ∞)
        E (TangentSpace I : M → Type _),
      ∀ (x : M) (v w : TangentSpace I x),
        h.inner x v w = g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ((r + 1 : ℕ) : WithTop ℕ∞)) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le r))
  have : IsManifold I ((r : WithTop ℕ∞) + 1) M := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (inferInstance : IsManifold I ((r + 1 : ℕ) : WithTop ℕ∞) M)
  let : ContMDiffVectorBundle (r : WithTop ℕ∞) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hpos : ∀ x, ∀ v : TangentSpace I x, v ≠ 0 →
      0 < finitePullbackInner (I := I) g f x v v := by
    intro x v hv
    apply g.pos
    exact fun hz => hv (himm x (by simpa using hz))
  refine ⟨{
    inner := finitePullbackInner (I := I) g f
    symm := fun x v w => g.symm (f x) _ _
    pos := hpos
    isVonNBounded := ?_
    contMDiff := finitePullbackInner_contMDiff (I := I) hrK hrs g f hf }, fun _ _ _ => rfl⟩
  intro x
  let B : E →L[ℝ] E →L[ℝ] ℝ := finitePullbackInner (I := I) g f x
  have hc := B.isCoercive_of_posDef (hpos x)
  change Bornology.IsVonNBounded ℝ {v : E | B v v < 1}
  exact NormedSpace.isVonNBounded_of_isBounded ℝ
    ((hc.isBounded_le 1).subset (fun v hv => show B v v ≤ 1 from le_of_lt hv))

omit [IsManifold I 1 M] in
theorem exists_finite_order_pullback_metric_of_diffeomorph
    (K s r : ℕ) [IsManifold I ((r + 1 : ℕ) : WithTop ℕ∞) M]
    (hrK : r ≤ K) (hrs : r + 1 ≤ s)
    (g : ContMDiffRiemannianMetric J (K : WithTop ℕ∞) F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N (s : WithTop ℕ∞)) :
    letI : IsManifold I 1 M := IsManifold.of_le (n := ((r + 1 : ℕ) : WithTop ℕ∞)) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le r))
    ∃ h : ContMDiffRiemannianMetric I (r : WithTop ℕ∞)
        E (TangentSpace I : M → Type _),
      ∀ (x : M) (v w : TangentSpace I x),
        h.inner x v w = g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  apply exists_finite_order_pullback_metric K s r hrK hrs g f f.contMDiff
  have hs : (s : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt ((Nat.succ_pos r).trans_le hrs)
  intro x
  exact (f.mfderivToContinuousLinearEquiv hs x).injective

end Geometry
end DifferentialGeometry
