import DifferentialGeometry.Topology.DirectLimitManifold
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Bundle.ClmSectionSmooth

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry

open Set Topology
open scoped Manifold ContDiff

namespace SmoothSeqSystem

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
variable (S : SmoothSeqSystem I A)

section MetricTransport

variable [FiniteDimensional ℝ E]
variable [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]

open Bundle

omit [FiniteDimensional ℝ E] in
private theorem mfd_comp_id
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂]
    {f : M₁ → M₂} {g' : M₂ → M₁} {x : M₁}
    (hfg : g' ∘ f =ᶠ[nhds x] id)
    (hg : MDifferentiableAt I I g' (f x)) (hf : MDifferentiableAt I I f x) :
    (mfderiv I I g' (f x)).comp (mfderiv I I f x)
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  rw [← mfderiv_comp x hg hf, hfg.mfderiv_eq]
  exact mfderiv_id

omit [FiniteDimensional ℝ E] in
private theorem mfd_comp_id_app
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂]
    {f : M₁ → M₂} {g' : M₂ → M₁} {x : M₁}
    (hfg : g' ∘ f =ᶠ[nhds x] id)
    (hg : MDifferentiableAt I I g' (f x)) (hf : MDifferentiableAt I I f x)
    (v : TangentSpace I x) :
    mfderiv I I g' (f x) (mfderiv I I f x v) = v := by
  have h := DFunLike.congr_fun (mfd_comp_id (I := I) hfg hg hf) v
  simpa using h

omit [FiniteDimensional ℝ E] in
private theorem inner_base_eq
    {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H M₀] [IsManifold I ∞ M₀]
    (g₀ : SmoothRiemannianMetric I M₀) {x y : M₀} (hxy : x = y) (v w : E) :
    (g₀.inner x : E →L[ℝ] E →L[ℝ] ℝ) v w = (g₀.inner y : E →L[ℝ] E →L[ℝ] ℝ) v w := by
  subst hxy; rfl


omit [FiniteDimensional ℝ E] in
private theorem mfd_base_eq
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂]
    (f : M₁ → M₂) {x y : M₁} (hxy : x = y) (v : E) :
    (mfderiv I I f x : E →L[ℝ] E) v = (mfderiv I I f y : E →L[ℝ] E) v := by
  subst hxy; rfl

def MetricCocycle (g : ∀ k, SmoothRiemannianMetric I (A k)) : Prop :=
  ∀ ⦃k ℓ : ℕ⦄ (h : k ≤ ℓ) (a : A k) (v w : TangentSpace I a),
    (g ℓ).inner (S.toSeqSystem.F h a)
      (mfderiv I I (S.toSeqSystem.F h) a v) (mfderiv I I (S.toSeqSystem.F h) a w)
      = (g k).inner a v w


omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem MetricCocycle.ofSucc (g : ∀ k, SmoothRiemannianMetric I (A k))
    (hstep : ∀ k (a : A k) (v w : TangentSpace I a),
      (g (k + 1)).inner (S.toSeqSystem.F (Nat.le_succ k) a)
        (mfderiv I I (S.toSeqSystem.F (Nat.le_succ k)) a v)
        (mfderiv I I (S.toSeqSystem.F (Nat.le_succ k)) a w) =
      (g k).inner a v w) :
    S.MetricCocycle g := by
  intro k l h
  induction l, h using Nat.le_induction with
  | base =>
      intro a v w
      have hself : S.toSeqSystem.F (Nat.le_refl k) = id := by
        funext x
        exact S.toSeqSystem.map_self k x
      rw [hself, mfderiv_id]
      rfl
  | succ l hkl ih =>
      intro a v w
      let hs : l ≤ l + 1 := Nat.le_succ l
      have hcomp : S.toSeqSystem.F (Nat.le.step hkl) =
          S.toSeqSystem.F hs ∘ S.toSeqSystem.F hkl := by
        funext x
        calc
          S.toSeqSystem.F (Nat.le.step hkl) x =
              S.toSeqSystem.F (hkl.trans hs) x :=
            S.toSeqSystem.F_apply_irrel (Nat.le.step hkl) (hkl.trans hs) x
          _ = S.toSeqSystem.F hs (S.toSeqSystem.F hkl x) :=
            (S.toSeqSystem.map_map hkl hs x).symm
      have hhd : MDifferentiableAt I I (S.toSeqSystem.F hkl) a :=
        (S.contMDiff_F hkl).contMDiffAt.mdifferentiableAt (by decide)
      have hsd : MDifferentiableAt I I (S.toSeqSystem.F hs)
          (S.toSeqSystem.F hkl a) :=
        (S.contMDiff_F hs).contMDiffAt.mdifferentiableAt (by decide)
      rw [hcomp, mfderiv_comp a hsd hhd]
      simp only [Function.comp_apply]
      calc
        (g (l + 1)).inner (S.toSeqSystem.F hs (S.toSeqSystem.F hkl a))
            (mfderiv I I (S.toSeqSystem.F hs) (S.toSeqSystem.F hkl a)
              (mfderiv I I (S.toSeqSystem.F hkl) a v))
            (mfderiv I I (S.toSeqSystem.F hs) (S.toSeqSystem.F hkl a)
              (mfderiv I I (S.toSeqSystem.F hkl) a w)) =
          (g l).inner (S.toSeqSystem.F hkl a)
            (mfderiv I I (S.toSeqSystem.F hkl) a v)
            (mfderiv I I (S.toSeqSystem.F hkl) a w) :=
          hstep l (S.toSeqSystem.F hkl a)
            (mfderiv I I (S.toSeqSystem.F hkl) a v)
            (mfderiv I I (S.toSeqSystem.F hkl) a w)
        _ = (g k).inner a v w := ih a v w

noncomputable def stageInner (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ)
    (z : S.toSeqSystem.Lim) :
    TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ :=
  let D := mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z
  let step1 : TangentSpace I z →L[ℝ]
      TangentSpace I (Function.invFun (S.toSeqSystem.incl k) z) →L[ℝ] ℝ :=
    ((g k).inner (Function.invFun (S.toSeqSystem.incl k) z)).comp D
  (ContinuousLinearMap.precomp ℝ D).comp step1

omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem stageInner_apply (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ)
    (z : S.toSeqSystem.Lim) (v w : TangentSpace I z) :
    S.stageInner g k z v w
      = (g k).inner (Function.invFun (S.toSeqSystem.incl k) z)
          (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z v)
          (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z w) := by
  unfold stageInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem stageInner_symm (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ)
    (z : S.toSeqSystem.Lim) (v w : TangentSpace I z) :
    S.stageInner g k z v w = S.stageInner g k z w v := by
  rw [stageInner_apply, stageInner_apply]
  exact (g k).symm _ _ _

omit [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
omit [FiniteDimensional ℝ E] in
theorem stageInner_pos (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ)
    {z : S.toSeqSystem.Lim} (hz : z ∈ Set.range (S.toSeqSystem.incl k))
    (v : TangentSpace I z) (hv : v ≠ 0) : 0 < S.stageInner g k z v v := by
  have hfg : (S.toSeqSystem.incl k) ∘ (Function.invFun (S.toSeqSystem.incl k))
      =ᶠ[nhds z] id := by
    filter_upwards [(S.toSeqSystem.incl_isOpenEmb k).isOpen_range.mem_nhds hz] with z' hz'
    exact Function.invFun_eq hz'
  have happ := mfd_comp_id_app (I := I) hfg
    ((S.contMDiff_incl k).mdifferentiableAt (by decide))
    ((S.contMDiffAt_invIncl k hz).mdifferentiableAt (by decide)) v
  rw [stageInner_apply]
  refine (g k).pos _ _ (fun h0 => hv ?_)
  rw [← happ, h0]
  exact (mfderiv I I (S.toSeqSystem.incl k) _).map_zero

omit [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
omit [FiniteDimensional ℝ E] in
theorem stageInner_bounded (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ)
    {z : S.toSeqSystem.Lim} (hz : z ∈ Set.range (S.toSeqSystem.incl k)) :
    Bornology.IsVonNBounded ℝ {v : TangentSpace I z | S.stageInner g k z v v < 1} := by
  classical
  have hza : S.toSeqSystem.incl k (Function.invFun (S.toSeqSystem.incl k) z) = z :=
    Function.invFun_eq hz
  have hfg1 : (S.toSeqSystem.incl k) ∘ (Function.invFun (S.toSeqSystem.incl k))
      =ᶠ[nhds z] id := by
    filter_upwards [(S.toSeqSystem.incl_isOpenEmb k).isOpen_range.mem_nhds hz] with z' hz'
    exact Function.invFun_eq hz'
  have hid1 := mfd_comp_id_app (I := I) hfg1
    ((S.contMDiff_incl k).mdifferentiableAt (by decide))
    ((S.contMDiffAt_invIncl k hz).mdifferentiableAt (by decide))
  have hfg2 : (Function.invFun (S.toSeqSystem.incl k)) ∘ (S.toSeqSystem.incl k)
      =ᶠ[nhds (Function.invFun (S.toSeqSystem.incl k) z)] id :=
    Filter.EventuallyEq.of_eq (Function.invFun_comp (S.toSeqSystem.incl_injective k))
  have hinv_at' : ContMDiffAt I I ∞ (Function.invFun (S.toSeqSystem.incl k))
      (S.toSeqSystem.incl k (Function.invFun (S.toSeqSystem.incl k) z)) := by
    rw [hza]; exact S.contMDiffAt_invIncl k hz
  have hid2 := mfd_comp_id_app (I := I) hfg2
    (hinv_at'.mdifferentiableAt (by decide))
    ((S.contMDiff_incl k).mdifferentiableAt (by decide))
  have hset : {v : TangentSpace I z | S.stageInner g k z v v < 1}
      = (mfderiv I I (S.toSeqSystem.incl k) (Function.invFun (S.toSeqSystem.incl k) z) :
            TangentSpace I (Function.invFun (S.toSeqSystem.incl k) z) →L[ℝ] TangentSpace I z) ''
          {u : TangentSpace I (Function.invFun (S.toSeqSystem.incl k) z) |
            (g k).inner (Function.invFun (S.toSeqSystem.incl k) z) u u < 1} := by
    ext v
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hv1
      refine ⟨mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z v, ?_, hid1 v⟩
      rw [stageInner_apply] at hv1
      exact hv1
    · rintro ⟨u, hu, rfl⟩
      rw [stageInner_apply]
      have hDu : mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z
          (mfderiv I I (S.toSeqSystem.incl k) (Function.invFun (S.toSeqSystem.incl k) z) u)
            = u := by
        have hb := mfd_base_eq (I := I) (Function.invFun (S.toSeqSystem.incl k)) hza
          (mfderiv I I (S.toSeqSystem.incl k) (Function.invFun (S.toSeqSystem.incl k) z) u)
        rw [← hb]
        exact hid2 u
      rw [hDu]
      exact hu
  rw [hset]
  exact ((g k).isVonNBounded _).image _

omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem stageInner_mono (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    {k m : ℕ} (hkm : k ≤ m) {z : S.toSeqSystem.Lim}
    (hz : z ∈ Set.range (S.toSeqSystem.incl k)) :
    S.stageInner g k z = S.stageInner g m z := by
  obtain ⟨a, rfl⟩ := hz
  have hinjk := S.toSeqSystem.incl_injective k
  have hinjm := S.toSeqSystem.incl_injective m
  have hφk : Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a) = a :=
    Function.leftInverse_invFun hinjk a
  have hcomp : S.toSeqSystem.incl m (S.toSeqSystem.F hkm a) = S.toSeqSystem.incl k a :=
    S.toSeqSystem.incl_comp hkm a
  have hφm : Function.invFun (S.toSeqSystem.incl m) (S.toSeqSystem.incl k a)
      = S.toSeqSystem.F hkm a := by
    conv_lhs => rw [← hcomp]
    exact Function.leftInverse_invFun hinjm _
  have hev : (S.toSeqSystem.F hkm) ∘ (Function.invFun (S.toSeqSystem.incl k))
      =ᶠ[nhds (S.toSeqSystem.incl k a)] Function.invFun (S.toSeqSystem.incl m) := by
    filter_upwards [(S.toSeqSystem.incl_isOpenEmb k).isOpen_range.mem_nhds ⟨a, rfl⟩] with z' hz'
    obtain ⟨a', rfl⟩ := hz'
    change S.toSeqSystem.F hkm (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a'))
      = Function.invFun (S.toSeqSystem.incl m) (S.toSeqSystem.incl k a')
    rw [Function.leftInverse_invFun hinjk a']
    conv_rhs => rw [← S.toSeqSystem.incl_comp hkm a']
    rw [Function.leftInverse_invFun hinjm _]
  have hφk_at : ContMDiffAt I I ∞ (Function.invFun (S.toSeqSystem.incl k))
      (S.toSeqSystem.incl k a) := S.contMDiffAt_invIncl k ⟨a, rfl⟩
  have hD : (mfderiv I I (S.toSeqSystem.F hkm)
        (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a))).comp
      (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) (S.toSeqSystem.incl k a))
      = mfderiv I I (Function.invFun (S.toSeqSystem.incl m)) (S.toSeqSystem.incl k a) := by
    rw [← mfderiv_comp _ ((S.contMDiff_F hkm).mdifferentiableAt (by decide))
      (hφk_at.mdifferentiableAt (by decide))]
    exact hev.mfderiv_eq
  have hDapp : ∀ u : TangentSpace I (S.toSeqSystem.incl k a),
      mfderiv I I (S.toSeqSystem.F hkm)
        (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a))
        (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) (S.toSeqSystem.incl k a) u)
      = mfderiv I I (Function.invFun (S.toSeqSystem.incl m)) (S.toSeqSystem.incl k a) u := by
    intro u
    have h := DFunLike.congr_fun hD u
    simpa using h
  have hFb : S.toSeqSystem.F hkm (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a))
      = Function.invFun (S.toSeqSystem.incl m) (S.toSeqSystem.incl k a) := by
    rw [hφk, hφm]
  apply ContinuousLinearMap.ext; intro v
  apply ContinuousLinearMap.ext; intro w
  rw [stageInner_apply, stageInner_apply]
  calc (g k).inner (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a))
        (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) (S.toSeqSystem.incl k a) v)
        (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) (S.toSeqSystem.incl k a) w)
      = (g m).inner (S.toSeqSystem.F hkm
            (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a)))
          (mfderiv I I (S.toSeqSystem.F hkm)
            (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a))
            (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) (S.toSeqSystem.incl k a) v))
          (mfderiv I I (S.toSeqSystem.F hkm)
            (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a))
            (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) (S.toSeqSystem.incl k a) w)) :=
        (hg hkm _ _ _).symm
    _ = (g m).inner (S.toSeqSystem.F hkm
            (Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a)))
          (mfderiv I I (Function.invFun (S.toSeqSystem.incl m)) (S.toSeqSystem.incl k a) v)
          (mfderiv I I (Function.invFun (S.toSeqSystem.incl m)) (S.toSeqSystem.incl k a) w) := by
        rw [hDapp v, hDapp w]
    _ = (g m).inner (Function.invFun (S.toSeqSystem.incl m) (S.toSeqSystem.incl k a))
          (mfderiv I I (Function.invFun (S.toSeqSystem.incl m)) (S.toSeqSystem.incl k a) v)
          (mfderiv I I (Function.invFun (S.toSeqSystem.incl m)) (S.toSeqSystem.incl k a) w) :=
        inner_base_eq (g m) hFb _ _

omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem stageInner_congr (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    {k ℓ : ℕ} {z : S.toSeqSystem.Lim}
    (hzk : z ∈ Set.range (S.toSeqSystem.incl k)) (hzℓ : z ∈ Set.range (S.toSeqSystem.incl ℓ)) :
    S.stageInner g k z = S.stageInner g ℓ z :=
  (S.stageInner_mono g hg (le_max_left k ℓ) hzk).trans
    (S.stageInner_mono g hg (le_max_right k ℓ) hzℓ).symm

omit [FiniteDimensional ℝ E] [∀ (k : ℕ), SigmaCompactSpace (A k)] [∀ (k : ℕ), T2Space (A k)] in
theorem mem_range_rep (z : S.toSeqSystem.Lim) :
    z ∈ Set.range (S.toSeqSystem.incl (S.toSeqSystem.rep z).1) :=
  ⟨(S.toSeqSystem.rep z).2, S.toSeqSystem.incl_rep z⟩

noncomputable def limitMetric (g : ∀ k, SmoothRiemannianMetric I (A k))
    (hg : S.MetricCocycle g) : SmoothRiemannianMetric I S.toSeqSystem.Lim where
  inner z := S.stageInner g (S.toSeqSystem.rep z).1 z
  symm z v w := S.stageInner_symm g _ z v w
  pos z v hv := S.stageInner_pos g _ (S.mem_range_rep z) v hv
  isVonNBounded z := S.stageInner_bounded g _ (S.mem_range_rep z)
  contMDiff := by
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun z : S.toSeqSystem.Lim => TangentSpace I z →L[ℝ] ℝ)
      (φ := fun z => S.stageInner g (S.toSeqSystem.rep z).1 z)
    intro Y
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun _ : S.toSeqSystem.Lim => ℝ)
      (φ := fun z => S.stageInner g (S.toSeqSystem.rep z).1 z (Y z))
    intro W z₀
    rw [Bundle.contMDiffAt_section]
    have hstage : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun z => S.stageInner g (S.toSeqSystem.rep z).1 z (Y z) (W z)) z₀ := by
      set k₀ := (S.toSeqSystem.rep z₀).1 with hk₀
      have hz₀ : z₀ ∈ Set.range (S.toSeqSystem.incl k₀) := S.mem_range_rep z₀
      have hs_open : IsOpen (Set.range (S.toSeqSystem.incl k₀)) :=
        (S.toSeqSystem.incl_isOpenEmb k₀).isOpen_range
      have hφ : ContMDiffAt I I ∞ (Function.invFun (S.toSeqSystem.incl k₀)) z₀ :=
        S.contMDiffAt_invIncl k₀ hz₀
      have hg' : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun z => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun b : A k₀ => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
            (Function.invFun (S.toSeqSystem.incl k₀) z)
            ((g k₀).inner (Function.invFun (S.toSeqSystem.incl k₀) z))) z₀ := by
        have h := ContMDiffAt.comp (I' := I) z₀
          ((g k₀).contMDiff (Function.invFun (S.toSeqSystem.incl k₀) z₀)) hφ
        exact h
      have hφOn : ContMDiffOn I I ∞ (Function.invFun (S.toSeqSystem.incl k₀))
          (Set.range (S.toSeqSystem.incl k₀)) :=
        fun z hz => (S.contMDiffAt_invIncl k₀ hz).contMDiffWithinAt
      have htm : ContMDiffOn I.tangent I.tangent ∞
          (tangentMapWithin I I (Function.invFun (S.toSeqSystem.incl k₀))
            (Set.range (S.toSeqSystem.incl k₀)))
          (Bundle.TotalSpace.proj ⁻¹' (Set.range (S.toSeqSystem.incl k₀))) :=
        hφOn.contMDiffOn_tangentMapWithin le_rfl hs_open.uniqueMDiffOn
      have hpre_open : IsOpen
          (Bundle.TotalSpace.proj ⁻¹' (Set.range (S.toSeqSystem.incl k₀)) :
            Set (TangentBundle I S.toSeqSystem.Lim)) :=
        hs_open.preimage (FiberBundle.continuous_proj E (TangentSpace I))
      have hsec : ∀ Y' : Cₛ^∞⟮I; E, (TangentSpace I : S.toSeqSystem.Lim → Type _)⟯,
          ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
            (fun z => TotalSpace.mk' E (E := fun b : A k₀ => TangentSpace I b)
              (Function.invFun (S.toSeqSystem.incl k₀) z)
              (mfderiv I I (Function.invFun (S.toSeqSystem.incl k₀)) z (Y' z))) z₀ := by
        intro Y'
        have hYs : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
            (fun z => TotalSpace.mk' E (E := fun b : S.toSeqSystem.Lim => TangentSpace I b)
              z (Y' z)) z₀ := Y'.contMDiff z₀
        have hmem : (TotalSpace.mk' E (E := fun b : S.toSeqSystem.Lim => TangentSpace I b)
              z₀ (Y' z₀) : TangentBundle I S.toSeqSystem.Lim)
            ∈ Bundle.TotalSpace.proj ⁻¹' (Set.range (S.toSeqSystem.incl k₀)) := hz₀
        have hcomp := (htm.contMDiffAt (hpre_open.mem_nhds hmem)).comp z₀ hYs
        refine hcomp.congr_of_eventuallyEq ?_
        filter_upwards [hs_open.mem_nhds hz₀] with z hz
        change TotalSpace.mk' E (E := fun b : A k₀ => TangentSpace I b)
            (Function.invFun (S.toSeqSystem.incl k₀) z)
            (mfderiv I I (Function.invFun (S.toSeqSystem.incl k₀)) z (Y' z))
          = TotalSpace.mk' E (E := fun b : A k₀ => TangentSpace I b)
            (Function.invFun (S.toSeqSystem.incl k₀) z)
            (mfderivWithin I I (Function.invFun (S.toSeqSystem.incl k₀))
              (Set.range (S.toSeqSystem.incl k₀)) z (Y' z))
        rw [mfderivWithin_of_isOpen hs_open hz]
      have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
          (fun z => TotalSpace.mk' ℝ (E := Bundle.Trivial (A k₀) ℝ)
            (Function.invFun (S.toSeqSystem.incl k₀) z)
            ((g k₀).inner (Function.invFun (S.toSeqSystem.incl k₀) z)
              (mfderiv I I (Function.invFun (S.toSeqSystem.incl k₀)) z (Y z))
              (mfderiv I I (Function.invFun (S.toSeqSystem.incl k₀)) z (W z)))) z₀ :=
        ContMDiffAt.clm_bundle_apply₂
          (E₁ := fun b : A k₀ => TangentSpace I b)
          (E₂ := fun b : A k₀ => TangentSpace I b)
          (E₃ := fun _ : A k₀ => ℝ)
          hg' (hsec Y) (hsec W)
      have h_scalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun z => (g k₀).inner (Function.invFun (S.toSeqSystem.incl k₀) z)
            (mfderiv I I (Function.invFun (S.toSeqSystem.incl k₀)) z (Y z))
            (mfderiv I I (Function.invFun (S.toSeqSystem.incl k₀)) z (W z))) z₀ := by
        rw [contMDiffAt_totalSpace] at h_total
        convert h_total.2 using 1
      refine h_scalar.congr_of_eventuallyEq ?_
      filter_upwards [hs_open.mem_nhds hz₀] with z hz
      rw [show S.stageInner g (S.toSeqSystem.rep z).1 z = S.stageInner g k₀ z from
        S.stageInner_congr g hg (S.mem_range_rep z) hz]
      exact S.stageInner_apply g k₀ z (Y z) (W z)
    refine hstage.congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl

omit [∀ k, SigmaCompactSpace (A k)] in
theorem limitMetric_pullback (g : ∀ k, SmoothRiemannianMetric I (A k))
    (hg : S.MetricCocycle g) (k : ℕ) (a : A k) (v w : TangentSpace I a) :
    (S.limitMetric g hg).inner (S.toSeqSystem.incl k a)
        (mfderiv I I (S.toSeqSystem.incl k) a v) (mfderiv I I (S.toSeqSystem.incl k) a w)
      = (g k).inner a v w := by
  have hz : S.toSeqSystem.incl k a ∈ Set.range (S.toSeqSystem.incl k) := ⟨a, rfl⟩
  have hstage : (S.limitMetric g hg).inner (S.toSeqSystem.incl k a)
      = S.stageInner g k (S.toSeqSystem.incl k a) := by
    change S.stageInner g (S.toSeqSystem.rep (S.toSeqSystem.incl k a)).1 (S.toSeqSystem.incl k a)
      = S.stageInner g k (S.toSeqSystem.incl k a)
    exact S.stageInner_congr g hg (S.mem_range_rep _) hz
  rw [hstage, stageInner_apply]
  have hφk : Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl k a) = a :=
    Function.leftInverse_invFun (S.toSeqSystem.incl_injective k) a
  have hfg : (Function.invFun (S.toSeqSystem.incl k)) ∘ (S.toSeqSystem.incl k)
      =ᶠ[nhds a] id :=
    Filter.EventuallyEq.of_eq (Function.invFun_comp (S.toSeqSystem.incl_injective k))
  have hinv_at : ContMDiffAt I I ∞ (Function.invFun (S.toSeqSystem.incl k))
      (S.toSeqSystem.incl k a) := S.contMDiffAt_invIncl k hz
  have happ := mfd_comp_id_app (I := I) hfg
    (hinv_at.mdifferentiableAt (by decide))
    ((S.contMDiff_incl k).mdifferentiableAt (by decide))
  rw [happ v, happ w]
  exact inner_base_eq (g k) hφk v w

omit [∀ k, SigmaCompactSpace (A k)] in
theorem limitMetric_of_mem (g : ∀ k, SmoothRiemannianMetric I (A k))
    (hg : S.MetricCocycle g) (k : ℕ) {z : S.toSeqSystem.Lim}
    (hz : z ∈ Set.range (S.toSeqSystem.incl k)) (v w : TangentSpace I z) :
    (S.limitMetric g hg).inner z v w =
      (g k).inner (Function.invFun (S.toSeqSystem.incl k) z)
        (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z v)
        (mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z w) := by
  have hstage : (S.limitMetric g hg).inner z = S.stageInner g k z := by
    change S.stageInner g (S.toSeqSystem.rep z).1 z = S.stageInner g k z
    exact S.stageInner_congr g hg (S.mem_range_rep z) hz
  rw [hstage, S.stageInner_apply]

end MetricTransport

end SmoothSeqSystem

end DifferentialGeometry
