import DifferentialGeometry.Geometry.Metric.DirectLimit.Defs
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace SmoothSeqSystem

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
  [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [∀ k, SigmaCompactSpace (A k)] in
theorem enorm_mfderiv_incl (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) (a : A k) (v : TangentSpace I a) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
      ⟨(g k).toRiemannianMetric⟩
    ‖mfderiv I I (S.toSeqSystem.incl k) a v‖ₑ = ‖v‖ₑ := by
  let : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  rw [← ofReal_norm, ← ofReal_norm,
    norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  have h1 : (inner ℝ (mfderiv I I (S.toSeqSystem.incl k) a v)
        (mfderiv I I (S.toSeqSystem.incl k) a v) : ℝ)
      = (S.limitMetric g hg).inner (S.toSeqSystem.incl k a)
          (mfderiv I I (S.toSeqSystem.incl k) a v)
          (mfderiv I I (S.toSeqSystem.incl k) a v) := rfl
  have h2 : (inner ℝ v v : ℝ) = (g k).inner a v v := rfl
  rw [h1, h2, S.limitMetric_pullback g hg k a v v]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [∀ k, SigmaCompactSpace (A k)] in
theorem pathELength_incl (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) {γ : ℝ → A k} {t₀ t₁ : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc t₀ t₁)) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
      ⟨(g k).toRiemannianMetric⟩
    Manifold.pathELength I (S.toSeqSystem.incl k ∘ γ) t₀ t₁
      = Manifold.pathELength I γ t₀ t₁ := by
  let : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    ((hγ.mdifferentiableOn one_ne_zero) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  have hincl : MDifferentiableAt I I (S.toSeqSystem.incl k) (γ t) :=
    (S.contMDiff_incl k).mdifferentiableAt (by decide)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) I (S.toSeqSystem.incl k ∘ γ) t
      = (mfderiv I I (S.toSeqSystem.incl k) (γ t)).comp (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
    mfderiv_comp t hincl hγt
  rw [hcomp]
  exact S.enorm_mfderiv_incl g hg k (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [∀ k, SigmaCompactSpace (A k)] in
theorem riemannianEDist_incl_le (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) (a b : A k) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
      ⟨(g k).toRiemannianMetric⟩
    Manifold.riemannianEDist I (S.toSeqSystem.incl k a) (S.toSeqSystem.incl k b)
      ≤ Manifold.riemannianEDist I a b := by
  let : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  obtain ⟨γ, hγ0, hγ1, hγC, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr
  have hle : Manifold.riemannianEDist I (S.toSeqSystem.incl k a) (S.toSeqSystem.incl k b)
      ≤ Manifold.pathELength I (S.toSeqSystem.incl k ∘ γ) 0 1 :=
    Manifold.riemannianEDist_le_pathELength
      (((S.contMDiff_incl k).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)).comp_contMDiffOn hγC)
      (by rw [Function.comp_apply, hγ0]) (by rw [Function.comp_apply, hγ1]) zero_le_one
  refine hle.trans ?_
  rw [S.pathELength_incl g hg k hγC]
  exact hlen.le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [∀ k, SigmaCompactSpace (A k)] in
theorem pathELength_invIncl (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) {δ : ℝ → S.toSeqSystem.Lim} {t₀ t₁ : ℝ}
    (hδ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 δ (Set.Icc t₀ t₁))
    (hδr : ∀ t ∈ Set.Icc t₀ t₁, δ t ∈ Set.range (S.toSeqSystem.incl k)) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
      ⟨(g k).toRiemannianMetric⟩
    Manifold.pathELength I (Function.invFun (S.toSeqSystem.incl k) ∘ δ) t₀ t₁
      = Manifold.pathELength I δ t₀ t₁ := by
  let : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  have hpull : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (Function.invFun (S.toSeqSystem.incl k) ∘ δ)
      (Set.Icc t₀ t₁) := by
    intro t ht
    exact ContMDiffAt.comp_contMDiffWithinAt t
      ((S.contMDiffAt_invIncl k (hδr t ht)).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞))
      (hδ t ht)
  have h1 := S.pathELength_incl g hg k hpull
  have h2 : Manifold.pathELength I
      (S.toSeqSystem.incl k ∘ (Function.invFun (S.toSeqSystem.incl k) ∘ δ)) t₀ t₁
      = Manifold.pathELength I δ t₀ t₁ :=
    Manifold.pathELength_congr fun t ht => Function.invFun_eq (hδr t ht)
  rw [← h2, h1]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [∀ k, SigmaCompactSpace (A k)] in
theorem riemannianEDist_invIncl_le (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) {x y : S.toSeqSystem.Lim} {r : ENNReal}
    (hxy :
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      Manifold.riemannianEDist I x y < r)
    (hsub : ∀ z : S.toSeqSystem.Lim,
      (letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      Manifold.riemannianEDist I x z ≤ r) → z ∈ Set.range (S.toSeqSystem.incl k)) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun a : A k => TangentSpace I a) :=
      ⟨(g k).toRiemannianMetric⟩
    Manifold.riemannianEDist I
        (Function.invFun (S.toSeqSystem.incl k) x) (Function.invFun (S.toSeqSystem.incl k) y)
      ≤ r := by
  let : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  let : RiemannianBundle (fun a : A k => TangentSpace I a) :=
    ⟨(g k).toRiemannianMetric⟩
  obtain ⟨γ, hγ0, hγ1, hγC, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hxy
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Set.range (S.toSeqSystem.incl k) := by
    intro t ht
    refine hsub (γ t) ?_
    have hseg : Manifold.riemannianEDist I x (γ t)
        ≤ Manifold.pathELength I γ 0 t :=
      Manifold.riemannianEDist_le_pathELength
        (hγC.mono (Set.Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
    refine hseg.trans (le_trans ?_ hlen.le)
    exact Manifold.pathELength_mono le_rfl ht.2
  have hpull1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (Function.invFun (S.toSeqSystem.incl k) ∘ γ) (Set.Icc 0 1) := by
    intro t ht
    exact ContMDiffAt.comp_contMDiffWithinAt t
      ((S.contMDiffAt_invIncl k (hmem t ht)).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞))
      (hγC t ht)
  have hle : Manifold.riemannianEDist I
      (Function.invFun (S.toSeqSystem.incl k) x) (Function.invFun (S.toSeqSystem.incl k) y)
      ≤ Manifold.pathELength I (Function.invFun (S.toSeqSystem.incl k) ∘ γ) 0 1 :=
    Manifold.riemannianEDist_le_pathELength hpull1
      (by rw [Function.comp_apply, hγ0]) (by rw [Function.comp_apply, hγ1]) zero_le_one
  refine hle.trans ?_
  rw [S.pathELength_invIncl g hg k hγC hmem]
  exact hlen.le

end SmoothSeqSystem
end DifferentialGeometry
