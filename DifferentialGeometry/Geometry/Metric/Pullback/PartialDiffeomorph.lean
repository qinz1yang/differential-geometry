import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Pullback.Basic
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphOpens
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

theorem PartialDiffeomorph.exists_cutoff_pullback_inner
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ Φ.source) (h : SmoothRiemannianMetric I N) :
    ∃ (χ : M → ℝ) (P : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ),
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (∞ : WithTop ℕ∞)
        (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (P x)) ∧
      ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) χ ∧
      Set.EqOn χ 1 K ∧ tsupport χ ⊆ Φ.source ∧ (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ x : M, P x = χ x •
        (ContinuousLinearMap.precomp ℝ (mfderiv I I Φ x)).comp
          ((h.inner (Φ x)).comp (mfderiv I I Φ x)) := by
  classical
  obtain ⟨χ, hχ, _, hχK_nhds, hχsupp, hχrange⟩ :=
    Analysis.exists_mfd_bump (I := I) hK Φ.open_source hKs
  have hχK : Set.EqOn χ 1 K := fun _ hx => hχK_nhds.self_of_nhdsSet hx
  have hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := Set.range_subset_iff.mp hχrange
  set Q : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := fun x =>
    (ContinuousLinearMap.precomp ℝ (mfderiv I I Φ x)).comp
      ((h.inner (Φ x)).comp (mfderiv I I Φ x)) with hQ
  refine ⟨χ, fun x => χ x • Q x, ?_, hχ, hχK, hχsupp, hχ01, fun x => rfl⟩
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x => χ x • Q x)
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x => (χ x • Q x) (Y x))
  intro W x₀
  rw [Bundle.contMDiffAt_section]
  have hval : ∀ x : M, (χ x • Q x) (Y x) (W x)
      = χ x * (h.inner (Φ x) (mfderiv I I Φ x (Y x)) (mfderiv I I Φ x (W x))) := by
    intro x
    simp only [hQ, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.precomp_apply, smul_eq_mul]
  have hstage : ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun x => (χ x • Q x) (Y x) (W x)) x₀ := by
    by_cases hx₀ : x₀ ∈ Φ.source
    · have hφ : ContMDiffAt I I (∞ : WithTop ℕ∞) (Φ : M → N) x₀ :=
        Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hx₀)
      have hg' : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (∞ : WithTop ℕ∞)
          (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun b : N => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
            ((Φ : M → N) x) (h.inner ((Φ : M → N) x))) x₀ := by
        have hcomp := ContMDiffAt.comp (I' := I) x₀ (h.contMDiff ((Φ : M → N) x₀)) hφ
        exact hcomp
      have hφOn : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ : M → N) Φ.source :=
        Φ.contMDiffOn_toFun
      have htm : ContMDiffOn I.tangent I.tangent (∞ : WithTop ℕ∞)
          (tangentMapWithin I I (Φ : M → N) Φ.source)
          (Bundle.TotalSpace.proj ⁻¹' Φ.source) :=
        hφOn.contMDiffOn_tangentMapWithin le_rfl Φ.open_source.uniqueMDiffOn
      have hpre_open : IsOpen
          (Bundle.TotalSpace.proj ⁻¹' Φ.source : Set (TangentBundle I M)) :=
        Φ.open_source.preimage (FiberBundle.continuous_proj E (TangentSpace I))
      have hsec : ∀ Y' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
          ContMDiffAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
            (fun x => TotalSpace.mk' E (E := fun b : N => TangentSpace I b)
              ((Φ : M → N) x) (mfderiv I I (Φ : M → N) x (Y' x))) x₀ := by
        intro Y'
        have hYs : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
            (fun x => TotalSpace.mk' E (E := fun b : M => TangentSpace I b)
              x (Y' x)) x₀ := Y'.contMDiff x₀
        have hmem : (TotalSpace.mk' E (E := fun b : M => TangentSpace I b)
              x₀ (Y' x₀) : TangentBundle I M)
            ∈ Bundle.TotalSpace.proj ⁻¹' Φ.source := hx₀
        have hcomp := (htm.contMDiffAt (hpre_open.mem_nhds hmem)).comp x₀ hYs
        refine hcomp.congr_of_eventuallyEq ?_
        filter_upwards [Φ.open_source.mem_nhds hx₀] with x hx
        change TotalSpace.mk' E (E := fun b : N => TangentSpace I b)
            ((Φ : M → N) x) (mfderiv I I (Φ : M → N) x (Y' x))
          = TotalSpace.mk' E (E := fun b : N => TangentSpace I b)
            ((Φ : M → N) x)
            (mfderivWithin I I (Φ : M → N) Φ.source x (Y' x))
        rw [mfderivWithin_of_isOpen Φ.open_source hx]
      have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) (∞ : WithTop ℕ∞)
          (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial N ℝ)
            ((Φ : M → N) x)
            (h.inner ((Φ : M → N) x)
              (mfderiv I I (Φ : M → N) x (Y x))
              (mfderiv I I (Φ : M → N) x (W x)))) x₀ :=
        ContMDiffAt.clm_bundle_apply₂
          (E₁ := fun b : N => TangentSpace I b)
          (E₂ := fun b : N => TangentSpace I b)
          (E₃ := fun _ : N => ℝ)
          hg' (hsec Y) (hsec W)
      have h_scalar : ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (fun x => h.inner ((Φ : M → N) x)
            (mfderiv I I (Φ : M → N) x (Y x))
            (mfderiv I I (Φ : M → N) x (W x))) x₀ := by
        rw [contMDiffAt_totalSpace] at h_total
        simpa using h_total.2
      have hmul := (hχ.contMDiffAt (x := x₀)).mul h_scalar
      refine hmul.congr_of_eventuallyEq ?_
      filter_upwards with x
      exact hval x
    · have hx₀' : x₀ ∉ tsupport χ := fun hmem => hx₀ (hχsupp hmem)
      have hev : (fun x => (χ x • Q x) (Y x) (W x)) =ᶠ[nhds x₀] (fun _ => (0 : ℝ)) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx₀'] with x hx
        rw [hval x, image_eq_zero_of_notMem_tsupport hx, zero_mul]
      exact contMDiffAt_const.congr_of_eventuallyEq hev
  refine hstage.congr_of_eventuallyEq ?_
  filter_upwards with y
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem PartialDiffeomorph.pullback_inner_pos
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {x : M} (hx : x ∈ Φ.source) (h : SmoothRiemannianMetric I N)
    (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < h.inner ((Φ : M → N) x) (mfderiv I I (Φ : M → N) x v)
        (mfderiv I I (Φ : M → N) x v) := by
  refine h.pos _ _ (fun hzero => hv ?_)
  have hfg : (Φ.symm : N → M) ∘ (Φ : M → N) =ᶠ[nhds x] id := by
    filter_upwards [Φ.open_source.mem_nhds hx] with y hy
    exact Φ.left_inv' hy
  have hΦd : MDifferentiableAt I I (Φ : M → N) x :=
    (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hx)).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hΦsd : MDifferentiableAt I I (Φ.symm : N → M) ((Φ : M → N) x) :=
    (Φ.symm.contMDiffOn_toFun.contMDiffAt
      (Φ.symm.open_source.mem_nhds (Φ.map_source' hx))).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp : (mfderiv I I (Φ.symm : N → M) ((Φ : M → N) x)).comp
      (mfderiv I I (Φ : M → N) x) = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    rw [← mfderiv_comp x hΦsd hΦd, hfg.mfderiv_eq]
    exact mfderiv_id
  have happ : mfderiv I I (Φ.symm : N → M) ((Φ : M → N) x)
      (mfderiv I I (Φ : M → N) x v) = v := by
    have hv := DFunLike.congr_fun hcomp v
    rw [ContinuousLinearMap.comp_apply] at hv
    exact hv.trans (by rfl)
  rw [← happ, hzero]
  exact (mfderiv I I (Φ.symm : N → M) ((Φ : M → N) x)).map_zero

section PullbackMetricOn

variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [T2Space Y]

noncomputable def PartialDiffeomorph.pullbackMetricOn
    (Φ : PartialDiffeomorph I I X Y (∞ : WithTop ℕ∞))
    (U : TopologicalSpace.Opens X) (hU : (U : Set X) ⊆ Φ.source)
    (g : SmoothRiemannianMetric I Y) : SmoothRiemannianMetric I U := by
  let W : TopologicalSpace.Opens Y :=
    ⟨(Φ : X → Y) '' (U : Set X), image_opens_isOpen Φ hU⟩
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  exact Diffeomorph.pullbackMetric (I := I) (g.restrictOpen (I := I) W) F

theorem PartialDiffeomorph.pullbackMetricOn_inner
    (Φ : PartialDiffeomorph I I X Y (∞ : WithTop ℕ∞))
    (U : TopologicalSpace.Opens X) (hU : (U : Set X) ⊆ Φ.source)
    (g : SmoothRiemannianMetric I Y) (x : U) (v w : TangentSpace I x) :
    (PartialDiffeomorph.pullbackMetricOn Φ U hU g).inner x v w =
      g.inner ((Φ : X → Y) x)
        (mfderiv I I (Φ : X → Y) (x : X) v)
        (mfderiv I I (Φ : X → Y) (x : X) w) := by
  let W : TopologicalSpace.Opens Y :=
    ⟨(Φ : X → Y) '' (U : Set X), image_opens_isOpen Φ hU⟩
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  rw [PartialDiffeomorph.pullbackMetricOn, Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  rw [PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hU x v,
    PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hU x w]
  rfl

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z] [T2Space Z]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ X] [IsManifold I ∞ Y]
    [IsManifold I ∞ Z] [T2Space X] [T2Space Y] [T2Space Z] in
theorem PartialDiffeomorph.subset_trans_source
    (Φ : PartialDiffeomorph I I X Y (∞ : WithTop ℕ∞))
    (Θ : PartialDiffeomorph I I Y Z (∞ : WithTop ℕ∞))
    (U : TopologicalSpace.Opens X) (hU : (U : Set X) ⊆ Φ.source)
    (hnext : (Φ : X → Y) '' (U : Set X) ⊆ Θ.source) :
    (U : Set X) ⊆ (_root_.PartialDiffeomorph.trans (I := I) Φ Θ).source := by
  intro x hx
  exact ⟨hU hx, hnext (Set.mem_image_of_mem _ hx)⟩

noncomputable def PartialDiffeomorph.nestedPullbackMetricOn
    (Φ : PartialDiffeomorph I I X Y (∞ : WithTop ℕ∞))
    (Θ : PartialDiffeomorph I I Y Z (∞ : WithTop ℕ∞))
    (U : TopologicalSpace.Opens X) (hU : (U : Set X) ⊆ Φ.source)
    (hnext : (Φ : X → Y) '' (U : Set X) ⊆ Θ.source)
    (g : SmoothRiemannianMetric I Z) : SmoothRiemannianMetric I U := by
  let W : TopologicalSpace.Opens Y :=
    ⟨(Φ : X → Y) '' (U : Set X), image_opens_isOpen Φ hU⟩
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  exact Diffeomorph.pullbackMetric (I := I)
    (PartialDiffeomorph.pullbackMetricOn Θ W hnext g) F

theorem PartialDiffeomorph.pullbackMetricOn_trans
    (Φ : PartialDiffeomorph I I X Y (∞ : WithTop ℕ∞))
    (Θ : PartialDiffeomorph I I Y Z (∞ : WithTop ℕ∞))
    (U : TopologicalSpace.Opens X) (hU : (U : Set X) ⊆ Φ.source)
    (hnext : (Φ : X → Y) '' (U : Set X) ⊆ Θ.source)
    (g : SmoothRiemannianMetric I Z) :
    PartialDiffeomorph.pullbackMetricOn (_root_.PartialDiffeomorph.trans (I := I) Φ Θ) U
        (PartialDiffeomorph.subset_trans_source Φ Θ U hU hnext) g =
      PartialDiffeomorph.nestedPullbackMetricOn Φ Θ U hU hnext g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [PartialDiffeomorph.pullbackMetricOn_inner]
  let W : TopologicalSpace.Opens Y :=
    ⟨(Φ : X → Y) '' (U : Set X), image_opens_isOpen Φ hU⟩
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  change _ = (Diffeomorph.pullbackMetric (I := I)
    (PartialDiffeomorph.pullbackMetricOn Θ W hnext g) F).inner x v w
  rw [Diffeomorph.pullbackMetric_inner, PartialDiffeomorph.pullbackMetricOn_inner,
    PartialDiffeomorph.mfderiv_toOpensDiffeo,
    PartialDiffeomorph.mfderiv_toOpensDiffeo]
  have hΦd : MDifferentiableAt I I (Φ : X → Y) (x : X) :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hU x.2))).mdifferentiableAt (by decide)
  have hΘd : MDifferentiableAt I I (Θ : Y → Z) ((Φ : X → Y) x) :=
    (Θ.contMDiffOn_toFun.contMDiffAt
      (Θ.open_source.mem_nhds (hnext (Set.mem_image_of_mem _ x.2)))).mdifferentiableAt
        (by decide)
  have hcomp : mfderiv I I
      (_root_.PartialDiffeomorph.trans (I := I) Φ Θ : X → Z) (x : X) =
      (mfderiv I I (Θ : Y → Z) ((Φ : X → Y) x)).comp
        (mfderiv I I (Φ : X → Y) (x : X)) := by
    exact mfderiv_comp (x : X) hΘd hΦd
  rw [hcomp]
  rfl

theorem PartialDiffeomorph.pullbackMetricOn_congr
    (Φ Ψ : PartialDiffeomorph I I X Y (∞ : WithTop ℕ∞))
    (U : TopologicalSpace.Opens X) (hΦ : (U : Set X) ⊆ Φ.source)
    (hΨ : (U : Set X) ⊆ Ψ.source)
    (g : SmoothRiemannianMetric I Y)
    (hmap : Set.EqOn (Φ : X → Y) (Ψ : X → Y) U) :
    PartialDiffeomorph.pullbackMetricOn Φ U hΦ g =
      PartialDiffeomorph.pullbackMetricOn Ψ U hΨ g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hmap_nhds : (Φ : X → Y) =ᶠ[nhds (x : X)] (Ψ : X → Y) :=
    Filter.Eventually.mono (U.isOpen.mem_nhds x.2) fun y hy => hmap hy
  rw [PartialDiffeomorph.pullbackMetricOn_inner,
    PartialDiffeomorph.pullbackMetricOn_inner, hmap_nhds.eq_of_nhds,
    hmap_nhds.mfderiv_eq]

end PullbackMetricOn

end DifferentialGeometry
