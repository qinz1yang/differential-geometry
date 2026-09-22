import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Geometry.Operator.Restriction
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false
noncomputable section
open Bundle Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N] [BoundarylessManifold J N]

private theorem inner_cov_gradient_pullbackCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    {f : N → ℝ} {x : M} (hf : ContMDiffAt J 𝓘(ℝ, ℝ) 2 f (Φ x))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    (Diffeomorph.pullbackMetricCross g Φ).inner x
      (LeviCivita (Diffeomorph.pullbackMetricCross g Φ)
        (fun y => gradientFun (Diffeomorph.pullbackMetricCross g Φ) (f ∘ Φ) y) x v) (X x) =
      g.inner (Φ x) (LeviCivita g (fun y => gradientFun g f y) (Φ x)
        (mfderiv I J Φ x v)) (mfderiv I J Φ x (X x)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let h := Diffeomorph.pullbackMetricCross g Φ
  let Y := pushFwdSectionCross Φ X
  have hcomp : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (f ∘ Φ) x :=
    hf.comp x (Φ.contMDiff.contMDiffAt.of_le (by decide))
  have hg1 := (gradientFun_contMDiffAt_one h hcomp).mdifferentiableAt (by norm_num)
  have hg2 := (gradientFun_contMDiffAt_one g hf).mdifferentiableAt (by norm_num)
  have hc1 := (LeviCivita_isMetricCompatible h).apply hg1 X.mdifferentiableAt v
  have hc2 := (LeviCivita_isMetricCompatible g).apply hg2 Y.mdifferentiableAt (mfderiv I J Φ x v)
  have heq : (fun y => h.inner y (gradientFun h (f ∘ Φ) y) (X y)) =ᶠ[𝓝 x]
      (fun y => mfderiv J 𝓘(ℝ, ℝ) f (Φ y) (Y (Φ y))) := by
    have hfe : ∀ᶠ y in 𝓝 (Φ x), MDifferentiableAt J 𝓘(ℝ, ℝ) f y := by
      filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hf] with y hy
      exact hy.mdifferentiableAt (by norm_num)
    filter_upwards [Φ.continuous.continuousAt.tendsto.eventually hfe] with y hy
    rw [inner_gradientFun, mvfderiv_comp_apply y hy (Φ.contMDiff.mdifferentiableAt (by simp))]
    rw [show Y (Φ y) = mfderiv I J Φ y (X y) from pushFwdSectionCross_apply_at_image Φ X y]
    rfl
  have hdir : MDifferentiableAt J 𝓘(ℝ, ℝ)
      (fun y => mfderiv J 𝓘(ℝ, ℝ) f y (Y y)) (Φ x) :=
    (mvfderiv_apply_contMDiffAt_of_section_one hf
      (Y.contMDiff.contMDiffAt.of_le (by simp))).mdifferentiableAt (by norm_num)
  have hd : (mfderiv I 𝓘(ℝ, ℝ) (fun y => h.inner y (gradientFun h (f ∘ Φ) y) (X y)) x : TangentSpace I x →L[ℝ] ℝ) =
      mfderiv I 𝓘(ℝ, ℝ) (fun y => mfderiv J 𝓘(ℝ, ℝ) f (Φ y) (Y (Φ y))) x := heq.mfderiv_eq
  have hdv := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) hd
  change mfderiv I 𝓘(ℝ, ℝ) (fun y => h.inner y (gradientFun h (f ∘ Φ) y) (X y)) x v =
    mfderiv I 𝓘(ℝ, ℝ) ((fun y => mfderiv J 𝓘(ℝ, ℝ) f y (Y y)) ∘ Φ) x v at hdv
  have hchain := mvfderiv_comp_apply x hdir (Φ.contMDiff.mdifferentiableAt (by simp)) v
  have hdv' := hdv.trans hchain
  have hinner : (fun y => g.inner y (gradientFun g f y) (Y y)) =
      (fun y => mfderiv J 𝓘(ℝ, ℝ) f y (Y y)) := by funext y; exact inner_gradientFun g f y (Y y)
  rw [hinner] at hc2
  have hconn : h.inner x (gradientFun h (f ∘ Φ) x) (LeviCivita h X x v) =
      g.inner (Φ x) (gradientFun g f (Φ x)) (LeviCivita g Y (Φ x) (mfderiv I J Φ x v)) := by
    rw [inner_gradientFun, mvfderiv_comp_apply x (hf.mdifferentiableAt (by norm_num))
      (Φ.contMDiff.mdifferentiableAt (by simp)), inner_gradientFun]
    congr 1
    exact metricCov_pullbackCross g Φ X x v
  have hY : Y (Φ x) = mfderiv I J Φ x (X x) := pushFwdSectionCross_apply_at_image Φ X x
  rw [hY] at hc2
  rw [hconn] at hc1
  exact add_right_cancel (hc1.symm.trans (hdv'.trans hc2))

theorem laplacian_pullbackCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    {f : N → ℝ} {x : M} (hf : ContMDiffAt J 𝓘(ℝ, ℝ) 2 f (Φ x)) :
    laplacian (LeviCivita (Diffeomorph.pullbackMetricCross g Φ))
      (Diffeomorph.pullbackMetricCross g Φ) (f ∘ Φ) x =
      laplacian (LeviCivita g) g f (Φ x) := by
  let h := Diffeomorph.pullbackMetricCross g Φ
  let e := Φ.mfderivToContinuousLinearEquiv (by simp : (∞ : WithTop ℕ∞) ≠ 0) x
  have he (v : TangentSpace I x) : e v = mfderiv I J Φ x v :=
    congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) => L v)
      (Φ.mfderivToContinuousLinearEquiv_coe (by simp))
  have hcov (v : TangentSpace I x) :
      e (LeviCivita h (fun y => gradientFun h (f ∘ Φ) y) x v) =
        LeviCivita g (fun y => gradientFun g f y) (Φ x) (e v) := by
    apply (metricFlatEquiv g (Φ x)).injective
    ext w
    obtain ⟨z, rfl⟩ := e.surjective w
    obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := TangentSpace I) (n := (⊤ : ℕ∞)) x z
    rw [metricFlatEquiv_apply, metricFlatEquiv_apply, he, he, he,
      ← Diffeomorph.pullbackMetricCross_inner]
    rw [← hX]
    exact inner_cov_gradient_pullbackCross g Φ hf X v
  let A := (LeviCivita h (fun y => gradientFun h (f ∘ Φ) y) x).toLinearMap
  let B := (LeviCivita g (fun y => gradientFun g f y) (Φ x)).toLinearMap
  have hconj : B = e.toLinearEquiv.conj A := by
    ext v
    have hv := hcov (e.symm v)
    change e (A (e.symm v)) = B (e (e.symm v)) at hv
    rw [e.apply_symm_apply] at hv
    exact hv.symm
  change LinearMap.trace ℝ (TangentSpace I x) A = LinearMap.trace ℝ (TangentSpace J (Φ x)) B
  rw [hconj, LinearMap.trace_conj']

theorem laplacian_eq_of_partialDiffeomorph_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞) {x : M} (hx : x ∈ Φ.source)
    (hinner : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      g.inner y v w = h.inner (Φ y) (mfderiv I J Φ y v) (mfderiv I J Φ y w))
    {f : N → ℝ} (hf : ContMDiffAt J 𝓘(ℝ, ℝ) 2 f (Φ x)) :
    laplacian (LeviCivita g) g (f ∘ Φ) x = laplacian (LeviCivita h) h f (Φ x) := by
  obtain ⟨s, hs, hsopen, hxs⟩ := mem_nhds_iff.mp
    (inter_mem hinner (Φ.open_source.mem_nhds hx))
  let U : TopologicalSpace.Opens M := ⟨s, hsopen⟩
  have hU : (U : Set M) ⊆ Φ.source := fun y hy => (hs hy).2
  let V : TopologicalSpace.Opens N :=
    ⟨(Φ : M → N) '' (U : Set M), DifferentialGeometry.image_opens_isOpen Φ hU⟩
  let Ψ : U ≃ₘ⟮I, J⟯ V := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU
  let xu : U := ⟨x, hxs⟩
  have hΨd (y : U) (v : TangentSpace I y) :
      mfderiv I J Ψ y v = mfderiv I J Φ (y : M) v :=
    DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hU y v
  have hmetric : g.restrictOpen U = Diffeomorph.pullbackMetricCross (h.restrictOpen V) Ψ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    simp only [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
      hΨd]
    exact (hs y.property).1 v w
  have hcomp : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (f ∘ Φ) x :=
    hf.comp x ((Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hx)).of_le (by decide))
  have hfV : ContMDiffAt J 𝓘(ℝ, ℝ) 2 (fun y : V => f (y : N)) (Ψ xu) := by
    apply ContMDiffAt.comp (Ψ xu) _ (contMDiff_subtype_val (I := J) (U := V)).contMDiffAt
    exact hf
  calc
    _ = laplacian (LeviCivita (g.restrictOpen U)) (g.restrictOpen U)
        (fun y : U => f (Φ (y : M))) xu :=
      (laplacian_restrictOpen_of_contMDiffAt g U (x := xu) (f := f ∘ Φ) hcomp).symm
    _ = laplacian (LeviCivita (Diffeomorph.pullbackMetricCross (h.restrictOpen V) Ψ))
        (Diffeomorph.pullbackMetricCross (h.restrictOpen V) Ψ)
        ((fun y : V => f (y : N)) ∘ Ψ) xu := by rw [hmetric]; rfl
    _ = laplacian (LeviCivita (h.restrictOpen V)) (h.restrictOpen V)
        (fun y : V => f (y : N)) (Ψ xu) := laplacian_pullbackCross (h.restrictOpen V) Ψ (x := xu) (f := fun y : V => f (y : N)) hfV
    _ = _ := laplacian_restrictOpen_of_contMDiffAt h V (x := Ψ xu) (f := f) hf

theorem laplacian_comp_symm_eq_of_partialDiffeomorph_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞) {x : M} (hx : x ∈ Φ.source)
    (hinner : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      g.inner y v w = h.inner (Φ y) (mfderiv I J Φ y v) (mfderiv I J Φ y w))
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) :
    laplacian (LeviCivita h) h (f ∘ Φ.symm) (Φ x) = laplacian (LeviCivita g) g f x := by
  have hleft : Φ.symm (Φ x) = x := Φ.left_inv' hx
  have htarget := Φ.map_source' hx
  have hinv : Tendsto (Φ.symm : N → M) (𝓝 (Φ x)) (𝓝 x) := by
    simpa only [hleft] using (Φ.symm.mdifferentiableAt (by simp) htarget).continuousAt.tendsto
  have hinnerInv : ∀ᶠ y in 𝓝 (Φ x), ∀ v w : TangentSpace J y,
      h.inner y v w = g.inner (Φ.symm y) (mfderiv J I Φ.symm y v) (mfderiv J I Φ.symm y w) := by
    filter_upwards [hinv.eventually hinner, Φ.open_target.mem_nhds htarget] with y hy hyt
    intro v w
    have hright : Φ (Φ.symm y) = y := Φ.right_inv' hyt
    have heq : (Φ : M → N) ∘ (Φ.symm : N → M) =ᶠ[𝓝 y] id := by
      filter_upwards [Φ.open_target.mem_nhds hyt] with z hz
      exact Φ.right_inv' hz
    have hd (v : TangentSpace J y) :
        (mfderiv I J Φ (Φ.symm y) : E →L[ℝ] F) (mfderiv J I Φ.symm y v) = v := by
      have hc := mfderiv_comp_apply y (Φ.mdifferentiableAt (by simp) (Φ.symm.map_source' hyt))
        (Φ.symm.mdifferentiableAt (by simp) hyt) v
      rw [heq.mfderiv_eq, mfderiv_id] at hc
      exact hc.symm
    have hh := hy (mfderiv J I Φ.symm y v) (mfderiv J I Φ.symm y w)
    rw [hd v, hd w] at hh
    exact (congrArg (fun z : N => h.inner z v w) hright).symm.trans hh.symm
  have hf' : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f (Φ.symm (Φ x)) := by
    simpa only [hleft] using hf
  have hh := laplacian_eq_of_partialDiffeomorph_inner h g Φ.symm (x := Φ x) htarget hinnerInv (f := f) hf'
  simpa only [hleft] using hh

end DifferentialGeometry.Geometry.Operator
