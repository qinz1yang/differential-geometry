import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA4
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Canonical
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Gradient
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Laplacian
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough

/-!
# The gradient gauge of the potential along a surface flow: first wrappers

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (potential gauge, design D18 (iv)).

* `lieDerivMetric_gradFun_eq_two_hessFun`: `L_{∇f} g = 2 ∇²f` (a public form of the identity used in
  `RF/Soliton/Canonical.lean`, through `cartan_formula_for_lie_deriv_metric`).
* `surfaceFlow_gradient_field_contMDiffOn`: for a potential family `f` jointly smooth on
  `(0, T) × M`, the field `(t, y) ↦ ∇_{g(t)} f(t)(y)` is jointly smooth as a map into the tangent
  bundle (`gradient_joint_contMDiffOn`).
* `surfaceFlow_exists_gradient_flow_window`: for `0 < t₀ < t₁ < T` the flow `Φ` of this field with
  `Φ t₀ = id` exists, consists of diffeomorphisms on `(t₀, t₁)`, has velocity `∇_{g(t)} f(t)` and is
  jointly smooth on a neighbourhood of `[t₀, t₁]`
  (`forward_flow_existence_smooth_neighborhood_of_jointsmooth_field` after a time shift).
* `tracelessHessAt g f x = ∇²f − ½ (Δf) g` at `x`.
* `surfaceFlow_pullback_normalized_hasDerivAt`: if `Δ_{g(t)} f(t) = R − 1 / (T* − t)` and `ψ` is a
  jointly smooth family of diffeomorphisms on `(t₀, t₁)` with velocity `∇_{g(t)} f(t)`, then
  `∂ₜ [ψₜ* g(t) / (2 (T* − t))] = ψₜ* M / (T* − t)` with `M` the traceless Hessian. The chain rule
  of `evalForm_joint` / `deTurck_evalForm_chain_hasDerivWithinAt` combines `∂ₜ g = −R g` with
  `flow_slot_deriv` for the field `−∇f` and `L_{∇f} g = 2 ∇²f`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck (lieDerivMetric lieDerivMetric_smul_vectorField)
open DifferentialGeometry.PDE.RicciFlow.Pullback
  (cartan_formula_for_lie_deriv_metric deTurck_evalForm_chain_hasDerivWithinAt)
open DifferentialGeometry.Tensor0SBundle
open Bundle Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]
  {T : ℝ} {hT : 0 < T}

omit [CompactSpace M] in
theorem lieDerivMetric_gradFun_eq_two_hessFun
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (x : M) (v w : TangentSpace I x) :
    lieDerivMetric (I := I) g
        (⟨fun y => gradFun (I := I) g f y,
          gradFun_contMDiff_total_section (I := I) g f.contMDiff⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x v w =
      2 * hessFun (I := I) g f x v w := by
  let W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y => gradFun (I := I) g f y, gradFun_contMDiff_total_section (I := I) g f.contMDiff⟩
  change lieDerivMetric (I := I) g W x v w = _
  rw [cartan_formula_for_lie_deriv_metric]
  change g.inner x
      ((LeviCivita (I := I) g) (fun y => gradFun (I := I) g f y) x v) w +
    g.inner x v
      ((LeviCivita (I := I) g) (fun y => gradFun (I := I) g f y) x w) = _
  rw [← hessFun_eq_cov_grad (I := I) g f.contMDiff x v w, g.symm x v,
    ← hessFun_eq_cov_grad (I := I) g f.contMDiff x w v,
    hessFun_symm_of_boundaryless (I := I) g f.contMDiff x w v]
  ring

omit [I.Boundaryless] [CompactSpace M] in
theorem surfaceFlow_gradient_field_contMDiffOn
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (gradFun (S.family.metric q.1) (f q.1) q.2) :
        TangentBundle I M)) (Ioo 0 T ×ˢ univ) :=
  MetricFamilySmoothOn.gradient_joint_contMDiffOn (D := RealTimeInterval.closedOpen 0 T hT)
    hS.smoothMetric (f := fun q : ℝ × M => f q.1 q.2) hf

theorem surfaceFlow_exists_gradient_flow_window
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) :
    ∃ Φ : ℝ → M → M, (∀ x, Φ t₀ x = x) ∧
      (∀ t ∈ Ioo t₀ t₁, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x, d x = Φ t x) ∧
      (∀ t ∈ Ioo t₀ t₁, ∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (gradFun (S.family.metric t) (f t) (Φ t x)))) ∧
      ∃ lo hi : ℝ, lo < t₀ ∧ t₁ < hi ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) (Ioo lo hi ×ˢ univ) := by
  have hfield := surfaceFlow_gradient_field_contMDiffOn S hS f hf
  let X : ℝ → ∀ x : M, TangentSpace I x := fun s y =>
    gradFun (S.family.metric (s + t₀)) (f (s + t₀)) y
  have hshift : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M => (q.1 + t₀, q.2)) :=
    ContMDiff.prodMk (contMDiff_fst.add contMDiff_const) contMDiff_snd
  have hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Icc 0 (t₁ - t₀) ×ˢ univ) :=
    hfield.comp hshift.contMDiffOn (fun q hq =>
      ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ _⟩)
  obtain ⟨Φ₀, hΦ₀0, hdiff, hvel, -, -, -, -, lo, hi, hlo, hhi, hsm⟩ :=
    forward_flow_existence_smooth_neighborhood_of_jointsmooth_field X (t₁ - t₀)
      (sub_pos.mpr h01) hX
  refine ⟨fun s x => Φ₀ (s - t₀) x, fun x => by simpa using hΦ₀0 x, fun t ht => ?_,
    fun t ht x => ?_, lo + t₀, hi + t₀, by linarith, by linarith, ?_⟩
  · obtain ⟨d, hd⟩ := hdiff (t - t₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨d, hd⟩
  · have hτ : t - t₀ ∈ Ioo 0 (t₁ - t₀) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hw := hvel (t - t₀) hτ x
    have hat : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ₀ s x) (t - t₀)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (t - t₀) (Φ₀ (t - t₀) x))) :=
      hw.hasMFDerivAt (Ici_mem_nhds hτ.1)
    have htrans : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s - t₀) t
        (1 : ℝ →L[ℝ] ℝ) := by
      have h := ((hasDerivAt_id t).sub_const t₀).hasFDerivAt.hasMFDerivAt
      have hone : (1 : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.toSpanSingleton ℝ 1 := by
        ext
        simp
      rw [hone]
      exact h
    have hcomp := hat.comp t htrans
    have hX' : X (t - t₀) (Φ₀ (t - t₀) x) =
        gradFun (S.family.metric t) (f t) (Φ₀ (t - t₀) x) := by
      simp only [X, sub_add_cancel]
    rw [hX'] at hcomp
    exact hcomp.congr_mfderiv (by ext; rfl)
  · have hback : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × M => (q.1 - t₀, q.2)) :=
      ContMDiff.prodMk (contMDiff_fst.sub contMDiff_const) contMDiff_snd
    exact hsm.comp hback.contMDiffOn (fun q hq =>
      ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ _⟩)

def tracelessHessAt [NeZero (Module.finrank ℝ E)] (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) : Tensor0SSpace (E := E) (H := H) (I := I) (M := M) 2 x :=
  hessTensorAt g f x - (ΔG g f x / 2) • metricTensor0S g x

omit [T2Space M] [CompactSpace M] in
theorem tracelessHessAt_vec2 [NeZero (Module.finrank ℝ E)] (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) (v w : TangentSpace I x) :
    tracelessHessAt g f x (vec2 v w) = hessFun g f x v w - ΔG g f x / 2 * g.inner x v w := by
  simp only [tracelessHessAt, sub_apply,
    smul_apply, hessTensorAt_apply, metricTensor0S_apply, smul_eq_mul]
  rfl

omit [CompactSpace M] in
theorem surfaceFlow_pullback_normalized_hasDerivAt [NeZero (Module.finrank ℝ E)]
    (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯) {Tst : ℝ} (hTT : T ≤ Tst)
    (hfeq : ∀ t ∈ Ioo 0 T, ∀ x,
      ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (Tst - t))
    {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h1 : t₁ ≤ T) (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hψ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ψ q.1 q.2) (Ioo t₀ t₁ ×ˢ univ))
    (hvel : ∀ t ∈ Ioo t₀ t₁, ∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => ψ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (gradFun (S.family.metric t) (f t) (ψ t x)))) :
    ∀ t ∈ Ioo t₀ t₁, ∀ x (v w : TangentSpace I x),
      HasDerivAt (fun s => 1 / (2 * (Tst - s)) *
          (Diffeomorph.pullbackMetric (S.family.metric s) (ψ s)).inner x v w)
        (1 / (Tst - t) * tracelessHessAt (S.family.metric t) (f t) (ψ t x)
          (vec2 (mfderiv I I (ψ t) x v) (mfderiv I I (ψ t) x w))) t := by
  intro t ht x v w
  obtain ⟨u, rfl⟩ : ∃ u, t = u + t₀ := ⟨t - t₀, by ring⟩
  set T' := t₁ - t₀ with hT'
  let g' : ℝ → SmoothRiemannianMetric I M := fun r => S.family.metric (r + t₀)
  let Φ' : ℝ → (M ≃ₘ⟮I, I⟯ M) := fun r => ψ (r + t₀)
  have hshift : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M => (q.1 + t₀, q.2)) :=
    ContMDiff.prodMk (contMDiff_fst.add contMDiff_const) contMDiff_snd
  have hjoint' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ' q.1 q.2)
      (Ioo 0 T' ×ˢ univ) :=
    hψ.comp hshift.contMDiffOn (fun q hq =>
      ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ _⟩)
  have hmetric := MetricFamilySmoothOn.metricCLMSection_contMDiffOn
    (D := RealTimeInterval.closedOpen 0 T hT) hS.smoothMetric (J := Ioo 0 T) subset_rfl
  have hmetric' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g' p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ioo 0 T' ×ˢ univ) :=
    hmetric.comp hshift.contMDiffOn (fun q hq =>
      ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ _⟩)
  have hgram' := fun (x₀ : M) (i j : Fin (Module.finrank ℝ E)) =>
    chartGramMatrix_joint_contMDiffOn g' (Ioo 0 T') hmetric' x₀ i j
  have hu : u ∈ Ioo 0 T' := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let grad' : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := fun r =>
    ⟨fun y => gradFun (I := I) (g' r) (f (r + t₀)) y,
      gradFun_contMDiff_total_section (I := I) (g' r) (f (r + t₀)).contMDiff⟩
  let X' : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := fun r => (-1 : ℝ) • grad' r
  have hode' : ∀ y : M, ∀ r ∈ Ioo (0 : ℝ) T',
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ' s : M → M) y) (Ici (0 : ℝ)) r
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-(X' r ((Φ' r : M → M) y)))) := by
    intro y r hr
    have hrt : r + t₀ ∈ Ioo t₀ t₁ := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have h := hvel (r + t₀) hrt y
    have htrans : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + t₀) r (1 : ℝ →L[ℝ] ℝ) := by
      have h' := ((hasDerivAt_id r).add_const t₀).hasFDerivAt.hasMFDerivAt
      have hone : (1 : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.toSpanSingleton ℝ 1 := by
        ext
        simp
      rw [hone]
      exact h'
    have hcomp := (h.comp r htrans).hasMFDerivWithinAt (s := Ici (0 : ℝ))
    have hX : -(X' r ((Φ' r : M → M) y)) =
        gradFun (S.family.metric (r + t₀)) (f (r + t₀)) (ψ (r + t₀) y) := by
      simp only [X', neg_smul, one_smul, ContMDiffSection.coe_neg, Pi.neg_apply, neg_neg]
      rfl
    rw [hX]
    exact hcomp.congr_mfderiv (by ext; rfl)
  have hpush := flow_slot_deriv (g' u) X' T' Φ' hode' hjoint' u hu x v w
  have hlie : lieDerivMetric (I := I) (g' u) (X' u) ((Φ' u : M → M) x)
      (mfderiv I I (Φ' u : M → M) x v) (mfderiv I I (Φ' u : M → M) x w) =
      -(2 * hessFun (I := I) (g' u) (f (u + t₀)) ((Φ' u : M → M) x)
        (mfderiv I I (Φ' u : M → M) x v) (mfderiv I I (Φ' u : M → M) x w)) := by
    simp only [X']
    rw [lieDerivMetric_smul_vectorField, lieDerivMetric_gradFun_eq_two_hessFun]
    ring
  rw [hlie, neg_neg] at hpush
  have hreg : u + t₀ ∈ (RealTimeInterval.closedOpen 0 T hT).regular :=
    (⟨by linarith [hu.1], by linarith [hu.2]⟩ : u + t₀ ∈ Ioo 0 T)
  have hmd := metricDerivAt S hS ⟨u + t₀, hreg⟩ ((Φ' u : M → M) x)
    (mfderiv I I (Φ' u : M → M) x v) (mfderiv I I (Φ' u : M → M) x w)
  have hmetricd : HasDerivWithinAt (fun s : ℝ => (g' s).inner ((Φ' u : M → M) x)
      (mfderiv I I (Φ' u : M → M) x v) (mfderiv I I (Φ' u : M → M) x w))
      ((-2 : ℝ) * S.ricciAt (u + t₀) ((Φ' u : M → M) x)
        (vec2 (mfderiv I I (Φ' u : M → M) x v) (mfderiv I I (Φ' u : M → M) x w)))
      (Ici (0 : ℝ)) u :=
    (hmd.comp_add_const u t₀).hasDerivWithinAt
  obtain ⟨Q', hQ'⟩ := evalForm_joint g' T' Φ' hjoint' hgram' u hu x v w
  have htot := deTurck_evalForm_chain_hasDerivWithinAt g' Φ' u hu.1.le x v w _ _ hmetricd
    hpush hQ'
  have key : ∀ (F : ℝ → ℝ) (d : ℝ), HasDerivAt (fun s => F (s + t₀)) d u →
      HasDerivAt F d (u + t₀) := by
    intro F d h
    have h' : HasDerivAt (fun s => F (s + t₀)) d (u + t₀ - t₀) := by
      rwa [add_sub_cancel_right]
    simpa only [sub_add_cancel] using h'.comp_sub_const (u + t₀) t₀
  have hat := key (fun s => (S.family.metric s).inner ((ψ s : M → M) x)
    (mfderiv I I (ψ s : M → M) x v) (mfderiv I I (ψ s : M → M) x w)) _
    (htot.hasDerivAt (Ici_mem_nhds hu.1))
  have hgap : 0 < Tst - (u + t₀) := by linarith [ht.2]
  have hlam : HasDerivAt (fun s : ℝ => 1 / (2 * (Tst - s)))
      (2 / (2 * (Tst - (u + t₀))) ^ 2) (u + t₀) := by
    have hd : HasDerivAt (fun s : ℝ => 2 * (Tst - s)) (-2) (u + t₀) := by
      simpa using ((hasDerivAt_id (u + t₀)).const_sub Tst).const_mul 2
    have h := hd.inv (by positivity)
    simp only [one_div]
    convert h using 1
    ring
  have hprod := hlam.mul hat
  have hric : S.ricciAt (u + t₀) ((Φ' u : M → M) x)
      (vec2 (mfderiv I I (Φ' u : M → M) x v) (mfderiv I I (Φ' u : M → M) x w)) =
      S.scalar (u + t₀) ((Φ' u : M → M) x) / 2 * (S.family.metric (u + t₀)).inner
        ((Φ' u : M → M) x) (mfderiv I I (Φ' u : M → M) x v)
        (mfderiv I I (Φ' u : M → M) x w) := by
    simp only [SolutionOn.ricciAt, SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor,
      SolutionOn.family_metric]
    exact ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two _ hdim _ _ _
  rw [hric] at hprod
  have hΔ := hfeq (u + t₀) ⟨h0.trans ht.1, ht.2.trans_le h1⟩ ((ψ (u + t₀) : M → M) x)
  simp only [Diffeomorph.pullbackMetric_inner]
  convert hprod using 1
  rw [tracelessHessAt_vec2, hΔ]
  simp only [g', Φ']
  field_simp
  ring

end GC.Geometry
