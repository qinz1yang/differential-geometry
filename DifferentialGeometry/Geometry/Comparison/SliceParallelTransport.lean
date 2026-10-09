import DifferentialGeometry.Geometry.Comparison.ConvexTangentParallel
import DifferentialGeometry.Geometry.Comparison.Hessian.AlongGeodesic

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]



omit [T2Space (TangentBundle I M)] in
theorem eventually_intrinsicGeodesic_mem_maxSliceLocus
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {x : M} (hx : x ∈ maxSliceLocus I C) {v : TangentSpace I x}
    (hv : v ∈ sliceTangent I (maxSliceLocus I C) x) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm x v s ∈ maxSliceLocus I C := by
  obtain ⟨O, hOopen, hOeq⟩ := exists_isOpen_inter_eq_maxSliceLocus (I := I) hEnorm hC
  have hOsub : O ∩ C ⊆ maxSliceLocus I C := by
    intro z hz
    rw [← hOeq]
    exact ⟨hz.2, hz.1⟩
  have hxO : x ∈ O := by
    rw [← hOeq] at hx
    exact hx.2
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x v with hγdef
  have hγcont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm x v
  have hγ0 : γ 0 = x := intrinsicGeodesic_zero (I := I) g hEnorm x v
  have hpre : γ ⁻¹' O ∈ 𝓝 (0 : ℝ) := by
    refine hγcont.continuousAt.preimage_mem_nhds ?_
    rw [hγ0]
    exact hOopen.mem_nhds hxO
  obtain ⟨R, hRpos, hRsub⟩ := Metric.mem_nhds_iff.mp hpre
  set T : ℝ := R / 2 with hTdef
  have hTpos : 0 < T := by rw [hTdef]; linarith
  have hTmem : ∀ s ∈ Icc (-T) T, γ s ∈ O := by
    intro s hs
    refine hRsub ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> [linarith [hs.1]; linarith [hs.2]]
  have hstay : ∀ s ∈ Icc (0 : ℝ) T, γ s ∈ O := fun s hs =>
    hTmem s ⟨by linarith [hs.1, hTpos], hs.2⟩
  have hfwd := mem_maxSliceLocus_of_mem_sliceTangent hEnorm hC hCclosed hx hv hOsub
    hTpos.le hstay
  have hvneg : -v ∈ sliceTangent I (maxSliceLocus I C) x :=
    (sliceTangent I (maxSliceLocus I C) x).neg_mem hv
  have hstayneg : ∀ s ∈ Icc (0 : ℝ) T,
      intrinsicGeodesic (I := I) g hEnorm x (-v) s ∈ O := by
    intro s hs
    rw [intrinsicGeodesic_neg]
    exact hTmem (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hbwd := mem_maxSliceLocus_of_mem_sliceTangent hEnorm hC hCclosed hx hvneg hOsub
    hTpos.le hstayneg
  filter_upwards [Icc_mem_nhds (by linarith : -T < (0 : ℝ)) hTpos] with s hs
  rcases le_or_gt 0 s with hs0 | hs0
  · exact hfwd s ⟨hs0, hs.2⟩
  · have hmem := hbwd (-s) ⟨by linarith, by linarith [hs.1]⟩
    rwa [intrinsicGeodesic_neg, neg_neg] at hmem



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem hessFun_transfer
    {g : SmoothRiemannianMetric I M} {F : M → ℝ} {γ : ℝ → M} {t : ℝ} {x : M}
    {a : TangentSpace I x} (hx : γ t = x)
    (ha : (curveVelocity (I := I) γ t : E) = (a : E))
    (h : hessFun (I := I) g F (γ t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t) = 0) :
    hessFun (I := I) g F x a a = 0 := by
  subst hx
  have ha' : (curveVelocity (I := I) γ t : TangentSpace I (γ t)) = a := ha
  rw [← ha']
  exact h

omit [T2Space (TangentBundle I M)] in
theorem hessFun_apply_self_eq_zero_of_mem_sliceTangent
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {F : M → ℝ} (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F)
    {x : M} (hx : x ∈ maxSliceLocus I C)
    (hconst : ∀ᶠ z in 𝓝 x, z ∈ maxSliceLocus I C → F z = F x)
    {a : TangentSpace I x} (ha : a ∈ sliceTangent I (maxSliceLocus I C) x) :
    hessFun (I := I) g F x a a = 0 := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x a with hγdef
  have hγsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm x a
  have hγ0 : γ 0 = x := intrinsicGeodesic_zero (I := I) g hEnorm x a
  have hgeo : IsGeodesic (I := I) g γ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm x a
  have hmem := eventually_intrinsicGeodesic_mem_maxSliceLocus hEnorm hC hCclosed hx ha
  have htend : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := by
    rw [← hγ0]
    exact hγsm.continuous.continuousAt
  have hpull : ∀ᶠ s in 𝓝 (0 : ℝ), γ s ∈ maxSliceLocus I C → F (γ s) = F x :=
    htend.eventually hconst
  have heq : (F ∘ γ) =ᶠ[𝓝 (0 : ℝ)] fun _ : ℝ => F x := by
    filter_upwards [hmem, hpull] with s h1 h2 using h2 h1
  have hderiv2 : (deriv^[2] (F ∘ γ)) 0 = 0 := by
    have h2 : deriv (F ∘ γ) =ᶠ[𝓝 (0 : ℝ)] deriv (fun _ : ℝ => F x) := heq.deriv
    have h3 : deriv (deriv (F ∘ γ)) 0 = deriv (deriv (fun _ : ℝ => F x)) 0 :=
      Filter.EventuallyEq.deriv_eq h2
    have h4 : deriv (deriv (fun _ : ℝ => F x)) 0 = 0 := by simp
    rw [show (deriv^[2] (F ∘ γ)) 0 = deriv (deriv (F ∘ γ)) 0 from rfl, h3, h4]
  have hHess := deriv2_comp_geo_at (I := I) g hF hγsm (hgeo 0)
  rw [hderiv2] at hHess
  have hvel : (curveVelocity (I := I) γ 0 : E) = (a : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x a
  exact hessFun_transfer hγ0 hvel hHess.symm

omit [T2Space (TangentBundle I M)] in
theorem hessFun_apply_eq_zero_of_mem_sliceTangent
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {F : M → ℝ} (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F)
    {x : M} (hx : x ∈ maxSliceLocus I C)
    (hconst : ∀ᶠ z in 𝓝 x, z ∈ maxSliceLocus I C → F z = F x)
    {a b : TangentSpace I x} (ha : a ∈ sliceTangent I (maxSliceLocus I C) x)
    (hb : b ∈ sliceTangent I (maxSliceLocus I C) x) :
    hessFun (I := I) g F x a b = 0 := by
  have hsymm := hessFun_symm_of_boundaryless (I := I) g hF x a b
  have hzero : ∀ c : TangentSpace I x, c ∈ sliceTangent I (maxSliceLocus I C) x →
      hessFun (I := I) g F x c c = 0 := fun c hc =>
    hessFun_apply_self_eq_zero_of_mem_sliceTangent hEnorm hC hCclosed hF hx hconst hc
  have hab : a + b ∈ sliceTangent I (maxSliceLocus I C) x :=
    (sliceTangent I (maxSliceLocus I C) x).add_mem ha hb
  have hout : ∀ c : TangentSpace I x, hessFun (I := I) g F x (a + b) c
      = hessFun (I := I) g F x a c + hessFun (I := I) g F x b c := by
    intro c
    rw [LinearMap.map_add (hessFun (I := I) g F x) a b]
    rfl
  have hin : hessFun (I := I) g F x (a + b) (a + b)
      = hessFun (I := I) g F x (a + b) a + hessFun (I := I) g F x (a + b) b :=
    LinearMap.map_add _ a b
  have key : (0 : ℝ) = hessFun (I := I) g F x a a + hessFun (I := I) g F x b a
      + (hessFun (I := I) g F x a b + hessFun (I := I) g F x b b) := by
    rw [← hzero _ hab, hin, hout a, hout b]
  rw [hzero _ ha, hzero _ hb, ← hsymm] at key
  linarith



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem chartRep_sec_diff
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (X : ∀ x : M, TangentSpace I x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) (t : ℝ) :
    DifferentiableAt ℝ (chartRepAt (I := I) γ (fun s => X (γ s)) t) t := by
  let α : M := γ t
  have hbase : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hrepr : ContMDiffAt I 𝓘(ℝ, E) ∞ (chartESectionRepr (I := I) α X) α :=
    (contMDiffAt_section_iff_chartE I α X hbase).mp hX.contMDiffAt
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((chartESectionRepr (I := I) α X) ∘ γ) t :=
    hrepr.comp t hγ.contMDiffAt
  change DifferentiableAt ℝ ((chartESectionRepr (I := I) α X) ∘ γ) t
  exact (contMDiffAt_iff_contDiffAt.mp hcomp).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem hasDerivAt_inner_gradFun
    (g : SmoothRiemannianMetric I M) {F : M → ℝ} (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (V : ∀ t : ℝ, TangentSpace I (γ t)) {t : ℝ}
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    HasDerivAt (fun s : ℝ => g.inner (γ s) (gradFun (I := I) g F (γ s)) (V s))
      (hessFun (I := I) g F (γ t) (curveVelocity (I := I) γ t) (V t)
        + g.inner (γ t) (gradFun (I := I) g F (γ t))
          (covDerivAlong (I := I) g γ V t)) t := by
  have hgrad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% fun x => gradFun (I := I) g F x) :=
    gradFun_contMDiff_total_section (I := I) g hF
  have hGdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => gradFun (I := I) g F (γ s)) t) t :=
    chartRep_sec_diff (I := I) hγ (fun x => gradFun (I := I) g F x) hgrad t
  have hinner := metric_compat_hasDerivAt_inner (I := I) (n := ∞) (by simp) g γ
    (fun s => gradFun (I := I) g F (γ s)) V t hγ hGdiff hV
  have hGcov : covDerivAlong (I := I) g γ (fun s => gradFun (I := I) g F (γ s)) t =
      (LeviCivita (I := I) g) (fun x => gradFun (I := I) g F x) (γ t)
        (curveVelocity (I := I) γ t) :=
    covDerivAlong_restrict_eq_leviCivita (I := I) g γ
      (fun x => gradFun (I := I) g F x) t hγ
      (hgrad.contMDiffAt.mdifferentiableAt (by simp))
  have hfirst : g.inner (γ t)
      (covDerivAlong (I := I) g γ (fun s => gradFun (I := I) g F (γ s)) t) (V t)
      = hessFun (I := I) g F (γ t) (curveVelocity (I := I) γ t) (V t) := by
    rw [hGcov]
    exact (hessFun_eq_cov_grad (I := I) g hF (γ t) (curveVelocity (I := I) γ t) (V t)).symm
  rw [hfirst] at hinner
  exact hinner

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem hasDerivAt_inner_gradFun_of_parallel
    (g : SmoothRiemannianMetric I M) {F : M → ℝ} (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (V : ∀ t : ℝ, TangentSpace I (γ t)) {t : ℝ}
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hpar : covDerivAlong (I := I) g γ V t = 0) :
    HasDerivAt (fun s : ℝ => g.inner (γ s) (gradFun (I := I) g F (γ s)) (V s))
      (hessFun (I := I) g F (γ t) (curveVelocity (I := I) γ t) (V t)) t := by
  have h := hasDerivAt_inner_gradFun (I := I) g hF hγ V hV
  rw [hpar] at h
  simpa using h



theorem eq_zero_of_norm_deriv_le_mul_norm {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {y y' : ℝ → F} {a b K t₁ : ℝ}
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (y' t) t)
    (hbound : ∀ t ∈ Icc a b, ‖y' t‖ ≤ K * ‖y t‖)
    (ht₁ : t₁ ∈ Icc a b) (h0 : y t₁ = 0) :
    ∀ t ∈ Icc a b, y t = 0 := by
  have hcont : ContinuousOn y (Icc a b) := fun t ht => ((hy t ht).continuousAt).continuousWithinAt
  have hforward : ∀ t ∈ Icc t₁ b, y t = 0 := by
    refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := K) (f' := y')
      (hcont.mono (Icc_subset_Icc_left ht₁.1)) (fun t ht => ?_) h0 (fun t ht => ?_)
    · exact (hy t ⟨le_trans ht₁.1 ht.1, ht.2.le⟩).hasDerivWithinAt
    · exact hbound t ⟨le_trans ht₁.1 ht.1, ht.2.le⟩
  have hbackward : ∀ t ∈ Icc a t₁, y t = 0 := by
    set z : ℝ → F := fun s => y (t₁ - s) with hzdef
    set z' : ℝ → F := fun s => -y' (t₁ - s) with hz'def
    have hzderiv : ∀ s ∈ Icc (0 : ℝ) (t₁ - a), HasDerivAt z (z' s) s := by
      intro s hs
      have hmem : t₁ - s ∈ Icc a b :=
        ⟨by linarith [hs.2], by linarith [hs.1, ht₁.2]⟩
      have hline : HasDerivAt (fun r : ℝ => t₁ - r) (-1 : ℝ) s := by
        simpa using (hasDerivAt_id s).const_sub t₁
      have := HasDerivAt.scomp s (hy (t₁ - s) hmem) hline
      simpa [hzdef, hz'def, Function.comp_def] using this
    have hzcont : ContinuousOn z (Icc (0 : ℝ) (t₁ - a)) := fun s hs =>
      ((hzderiv s hs).continuousAt).continuousWithinAt
    have hzbound : ∀ s ∈ Ico (0 : ℝ) (t₁ - a), ‖z' s‖ ≤ K * ‖z s‖ := by
      intro s hs
      have hmem : t₁ - s ∈ Icc a b :=
        ⟨by linarith [hs.2], by linarith [hs.1, ht₁.2]⟩
      simpa [hzdef, hz'def] using hbound (t₁ - s) hmem
    have hz0 : z 0 = 0 := by simpa [hzdef] using h0
    have hzzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := K) (f' := z')
      hzcont (fun s hs => (hzderiv s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) hz0 hzbound
    intro t ht
    have hs : t₁ - t ∈ Icc (0 : ℝ) (t₁ - a) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have := hzzero (t₁ - t) hs
    simpa [hzdef] using this
  intro t ht
  rcases le_or_gt t t₁ with hle | hlt
  · exact hbackward t ⟨ht.1, hle⟩
  · exact hforward t ⟨hlt.le, ht.2⟩



structure IsSliceDefiningFamilyOn (g : SmoothRiemannianMetric I M) (C : Set M)
    {m : ℕ} (F : Fin m → M → ℝ) (W : Set M) : Prop where

  isOpen : IsOpen W

  contMDiff : ∀ i : Fin m, ContMDiff I 𝓘(ℝ, ℝ) ∞ (F i)


  locallyConstant : ∀ z ∈ W, z ∈ maxSliceLocus I C → ∀ i : Fin m,
    ∀ᶠ z' in 𝓝 z, z' ∈ maxSliceLocus I C → F i z' = F i z

  mem_iff : ∀ z ∈ W, z ∈ maxSliceLocus I C → ∀ v : TangentSpace I z,
    (v ∈ sliceTangent I (maxSliceLocus I C) z ↔
      ∀ i : Fin m, g.inner z (gradFun (I := I) g (F i) z) v = 0)

  indep : ∀ z ∈ W, z ∈ maxSliceLocus I C → ∀ c : Fin m → ℝ,
    (∑ i : Fin m, c i • gradFun (I := I) g (F i) z) = 0 → c = 0

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
def sliceGram (g : SmoothRiemannianMetric I M) {m : ℕ} (F : Fin m → M → ℝ) (z : M) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => g.inner z (gradFun (I := I) g (F i) z) (gradFun (I := I) g (F j) z)

def HasSliceDefiningFamilies (g : SmoothRiemannianMetric I M) (C : Set M) : Prop :=
  ∀ x ∈ maxSliceLocus I C, ∃ (m : ℕ) (F : Fin m → M → ℝ) (W : Set M),
    x ∈ W ∧ IsSliceDefiningFamilyOn (I := I) g C F W



omit [T2Space (TangentBundle I M)] in
private theorem forall_mem_sliceTangent_of_gram_bound
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {m : ℕ} {F : Fin m → M → ℝ} {W : Set M}
    (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {τ : ℝ → M} (hτsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ τ)
    {ξ : ∀ t : ℝ, TangentSpace I (τ t)} {a b : ℝ}
    (hξdiff : ∀ t ∈ Icc a b, DifferentiableAt ℝ (chartRepAt (I := I) τ ξ t) t)
    (hξpar : ∀ t ∈ Icc a b, covDerivAlong (I := I) g τ ξ t = 0)
    (hτN : ∀ t ∈ Icc a b, τ t ∈ maxSliceLocus I C)
    (hτW : ∀ t ∈ Icc a b, τ t ∈ W)
    (hvel : ∀ t ∈ Icc a b,
      curveVelocity (I := I) τ t ∈ sliceTangent I (maxSliceLocus I C) (τ t))
    {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hgram : ∀ t ∈ Icc a b, ∀ c : Fin m → ℝ,
      δ * ‖c‖ ≤ ‖(sliceGram (I := I) g F (τ t)).mulVec c‖)
    (hbnd : ∀ t ∈ Icc a b, ∀ i j : Fin m,
      |hessFun (I := I) g (F i) (τ t) (curveVelocity (I := I) τ t)
        (gradFun (I := I) g (F j) (τ t))| ≤ B)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (h0 : ξ t₀ ∈ sliceTangent I (maxSliceLocus I C) (τ t₀)) :
    ∀ t ∈ Icc a b, ξ t ∈ sliceTangent I (maxSliceLocus I C) (τ t) := by
  classical
  set y : ℝ → (Fin m → ℝ) := fun t i =>
    g.inner (τ t) (gradFun (I := I) g (F i) (τ t)) (ξ t) with hydef
  set y' : ℝ → (Fin m → ℝ) := fun t i =>
    hessFun (I := I) g (F i) (τ t) (curveVelocity (I := I) τ t) (ξ t) with hy'def
  have hmem : ∀ t ∈ Icc a b,
      (ξ t ∈ sliceTangent I (maxSliceLocus I C) (τ t) ↔ y t = 0) := by
    intro t ht
    rw [hfam.mem_iff (τ t) (hτW t ht) (hτN t ht) (ξ t)]
    constructor
    · intro h; funext i; exact h i
    · intro h i; exact congrFun h i
  have hderiv : ∀ t ∈ Icc a b, HasDerivAt y (y' t) t := by
    intro t ht
    refine hasDerivAt_pi.2 fun i => ?_
    exact hasDerivAt_inner_gradFun_of_parallel (I := I) g (hfam.contMDiff i) hτsm ξ
      (hξdiff t ht) (hξpar t ht)
  have hbound : ∀ t ∈ Icc a b, ‖y' t‖ ≤ (m * B / δ) * ‖y t‖ := by
    intro t ht
    set Gm : Matrix (Fin m) (Fin m) ℝ := sliceGram (I := I) g F (τ t) with hGmdef
    have hGinj : Function.Injective (Matrix.toLin' Gm) := by
      rw [← LinearMap.ker_eq_bot]
      refine (Submodule.eq_bot_iff _).2 fun c hc => ?_
      have hc0 : Gm.mulVec c = 0 := by simpa [Matrix.toLin'_apply] using hc
      have := hgram t ht c
      rw [← hGmdef, hc0, norm_zero] at this
      have hcn : ‖c‖ ≤ 0 := by nlinarith [norm_nonneg c]
      exact norm_le_zero_iff.1 hcn
    have hGsurj : Function.Surjective (Matrix.toLin' Gm) :=
      LinearMap.injective_iff_surjective.1 hGinj
    obtain ⟨c, hc⟩ := hGsurj (y t)
    have hcmul : Gm.mulVec c = y t := by simpa [Matrix.toLin'_apply] using hc
    have hcnorm : ‖c‖ ≤ ‖y t‖ / δ := by
      have h1 := hgram t ht c
      rw [← hGmdef, hcmul] at h1
      rw [le_div_iff₀ hδ]
      linarith [h1]
    set Wv : TangentSpace I (τ t) :=
      ∑ j : Fin m, c j • gradFun (I := I) g (F j) (τ t) with hWvdef
    have hinnerWv : ∀ i : Fin m,
        g.inner (τ t) (gradFun (I := I) g (F i) (τ t)) Wv = y t i := by
      intro i
      rw [hWvdef, map_sum]
      have : ∀ j : Fin m,
          g.inner (τ t) (gradFun (I := I) g (F i) (τ t))
              (c j • gradFun (I := I) g (F j) (τ t))
            = Gm i j * c j := by
        intro j
        rw [ContinuousLinearMap.map_smul, smul_eq_mul, hGmdef, sliceGram]
        ring
      rw [Finset.sum_congr rfl fun j _ => this j]
      rw [← hcmul, Matrix.mulVec, dotProduct]
    have hrest : ξ t - Wv ∈ sliceTangent I (maxSliceLocus I C) (τ t) := by
      rw [hfam.mem_iff (τ t) (hτW t ht) (hτN t ht)]
      intro i
      rw [ContinuousLinearMap.map_sub, hinnerWv i, hydef]
      simp
    have hzero : ∀ i : Fin m,
        hessFun (I := I) g (F i) (τ t) (curveVelocity (I := I) τ t) (ξ t - Wv) = 0 := by
      intro i
      exact hessFun_apply_eq_zero_of_mem_sliceTangent hEnorm hC hCclosed
        (hfam.contMDiff i) (hτN t ht) (hfam.locallyConstant (τ t) (hτW t ht) (hτN t ht) i)
        (hvel t ht) hrest
    have hcomp : ∀ i : Fin m, y' t i
        = ∑ j : Fin m, c j *
          hessFun (I := I) g (F i) (τ t) (curveVelocity (I := I) τ t)
            (gradFun (I := I) g (F j) (τ t)) := by
      intro i
      have hsplit : ξ t = Wv + (ξ t - Wv) := by abel
      rw [hy'def]
      simp only
      rw [hsplit, LinearMap.map_add]
      rw [hzero i, add_zero, hWvdef, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [LinearMap.map_smul, smul_eq_mul]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    have hstep : ∀ j : Fin m,
        |c j * hessFun (I := I) g (F i) (τ t) (curveVelocity (I := I) τ t)
            (gradFun (I := I) g (F j) (τ t))| ≤ ‖c‖ * B := by
      intro j
      have hcj : |c j| ≤ ‖c‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm c j
      rw [abs_mul]
      exact mul_le_mul hcj (hbnd t ht i j) (abs_nonneg _) (norm_nonneg c)
    have hi : ‖y' t i‖ ≤ (m : ℝ) * (‖c‖ * B) := by
      rw [hcomp i, Real.norm_eq_abs]
      calc |∑ j : Fin m, c j * hessFun (I := I) g (F i) (τ t)
              (curveVelocity (I := I) τ t) (gradFun (I := I) g (F j) (τ t))|
          ≤ ∑ j : Fin m, |c j * hessFun (I := I) g (F i) (τ t)
              (curveVelocity (I := I) τ t) (gradFun (I := I) g (F j) (τ t))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin m, ‖c‖ * B := Finset.sum_le_sum fun j _ => hstep j
        _ = (m : ℝ) * (‖c‖ * B) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ‖y' t i‖ ≤ (m : ℝ) * (‖c‖ * B) := hi
      _ ≤ (m : ℝ) * ((‖y t‖ / δ) * B) := by
          have := mul_le_mul_of_nonneg_right hcnorm hB
          exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg m)
      _ = (m * B / δ) * ‖y t‖ := by field_simp
  have hy0 : y t₀ = 0 := (hmem t₀ ht₀).1 h0
  have hall := eq_zero_of_norm_deriv_le_mul_norm (K := (m * B / δ)) hderiv hbound ht₀ hy0
  intro t ht
  exact (hmem t ht).2 (hall t ht)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem inner_sum_smul (g : SmoothRiemannianMetric I M) (x : M) {m : ℕ}
    (c : Fin m → ℝ) (v : Fin m → TangentSpace I x) (w : TangentSpace I x) :
    g.inner x w (∑ j : Fin m, c j • v j) = ∑ j : Fin m, c j * g.inner x w (v j) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem exists_gram_lower_bound
    {g : SmoothRiemannianMetric I M} {C : Set M} {m : ℕ} {F : Fin m → M → ℝ} {W : Set M}
    (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {x : M} (hxW : x ∈ W) (hxN : x ∈ maxSliceLocus I C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : Fin m → ℝ,
      δ * ‖c‖ ≤ ‖(sliceGram (I := I) g F x).mulVec c‖ := by
  classical
  set Gm : Matrix (Fin m) (Fin m) ℝ := sliceGram (I := I) g F x with hGmdef
  have hquad : ∀ c : Fin m → ℝ,
      g.inner x (∑ i : Fin m, c i • gradFun (I := I) g (F i) x)
          (∑ j : Fin m, c j • gradFun (I := I) g (F j) x)
        = ∑ i : Fin m, c i * Gm.mulVec c i := by
    intro c
    rw [g.symm x, inner_sum_smul (I := I) g x c _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [g.symm x, inner_sum_smul (I := I) g x c _ _]
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hGmdef, sliceGram]; ring
  have hinj : Function.Injective (Matrix.toLin' Gm) := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 fun c hc => ?_
    have hc0 : Gm.mulVec c = 0 := by simpa [Matrix.toLin'_apply] using hc
    have hzero : g.inner x (∑ i : Fin m, c i • gradFun (I := I) g (F i) x)
        (∑ j : Fin m, c j • gradFun (I := I) g (F j) x) = 0 := by
      rw [hquad c, hc0]
      simp
    have hV : (∑ i : Fin m, c i • gradFun (I := I) g (F i) x) = 0 := by
      by_contra hne
      exact absurd hzero (ne_of_gt (g.pos x _ hne))
    exact hfam.indep x hxW hxN c hV
  have hbij : Function.Bijective (Matrix.toLin' Gm) :=
    ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  set e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) := LinearEquiv.ofBijective _ hbij with hedef
  set ec : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) := e.toContinuousLinearEquiv with hecdef
  set K : ℝ := ‖(ec.symm : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ))‖ with hKdef
  have hK0 : 0 ≤ K := norm_nonneg _
  have hlow : ∀ c : Fin m → ℝ, ‖c‖ ≤ K * ‖Gm.mulVec c‖ := by
    intro c
    have happ : (ec : (Fin m → ℝ) → (Fin m → ℝ)) c = Gm.mulVec c := by
      simp [hecdef, hedef, Matrix.toLin'_apply]
    have h1 : (ec.symm : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) (ec c) = c :=
      ec.symm_apply_apply c
    calc ‖c‖ = ‖(ec.symm : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) (ec c)‖ := by rw [h1]
      _ ≤ K * ‖(ec : (Fin m → ℝ) → (Fin m → ℝ)) c‖ :=
        (ec.symm : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)).le_opNorm _
      _ = K * ‖Gm.mulVec c‖ := by rw [happ]
  refine ⟨1 / (K + 1), by positivity, fun c => ?_⟩
  have h2 := hlow c
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (Gm.mulVec c), norm_nonneg c]

omit [T2Space (TangentBundle I M)] in
private theorem exists_local_sliceTangent_iff
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {m : ℕ} {F : Fin m → M → ℝ} {W : Set M}
    (hfam : IsSliceDefiningFamilyOn (I := I) g C F W)
    {τ : ℝ → M} (hτsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ τ)
    {ξ : ∀ t : ℝ, TangentSpace I (τ t)} {a b : ℝ}
    (hξdiff : ∀ t ∈ Icc a b, DifferentiableAt ℝ (chartRepAt (I := I) τ ξ t) t)
    (hξpar : ∀ t ∈ Icc a b, covDerivAlong (I := I) g τ ξ t = 0)
    (hτN : ∀ t ∈ Icc a b, τ t ∈ maxSliceLocus I C)
    (hvel : ∀ t ∈ Icc a b,
      curveVelocity (I := I) τ t ∈ sliceTangent I (maxSliceLocus I C) (τ t))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hτ₀ : τ t₀ ∈ W) :
    ∃ ε > 0, ∀ t ∈ Icc a b, |t - t₀| < ε →
      (ξ t ∈ sliceTangent I (maxSliceLocus I C) (τ t) ↔
        ξ t₀ ∈ sliceTangent I (maxSliceLocus I C) (τ t₀)) := by
  classical
  set ν : Fin m → ∀ z : M, TangentSpace I z := fun i z => gradFun (I := I) g (F i) z with hνdef
  have hνsm : ∀ i : Fin m, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (ν i)) := fun i =>
    gradFun_contMDiff_total_section (I := I) g (hfam.contMDiff i)
  set S : Fin m → Fin m → ∀ z : M, TangentSpace I z := fun i j =>
    covApply (LeviCivita (I := I) g) (ν j) (ν i) with hSdef
  have hSsm : ∀ i j : Fin m, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (S i j)) := by
    intro i j
    refine contMDiffOn_univ.mp (covApply_contMDiffOn (cov := LeviCivita (I := I) g)
      (hνsm j) ?_)
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hνsm i
  set Gf : Fin m → Fin m → ℝ → ℝ := fun i j t => g.inner (τ t) (ν i (τ t)) (ν j (τ t))
    with hGfdef
  set Hf : Fin m → Fin m → ℝ → ℝ := fun i j t =>
    g.inner (τ t) (S i j (τ t)) (curveVelocity (I := I) τ t) with hHfdef
  have hGcont : ∀ i j : Fin m, ContinuousAt (Gf i j) t₀ := by
    intro i j
    exact (metric_compat_hasDerivAt_inner (I := I) (n := ∞) (by simp) g τ
      (fun s => ν i (τ s)) (fun s => ν j (τ s)) t₀ hτsm
      (chartRep_sec_diff (I := I) hτsm (ν i) (hνsm i) t₀)
      (chartRep_sec_diff (I := I) hτsm (ν j) (hνsm j) t₀)).continuousAt
  have hHcont : ∀ i j : Fin m, ContinuousAt (Hf i j) t₀ := by
    intro i j
    exact (metric_compat_hasDerivAt_inner (I := I) (n := ∞) (by simp) g τ
      (fun s => S i j (τ s)) (fun s => curveVelocity (I := I) τ s) t₀ hτsm
      (chartRep_sec_diff (I := I) hτsm (S i j) (hSsm i j) t₀)
      (velocity_chartRepAt_differentiableAt (I := I) τ hτsm t₀)).continuousAt
  have hHess : ∀ (i j : Fin m) (t : ℝ),
      hessFun (I := I) g (F i) (τ t) (curveVelocity (I := I) τ t) (ν j (τ t))
        = Hf i j t := by
    intro i j t
    rw [hessFun_symm_of_boundaryless (I := I) g (hfam.contMDiff i) (τ t)]
    exact hessFun_eq_cov_grad (I := I) g (hfam.contMDiff i) (τ t) (ν j (τ t))
      (curveVelocity (I := I) τ t)
  obtain ⟨δ₀, hδ₀, hδ₀bd⟩ := exists_gram_lower_bound hfam hτ₀ (hτN t₀ ht₀)
  set η : ℝ := δ₀ / (2 * ((m : ℝ) + 1)) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  set B : ℝ := 1 + ∑ i : Fin m, ∑ j : Fin m, |Hf i j t₀| with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, |Hf i j t₀| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith
  have hBle : ∀ i j : Fin m, |Hf i j t₀| + 1 ≤ B := by
    intro i j
    rw [hBdef]
    have hsub : |Hf i j t₀| ≤ ∑ i' : Fin m, ∑ j' : Fin m, |Hf i' j' t₀| := by
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun i' : Fin m => ∑ j' : Fin m, |Hf i' j' t₀|)
        (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j' : Fin m => |Hf i j' t₀|)
        (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  have hev1 : ∀ᶠ t in 𝓝 t₀, τ t ∈ W :=
    (hτsm.continuous.continuousAt).preimage_mem_nhds (hfam.isOpen.mem_nhds hτ₀)
  have hev2 : ∀ᶠ t in 𝓝 t₀, ∀ i j : Fin m, |Gf i j t - Gf i j t₀| < η := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hc : ContinuousAt (fun t => |Gf i j t - Gf i j t₀|) t₀ :=
      ((hGcont i j).sub continuousAt_const).abs
    have hlt : |Gf i j t₀ - Gf i j t₀| < η := by simpa using hηpos
    exact Filter.Tendsto.eventually_lt_const hlt hc
  have hev3 : ∀ᶠ t in 𝓝 t₀, ∀ i j : Fin m, |Hf i j t - Hf i j t₀| < 1 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hc : ContinuousAt (fun t => |Hf i j t - Hf i j t₀|) t₀ :=
      ((hHcont i j).sub continuousAt_const).abs
    have hlt : |Hf i j t₀ - Hf i j t₀| < 1 := by simp
    exact Filter.Tendsto.eventually_lt_const hlt hc
  obtain ⟨ε, hεpos, hεsub⟩ :=
    Metric.eventually_nhds_iff.mp (hev1.and (hev2.and hev3))
  refine ⟨ε, hεpos, fun t ht hdist => ?_⟩
  set a' : ℝ := min t t₀ with ha'def
  set b' : ℝ := max t t₀ with hb'def
  have hsub : Icc a' b' ⊆ Icc a b := by
    refine Icc_subset_Icc ?_ ?_
    · exact le_min ht.1 ht₀.1
    · exact max_le ht.2 ht₀.2
  have hnear : ∀ s ∈ Icc a' b', dist s t₀ < ε := by
    intro s hs
    rw [Real.dist_eq]
    rcases le_total t t₀ with hle | hle
    · have h1 : t ≤ s := by simpa [ha'def, min_eq_left hle] using hs.1
      have h2 : s ≤ t₀ := by simpa [hb'def, max_eq_right hle] using hs.2
      have : |t - t₀| = t₀ - t := by rw [abs_of_nonpos (by linarith)]; ring
      rw [abs_of_nonpos (by linarith)]
      rw [this] at hdist
      linarith
    · have h1 : t₀ ≤ s := by simpa [ha'def, min_eq_right hle] using hs.1
      have h2 : s ≤ t := by simpa [hb'def, max_eq_left hle] using hs.2
      have : |t - t₀| = t - t₀ := by rw [abs_of_nonneg (by linarith)]
      rw [abs_of_nonneg (by linarith)]
      rw [this] at hdist
      linarith
  have hprop : ∀ s ∈ Icc a' b',
      τ s ∈ W ∧ (∀ i j : Fin m, |Gf i j s - Gf i j t₀| < η) ∧
        (∀ i j : Fin m, |Hf i j s - Hf i j t₀| < 1) := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hεsub (hnear s hs)
    exact ⟨h1, h2, h3⟩
  have hgram : ∀ s ∈ Icc a' b', ∀ c : Fin m → ℝ,
      (δ₀ / 2) * ‖c‖ ≤ ‖(sliceGram (I := I) g F (τ s)).mulVec c‖ := by
    intro s hs c
    have hdiff : ‖(sliceGram (I := I) g F (τ s)).mulVec c
        - (sliceGram (I := I) g F (τ t₀)).mulVec c‖ ≤ (δ₀ / 2) * ‖c‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      have hentry : ∀ j : Fin m,
          |(sliceGram (I := I) g F (τ s) i j - sliceGram (I := I) g F (τ t₀) i j) * c j|
            ≤ η * ‖c‖ := by
        intro j
        rw [abs_mul]
        have h1 : |sliceGram (I := I) g F (τ s) i j
            - sliceGram (I := I) g F (τ t₀) i j| ≤ η := le_of_lt ((hprop s hs).2.1 i j)
        have h2 : |c j| ≤ ‖c‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm c j
        exact mul_le_mul h1 h2 (abs_nonneg _) hηpos.le
      have hrw : ((sliceGram (I := I) g F (τ s)).mulVec c
            - (sliceGram (I := I) g F (τ t₀)).mulVec c) i
          = ∑ j : Fin m,
            (sliceGram (I := I) g F (τ s) i j - sliceGram (I := I) g F (τ t₀) i j) * c j := by
        simp [Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, sub_mul]
      rw [Real.norm_eq_abs, hrw]
      calc |∑ j : Fin m,
            (sliceGram (I := I) g F (τ s) i j - sliceGram (I := I) g F (τ t₀) i j) * c j|
          ≤ ∑ j : Fin m,
            |(sliceGram (I := I) g F (τ s) i j - sliceGram (I := I) g F (τ t₀) i j) * c j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin m, η * ‖c‖ := Finset.sum_le_sum fun j _ => hentry j
        _ = (m : ℝ) * (η * ‖c‖) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (δ₀ / 2) * ‖c‖ := by
            have hkey : (m : ℝ) * η ≤ δ₀ / 2 := by
              rw [hηdef, mul_div_assoc',
                div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
              nlinarith [hδ₀.le, Nat.cast_nonneg (α := ℝ) m]
            calc (m : ℝ) * (η * ‖c‖) = ((m : ℝ) * η) * ‖c‖ := by ring
              _ ≤ (δ₀ / 2) * ‖c‖ := mul_le_mul_of_nonneg_right hkey (norm_nonneg c)
    have hbase := hδ₀bd c
    have htri : ‖(sliceGram (I := I) g F (τ t₀)).mulVec c‖
        - ‖(sliceGram (I := I) g F (τ s)).mulVec c‖
        ≤ ‖(sliceGram (I := I) g F (τ s)).mulVec c
          - (sliceGram (I := I) g F (τ t₀)).mulVec c‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le _ _
    linarith
  have hbnd : ∀ s ∈ Icc a' b', ∀ i j : Fin m,
      |hessFun (I := I) g (F i) (τ s) (curveVelocity (I := I) τ s)
        (gradFun (I := I) g (F j) (τ s))| ≤ B := by
    intro s hs i j
    have := (hprop s hs).2.2 i j
    have h2 : hessFun (I := I) g (F i) (τ s) (curveVelocity (I := I) τ s)
        (gradFun (I := I) g (F j) (τ s)) = Hf i j s := hHess i j s
    rw [h2]
    have h3 : |Hf i j s| ≤ |Hf i j t₀| + 1 := by
      have := abs_sub_abs_le_abs_sub (Hf i j s) (Hf i j t₀)
      linarith [(hprop s hs).2.2 i j]
    linarith [hBle i j]
  have hcore : ∀ t₂ ∈ Icc a' b', ξ t₂ ∈ sliceTangent I (maxSliceLocus I C) (τ t₂) →
      ∀ s ∈ Icc a' b', ξ s ∈ sliceTangent I (maxSliceLocus I C) (τ s) := by
    intro t₂ ht₂ hmem₂
    exact forall_mem_sliceTangent_of_gram_bound hEnorm hC hCclosed hfam hτsm
      (fun s hs => hξdiff s (hsub hs)) (fun s hs => hξpar s (hsub hs))
      (fun s hs => hτN s (hsub hs)) (fun s hs => (hprop s hs).1)
      (fun s hs => hvel s (hsub hs)) (by positivity) hB0 hgram hbnd ht₂ hmem₂
  have ht₀' : t₀ ∈ Icc a' b' := ⟨min_le_right t t₀, le_max_right t t₀⟩
  have ht' : t ∈ Icc a' b' := ⟨min_le_left t t₀, le_max_left t t₀⟩
  constructor
  · intro h; exact hcore t ht' h t₀ ht₀'
  · intro h; exact hcore t₀ ht₀' h t ht'



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem mfderiv_reflect {f : ℝ → M} {s : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I f s) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun σ : ℝ => f (s - σ)) 0 1 : E)
      = -(mfderiv 𝓘(ℝ, ℝ) I f s 1 : E) := by
  have hline : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun σ : ℝ => s - σ) 0
      (-(ContinuousLinearMap.id ℝ ℝ)) := by
    have h : HasFDerivAt (fun σ : ℝ => s - σ) (-(ContinuousLinearMap.id ℝ ℝ)) 0 := by
      simpa [sub_eq_add_neg] using (hasFDerivAt_id (0 : ℝ)).neg.const_add s
    exact h.hasMFDerivAt
  have hf0 : MDifferentiableAt 𝓘(ℝ, ℝ) I f ((fun σ : ℝ => s - σ) 0) := by
    simpa only [sub_zero] using hf
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun σ : ℝ => f (s - σ)) 0
      ((mfderiv 𝓘(ℝ, ℝ) I f ((fun σ : ℝ => s - σ) 0)).comp
        (-(ContinuousLinearMap.id ℝ ℝ))) :=
    HasMFDerivAt.comp (0 : ℝ) hf0.hasMFDerivAt hline
  have harg : ((fun σ : ℝ => s - σ) 0) = s := by norm_num
  rw [hcomp.mfderiv, harg]
  exact ContinuousLinearMap.map_neg (mfderiv 𝓘(ℝ, ℝ) I f s) (1 : ℝ)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem curveVelocity_mem_sliceTangent_Icc {S : Set M} {c : ℝ → M} {a b t : ℝ}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) (hab : a < b) (ht : t ∈ Icc a b)
    (hmem : ∀ s ∈ Icc a b, c s ∈ S) :
    curveVelocity (I := I) c t ∈ sliceTangent I S (c t) := by
  have hcd : MDifferentiableAt 𝓘(ℝ, ℝ) I c t :=
    hc.contMDiffAt.mdifferentiableAt (by simp)
  rcases lt_or_ge t b with hlt | hge
  · have hev : ∀ᶠ σ in 𝓝[>] (0 : ℝ), c (t + σ) ∈ S := by
      filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hlt)] with σ hσ
      exact hmem (t + σ) ⟨by linarith [hσ.1, ht.1], by linarith [hσ.2]⟩
    exact curveVelocity_mem_sliceTangent hcd hev
  · have htb : t = b := le_antisymm ht.2 hge
    have hat : a < t := by rw [htb]; exact hab
    have hev : ∀ᶠ σ in 𝓝[>] (0 : ℝ), c (t - σ) ∈ S := by
      filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hat)] with σ hσ
      exact hmem (t - σ) ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
    have hline : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun σ : ℝ => t - σ) 0 := by
      have h : HasFDerivAt (fun σ : ℝ => t - σ) (-(ContinuousLinearMap.id ℝ ℝ)) 0 := by
        simpa [sub_eq_add_neg] using (hasFDerivAt_id (0 : ℝ)).neg.const_add t
      exact h.hasMFDerivAt.mdifferentiableAt
    have hf0 : MDifferentiableAt 𝓘(ℝ, ℝ) I c ((fun σ : ℝ => t - σ) 0) := by
      simpa only [sub_zero] using hcd
    have hshift : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun σ : ℝ => c (t - σ)) 0 :=
      MDifferentiableAt.comp (0 : ℝ) hf0 hline
    have hmm := mem_sliceTangent_of_curve (I := I) (S := S) (f := fun σ : ℝ => c (t - σ))
      (x := c t) (by simp) hev hshift
    have hrefl : (mfderiv 𝓘(ℝ, ℝ) I (fun σ : ℝ => c (t - σ)) 0 (1 : ℝ) :
        TangentSpace I (c t)) = -(curveVelocity (I := I) c t) := mfderiv_reflect hcd
    rw [hrefl] at hmm
    simpa using (sliceTangent I S (c t)).neg_mem hmm

omit [T2Space (TangentBundle I M)] in
private theorem forall_mem_sliceTangent_of_hasFamilies
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hfam : HasSliceDefiningFamilies (I := I) g C)
    {τ : ℝ → M} (hτsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ τ)
    {ξ : ∀ t : ℝ, TangentSpace I (τ t)} {a b : ℝ}
    (hξdiff : ∀ t ∈ Icc a b, DifferentiableAt ℝ (chartRepAt (I := I) τ ξ t) t)
    (hξpar : ∀ t ∈ Icc a b, covDerivAlong (I := I) g τ ξ t = 0)
    (hτN : ∀ t ∈ Icc a b, τ t ∈ maxSliceLocus I C)
    (hvel : ∀ t ∈ Icc a b,
      curveVelocity (I := I) τ t ∈ sliceTangent I (maxSliceLocus I C) (τ t))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (h0 : ξ t₀ ∈ sliceTangent I (maxSliceLocus I C) (τ t₀)) :
    ∀ t ∈ Icc a b, ξ t ∈ sliceTangent I (maxSliceLocus I C) (τ t) := by
  classical
  have hlocal : ∀ s ∈ Icc a b, ∃ ε > 0, ∀ t ∈ Icc a b, |t - s| < ε →
      (ξ t ∈ sliceTangent I (maxSliceLocus I C) (τ t) ↔
        ξ s ∈ sliceTangent I (maxSliceLocus I C) (τ s)) := by
    intro s hs
    obtain ⟨m, F, W, hxW, hfamW⟩ := hfam (τ s) (hτN s hs)
    exact exists_local_sliceTangent_iff hEnorm hC hCclosed hfamW hτsm hξdiff hξpar
      hτN hvel hs hxW
  have : PreconnectedSpace ↥(Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  set T : Set ↥(Icc a b) :=
    {p | ξ (p : ℝ) ∈ sliceTangent I (maxSliceLocus I C) (τ (p : ℝ))} with hTdef
  have hdist : ∀ p q : ↥(Icc a b), ∀ ε : ℝ, q ∈ Metric.ball p ε →
      |(q : ℝ) - (p : ℝ)| < ε := by
    intro p q ε hq
    have h := Metric.mem_ball.mp hq
    rwa [Subtype.dist_eq, Real.dist_eq] at h
  have hTopen : IsOpen T := by
    rw [Metric.isOpen_iff]
    intro p hp
    obtain ⟨ε, hε, hiff⟩ := hlocal (p : ℝ) p.2
    exact ⟨ε, hε, fun q hq => (hiff (q : ℝ) q.2 (hdist p q ε hq)).2 hp⟩
  have hTclosed : IsClosed T := by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro p hp
    obtain ⟨ε, hε, hiff⟩ := hlocal (p : ℝ) p.2
    refine ⟨ε, hε, fun q hq hq' => ?_⟩
    exact hp ((hiff (q : ℝ) q.2 (hdist p q ε hq)).1 hq')
  have huniv : T = Set.univ :=
    IsClopen.eq_univ ⟨hTclosed, hTopen⟩ ⟨⟨t₀, ht₀⟩, h0⟩
  intro t ht
  have hmem : (⟨t, ht⟩ : ↥(Icc a b)) ∈ T := by rw [huniv]; exact Set.mem_univ _
  exact hmem



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem mfderiv_symm_apply_mfderiv
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞} {x : M} (hxc : x ∈ c.source)
    (v : TangentSpace I x) :
    mfderiv 𝓘(ℝ, E) I c.symm (c x) (mfderiv I 𝓘(ℝ, E) c x v) = v := by
  have hcdiff : MDifferentiableAt I 𝓘(ℝ, E) c x := c.mdifferentiableAt (by simp) hxc
  have hcx : c x ∈ c.target := c.toPartialEquiv.map_source hxc
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I c.symm (c x) :=
    c.symm.mdifferentiableAt (by simp) hcx
  have hcomp : mfderiv I I (fun y : M => c.symm (c y)) x =
      (mfderiv 𝓘(ℝ, E) I c.symm (c x)).comp (mfderiv I 𝓘(ℝ, E) c x) :=
    mfderiv_comp x hsymm hcdiff
  have heq : (fun y : M => c.symm (c y)) =ᶠ[𝓝 x] id := by
    filter_upwards [c.open_source.mem_nhds hxc] with y hy
    exact c.toPartialEquiv.left_inv hy
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hcomp.symm

omit [T2Space (TangentBundle I M)] in
theorem hasSliceDefiningFamilies_of_totallyConvex
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) :
    HasSliceDefiningFamilies (I := I) g C := by
  classical
  intro x hx
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ :=
    isEmbeddedSlice_maxSliceLocus (I := I) hEnorm hC x hx
  set K : Submodule ℝ E := A.direction with hKdef
  have hAfin : FiniteDimensional ℝ K := hA
  set m : ℕ := Module.finrank ℝ (E ⧸ K) with hmdef
  set bq : Module.Basis (Fin m) ℝ (E ⧸ K) := Module.finBasis ℝ (E ⧸ K) with hbqdef
  set μ : Fin m → (E →L[ℝ] ℝ) := fun i =>
    LinearMap.toContinuousLinearMap ((bq.coord i).comp K.mkQ) with hμdef
  have hμapply : ∀ (i : Fin m) (w : E), μ i w = bq.coord i (K.mkQ w) := fun i w => rfl
  have hker : ∀ w : E, (∀ i : Fin m, μ i w = 0) ↔ w ∈ K := by
    intro w
    constructor
    · intro h
      have hq : K.mkQ w = 0 := by
        refine bq.ext_elem fun i => ?_
        have hi : bq.coord i (K.mkQ w) = 0 := by rw [← hμapply]; exact h i
        simpa using hi
      rwa [← Submodule.ker_mkQ K, LinearMap.mem_ker]
    · intro hw i
      have hq : K.mkQ w = 0 := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact hw
      rw [hμapply, hq]
      simp
  have hconstA : ∀ (i : Fin m) (y₁ y₂ : E), y₁ ∈ A → y₂ ∈ A → μ i y₁ = μ i y₂ := by
    intro i y₁ y₂ h₁ h₂
    have hsub : y₁ - y₂ ∈ K := AffineSubspace.vsub_mem_direction h₁ h₂
    have := (hker (y₁ - y₂)).2 hsub i
    have hlin : μ i (y₁ - y₂) = μ i y₁ - μ i y₂ := ContinuousLinearMap.map_sub _ _ _
    linarith [hlin ▸ this]
  set f : Fin m → M → ℝ := fun i z => μ i (c z) with hfdef
  have hfOn : ∀ i : Fin m, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f i) c.source := by
    intro i
    exact (μ i).contMDiff.comp_contMDiffOn c.contMDiffOn
  have hgerm : ∀ i : Fin m, ∃ Fi : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ Fi ∧ Fi =ᶠ[𝓝 x] f i :=
    fun i => DifferentialGeometry.exists_smooth_germ (I := I) c.open_source hxc (hfOn i)
  choose F hFsm hFeq using hgerm
  have hVex : ∀ i : Fin m, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∀ z ∈ V, F i z = f i z := by
    intro i
    obtain ⟨S, hS, hSsub⟩ := Filter.eventually_iff_exists_mem.mp (hFeq i)
    obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hS
    exact ⟨V, hVopen, hxV, fun z hz => hSsub z (hVsub hz)⟩
  choose V hVopen hxV hVeq using hVex
  set W : Set M := c.source ∩ ⋂ i : Fin m, V i with hWdef
  have hWopen : IsOpen W := c.open_source.inter (isOpen_iInter_of_finite hVopen)
  have hxW : x ∈ W := ⟨hxc, Set.mem_iInter.2 hxV⟩
  have hWc : ∀ z ∈ W, z ∈ c.source := fun z hz => hz.1
  have hWF : ∀ z ∈ W, ∀ i : Fin m, F i z = μ i (c z) := by
    intro z hz i
    exact hVeq i z (Set.mem_iInter.1 hz.2 i)
  have hWnhds : ∀ z ∈ W, ∀ i : Fin m, F i =ᶠ[𝓝 z] f i := by
    intro z hz i
    filter_upwards [hWopen.mem_nhds hz] with z' hz'
    exact hWF z' hz' i
  have hmfderivF : ∀ z ∈ W, ∀ (i : Fin m) (v : TangentSpace I z),
      (mfderiv I 𝓘(ℝ, ℝ) (F i) z v : ℝ) = μ i (mfderiv I 𝓘(ℝ, E) c z v) := by
    intro z hz i v
    have hcz : MDifferentiableAt I 𝓘(ℝ, E) c z := c.mdifferentiableAt (by simp) (hWc z hz)
    have hcomp : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y : M => μ i (c y)) z
        ((μ i).comp (mfderiv I 𝓘(ℝ, E) c z)) :=
      HasMFDerivAt.comp z (μ i).hasMFDerivAt hcz.hasMFDerivAt
    rw [(hWnhds z hz i).mfderiv_eq]
    rw [hcomp.mfderiv]
    rfl
  refine ⟨m, F, W, hxW, ?_, ?_, ?_, ?_, ?_⟩
  · exact hWopen
  · exact hFsm
  · intro z hz hzN i
    filter_upwards [hWopen.mem_nhds hz] with z' hz' hz'N
    rw [hWF z' hz' i, hWF z hz i]
    exact hconstA i (c z') (c z) ((himage.apply_mem_iff (hWc z' hz')).2 hz'N)
      ((himage.apply_mem_iff (hWc z hz)).2 hzN)
  · intro z hz hzN v
    have hst := sliceTangent_eq_comap (I := I) hzN hA (hWc z hz) himage
    constructor
    · intro hv i
      have hv' : mfderiv I 𝓘(ℝ, E) c z v ∈ K := by rw [hst] at hv; exact hv
      rw [gradFun_metricDual (I := I) g (F i) z v, hmfderivF z hz i v]
      exact (hker _).2 hv' i
    · intro h
      have hall : ∀ i : Fin m, μ i (mfderiv I 𝓘(ℝ, E) c z v) = 0 := by
        intro i
        rw [← hmfderivF z hz i v, ← gradFun_metricDual (I := I) g (F i) z v]
        exact h i
      rw [hst]
      exact (hker _).1 hall
  · intro z hz hzN cf hcf
    have hzero : ∀ v : TangentSpace I z,
        ∑ i : Fin m, cf i * μ i (mfderiv I 𝓘(ℝ, E) c z v) = 0 := by
      intro v
      have h1 : g.inner z v (∑ i : Fin m, cf i • gradFun (I := I) g (F i) z) = 0 := by
        rw [hcf]
        simp
      rw [inner_sum_smul (I := I) g z cf _ v] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [g.symm z v, gradFun_metricDual (I := I) g (F i) z v, hmfderivF z hz i v]
    have hsurj : Function.Surjective (mfderiv I 𝓘(ℝ, E) c z) := by
      have hinj : Function.Injective
          ((mfderiv I 𝓘(ℝ, E) c z).toLinearMap : TangentSpace I z →ₗ[ℝ] E) := by
        intro v w hvw
        have h1 := mfderiv_symm_apply_mfderiv (c := c) (hWc z hz) v
        have h2 := mfderiv_symm_apply_mfderiv (c := c) (hWc z hz) w
        rw [← h1, ← h2]
        exact congrArg _ hvw
      have hfin : Module.finrank ℝ (TangentSpace I z) = Module.finrank ℝ E := rfl
      have : FiniteDimensional ℝ (TangentSpace I z) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj
    have hall : ∀ w : E, ∑ i : Fin m, cf i * μ i w = 0 := by
      intro w
      obtain ⟨v, hv⟩ := hsurj w
      rw [← hv]
      exact hzero v
    funext j
    obtain ⟨w₀, hw₀⟩ := Submodule.mkQ_surjective K (bq j)
    have hj := hall w₀
    have hcoord : ∀ i : Fin m, cf i * μ i w₀ = if i = j then cf i else 0 := by
      intro i
      rw [hμapply, hw₀, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply]
      by_cases h : i = j
      · simp [h]
      · simp [h, Ne.symm h]
    simp only [hcoord] at hj
    rw [Finset.sum_ite_eq' Finset.univ j cf] at hj
    simpa using hj



omit [T2Space (TangentBundle I M)] in
theorem hasSliceParallelTransport_of_hasSliceDefiningFamilies
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hfam : HasSliceDefiningFamilies (I := I) g C) :
    HasSliceParallelTransport (I := I) g hEnorm C := by
  intro y u ξ L hξ hτN hξ0 t ht
  set τ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm y u with hτdef
  have hτsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ τ :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm y u
  rcases lt_or_ge 0 L with hL | hL
  · have hvel : ∀ s ∈ Icc (0 : ℝ) L,
        curveVelocity (I := I) τ s ∈ sliceTangent I (maxSliceLocus I C) (τ s) := fun s hs =>
      curveVelocity_mem_sliceTangent_Icc hτsm hL hs hτN
    exact forall_mem_sliceTangent_of_hasFamilies hEnorm hC hCclosed hfam hτsm
      hξ.1 hξ.2.1 hτN hvel (left_mem_Icc.2 hL.le) hξ0 t ht
  · rcases lt_or_ge L 0 with hLneg | hL0
    · exact absurd (le_trans ht.1 ht.2) (not_le.2 hLneg)
    · have hL0' : L = 0 := le_antisymm hL hL0
      have ht0 : t = 0 := le_antisymm (by rw [← hL0']; exact ht.2) ht.1
      rw [ht0]
      exact hξ0

omit [T2Space (TangentBundle I M)] in
theorem hasSliceParallelTransport_of_totallyConvex
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C) :
    HasSliceParallelTransport (I := I) g hEnorm C :=
  hasSliceParallelTransport_of_hasSliceDefiningFamilies hEnorm hC hCclosed
    (hasSliceDefiningFamilies_of_totallyConvex hEnorm hC)

omit [T2Space (TangentBundle I M)] in
theorem forall_mem_sliceTangent_of_parallel
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {τ : ℝ → M} (hτsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ τ)
    {ξ : ∀ t : ℝ, TangentSpace I (τ t)} {a b : ℝ}
    (hξdiff : ∀ t ∈ Icc a b, DifferentiableAt ℝ (chartRepAt (I := I) τ ξ t) t)
    (hξpar : ∀ t ∈ Icc a b, covDerivAlong (I := I) g τ ξ t = 0)
    (hτN : ∀ t ∈ Icc a b, τ t ∈ maxSliceLocus I C)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (h0 : ξ t₀ ∈ sliceTangent I (maxSliceLocus I C) (τ t₀)) :
    ∀ t ∈ Icc a b, ξ t ∈ sliceTangent I (maxSliceLocus I C) (τ t) := by
  rcases lt_or_ge a b with hab | hab
  · have hvel : ∀ t ∈ Icc a b,
        curveVelocity (I := I) τ t ∈ sliceTangent I (maxSliceLocus I C) (τ t) :=
      fun t ht => curveVelocity_mem_sliceTangent_Icc hτsm hab ht hτN
    exact forall_mem_sliceTangent_of_hasFamilies hEnorm hC hCclosed
      (hasSliceDefiningFamilies_of_totallyConvex hEnorm hC) hτsm hξdiff hξpar hτN
      hvel ht₀ h0
  · intro t ht
    have htt : t = t₀ :=
      le_antisymm (le_trans (le_trans ht.2 hab) ht₀.1)
        (le_trans (le_trans ht₀.2 hab) ht.1)
    subst htt
    exact h0

theorem parallelShift_mem_maxSliceLocus_of_totallyConvex
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {y : M} {u : TangentSpace I y}
    {ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t)} {L : ℝ}
    (hξ : IsParallelPerpUnitField (I := I) g hEnorm y u ξ L)
    (hτ : ∀ t ∈ Icc (0 : ℝ) L,
      intrinsicGeodesic (I := I) g hEnorm y u t ∈ maxSliceLocus I C)
    (hξ0 : ξ 0 ∈ sliceTangent I (maxSliceLocus I C)
      (intrinsicGeodesic (I := I) g hEnorm y u 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L)
    {h : ℝ} (hh : |h| < Metric.infDist (intrinsicGeodesic (I := I) g hEnorm y u t)
      (relBoundary I C)) :
    parallelShift (I := I) g hEnorm y u ξ h t ∈ maxSliceLocus I C :=
  parallelShift_mem_maxSliceLocus_of_sliceParallelTransport hEnorm hC hCclosed
    (hasSliceParallelTransport_of_totallyConvex hEnorm hC hCclosed) hξ hτ hξ0 ht hh

end DifferentialGeometry.Geometry.Topology

end
