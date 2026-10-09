import DifferentialGeometry.Topology.Manifold.SmoothCarrier.Metric
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientPullback
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.SectionalTransition
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.SectionalPlane

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

namespace DifferentialGeometry.Analysis

open DifferentialGeometry.Topology.Manifold (SmoothCompatibleAtlas)

private theorem two_le_cast_pred {K : ℕ} (hK : 3 ≤ K) : (2 : ℕ∞ω) ≤ ((K - 1 : ℕ) : ℕ∞ω) := by
  exact_mod_cast (by omega : 2 ≤ K - 1)

private theorem three_le_cast {K : ℕ} (hK : 3 ≤ K) : (3 : ℕ∞ω) ≤ (K : ℕ∞ω) := by
  exact_mod_cast hK

theorem coefficientRm04_coefficientPullback_homeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {c : E → E →L[ℝ] E →L[ℝ] ℝ} {κ : E ≃ₜ E} {K : ℕ} (hK : 3 ≤ K)
    (hc : ContDiffOn ℝ (K - 1 : ℕ) c V) (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ V, IsCoercive (c z)) (hκ : ContDiff ℝ K κ) (hκs : ContDiff ℝ K κ.symm)
    (hmaps : MapsTo κ.symm U V) {y : E} (hy : y ∈ U) (X Y Z W : E) :
    coefficientRm04 (coefficientPullback c κ.symm) y X Y Z W =
      coefficientRm04 c (κ.symm y) (fderiv ℝ κ.symm y X) (fderiv ℝ κ.symm y Y)
        (fderiv ℝ κ.symm y Z) (fderiv ℝ κ.symm y W) := by
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact coefficientRm04_transition hU hV (hc.of_le (two_le_cast_pred hK)) hcsymm hcco
    (hκs.of_le (three_le_cast hK)).contDiffOn hmaps
    (fun z _ => isInvertible_fderiv_homeomorph_symm hK0 hκ hκs z)
    (fun z _ u v => coefficientPullback_apply c κ.symm z u v) hy X Y Z W

theorem coefficientSectional_coefficientPullback_homeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {c : E → E →L[ℝ] E →L[ℝ] ℝ} {κ : E ≃ₜ E} {K : ℕ} (hK : 3 ≤ K)
    (hc : ContDiffOn ℝ (K - 1 : ℕ) c V) (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ V, IsCoercive (c z)) (hκ : ContDiff ℝ K κ) (hκs : ContDiff ℝ K κ.symm)
    (hmaps : MapsTo κ.symm U V) {y : E} (hy : y ∈ U) (v u : E) :
    coefficientSectional (coefficientPullback c κ.symm) y v u =
      coefficientSectional c (κ.symm y) (fderiv ℝ κ.symm y v) (fderiv ℝ κ.symm y u) := by
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact coefficientSectional_transition hU hV (hc.of_le (two_le_cast_pred hK)) hcsymm hcco
    (hκs.of_le (three_le_cast hK)).contDiffOn hmaps
    (fun z _ => isInvertible_fderiv_homeomorph_symm hK0 hκ hκs z)
    (fun z _ u' v' => coefficientPullback_apply c κ.symm z u' v') hy v u

theorem coefficientRm04_nonneg_coefficientPullback_homeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) {c : E → E →L[ℝ] E →L[ℝ] ℝ} {κ : E ≃ₜ E} {K : ℕ}
    (hK : 3 ≤ K) (hc : ContDiffOn ℝ (K - 1 : ℕ) c V)
    (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u) (hcco : ∀ z ∈ V, IsCoercive (c z))
    (hκ : ContDiff ℝ K κ) (hκs : ContDiff ℝ K κ.symm) (hmaps : MapsTo κ.symm U V)
    (hsign : ∀ z ∈ V, ∀ v u : E, 0 ≤ coefficientRm04 c z v u u v) :
    ∀ y ∈ U, ∀ v u : E,
      0 ≤ coefficientRm04 (coefficientPullback c κ.symm) y v u u v ∧
        0 ≤ coefficientSectional (coefficientPullback c κ.symm) y v u := by
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact coefficientSectional_nonneg_of_pullback hU hV (hc.of_le (two_le_cast_pred hK)) hcsymm
    hcco (hκs.of_le (three_le_cast hK)).contDiffOn hmaps
    (fun z _ => isInvertible_fderiv_homeomorph_symm hK0 hκ hκs z)
    (fun z _ u v => coefficientPullback_apply c κ.symm z u v) hsign

theorem coefficientSectional_chart_transition {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] {ι : Type*}
    (ψ : ι → OpenPartialHomeomorph E X) (b : ι → E → E →L[ℝ] E →L[ℝ] ℝ) (Ω : ι → Set E)
    (hΩ : ∀ j, IsOpen (Ω j)) (hψΩ : ∀ j, (ψ j).source ⊆ Ω j)
    (hb : ∀ j, ContDiffOn ℝ 2 (b j) (Ω j))
    (hbsymm : ∀ j, ∀ u ∈ Ω j, ∀ v w : E, b j u v w = b j u w v)
    (hbco : ∀ j, ∀ u ∈ Ω j, IsCoercive (b j u))
    (htr : ∀ j d, ContDiffOn ℝ 3 ((ψ j).symm.symm.trans (ψ d).symm)
      ((ψ j).symm.symm.trans (ψ d).symm).source)
    (hlaw : ∀ (j d : ι) (u : E), u ∈ ((ψ j).symm.symm.trans (ψ d).symm).source →
      b j u = (b d (((ψ j).symm.symm.trans (ψ d).symm) u)).bilinearComp
        (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u)
        (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u))
    (j d : ι) {u : E} (hu : u ∈ ((ψ j).symm.symm.trans (ψ d).symm).source) (v w : E) :
    coefficientSectional (b j) u v w =
      coefficientSectional (b d) (((ψ j).symm.symm.trans (ψ d).symm) u)
        (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u v)
        (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u w) := by
  have hmaps : MapsTo ((ψ j).symm.symm.trans (ψ d).symm)
      ((ψ j).symm.symm.trans (ψ d).symm).source (Ω d) := by
    intro z hz
    have h := ((ψ j).symm.symm.trans (ψ d).symm).map_source hz
    rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target] at h
    exact hψΩ d h.1
  have hTs : ContDiffOn ℝ 3 ((ψ j).symm.symm.trans (ψ d).symm).symm
      ((ψ j).symm.symm.trans (ψ d).symm).target := by
    rw [← OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm ((ψ j).symm)]
    exact htr d j
  exact coefficientSectional_transition ((ψ j).symm.symm.trans (ψ d).symm).open_source (hΩ d)
    (hb d) (hbsymm d) (hbco d) (htr j d) hmaps
    (fun z hz => isInvertible_fderiv_of_contDiffOn _ (by norm_num) (htr j d) hTs hz)
    (fun z hz u' v' => by rw [hlaw j d z hz, ContinuousLinearMap.bilinearComp_apply]) hu v w

private theorem mapsTo_homeomorph_symm_of_chart_eq {E X ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] {A : SmoothCompatibleAtlas E X ι}
    {ψ : OpenPartialHomeomorph E X} {κ : E ≃ₜ E} {j : ι}
    (hchart : A.chart j = ψ.symm.trans κ.toOpenPartialHomeomorph)
    (htarget : (A.chart j).target = ψ.source) : MapsTo κ.symm ψ.source ψ.source := by
  intro z hz
  rw [← htarget, hchart, OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage,
    Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.symm_target] at hz
  exact hz.2

private theorem fderiv_apply_eq_of_comp_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g h k : E → E} (hfg : f ∘ g = h ∘ k) {y : E}
    (hf : DifferentiableAt ℝ f (g y)) (hg : DifferentiableAt ℝ g y)
    (hh : DifferentiableAt ℝ h (k y)) (hk : DifferentiableAt ℝ k y) (t : E) :
    fderiv ℝ f (g y) (fderiv ℝ g y t) = fderiv ℝ h (k y) (fderiv ℝ k y t) := by
  have h1 : fderiv ℝ (f ∘ g) y = (fderiv ℝ f (g y)).comp (fderiv ℝ g y) := fderiv_comp y hf hg
  have h2 : fderiv ℝ (h ∘ k) y = (fderiv ℝ h (k y)).comp (fderiv ℝ k y) := fderiv_comp y hh hk
  rw [hfg, h2] at h1
  have h3 := DFunLike.congr_fun h1 t
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h3
  exact h3.symm

theorem coefficientSectional_carrier_chart_transition {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] {ι : Type*}
    (ψ : ι → OpenPartialHomeomorph E X) (b : ι → E → E →L[ℝ] E →L[ℝ] ℝ) (Ω : ι → Set E)
    (hΩ : ∀ j, IsOpen (Ω j)) (hψΩ : ∀ j, (ψ j).source ⊆ Ω j)
    (hb : ∀ j, ContDiffOn ℝ 2 (b j) (Ω j))
    (hbsymm : ∀ j, ∀ u ∈ Ω j, ∀ v w : E, b j u v w = b j u w v)
    (hbco : ∀ j, ∀ u ∈ Ω j, IsCoercive (b j u))
    (htr : ∀ j d, ContDiffOn ℝ 3 ((ψ j).symm.symm.trans (ψ d).symm)
      ((ψ j).symm.symm.trans (ψ d).symm).source)
    (hlaw : ∀ (j d : ι) (u : E), u ∈ ((ψ j).symm.symm.trans (ψ d).symm).source →
      b j u = (b d (((ψ j).symm.symm.trans (ψ d).symm) u)).bilinearComp
        (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u)
        (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u))
    {K : ℕ} (hK : 3 ≤ K) (A : SmoothCompatibleAtlas E X ι) (κ : ι → E ≃ₜ E)
    (hchart : ∀ j, A.chart j = (ψ j).symm.trans (κ j).toOpenPartialHomeomorph)
    (htarget : ∀ j, (A.chart j).target = (ψ j).source)
    (hκ : ∀ j, ContDiff ℝ K (κ j) ∧ ContDiff ℝ K (κ j).symm)
    (j d : ι) {y : E} (hy : y ∈ ((A.chart j).symm.trans (A.chart d)).source) (v u : E) :
    coefficientSectional (coefficientPullback (b j) (κ j).symm) y v u =
      coefficientSectional (coefficientPullback (b d) (κ d).symm)
        (((A.chart j).symm.trans (A.chart d)) y)
        (fderiv ℝ ((A.chart j).symm.trans (A.chart d)) y v)
        (fderiv ℝ ((A.chart j).symm.trans (A.chart d)) y u) := by
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmj := mapsTo_homeomorph_symm_of_chart_eq (hchart j) (htarget j)
  have hmd := mapsTo_homeomorph_symm_of_chart_eq (hchart d) (htarget d)
  have hy' := hy
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, htarget j] at hy'
  have hu : (κ j).symm y ∈ ((ψ j).symm.symm.trans (ψ d).symm).source := by
    have h := hy'.2
    rw [Set.mem_preimage, hchart d, hchart j, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.symm_symm (ψ j)] at h
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_symm (ψ j)]
    exact ⟨hmj hy'.1, h.1⟩
  have hSy : ((A.chart j).symm.trans (A.chart d)) y ∈ (ψ d).source := by
    have h := ((A.chart j).symm.trans (A.chart d)).map_source hy
    rw [OpenPartialHomeomorph.trans_target, htarget d] at h
    exact h.1
  have hcoord : ⇑(κ d).symm ∘ ⇑((A.chart j).symm.trans (A.chart d)) =
      ⇑((ψ j).symm.symm.trans (ψ d).symm) ∘ ⇑(κ j).symm := by
    funext z
    rw [hchart j, hchart d]
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.coe_trans_symm, Homeomorph.toOpenPartialHomeomorph_apply,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.symm_apply_apply]
  have hpt := congrFun hcoord y
  rw [Function.comp_apply, Function.comp_apply] at hpt
  have hder : ∀ t : E, fderiv ℝ (κ d).symm (((A.chart j).symm.trans (A.chart d)) y)
      (fderiv ℝ ((A.chart j).symm.trans (A.chart d)) y t) =
      fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) ((κ j).symm y)
        (fderiv ℝ (κ j).symm y t) :=
    fderiv_apply_eq_of_comp_eq hcoord ((hκ d).2.differentiable hK0 _)
      (((A.contDiffOn_transition j d).contDiffAt
        (((A.chart j).symm.trans (A.chart d)).open_source.mem_nhds hy)).differentiableAt
        (by decide))
      (((htr j d).contDiffAt
        (((ψ j).symm.symm.trans (ψ d).symm).open_source.mem_nhds hu)).differentiableAt
        (by norm_num))
      ((hκ j).2.differentiable hK0 _)
  rw [coefficientSectional_transition (b := coefficientPullback (b j) (κ j).symm)
      (ψ j).open_source (hΩ j) (hb j) (hbsymm j) (hbco j)
      ((hκ j).2.of_le (three_le_cast hK)).contDiffOn (hmj.mono_right (hψΩ j))
      (fun z _ => isInvertible_fderiv_homeomorph_symm hK0 (hκ j).1 (hκ j).2 z)
      (fun z _ u' v' => coefficientPullback_apply (b j) (κ j).symm z u' v') hy'.1 v u,
    coefficientSectional_chart_transition ψ b Ω hΩ hψΩ hb hbsymm hbco htr hlaw j d hu,
    coefficientSectional_transition (b := coefficientPullback (b d) (κ d).symm)
      (ψ d).open_source (hΩ d) (hb d) (hbsymm d) (hbco d)
      ((hκ d).2.of_le (three_le_cast hK)).contDiffOn (hmd.mono_right (hψΩ d))
      (fun z _ => isInvertible_fderiv_homeomorph_symm hK0 (hκ d).1 (hκ d).2 z)
      (fun z _ u' v' => coefficientPullback_apply (b d) (κ d).symm z u' v') hSy,
    hpt, hder v, hder u]

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Topology.Manifold

open DifferentialGeometry.Analysis

private theorem chart_target_eq {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace X] (A : SmoothCompatibleAtlas E X ι) (j : ι) :
    (SmoothCarrier.chart A j).target = (A.chart j).target :=
  rfl

private theorem symm_toBase_eq_of_chart_eq {E X ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MetricSpace X] {A : SmoothCompatibleAtlas E X ι}
    {ψ : OpenPartialHomeomorph E X} {κ : E ≃ₜ E} {j : ι}
    (hchart : A.chart j = ψ.symm.trans κ.toOpenPartialHomeomorph) (x : SmoothCarrier A) :
    ψ.symm (SmoothCarrier.toBase A x) = κ.symm (SmoothCarrier.chart A j x) := by
  rw [SmoothCarrier.chart_apply, hchart, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.symm_apply_apply]

private theorem mfderiv_toBase_transport {E X ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MetricSpace X] [ChartedSpace E X] {A : SmoothCompatibleAtlas E X ι}
    {ψ : OpenPartialHomeomorph E X} {κ : E ≃ₜ E} {j : ι}
    (hchart : A.chart j = ψ.symm.trans κ.toOpenPartialHomeomorph) {x : SmoothCarrier A}
    (hψd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) ψ.symm (SmoothCarrier.toBase A x))
    (htb : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x)
    (hθd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x)
    (hκd : DifferentiableAt ℝ κ.symm (SmoothCarrier.chart A j x)) (v : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ.symm (SmoothCarrier.toBase A x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v) =
      fderiv ℝ κ.symm (SmoothCarrier.chart A j x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x v) := by
  have hfun : ψ.symm ∘ SmoothCarrier.toBase A = κ.symm ∘ SmoothCarrier.chart A j :=
    funext (symm_toBase_eq_of_chart_eq hchart)
  rw [← mfderiv_comp_apply x hψd htb v, hfun, mfderiv_comp_apply x hκd.mdifferentiableAt hθd v]
  exact DFunLike.congr_fun hκd.hasFDerivAt.hasMFDerivAt.mfderiv _

theorem SmoothCarrier.inner_chart_symm_eq_coefficientPullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Type*} [MetricSpace X] {ι : Type*} {K : ℕ} (hK : 1 ≤ K)
    (ψ : ι → OpenPartialHomeomorph E X) (hcover : ∀ x, ∃ j, x ∈ (ψ j).target)
    (hM : letI := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
      IsManifold 𝓘(ℝ, E) K X)
    (A : SmoothCompatibleAtlas E X ι) (κ : ι → E ≃ₜ E)
    (hchart : ∀ j, A.chart j = (ψ j).symm.trans (κ j).toOpenPartialHomeomorph)
    (htarget : ∀ j, (A.chart j).target = (ψ j).source)
    (hcomp : A.IsCompatible (fun j => (ψ j).symm) K)
    (b : ι → E → E →L[ℝ] E →L[ℝ] ℝ) :
    letI := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
    letI := hM
    letI : IsManifold 𝓘(ℝ, E) 1 X := IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast hK)
    ∀ (G : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
        (TangentSpace 𝓘(ℝ, E) : X → Type _))
      (G' : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
        (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _)),
      (∀ j x, x ∈ (ψ j).symm.source → ∀ v w : E,
        G.inner x v w = b j ((ψ j).symm x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm x v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm x w)) →
      (∀ (x : SmoothCarrier A) (v w : E),
        G'.inner x v w = G.inner (SmoothCarrier.toBase A x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w)) →
      ∀ j, ∀ y ∈ (ψ j).source, ∀ v w : E,
        G'.inner ((SmoothCarrier.chart A j).symm y)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j).symm y v)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j).symm y w) =
          coefficientPullback (b j) (κ j).symm y v w := by
  let _ : ChartedSpace E X := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
  have : IsManifold 𝓘(ℝ, E) K X := hM
  have : IsManifold 𝓘(ℝ, E) 1 X := IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast hK)
  intro G G' hG hG' j y hy v w
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hθ : SmoothCarrier.chart A j ∈ atlas E (SmoothCarrier A) := ⟨j, rfl⟩
  have hψm : (ψ j).symm ∈ atlas E X := ⟨j, rfl⟩
  have hyt : y ∈ (SmoothCarrier.chart A j).target := by
    rw [chart_target_eq, htarget j]
    exact hy
  have hp := (SmoothCarrier.chart A j).map_target hyt
  have hpy := (SmoothCarrier.chart A j).right_inv hyt
  have hq := (SmoothCarrier.mem_chart_source_iff A j _).mp hp
  rw [hchart j, OpenPartialHomeomorph.trans_source] at hq
  have htb : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A)
      ((SmoothCarrier.chart A j).symm y) :=
    ((SmoothCarrier.contMDiff_toBase A (fun j => (ψ j).symm) hcover hcomp) _).mdifferentiableAt
      hK0
  have hψd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm
      (SmoothCarrier.toBase A ((SmoothCarrier.chart A j).symm y)) :=
    mdifferentiableAt_atlas hψm hq.1
  have hθd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j)
      ((SmoothCarrier.chart A j).symm y) :=
    mdifferentiableAt_atlas hθ hp
  have hθs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j).symm y :=
    mdifferentiableAt_atlas_symm hθ hyt
  have hcd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      ((ψ j).symm ∘ SmoothCarrier.toBase A ∘ (SmoothCarrier.chart A j).symm) y :=
    MDifferentiableAt.comp y hψd (MDifferentiableAt.comp y htb hθs)
  have hev : (κ j).symm =ᶠ[𝓝 y]
      (ψ j).symm ∘ SmoothCarrier.toBase A ∘ (SmoothCarrier.chart A j).symm :=
    Filter.eventually_of_mem ((SmoothCarrier.chart A j).open_target.mem_nhds hyt) fun z hz => by
      rw [Function.comp_apply, Function.comp_apply, symm_toBase_eq_of_chart_eq (hchart j),
        (SmoothCarrier.chart A j).right_inv hz]
  have hκs : DifferentiableAt ℝ (κ j).symm y := hcd.differentiableAt.congr_of_eventuallyEq hev
  have hκs' : DifferentiableAt ℝ (κ j).symm
      (SmoothCarrier.chart A j ((SmoothCarrier.chart A j).symm y)) := by
    rw [hpy]
    exact hκs
  have hinv : ∀ t : E, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j)
      ((SmoothCarrier.chart A j).symm y)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j).symm y t) = t := fun t =>
    DFunLike.congr_fun ((mdifferentiable_of_mem_atlas (I := 𝓘(ℝ, E)) hθ).comp_symm_deriv hyt) t
  have hT : ∀ t : E, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm
      (SmoothCarrier.toBase A ((SmoothCarrier.chart A j).symm y))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) ((SmoothCarrier.chart A j).symm y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j).symm y t)) =
      fderiv ℝ (κ j).symm y t := by
    intro t
    rw [mfderiv_toBase_transport (hchart j) hψd htb hθd hκs'
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j).symm y t), hinv t, hpy]
  have hpt := symm_toBase_eq_of_chart_eq (hchart j) ((SmoothCarrier.chart A j).symm y)
  rw [hpy] at hpt
  rw [coefficientPullback_apply, ← hT v, ← hT w, ← hpt]
  exact (hG' ((SmoothCarrier.chart A j).symm y) _ _).trans (hG j _ hq.1 _ _)

theorem SmoothCarrier.coefficientSectional_chart_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [MetricSpace X] {ι : Type*} {K : ℕ} (hK : 3 ≤ K)
    (ψ : ι → OpenPartialHomeomorph E X) (hcover : ∀ x, ∃ j, x ∈ (ψ j).target)
    (hM : letI := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
      IsManifold 𝓘(ℝ, E) K X)
    (A : SmoothCompatibleAtlas E X ι) (κ : ι → E ≃ₜ E)
    (hchart : ∀ j, A.chart j = (ψ j).symm.trans (κ j).toOpenPartialHomeomorph)
    (htarget : ∀ j, (A.chart j).target = (ψ j).source)
    (hκ : ∀ j, ContDiff ℝ K (κ j) ∧ ContDiff ℝ K (κ j).symm)
    (hcomp : A.IsCompatible (fun j => (ψ j).symm) K)
    (b : ι → E → E →L[ℝ] E →L[ℝ] ℝ) (Ω : ι → Set E) (hΩ : ∀ j, IsOpen (Ω j))
    (hψΩ : ∀ j, (ψ j).source ⊆ Ω j) (hb : ∀ j, ContDiffOn ℝ (K - 1 : ℕ) (b j) (Ω j))
    (hbsymm : ∀ j, ∀ u ∈ Ω j, ∀ v w : E, b j u v w = b j u w v)
    (hbco : ∀ j, ∀ u ∈ Ω j, IsCoercive (b j u)) :
    letI := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
    ∀ (j : ι) (x : SmoothCarrier A), x ∈ (SmoothCarrier.chart A j).source → ∀ v u : E,
      coefficientSectional (coefficientPullback (b j) (κ j).symm) (SmoothCarrier.chart A j x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x u) =
        coefficientSectional (b j) ((ψ j).symm (SmoothCarrier.toBase A x))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u)) := by
  let _ : ChartedSpace E X := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
  have : IsManifold 𝓘(ℝ, E) K X := hM
  have : IsManifold 𝓘(ℝ, E) 1 X :=
    IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast (by omega : 1 ≤ K))
  intro j x hx v u
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hθ : SmoothCarrier.chart A j ∈ atlas E (SmoothCarrier A) := ⟨j, rfl⟩
  have hψm : (ψ j).symm ∈ atlas E X := ⟨j, rfl⟩
  have hx' := (SmoothCarrier.mem_chart_source_iff A j x).mp hx
  have hy : SmoothCarrier.chart A j x ∈ (ψ j).source := by
    rw [SmoothCarrier.chart_apply, ← htarget j]
    exact (A.chart j).map_source hx'
  rw [hchart j, OpenPartialHomeomorph.trans_source] at hx'
  have htb : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x :=
    ((SmoothCarrier.contMDiff_toBase A (fun j => (ψ j).symm) hcover hcomp) x).mdifferentiableAt
      hK0
  have hψd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x) :=
    mdifferentiableAt_atlas hψm hx'.1
  have hθd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x :=
    mdifferentiableAt_atlas hθ hx
  have hκd : DifferentiableAt ℝ (κ j).symm (SmoothCarrier.chart A j x) :=
    (hκ j).2.differentiable hK0 _
  have key := coefficientSectional_coefficientPullback_homeomorph (ψ j).open_source (hΩ j) hK
    (hb j) (hbsymm j) (hbco j) (hκ j).1 (hκ j).2
    ((mapsTo_homeomorph_symm_of_chart_eq (hchart j) (htarget j)).mono_right (hψΩ j)) hy
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x v)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x u)
  rw [← mfderiv_toBase_transport (hchart j) hψd htb hθd hκd v,
    ← mfderiv_toBase_transport (hchart j) hψd htb hθd hκd u,
    ← symm_toBase_eq_of_chart_eq (hchart j) x] at key
  exact key

private theorem linearIndependent_pair_of_injective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E →L[ℝ] E} (hf : Function.Injective f) {v u : E}
    (hvu : LinearIndependent ℝ ![v, u]) : LinearIndependent ℝ ![f v, f u] := by
  refine LinearIndependent.pair_iff.mpr fun s t hst => LinearIndependent.pair_iff.mp hvu s t ?_
  apply hf
  rw [map_add, map_smul, map_smul, map_zero]
  exact hst

private theorem span_pair_map_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →L[ℝ] E) {v u v' u' : E}
    (h : Submodule.span ℝ ({v', u'} : Set E) = Submodule.span ℝ ({v, u} : Set E)) :
    Submodule.span ℝ ({f v', f u'} : Set E) = Submodule.span ℝ ({f v, f u} : Set E) := by
  have h1 := congrArg (Submodule.map (f : E →ₗ[ℝ] E)) h
  rw [Submodule.map_span, Submodule.map_span, Set.image_pair, Set.image_pair] at h1
  exact h1

private theorem chart_mem_transition_source {E X ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MetricSpace X] (A : SmoothCompatibleAtlas E X ι) {j d : ι}
    {x : SmoothCarrier A} (hxj : x ∈ (SmoothCarrier.chart A j).source)
    (hxd : x ∈ (SmoothCarrier.chart A d).source) :
    SmoothCarrier.chart A j x ∈ ((A.chart j).symm.trans (A.chart d)).source := by
  have hxj' := (SmoothCarrier.mem_chart_source_iff A j x).mp hxj
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    SmoothCarrier.chart_apply]
  refine ⟨(A.chart j).map_source hxj', ?_⟩
  rw [Set.mem_preimage, (A.chart j).left_inv hxj']
  exact (SmoothCarrier.mem_chart_source_iff A d x).mp hxd

private theorem transition_apply_chart {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace X] (A : SmoothCompatibleAtlas E X ι) {j : ι} (d : ι) {x : SmoothCarrier A}
    (hxj : x ∈ (SmoothCarrier.chart A j).source) :
    ((A.chart j).symm.trans (A.chart d)) (SmoothCarrier.chart A j x) =
      SmoothCarrier.chart A d x := by
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, SmoothCarrier.chart_apply A j,
    SmoothCarrier.chart_apply A d,
    (A.chart j).left_inv ((SmoothCarrier.mem_chart_source_iff A j x).mp hxj)]

private theorem fderiv_transition_apply_chart {E X ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MetricSpace X] (A : SmoothCompatibleAtlas E X ι) {j d : ι}
    {x : SmoothCarrier A} (hxj : x ∈ (SmoothCarrier.chart A j).source)
    (hmem : SmoothCarrier.chart A j x ∈ ((A.chart j).symm.trans (A.chart d)).source) (w : E) :
    fderiv ℝ ((A.chart j).symm.trans (A.chart d)) (SmoothCarrier.chart A j x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x w) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A d) x w := by
  have hθ : SmoothCarrier.chart A j ∈ atlas E (SmoothCarrier A) := ⟨j, rfl⟩
  have hSd : DifferentiableAt ℝ ((A.chart j).symm.trans (A.chart d))
      (SmoothCarrier.chart A j x) :=
    ((A.contDiffOn_transition j d).contDiffAt
      (((A.chart j).symm.trans (A.chart d)).open_source.mem_nhds hmem)).differentiableAt
      (by decide)
  have hev : ⇑(SmoothCarrier.chart A d) =ᶠ[𝓝 x]
      ⇑((A.chart j).symm.trans (A.chart d)) ∘ ⇑(SmoothCarrier.chart A j) :=
    Filter.eventually_of_mem ((SmoothCarrier.chart A j).open_source.mem_nhds hxj) fun z hz =>
      (transition_apply_chart A d hz).symm
  have h := (hSd.hasFDerivAt.hasMFDerivAt.comp x
    (mdifferentiableAt_atlas (I := 𝓘(ℝ, E)) hθ hxj).hasMFDerivAt).congr_of_eventuallyEq_abuse hev
  exact (DFunLike.congr_fun h.mfderiv w).symm

theorem SmoothCarrier.coefficientSectional_transport_of_witnesses
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type*} [MetricSpace X] {ι : Type*} {K : ℕ} (hK : 3 ≤ K)
    (ψ : ι → OpenPartialHomeomorph E X) (hcover : ∀ x, ∃ j, x ∈ (ψ j).target)
    (hM : letI := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
      IsManifold 𝓘(ℝ, E) K X)
    (b : ι → E → E →L[ℝ] E →L[ℝ] ℝ) (Ω : ι → Set E) (hΩ : ∀ j, IsOpen (Ω j))
    (hψΩ : ∀ j, (ψ j).source ⊆ Ω j) (hb : ∀ j, ContDiffOn ℝ (K - 1 : ℕ) (b j) (Ω j))
    (hbsymm : ∀ j, ∀ u ∈ Ω j, ∀ v w : E, b j u v w = b j u w v)
    (hblow : ∀ j, ∀ u ∈ Ω j, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ b j u v v)
    (hlaw : ∀ (j d : ι) (u : E), u ∈ ((ψ j).symm.symm.trans (ψ d).symm).source →
      b j u = (b d (((ψ j).symm.symm.trans (ψ d).symm) u)).bilinearComp
        (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u)
        (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u))
    (htr : ∀ j d, ContDiffOn ℝ ((K - 1 + 1 : ℕ) : ℕ∞ω) ((ψ j).symm.symm.trans (ψ d).symm)
      ((ψ j).symm.symm.trans (ψ d).symm).source)
    (A : SmoothCompatibleAtlas E X ι) (κ : ι → E ≃ₜ E)
    (hchart : ∀ j, A.chart j = (ψ j).symm.trans (κ j).toOpenPartialHomeomorph)
    (htarget : ∀ j, (A.chart j).target = (ψ j).source)
    (hκ : ∀ j, ContDiff ℝ K (κ j) ∧ ContDiff ℝ K (κ j).symm)
    (hcomp : A.IsCompatible (fun j => (ψ j).symm) K) :
    letI := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
    letI := hM
    letI : IsManifold 𝓘(ℝ, E) 1 X :=
      IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast (by omega : 1 ≤ K))
    ∀ (G : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
        (TangentSpace 𝓘(ℝ, E) : X → Type _))
      (G' : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
        (TangentSpace 𝓘(ℝ, E) : SmoothCarrier A → Type _)),
      (∀ j x, x ∈ (ψ j).symm.source → ∀ v w : E,
        G.inner x v w = b j ((ψ j).symm x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm x v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm x w)) →
      (∀ (x : SmoothCarrier A) (v w : E),
        G'.inner x v w = G.inner (SmoothCarrier.toBase A x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x w)) →
      ∀ j : ι,
        (∀ y ∈ (ψ j).source, ∀ w₁ w₂ : E,
          G'.inner ((SmoothCarrier.chart A j).symm y)
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j).symm y w₁)
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j).symm y w₂) =
            coefficientPullback (b j) (κ j).symm y w₁ w₂) ∧
        ∀ x : SmoothCarrier A, x ∈ (SmoothCarrier.chart A j).source →
          (∀ w₁ w₂ : E,
            G'.inner x w₁ w₂ =
              coefficientPullback (b j) (κ j).symm (SmoothCarrier.chart A j x)
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x w₁)
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x w₂)) ∧
          (∀ w₁ w₂ : E,
            G.inner (SmoothCarrier.toBase A x) w₁ w₂ =
              b j ((ψ j).symm (SmoothCarrier.toBase A x))
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x) w₁)
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x) w₂)) ∧
          Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x) ∧
          ∀ v u : E, LinearIndependent ℝ ![v, u] →
            LinearIndependent ℝ
              (![mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v,
                mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u] : Fin 2 → E) ∧
            0 < G'.inner x v v * G'.inner x u u - (G'.inner x v u) ^ 2 ∧
            0 < G.inner (SmoothCarrier.toBase A x)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v) *
                G.inner (SmoothCarrier.toBase A x)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u) -
                (G.inner (SmoothCarrier.toBase A x)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u)) ^ 2 ∧
            G'.inner x v v * G'.inner x u u - (G'.inner x v u) ^ 2 =
              G.inner (SmoothCarrier.toBase A x)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v) *
                G.inner (SmoothCarrier.toBase A x)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u) -
                (G.inner (SmoothCarrier.toBase A x)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u)) ^ 2 ∧
            coefficientSectional (coefficientPullback (b j) (κ j).symm)
                (SmoothCarrier.chart A j x)
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x v)
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x u) =
              coefficientSectional (b j) ((ψ j).symm (SmoothCarrier.toBase A x))
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v))
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u)) ∧
            (∀ d : ι, x ∈ (SmoothCarrier.chart A d).source →
              coefficientSectional (coefficientPullback (b d) (κ d).symm)
                  (SmoothCarrier.chart A d x)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A d) x v)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A d) x u) =
                coefficientSectional (coefficientPullback (b j) (κ j).symm)
                  (SmoothCarrier.chart A j x)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x v)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x u) ∧
              coefficientSectional (b d) ((ψ d).symm (SmoothCarrier.toBase A x))
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ d).symm (SmoothCarrier.toBase A x)
                    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v))
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ d).symm (SmoothCarrier.toBase A x)
                    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u)) =
                coefficientSectional (b j) ((ψ j).symm (SmoothCarrier.toBase A x))
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x)
                    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v))
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x)
                    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u))) ∧
            ∀ v' u' : E,
              Submodule.span ℝ ({v', u'} : Set E) = Submodule.span ℝ ({v, u} : Set E) →
              LinearIndependent ℝ ![v', u'] ∧
              coefficientSectional (coefficientPullback (b j) (κ j).symm)
                  (SmoothCarrier.chart A j x)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x v')
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x u') =
                coefficientSectional (coefficientPullback (b j) (κ j).symm)
                  (SmoothCarrier.chart A j x)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x v)
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x u) ∧
              coefficientSectional (b j) ((ψ j).symm (SmoothCarrier.toBase A x))
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x)
                    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v'))
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x)
                    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u')) =
                coefficientSectional (b j) ((ψ j).symm (SmoothCarrier.toBase A x))
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x)
                    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x v))
                  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x)
                    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x u)) := by
  let _ : ChartedSpace E X := chartedSpaceOfOpenCover (fun j => (ψ j).symm) hcover
  have : IsManifold 𝓘(ℝ, E) K X := hM
  have : IsManifold 𝓘(ℝ, E) 1 X :=
    IsManifold.of_le (n := (K : ℕ∞ω)) (by exact_mod_cast (by omega : 1 ≤ K))
  intro G G' hG hG' j
  have hK1 : 1 ≤ K := by omega
  have hleft := SmoothCarrier.mfderiv_ofBase_comp_mfderiv_toBase A (fun j => (ψ j).symm) hcover
    hK1 hcomp
  have hright := SmoothCarrier.mfderiv_toBase_comp_mfderiv_ofBase A (fun j => (ψ j).symm) hcover
    hK1 hcomp
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 := two_le_cast_pred hK
  have h3 : (3 : ℕ∞ω) ≤ ((K - 1 + 1 : ℕ) : ℕ∞ω) := by
    exact_mod_cast (by omega : 3 ≤ K - 1 + 1)
  have hbco : ∀ d, ∀ u ∈ Ω d, IsCoercive (b d u) := fun d u hu =>
    isCoercive_of_half_sq_le (hblow d u hu)
  have hB7 := SmoothCarrier.coefficientSectional_chart_eq hK ψ hcover hM A κ hchart htarget hκ
    hcomp b Ω hΩ hψΩ hb hbsymm hbco
  have hθ : SmoothCarrier.chart A j ∈ atlas E (SmoothCarrier A) := ⟨j, rfl⟩
  have hmaps : MapsTo (κ j).symm (ψ j).source (Ω j) :=
    (mapsTo_homeomorph_symm_of_chart_eq (hchart j) (htarget j)).mono_right (hψΩ j)
  have hinvκ : ∀ z ∈ (ψ j).source, (fderiv ℝ (κ j).symm z).IsInvertible := fun z _ =>
    isInvertible_fderiv_homeomorph_symm hK0 (hκ j).1 (hκ j).2 z
  refine ⟨SmoothCarrier.inner_chart_symm_eq_coefficientPullback hK1 ψ hcover hM A κ hchart htarget
    hcomp b G G' hG hG' j, fun x hx => ?_⟩
  have hx' := (SmoothCarrier.mem_chart_source_iff A j x).mp hx
  have hy : SmoothCarrier.chart A j x ∈ (ψ j).source := by
    rw [SmoothCarrier.chart_apply, ← htarget j]
    exact (A.chart j).map_source hx'
  have hq : SmoothCarrier.toBase A x ∈ (ψ j).symm.source := by
    rw [hchart j, OpenPartialHomeomorph.trans_source] at hx'
    exact hx'.1
  have htb : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x :=
    ((SmoothCarrier.contMDiff_toBase A (fun j => (ψ j).symm) hcover hcomp) x).mdifferentiableAt
      hK0
  have hψd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm (SmoothCarrier.toBase A x) :=
    mdifferentiableAt_atlas (⟨j, rfl⟩ : (ψ j).symm ∈ atlas E X) hq
  have hθd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x :=
    mdifferentiableAt_atlas hθ hx
  have hT := mfderiv_toBase_transport (hchart j) hψd htb hθd
    ((hκ j).2.differentiable hK0 _)
  have hpt := symm_toBase_eq_of_chart_eq (hchart j) x
  have hlinvx : Function.LeftInverse
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) (SmoothCarrier.toBase A x))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x) := fun a =>
    DFunLike.congr_fun (hleft x) a
  have hrinvx : Function.RightInverse
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) (SmoothCarrier.toBase A x))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x) := by
    intro w
    have h : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A)
        (SmoothCarrier.ofBase A (SmoothCarrier.toBase A x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.ofBase A) (SmoothCarrier.toBase A x) w) = w :=
      DFunLike.congr_fun (hright (SmoothCarrier.toBase A x)) w
    rw [SmoothCarrier.ofBase_toBase] at h
    exact h
  have hθli : Function.LeftInverse
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j).symm (SmoothCarrier.chart A j x))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x) := fun a =>
    DFunLike.congr_fun ((mdifferentiable_of_mem_atlas (I := 𝓘(ℝ, E)) hθ).symm_comp_deriv hx) a
  refine ⟨fun w₁ w₂ => ?_, fun w₁ w₂ => hG j _ hq w₁ w₂,
    ⟨hlinvx.injective, hrinvx.surjective⟩, fun v u hvu => ?_⟩
  · rw [coefficientPullback_apply (b j) (κ j).symm (SmoothCarrier.chart A j x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x w₁)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x w₂), ← hT w₁, ← hT w₂, ← hpt]
    exact (hG' x w₁ w₂).trans (hG j _ hq _ _)
  have hGco := ContinuousLinearMap.isCoercive_of_posDef (F := E) (G'.inner x) fun a ha =>
    G'.pos x a ha
  have hpos := bilin_gram_pos_of_linearIndependent (E := E) (B := G'.inner x)
    (fun a c => G'.symm x a c) hGco hvu
  refine ⟨linearIndependent_pair_of_injective (E := E)
      (f := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase A) x) hlinvx.injective hvu,
    hpos, ?_, ?_, hB7 j x hx v u, fun d hxd => ?_, fun v' u' hspan => ?_⟩
  · rw [← hG' x v v, ← hG' x u u, ← hG' x v u]
    exact hpos
  · rw [hG' x v v, hG' x u u, hG' x v u]
  · have hmem := chart_mem_transition_source A hx hxd
    have hcar := coefficientSectional_carrier_chart_transition ψ b Ω hΩ hψΩ
      (fun i => (hb i).of_le h2) hbsymm hbco (fun i k => (htr i k).of_le h3) hlaw hK A κ hchart
      htarget hκ j d hmem (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x u)
    rw [transition_apply_chart A d hx, fderiv_transition_apply_chart A hx hmem v,
      fderiv_transition_apply_chart A hx hmem u] at hcar
    exact ⟨hcar.symm, (hB7 d x hxd v u).symm.trans (hcar.symm.trans (hB7 j x hx v u))⟩
  · have hvu' := linearIndependent_pair_of_span_eq hvu hspan.symm
    have hcd : ContDiffAt ℝ 2 (coefficientPullback (b j) (κ j).symm)
        (SmoothCarrier.chart A j x) :=
      ((contDiffOn_coefficientPullback_homeomorph_symm (ψ j).open_source hK1 (hb j)
        (hκ j).2 hmaps).contDiffAt ((ψ j).open_source.mem_nhds hy)).of_le h2
    have hcar := coefficientSectional_eq_of_span_eq hcd
      (Filter.eventually_of_mem ((ψ j).open_source.mem_nhds hy)
        (coefficientPullback_symm (hbsymm j) hmaps))
      (isCoercive_coefficientPullback (hbco j) hmaps hinvκ _ hy)
      (linearIndependent_pair_of_injective (E := E)
        (f := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x) hθli.injective hvu')
      (span_pair_map_eq (E := E) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.chart A j) x) hspan)
    exact ⟨hvu', hcar, (hB7 j x hx v' u').symm.trans (hcar.trans (hB7 j x hx v u))⟩

end DifferentialGeometry.Topology.Manifold
