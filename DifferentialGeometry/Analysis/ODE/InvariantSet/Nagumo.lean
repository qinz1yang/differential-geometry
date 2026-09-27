import DifferentialGeometry.Analysis.ODE.InvariantSet.Basic
import DifferentialGeometry.Analysis.ODE.InvariantSet.Naturality
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.ODE.Gronwall

open Filter Set
open scoped Topology NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem Convex.real_inner_sub_nonpos_of_norm_eq_iInf_of_mem_posTangentConeAt
    {C : Set E} (hC : Convex ℝ C) {x p v : E} (hp : p ∈ C)
    (hmin : ‖x - p‖ = ⨅ y : C, ‖x - y‖) (hv : v ∈ posTangentConeAt C p) :
    inner ℝ (x - p) v ≤ 0 := by
  have hnormal : ∀ y ∈ C, inner ℝ (x - p) (y - p) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hC hp).mp hmin
  have hmax : IsMaxOn (fun y : E ↦ inner ℝ (x - p) y) C p := by
    intro y hy
    have := hnormal y hy
    rw [inner_sub_right] at this
    exact sub_nonpos.mp this
  have hderiv : HasFDerivAt (fun y : E ↦ inner ℝ (x - p) y) (innerSL ℝ (x - p)) p := by
    change HasFDerivAt (innerSL ℝ (x - p)) (innerSL ℝ (x - p)) p
    exact (innerSL ℝ (x - p)).hasFDerivAt
  exact hmax.localize.hasFDerivWithinAt_nonpos hderiv.hasFDerivWithinAt hv

theorem frequently_slope_lt_of_le_of_eq_of_hasDerivWithinAt_right
    {g q : ℝ → ℝ} {t q' : ℝ} (hgq : ∀ s, g s ≤ q s) (heq : g t = q t)
    (hq : HasDerivWithinAt q q' (Ici t) t) :
    ∀ r, q' < r → ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (g z - g t) < r := by
  intro r hr
  refine ((hq.liminf_right_slope_le hr).and_eventually self_mem_nhdsWithin).mono ?_
  intro z hz
  rw [slope, vsub_eq_sub] at hz
  have hzt : 0 < z - t := sub_pos.mpr hz.2
  have hdiff : g z - g t ≤ q z - q t := by rw [heq]; linarith [hgq z]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hzt.le)) hz.1

theorem nagumo_mapsTo_of_lipschitzOn_closedBall [CompleteSpace E]
    {f : ℝ → E → E} {C : Set E} {a b : ℝ} {γ : ℝ → E} {p₀ : E} {R : ℝ}
    (hp₀ : p₀ ∈ C) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (htangent : ∀ t ∈ Ico a b, ∀ x ∈ C, f t x ∈ posTangentConeAt C x) (L : ℝ≥0)
    (hL : ∀ t ∈ Ico a b, LipschitzOnWith L (f t) (Metric.closedBall p₀ (2 * R)))
    (hγ : IsIntegralCurveOn γ f (Icc a b))
    (hbound : MapsTo γ (Icc a b) (Metric.closedBall p₀ R)) (ha : γ a ∈ C) :
    MapsTo γ (Icc a b) C := by
  intro t ht
  let g : ℝ → ℝ := fun s ↦ Metric.infDist (γ s) C ^ 2
  have hgcont : ContinuousOn g (Icc a b) := by
    exact ((Metric.continuous_infDist_pt C).comp_continuousOn hγ.continuousOn).pow 2
  have hgslope :
      ∀ x ∈ Ico a b, ∀ r,
        2 * (L : ℝ) * g x < r →
          ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (g z - g x) < r := by
    intro x hx
    obtain ⟨p, hp, hmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex ⟨p₀, hp₀⟩ hclosed.isComplete hconvex (γ x)
    let q : ℝ → ℝ := fun s ↦ ‖γ s - p‖ ^ 2
    have hγright : HasDerivWithinAt γ (f x (γ x)) (Ici x) x :=
      (hγ x (mem_Icc_of_Ico hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
    have hq : HasDerivWithinAt q (2 * inner ℝ (γ x - p) (f x (γ x))) (Ici x) x := by
      simpa [q] using (hγright.sub_const p).norm_sq
    have hgq : ∀ s, g s ≤ q s := by
      intro s
      have hle : Metric.infDist (γ s) C ≤ ‖γ s - p‖ := by
        simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := γ s) hp
      exact (sq_le_sq₀ Metric.infDist_nonneg (norm_nonneg _)).mpr hle
    have hdist : Metric.infDist (γ x) C = ‖γ x - p‖ := by
      rw [Metric.infDist_eq_iInf]
      simpa [dist_eq_norm] using hmin.symm
    have heq : g x = q x := by simp [g, q, hdist]
    have hnormal : inner ℝ (γ x - p) (f x p) ≤ 0 :=
      Convex.real_inner_sub_nonpos_of_norm_eq_iInf_of_mem_posTangentConeAt
        hconvex hp hmin (htangent x hx p hp)
    have hγR : dist (γ x) p₀ ≤ R := hbound (mem_Icc_of_Ico hx)
    have hR : 0 ≤ R := dist_nonneg.trans hγR
    have hpR : dist p p₀ ≤ 2 * R := by
      have hnear : dist (γ x) p ≤ dist (γ x) p₀ := by
        rw [dist_eq_norm, ← hdist]
        exact Metric.infDist_le_dist_of_mem hp₀
      calc
        dist p p₀ ≤ dist p (γ x) + dist (γ x) p₀ := dist_triangle _ _ _
        _ ≤ 2 * R := by rw [dist_comm p]; linarith
    have hLip : ‖f x (γ x) - f x p‖ ≤ (L : ℝ) * ‖γ x - p‖ :=
      (hL x hx).norm_sub_le (by change dist (γ x) p₀ ≤ 2 * R; linarith) hpR
    have hinner :
        inner ℝ (γ x - p) (f x (γ x) - f x p) ≤
          ‖γ x - p‖ * ‖f x (γ x) - f x p‖ :=
      real_inner_le_norm _ _
    have hqbound :
        2 * inner ℝ (γ x - p) (f x (γ x)) ≤ 2 * (L : ℝ) * g x := by
      change
        2 * inner ℝ (γ x - p) (f x (γ x)) ≤
          2 * (L : ℝ) * Metric.infDist (γ x) C ^ 2
      rw [hdist]
      have hnorm : 0 ≤ ‖γ x - p‖ := norm_nonneg _
      have hLnonneg : 0 ≤ (L : ℝ) := L.coe_nonneg
      rw [inner_sub_right] at hinner
      nlinarith [sq_nonneg ‖γ x - p‖]
    intro r hr
    exact frequently_slope_lt_of_le_of_eq_of_hasDerivWithinAt_right hgq heq hq r
      (lt_of_le_of_lt hqbound hr)
  have hga : g a ≤ 0 := by simp [g, Metric.infDist_zero_of_mem ha]
  have hbound' : ∀ x ∈ Ico a b, 2 * (L : ℝ) * g x ≤ (2 * (L : ℝ)) * g x + 0 := by
    intro x _
    ring_nf
    exact le_rfl
  have hgronwall :=
    le_gronwallBound_of_liminf_deriv_right_le hgcont hgslope hga hbound' t ht
  have hgle : g t ≤ 0 := by
    simpa [gronwallBound_ε0_δ0] using hgronwall
  have hge : 0 ≤ g t := by simp [g, sq_nonneg]
  have hgt : g t = 0 := le_antisymm hgle hge
  have hinf : Metric.infDist (γ t) C = 0 := by
    have : Metric.infDist (γ t) C ^ 2 = 0 := by simpa [g] using hgt
    exact sq_eq_zero_iff.mp this
  exact (hclosed.mem_iff_infDist_zero ⟨p₀, hp₀⟩).mpr hinf

theorem nagumo_mapsTo_of_lipschitz [CompleteSpace E]
    {f : ℝ → E → E} {C : Set E} {a b : ℝ} {γ : ℝ → E}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (htangent : VectorFieldTangentTo f C) (L : ℝ≥0)
    (hL : ∀ t ∈ Ico a b, LipschitzWith L (f t))
    (hγ : IsIntegralCurveOn γ f (Icc a b)) (ha : γ a ∈ C) :
    MapsTo γ (Icc a b) C := by
  obtain ⟨p₀, hp₀⟩ := hne
  have hdiff : ContinuousOn (fun t => γ t - p₀) (Icc a b) :=
    hγ.continuousOn.sub continuousOn_const
  obtain ⟨R, _, hbound⟩ :=
    (isCompact_Icc.image_of_continuousOn hdiff).isBounded.exists_pos_norm_le
  apply nagumo_mapsTo_of_lipschitzOn_closedBall (R := R) hp₀ hclosed hconvex
    (fun t _ => htangent t) L
    (fun t ht => (hL t ht).lipschitzOnWith) hγ ?_ ha
  intro t ht
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact hbound _ ⟨t, ht, rfl⟩

private theorem nagumo_mapsTo_of_contDiffOn_inner [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {C : Set E} {a b : ℝ} {γ : ℝ → E}
    (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (htangent : ∀ t ∈ Ico a b, ∀ x ∈ C, f t x ∈ posTangentConeAt C x)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (Icc a b ×ˢ (univ : Set E)))
    (hγ : IsIntegralCurveOn γ f (Icc a b)) (ha : γ a ∈ C) :
    MapsTo γ (Icc a b) C := by
  have hdiff : ContinuousOn (fun t => γ t - γ a) (Icc a b) :=
    hγ.continuousOn.sub continuousOn_const
  obtain ⟨R, _, hbound⟩ :=
    (isCompact_Icc.image_of_continuousOn hdiff).isBounded.exists_pos_norm_le
  have hγbound : MapsTo γ (Icc a b) (Metric.closedBall (γ a) R) := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hbound _ ⟨t, ht, rfl⟩
  have hfBall := hf.mono
    (Set.prod_mono (Set.Subset.refl (Icc a b))
      (Set.subset_univ (Metric.closedBall (γ a) (2 * R))))
  obtain ⟨L, hL⟩ := hfBall.exists_lipschitzOnWith one_ne_zero
    ((convex_Icc a b).prod (convex_closedBall (γ a) (2 * R)))
    (isCompact_Icc.prod (isCompact_closedBall (γ a) (2 * R)))
  apply nagumo_mapsTo_of_lipschitzOn_closedBall ha hclosed hconvex htangent L
    (fun t ht => ?_) hγ hγbound ha
  intro x hx y hy
  simpa [Prod.edist_eq] using
    hL (x := (t, x)) ⟨mem_Icc_of_Ico ht, hx⟩
      (y := (t, y)) ⟨mem_Icc_of_Ico ht, hy⟩

theorem nagumo_mapsTo_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {C : Set E} {a b : ℝ} {γ : ℝ → E}
    (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (htangent : ∀ t ∈ Ico a b, ∀ x ∈ C, f t x ∈ posTangentConeAt C x)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (Icc a b ×ˢ (univ : Set E)))
    (hγ : IsIntegralCurveOn γ f (Icc a b)) (ha : γ a ∈ C) :
    MapsTo γ (Icc a b) C := by
  let e := toEuclidean (E := E)
  have hclosed' : IsClosed (e '' C) := e.toHomeomorph.isClosedMap _ hclosed
  have hconvex' : Convex ℝ (e '' C) := hconvex.linear_image e.toLinearEquiv.toLinearMap
  have htangent' : ∀ t ∈ Ico a b, ∀ y ∈ e '' C,
      pushForwardVectorField e f t y ∈ posTangentConeAt (e '' C) y := by
    intro t ht y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using ContinuousLinearEquiv.mapsTo_posTangentConeAt e (htangent t ht x hx)
  have hf' : ContDiffOn ℝ 1 (Function.uncurry (pushForwardVectorField e f))
      (Icc a b ×ˢ univ) := by
    apply e.contDiff.comp_contDiffOn
    apply hf.comp
      (contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd)).contDiffOn
    exact fun p hp => ⟨hp.1, mem_univ _⟩
  have hmap := nagumo_mapsTo_of_contDiffOn_inner hclosed' hconvex' htangent' hf'
    (IsIntegralCurveOn.pushForwardVectorField hγ e) ⟨γ a, ha, rfl⟩
  intro t ht
  obtain ⟨x, hx, heq⟩ := hmap ht
  rwa [e.injective heq] at hx

theorem nagumo_isForwardInvariantForODE_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {C : Set E} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (htangent : VectorFieldTangentTo f C)
    (hf : ContDiff ℝ 1 (Function.uncurry f)) :
    IsForwardInvariantForODE f C := by
  intro a b _ γ hγ ha
  exact nagumo_mapsTo_of_contDiffOn hclosed hconvex
    (fun t _ => htangent t) hf.contDiffOn hγ ha

theorem nagumo_isForwardInvariantForODE_of_lipschitz [CompleteSpace E]
    {f : ℝ → E → E} {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconvex : Convex ℝ C) (htangent : VectorFieldTangentTo f C) (L : ℝ≥0)
    (hL : ∀ t, LipschitzWith L (f t)) :
    IsForwardInvariantForODE f C := by
  intro a b _ γ hγ ha
  exact nagumo_mapsTo_of_lipschitz hne hclosed hconvex htangent L
    (fun t _ ↦ hL t) hγ ha

theorem nagumo_convexCone_isForwardInvariantForODE_of_mapsTo [CompleteSpace E]
    (C : ConvexCone ℝ E) (hne : (C : Set E).Nonempty) (hclosed : IsClosed (C : Set E))
    {f : ℝ → E → E} (L : ℝ≥0) (hL : ∀ t, LipschitzWith L (f t))
    (hf : ∀ t, MapsTo (f t) C C) :
    IsForwardInvariantForODE f C :=
  nagumo_isForwardInvariantForODE_of_lipschitz
    hne hclosed C.convex
      (ConvexCone.vectorFieldTangentTo_of_mapsTo C hf) L hL

theorem nagumo_properCone_isForwardInvariantForODE_of_mapsTo [CompleteSpace E]
    (C : ProperCone ℝ E) {f : ℝ → E → E} (L : ℝ≥0)
    (hL : ∀ t, LipschitzWith L (f t)) (hf : ∀ t, MapsTo (f t) C C) :
    IsForwardInvariantForODE f C :=
  nagumo_isForwardInvariantForODE_of_lipschitz
    C.nonempty C.isClosed C.convex
      (ProperCone.vectorFieldTangentTo_of_mapsTo C hf) L hL

end DifferentialGeometry.Analysis.ODE
