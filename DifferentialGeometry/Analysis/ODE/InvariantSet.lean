import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.ODE.Basic

open Filter Set
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def VectorFieldTangentTo (f : ℝ → E → E) (C : Set E) : Prop :=
  ∀ t x, x ∈ C → f t x ∈ posTangentConeAt C x

def IsForwardInvariantForODE (f : ℝ → E → E) (C : Set E) : Prop :=
  ∀ a b, a ≤ b → ∀ γ : ℝ → E,
    IsIntegralCurveOn γ f (Icc a b) → γ a ∈ C → MapsTo γ (Icc a b) C

def IsForwardInvariantForODEOn (f : ℝ → E → E) (C : Set E) (J : Set ℝ) : Prop :=
  ∀ a b, a ≤ b → Icc a b ⊆ J → ∀ γ : ℝ → E,
    IsIntegralCurveOn γ f (Icc a b) → γ a ∈ C → MapsTo γ (Icc a b) C

@[simp] theorem isForwardInvariantForODEOn_univ {f : ℝ → E → E} {C : Set E} :
    IsForwardInvariantForODEOn f C univ ↔ IsForwardInvariantForODE f C := by
  constructor
  · exact fun h a b hab γ hγ hinit => h a b hab (subset_univ _) γ hγ hinit
  · exact fun h a b hab _ γ hγ hinit => h a b hab γ hγ hinit

theorem IsForwardInvariantForODEOn.mono {f : ℝ → E → E} {C : Set E} {J K : Set ℝ}
    (h : IsForwardInvariantForODEOn f C J) (hKJ : K ⊆ J) :
    IsForwardInvariantForODEOn f C K :=
  fun a b hab hsub γ hγ hinit => h a b hab (hsub.trans hKJ) γ hγ hinit


theorem HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right
    {γ : ℝ → E} {t : ℝ} {v : E} {C : Set E}
    (hγ : HasDerivAt γ v t) (hC : ∀ᶠ h in 𝓝[>] (0 : ℝ), γ (t + h) ∈ C) :
    v ∈ posTangentConeAt C (γ t) := by
  let c : ℝ → ℝ≥0 := fun h ↦ ⟨max h⁻¹ 0, le_max_right _ _⟩
  let d : ℝ → E := fun h ↦ γ (t + h) - γ t
  refine mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) c d ?_ ?_ ?_
  · have htadd : Tendsto (fun h : ℝ ↦ t + h) (𝓝[>] (0 : ℝ)) (𝓝 t) := by
      simpa using
        (tendsto_const_nhds.add tendsto_id).mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    simpa [d, Function.comp_def] using
      (hγ.continuousAt.tendsto.comp htadd).sub_const (γ t)
  · filter_upwards [hC] with h hh
    simpa [d] using hh
  · apply Tendsto.congr' _ hγ.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := hh
    rw [NNReal.smul_def]
    simp [c, d, max_eq_left (inv_nonneg.mpr hpos.le)]
    congr 1

theorem IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_right
    {f : ℝ → E → E} {γ : ℝ → E} {t : ℝ} {C : Set E}
    (hγ : IsIntegralCurve γ f) (hC : MapsTo γ (Ici t) C) :
    f t (γ t) ∈ posTangentConeAt C (γ t) := by
  apply HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right (hγ t)
  filter_upwards [self_mem_nhdsWithin] with h hh
  apply hC
  change t ≤ t + h
  exact le_add_of_nonneg_right hh.le

theorem IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_Icc
    {f : ℝ → E → E} {γ : ℝ → E} {a b : ℝ} {C : Set E}
    (hγ : IsIntegralCurve γ f) (hab : a < b) (hC : MapsTo γ (Icc a b) C) :
    f a (γ a) ∈ posTangentConeAt C (γ a) := by
  apply HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right (hγ a)
  have hb : Iio (b - a) ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds (sub_pos.mpr hab)
  have hb' : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Iio (b - a) :=
    Filter.Eventually.filter_mono inf_le_left hb
  filter_upwards [self_mem_nhdsWithin, hb'] with h hpos hlt
  apply hC
  constructor
  · exact le_add_of_nonneg_right hpos.le
  · have hlt' : h < b - a := hlt
    linarith

theorem HasDerivWithinAt.mem_posTangentConeAt_of_eventually_mem_right
    {γ : ℝ → E} {t : ℝ} {v : E} {C : Set E}
    (hγ : HasDerivWithinAt γ v (Ici t) t)
    (hC : ∀ᶠ s in 𝓝[>] t, γ s ∈ C) :
    v ∈ posTangentConeAt C (γ t) := by
  let c : ℝ → ℝ≥0 := fun s ↦ ⟨max (s - t)⁻¹ 0, le_max_right _ _⟩
  let d : ℝ → E := fun s ↦ γ s - γ t
  refine mem_tangentConeAt_of_seq (𝓝[>] t) c d ?_ ?_ ?_
  · simpa only [sub_self] using
      (hγ.continuousWithinAt.tendsto.mono_left
        (nhdsWithin_mono t Ioi_subset_Ici_self)).sub_const (γ t)
  · filter_upwards [hC] with s hs
    simpa [d] using hs
  · have hslope : Tendsto (slope γ t) (𝓝[>] t) (𝓝 v) := by
      have heq : Ici t \ {t} = Ioi t := by
        ext s
        simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
        constructor
        · exact fun h => lt_of_le_of_ne h.1 (Ne.symm h.2)
        · exact fun h => ⟨h.le, ne_of_gt h⟩
      simpa only [heq] using (hasDerivWithinAt_iff_tendsto_slope.mp hγ)
    apply Tendsto.congr' _ hslope
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : 0 < s - t := sub_pos.mpr hs
    rw [NNReal.smul_def]
    simp [c, d, slope, max_eq_left (inv_nonneg.mpr hst.le)]
    rfl

theorem IsIntegralCurveOn.mem_posTangentConeAt_of_mapsTo_Icc
    {f : ℝ → E → E} {γ : ℝ → E} {a b : ℝ} {C : Set E}
    (hγ : IsIntegralCurveOn γ f (Icc a b)) (hab : a < b)
    (hC : MapsTo γ (Icc a b) C) :
    f a (γ a) ∈ posTangentConeAt C (γ a) := by
  apply HasDerivWithinAt.mem_posTangentConeAt_of_eventually_mem_right
    ((hγ a ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem (show a ∈ Ico a b from ⟨le_rfl, hab⟩)))
  have hb : ∀ᶠ s in 𝓝[>] a, s < b :=
    Filter.Eventually.filter_mono inf_le_left
      (isOpen_Iio.mem_nhds (show a ∈ Iio b from hab))
  filter_upwards [self_mem_nhdsWithin, hb] with s hsa hsb
  exact hC ⟨hsa.le, hsb.le⟩

theorem IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurveAt
    {f : ℝ → E → E} {C : Set E} (hC : IsForwardInvariantForODE f C)
    (hex : ∀ t x, x ∈ C → ∃ γ : ℝ → E, IsIntegralCurveAt γ f t ∧ γ t = x) :
    VectorFieldTangentTo f C := by
  intro t x hx
  obtain ⟨γ, hγ, hγt⟩ := hex t x hx
  obtain ⟨ε, hε, hγBall⟩ := isIntegralCurveAt_iff_exists_pos.mp hγ
  have hinterval : Icc t (t + ε / 2) ⊆ Metric.ball t ε := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    linarith [hs.2]
  have hγIcc := hγBall.mono hinterval
  have hmap : MapsTo γ (Icc t (t + ε / 2)) C :=
    hC t (t + ε / 2) (by linarith) γ hγIcc (hγt.symm ▸ hx)
  simpa [hγt] using
    IsIntegralCurveOn.mem_posTangentConeAt_of_mapsTo_Icc hγIcc (by linarith) hmap


theorem IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurve
    {f : ℝ → E → E} {C : Set E} (hC : IsForwardInvariantForODE f C)
    (hex : ∀ t x, ∃ γ : ℝ → E, IsIntegralCurve γ f ∧ γ t = x) :
    VectorFieldTangentTo f C := by
  apply hC.vectorFieldTangentTo_of_exists_isIntegralCurveAt
  intro t x _
  obtain ⟨γ, hγ, hγt⟩ := hex t x
  exact ⟨γ, hγ.isIntegralCurveAt t, hγt⟩

theorem IsForwardInvariantForODE.inter
    {f : ℝ → E → E} {C D : Set E}
    (hC : IsForwardInvariantForODE f C) (hD : IsForwardInvariantForODE f D) :
    IsForwardInvariantForODE f (C ∩ D) := by
  intro a b hab γ hγ hγab
  exact (hC a b hab γ hγ hγab.1).inter (hD a b hab γ hγ hγab.2)

theorem isForwardInvariantForODE_univ (f : ℝ → E → E) :
    IsForwardInvariantForODE f univ := by
  intro a b hab γ hγ ha
  exact mapsTo_univ γ _

theorem Convex.vectorFieldTangentTo_of_sub_mem
    {f : ℝ → E → E} {C : Set E} (hC : Convex ℝ C)
    (hf : ∀ t x, x ∈ C → ∃ y ∈ C, f t x = y - x) :
    VectorFieldTangentTo f C := by
  intro t x hx
  obtain ⟨y, hy, hfy⟩ := hf t x hx
  rw [hfy]
  exact sub_mem_posTangentConeAt_of_segment_subset (hC.segment_subset hx hy)

theorem ConvexCone.vectorFieldTangentTo_of_mapsTo
    (C : ConvexCone ℝ E) {f : ℝ → E → E}
    (hf : ∀ t, MapsTo (f t) C C) :
    VectorFieldTangentTo f C := by
  apply Convex.vectorFieldTangentTo_of_sub_mem C.convex
  intro t x hx
  refine ⟨x + f t x, C.add_mem hx (hf t hx), ?_⟩
  abel

theorem ProperCone.vectorFieldTangentTo_of_mapsTo
    (C : ProperCone ℝ E) {f : ℝ → E → E}
    (hf : ∀ t, MapsTo (f t) C C) :
    VectorFieldTangentTo f C := by
  apply Convex.vectorFieldTangentTo_of_sub_mem C.convex
  intro t x hx
  refine ⟨x + f t x, C.add_mem hx (hf t hx), ?_⟩
  abel

end DifferentialGeometry.Analysis.ODE
