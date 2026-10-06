import DifferentialGeometry.Geometry.MinimalSurface.Variation.TransverseSeamFlux
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.MeanCurvatureReparametrization
import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] in
private theorem eventually_ne_of_injective_mfderivWithin
    {F : ℂ → M} {H : Set ℂ} {x : ℂ}
    (hF : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H x)
    (hi : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H x)) :
    ∀ᶠ z in 𝓝[H \ {x}] x, F z ≠ F x := by
  let A : ℂ →L[ℝ] E :=
    (tangentSpaceCastModel 𝓘(ℝ, E) (F x)).toContinuousLinearMap ∘L
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H x ∘L
      (tangentSpaceCastModel 𝓘(ℝ, ℂ) x).symm.toContinuousLinearMap
  have hd : HasFDerivWithinAt (fun z => extChartAt 𝓘(ℝ, E) (F x) (F z)) A H x := by
    simpa only [A, writtenInExtChartAt, mfld_simps] using! hF.hasMFDerivWithinAt.2
  have hA : Function.Injective A :=
    (tangentSpaceCastModel 𝓘(ℝ, E) (F x)).injective.comp
      (hi.comp (tangentSpaceCastModel 𝓘(ℝ, ℂ) x).symm.injective)
  obtain ⟨K, _, hK⟩ := A.toLinearMap.injective_iff_antilipschitz.mp hA
  have hn : ∀ᶠ z in 𝓝[H \ {x}] x,
      extChartAt 𝓘(ℝ, E) (F x) (F z) ≠ extChartAt 𝓘(ℝ, E) (F x) (F x) :=
    hd.eventually_ne ⟨K, hK⟩
  exact hn.mono (fun z hz h => hz (congrArg (extChartAt 𝓘(ℝ, E) (F x)) h))

private theorem real_mem_fold_halfdisk {p r s : ℝ} (hs : s ∈ Icc (p - r) (p + r)) :
    (s : ℂ) ∈ closedHalfDisk p r := by
  refine ⟨(show 0 ≤ (s : ℂ).im from le_rfl), ?_⟩
  rw [Metric.mem_closedBall, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
  exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩

private theorem uniqueDiffOn_fold_halfdisk (p : ℝ) {r : ℝ} (hr : 0 < r) :
    UniqueDiffOn ℝ (closedHalfDisk p r) := by
  apply uniqueDiffOn_convex
    ((convex_halfSpace_im_ge 0).inter (convex_closedBall (p : ℂ) r))
  let q : ℂ := (p : ℂ) + (r / 2 : ℂ) * Complex.I
  have hq : q ∈ (openHalfDisk p r : Set ℂ) := by
    constructor
    · change 0 < q.im
      simp only [q, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
        Complex.div_ofNat_re, Complex.ofReal_re, zero_add]
      positivity
    · rw [Metric.mem_ball, dist_eq_norm]
      simp only [q, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
      rw [abs_of_pos hr]
      linarith
  refine ⟨q, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact mem_of_superset ((openHalfDisk p r).isOpen.mem_nhds hq)
    (fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] in
private theorem common_within_tangent_of_eqOn_seam
    {Splus Sminus : Set ℂ} {Fplus Fminus : ℂ → M}
    {p v : ℂ} {a b q : ℝ} (hab : a < b) (hq : q ∈ Icc a b)
    (hmapsPlus : MapsTo (fun t : ℝ => p + t • v) (Icc a b) Splus)
    (hmapsMinus : MapsTo (fun t : ℝ => p + t • v) (Icc a b) Sminus)
    (hplus : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      Fplus Splus (p + q • v))
    (hminus : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
      Fminus Sminus (p + q • v))
    (htrace : ∀ t ∈ Icc a b, Fplus (p + t • v) = Fminus (p + t • v)) :
    mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Fplus Splus (p + q • v) v =
      tangentSpaceCast 𝓘(ℝ, E) (Fminus (p + q • v)) (Fplus (p + q • v))
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Fminus Sminus (p + q • v) v) := by
  let line : ℝ → ℂ := fun t => p + t • v
  have hline : HasDerivAt line v q := by
    simpa only [line, id_eq, one_smul] using!
      ((hasDerivAt_id q).smul_const v).const_add p
  have hunique := (uniqueDiffOn_Icc hab q hq).uniqueMDiffWithinAt
  have hdl := hline.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt.mfderivWithin hunique
  have hdplus := mfderivWithin_comp q hplus
    hline.hasFDerivAt.hasMFDerivAt.mdifferentiableAt.mdifferentiableWithinAt
    hmapsPlus hunique
  have hdminus := mfderivWithin_comp q hminus
    hline.hasFDerivAt.hasMFDerivAt.mdifferentiableAt.mdifferentiableWithinAt
    hmapsMinus hunique
  have hsame := mfderivWithin_congr_of_mem
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
    (f₁ := Fplus ∘ line) (f := Fminus ∘ line) htrace hq
  rw [hdplus, hdminus, hdl] at hsame
  have heval := congrArg (fun A : ℝ →L[ℝ] E => A 1) hsame
  change mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Fplus Splus (p + q • v)
      ((1 : ℝ) • v) =
    tangentSpaceCast 𝓘(ℝ, E) (Fminus (p + q • v)) (Fplus (p + q • v))
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Fminus Sminus (p + q • v)
        ((1 : ℝ) • v)) at heval
  simpa only [one_smul] using! heval


omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem inner_cast_seam
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {x y : M} (h : x = y)
    (v w : TangentSpace 𝓘(ℝ, E) y) :
    g.inner x (tangentSpaceCast 𝓘(ℝ, E) y x v)
      (tangentSpaceCast 𝓘(ℝ, E) y x w) = g.inner y v w := by
  subst y
  rfl

omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem inner_section_cast_seam
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {x y : M} (h : x = y)
    (Y : ∀ p : M, TangentSpace 𝓘(ℝ, E) p) (w : TangentSpace 𝓘(ℝ, E) y) :
    g.inner x (Y x) (tangentSpaceCast 𝓘(ℝ, E) y x w) = g.inner y (Y y) w := by
  subst y
  rfl

omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem continuousOn_seam_gram
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F : ℂ → M} {H : Set ℂ}
    (hH : UniqueDiffOn ℝ H) (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F H) :
    ContinuousOn (fun z => gramWithin g F H z 1 1) H := by
  have hT := contMDiffOn_source_partialWithin hH hF (m := 0) (by simp) (1 : ℂ)
  have hc : ContDiffOn ℝ 0 (fun z => gramWithin g F H z 1 1) H := by
    intro z hz
    have h : ContMDiffWithinAt 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 0
        (fun q => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (F q)
          (gramWithin g F H q 1 1)) H z := by
      apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
      · exact (g.contMDiff.contMDiffAt.of_le (by simp)).comp_contMDiffWithinAt z
          ((hF.of_le (by simp)) z hz)
      · exact hT z hz
      · exact hT z hz
    exact (contMDiffWithinAt_totalSpace.mp h).2.contDiffWithinAt
  exact hc.continuousOn


omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem fold_seam_tangent_speed
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F₁ F₂ : ℂ → M} {p r : ℝ}
    (hr : 0 < r)
    (hF₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F₁ (closedHalfDisk p r))
    (hF₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F₂ (closedHalfDisk p r))
    (hseam : ∀ t ∈ Icc (p - r) (p + r), F₁ (t : ℂ) = F₂ (t : ℂ)) :
    ∀ s ∈ Icc (p - r) (p + r),
      F₁ (s : ℂ) = F₂ (s : ℂ) ∧
      partialWithin F₁ (closedHalfDisk p r) (s : ℂ) (1 : ℂ) =
        tangentSpaceCast 𝓘(ℝ, E) (F₂ (s : ℂ)) (F₁ (s : ℂ))
          (partialWithin F₂ (closedHalfDisk p r) (s : ℂ) (1 : ℂ)) ∧
      Real.sqrt (gramWithin g F₁ (closedHalfDisk p r) (s : ℂ) 1 1) =
        Real.sqrt (gramWithin g F₂ (closedHalfDisk p r) (s : ℂ) 1 1) := by
  intro s hs
  have hreal : MapsTo (fun t : ℝ => (t : ℂ)) (Icc (p - r) (p + r))
      (closedHalfDisk p r) := fun _ ht => real_mem_fold_halfdisk ht
  have hline (t : ℝ) : (0 : ℂ) + t • (1 : ℂ) = (t : ℂ) := by simp
  have ht := common_within_tangent_of_eqOn_seam (p := (0 : ℂ)) (v := (1 : ℂ))
    (by linarith : p - r < p + r) hs
    (by simpa only [hline] using hreal) (by simpa only [hline] using hreal)
    (by simpa only [hline] using (hF₁ (s : ℂ) (hreal hs)).mdifferentiableWithinAt one_ne_zero)
    (by simpa only [hline] using (hF₂ (s : ℂ) (hreal hs)).mdifferentiableWithinAt one_ne_zero)
    (by simpa only [hline] using hseam)
  have ht' : partialWithin F₁ (closedHalfDisk p r) (s : ℂ) (1 : ℂ) =
      tangentSpaceCast 𝓘(ℝ, E) (F₂ (s : ℂ)) (F₁ (s : ℂ))
        (partialWithin F₂ (closedHalfDisk p r) (s : ℂ) (1 : ℂ)) := by
    let P : ℂ → Prop := fun q => @Eq E
      ((show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ (closedHalfDisk p r) q) (1 : ℂ))
      ((show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ (closedHalfDisk p r) q) (1 : ℂ))
    have hP : P ((0 : ℂ) + s • (1 : ℂ)) := by simpa only [P] using! ht
    have hPs : P (s : ℂ) := (congrArg P (hline s)).mp hP
    simpa only [P, partialWithin] using! hPs
  refine ⟨hseam s hs, ht', congrArg Real.sqrt ?_⟩
  change g.inner (F₁ (s : ℂ)) (partialWithin F₁ (closedHalfDisk p r) (s : ℂ) 1)
      (partialWithin F₁ (closedHalfDisk p r) (s : ℂ) 1) =
    g.inner (F₂ (s : ℂ)) (partialWithin F₂ (closedHalfDisk p r) (s : ℂ) 1)
      (partialWithin F₂ (closedHalfDisk p r) (s : ℂ) 1)
  rw [ht']
  exact inner_cast_seam g (hseam s hs) _ _


/-- The two one-sided restrictions of a fold admit one actual supported velocity.
The support excludes the circular patch edge and lies in the original exterior. -/
private theorem exists_supported_field_negative_fold_flux
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F₁ F₂ : ℂ → M} {W : Set M}
    {p r : ℝ} (hr : 0 < r)
    (hFH₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F₁ (closedHalfDisk p r))
    (hFH₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F₂ (closedHalfDisk p r))
    (himm₁ : ∀ z ∈ closedHalfDisk p r, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ (closedHalfDisk p r) z))
    (himm₂ : ∀ z ∈ closedHalfDisk p r, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ (closedHalfDisk p r) z))
    (hseam : ∀ s ∈ Icc (p - r) (p + r), F₁ (s : ℂ) = F₂ (s : ℂ))
    (hnonreturn₁ : ∀ z ∈ closedHalfDisk p r, z ≠ (p : ℂ) → F₁ z ≠ F₁ (p : ℂ))
    (hnonreturn₂ : ∀ z ∈ closedHalfDisk p r, z ≠ (p : ℂ) → F₂ z ≠ F₂ (p : ℂ))
    (hpW : F₁ (p : ℂ) ∈ interior W)
    (hfold : inwardConormalWithin g F₁ (closedHalfDisk p r) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) (F₂ (p : ℂ)) (F₁ (p : ℂ))
        (inwardConormalWithin g F₂ (closedHalfDisk p r) (p : ℂ)) ≠ 0) :
    ∃ Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E x (Y x)) ∧
      HasCompactSupport Y ∧ tsupport Y ⊆ W ∧
      Y (F₁ (p : ℂ)) = inwardConormalWithin g F₁ (closedHalfDisk p r) (p : ℂ) +
        tangentSpaceCast 𝓘(ℝ, E) (F₂ (p : ℂ)) (F₁ (p : ℂ))
          (inwardConormalWithin g F₂ (closedHalfDisk p r) (p : ℂ)) ∧
      (∀ q ∈ upperClosed ∩ Metric.sphere (p : ℂ) r, F₁ q ∉ tsupport Y) ∧
      (∀ q ∈ upperClosed ∩ Metric.sphere (p : ℂ) r, F₂ q ∉ tsupport Y) ∧
      ((∫ s : ℝ, (Icc (p - r) (p + r)).indicator
          (fun s => Real.sqrt (gramWithin g F₁ (closedHalfDisk p r) (s : ℂ) 1 1) *
            g.inner (F₁ (s : ℂ)) (Y (F₁ (s : ℂ)))
              (-inwardConormalWithin g F₁ (closedHalfDisk p r) (s : ℂ))) s) +
        (∫ s : ℝ, (Icc (p - r) (p + r)).indicator
          (fun s => Real.sqrt (gramWithin g F₂ (closedHalfDisk p r) (s : ℂ) 1 1) *
            g.inner (F₂ (s : ℂ)) (Y (F₂ (s : ℂ)))
              (-inwardConormalWithin g F₂ (closedHalfDisk p r) (s : ℂ))) s)) < 0 := by
  classical
  let H : Set ℂ := closedHalfDisk p r
  let J : Set ℝ := Icc (p - r) (p + r)
  have hreal : MapsTo (fun s : ℝ => (s : ℂ)) J H :=
    fun _ hs => real_mem_fold_halfdisk hs
  have hpJ : p ∈ J := ⟨by linarith, by linarith⟩
  have hpH : (p : ℂ) ∈ H := hreal hpJ
  have huniq : UniqueDiffOn ℝ H := uniqueDiffOn_fold_halfdisk p hr
  have hall := fold_seam_tangent_speed g hr hFH₁ hFH₂ hseam
  -- The uncut field is chosen before the smaller scalar positivity interval.
  obtain ⟨Y₀, hY₀center⟩ :=
    ContMDiffSection.exists_eq_at (I := 𝓘(ℝ, E)) (F := E)
      (V := TangentSpace 𝓘(ℝ, E)) (n := (⊤ : ℕ∞)) (F₁ (p : ℂ))
      (inwardConormalWithin g F₁ H (p : ℂ) +
        tangentSpaceCast 𝓘(ℝ, E) (F₂ (p : ℂ)) (F₁ (p : ℂ)) (inwardConormalWithin g F₂ H (p : ℂ)))
  have hY₀ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y₀ x)) := Y₀.contMDiff
  let γ₀ : ℝ → M := fun s => F₁ (s : ℂ)
  let T : ∀ s, TangentSpace 𝓘(ℝ, E) (γ₀ s) :=
    fun s => partialWithin F₁ H (s : ℂ) (1 : ℂ)
  let νPlus : ∀ s, TangentSpace 𝓘(ℝ, E) (γ₀ s) :=
    fun s => inwardConormalWithin g F₁ H (s : ℂ)
  let νMinus : ∀ s, TangentSpace 𝓘(ℝ, E) (γ₀ s) := fun s =>
    if s ∈ J then tangentSpaceCast 𝓘(ℝ, E) (F₂ (s : ℂ)) (F₁ (s : ℂ))
      (inwardConormalWithin g F₂ H (s : ℂ)) else 0
  have hplus : ContinuousOn (fun s => g.inner (γ₀ s) (Y₀ (γ₀ s)) (νPlus s)) J :=
    (continuousOn_inner_inwardConormalWithin g F₁ huniq.uniqueMDiffOn hFH₁ himm₁
      (fun x => Y₀ x) hY₀).comp Complex.continuous_ofReal.continuousOn hreal
  have hminus : ContinuousOn (fun s => g.inner (γ₀ s) (Y₀ (γ₀ s)) (νMinus s)) J := by
    apply ((continuousOn_inner_inwardConormalWithin g F₂ huniq.uniqueMDiffOn hFH₂ himm₂
      (fun x => Y₀ x) hY₀).comp Complex.continuous_ofReal.continuousOn hreal).congr
    intro s hs
    change g.inner (F₁ (s : ℂ)) (Y₀ (F₁ (s : ℂ))) (νMinus s) =
      g.inner (F₂ (s : ℂ)) (Y₀ (F₂ (s : ℂ))) (inwardConormalWithin g F₂ H (s : ℂ))
    rw [show νMinus s = tangentSpaceCast 𝓘(ℝ, E) (F₂ (s : ℂ)) (F₁ (s : ℂ))
      (inwardConormalWithin g F₂ H (s : ℂ)) from ite_eq_left hs]
    exact inner_section_cast_seam g (hall s hs).1 (fun x => Y₀ x) _
  have hspeed : ContinuousOn (fun s => g.inner (γ₀ s) (T s) (T s)) J :=
    (continuousOn_seam_gram g huniq hFH₁).comp Complex.continuous_ofReal.continuousOn hreal
  have hcenter : Y₀ (γ₀ p) = νPlus p + νMinus p := by
    simpa only [γ₀, νPlus, νMinus, ite_eq_left hpJ, Complex.ofReal_zero] using hY₀center
  have hfold₀ : νPlus p + νMinus p ≠ 0 := by
    simpa only [νPlus, νMinus, ite_eq_left hpJ, Complex.ofReal_zero] using hfold
  have hT : T p ≠ 0 := by
    change @Ne E
      ((show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ H (p : ℂ)) (1 : ℂ))
      (0 : E)
    exact fun h => (one_ne_zero : (1 : ℂ) ≠ 0) ((himm₁ _ hpH) (h.trans (map_zero _).symm))
  obtain ⟨δ, hδ, hδr, _, hsmall⟩ :=
    exists_patch_for_strict_negative_outward_seam_flux g γ₀ T (fun s => Y₀ (γ₀ s))
      νPlus νMinus (s₀ := p) hr
      hplus hminus hspeed hcenter hfold₀ hT
  let ρ : ℝ := δ / 2
  have hρ : 0 < ρ := half_pos hδ
  have hρδ : ρ ≤ δ := half_le_self hδ.le
  have hρr : ρ ≤ r := hρδ.trans hδr
  let K : Set ℝ := Icc (p - ρ) (p + ρ)
  have hKJ : K ⊆ J := Icc_subset_Icc (by linarith) (by linarith)
  -- Both curved edges and every remaining real-seam point are excluded.
  let A : Set ℂ := (upperClosed ∩ Metric.sphere (p : ℂ) r) ∪
    (fun s : ℝ => (s : ℂ)) '' (Icc (p - r) (p - ρ) ∪ Icc (p + ρ) (p + r))
  have hAc : IsCompact A :=
    ((isCompact_sphere (p : ℂ) r).inter_left
      (isClosed_le continuous_const Complex.continuous_im)).union
      ((isCompact_Icc.union isCompact_Icc).image Complex.continuous_ofReal)
  have hAH : A ⊆ H := by
    intro z hz
    rcases hz with hz | ⟨s, hs, rfl⟩
    · exact ⟨hz.1, (show dist z (p : ℂ) = r from hz.2).le⟩
    · apply real_mem_fold_halfdisk
      rcases hs with hs | hs
      · exact ⟨hs.1, hs.2.trans (by linarith)⟩
      · exact ⟨(by linarith : p - r ≤ p + ρ).trans hs.1, hs.2⟩
  have hpA : (p : ℂ) ∉ A := by
    intro hz
    rcases hz with hz | ⟨s, hs, hs0⟩
    · have he : (0 : ℝ) = r := by simpa only [Metric.mem_sphere, dist_self] using hz.2
      linarith
    · have hs0r : s = p := Complex.ofReal_injective hs0
      subst s
      rcases hs with hs | hs <;> linarith [hs.1, hs.2]
  let B : Set M := F₁ '' A ∪ F₂ '' A
  have hBc : IsCompact B :=
    (hAc.image_of_continuousOn (hFH₁.continuousOn.mono hAH)).union
      (hAc.image_of_continuousOn (hFH₂.continuousOn.mono hAH))
  have hpB : F₁ (p : ℂ) ∉ B := by
    intro hp
    rcases hp with ⟨z, hz, he⟩ | ⟨z, hz, he⟩
    · exact hnonreturn₁ z (hAH hz) (fun heq => hpA (heq ▸ hz)) he
    · exact hnonreturn₂ z (hAH hz) (fun heq => hpA (heq ▸ hz))
        (he.trans (hseam p hpJ))
  let O : Set M := interior W ∩ Bᶜ
  have hO : IsOpen O := isOpen_interior.inter hBc.isClosed.isOpen_compl
  have hpO : ({F₁ (p : ℂ)} : Set M) ⊆ O := by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨hpW, hpB⟩
  obtain ⟨β, hβ, hβc, hβO, hβrange, hβone⟩ :=
    DifferentialGeometry.Topology.exists_contMDiff_cutoff_of_isCompact
      (I := 𝓘(ℝ, E)) isCompact_singleton hO hpO
  have hβp : β (F₁ (p : ℂ)) = 1 := by
    have he : β =ᶠ[𝓝 (F₁ (p : ℂ))] (1 : M → ℝ) := by
      simpa only [nhdsSet_singleton] using hβone
    exact he.self_of_nhds
  have hβzero : ∀ p ∈ B, β p = 0 := by
    intro p hp
    exact image_eq_zero_of_notMem_tsupport (fun hpt => (hβO hpt).2 hp)
  let Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x := fun x => β x • Y₀ x
  have hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x)) := hβ.smul_section hY₀
  have hYs : tsupport Y ⊆ tsupport β := tsupport_smul_subset_left β (fun x => Y₀ x)
  have hYc : HasCompactSupport Y := hβc.of_isClosed_subset (isClosed_tsupport Y) hYs
  have hYcenter : Y (F₁ (p : ℂ)) = inwardConormalWithin g F₁ H (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) (F₂ (p : ℂ)) (F₁ (p : ℂ)) (inwardConormalWithin g F₂ H (p : ℂ)) := by
    change β (F₁ (p : ℂ)) • Y₀ (F₁ (p : ℂ)) = _
    rw [hβp, one_smul]
    exact hY₀center
  have havoid₁ : ∀ q ∈ upperClosed ∩ Metric.sphere (p : ℂ) r, F₁ q ∉ tsupport Y := by
    intro q hq hqY
    exact (hβO (hYs hqY)).2 (Or.inl ⟨q, Or.inl hq, rfl⟩)
  have havoid₂ : ∀ q ∈ upperClosed ∩ Metric.sphere (p : ℂ) r, F₂ q ∉ tsupport Y := by
    intro q hq hqY
    exact (hβO (hYs hqY)).2 (Or.inr ⟨q, Or.inl hq, rfl⟩)
  have houter₁ : ∀ s ∈ Icc (p - r) (p - ρ) ∪ Icc (p + ρ) (p + r), β (F₁ (s : ℂ)) = 0 := by
    intro s hs
    exact hβzero _ (Or.inl ⟨(s : ℂ), Or.inr ⟨s, hs, rfl⟩, rfl⟩)
  have houter₂ : ∀ s ∈ Icc (p - r) (p - ρ) ∪ Icc (p + ρ) (p + r), β (F₂ (s : ℂ)) = 0 := by
    intro s hs
    exact hβzero _ (Or.inr ⟨(s : ℂ), Or.inr ⟨s, hs, rfl⟩, rfl⟩)
  have hγc : ContinuousOn γ₀ J :=
    hFH₁.continuousOn.comp Complex.continuous_ofReal.continuousOn hreal
  have hβK : ContinuousOn (fun s => β (γ₀ s)) K :=
    hβ.continuous.comp_continuousOn (hγc.mono hKJ)
  have hβleft : β (γ₀ (p - ρ)) = 0 :=
    houter₁ _ (Or.inl ⟨by linarith, le_rfl⟩)
  have hβright : β (γ₀ (p + ρ)) = 0 := houter₁ _ (Or.inr ⟨le_rfl, by linarith⟩)
  have hnegative := hsmall ρ hρ hρδ β
    (by simpa only [zero_sub, zero_add] using hβK)
    (fun s _ => (hβrange (γ₀ s)).1)
    (by simpa only [γ₀, Complex.ofReal_zero, hβp] using (zero_lt_one : (0 : ℝ) < 1))
    (by simpa only [zero_sub] using hβleft)
    (by simpa only [zero_add] using hβright)
  let PPlus : ℝ → ℝ := fun s => Real.sqrt (g.inner (γ₀ s) (T s) (T s)) *
    g.inner (γ₀ s) (β (γ₀ s) • Y₀ (γ₀ s)) (νPlus s)
  let PMinus : ℝ → ℝ := fun s => Real.sqrt (g.inner (γ₀ s) (T s) (T s)) *
    g.inner (γ₀ s) (β (γ₀ s) • Y₀ (γ₀ s)) (νMinus s)
  have hnegative' : -(∫ s : ℝ, K.indicator PPlus s) -
      (∫ s : ℝ, K.indicator PMinus s) < 0 := by
    simpa only [zero_sub, zero_add] using hnegative
  have houter (s : ℝ) (hs : s ∈ J) (hn : s ∉ K) :
      s ∈ Icc (p - r) (p - ρ) ∪ Icc (p + ρ) (p + r) := by
    by_cases hleft : s < p - ρ
    · exact Or.inl ⟨hs.1, hleft.le⟩
    · exact Or.inr ⟨le_of_lt (lt_of_not_ge (fun h => hn ⟨le_of_not_gt hleft, h⟩)), hs.2⟩
  have hflux₁ : (fun s : ℝ => J.indicator
      (fun s => Real.sqrt (gramWithin g F₁ H (s : ℂ) 1 1) *
        g.inner (F₁ (s : ℂ)) (Y (F₁ (s : ℂ)))
          (-inwardConormalWithin g F₁ H (s : ℂ))) s) =
      fun s => -(K.indicator PPlus s) := by
    funext s
    by_cases hs : s ∈ K
    · rw [indicator_of_mem (hKJ hs), indicator_of_mem hs]
      simp only [PPlus, γ₀, T, νPlus, Y, gramWithin, map_neg, mul_neg]
    · rw [indicator_of_notMem hs, neg_zero]
      by_cases hsJ : s ∈ J
      · rw [indicator_of_mem hsJ]
        have hz : Y (F₁ (s : ℂ)) = 0 := by
          change β (F₁ (s : ℂ)) • Y₀ (F₁ (s : ℂ)) = 0
          rw [houter₁ s (houter s hsJ hs), zero_smul]
        rw [hz, map_zero]
        exact mul_zero _
      · exact indicator_of_notMem hsJ _
  have hflux₂ : (fun s : ℝ => J.indicator
      (fun s => Real.sqrt (gramWithin g F₂ H (s : ℂ) 1 1) *
        g.inner (F₂ (s : ℂ)) (Y (F₂ (s : ℂ)))
          (-inwardConormalWithin g F₂ H (s : ℂ))) s) =
      fun s => -(K.indicator PMinus s) := by
    funext s
    by_cases hs : s ∈ K
    · have hsJ := hKJ hs
      rw [indicator_of_mem hsJ, indicator_of_mem hs]
      have hpair : g.inner (γ₀ s) (Y (γ₀ s)) (νMinus s) =
          g.inner (F₂ (s : ℂ)) (Y (F₂ (s : ℂ)))
            (inwardConormalWithin g F₂ H (s : ℂ)) := by
        change g.inner (F₁ (s : ℂ)) (Y (F₁ (s : ℂ))) (νMinus s) = _
        rw [show νMinus s = tangentSpaceCast 𝓘(ℝ, E) (F₂ (s : ℂ)) (F₁ (s : ℂ))
          (inwardConormalWithin g F₂ H (s : ℂ)) from ite_eq_left hsJ]
        exact inner_section_cast_seam g (hall s hsJ).1 Y _
      change Real.sqrt (gramWithin g F₂ H (s : ℂ) 1 1) *
        g.inner (F₂ (s : ℂ)) (Y (F₂ (s : ℂ)))
          (-inwardConormalWithin g F₂ H (s : ℂ)) = -PMinus s
      have hpm : PMinus s = Real.sqrt (gramWithin g F₁ H (s : ℂ) 1 1) *
          g.inner (F₂ (s : ℂ)) (Y (F₂ (s : ℂ)))
            (inwardConormalWithin g F₂ H (s : ℂ)) :=
        congrArg (fun t : ℝ => Real.sqrt (gramWithin g F₁ H (s : ℂ) 1 1) * t) hpair
      rw [hpm, (hall s hsJ).2.2, map_neg, mul_neg]
    · rw [indicator_of_notMem hs, neg_zero]
      by_cases hsJ : s ∈ J
      · rw [indicator_of_mem hsJ]
        have hz : Y (F₂ (s : ℂ)) = 0 := by
          change β (F₂ (s : ℂ)) • Y₀ (F₂ (s : ℂ)) = 0
          rw [houter₂ s (houter s hsJ hs), zero_smul]
        rw [hz, map_zero]
        exact mul_zero _
      · exact indicator_of_notMem hsJ _
  refine ⟨Y, hY, hYc, (fun x hx => interior_subset (hβO (hYs hx)).1),
    hYcenter, havoid₁, havoid₂, ?_⟩
  change (∫ s : ℝ, J.indicator _ s) + (∫ s : ℝ, J.indicator _ s) < 0
  rw [hflux₁, hflux₂, integral_neg, integral_neg]
  simpa only [sub_eq_add_neg] using hnegative'

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] in
private theorem exists_halfdisk_nonreturn_radius
    {F₁ F₂ : ℂ → M} {p R : ℝ} (hR : 0 < R)
    (hF₁ : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ (closedHalfDisk p R) (p : ℂ))
    (hF₂ : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ (closedHalfDisk p R) (p : ℂ))
    (hi₁ : Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ (closedHalfDisk p R) (p : ℂ)))
    (hi₂ : Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ (closedHalfDisk p R) (p : ℂ))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      (∀ z ∈ closedHalfDisk p r, z ≠ (p : ℂ) → F₁ z ≠ F₁ (p : ℂ)) ∧
      (∀ z ∈ closedHalfDisk p r, z ≠ (p : ℂ) → F₂ z ≠ F₂ (p : ℂ)) := by
  have hne₁ := eventually_ne_of_injective_mfderivWithin hF₁ hi₁
  have hne₂ := eventually_ne_of_injective_mfderivWithin hF₂ hi₂
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp (hne₁.and hne₂)
  let r : ℝ := min R ε / 2
  have hr : 0 < r := half_pos (lt_min hR hε)
  have hrR : r ≤ R := (half_le_self (le_of_lt (lt_min hR hε))).trans (min_le_left _ _)
  have hrε : r < ε := (half_lt_self (lt_min hR hε)).trans_le (min_le_right _ _)
  have hlocal (z : ℂ) (hz : z ∈ closedHalfDisk p r) (hne : z ≠ (p : ℂ)) :
      F₁ z ≠ F₁ (p : ℂ) ∧ F₂ z ≠ F₂ (p : ℂ) := by
    apply hεsub
    refine ⟨?_, ⟨?_, hne⟩⟩
    · exact (Metric.mem_closedBall.mp hz.2).trans_lt hrε
    · exact ⟨hz.1, (Metric.mem_closedBall.mp hz.2).trans hrR⟩
  exact ⟨r, hr, hrR, fun z hz hne => (hlocal z hz hne).1,
    fun z hz hne => (hlocal z hz hne).2⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] in
private theorem fold_partialWithin_shrink
    {F : ℂ → M} {p r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F (closedHalfDisk p R))
    {z : ℂ} (hz : z ∈ closedHalfDisk p r) :
    mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (closedHalfDisk p r) z =
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (closedHalfDisk p R) z := by
  have hsub : closedHalfDisk p r ⊆ closedHalfDisk p R :=
    fun q hq => ⟨hq.1, (Metric.mem_closedBall.mp hq.2).trans hrR⟩
  exact mfderivWithin_subset hsub
    ((uniqueDiffOn_fold_halfdisk p hr).uniqueMDiffOn z hz)
    ((hF z (hsub hz)).mdifferentiableWithinAt one_ne_zero)

omit [T3Space M] in
private theorem fold_meanTrace_of_harmonic_conformal
    (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (F : ℂ → M)
    (hFinterior : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => F q))
    (hiFinterior : ∀ z : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => F q) z))
    (hconf : ∀ z ∈ (N : Set ℂ), DiskMapConformalAt g F z)
    (htension : ∀ z ∈ (N : Set ℂ), diskMapTension g F z = 0)
    (z : N) :
    ImmersedDiskDivergence.inducedMeanTrace N g F hFinterior hiFinterior z = 0 := by
  let gN := g.pullback (fun q : N => F q) hFinterior hiFinterior
  have hmetric : ∀ (q : N) (v w : ℂ),
      g.inner (F q) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F q v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F q w) = gN.inner q v w := by
    intro q v w
    change _ = g.inner (F q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun a : N => F a) q v)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun a : N => F a) q w)
    rw [DifferentialGeometry.mfderiv_restrict_open]
    rfl
  have htrace := secondFundamentalForm_disk_coordinate_trace_eq_zero_of_tension_eq_zero
    (N) gN g F hFinterior hmetric z (htension z z.property)
  dsimp only [gN] at htrace
  have hb : ImmersedDiskDivergence.gramB g F z = 0 := (hconf z z.property).1
  have hac : ImmersedDiskDivergence.gramA g F z =
      ImmersedDiskDivergence.gramC g F z := (hconf z z.property).2
  unfold ImmersedDiskDivergence.inducedMeanTrace
  simp only [hb, ← hac, mul_zero, zero_smul, sub_zero, ← smul_add, htrace, smul_zero]

private theorem fold_sheet_flux_of_mean_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (F : ℂ → M)
    (p : ℝ) {r : ℝ} (hr : 0 < r)
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F (closedHalfDisk p r))
    (hi : ∀ z ∈ closedHalfDisk p r, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (closedHalfDisk p r) z))
    (hFi : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F (openHalfDisk p r))
    (hminimal : ∀
      (hFinterior : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : openHalfDisk p r => F q))
      (hiFinterior : ∀ z : openHalfDisk p r, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : openHalfDisk p r => F q) z)),
      ∀ z : openHalfDisk p r, ImmersedDiskDivergence.inducedMeanTrace
        (openHalfDisk p r) g F hFinterior hiFinterior z = 0)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x)))
    (havoid : ∀ q ∈ upperClosed ∩ Metric.sphere (p : ℂ) r, F q ∉ tsupport Y) :
    (∫ z in (openHalfDisk p r : Set ℂ),
        ambientDivergenceWithin g F (closedHalfDisk p r) Y z) =
      ∫ s : ℝ, (Icc (p - r) (p + r)).indicator
        (fun s => Real.sqrt (gramWithin g F (closedHalfDisk p r) (s : ℂ) 1 1) *
          g.inner (F (s : ℂ)) (Y (F (s : ℂ)))
            (-inwardConormalWithin g F (closedHalfDisk p r) (s : ℂ))) s := by
  have hFinterior : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞
      (fun q : openHalfDisk p r => F q) :=
    hFi.comp_contMDiff contMDiff_subtype_val (fun q => q.property)
  have hiFinterior (z : openHalfDisk p r) : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : openHalfDisk p r => F q) z) := by
    rw [DifferentialGeometry.mfderiv_restrict_open]
    have hS : closedHalfDisk p r ∈ 𝓝 (z : ℂ) :=
      mem_of_superset ((openHalfDisk p r).isOpen.mem_nhds z.property)
        (fun q hq => ⟨(show 0 < q.im from hq.1).le, Metric.ball_subset_closedBall hq.2⟩)
    rw [← mfderivWithin_of_mem_nhds hS]
    exact hi z (mem_of_mem_nhds hS)
  exact integral_actual_halfdisk_ambient_divergence_eq_outward_conormal_flux g F p hr
    hF hi hFinterior (hminimal hFinterior hiFinterior) Y hY havoid

private theorem exists_flow_of_supported_fold_field
    {W : Set M} (Y : ∀ y : M, TangentSpace 𝓘(ℝ, E) y)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E y (Y y)))
    (hYc : HasCompactSupport Y) (hYW : tsupport Y ⊆ W) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => Φ q.1 q.2) ∧
      (∀ y, Φ 0 y = y) ∧
      (∀ t y, y ∉ tsupport Y → Φ t y = y) ∧
      (∀ t, MapsTo (Φ t) W W) ∧
      ∀ y, (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => Φ t y) 0 (1 : ℝ) : E) = Y y := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let hc := Analysis.ODE.exists_globalIntegralCurve_of_compactSupport Y hY hYc.isCompact
  choose Φ hΦ hΦinv using Analysis.ODE.globalFlow_diffeomorph_of_complete Y hY hc
  have hsm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Φ q.1 q.2) :=
    (Analysis.ODE.contMDiff_globalFlow_joint_of_complete Y hY hc).congr
      (fun q => hΦ q.1 q.2)
  have hzero (y : M) : Φ 0 y = y :=
    (hΦ 0 y).trans (Analysis.ODE.curveAt_zero Y hc y)
  have hfix (t : ℝ) (y : M) (hy : y ∉ tsupport Y) : Φ t y = y := by
    rw [hΦ t y]
    exact Analysis.ODE.curveAt_eq_self_of_not_mem_tsupport Y hY hc hy t
  have hmaps (t : ℝ) : MapsTo (Φ t) W W := by
    intro y hy
    by_contra hnot
    have hout : Φ t y ∉ tsupport Y := fun hp => hnot (hYW hp)
    have heq : Φ t y = y := (Φ t).injective (hfix t (Φ t y) hout)
    exact hnot (heq.symm ▸ hy)
  refine ⟨Φ, hsm, hzero, hfix, hmaps, ?_⟩
  intro y
  have heq : (fun t => Φ t y) = Analysis.ODE.curveAt Y hc y :=
    funext (fun t => hΦ t y)
  have hd : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (Analysis.ODE.curveAt Y hc y) 0 (1 : ℝ) : E) =
      Y (Analysis.ODE.curveAt Y hc y 0) := by
    refine (congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ))
      (Analysis.ODE.curveAt_integralCurve Y hc y 0).mfderiv).trans ?_
    change (1 : ℝ) • (Y (Analysis.ODE.curveAt Y hc y 0) : E) =
      Y (Analysis.ODE.curveAt Y hc y 0)
    exact one_smul ℝ _
  rw [heq]
  exact hd.trans (congrArg (fun z => (Y z : E)) (Analysis.ODE.curveAt_zero Y hc y))

private theorem exists_supported_flow_of_fold_mean_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {W : Set M} {p R : ℝ} (hR : 0 < R)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u) (closedHalfDisk p R))
    (hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ conj) (closedHalfDisk p R))
    (hi : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (closedHalfDisk p R) z))
    (hir : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) (closedHalfDisk p R) z))
    (hUi : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) (openHalfDisk p R))
    (hUri : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ conj) (openHalfDisk p R))
    (hminimal : ∀ r : ℝ, 0 < r → r ≤ R → ∀
      (hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : openHalfDisk p r => (diskExtension u) q))
      (hiF : ∀ z : openHalfDisk p r, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : openHalfDisk p r => (diskExtension u) q) z)),
      ∀ z : openHalfDisk p r, ImmersedDiskDivergence.inducedMeanTrace
        (openHalfDisk p r) g (diskExtension u) hF hiF z = 0)
    (hminimalr : ∀ r : ℝ, 0 < r → r ≤ R → ∀
      (hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : openHalfDisk p r => (diskExtension u ∘ conj) q))
      (hiF : ∀ z : openHalfDisk p r, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : openHalfDisk p r => (diskExtension u ∘ conj) q) z)),
      ∀ z : openHalfDisk p r, ImmersedDiskDivergence.inducedMeanTrace
        (openHalfDisk p r) g (diskExtension u ∘ conj) hF hiF z = 0)
    (hpW : diskExtension u (p : ℂ) ∈ interior W)
    (hfold : inwardConormalWithin g (diskExtension u) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ conj) (p : ℂ)) (diskExtension u (p : ℂ))
        (inwardConormalWithin g (diskExtension u ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0) :
    ∃ (r : ℝ) (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
      (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞),
      0 < r ∧ r ≤ R ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E x (Y x)) ∧
      HasCompactSupport Y ∧ tsupport Y ⊆ W ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => Φ t x) 0 1 = Y x) ∧
      (∀ t z, z ∈ Metric.sphere (p : ℂ) r → Φ t (diskExtension u z) = diskExtension u z) ∧
      (∀ t, MapsTo (Φ t) W W) ∧
      ((∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
          ambientDivergenceWithin g (diskExtension u) (closedHalfDisk p r) Y z) +
        ∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
          ambientDivergenceWithin g (diskExtension u ∘ conj) (closedHalfDisk p r) Y z) < 0 := by
  have hpH : (p : ℂ) ∈ closedHalfDisk p R :=
    real_mem_fold_halfdisk ⟨by linarith, by linarith⟩
  obtain ⟨r, hr, hrR, hnonreturn₁, hnonreturn₂⟩ :=
    exists_halfdisk_nonreturn_radius hR
      ((hU _ hpH).mdifferentiableWithinAt one_ne_zero)
      ((hUr _ hpH).mdifferentiableWithinAt one_ne_zero) (hi _ hpH) (hir _ hpH)
  have hclosed : closedHalfDisk p r ⊆ closedHalfDisk p R :=
    fun z hz => ⟨hz.1, (Metric.mem_closedBall.mp hz.2).trans hrR⟩
  have hopen : (openHalfDisk p r : Set ℂ) ⊆ (openHalfDisk p R : Set ℂ) :=
    fun z hz => ⟨hz.1, (Metric.mem_ball.mp hz.2).trans_le hrR⟩
  have hi₁ : ∀ z ∈ closedHalfDisk p r, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (closedHalfDisk p r) z) := by
    intro z hz
    rw [fold_partialWithin_shrink hr hrR hU hz]
    exact hi z (hclosed hz)
  have hi₂ : ∀ z ∈ closedHalfDisk p r, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) (closedHalfDisk p r) z) := by
    intro z hz
    rw [fold_partialWithin_shrink hr hrR hUr hz]
    exact hir z (hclosed hz)
  have hpHr : (p : ℂ) ∈ closedHalfDisk p r :=
    real_mem_fold_halfdisk ⟨by linarith, by linarith⟩
  have hconormal (F : ℂ → M)
      (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F (closedHalfDisk p R)) :
      inwardConormalWithin g F (closedHalfDisk p r) (p : ℂ) =
        inwardConormalWithin g F (closedHalfDisk p R) (p : ℂ) := by
    simp only [inwardConormalWithin, gramWithin, densityWithin, partialWithin,
      fold_partialWithin_shrink hr hrR hF hpHr]
  have hfoldr : inwardConormalWithin g (diskExtension u) (closedHalfDisk p r) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ conj) (p : ℂ)) (diskExtension u (p : ℂ))
        (inwardConormalWithin g (diskExtension u ∘ conj) (closedHalfDisk p r) (p : ℂ)) ≠ 0 := by
    rw [hconormal _ hU, hconormal _ hUr]
    exact hfold
  have hseam : ∀ s ∈ Icc (p - r) (p + r),
      diskExtension u (s : ℂ) = (diskExtension u ∘ conj) (s : ℂ) := by
    intro s _
    simp only [Function.comp_apply, Complex.conj_ofReal]
  obtain ⟨Y, hY, hYc, hYW, _, havoid₁, havoid₂, hnegative⟩ :=
    exists_supported_field_negative_fold_flux g hr (hU.mono hclosed) (hUr.mono hclosed)
      hi₁ hi₂ hseam hnonreturn₁ hnonreturn₂ hpW hfoldr
  have hflux₁ := fold_sheet_flux_of_mean_zero g (diskExtension u) p hr
    (hU.mono hclosed) hi₁ (hUi.mono hopen)
    (hminimal r hr hrR) Y hY havoid₁
  have hflux₂ := fold_sheet_flux_of_mean_zero g (diskExtension u ∘ conj) p hr
    (hUr.mono hclosed) hi₂ (hUri.mono hopen)
    (hminimalr r hr hrR) Y hY havoid₂
  obtain ⟨Φ, hΦ, hΦzero, hfix, hΦW, hvelocity⟩ :=
    exists_flow_of_supported_fold_field Y hY hYc hYW
  refine ⟨r, Y, Φ, hr, hrR, hY, hYc, hYW, hΦ, hΦzero, hvelocity, ?_, hΦW, ?_⟩
  · intro t z hz
    apply hfix
    by_cases him : 0 ≤ z.im
    · exact havoid₁ z ⟨him, hz⟩
    · have hzbar : conj z ∈ upperClosed ∩ Metric.sphere (p : ℂ) r := by
        refine ⟨?_, ?_⟩
        · change 0 ≤ (conj z).im
          simpa only [Complex.conj_im] using neg_nonneg.mpr (not_le.mp him).le
        · simpa only [Metric.mem_sphere, Complex.dist_conj_comm, Complex.conj_ofReal] using hz
      simpa only [Function.comp_apply, Complex.conj_conj] using havoid₂ (conj z) hzbar
  · have hS : Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im} =
        (openHalfDisk p r : Set ℂ) := Set.inter_comm _ _
    rw [hS, hflux₁, hflux₂]
    exact hnegative


/-- Conformal-parameter specialization; copying charts need not satisfy these coordinate hypotheses. -/
theorem exists_supported_flow_of_nonzero_fold
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {W : Set M} {p R : ℝ} (hR : 0 < R)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u) (closedHalfDisk p R))
    (hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ conj) (closedHalfDisk p R))
    (hi : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (closedHalfDisk p R) z))
    (hir : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) (closedHalfDisk p R) z))
    (hUi : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) (openHalfDisk p R))
    (hUri : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ conj) (openHalfDisk p R))
    (hconf : ∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt g (diskExtension u) z)
    (hconfr : ∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt g (diskExtension u ∘ conj) z)
    (htension : ∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension g (diskExtension u) z = 0)
    (htensionr : ∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension g (diskExtension u ∘ conj) z = 0)
    (hpW : diskExtension u (p : ℂ) ∈ interior W)
    (hfold : inwardConormalWithin g (diskExtension u) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ conj) (p : ℂ)) (diskExtension u (p : ℂ))
        (inwardConormalWithin g (diskExtension u ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0) :
    ∃ (r : ℝ) (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
      (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞),
      0 < r ∧ r ≤ R ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E x (Y x)) ∧
      HasCompactSupport Y ∧ tsupport Y ⊆ W ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => Φ t x) 0 1 = Y x) ∧
      (∀ t z, z ∈ Metric.sphere (p : ℂ) r → Φ t (diskExtension u z) = diskExtension u z) ∧
      (∀ t, MapsTo (Φ t) W W) ∧
      ((∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
          ambientDivergenceWithin g (diskExtension u) (closedHalfDisk p r) Y z) +
        ∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
          ambientDivergenceWithin g (diskExtension u ∘ conj) (closedHalfDisk p r) Y z) < 0 := by
  apply exists_supported_flow_of_fold_mean_zero g u hR hU hUr hi hir hUi hUri
    ?_ ?_ hpW hfold
  · intro r hr hrR hF hiF z
    exact fold_meanTrace_of_harmonic_conformal (openHalfDisk p r) g (diskExtension u) hF hiF
      (fun q hq => hconf q ⟨hq.1, (Metric.mem_ball.mp hq.2).trans_le hrR⟩)
      (fun q hq => htension q ⟨hq.1, (Metric.mem_ball.mp hq.2).trans_le hrR⟩) z
  · intro r hr hrR hF hiF z
    exact fold_meanTrace_of_harmonic_conformal (openHalfDisk p r) g (diskExtension u ∘ conj) hF hiF
      (fun q hq => hconfr q ⟨hq.1, (Metric.mem_ball.mp hq.2).trans_le hrR⟩)
      (fun q hq => htensionr q ⟨hq.1, (Metric.mem_ball.mp hq.2).trans_le hrR⟩) z

/-- The literal folded disk may use arbitrary smooth source coordinates.
Geometric minimality of both actual open half-sheets is derived from their
identities with reparameterizations of the original harmonic conformal map.
No conformality or flat-source harmonicity of the copied coordinates is assumed. -/
theorem exists_supported_flow_of_reparametrized_nonzero_fold
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (U₀ : ℂ → M) (ψ₁ ψ₂ : ℂ → ℂ)
    (hU₀ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₀ (Metric.ball (0 : ℂ) 1))
    (hconf₀ : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U₀ z)
    (htension₀ : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U₀ z = 0)
    {W : Set M} {p R : ℝ} (hR : 0 < R)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u) (closedHalfDisk p R))
    (hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ conj) (closedHalfDisk p R))
    (hi : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (closedHalfDisk p R) z))
    (hir : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) (closedHalfDisk p R) z))
    (hψ₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₁ (openHalfDisk p R))
    (hψ₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₂ (openHalfDisk p R))
    (hmaps₁ : MapsTo ψ₁ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1))
    (hmaps₂ : MapsTo ψ₂ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1))
    (hbij₁ : ∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₁ z))
    (hbij₂ : ∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₂ z))
    (heq₁ : EqOn (diskExtension u) (U₀ ∘ ψ₁) (openHalfDisk p R))
    (heq₂ : EqOn (diskExtension u ∘ conj) (U₀ ∘ ψ₂) (openHalfDisk p R))
    (hpW : diskExtension u (p : ℂ) ∈ interior W)
    (hfold : inwardConormalWithin g (diskExtension u) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ conj) (p : ℂ)) (diskExtension u (p : ℂ))
        (inwardConormalWithin g (diskExtension u ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0) :
    ∃ (r : ℝ) (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
      (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞),
      0 < r ∧ r ≤ R ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E x (Y x)) ∧
      HasCompactSupport Y ∧ tsupport Y ⊆ W ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => Φ t x) 0 1 = Y x) ∧
      (∀ t z, z ∈ Metric.sphere (p : ℂ) r → Φ t (diskExtension u z) = diskExtension u z) ∧
      (∀ t, MapsTo (Φ t) W W) ∧
      ((∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
          ambientDivergenceWithin g (diskExtension u) (closedHalfDisk p r) Y z) +
        ∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
          ambientDivergenceWithin g (diskExtension u ∘ conj) (closedHalfDisk p r) Y z) < 0 := by
  have hUi : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) (openHalfDisk p R) :=
    (hU₀.comp hψ₁ hmaps₁).congr (fun z hz => heq₁ hz)
  have hUri : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ conj) (openHalfDisk p R) :=
    (hU₀.comp hψ₂ hmaps₂).congr (fun z hz => heq₂ hz)
  apply exists_supported_flow_of_fold_mean_zero g u hR hU hUr hi hir hUi hUri
    ?_ ?_ hpW hfold
  · intro r hr hrR hF hiF z
    have hopen : (openHalfDisk p r : Set ℂ) ⊆ (openHalfDisk p R : Set ℂ) :=
      fun q hq => ⟨hq.1, (Metric.mem_ball.mp hq.2).trans_le hrR⟩
    have hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : openHalfDisk p r => ψ₁ q) :=
      hψ₁.comp_contMDiff contMDiff_subtype_val (fun q => hopen q.property)
    have hbij (q : openHalfDisk p r) : Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun a : openHalfDisk p r => ψ₁ a) q) := by
      rw [DifferentialGeometry.mfderiv_restrict_open]
      exact hbij₁ q (hopen q.property)
    exact inverseGram_secondFundamental_trace_eq_zero_of_harmonic_reparametrization
      (openHalfDisk p r) g U₀ (diskExtension u) ψ₁ hU₀ hψ
      (fun q hq => hmaps₁ (hopen hq)) hbij hF hiF
      (fun q hq => heq₁ (hopen hq)) hconf₀ htension₀ z
  · intro r hr hrR hF hiF z
    have hopen : (openHalfDisk p r : Set ℂ) ⊆ (openHalfDisk p R : Set ℂ) :=
      fun q hq => ⟨hq.1, (Metric.mem_ball.mp hq.2).trans_le hrR⟩
    have hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : openHalfDisk p r => ψ₂ q) :=
      hψ₂.comp_contMDiff contMDiff_subtype_val (fun q => hopen q.property)
    have hbij (q : openHalfDisk p r) : Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun a : openHalfDisk p r => ψ₂ a) q) := by
      rw [DifferentialGeometry.mfderiv_restrict_open]
      exact hbij₂ q (hopen q.property)
    exact inverseGram_secondFundamental_trace_eq_zero_of_harmonic_reparametrization
      (openHalfDisk p r) g U₀ (diskExtension u ∘ conj) ψ₂ hU₀ hψ
      (fun q hq => hmaps₂ (hopen hq)) hbij hF hiF
      (fun q hq => heq₂ (hopen hq)) hconf₀ htension₀ z

/-- The two actual halves of one literal folded disk may be reparameterized
from different harmonic conformal maps in the same original metric. This is the
replacement-filling variant: geometric minimality is proved independently for
each half before applying the same supported fold variation. -/
theorem exists_supported_flow_of_nonzero_fold_of_two_reparametrizations
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (U₁ U₂ : ℂ → M) (ψ₁ ψ₂ : ℂ → ℂ)
    (hU₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₁ (Metric.ball (0 : ℂ) 1))
    (hconf₁ : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U₁ z)
    (htension₁ : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U₁ z = 0)
    (hU₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₂ (Metric.ball (0 : ℂ) 1))
    (hconf₂ : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U₂ z)
    (htension₂ : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U₂ z = 0)
    {W : Set M} {p R : ℝ} (hR : 0 < R)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u) (closedHalfDisk p R))
    (hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ conj) (closedHalfDisk p R))
    (hi : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (closedHalfDisk p R) z))
    (hir : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) (closedHalfDisk p R) z))
    (hψ₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₁ (openHalfDisk p R))
    (hψ₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₂ (openHalfDisk p R))
    (hmaps₁ : MapsTo ψ₁ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1))
    (hmaps₂ : MapsTo ψ₂ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1))
    (hbij₁ : ∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₁ z))
    (hbij₂ : ∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₂ z))
    (heq₁ : EqOn (diskExtension u) (U₁ ∘ ψ₁) (openHalfDisk p R))
    (heq₂ : EqOn (diskExtension u ∘ conj) (U₂ ∘ ψ₂) (openHalfDisk p R))
    (hpW : diskExtension u (p : ℂ) ∈ interior W)
    (hfold : inwardConormalWithin g (diskExtension u) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ conj) (p : ℂ)) (diskExtension u (p : ℂ))
        (inwardConormalWithin g (diskExtension u ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0) :
    ∃ (r : ℝ) (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
      (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞),
      0 < r ∧ r ≤ R ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E x (Y x)) ∧
      HasCompactSupport Y ∧ tsupport Y ⊆ W ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => Φ t x) 0 1 = Y x) ∧
      (∀ t z, z ∈ Metric.sphere (p : ℂ) r → Φ t (diskExtension u z) = diskExtension u z) ∧
      (∀ t, MapsTo (Φ t) W W) ∧
      ((∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
          ambientDivergenceWithin g (diskExtension u) (closedHalfDisk p r) Y z) +
        ∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
          ambientDivergenceWithin g (diskExtension u ∘ conj) (closedHalfDisk p r) Y z) < 0 := by
  have hUi : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) (openHalfDisk p R) :=
    (hU₁.comp hψ₁ hmaps₁).congr (fun z hz => heq₁ hz)
  have hUri : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ conj) (openHalfDisk p R) :=
    (hU₂.comp hψ₂ hmaps₂).congr (fun z hz => heq₂ hz)
  apply exists_supported_flow_of_fold_mean_zero g u hR hU hUr hi hir hUi hUri
    ?_ ?_ hpW hfold
  · intro r hr hrR hF hiF z
    have hopen : (openHalfDisk p r : Set ℂ) ⊆ (openHalfDisk p R : Set ℂ) :=
      fun q hq => ⟨hq.1, (Metric.mem_ball.mp hq.2).trans_le hrR⟩
    have hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : openHalfDisk p r => ψ₁ q) :=
      hψ₁.comp_contMDiff contMDiff_subtype_val (fun q => hopen q.property)
    have hbij (q : openHalfDisk p r) : Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun a : openHalfDisk p r => ψ₁ a) q) := by
      rw [DifferentialGeometry.mfderiv_restrict_open]
      exact hbij₁ q (hopen q.property)
    exact inverseGram_secondFundamental_trace_eq_zero_of_harmonic_reparametrization
      (openHalfDisk p r) g U₁ (diskExtension u) ψ₁ hU₁ hψ
      (fun q hq => hmaps₁ (hopen hq)) hbij hF hiF
      (fun q hq => heq₁ (hopen hq)) hconf₁ htension₁ z
  · intro r hr hrR hF hiF z
    have hopen : (openHalfDisk p r : Set ℂ) ⊆ (openHalfDisk p R : Set ℂ) :=
      fun q hq => ⟨hq.1, (Metric.mem_ball.mp hq.2).trans_le hrR⟩
    have hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : openHalfDisk p r => ψ₂ q) :=
      hψ₂.comp_contMDiff contMDiff_subtype_val (fun q => hopen q.property)
    have hbij (q : openHalfDisk p r) : Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun a : openHalfDisk p r => ψ₂ a) q) := by
      rw [DifferentialGeometry.mfderiv_restrict_open]
      exact hbij₂ q (hopen q.property)
    exact inverseGram_secondFundamental_trace_eq_zero_of_harmonic_reparametrization
      (openHalfDisk p r) g U₂ (diskExtension u ∘ conj) ψ₂ hU₂ hψ
      (fun q hq => hmaps₂ (hopen hq)) hbij hF hiF
      (fun q hq => heq₂ (hopen hq)) hconf₂ htension₂ z

end DifferentialGeometry.Geometry
