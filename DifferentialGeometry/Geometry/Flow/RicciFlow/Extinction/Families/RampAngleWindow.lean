import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.GoodWindows

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

private theorem deriv_add_period_real {F : ℝ → ℝ} (hF : ∀ z, F (z + 1) = F z) (x : ℝ) :
    deriv F (x + 1) = deriv F x := by
  have hfun : (fun z => F (z + 1)) = F := funext hF
  rw [← deriv_comp_add_const (f := F) (a := 1) (x := x), hfun]

namespace CurveMap

omit [CompleteSpace E] in
theorem curvatureSq_add_period [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I Q)
    (c : CurveMap Q) (J : Set ℝ) (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (x : ℝ) :
    c.curvatureSq g (x + 1) t = c.curvatureSq g x t := by
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) (x + 1) :=
    (contMDiffOn_univ.mp (c.space_slice_contMDiffOn (I := I) J hc t ht)).mdifferentiableAt
      (by simp)
  have hsp : c.speed g (x + 1) t = c.speed g x t := c.speed_add_period g t x hγ
  have hper : c.curvatureSq g (x + 1) t * c.speed g (x + 1) t =
      c.curvatureSq g x t * c.speed g x t :=
    CurveMap.curvatureSq_speed_periodic g c J hc hi t ht x
  rw [hsp] at hper
  have hpos : c.speed g x t ≠ 0 := by
    rw [CurveMap.speed]
    exact ne_of_gt (Real.sqrt_pos.mpr ((g t).pos (c.lift x t) (c.X x t) (hi x t ht)))
  exact mul_right_cancel₀ hpos hper

end CurveMap

namespace ProductCurve

variable (c : ProductCurve Q) (g : ℝ → SmoothRiemannianMetric I Q) (lambda : ℝ)

theorem curvatureSq_add_period [SigmaCompactSpace Q] [T2Space Q] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (x : ℝ) :
    c.curvatureSq g lambda (x + 1) t = c.curvatureSq g lambda x t := by
  have hsp : ∀ z, c.speed g lambda (z + 1) t = c.speed g lambda z t :=
    speed_add_period c g lambda hc.smooth t ht
  have hang : ∀ z, c.angle g lambda (z + 1) t = c.angle g lambda z t :=
    angle_add_period c g lambda hc.smooth t ht
  have hpe : ∀ z, c.horizontalSpeedFraction g lambda (z + 1) t =
      c.horizontalSpeedFraction g lambda z t :=
    fun z => by simp only [horizontalSpeedFraction, hang z]
  have hdpe : deriv (fun z => c.horizontalSpeedFraction g lambda z t) (x + 1) =
      deriv (fun z => c.horizontalSpeedFraction g lambda z t) x :=
    deriv_add_period_real hpe x
  rw [curvatureSq_eq c g lambda hlambda hc hi (x + 1) t ht,
    curvatureSq_eq c g lambda hlambda hc hi x t ht]
  set F : ℝ → ℝ := fun z => (c.speed g lambda z t)⁻¹ * deriv (fun w => c.y w t) z with hFdef
  have hFper : ∀ z, F (z + 1) = F z := by
    intro z
    simp only [hFdef, hsp z, deriv_y_add_period c t z]
  have hFd : deriv F (x + 1) = deriv F x := deriv_add_period_real hFper x
  have hproj := CurveMap.curvatureSq_add_period g c.projection J hc.smooth.1 hi t ht x
  rw [hsp x, hpe x, hdpe, hFd, hproj]

theorem sliceRegularity [SigmaCompactSpace Q] [T2Space Q] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    ProductCurve.SliceRegularity c g lambda t where
  speed_continuous := (speed_contDiff c g lambda hc.smooth hi t ht).continuous
  curvatureSq_continuous := curvatureSq_continuous c g lambda hlambda hc hi t ht
  curvatureSq_speed_periodic := fun x => by
    change c.curvatureSq g lambda (x + 1) t * c.speed g lambda (x + 1) t =
      c.curvatureSq g lambda x t * c.speed g lambda x t
    rw [curvatureSq_add_period c g lambda hlambda hc hi t ht x,
      speed_add_period c g lambda hc.smooth t ht x]

end ProductCurve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open CurveShortening

theorem exists_lambda_small_angle {ell K eta : ℝ} (hell : 0 < ell) (hK : 0 < K)
    (heta : 0 < eta) :
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ →
        2 * lambda / ell + 2 * Real.sqrt (K * lambda) ≤ eta := by
  have hpos₁ : 0 < eta * ell / 4 := by positivity
  have hpos₂ : 0 < eta ^ 2 / (16 * K) := by positivity
  refine ⟨min 1 (min (eta * ell / 4) (eta ^ 2 / (16 * K))),
    lt_min one_pos (lt_min hpos₁ hpos₂), min_le_left _ _, ?_⟩
  intro lambda hlambda hle
  have h₁ : lambda ≤ eta * ell / 4 :=
    hle.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have h₂ : lambda ≤ eta ^ 2 / (16 * K) :=
    hle.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  have hterm₁ : 2 * lambda / ell ≤ eta / 2 := by
    rw [div_le_iff₀ hell]
    nlinarith [h₁]
  have hterm₂ : 2 * Real.sqrt (K * lambda) ≤ eta / 2 := by
    have hKlam : K * lambda ≤ (eta / 4) ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * K)] at h₂
      have heq : (eta / 4) ^ 2 = eta ^ 2 / 16 := by ring
      rw [heq, le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
      nlinarith [h₂]
    have hsqrt : Real.sqrt (K * lambda) ≤ eta / 4 :=
      (Real.sqrt_le_sqrt hKlam).trans_eq (Real.sqrt_sq (by positivity))
    linarith
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hConnected hBoundary

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem exists_lambda_ramp_angle_window
    (B : RicciBackground (I := I) (M := Q) D a b)
    (K ell eta : ℝ) (hK : 0 < K) (hell : 0 < ell) (heta : 0 < eta) :
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        (∀ t ∈ Icc a b, ell ≤ c.length B.family.metric lambda t) →
        (∀ t ∈ Icc a b, ∀ x, c.curvature B.family.metric lambda x t ≤ K) →
        ∀ t ∈ Icc a b, ∀ x, c.angle B.family.metric lambda x t ≤ eta := by
  obtain ⟨lambda₀, hpos, hle₁, hsmall⟩ := exists_lambda_small_angle hell hK heta
  refine ⟨lambda₀, hpos, hle₁, ?_⟩
  intro lambda hlambda hle c hsol hramp hdeg hlen hcurv t ht x
  have hsub : (univ : Set ℝ) ×ˢ ({t} : Set ℝ) ⊆ univ ×ˢ Icc a b :=
    Set.prod_mono subset_rfl (singleton_subset_iff.mpr ht)
  have hsmooth : c.SmoothOn (I := I) {t} :=
    ⟨hsol.smooth.1.mono hsub, hsol.smooth.2.mono hsub⟩
  have hramp' : c.IsRampOn (fun _ => B.family.metric t) lambda {t} := by
    constructor
    · intro z s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact hramp.1 z t ht
    · intro z s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact hramp.2 z t ht
  have hlen' : ell ≤ c.length (fun _ => B.family.metric t) lambda t := hlen t ht
  have hcurv' : ∀ z, c.curvature (fun _ => B.family.metric t) lambda z t ≤ K :=
    fun z => hcurv t ht z
  have hb : c.angle B.family.metric lambda x t ≤
      2 * lambda / ell + 2 * Real.sqrt (K * lambda) :=
    rfs_ramp_small_angle (B.family.metric t) c lambda t ell K hlambda hell hK hdeg
      hsmooth hramp' hlen' hcurv' x
  linarith [hb, hsmall lambda hlambda hle]

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
