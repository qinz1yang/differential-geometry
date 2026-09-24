import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProjectedAreaVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution.Immersed
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.AffineComparison

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [T2Space Q] [CompactSpace Q] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

theorem projected_leastArea_slope_le_of_angle_le
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3) {lambda eta L Theta : ℝ}
    (hlambda : 0 < lambda) (heta : 0 ≤ eta) (heta_one : eta < 1)
    (hL : 0 ≤ L) (hTheta : 0 ≤ Theta) (c : ProductCurve Q)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc a b))
    (hlen : c.length B.family.metric lambda a ≤ L)
    (hcurv : c.totalCurvature B.family.metric lambda a ≤ Theta)
    (γ : ℝ → ContinuousFreeLoop Q)
    (hγ : ∀ s ∈ Icc a b, ∀ z, γ s z = c.projection z s)
    (hctr : ∀ s ∈ Icc a b, IsContractibleLoop (γ s))
    {t : ℝ} (ht : t ∈ Ico a b)
    (hu : ∀ x, |c.angle B.family.metric lambda x t| ≤ eta) :
    ∀ eps > 0, ∃ dd > 0, ∀ h ∈ Ioo (0 : ℝ) dd, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        -2 * Real.pi - halfScalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t +
          eta ^ 2 / Real.sqrt (1 - eta ^ 2) * ((Theta + L) * Real.exp ((B.C + B.B₀) * (b - a))) + eps := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : Nonempty Q := ⟨γ a 0⟩
  obtain ⟨τ, hτ, hτb, hi, herr⟩ :=
    c.exists_projection_immersedOn_areaError_le B.family.metric hlambda hc ht heta heta_one hu
  have htb : t + τ ≤ b := by linarith
  have htt : t < t + τ := by linarith
  have hsub : Icc t (t + τ) ⊆ Icc a b := Icc_subset_Icc ht.1 htb
  let B' : RicciBackground (I := I) (M := Q) D t (t + τ) :=
    { family := B.family
      smooth := B.smooth
      lt := htt
      regular := fun s hs => B.regular (hsub hs)
      equation := B.equation
      B₀ := B.B₀
      B₁ := B.B₁
      B₂ := B.B₂
      B₀_nonneg := B.B₀_nonneg
      B₁_nonneg := B.B₁_nonneg
      B₂_nonneg := B.B₂_nonneg
      ricci_bound := fun s hs p => B.ricci_bound s (hsub hs) p
      riemann_bound := fun s hs p => B.riemann_bound s (hsub hs) p
      nablaRicci_bound := fun s hs p => B.nablaRicci_bound s (hsub hs) p }
  have hagree : ∀ z s, s ∈ Icc t (t + τ) → (curveOfLoopFamily γ) z s = c.projection z s :=
    fun z s hs => hγ s (hsub hs) z
  have hγsmooth : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc t (t + τ)) := by
    refine (hc.smooth.1.mono (Set.prod_mono Subset.rfl hsub)).congr ?_
    intro p hp
    exact hagree (p.1 : Surgery.Topology.Circle) p.2 hp.2
  have hγi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc t (t + τ)) := by
    intro x s hs
    have hX := CurveMap.X_congr (I := I) (c := curveOfLoopFamily γ) (d := c.projection)
      (t := s) (fun y : ℝ => hagree (y : Surgery.Topology.Circle) s hs) x
    rw [hX]
    exact hi x s hs
  have htJ : t ∈ Icc t (t + τ) := ⟨le_rfl, htt.le⟩
  have herror : (curveOfLoopFamily γ).areaError B.family.metric (Icc t (t + τ)) t ≤
      eta ^ 2 / Real.sqrt (1 - eta ^ 2) * c.totalCurvature B.family.metric lambda t := by
    rw [CurveMap.areaError_congr hagree t htJ]
    exact herr
  have hThetaBound : c.totalCurvature B.family.metric lambda t ≤ ((Theta + L) * Real.exp ((B.C + B.B₀) * (b - a))) := by
    have hsum := c.totalCurvature_add_length_le_exp B lambda hlambda (uniqueDiffOn_Icc B.lt)
      hc B.lt Subset.rfl Subset.rfl a t ⟨le_rfl, B.lt.le⟩ ⟨ht.1, ht.2.le⟩
    have hC : 0 ≤ B.C + B.B₀ := by
      rw [RicciBackground.C]
      nlinarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
    have hgrow : Real.exp ((B.C + B.B₀) * (t - a)) ≤
        Real.exp ((B.C + B.B₀) * (b - a)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hC)
    have hbound := (hsum.trans
      (mul_le_mul_of_nonneg_left (add_le_add hcurv hlen) (Real.exp_nonneg _))).trans
        (mul_le_mul_of_nonneg_right hgrow (add_nonneg hTheta hL))
    have hnonneg := ProductCurve.length_nonneg B.family.metric lambda t c
    nlinarith [hbound]
  have herror' : (curveOfLoopFamily γ).areaError B.family.metric (Icc t (t + τ)) t ≤
      eta ^ 2 / Real.sqrt (1 - eta ^ 2) * ((Theta + L) * Real.exp ((B.C + B.B₀) * (b - a))) :=
    herror.trans (mul_le_mul_of_nonneg_left hThetaBound
      (div_nonneg (sq_nonneg eta) (Real.sqrt_nonneg _)))
  intro eps heps
  obtain ⟨δ, hδ, hslope⟩ :=
    (rfs_csf_immersed_area B' hdim γ hγsmooth hγi (fun s hs => hctr s (hsub hs))).2.2
      t ⟨le_rfl, htt⟩ eps heps
  refine ⟨min δ τ, lt_min hδ hτ, fun h hh _ => ?_⟩
  have hhδ : h < δ := hh.2.trans_le (min_le_left _ _)
  have hhτ : h < τ := hh.2.trans_le (min_le_right _ _)
  have hbound := hslope h ⟨hh.1, hhδ⟩ (by linarith)
  change (loopFamilyLeastArea B.family.metric γ (t + h) - loopFamilyLeastArea B.family.metric γ t) / h ≤
    -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
      (curveOfLoopFamily γ).areaError B.family.metric (Icc t (t + τ)) t + eps at hbound
  dsimp only [halfScalarMinimum]
  nlinarith [hbound, herror']

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
