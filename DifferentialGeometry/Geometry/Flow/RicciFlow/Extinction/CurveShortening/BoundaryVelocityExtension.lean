import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.BoundaryIsotopy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauFrontierReduction

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem SmoothDisk.boundaryFluxDensity_congr (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) {V V' : ∀ z : Disk, TangentSpace I (u.map z)}
    (h : ∀ x : ℝ, V (diskBoundary (x : Surgery.Topology.Circle)) =
      V' (diskBoundary (x : Surgery.Topology.Circle))) :
    u.boundaryFluxDensity g V = u.boundaryFluxDensity g V' := by
  funext x
  simp only [SmoothDisk.boundaryFluxDensity, h x]

theorem SmoothDisk.boundaryFlux_congr (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) {V V' : ∀ z : Disk, TangentSpace I (u.map z)}
    (h : ∀ x : ℝ, V (diskBoundary (x : Surgery.Topology.Circle)) =
      V' (diskBoundary (x : Surgery.Topology.Circle))) :
    u.boundaryFlux g V = u.boundaryFlux g V' := by
  rw [SmoothDisk.boundaryFlux, SmoothDisk.boundaryFlux,
    SmoothDisk.boundaryFluxDensity_congr u g h]

omit [IsManifold I ∞ Q] in
theorem SmoothDisk.isotopyVelocity_diskBoundary_eq_curveVelocity
    (u : SmoothDisk (I := I) (Q := Q)) (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (J : Set ℝ) (t₀ : ℝ) (hid : ∀ q, Phi t₀ q = q)
    (γ : ℝ → ContinuousFreeLoop Q)
    (hbdy : ∀ t ∈ J, ∀ z : Surgery.Topology.Circle, Phi t (γ t₀ z) = γ t z)
    (htrace : ∀ z : Surgery.Topology.Circle, u.map (diskBoundary z) = γ t₀ z)
    (x : ℝ) :
    (u.isotopyVelocity Phi J t₀ hid (diskBoundary (x : Surgery.Topology.Circle)) : E) =
      ((curveOfLoopFamily γ).velocity (I := I) J x t₀ : E) := by
  have hfun : ∀ t ∈ J, Phi t (u.map (diskBoundary (x : Surgery.Topology.Circle))) =
      (curveOfLoopFamily γ).lift x t := by
    intro t ht
    rw [CurveMap.lift, curveOfLoopFamily, htrace (x : Surgery.Topology.Circle)]
    exact hbdy t ht (x : Surgery.Topology.Circle)
  have hpt : Phi t₀ (u.map (diskBoundary (x : Surgery.Topology.Circle))) =
      (curveOfLoopFamily γ).lift x t₀ := by
    rw [CurveMap.lift, curveOfLoopFamily, htrace (x : Surgery.Topology.Circle)]
    exact hid (γ t₀ (x : Surgery.Topology.Circle))
  have hmain := mfderivWithin_congr (I := 𝓘(ℝ, ℝ)) (I' := I)
    (f₁ := fun t : ℝ => Phi t (u.map (diskBoundary (x : Surgery.Topology.Circle))))
    (f := fun t : ℝ => (curveOfLoopFamily γ).lift x t) (s := J) (x := t₀) hfun hpt
  have hval := congrArg (fun L : (TangentSpace 𝓘(ℝ, ℝ) t₀ →L[ℝ]
      TangentSpace I (Phi t₀ (u.map (diskBoundary (x : Surgery.Topology.Circle))))) => L 1) hmain
  change ((mfderivWithin 𝓘(ℝ, ℝ) I
      (fun t : ℝ => Phi t (u.map (diskBoundary (x : Surgery.Topology.Circle)))) J t₀ 1 :
        TangentSpace I (Phi t₀ (u.map (diskBoundary (x : Surgery.Topology.Circle))))) : E) =
    (((curveOfLoopFamily γ).velocity (I := I) J x t₀ :
      TangentSpace I ((curveOfLoopFamily γ).lift x t₀)) : E)
  exact congrArg (fun w => (w : E)) hval

omit [IsManifold I ∞ Q] in
theorem SmoothDisk.isotopyVelocity_congr_of_mem_nhds
    (u : SmoothDisk (I := I) (Q := Q)) (Phi : ℝ → Diffeomorph I I Q Q ∞)
    {J J' : Set ℝ} (t₀ : ℝ) (hid : ∀ q, Phi t₀ q = q) (hJ : J ∈ 𝓝 t₀)
    (hJ' : J' ∈ 𝓝 t₀) :
    u.isotopyVelocity Phi J t₀ hid = u.isotopyVelocity Phi J' t₀ hid := by
  funext z
  change mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) J t₀ 1 =
    mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) J' t₀ 1
  rw [mfderivWithin_of_mem_nhds hJ, mfderivWithin_of_mem_nhds hJ']

theorem transportedAreaFirstVariation_of_isotopy_smoothOn_nhds
    [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Q] [CompactSpace Q] [SigmaCompactSpace Q]
    {D : RealTimeInterval} {a b : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ico a b)
    (u : SmoothDisk (I := I) (Q := Q)) (hconformal : u.IsConformal (W.family.metric t₀))
    (hharmonic : u.IsHarmonic (W.family.metric t₀))
    (Phi : ℝ → Diffeomorph I I Q Q ∞) {T : Set ℝ} (hTopen : IsOpen T) (hT₀ : t₀ ∈ T)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ T))
    (hid : ∀ q, Phi t₀ q = q) :
    TransportedAreaFirstVariation W t₀ ht₀ u Phi hid := by
  classical
  let c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E :=
    DifferentialGeometry.Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q :=
    DifferentialGeometry.Geometry.Topology.StandardModelCopy.compactSpace c
  have hreg : D.regular ∈ 𝓝 t₀ :=
    D.regular_isOpen.mem_nhds (W.regular ⟨ht₀.1, ht₀.2.le⟩)
  obtain ⟨-, hFluxT, hDerivT⟩ :=
    SmoothDisk.hasDerivAt_transportedArea_isotopy_flux c W.smooth hreg u hconformal hharmonic
      hTopen hT₀ Phi hPhi hid
  have hslice (z : Disk) :
      MDifferentiableAt 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) t₀ :=
    ((hPhi.contMDiffAt ((isOpen_univ.prod hTopen).mem_nhds ⟨mem_univ _, hT₀⟩)).comp t₀
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hvel : u.isotopyVelocity Phi (Icc a b) t₀ hid =
      u.isotopyVelocity Phi T t₀ hid := by
    funext z
    change mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) (Icc a b) t₀ 1 =
      mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) T t₀ 1
    exact congrArg (fun L => L 1)
      (mfderivWithin_Icc_eq_mfderivWithin_of_isOpen ht₀ (hslice z) hTopen hT₀)
  have hdiff₁ (z : Disk) : DifferentiableAt ℝ (fun t : ℝ =>
      (W.family.metric t).inner (u.map z) (u.differential z (1 : ℂ))
        (u.differential z (1 : ℂ))) t₀ :=
    ((W.smooth.coeff (u.map z) (u.differential z (1 : ℂ))
      (u.differential z (1 : ℂ))).contDiffAt hreg).differentiableAt (by simp)
  have hdiff₂ (z : Disk) : DifferentiableAt ℝ (fun t : ℝ =>
      (W.family.metric t).inner (u.map z) (u.differential z Complex.I)
        (u.differential z Complex.I)) t₀ :=
    ((W.smooth.coeff (u.map z) (u.differential z Complex.I)
      (u.differential z Complex.I)).contDiffAt hreg).differentiableAt (by simp)
  have hdensInt : (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric T t₀) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z := by
    refine setIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
    rw [show diskExtension (u.metricVariationDensity W.family.metric T t₀) z =
        u.metricVariationDensity W.family.metric T t₀ ⟨z, hz⟩ from dif_pos hz,
      show diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z =
        u.metricVariationDensity W.family.metric (Icc a b) t₀ ⟨z, hz⟩ from dif_pos hz]
    simp only [SmoothDisk.metricVariationDensity]
    split_ifs with hpos
    · rw [derivWithin_of_mem_nhds (hTopen.mem_nhds hT₀),
        derivWithin_of_mem_nhds (hTopen.mem_nhds hT₀),
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀ (hdiff₁ ⟨z, hz⟩),
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀ (hdiff₂ ⟨z, hz⟩)]
    · rfl
  refine ⟨?_, ?_⟩
  · rw [hvel]
    exact hFluxT
  · have hb : HasDerivWithinAt (u.transportedArea W.family.metric Phi)
        ((1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (u.metricVariationDensity W.family.metric T t₀) z) -
          u.boundaryFlux (W.family.metric t₀) (u.isotopyVelocity Phi T t₀ hid))
        (Icc a b) t₀ := hDerivT.hasDerivWithinAt
    convert hb using 1
    rw [hdensInt, hvel]

theorem exists_diskBoundaryVelocityExtension_of_loopFamilyVelocityExtension
    [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Q] [CompactSpace Q] [SigmaCompactSpace Q]
    {a b : ℝ} (γ : ℝ → ContinuousFreeLoop Q) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b)
    (hvel : LoopFamilyVelocityExtension (I := I) a b γ)
    (u : SmoothDisk (I := I) (Q := Q))
    (htrace : ∀ z : Surgery.Topology.Circle, u.map (diskBoundary z) = γ t₀ z) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I Q Q ∞, ∃ hid : ∀ q, Φ t₀ q = q,
      (∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z : Surgery.Topology.Circle,
        Φ t (γ t₀ z) = γ t z) ∧
      ∀ x : ℝ, (u.isotopyVelocity Φ (Icc a b) t₀ hid
          (diskBoundary (x : Surgery.Topology.Circle)) : E) =
        ((curveOfLoopFamily γ).velocity (I := I) (Icc a b) x t₀ : E) := by
  obtain ⟨ε, hε, Φ, hΦ, hid, htraj⟩ :=
    rfs_csf_boundary_isotopy_of_velocityExtension a b γ t₀ ⟨ht₀.1.le, ht₀.2.le⟩ hvel
  have hS : Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε) ∈ 𝓝 t₀ :=
    Filter.inter_mem (Icc_mem_nhds_iff.mpr ⟨ht₀.1, ht₀.2⟩)
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  refine ⟨ε, hε, Φ, hid, htraj, fun x => ?_⟩
  have hIcc : Icc a b ∈ 𝓝 t₀ := Icc_mem_nhds_iff.mpr ⟨ht₀.1, ht₀.2⟩
  have hvelIcc : (curveOfLoopFamily γ).velocity (I := I) (Icc a b) x t₀ =
      (curveOfLoopFamily γ).velocity (I := I)
        (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε)) x t₀ := by
    simp only [CurveMap.velocity, CurveMap.lift, curveOfLoopFamily]
    rw [mfderivWithin_of_mem_nhds hIcc, mfderivWithin_of_mem_nhds hS]
  rw [SmoothDisk.isotopyVelocity_congr_of_mem_nhds u Φ t₀ hid hIcc hS, hvelIcc]
  exact SmoothDisk.isotopyVelocity_diskBoundary_eq_curveVelocity u Φ _ t₀ hid γ htraj htrace x

theorem exists_transportedAreaFirstVariation_of_loopFamilyVelocityExtension
    [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Q] [CompactSpace Q] [SigmaCompactSpace Q]
    {D : RealTimeInterval} {a b : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (γ : ℝ → ContinuousFreeLoop Q) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b)
    (hvel : LoopFamilyVelocityExtension (I := I) a b γ)
    (u : SmoothDisk (I := I) (Q := Q)) (hconformal : u.IsConformal (W.family.metric t₀))
    (hharmonic : u.IsHarmonic (W.family.metric t₀)) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I Q Q ∞, ∃ hid : ∀ q, Φ t₀ q = q,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Ioo a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z : Surgery.Topology.Circle,
        Φ t (γ t₀ z) = γ t z) ∧
      TransportedAreaFirstVariation W t₀ ⟨ht₀.1.le, ht₀.2⟩ u Φ hid := by
  obtain ⟨ε, hε, Φ, hΦ, hid, htraj⟩ :=
    rfs_csf_boundary_isotopy_of_velocityExtension a b γ t₀ ⟨ht₀.1.le, ht₀.2.le⟩ hvel
  have hsub : Ioo a b ∩ Ioo (t₀ - ε) (t₀ + ε) ⊆ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε) :=
    fun t ht => ⟨⟨ht.1.1.le, ht.1.2.le⟩, ht.2⟩
  refine ⟨ε, hε, Φ, hid, hΦ.mono (Set.prod_mono Subset.rfl hsub), htraj, ?_⟩
  exact transportedAreaFirstVariation_of_isotopy_smoothOn_nhds W t₀ ⟨ht₀.1.le, ht₀.2⟩ u
    hconformal hharmonic Φ (isOpen_Ioo.inter isOpen_Ioo)
    ⟨ht₀, by constructor <;> linarith⟩ (hΦ.mono (Set.prod_mono Subset.rfl hsub)) hid

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
