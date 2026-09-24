import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProjectedAreaBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialRampBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampLengthEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.UniformRampFrontier

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hConnected hBoundary

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ Q] [SigmaCompactSpace Q]
  hT2 hCompact hConnected hBoundary in
private theorem productCurve_slice_sub_const_of_map_eq_initialRamp (c : ProductCurve Q)
    (γ : Surgery.Topology.Circle → Q) (t : ℝ) (hc : c.SmoothOn (I := I) {t})
    (hmap : ∀ z : Surgery.Topology.Circle, c.map z t = (γ z, z)) :
    ∃ k : ℝ, ∀ x, c.y x t = x + k := by
  have hcy : Continuous fun x : ℝ => c.y x t := by
    have hz : ContDiffOn ℝ ∞ (fun z : ℝ => (z, t)) univ := by fun_prop
    have h := hc.2.comp hz (fun z _ => ⟨mem_univ z, mem_singleton t⟩)
    exact continuousOn_univ.mp h.continuousOn
  have hcont : Continuous fun x : ℝ => c.y x t - x := hcy.sub continuous_id
  have hint : ∀ x, ∃ n : ℤ, c.y x t - x = (n : ℝ) := by
    intro x
    have hcoe : ((c.y x t - x : ℝ) : Surgery.Topology.Circle) = 0 := by
      rw [AddCircle.coe_sub, c.lift_eq x t, hmap (x : Surgery.Topology.Circle)]
      simp
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcoe
    exact ⟨n, by simpa using hn.symm⟩
  have hconst : ∀ x, c.y x t - x = c.y 0 t - 0 := by
    intro x
    obtain ⟨n, hn⟩ := hint x
    obtain ⟨m, hm⟩ := hint 0
    have hnm : n = m := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hmem : (c.y x t - x) + 1 / 2 ∈
            Set.Icc (c.y x t - x) (c.y 0 t - 0) := by
          refine ⟨by linarith, ?_⟩
          have h1 : n + 1 ≤ m := by omega
          have h2 : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h1
          rw [hn, hm]
          linarith
        obtain ⟨z, _, hz⟩ := isPreconnected_univ.intermediate_value (Set.mem_univ x)
          (Set.mem_univ 0) hcont.continuousOn hmem
        obtain ⟨nz, hnz⟩ := hint z
        have hz' : (nz : ℝ) = (n : ℝ) + 1 / 2 := by
          rw [← hnz]
          simpa only [hn] using hz
        have hcast : ((2 * nz : ℤ) : ℝ) = ((2 * n + 1 : ℤ) : ℝ) := by push_cast; linarith
        have hzi : 2 * nz = 2 * n + 1 := Int.cast_inj.mp hcast
        omega
      · have hmem : (c.y 0 t - 0) + 1 / 2 ∈
            Set.Icc (c.y 0 t - 0) (c.y x t - x) := by
          refine ⟨by linarith, ?_⟩
          have h1 : m + 1 ≤ n := by omega
          have h2 : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
          rw [hn, hm]
          linarith
        obtain ⟨z, _, hz⟩ := isPreconnected_univ.intermediate_value (Set.mem_univ 0)
          (Set.mem_univ x) hcont.continuousOn hmem
        obtain ⟨nz, hnz⟩ := hint z
        have hz' : (nz : ℝ) = (m : ℝ) + 1 / 2 := by
          rw [← hnz]
          simpa only [hm] using hz
        have hcast : ((2 * nz : ℤ) : ℝ) = ((2 * m + 1 : ℤ) : ℝ) := by push_cast; linarith
        have hzi : 2 * nz = 2 * m + 1 := Int.cast_inj.mp hcast
        omega
    rw [hn, hm, hnm]
  exact ⟨c.y 0 t, fun x => by linarith [hconst x]⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ Q] [SigmaCompactSpace Q]
  hT2 hCompact hConnected hBoundary in
theorem productCurve_degree_eq_one_of_map_eq_initialRamp (c : ProductCurve Q)
    (γ : Surgery.Topology.Circle → Q) (t : ℝ) (hc : c.SmoothOn (I := I) {t})
    (hmap : ∀ z : Surgery.Topology.Circle, c.map z t = (γ z, z)) :
    c.degree = 1 := by
  obtain ⟨k, hk⟩ := productCurve_slice_sub_const_of_map_eq_initialRamp c γ t hc hmap
  have h0 : c.y 0 t = (0 : ℝ) + k := hk 0
  have h1 : c.y (0 + 1) t = ((0 : ℝ) + 1) + k := hk (0 + 1)
  have hinc : c.y (0 + 1) t = c.y 0 t + (c.degree : ℝ) := c.increment 0 t
  have hz : (c.degree : ℝ) = 1 := by linarith
  exact_mod_cast hz


omit [SigmaCompactSpace Q] in
theorem rampAreaBounds_of_projection_frontiers
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hslope : curveShorteningLeastAreaSlope (I := I) (M := Q) B)
    (hcurv : curveShorteningTotalCurvatureBound (I := I) (M := Q) B)
    (Ainit : ℝ) (hAinit : 0 ≤ Ainit) :
    RampAreaBounds (I := I) (Q := Q) (D := D) (a := a) (b := b) B Ainit := by
  intro L Theta hL hTheta lambda hlambda hlambda_one c hsol hlen htot γ hγ hctr hLa
  have hagree : ∀ z t, t ∈ Icc a b → γ t z = c.projection z t := fun z t ht => hγ t ht z
  have hγsmooth : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) := by
    rw [CurveMap.SmoothOn]
    refine hsol.smooth.1.congr ?_
    intro p hp
    exact hagree (p.1 : AddCircle (1 : ℝ)) p.2 hp.2
  have hcont := continuousOn_loopFamilyLeastArea_of_contractible B γ hγsmooth hctr
  obtain ⟨hrange, hslopeBound⟩ := rfs_csf_projection_upper_control B hslope hcurv L Theta Ainit hL
    hTheta hAinit lambda hlambda hlambda_one c hsol γ hagree hctr hcont hlen htot hLa
  exact ⟨hcont, hrange, hslopeBound⟩

omit [SigmaCompactSpace Q] in
theorem rampUniformBoundsInput_of_extinction_frontiers
    (B : RicciBackground (I := I) (M := Q) D a b) (Ainit : ℝ) (hAinit : 0 ≤ Ainit)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (hcurv : curveShorteningTotalCurvatureBound (I := I) (M := Q) B)
    (hslope : curveShorteningLeastAreaSlope (I := I) (M := Q) B) :
    RampUniformBoundsInput (I := I) (Q := Q) (D := D) (a := a) (b := b) B Ainit :=
  ⟨rfs_rampProductBounds_of_length_evolution B hev hcurv,
    rampAreaBounds_of_projection_frontiers B hslope hcurv Ainit hAinit⟩

theorem rfs_rampFamilyFlowSolutions_of_ramp_frontiers
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hsmooth : HasContinuousSmoothLoopJets e prepared)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    (hinit : @Continuous (Sphere 2) (ProductCurve Q) inferInstance
      (smoothProductInitialTopology e a) (fun p => initialRamp ((prepared p).1)))
    (K : RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (L : RampFamilyInput (I := I) (M := Q) (D := D) (a := a) (b := b) (N := d) B lambda e) :
    RampFamilyFlowSolutions (I := I) (Q := Q) (D := D) (a := a) (b := b) B e prepared lambda := by
  have haI : ({a} : Set ℝ) ⊆ Icc a b := by
    intro x hx
    rw [mem_singleton_iff] at hx
    subst hx
    exact ⟨le_rfl, B.lt.le⟩
  have hsmooth_at : ∀ p : Sphere 2,
      (initialRamp ((prepared p).1)).SmoothOn (I := I) {a} := by
    intro p
    have hγmd : ContMDiff 𝓘(ℝ, ℝ) I ∞
        (fun t : ℝ => ((prepared p).1).toContinuousLoop (t : Surgery.Topology.Circle)) :=
      hsmooth.1 p
    obtain ⟨h1, h2⟩ := initialRamp_smoothOn (I := I) (Q := Q)
      (γ := ((prepared p).1).toContinuousLoop) hγmd
    exact ⟨h1.mono (Set.prod_mono Subset.rfl (Set.subset_univ _)),
      h2.mono (Set.prod_mono Subset.rfl (Set.subset_univ _))⟩
  have hramp_at : ∀ p : Sphere 2,
      (initialRamp ((prepared p).1)).IsRampOn B.family.metric lambda {a} := by
    intro p
    refine ⟨fun x t _ => initialRamp_immersedOn ((prepared p).1) x t trivial, fun x t ht => ?_⟩
    rw [mem_singleton_iff] at ht
    rw [ht]
    simpa only [ProductCurve.angle, ProductCurve.unitTangent, ProductCurve.speed,
      ProductCurve.inner] using
      initialRamp_angle_pos (B.family.metric a) hlambda ((prepared p).1) x a
  obtain ⟨solutions, hcont, hdata⟩ := rfs_csf_ramp_family B lambda hlambda hlambda_one e
    (fun p : Sphere 2 => initialRamp ((prepared p).1)) hinit hsmooth_at hramp_at K L
  refine ⟨solutions, hcont, fun p => ⟨(hdata p).1, (hdata p).2.1, ?_, ?_⟩⟩
  · exact productCurve_degree_eq_one_of_map_eq_initialRamp (solutions p)
      (((prepared p).1).toContinuousLoop) a
      ⟨(hdata p).1.smooth.1.mono (Set.prod_mono Subset.rfl haI),
        (hdata p).1.smooth.2.mono (Set.prod_mono Subset.rfl haI)⟩
      (fun z => by rw [(hdata p).2.2 z]; rfl)
  · intro z
    rw [(hdata p).2.2 z]
    rfl


end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
