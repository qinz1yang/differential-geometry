import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProjectedAreaBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SweptAnnulus
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductLengthEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Preparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection



noncomputable section

open Bundle Manifold Set MeasureTheory
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

theorem rfs_prepared_family_flow (B : RicciBackground (I := I) (M := Q) D a b)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hsmooth : HasContinuousSmoothLoopJets e prepared)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1) :
    ∃ solutions : Sphere 2 → ProductCurve Q,
      ∃ projected : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
        @Continuous (Sphere 2) (ProductCurve Q) inferInstance
          (smoothProductCylinderTopology e (Icc a b)) solutions ∧
        (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
          (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
          (solutions p).degree = 1 ∧
          ∀ z, (solutions p).map z a = ((prepared p).1 z, z)) ∧
        (∀ t : Icc a b, ∀ p z,
          ((projected t) p).1 z = (solutions p).projection z t) ∧
        projected ⟨a, le_rfl, B.lt.le⟩ = prepared ∧
        (∀ t : Icc a b, HasContinuousSmoothLoopJets e (projected t)) ∧
        ∀ t : Icc a b,
          FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (projected t)) =
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp prepared) := by
  sorry


private def rampThetabar (B₀ C L₀ Θ₀ a b : ℝ) : ℝ :=
  (Θ₀ + L₀) * Real.exp ((C + B₀) * (b - a))

private def rampAbar (B₀ C L₀ Θ₀ A a b : ℝ) : ℝ :=
  Real.exp (2 * B₀ * (b - a)) * (A + (b - a) * rampThetabar B₀ C L₀ Θ₀ a b)

private def rampCup (B₀ C L₀ Θ₀ A a b : ℝ) : ℝ :=
  Real.exp (2 * B₀ * (b - a)) * (2 * B₀ * rampAbar B₀ C L₀ Θ₀ A a b +
    rampThetabar B₀ C L₀ Θ₀ a b)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace Q] hT2 hCompact hConnected
  hBoundary in
theorem productCurve_length_nonneg (g : ℝ → SmoothRiemannianMetric I Q) (lambda t : ℝ)
    (c : ProductCurve Q) : 0 ≤ c.length g lambda t := by
  rw [ProductCurve.length, ProductCurve.integral]
  exact intervalIntegral.integral_nonneg zero_le_one
    (fun x _ => mul_nonneg zero_le_one (c.speed_nonneg g lambda x t))

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_ramp_uniform_bounds_of_product_bounds
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (hproduct : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
      ∀ t ∈ Icc a b,
        c.length B.family.metric lambda t ≤ Real.exp (B.B₀ * (t - a)) * L₀ ∧
        (∫ v in a..t, c.energy B.family.metric lambda v) ≤
          Real.exp (B.B₀ * (t - a)) * L₀ ∧
        c.totalCurvature B.family.metric lambda t + c.length B.family.metric lambda t ≤
          Real.exp ((B.C + B.B₀) * (t - a)) * (Theta₀ + L₀))
    (harea : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      ∀ γ : ℝ → ContinuousFreeLoop Q,
        (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
        ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ t ∈ Icc a b, 0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
          loopFamilyLeastArea B.family.metric γ t ≤
            rampAbar B.B₀ B.C L₀ Theta₀ Ainit a b) ∧
        (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
            rampCup B.B₀ B.C L₀ Theta₀ Ainit a b * (t - s))) :
    let delta := b - a
    let Lbar := Real.exp (B.B₀ * delta) * L₀
    let Thetabar := (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * delta)
    let Abar := Real.exp (2 * B.B₀ * delta) * (Ainit + delta * Thetabar)
    let Cup := Real.exp (2 * B.B₀ * delta) * (2 * B.B₀ * Abar + Thetabar)
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      ∀ γ : ℝ → ContinuousFreeLoop Q,
        (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
        ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ t ∈ Icc a b,
          c.length B.family.metric lambda t ≤ Lbar ∧
          c.totalCurvature B.family.metric lambda t ≤ Thetabar ∧
          0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
          loopFamilyLeastArea B.family.metric γ t ≤ Abar) ∧
        (∫ t in a..b, c.energy B.family.metric lambda t) ≤ Lbar ∧
        ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
            Cup * (t - s) := by
  dsimp only [rampThetabar, rampAbar, rampCup]
  let _ := hAinit
  intro lambda hlambda hlambda_one c hsol _hramp _hdeg γ hγ hctr hlen0 hcurv0 hAinit0
  have hC : 0 ≤ B.C + B.B₀ := by
    rw [RicciBackground.C]
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hTnn : 0 ≤ Theta₀ + L₀ := by linarith
  obtain ⟨hcont, hrange, hslope⟩ :=
    harea lambda hlambda hlambda_one c hsol γ hγ hctr hlen0 hcurv0 hAinit0
  have hkeys := hproduct lambda hlambda hlambda_one c hsol hlen0 hcurv0
  refine ⟨hcont, ?_, ?_, fun s hs t ht => ?_⟩
  · intro t ht
    have hlen_le : c.length B.family.metric lambda t ≤
        Real.exp (B.B₀ * (b - a)) * L₀ :=
      (hkeys t ht).1.trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2]) B.B₀_nonneg)) hL₀)
    have hcurv_le : c.totalCurvature B.family.metric lambda t ≤
        (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * (b - a)) := by
      have hexp : Real.exp ((B.C + B.B₀) * (t - a)) ≤
          Real.exp ((B.C + B.B₀) * (b - a)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hC)
      have hstep : Real.exp ((B.C + B.B₀) * (t - a)) * (Theta₀ + L₀) ≤
          (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * (b - a)) := by
        rw [mul_comm (Real.exp ((B.C + B.B₀) * (t - a))) (Theta₀ + L₀)]
        exact mul_le_mul_of_nonneg_left hexp hTnn
      have hlen_nn := productCurve_length_nonneg B.family.metric lambda t c
      linarith [(hkeys t ht).2.2, hstep, hlen_nn]
    exact ⟨hlen_le, hcurv_le, (hrange t ht).1, (hrange t ht).2⟩
  · have hb := (hkeys b ⟨B.lt.le, le_rfl⟩).2.1
    simpa only [sub_self] using hb
  · exact hslope s hs t ht

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ Q] [SigmaCompactSpace Q]
  hT2 hCompact hConnected hBoundary in
private theorem productCurve_slice_y_sub_const (c c₀ : ProductCurve Q) (t t₀ : ℝ)
    (hc : c.SmoothOn (I := I) {t}) (hc₀ : c₀.SmoothOn (I := I) {t₀})
    (hmap : ∀ z, c.map z t = c₀.map z t₀) :
    ∃ k : ℝ, ∀ x, c.y x t - c₀.y x t₀ = k := by
  have hcy : Continuous (fun x : ℝ => c.y x t) := by
    have hz : ContDiffOn ℝ ∞ (fun z : ℝ => (z, t)) univ := by fun_prop
    have h := hc.2.comp hz (fun z _ => ⟨mem_univ z, mem_singleton t⟩)
    exact continuousOn_univ.mp h.continuousOn
  have hc₀y : Continuous (fun x : ℝ => c₀.y x t₀) := by
    have hz : ContDiffOn ℝ ∞ (fun z : ℝ => (z, t₀)) univ := by fun_prop
    have h := hc₀.2.comp hz (fun z _ => ⟨mem_univ z, mem_singleton t₀⟩)
    exact continuousOn_univ.mp h.continuousOn
  have hcont : Continuous (fun x : ℝ => c.y x t - c₀.y x t₀) := hcy.sub hc₀y
  have hint : ∀ x, ∃ n : ℤ, c.y x t - c₀.y x t₀ = (n : ℝ) := by
    intro x
    have hcoe : ((c.y x t - c₀.y x t₀ : ℝ) : Surgery.Topology.Circle) = 0 := by
      rw [AddCircle.coe_sub, c.lift_eq x t, c₀.lift_eq x t₀, hmap (x : Surgery.Topology.Circle),
        sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcoe
    exact ⟨n, by simpa using hn.symm⟩
  have hconst : ∀ x, c.y x t - c₀.y x t₀ = c.y 0 t - c₀.y 0 t₀ := by
    intro x
    obtain ⟨n, hn⟩ := hint x
    obtain ⟨m, hm⟩ := hint 0
    have hnm : n = m := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hmem : (c.y x t - c₀.y x t₀) + 1 / 2 ∈
            Set.Icc (c.y x t - c₀.y x t₀) (c.y 0 t - c₀.y 0 t₀) := by
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
      · have hmem : (c.y 0 t - c₀.y 0 t₀) + 1 / 2 ∈
            Set.Icc (c.y 0 t - c₀.y 0 t₀) (c.y x t - c₀.y x t₀) := by
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
  exact ⟨c.y 0 t - c₀.y 0 t₀, hconst⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace Q]
  hT2 hCompact hConnected hBoundary in
private theorem productCurve_slice_speed_eq (g : SmoothRiemannianMetric I Q) (lambda : ℝ)
    (c c₀ : ProductCurve Q) (t t₀ : ℝ)
    (hc : c.SmoothOn (I := I) {t}) (hc₀ : c₀.SmoothOn (I := I) {t₀})
    (hmap : ∀ z, c.map z t = c₀.map z t₀) :
    ∀ x, c.speed (fun _ => g) lambda x t = c₀.speed (fun _ => g) lambda x t₀ := by
  obtain ⟨k, hk⟩ := productCurve_slice_y_sub_const c c₀ t t₀ hc hc₀ hmap
  have hky : (fun z : ℝ => c.y z t) = fun z : ℝ => c₀.y z t₀ + k := by
    funext z
    linarith [hk z]
  have hd : ∀ x, deriv (fun z : ℝ => c.y z t) x = deriv (fun z : ℝ => c₀.y z t₀) x := by
    intro x
    rw [hky, deriv_add_const]
  have hM : (fun y : ℝ => (c.map (y : Surgery.Topology.Circle) t).1) =
      fun y : ℝ => (c₀.map (y : Surgery.Topology.Circle) t₀).1 := by
    funext y
    exact congrArg Prod.fst (hmap (y : Surgery.Topology.Circle))
  intro x
  have hxM : (c.map (x : Surgery.Topology.Circle) t).1 =
      (c₀.map (x : Surgery.Topology.Circle) t₀).1 :=
    congrArg Prod.fst (hmap (x : Surgery.Topology.Circle))
  simp only [ProductCurve.speed, ProductCurve.inner, ProductCurve.X, ProductCurve.projection,
    CurveMap.lift, CurveMap.X]
  rw [hM, hxM, hd x]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace Q] hT2 hCompact hConnected hBoundary in
private theorem productCurve_slice_curvatureSq_eq (g : SmoothRiemannianMetric I Q) (lambda : ℝ)
    (c c₀ : ProductCurve Q) (t t₀ : ℝ)
    (hc : c.SmoothOn (I := I) {t}) (hc₀ : c₀.SmoothOn (I := I) {t₀})
    (hmap : ∀ z, c.map z t = c₀.map z t₀) :
    ∀ x, c.curvatureSq (fun _ => g) lambda x t =
      c₀.curvatureSq (fun _ => g) lambda x t₀ := by
  obtain ⟨k, hk⟩ := productCurve_slice_y_sub_const c c₀ t t₀ hc hc₀ hmap
  have hY : (fun z : ℝ => deriv (fun w : ℝ => c.y w t) z) =
      fun z : ℝ => deriv (fun w : ℝ => c₀.y w t₀) z := by
    funext z
    have hky : (fun w : ℝ => c.y w t) = fun w : ℝ => c₀.y w t₀ + k := by
      funext w
      linarith [hk w]
    rw [hky, deriv_add_const]
  have hspd := productCurve_slice_speed_eq g lambda c c₀ t t₀ hc hc₀ hmap
  have hM : (fun y : ℝ => (c.map (y : Surgery.Topology.Circle) t).1) =
      fun y : ℝ => (c₀.map (y : Surgery.Topology.Circle) t₀).1 := by
    funext y
    exact congrArg Prod.fst (hmap (y : Surgery.Topology.Circle))
  have hUT : ∀ z : ℝ,
      ((c.unitTangent (fun _ => g) lambda z t).1 : E) =
        ((c₀.unitTangent (fun _ => g) lambda z t₀).1 : E) := by
    intro z
    simp only [ProductCurve.unitTangent, ProductCurve.X, ProductCurve.projection, CurveMap.lift,
      CurveMap.X]
    rw [hM, hspd z]
    rfl
  have hUT2 : ∀ z : ℝ,
      (c.unitTangent (fun _ => g) lambda z t).2 =
        (c₀.unitTangent (fun _ => g) lambda z t₀).2 := by
    intro z
    simp only [ProductCurve.unitTangent, ProductCurve.X]
    rw [hspd z, congrFun hY z]
    rfl
  have hfield1 : (fun z : ℝ => (c.unitTangent (fun _ => g) lambda z t).1) =
      fun z : ℝ => (c₀.unitTangent (fun _ => g) lambda z t₀).1 := funext hUT
  have hfield2 : (fun z : ℝ => (c.unitTangent (fun _ => g) lambda z t).2) =
      fun z : ℝ => (c₀.unitTangent (fun _ => g) lambda z t₀).2 := funext hUT2
  intro x
  have hxM : (c.map (x : Surgery.Topology.Circle) t).1 =
      (c₀.map (x : Surgery.Topology.Circle) t₀).1 :=
    congrArg Prod.fst (hmap (x : Surgery.Topology.Circle))
  simp only [ProductCurve.curvatureSq, ProductCurve.curvatureVector, ProductCurve.Ds,
    ProductCurve.Dx, ProductCurve.normSq, ProductCurve.inner,
    ProductCurve.projection, CurveMap.lift]
  rw [hfield1, hfield2, hM, hxM, hspd x]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace Q] hT2 hCompact hConnected hBoundary in
private theorem productCurve_slice_curvature_eq (g : SmoothRiemannianMetric I Q) (lambda : ℝ)
    (c c₀ : ProductCurve Q) (t t₀ : ℝ)
    (hc : c.SmoothOn (I := I) {t}) (hc₀ : c₀.SmoothOn (I := I) {t₀})
    (hmap : ∀ z, c.map z t = c₀.map z t₀) :
    ∀ x, c.curvature (fun _ => g) lambda x t = c₀.curvature (fun _ => g) lambda x t₀ := by
  intro x
  rw [ProductCurve.curvature, ProductCurve.curvature]
  exact congrArg Real.sqrt (productCurve_slice_curvatureSq_eq g lambda c c₀ t t₀ hc hc₀ hmap x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace Q]
  hT2 hCompact hConnected hBoundary in
private theorem productCurve_slice_length_eq (g : SmoothRiemannianMetric I Q) (lambda : ℝ)
    (c c₀ : ProductCurve Q) (t t₀ : ℝ)
    (hc : c.SmoothOn (I := I) {t}) (hc₀ : c₀.SmoothOn (I := I) {t₀})
    (hmap : ∀ z, c.map z t = c₀.map z t₀) :
    c.length (fun _ => g) lambda t = c₀.length (fun _ => g) lambda t₀ := by
  simp only [ProductCurve.length, ProductCurve.integral]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [one_mul, one_mul, productCurve_slice_speed_eq g lambda c c₀ t t₀ hc hc₀ hmap x]

omit [CompleteSpace E] [SigmaCompactSpace Q] hT2 hCompact hConnected hBoundary in
private theorem productCurve_slice_totalCurvature_eq (g : SmoothRiemannianMetric I Q) (lambda : ℝ)
    (c c₀ : ProductCurve Q) (t t₀ : ℝ)
    (hc : c.SmoothOn (I := I) {t}) (hc₀ : c₀.SmoothOn (I := I) {t₀})
    (hmap : ∀ z, c.map z t = c₀.map z t₀) :
    c.totalCurvature (fun _ => g) lambda t = c₀.totalCurvature (fun _ => g) lambda t₀ := by
  simp only [ProductCurve.totalCurvature, ProductCurve.integral]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [productCurve_slice_curvature_eq g lambda c c₀ t t₀ hc hc₀ hmap x,
    productCurve_slice_speed_eq g lambda c c₀ t t₀ hc hc₀ hmap x]

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_prepared_family_solution_initial_bounds
    (B : RicciBackground (I := I) (M := Q) D a b) (lambda L₀ Theta₀ : ℝ)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (solutions : Sphere 2 → ProductCurve Q)
    (hinitial : ∀ p, (initialRamp (prepared p).1).SmoothOn (I := I) {0} ∧
      (initialRamp (prepared p).1).length (fun _ => B.family.metric a) lambda 0 ≤ L₀ ∧
      (initialRamp (prepared p).1).totalCurvature (fun _ => B.family.metric a) lambda 0 ≤ Theta₀)
    (hsol : ∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b))
    (hmap : ∀ p z, (solutions p).map z a = ((prepared p).1 z, z)) :
    ∀ p, (solutions p).length B.family.metric lambda a ≤ L₀ ∧
      (solutions p).totalCurvature B.family.metric lambda a ≤ Theta₀ := by
  intro p
  have haI : ({a} : Set ℝ) ⊆ Icc a b := by
    intro x hx
    rw [mem_singleton_iff] at hx
    subst hx
    exact ⟨le_rfl, B.lt.le⟩
  have hs : (solutions p).SmoothOn (I := I) {a} :=
    ⟨(hsol p).smooth.1.mono (Set.prod_mono Subset.rfl haI),
      (hsol p).smooth.2.mono (Set.prod_mono Subset.rfl haI)⟩
  have hmap' : ∀ z, (solutions p).map z a = (initialRamp ((prepared p).1)).map z 0 := by
    intro z
    rw [hmap p z]
    rfl
  have hlen := productCurve_slice_length_eq (B.family.metric a) lambda (solutions p)
    (initialRamp ((prepared p).1)) a 0 hs (hinitial p).1 hmap'
  have hcurv := productCurve_slice_totalCurvature_eq (B.family.metric a) lambda (solutions p)
    (initialRamp ((prepared p).1)) a 0 hs (hinitial p).1 hmap'
  have hlenβ : (solutions p).length (fun _ => B.family.metric a) lambda a =
      (solutions p).length B.family.metric lambda a := rfl
  have hcurvβ : (solutions p).totalCurvature (fun _ => B.family.metric a) lambda a =
      (solutions p).totalCurvature B.family.metric lambda a := rfl
  refine ⟨?_, ?_⟩
  · rw [← hlenβ]
    exact hlen.trans_le (hinitial p).2.1
  · rw [← hcurvβ]
    exact hcurv.trans_le (hinitial p).2.2

omit hCompact hConnected hBoundary in
def RampProductBounds (B : RicciBackground (I := I) (M := Q) D a b) : Prop :=
  ∀ (L Theta : ℝ), 0 ≤ L → 0 ≤ Theta → ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
    ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L →
      c.totalCurvature B.family.metric lambda a ≤ Theta →
      ∀ t ∈ Icc a b,
        c.length B.family.metric lambda t ≤ Real.exp (B.B₀ * (t - a)) * L ∧
        c.length B.family.metric lambda b ≤
          Real.exp (B.B₀ * (b - t)) * c.length B.family.metric lambda t ∧
        (∫ v in a..t, c.energy B.family.metric lambda v) ≤
          Real.exp (B.B₀ * (t - a)) * L ∧
        c.totalCurvature B.family.metric lambda t + c.length B.family.metric lambda t ≤
          Real.exp ((B.C + B.B₀) * (t - a)) * (Theta + L)

omit hCompact hConnected hBoundary in
def RampProjectedLength (B : RicciBackground (I := I) (M := Q) D a b) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
    c.IsSolutionOn B.family.metric lambda (Icc a b) →
    ∀ γ : ℝ → ContinuousFreeLoop Q, (∀ z, γ b z = c.projection z b) →
      loopLength (B.family.metric b) (γ b) ≤ c.length B.family.metric lambda b

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_ramp_projected_length (B : RicciBackground (I := I) (M := Q) D a b) :
    RampProjectedLength (I := I) (Q := Q) (D := D) (a := a) (b := b) B := by
  intro lambda hlambda hlambda_one c hsol γ hγ
  have hlift : Width.loopLift (γ b) = fun t => c.projection.lift t b := by
    funext t
    simp only [Width.loopLift]
    exact hγ (t : Surgery.Topology.Circle)
  have hb : b ∈ Icc a b := ⟨B.lt.le, le_rfl⟩
  have hspeed_cont : Continuous (fun t => c.speed B.family.metric lambda t b) :=
    (c.speed_contDiff_of_immersedOn B.family.metric lambda hlambda hsol.smooth hsol.immersed b
      hb).continuous
  have hlen : c.length B.family.metric lambda b =
      ∫ t in Icc (0 : ℝ) 1, c.speed B.family.metric lambda t b := by
    rw [ProductCurve.length, ProductCurve.integral,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      MeasureTheory.integral_Icc_eq_integral_Ioc]
    simp
  rw [Width.loopLength_eq_integral_curveSpeed, hlift, hlen]
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg _)
    (hspeed_cont.continuousOn.integrableOn_Icc) (Filter.Eventually.of_forall fun t => ?_)
  exact ProductCurve.projection_speed_le c B.family.metric lambda t b

omit hCompact hConnected hBoundary in
def RampAreaBounds (B : RicciBackground (I := I) (M := Q) D a b) (Ainit : ℝ) : Prop :=
  ∀ (L Theta : ℝ), 0 ≤ L → 0 ≤ Theta → ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
    ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L →
      c.totalCurvature B.family.metric lambda a ≤ Theta →
      ∀ γ : ℝ → ContinuousFreeLoop Q,
        (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
        ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ t ∈ Icc a b, 0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
          loopFamilyLeastArea B.family.metric γ t ≤
            Real.exp (2 * B.B₀ * (b - a)) *
              (Ainit + (b - a) * ((Theta + L) * Real.exp ((B.C + B.B₀) * (b - a))))) ∧
        (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
            Real.exp (2 * B.B₀ * (b - a)) *
              (2 * B.B₀ * (Real.exp (2 * B.B₀ * (b - a)) *
                  (Ainit + (b - a) * ((Theta + L) * Real.exp ((B.C + B.B₀) * (b - a))))) +
                (Theta + L) * Real.exp ((B.C + B.B₀) * (b - a))) * (t - s))

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_ramp_uniform_bounds_of_frontier
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (hproduct : RampProductBounds (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (harea : RampAreaBounds (I := I) (Q := Q) (D := D) (a := a) (b := b) B Ainit) :
    let delta := b - a
    let Lbar := Real.exp (B.B₀ * delta) * L₀
    let Thetabar := (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * delta)
    let Abar := Real.exp (2 * B.B₀ * delta) * (Ainit + delta * Thetabar)
    let Cup := Real.exp (2 * B.B₀ * delta) * (2 * B.B₀ * Abar + Thetabar)
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      ∀ γ : ℝ → ContinuousFreeLoop Q,
        (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
        ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ t ∈ Icc a b,
          c.length B.family.metric lambda t ≤ Lbar ∧
          c.totalCurvature B.family.metric lambda t ≤ Thetabar ∧
          0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
          loopFamilyLeastArea B.family.metric γ t ≤ Abar) ∧
        (∫ t in a..b, c.energy B.family.metric lambda t) ≤ Lbar ∧
        ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
            Cup * (t - s) := by
  refine rfs_ramp_uniform_bounds_of_product_bounds B L₀ Theta₀ Ainit hL₀ hTheta₀ hAinit
    (fun lambda hlambda hlambda_one c hsol hlen hcurv t ht => ?_)
    (fun lambda hlambda hlambda_one c hsol γ hγ hctr hlen hcurv hA => ?_)
  · obtain ⟨h₁, -, h₃, h₄⟩ := hproduct L₀ Theta₀ hL₀ hTheta₀ lambda hlambda hlambda_one c hsol
      hlen hcurv t ht
    exact ⟨h₁, h₃, h₄⟩
  · simpa only [rampThetabar, rampAbar, rampCup] using harea L₀ Theta₀ hL₀ hTheta₀ lambda
      hlambda hlambda_one c hsol hlen hcurv γ hγ hctr hA

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
def RampFamilyFlowSolutions (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2)) (lambda : ℝ) : Prop :=
  ∃ solutions : Sphere 2 → ProductCurve Q,
    @Continuous (Sphere 2) (ProductCurve Q) inferInstance
      (smoothProductCylinderTopology e (Icc a b)) solutions ∧
    ∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
      (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
      (solutions p).degree = 1 ∧
      ∀ z, (solutions p).map z a = ((prepared p).1 z, z)

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
def RampFamilyProjectedDeformation (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2)) (lambda : ℝ) : Prop :=
  ∀ solutions : Sphere 2 → ProductCurve Q,
    @Continuous (Sphere 2) (ProductCurve Q) inferInstance
      (smoothProductCylinderTopology e (Icc a b)) solutions →
    (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
      (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
      (solutions p).degree = 1 ∧
      ∀ z, (solutions p).map z a = ((prepared p).1 z, z)) →
    ∃ projected : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
      (∀ t : Icc a b, ∀ p z,
        ((projected t) p).1 z = (solutions p).projection z t) ∧
      projected ⟨a, le_rfl, B.lt.le⟩ = prepared ∧
      (∀ t : Icc a b, HasContinuousSmoothLoopJets e (projected t)) ∧
      ∀ t : Icc a b,
        FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (projected t)) =
          FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp prepared)

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_prepared_family_flow_of_frontier (B : RicciBackground (I := I) (M := Q) D a b)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hsmooth : HasContinuousSmoothLoopJets e prepared)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    (hsolutions : RampFamilyFlowSolutions (I := I) (Q := Q) (D := D) (a := a) (b := b) B e prepared
      lambda)
    (hprojected : RampFamilyProjectedDeformation (I := I) (Q := Q) (D := D) (a := a) (b := b) B e
      prepared lambda) :
    ∃ solutions : Sphere 2 → ProductCurve Q,
      ∃ projected : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
        @Continuous (Sphere 2) (ProductCurve Q) inferInstance
          (smoothProductCylinderTopology e (Icc a b)) solutions ∧
        (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
          (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
          (solutions p).degree = 1 ∧
          ∀ z, (solutions p).map z a = ((prepared p).1 z, z)) ∧
        (∀ t : Icc a b, ∀ p z,
          ((projected t) p).1 z = (solutions p).projection z t) ∧
        projected ⟨a, le_rfl, B.lt.le⟩ = prepared ∧
        (∀ t : Icc a b, HasContinuousSmoothLoopJets e (projected t)) ∧
        ∀ t : Icc a b,
          FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (projected t)) =
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp prepared) := by
  let _ := hsmooth
  let _ := hlambda
  let _ := hlambda_one
  obtain ⟨solutions, hcont, hdata⟩ := hsolutions
  obtain ⟨projected, hproj, hat, hjets, hclass⟩ := hprojected solutions hcont hdata
  exact ⟨solutions, projected, hcont, hdata, hproj, hat, hjets, hclass⟩

theorem rfs_ramp_uniform_bounds (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit) :
    let delta := b - a
    let Lbar := Real.exp (B.B₀ * delta) * L₀
    let Thetabar := (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * delta)
    let Abar := Real.exp (2 * B.B₀ * delta) * (Ainit + delta * Thetabar)
    let Cup := Real.exp (2 * B.B₀ * delta) * (2 * B.B₀ * Abar + Thetabar)
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      ∀ γ : ℝ → ContinuousFreeLoop Q,
        (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
        ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ t ∈ Icc a b,
          c.length B.family.metric lambda t ≤ Lbar ∧
          c.totalCurvature B.family.metric lambda t ≤ Thetabar ∧
          0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
          loopFamilyLeastArea B.family.metric γ t ≤ Abar) ∧
        (∫ t in a..b, c.energy B.family.metric lambda t) ≤ Lbar ∧
        ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
            Cup * (t - s) := by
  have hcurv : curveShorteningTotalCurvatureBound (I := I) (M := Q) B := by
    intro lambda hlambda _ c hc t ht
    exact c.totalCurvature_add_length_le_exp B lambda hlambda
      (uniqueDiffOn_Icc B.lt) hc B.lt Subset.rfl Subset.rfl a t
      ⟨le_rfl, B.lt.le⟩ ht
  refine rfs_ramp_uniform_bounds_of_product_bounds B L₀ Theta₀ Ainit hL₀ hTheta₀ hAinit
    (fun lambda hlambda _ c hsol hlen htot t ht => ?_)
    (fun lambda hlambda hlambda_one c hsol γ hγ hctr hlen htot hA => ?_)
  · have hbounds := (c.length_energy_bounds B lambda hlambda (uniqueDiffOn_Icc B.lt)
      hsol B.lt Subset.rfl Subset.rfl).2.2 a ⟨le_rfl, B.lt.le⟩ t ht
    refine ⟨hbounds.1.trans (mul_le_mul_of_nonneg_left hlen (Real.exp_nonneg _)),
      hbounds.2.trans (mul_le_mul_of_nonneg_left hlen (Real.exp_nonneg _)), ?_⟩
    exact (hcurv lambda hlambda (by assumption) c hsol t ht).trans
      (mul_le_mul_of_nonneg_left (add_le_add htot hlen) (Real.exp_nonneg _))
  · have hagree : ∀ z t, t ∈ Icc a b → γ t z = c.projection z t :=
      fun z t ht => hγ t ht z
    have hγsmooth : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) := by
      rw [CurveMap.SmoothOn]
      refine hsol.smooth.1.congr ?_
      intro p hp
      exact hagree (p.1 : AddCircle (1 : ℝ)) p.2 hp.2
    have hcont := continuousOn_loopFamilyLeastArea_of_contractible B γ hγsmooth hctr
    obtain ⟨hrange, hslope⟩ := rfs_csf_projection_upper_control B
      B.curveShorteningLeastAreaSlope hcurv L₀ Theta₀ Ainit hL₀ hTheta₀ hAinit
      lambda hlambda hlambda_one c hsol γ hagree hctr hcont hlen htot hA
    exact ⟨hcont, hrange, hslope⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
