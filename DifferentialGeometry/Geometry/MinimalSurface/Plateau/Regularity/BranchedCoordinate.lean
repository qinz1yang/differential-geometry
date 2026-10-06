import DifferentialGeometry.Analysis.Complex.BranchedCoordinate
import DifferentialGeometry.Topology.Covering.ComplexPowerExpansion
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientBranchOrder
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientBranchExpansion

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

theorem DiskRegularity.ConsumerAudit.morrey_leading_projection_branched_coordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    ∃ (m : ℕ) (B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)),
      ContDiffAt ℝ 1 B a ∧ B a ≠ 0 ∧
      (∀ᶠ z in 𝓝 a,
        (fun k => chartComplexGradient (E := E)
          (diskExtension u a) (diskExtension u) k z) = (z - a) ^ m • B z) ∧
      let p := diskExtension u a
      let proj := chartLeadingPlaneProjection g p p (B a)
      let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (diskExtension u z))
      ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
        Metric.closedBall a r ⊆ Metric.ball (0 : ℂ) 1 ∧
        (∀ z ∈ Metric.closedBall a r, diskExtension u z ∈ (chartAt E p).source) ∧
        (∀ z ∈ Metric.closedBall a r, z ≠ a → (fderiv ℝ F z).IsInvertible) ∧
        (∀ z ∈ Metric.closedBall a r, F z = F a ↔ z = a) ∧
        (∀ z ∈ Metric.sphere a r, δ < ‖F z - F a‖) ∧
        let f : Metric.closedBall a r → ℂ := fun z => F z.val
        let S : Set ℂ := Metric.ball (F a) δ \ {F a}
        IsCoveringMap (S.restrictPreimage f) ∧
          (∀ y ∈ S, (f ⁻¹' {y}).encard = ((m + 1 : ℕ) : ℕ∞)) ∧
          let Ψ : ℂ → ℂ := fun z =>
            if z = a then 0 else
              (z - a) * Complex.exp
                (Complex.log
                  (((m + 1 : ℕ) : ℂ) * (F z - F a) / (z - a) ^ (m + 1)) /
                    ((m + 1 : ℕ) : ℂ))
          ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧
            ∃ e : OpenPartialHomeomorph ℂ ℂ,
              e.source = Metric.ball a ρ ∧
              (e : ℂ → ℂ) = Ψ ∧ e a = 0 ∧
              HasFDerivAt Ψ (ContinuousLinearMap.id ℝ ℂ) a ∧
              ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source ∧
              ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target ∧
              ContDiffOn ℝ ∞ (e : ℂ → ℂ) (e.source \ {a}) ∧
              ContDiffOn ℝ ∞ (e.symm : ℂ → ℂ) (e.target \ {0}) ∧
              ∀ z ∈ e.source,
                F z = F a + Ψ z ^ (m + 1) / ((m + 1 : ℕ) : ℂ) := by
  have horder :
      ∃ (m : ℕ) (B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)),
        ContDiffAt ℝ 1 B a ∧ B a ≠ 0 ∧
          (∀ᶠ z in 𝓝 a,
            (fun k => chartComplexGradient (E := E)
              (diskExtension u a) (diskExtension u) k z) = (z - a) ^ m • B z) := by
    obtain ⟨R, _, _, _, A_R, _, _, P, _, _, _, _, hactual⟩ :=
      hu.exists_finite_order_complex_gradient_gauge hγ ha
    let V := Fin (Module.finrank ℝ E) → ℂ
    let P₀ : ℂ → V →L[ℂ] V := fun z =>
      1 + (Real.pi : ℂ)⁻¹ •
        ∫ w : closedBall a R,
          (z - (w : ℂ))⁻¹ • (A_R w * P w)
          ∂(volume.comap ((↑) : closedBall a R → ℂ))
    let ξ : ℂ → V := fun z k =>
      chartComplexGradient (diskExtension u a) (diskExtension u) k z
    let Q : ℂ → V := fun z => (Ring.inverse (P₀ z)) (ξ z)
    dsimp only at hactual
    obtain ⟨_, _, _, _, _, _, _, _, G, _, _, hB, hBne, hfactor, _⟩ := hactual
    let m := analyticOrderNatAt Q a
    let B : ℂ → V := fun z => P₀ z (G z)
    change ContDiffAt ℝ 1 B a at hB
    change B a ≠ 0 at hBne
    change ∀ᶠ z in 𝓝 a,
      (fun k => chartComplexGradient (diskExtension u a) (diskExtension u) k z) =
        (z - a) ^ m • B z at hfactor
    exact ⟨m, B, hB, hBne, hfactor⟩
  obtain ⟨m, B, hB, hBne, hfactor⟩ := horder
  refine ⟨m, B, hB, hBne, hfactor, ?_⟩
  let p := diskExtension u a
  let proj := chartLeadingPlaneProjection g p p (B a)
  let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (diskExtension u z))
  have hsrc : diskExtension u a ∈ (chartAt E p).source := mem_chart_source E p
  have hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u)
      (ball (0 : ℂ) 1) := hu.smoothInterior.of_le (by norm_num)
  obtain ⟨r₁, hr₁, hsub₁, hchart₁, hreg⟩ :=
    chartComplexGradient_leading_projection_nondegenerate (E := E) (M := M) g
      (U := diskExtension u) (s := ball (0 : ℂ) 1) isOpen_ball hU
      hu.conformal (a := a) ha (p := p) hsrc (m := m) (B := B)
      hB.continuousAt hBne hfactor
  obtain ⟨C, r₂, hC, hr₂, _, _, hexp⟩ :=
    chartComplexGradient_leading_projection_expansion (E := E) (M := M) g
      (U := diskExtension u) (s := ball (0 : ℂ) 1) isOpen_ball hU
      hu.conformal (a := a) ha (p := p) hsrc (m := m) (B := B) hB hBne hfactor
  change ∀ z ∈ ball a r₂,
    ‖F z - F a - (z - a) ^ (m + 1) / ((m + 1 : ℕ) : ℂ)‖ ≤
      C * ‖z - a‖ ^ (m + 2) at hexp
  let R0 := min r₁ r₂
  have hR0 : 0 < R0 := lt_min hr₁ hr₂
  have hleft : ball a R0 ⊆ ball a r₁ := ball_subset_ball (min_le_left _ _)
  have hright : ball a R0 ⊆ ball a r₂ := ball_subset_ball (min_le_right _ _)
  have hF : ContDiffOn ℝ 1 F (ball a R0) := by
    intro z hz
    have hX : ContDiffAt ℝ 1
        (fun w => extChartAt 𝓘(ℝ, E) p (diskExtension u w)) z :=
      ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) (hchart₁ z (hleft hz))).comp z
        (hU.contMDiffAt (isOpen_ball.mem_nhds (hsub₁ (hleft hz))))).contDiffAt
    exact (proj.contDiff.contDiffAt.comp z hX).contDiffWithinAt
  obtain ⟨r, δ, hr, hrR0, hδ, hcenter, hgap, hcover, hcard⟩ :=
    Covering.exists_nsheeted_covering_of_complex_power_expansion
      (F := F) (a := a) (n := m + 1) (C := C) (R0 := R0)
      (Nat.succ_pos m) hR0 hC.le hF
      (fun z hz hza => (hreg z (hleft hz) hza).1)
      (fun z hz => hexp z (hright hz))
  have hclosed : closedBall a r ⊆ ball a R0 := closedBall_subset_ball hrR0
  obtain ⟨D, r₃, hD, hr₃, _, _, hderiv⟩ :=
    chartComplexGradient_leading_projection_fderiv_error (E := E) (M := M) g
      (U := diskExtension u) (s := ball (0 : ℂ) 1) isOpen_ball hU
      hu.conformal (a := a) ha (p := p) hsrc (m := m) (B := B) hB hBne hfactor
  change ∀ z ∈ ball a r₃, ∀ v : ℂ,
    ‖fderiv ℝ F z v - (z - a) ^ m * v‖ ≤ D * ‖z - a‖ ^ (m + 1) * ‖v‖ at hderiv
  let R₁ := min r r₃
  have hR₁ : 0 < R₁ := lt_min hr hr₃
  have hR₁r : ball a R₁ ⊆ ball a r := ball_subset_ball (min_le_left _ _)
  have hR₁r₃ : ball a R₁ ⊆ ball a r₃ := ball_subset_ball (min_le_right _ _)
  have hR₁R0 : ball a R₁ ⊆ ball a R0 :=
    hR₁r.trans ((ball_subset_closedBall).trans hclosed)
  have hexp₁ : ∀ z ∈ ball a R₁,
      ‖F z - F a - (z - a) ^ (m + 1) / ((m + 1 : ℕ) : ℂ)‖ ≤
        C * ‖z - a‖ ^ ((m + 1) + 1) :=
    fun z hz => hexp z (hright (hR₁R0 hz))
  obtain ⟨t, ht, htR₁, hslit⟩ :=
    DifferentialGeometry.Analysis.exists_ball_normalized_complex_power_mem_slitPlane
      (Nat.succ_pos m) hC.le hR₁ hexp₁
  have htR₁sub : ball a t ⊆ ball a R₁ := ball_subset_ball htR₁.le
  have htr : t < r := htR₁.trans_le (min_le_left _ _)
  have hFt : ContDiffOn ℝ ∞ F (ball a t) := by
    intro z hz
    have hzR0 := hR₁R0 (htR₁sub hz)
    have hX : ContDiffAt ℝ ∞
        (fun w => extChartAt 𝓘(ℝ, E) p (diskExtension u w)) z :=
      ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchart₁ z (hleft hzR0))).comp z
        (hu.smoothInterior.contMDiffAt (isOpen_ball.mem_nhds (hsub₁ (hleft hzR0))))).contDiffAt
    exact (proj.contDiff.contDiffAt.comp z hX).contDiffWithinAt
  have hderivt : ∀ z ∈ ball a t, ∀ v : ℂ,
      ‖fderiv ℝ F z v - (z - a) ^ ((m + 1) - 1) * v‖ ≤
        D * ‖z - a‖ ^ (m + 1) * ‖v‖ := by
    intro z hz v
    simpa only [Nat.add_sub_cancel] using hderiv z (hR₁r₃ (htR₁sub hz)) v
  obtain ⟨ρ, hρ, hρt, e, hesource, he, hea, hederiv, heC1, heiC1, hepower⟩ :=
    DifferentialGeometry.Analysis.exists_c1_coordinate_of_complex_power_remainders
      (Nat.succ_pos m) ht hC.le hD.le (hFt.of_le (by norm_num))
      (fun z hz => hexp₁ z (htR₁sub hz)) hderivt
  let Ψ : ℂ → ℂ := fun z =>
    if z = a then 0 else
      (z - a) * Complex.exp
        (Complex.log
          (((m + 1 : ℕ) : ℂ) * (F z - F a) / (z - a) ^ (m + 1)) /
            ((m + 1 : ℕ) : ℂ))
  change (e : ℂ → ℂ) = Ψ at he
  have hρtsub : ball a ρ ⊆ ball a t := ball_subset_ball hρt.le
  have heSmooth : ContDiffOn ℝ ∞ (e : ℂ → ℂ) (e.source \ {a}) := by
    intro z hz
    have hzt : z ∈ ball a t := hρtsub (hesource ▸ hz.1)
    have hza : z ≠ a := hz.2
    have hsmooth := DifferentialGeometry.Analysis.contDiffAt_complex_power_root_coordinate
      (hFt.contDiffAt (isOpen_ball.mem_nhds hzt)) hza (hslit z hzt hza)
    rw [he]
    exact hsmooth.contDiffWithinAt
  have heiSmooth : ContDiffOn ℝ ∞ (e.symm : ℂ → ℂ) (e.target \ {0}) := by
    intro y hy
    have hx : e.symm y ∈ e.source := e.map_target hy.1
    have hxa : e.symm y ≠ a := by
      intro h
      apply hy.2
      change y = 0
      rw [← e.right_inv hy.1, h, hea]
    have hxopen : e.source \ {a} ∈ 𝓝 (e.symm y) :=
      (e.open_source.sdiff isClosed_singleton).mem_nhds ⟨hx, hxa⟩
    have hCe : ContDiffAt ℝ ∞ (e : ℂ → ℂ) (e.symm y) :=
      heSmooth.contDiffAt hxopen
    have hd : HasFDerivAt (e : ℂ → ℂ) (fderiv ℝ (e : ℂ → ℂ) (e.symm y)) (e.symm y) :=
      (heC1.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt_one.hasFDerivAt
    have hi : HasFDerivAt (e.symm : ℂ → ℂ) (fderiv ℝ (e.symm : ℂ → ℂ) y) y :=
      (heiC1.contDiffAt (e.open_target.mem_nhds hy.1)).differentiableAt_one.hasFDerivAt
    have hi' : HasFDerivAt (e.symm : ℂ → ℂ) (fderiv ℝ (e.symm : ℂ → ℂ) y)
        (e (e.symm y)) := by simpa only [e.right_inv hy.1] using hi
    have hleftInv : (fderiv ℝ (e.symm : ℂ → ℂ) y).comp
        (fderiv ℝ (e : ℂ → ℂ) (e.symm y)) = ContinuousLinearMap.id ℝ ℂ :=
      ((hi'.comp (e.symm y) hd).congr_of_eventuallyEq
        (Filter.EventuallyEq.symm (e.eventually_left_inverse hx))).unique (hasFDerivAt_id (e.symm y))
    have hrightInv : (fderiv ℝ (e : ℂ → ℂ) (e.symm y)).comp
        (fderiv ℝ (e.symm : ℂ → ℂ) y) = ContinuousLinearMap.id ℝ ℂ :=
      ((hd.comp y hi).congr_of_eventuallyEq
        (Filter.EventuallyEq.symm (e.eventually_right_inverse hy.1))).unique (hasFDerivAt_id y)
    let L : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.equivOfInverse'
      (fderiv ℝ (e : ℂ → ℂ) (e.symm y)) (fderiv ℝ (e.symm : ℂ → ℂ) y)
      hrightInv hleftInv
    exact (e.contDiffAt_symm (f₀' := L) hy.1 hd hCe).contDiffWithinAt
  refine ⟨r, δ, hr, hδ, hclosed.trans (hleft.trans hsub₁),
    fun z hz => hchart₁ z (hleft (hclosed hz)),
    fun z hz hza => (hreg z (hleft (hclosed hz)) hza).1,
    hcenter, hgap, hcover.isCoveringMap_restrictPreimage, hcard,
    ρ, hρ, hρt.trans htr, e, hesource, he, hea, hederiv, heC1, heiC1,
    heSmooth, heiSmooth, hepower⟩
