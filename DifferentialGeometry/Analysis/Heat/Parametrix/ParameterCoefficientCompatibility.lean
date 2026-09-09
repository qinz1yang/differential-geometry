import DifferentialGeometry.Analysis.Heat.Parametrix.CoordinateCompatibility
import DifferentialGeometry.Analysis.Heat.Parametrix.ParameterCoefficientRegularity

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.DiagInvBranch

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral
open DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem heatParametrixCoefficientInTrivialization_eventuallyEq
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c p : M}
    (B : DiagInvBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e] (hp : p ∈ e.baseSet)
    (h0 : (0 : E) ∈ (B.fixed p).hom.source) (k : ℕ) :
    B.heatParametrixCoefficientInTrivialization e k p =ᶠ[𝓝 p]
      heatParametrixCoefficient g p k := by
  let L : E ≃L[ℝ] E := (e.continuousLinearEquivAt ℝ p hp).symm
  let Φ : E → M := (B.fixed p).hom
  let Ψ : M → E := (B.fixed p).inv
  let J : E → ℝ := fun v => paramDensity g Φ v / paramDensity g Φ 0
  let ψ : M → E := fun q => (e (B.inv (p, q))).2
  let a : ℕ → M → ℝ := fun j =>
    heatParametrixCoefficientInCoordinates g (Φ ∘ L) ψ (J ∘ L) j
  let b : ℕ → M → ℝ := fun j =>
    heatParametrixCoefficientInCoordinates g (Φ ∘ L) (L.symm ∘ Ψ) (J ∘ L) j
  have hΦ : (fun v => expMapIntrinsic g hEnorm p (e.symmL ℝ p v)) = Φ ∘ L := by
    funext v
    exact congrArg (expMapIntrinsic g hEnorm p)
      ((congrFun (e.symm_continuousLinearEquivAt_eq (R := ℝ) hp) v).symm)
  have hΦdiff (v : E) : MDifferentiableAt 𝓘(ℝ, E) I Φ v :=
    (intrinsicFiber_smooth g hEnorm p).contMDiffAt.mdifferentiableAt (by simp)
  have hJ : (fun v => paramDensity g (Φ ∘ L) v / paramDensity g (Φ ∘ L) 0) = J ∘ L := by
    funext v
    exact paramDensity_ratio_comp_continuousLinearEquiv g L (hΦdiff _) (hΦdiff 0)
  have ha (j : ℕ) : B.heatParametrixCoefficientInTrivialization e j p = a j := by
    unfold heatParametrixCoefficientInTrivialization
    rw [hΦ, hJ]
  have hb (j : ℕ) : b j = heatParametrixCoefficientInCoordinates g Φ Ψ J j :=
    heatParametrixCoefficientInCoordinates_comp_linearEquiv g Φ Ψ J L.toLinearEquiv j
  have hraw (j : ℕ) : b j =ᶠ[𝓝 p] heatParametrixCoefficient g p j := by
    rw [hb]
    exact (B.fixed p).heatParametrixCoefficientInCoordinates_eventuallyEq h0 j
  have hΦzero : Φ 0 = p := expMapIntrinsic_zero g hEnorm p
  have hpdom : p ∈ (B.fixed p).dom := by
    have h := (B.fixed p).hom.map_source h0
    change Φ 0 ∈ (B.fixed p).dom at h
    rwa [hΦzero] at h
  have hΨzero : Ψ p = 0 := by
    rw [← hΦzero]
    exact (B.fixed p).hom.left_inv h0
  have hΨ : Tendsto Ψ (𝓝 p) (𝓝 (0 : E)) := by
    rw [← hΨzero]
    exact (B.fixed p).inv_inf.continuousOn.continuousAt
      ((B.fixed p).hom.open_target.mem_nhds hpdom)
  have hψ : ψ =ᶠ[𝓝 p] L.symm ∘ Ψ := by
    filter_upwards [(B.fixed p).hom.open_target.mem_nhds hpdom] with q hq
    have htotal : B.inv (p, q) =
        (⟨p, show TangentSpace I p from (B.inv (p, q)).snd⟩ : TangentBundle I M) := by
      apply TotalSpace.ext (B.proj_eq hq)
      exact heq_of_eq rfl
    change (e (B.inv (p, q))).2 = L.symm (Ψ q)
    rw [htotal, e.apply_eq_prod_continuousLinearEquivAt ℝ p hp]
    rfl
  have hψzero : Tendsto ψ (𝓝 p) (𝓝 (0 : E)) := by
    have h := L.symm.continuous.continuousAt.tendsto.comp hΨ
    simpa only [map_zero] using h.congr' hψ.symm
  have hforw : Tendsto (Φ ∘ L) (𝓝 (0 : E)) (𝓝 p) := by
    have hcont : Continuous Φ := (intrinsicFiber_smooth g hEnorm p).continuous
    have h : Tendsto (Φ ∘ L) (𝓝 (0 : E)) (𝓝 (Φ (L 0))) :=
      (hcont.comp L.continuous).continuousAt
    simpa only [map_zero, hΦzero] using h
  let V : Set M := (normalChartAt g p).source ∩
    (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)
  have hV : IsOpen V :=
    (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
      (normalChartAt g p).open_source Metric.isOpen_ball
  have hpV : p ∈ V := by
    refine ⟨normalChartAt_source g p, ?_⟩
    change normalChartAt g p p ∈ Metric.ball (0 : E) (expMapC2Radius g p)
    rw [normalChartAt_centre]
    exact Metric.mem_ball_self (expMapC2Radius_pos g p)
  have hab : ∀ j : ℕ, a j =ᶠ[𝓝 p] b j := by
    intro j
    induction j with
    | zero =>
      filter_upwards [hψ] with q hq
      change (Real.sqrt (J (L (ψ q))))⁻¹ = (Real.sqrt (J (L (L.symm (Ψ q)))))⁻¹
      rw [hq]
      rfl
    | succ j ih =>
      have hΔ : laplacian (LeviCivita g) g (a j) =ᶠ[𝓝 p]
          laplacian (LeviCivita g) g (b j) := by
        filter_upwards [ih.eventuallyEq_nhds, (hraw j).eventuallyEq_nhds,
          hV.mem_nhds hpV] with q hq hr hqV
        have hs := ((contMDiffOn_heatParametrixCoefficient g p j q hqV).contMDiffAt
          (hV.mem_nhds hqV)).congr_of_eventuallyEq hr
        exact laplacian_congr_of_eventuallyEq (LeviCivita g) g
          (hs.congr_of_eventuallyEq hq) hs hq
      have hin : (fun v : E => Real.sqrt (J (L v)) *
          laplacian (LeviCivita g) g (a j) (Φ (L v))) =ᶠ[𝓝 (0 : E)]
          fun v : E => Real.sqrt (J (L v)) *
            laplacian (LeviCivita g) g (b j) (Φ (L v)) := by
        filter_upwards [hΔ.comp_tendsto hforw] with v hv
        exact congrArg (fun z => Real.sqrt (J (L v)) * z) hv
      have hrad := (radialIntegral_eventuallyEq j hin).comp_tendsto hψzero
      filter_upwards [hψ, hrad] with q hq hr
      change (Real.sqrt (J (L (ψ q))))⁻¹ *
          radialIntegral j (fun v => Real.sqrt (J (L v)) *
            laplacian (LeviCivita g) g (a j) (Φ (L v))) (ψ q) =
        (Real.sqrt (J (L (L.symm (Ψ q)))))⁻¹ *
          radialIntegral j (fun v => Real.sqrt (J (L v)) *
            laplacian (LeviCivita g) g (b j) (Φ (L v))) (L.symm (Ψ q))
      simp only [Function.comp_apply] at hr hq
      rw [hr, hq]
  rw [ha]
  exact (hab k).trans (hraw k)

theorem gradientFun_heatParametrixCoefficientInTrivialization_eventuallyEq
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c p : M}
    (B : DiagInvBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e] (hp : p ∈ e.baseSet)
    (h0 : (0 : E) ∈ (B.fixed p).hom.source) (k : ℕ) :
    (fun q => gradientFun g (B.heatParametrixCoefficientInTrivialization e k p) q) =ᶠ[𝓝 p]
      fun q => gradientFun g (heatParametrixCoefficient g p k) q := by
  have h := B.heatParametrixCoefficientInTrivialization_eventuallyEq e hp h0 k
  filter_upwards [h.eventuallyEq_nhds] with q hq
  have hD := hq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ))
  unfold gradientFun metricSharp mvfderiv
  rw [hD, hq.eq_of_nhds]

theorem laplacian_heatParametrixCoefficientInTrivialization_eventuallyEq
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c p : M}
    (B : DiagInvBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e] (hp : p ∈ e.baseSet)
    (h0 : (0 : E) ∈ (B.fixed p).hom.source) (k : ℕ) :
    laplacian (LeviCivita g) g (B.heatParametrixCoefficientInTrivialization e k p) =ᶠ[𝓝 p]
      laplacian (LeviCivita g) g (heatParametrixCoefficient g p k) := by
  let V : Set M := (normalChartAt g p).source ∩
    (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)
  have hV : IsOpen V :=
    (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
      (normalChartAt g p).open_source Metric.isOpen_ball
  have hpV : p ∈ V := by
    refine ⟨normalChartAt_source g p, ?_⟩
    change normalChartAt g p p ∈ Metric.ball (0 : E) (expMapC2Radius g p)
    rw [normalChartAt_centre]
    exact Metric.mem_ball_self (expMapC2Radius_pos g p)
  have h := B.heatParametrixCoefficientInTrivialization_eventuallyEq e hp h0 k
  filter_upwards [h.eventuallyEq_nhds, hV.mem_nhds hpV] with q hq hqV
  have hs := (contMDiffOn_heatParametrixCoefficient g p k q hqV).contMDiffAt (hV.mem_nhds hqV)
  exact laplacian_congr_of_eventuallyEq (LeviCivita g) g (hs.congr_of_eventuallyEq hq) hs hq

theorem heatParametrixCoefficientInTrivialization_succ_centre
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c p : M}
    (B : DiagInvBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e] (hp : p ∈ e.baseSet)
    (h0 : (0 : E) ∈ (B.fixed p).hom.source) (k : ℕ) :
    B.heatParametrixCoefficientInTrivialization e (k + 1) p p =
      laplacian (LeviCivita g) g (B.heatParametrixCoefficientInTrivialization e k p) p /
        (k + 1 : ℝ) := by
  rw [(B.heatParametrixCoefficientInTrivialization_eventuallyEq e hp h0 (k + 1)).eq_of_nhds,
    (B.laplacian_heatParametrixCoefficientInTrivialization_eventuallyEq e hp h0 k).eq_of_nhds]
  exact heatParametrixCoefficient_succ_centre g p k

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
private theorem heatParametrixCoefficientInTrivialization_eqOn_fixed_of_domain
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c p : M}
    (B : DiagInvBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e] (hp : p ∈ e.baseSet)
    {U : Set E} {Q : Set M} (hU : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (hQ : IsOpen Q) (hQB : ∀ q ∈ Q, (p, q) ∈ B.dom)
    (hΦ : ContMDiffOn 𝓘(ℝ, E) I ∞
      (fun v => expMapIntrinsic g hEnorm p (e.symmL ℝ p v)) U)
    (hΨ : ContMDiffOn I 𝓘(ℝ, E) ∞ (fun q => (e (B.inv (p, q))).2) Q)
    (hJ : ContDiffOn ℝ ∞ (fun v =>
      paramDensity g (fun w => expMapIntrinsic g hEnorm p (e.symmL ℝ p w)) v /
        paramDensity g (fun w => expMapIntrinsic g hEnorm p (e.symmL ℝ p w)) 0) U)
    (hJpos : ∀ v ∈ U, 0 <
      paramDensity g (fun w => expMapIntrinsic g hEnorm p (e.symmL ℝ p w)) v /
        paramDensity g (fun w => expMapIntrinsic g hEnorm p (e.symmL ℝ p w)) 0)
    (hΦQ : MapsTo (fun v => expMapIntrinsic g hEnorm p (e.symmL ℝ p v)) U Q)
    (hΨU : MapsTo (fun q => (e (B.inv (p, q))).2) Q U) (k : ℕ) :
    EqOn (B.heatParametrixCoefficientInTrivialization e k p)
      (heatParametrixCoefficientInCoordinates g (B.fixed p).hom (B.fixed p).inv
        (fun v => paramDensity g (B.fixed p).hom v / paramDensity g (B.fixed p).hom 0) k) Q := by
  let L : E ≃L[ℝ] E := (e.continuousLinearEquivAt ℝ p hp).symm
  let Φ : E → M := fun v => expMapIntrinsic g hEnorm p (e.symmL ℝ p v)
  let Ψ : M → E := fun q => (e (B.inv (p, q))).2
  let J : E → ℝ := fun v => paramDensity g Φ v / paramDensity g Φ 0
  let Φ₀ : E → M := (B.fixed p).hom
  let Ψ₀ : M → E := (B.fixed p).inv
  let J₀ : E → ℝ := fun v => paramDensity g Φ₀ v / paramDensity g Φ₀ 0
  have hΦeq : Φ = Φ₀ ∘ L := by
    funext v
    exact congrArg (expMapIntrinsic g hEnorm p)
      ((congrFun (e.symm_continuousLinearEquivAt_eq (R := ℝ) hp) v).symm)
  have hΦ₀diff (v : E) : MDifferentiableAt 𝓘(ℝ, E) I Φ₀ v :=
    (intrinsicFiber_smooth g hEnorm p).contMDiffAt.mdifferentiableAt (by simp)
  have hJeq : J = J₀ ∘ L := by
    funext v
    change paramDensity g Φ v / paramDensity g Φ 0 = _
    rw [hΦeq]
    exact paramDensity_ratio_comp_continuousLinearEquiv g L (hΦ₀diff _) (hΦ₀diff 0)
  have hΨeq : EqOn Ψ (L.symm ∘ Ψ₀) Q := by
    intro q hq
    have htotal : B.inv (p, q) =
        (⟨p, show TangentSpace I p from (B.inv (p, q)).snd⟩ : TangentBundle I M) := by
      apply TotalSpace.ext (B.proj_eq (hQB q hq))
      exact heq_of_eq rfl
    change (e (B.inv (p, q))).2 = L.symm (Ψ₀ q)
    rw [htotal, e.apply_eq_prod_continuousLinearEquivAt ℝ p hp]
    rfl
  have heq := heatParametrixCoefficientInCoordinates_congrOn g hU hstar hQ
    hΦ hΨ hΦQ hΨU hJ hJpos (fun _ _ => rfl) hΨeq (fun _ _ => rfl) k
  intro q hq
  change heatParametrixCoefficientInCoordinates g Φ Ψ J k q = _
  rw [heq hq]
  change heatParametrixCoefficientInCoordinates g Φ (L.symm ∘ Ψ₀) J k q = _
  rw [hΦeq, hJeq]
  exact congrFun (heatParametrixCoefficientInCoordinates_comp_linearEquiv g
    Φ₀ Ψ₀ J₀ L.toLinearEquiv k) q

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem exists_heatParametrixCoefficientInTrivialization_eqOn_fixed
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagInvBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e] (hc : c ∈ e.baseSet) :
    ∃ V : Set (M × M), IsOpen V ∧ (c, c) ∈ V ∧ V ⊆ B.dom ∧
      ∀ k : ℕ, EqOn (fun z : M × M => B.heatParametrixCoefficientInTrivialization e k z.1 z.2)
        (fun z : M × M => heatParametrixCoefficientInCoordinates g
          (B.fixed z.1).hom (B.fixed z.1).inv
          (fun v => paramDensity g (B.fixed z.1).hom v /
            paramDensity g (B.fixed z.1).hom 0) k z.2) V := by
  let Φ : M → E → M := fun p v => expMapIntrinsic g hEnorm p (e.symmL ℝ p v)
  let Ψ : M → M → E := fun p q => (e (B.inv (p, q))).2
  let J : M → E → ℝ := fun p v => paramDensity g (Φ p) v / paramDensity g (Φ p) 0
  obtain ⟨W, hW, _, hWzero, hJpos, hJ⟩ :=
    exists_contMDiffOn_paramDensity_ratio_expMapIntrinsic_trivialization g hEnorm e
  change ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry J) W at hJ
  obtain ⟨S, hS, hcS, r, hr, V, hV, hcV, hVB, hT, hTB, hRe,
      hF, hR, hFV, hRT, hleft, hright⟩ :=
    B.exists_ball_trivialization_domain e hc hW (hWzero c hc)
  refine ⟨V, hV, hcV, hVB, ?_⟩
  intro k z hz
  let p := z.1
  let Q : Set M := (fun q => (p, q)) ⁻¹' V
  have hQ : IsOpen Q := hV.preimage (continuous_const.prodMk continuous_id)
  have hpS : p ∈ S := (hRT hz).1
  have hp : p ∈ e.baseSet :=
    e.mem_target.mp (hT (show (p, (0 : E)) ∈ S ×ˢ Metric.ball (0 : E) r from
      ⟨hpS, Metric.mem_ball_self hr⟩)).2
  have hΦp : ContMDiffOn 𝓘(ℝ, E) I ∞ (Φ p) (Metric.ball (0 : E) r) := by
    exact contMDiff_snd.comp_contMDiffOn
      (hF.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun v hv => ⟨hpS, hv⟩))
  have hΨp : ContMDiffOn I 𝓘(ℝ, E) ∞ (Ψ p) Q := by
    have hpair : ContMDiffOn I (I.prod I) ∞ (fun q : M => (p, q)) Q :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffOn
    have hread : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun q => (p, Ψ p q)) Q :=
      hR.comp hpair (fun _ hq => hq)
    have h := contMDiff_snd.comp_contMDiffOn hread
    exact h
  have hJp : ContDiffOn ℝ ∞ (J p) (Metric.ball (0 : E) r) := by
    have hpair : ContMDiffOn 𝓘(ℝ, E) (I.prod 𝓘(ℝ, E)) ∞
        (fun v : E => (p, v)) (Metric.ball (0 : E) r) :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffOn
    have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (J p) (Metric.ball (0 : E) r) :=
      hJ.comp (s := Metric.ball (0 : E) r) (f := fun v : E => (p, v)) hpair
        (fun v hv => (hT ⟨hpS, hv⟩).1)
    exact contMDiffOn_iff_contDiffOn.mp hcomp
  exact heatParametrixCoefficientInTrivialization_eqOn_fixed_of_domain B e hp
    Metric.isOpen_ball ((convex_ball (0 : E) r).starConvex (Metric.mem_ball_self hr)) hQ
    (fun _ hq => hVB hq) hΦp hΨp hJp (fun v hv => hJpos (p, v) (hT ⟨hpS, hv⟩).1)
    (fun v hv => hFV (x := (p, v)) ⟨hpS, hv⟩)
    (fun q hq => (hRT (x := (p, q)) hq).2) k hz

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem exists_contMDiffOn_heatParametrixCoefficientInCoordinates_fixed_prod
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagInvBranch g hEnorm c) :
    ∃ V : Set (M × M), IsOpen V ∧ (c, c) ∈ V ∧ V ⊆ B.dom ∧
      ∀ k : ℕ, ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : M × M => heatParametrixCoefficientInCoordinates g
          (B.fixed z.1).hom (B.fixed z.1).inv
          (fun v => paramDensity g (B.fixed z.1).hom v /
            paramDensity g (B.fixed z.1).hom 0) k z.2) V := by
  let e := trivializationAt E (TangentSpace I) c
  have hc : c ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) c
  obtain ⟨V, hV, hcV, hVB, heq⟩ :=
    B.exists_heatParametrixCoefficientInTrivialization_eqOn_fixed e hc
  obtain ⟨W, hW, hcW, _, hs⟩ :=
    B.exists_contMDiffOn_heatParametrixCoefficientInTrivialization_prod e hc
  refine ⟨V ∩ W, hV.inter hW, ⟨hcV, hcW⟩, inter_subset_left.trans hVB, ?_⟩
  intro k
  exact ((hs k).mono inter_subset_right).congr (fun z hz => (heq k hz.1).symm)

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem exists_contMDiffOn_laplacian_heatParametrixCoefficientInCoordinates_fixed_prod
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagInvBranch g hEnorm c) :
    ∃ V : Set (M × M), IsOpen V ∧ (c, c) ∈ V ∧ V ⊆ B.dom ∧
      ∀ k : ℕ, ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : M × M => laplacian (LeviCivita g) g
          (heatParametrixCoefficientInCoordinates g (B.fixed z.1).hom (B.fixed z.1).inv
            (fun v => paramDensity g (B.fixed z.1).hom v /
              paramDensity g (B.fixed z.1).hom 0) k) z.2) V := by
  obtain ⟨V, hV, hcV, hVB, hs⟩ :=
    B.exists_contMDiffOn_heatParametrixCoefficientInCoordinates_fixed_prod
  refine ⟨V, hV, hcV, hVB, ?_⟩
  intro k
  let a : M → M → ℝ := fun p q => heatParametrixCoefficientInCoordinates g
    (B.fixed p).hom (B.fixed p).inv
    (fun v => paramDensity g (B.fixed p).hom v / paramDensity g (B.fixed p).hom 0) k q
  have ha : ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞ (Function.uncurry a) V := hs k
  exact contMDiffOn_laplacian_leviCivita_prod_of_isOpen (IP := I) (f := a) g hV ha

end DifferentialGeometry.Geometry.Riemannian.Exponential.DiagInvBranch
