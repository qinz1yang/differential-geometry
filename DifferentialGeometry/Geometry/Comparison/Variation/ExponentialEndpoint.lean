import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import DifferentialGeometry.Geometry.Comparison.Variation.Coordinates.FixedChartIdentities
import DifferentialGeometry.Geometry.Geodesic.Flow.CrossVectorFieldReduction
import DifferentialGeometry.Geometry.Geodesic.Local.Uniqueness
import DifferentialGeometry.Bundle.FiberBundleHausdorff

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_clamped_geodesic_variation_on_compactCarrier
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (W : ℝ → E) (L : ℝ)
    (S : Set ℝ) (K : Set (TangentBundle I M))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun t ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (W t) :
          TangentBundle I M)))
    (hK : IsCompact K)
    (hinitK : ∀ t ∈ S,
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (γ t) (W t) : TangentBundle I M) ∈ K)
    (hLS : L ∈ S) :
    ∃ η : ℝ → ℝ, ∃ f : ℝ → ℝ → M,
      ContDiff ℝ ∞ η ∧
      η =ᶠ[nhds (0 : ℝ)] id ∧
      (∀ r : ℝ, |η r| ≤ 1) ∧
      IsSmoothVariation (I := I) f ∧
      (∀ t : ℝ, f 0 t = γ t) ∧
      (∀ t ∈ S,
        (mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ ↦ f r t) 0 (1 : ℝ) : E) = W t) ∧
      (W 0 = 0 → ∀ r : ℝ, f r 0 = γ 0) ∧
      (∀ (β : ℝ → M) (B : ℝ → TangentBundle I M),
        (fun r : ℝ ↦ (B r).proj) =ᶠ[nhds (0 : ℝ)] β →
        IsMIntegralCurveAt B
          (geodesicVectorFieldChart (I := I) g (γ L)) 0 →
        B 0 = (TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _)) (γ L) (W L) : TangentBundle I M) →
        (fun r : ℝ ↦ f r L) =ᶠ[nhds (0 : ℝ)] β) := by
  classical
  let init : ℝ → TangentBundle I M := fun t ↦
    (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (W t) :
      TangentBundle I M)
  obtain ⟨ψ, hψ, hψcompact, hψone⟩ := exists_bump_nhds (I := I.tangent) hK
  let X : (q : TangentBundle I M) → TangentSpace I.tangent q :=
    fun q ↦ ψ q • geodesicVectorField (I := I) g q
  have hX : ContMDiff I.tangent I.tangent.tangent ∞
      (fun q : TangentBundle I M ↦
        (⟨q, X q⟩ : TangentBundle I.tangent (TangentBundle I M))) := by
    exact hψ.smul_section (contMDiff_geodesicVectorField (I := I) g)
  have hXcompact : IsCompact (tsupport X) := by
    change HasCompactSupport (ψ • geodesicVectorField (I := I) g)
    exact hψcompact.smul_right
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let hcomplete : ∀ q : TangentBundle I M,
      ∃ c : ℝ → TangentBundle I M, c 0 = q ∧ IsMIntegralCurve c X :=
    exists_globalIntegralCurve_of_compactSupport
      (I := I.tangent) (M := TangentBundle I M) X hX hXcompact
  have hflow : ContMDiff (𝓘(ℝ, ℝ).prod I.tangent) I.tangent ∞
      (fun p : ℝ × TangentBundle I M ↦ curveAt X hcomplete p.2 p.1) :=
    contMDiff_globalFlow_joint_of_compactSupport
      (I := I.tangent) (M := TangentBundle I M) X hX hXcompact
  obtain ⟨η, hηsmooth, hηid, hηbound⟩ :=
    DifferentialGeometry.exists_smooth_bounded_eventuallyEq_id (by norm_num : (0 : ℝ) < 1)
  let f : ℝ → ℝ → M := fun r t ↦
    (curveAt X hcomplete (init t) (η r)).proj
  have hη0 : η 0 = 0 := by
    simpa only [id_eq] using hηid.self_of_nhds
  have hηM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (8 : ℕ) η := by
    rw [contMDiff_iff_contDiff]
    exact hηsmooth.of_le (by decide)
  have hfSmooth : IsSmoothVariation (I := I) f := by
    have hin : ContMDiff
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod I.tangent) (8 : ℕ)
        (fun p : ℝ × ℝ ↦ (η p.1, init p.2)) := by
      exact (hηM.comp contMDiff_fst).prodMk (hW.comp contMDiff_snd)
    have hlift : ContMDiff
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I.tangent (8 : ℕ)
        (fun p : ℝ × ℝ ↦ curveAt X hcomplete (init p.2) (η p.1)) :=
      (hflow.of_le
        (WithTop.coe_le_coe.mpr (le_top : (8 : ℕ∞) ≤ ⊤))).comp hin
    have hproj : ContMDiff I.tangent I (8 : ℕ)
        (fun q : TangentBundle I M ↦ q.proj) :=
      contMDiff_proj (TangentSpace I)
    exact hproj.comp hlift
  have hfCentral : ∀ t : ℝ, f 0 t = γ t := by
    intro t
    simp only [f, hη0, curveAt_zero]
    rfl
  have hrawField : ∀ t ∈ S,
      (mfderiv 𝓘(ℝ, ℝ) I
        (fun r : ℝ ↦ (curveAt X hcomplete (init t) r).proj) 0 (1 : ℝ) : E) = W t := by
    intro t ht
    let c : ℝ → TangentBundle I M := fun r ↦ curveAt X hcomplete (init t) r
    have hc : IsMIntegralCurve c X := curveAt_integralCurve X hcomplete (init t)
    have hinitK' : init t ∈ K := hinitK t ht
    have hψinit : ψ =ᶠ[nhds (init t)] 1 :=
      eventually_nhdsSet_iff_forall.mp hψone (init t) hinitK'
    have hψc : ∀ᶠ r in nhds 0, ψ (c r) = 1 := by
      have hc0 : Tendsto c (nhds 0) (nhds (init t)) := by
        rw [← curveAt_zero X hcomplete (init t)]
        exact (hc.continuous.continuousAt : ContinuousAt c 0)
      exact hψinit.comp_tendsto hc0
    have hsrc0 : (c 0).proj ∈ (chartAt H (γ t)).source := by
      simp only [c, curveAt_zero]
      exact mem_chart_source H (γ t)
    have hcproj : Continuous (fun r ↦ (c r).proj) :=
      ((contMDiff_proj (TangentSpace I) :
        ContMDiff I.tangent I ∞ (fun q : TangentBundle I M ↦ q.proj))).continuous.comp
        hc.continuous
    have hsrcc : ∀ᶠ r in nhds 0, (c r).proj ∈ (chartAt H (γ t)).source :=
      hcproj.continuousAt.eventually
        ((chartAt H (γ t)).open_source.mem_nhds hsrc0)
    have hchart : IsMIntegralCurveAt c
        (geodesicVectorFieldChart (I := I) g (γ t)) 0 := by
      rw [IsMIntegralCurveAt]
      filter_upwards [hc.isMIntegralCurveAt 0, hψc, hsrcc] with r hr hψr hsrcr
      have hXr : X (c r) = geodesicVectorFieldChart (I := I) g (γ t) (c r) := by
        change ψ (c r) • geodesicVectorField (I := I) g (c r) = _
        rw [hψr, one_smul]
        exact (geodesicVectorFieldChart_eq_geodesicVectorField
          (I := I) g (γ t) hsrcr).symm
      rwa [← hXr]
    have hvel := hchart.mfderiv_proj_one hsrc0
    have hc0 : c 0 = init t := curveAt_zero X hcomplete (init t)
    rw [hc0] at hvel
    convert hvel using 1
    all_goals rfl
  have hfField : ∀ t ∈ S,
      (mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ ↦ f r t) 0 (1 : ℝ) : E) = W t := by
    intro t ht
    have heq : (fun r : ℝ ↦ f r t) =ᶠ[nhds (0 : ℝ)]
        (fun r : ℝ ↦ (curveAt X hcomplete (init t) r).proj) := by
      filter_upwards [hηid] with r hr
      simp only [f, id_eq] at hr ⊢
      rw [hr]
    rw [heq.mfderiv_eq]
    exact hrawField t ht
  have hfFixInitial : W 0 = 0 → ∀ r : ℝ, f r 0 = γ 0 := by
    intro hW0 r
    have hX0 : X (init 0) = 0 := by
      have hinit0 : init 0 =
          (⟨γ 0, (0 : E)⟩ : TangentBundle I M) := by
        simp only [init, hW0]
      rw [hinit0]
      simp only [X, geodesicVectorField_zero_section]
      exact smul_zero _
    have hconst : IsMIntegralCurve (fun _ : ℝ ↦ init 0) X := by
      intro s
      rw [hX0, ContinuousLinearMap.smulRight_zero]
      exact hasMFDerivAt_const (c := init 0) (x := s)
        (I := 𝓘(ℝ, ℝ)) (I' := I.tangent)
    have hXone : ContMDiff I.tangent I.tangent.tangent 1
        (fun q : TangentBundle I M ↦
          (⟨q, X q⟩ : TangentBundle I.tangent (TangentBundle I M))) :=
      hX.of_le (by norm_num)
    have heq := integralCurve_eq_of_agree_zero X hXone
      (curveAt_integralCurve X hcomplete (init 0)) hconst (by rw [curveAt_zero])
    have hcurve := congrFun heq (η r)
    simp only [f, hcurve, init]
  have hfTerminal : ∀ (β : ℝ → M) (B : ℝ → TangentBundle I M),
      (fun r : ℝ ↦ (B r).proj) =ᶠ[nhds (0 : ℝ)] β →
      IsMIntegralCurveAt B (geodesicVectorFieldChart (I := I) g (γ L)) 0 →
      B 0 = init L →
      (fun r : ℝ ↦ f r L) =ᶠ[nhds (0 : ℝ)] β := by
    intro β B hBproj hBint hB0
    let c : ℝ → TangentBundle I M := fun r ↦ curveAt X hcomplete (init L) r
    have hc : IsMIntegralCurve c X := curveAt_integralCurve X hcomplete (init L)
    have hLK : init L ∈ K := hinitK L hLS
    have hψinit : ψ =ᶠ[nhds (init L)] 1 :=
      eventually_nhdsSet_iff_forall.mp hψone (init L) hLK
    have hψc : ∀ᶠ r in nhds 0, ψ (c r) = 1 := by
      have hc0 : Tendsto c (nhds 0) (nhds (init L)) := by
        rw [← curveAt_zero X hcomplete (init L)]
        exact (hc.continuous.continuousAt : ContinuousAt c 0)
      exact hψinit.comp_tendsto hc0
    have hsrc0 : (c 0).proj ∈ (chartAt H (γ L)).source := by
      simp only [c, curveAt_zero]
      exact mem_chart_source H (γ L)
    have hcproj : Continuous (fun r ↦ (c r).proj) :=
      ((contMDiff_proj (TangentSpace I) :
        ContMDiff I.tangent I ∞ (fun q : TangentBundle I M ↦ q.proj))).continuous.comp
        hc.continuous
    have hsrcc : ∀ᶠ r in nhds 0, (c r).proj ∈ (chartAt H (γ L)).source :=
      hcproj.continuousAt.eventually
        ((chartAt H (γ L)).open_source.mem_nhds hsrc0)
    have hcChart : IsMIntegralCurveAt c
        (geodesicVectorFieldChart (I := I) g (γ L)) 0 := by
      rw [IsMIntegralCurveAt]
      filter_upwards [hc.isMIntegralCurveAt 0, hψc, hsrcc] with r hr hψr hsrcr
      have hXr : X (c r) = geodesicVectorFieldChart (I := I) g (γ L) (c r) := by
        change ψ (c r) • geodesicVectorField (I := I) g (c r) = _
        rw [hψr, one_smul]
        exact (geodesicVectorFieldChart_eq_geodesicVectorField
          (I := I) g (γ L) hsrcr).symm
      rwa [← hXr]
    have hc0 : c 0 = init L := curveAt_zero X hcomplete (init L)
    have hcb : c =ᶠ[nhds (0 : ℝ)] B :=
      isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
        (I := I) (g := g) (t₀ := 0) hsrc0 hcChart hBint (hc0.trans hB0.symm)
    have hηtendsto : Tendsto η (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
      have hcont : ContinuousAt η (0 : ℝ) := hηsmooth.continuous.continuousAt
      change Tendsto η (nhds (0 : ℝ)) (nhds (η 0)) at hcont
      simpa only [hη0] using hcont
    have hcbη : ∀ᶠ r in nhds (0 : ℝ), c (η r) = B (η r) :=
      hηtendsto.eventually hcb
    have hBprojη : ∀ᶠ r in nhds (0 : ℝ), (B (η r)).proj = β (η r) :=
      hηtendsto.eventually hBproj
    filter_upwards [hcbη, hBprojη, hηid] with r hcr hBr hηr
    simp only [id_eq] at hηr
    change (c (η r)).proj = β r
    rw [hcr, hBr, hηr]
  refine ⟨η, f, hηsmooth, hηid, hηbound, hfSmooth, hfCentral, hfField,
    hfFixInitial, ?_⟩
  intro β B hBproj hBint hB0
  exact hfTerminal β B hBproj hBint hB0

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_clamped_geodesic_variation
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (W : ℝ → E) (L : ℝ)
    (hL : 0 ≤ L)
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun t ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (W t) :
          TangentBundle I M))) :
    ∃ η : ℝ → ℝ, ∃ f : ℝ → ℝ → M,
      ContDiff ℝ ∞ η ∧
      η =ᶠ[nhds (0 : ℝ)] id ∧
      (∀ r : ℝ, |η r| ≤ 1) ∧
      IsSmoothVariation (I := I) f ∧
      (∀ t : ℝ, f 0 t = γ t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L,
        (mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ ↦ f r t) 0 (1 : ℝ) : E) = W t) ∧
      (W 0 = 0 → ∀ r : ℝ, f r 0 = γ 0) ∧
      (∀ (β : ℝ → M) (B : ℝ → TangentBundle I M),
        (fun r : ℝ ↦ (B r).proj) =ᶠ[nhds (0 : ℝ)] β →
        IsMIntegralCurveAt B
          (geodesicVectorFieldChart (I := I) g (γ L)) 0 →
        B 0 = (TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _)) (γ L) (W L) : TangentBundle I M) →
        (fun r : ℝ ↦ f r L) =ᶠ[nhds (0 : ℝ)] β) := by
  let init : ℝ → TangentBundle I M := fun t ↦
    (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (W t) :
      TangentBundle I M)
  let K : Set (TangentBundle I M) := init '' Set.Icc (0 : ℝ) L
  apply exists_clamped_geodesic_variation_on_compactCarrier
    (I := I) g γ W L (Set.Icc (0 : ℝ) L) K hW
  · exact isCompact_Icc.image hW.continuous
  · intro t ht
    exact ⟨t, ht, rfl⟩
  · exact ⟨hL, le_rfl⟩

omit [NeZero (Module.finrank ℝ E)] [T2Space M] in
theorem exists_centered_lift_of_isGeodesicAt
    (g : SmoothRiemannianMetric I M)
    (β : ℝ → M) (p : M) (v : E)
    (hβgeo : IsGeodesicAt (I := I) g β 0)
    (hβ0 : β 0 = p)
    (hβv : (mfderiv 𝓘(ℝ, ℝ) I β 0 (1 : ℝ) : E) = v) :
    ∃ B : ℝ → TangentBundle I M,
      (fun r : ℝ ↦ (B r).proj) =ᶠ[nhds (0 : ℝ)] β ∧
      IsMIntegralCurveAt B (geodesicVectorFieldChart (I := I) g p) 0 ∧
      B 0 = (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) p v : TangentBundle I M) := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨B, hBproj0, hBint0, hβB⟩ :=
    gc_cross_vf_projection_uniqueness (I := I) (g := g) (t₀ := 0) hβgeo
  have hBint : IsMIntegralCurveAt B
      (geodesicVectorFieldChart (I := I) g p) 0 := by
    rw [← hβ0]
    exact hBint0
  have hsrc0 : (B 0).proj ∈ (chartAt H p).source := by
    rw [hBproj0, hβ0]
    exact mem_chart_source H p
  have hvelLift := hBint.mfderiv_proj_one hsrc0
  have hβv' :
      (mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ ↦ (B r).proj) 0 (1 : ℝ) : E) = v := by
    rw [← hβB.mfderiv_eq]
    exact hβv
  have hBsnd : ((B 0).snd : E) = v := by
    exact hvelLift.symm.trans hβv'
  refine ⟨B, hβB.symm, hBint, ?_⟩
  apply TotalSpace.ext
  · exact hBproj0.trans hβ0
  · exact heq_of_eq hBsnd

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
