import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CorrectionAtBasepoint
import DifferentialGeometry.Geometry.Connection.LeviCivita.AlongCurve
import DifferentialGeometry.Geometry.Curvature.Coordinates.ChristoffelContraction
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Comparison.Variation.Coordinates.FixedChartIdentities
import DifferentialGeometry.Bundle.PartialMfderiv.TimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.DifferenceTimeDerivative
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem hasDerivWithinAt_fderiv_slice_fst_comm
    (F : ℝ × ℝ → E) (x t : ℝ) {J : Set ℝ}
    (huniqJ : UniqueDiffOn ℝ J) (htJ : t ∈ J) (hcl : t ∈ closure (interior J))
    (hF : ∀ᶠ z in 𝓝[univ ×ˢ J] (x, t), ContDiffWithinAt ℝ 2 F (univ ×ˢ J) z) :
    HasDerivWithinAt (fun s => fderiv ℝ (fun u => F (u, s)) x 1)
      (fderiv ℝ (fun u => fderivWithin ℝ (fun s => F (u, s)) J t 1) x 1) J t := by
  classical
  set S : Set (ℝ × ℝ) := univ ×ˢ J with hS
  have hSuniq : UniqueDiffOn ℝ S := by
    rw [hS]; exact UniqueDiffOn.prod uniqueDiffOn_univ huniqJ
  have hxS : (x, t) ∈ S := by rw [hS]; exact ⟨mem_univ x, htJ⟩
  have hmem : ∀ u v : ℝ, v ∈ J → (u, v) ∈ S := fun u v hv => by
    rw [hS]; exact ⟨mem_univ u, hv⟩
  have hSdef : S = univ ×ˢ J := hS
  have htendR : Filter.Tendsto (fun v : ℝ => ((x, v) : ℝ × ℝ)) (𝓝[J] t)
      (𝓝[univ ×ˢ J] ((x, t) : ℝ × ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · exact ((hasFDerivAt_prodMk_right (𝕜 := ℝ) x t).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact hmem x v hv
  have hFt : ContDiffWithinAt ℝ 2 F S (x, t) := by
    rw [hSdef]; exact hF.self_of_nhdsWithin hxS
  have hDd : DifferentiableWithinAt ℝ (fderivWithin ℝ F S) S (x, t) :=
    (hFt.fderivWithin_right hSuniq (m := 1) (by norm_num) hxS).differentiableWithinAt
      (by norm_num)
  set D : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] E) :=
    fderivWithin ℝ (fderivWithin ℝ F S) S (x, t) with hD
  set ev₁ : ((ℝ × ℝ) →L[ℝ] E) →L[ℝ] E :=
    ContinuousLinearMap.apply ℝ E ((1 : ℝ), (0 : ℝ)) with hev₁
  have hev₁_apply : ∀ L : (ℝ × ℝ) →L[ℝ] E, ev₁ L = L (1, 0) := by
    intro L; simp [hev₁]
  have hP : HasFDerivWithinAt (fun z : ℝ × ℝ => fderivWithin ℝ F S z (1, 0))
      (ev₁.comp D) S (x, t) :=
    HasFDerivAt.comp_hasFDerivWithinAt (x := (x, t))
      (ContinuousLinearMap.hasFDerivAt ev₁) hDd.hasFDerivWithinAt
  have hι : HasFDerivWithinAt (fun v : ℝ => (x, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) J t :=
    (hasFDerivAt_prodMk_right x t).hasFDerivWithinAt
  have hmap : MapsTo (fun v : ℝ => (x, v)) J S := fun v hv => hmem x v hv
  have hcomp := HasFDerivWithinAt.comp (x := t) hP hι hmap
  have hmain : HasDerivWithinAt (fun v : ℝ => fderivWithin ℝ F S (x, v) (1, 0))
      (D (0, 1) (1, 0)) J t := by
    have h2 := congrArg (fun L : ℝ →L[ℝ] E => L 1) (hcomp.fderivWithin (huniqJ t htJ))
    have h3 : ((ev₁ ∘SL D) ∘SL ContinuousLinearMap.inr ℝ ℝ ℝ) 1 = D (0, 1) (1, 0) := by
      simp only [hev₁_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact hcomp.hasDerivWithinAt.congr_deriv h3
  have hPid : (fun v : ℝ => fderiv ℝ (fun u => F (u, v)) x 1)
      =ᶠ[𝓝[J] t] (fun v : ℝ => fderivWithin ℝ F S (x, v) (1, 0)) := by
    filter_upwards [self_mem_nhdsWithin, htendR.eventually hF] with v hv hcv
    have hd : DifferentiableWithinAt ℝ F S (x, v) := hcv.differentiableWithinAt (by norm_num)
    have hι' : HasFDerivWithinAt (fun u : ℝ => (u, v)) (ContinuousLinearMap.inl ℝ ℝ ℝ) univ x :=
      (hasFDerivAt_prodMk_left x v).hasFDerivWithinAt
    have hmap' : MapsTo (fun u : ℝ => (u, v)) univ S := fun u _ => hmem u v hv
    have hcomp' := HasFDerivWithinAt.comp (x := x) hd.hasFDerivWithinAt hι' hmap'
    have h1 : fderivWithin ℝ (fun u : ℝ => F (u, v)) univ x
        = (fderivWithin ℝ F S (x, v)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) :=
      hcomp'.fderivWithin uniqueDiffWithinAt_univ
    rw [fderivWithin_univ] at h1
    have h2 := congrArg (fun L : ℝ →L[ℝ] E => L 1) h1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at h2
    simpa using h2
  have hx_eq : fderiv ℝ (fun u => F (u, t)) x 1 = fderivWithin ℝ F S (x, t) (1, 0) :=
    hPid.self_of_nhdsWithin htJ
  have hfin : HasDerivWithinAt (fun s => fderiv ℝ (fun u => F (u, s)) x 1)
      (D (0, 1) (1, 0)) J t := hmain.congr_of_eventuallyEq hPid hx_eq
  refine hfin.congr_deriv ?_
  rw [← hfin.derivWithin (huniqJ t htJ),
    DifferentialGeometry.Geometry.Riemannian.Variation.mixed_partialFderivWithin_comm
      F x t huniqJ htJ hcl hF, fderiv_apply_one_eq_deriv]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem hasDerivWithinAt_comp_pair_tendsto
    {Θ : ℝ × E → ℝ} {L : (ℝ × E) →L[ℝ] ℝ} {y : ℝ → E} {y' : E}
    {J : Set ℝ} {S : Set E} {t : ℝ}
    (hΘ : HasFDerivWithinAt Θ L (J ×ˢ S) (t, y t))
    (hy : HasDerivWithinAt y y' J t) (hS : S ∈ 𝓝 (y t)) :
    HasDerivWithinAt (fun r => Θ (r, y r)) (L (1, 0) + L (0, y')) J t := by
  have htend : Filter.Tendsto (fun r : ℝ => (r, y r)) (𝓝[J] t) (𝓝[J ×ˢ S] (t, y t)) := by
    rw [nhdsWithin_prod_eq, nhdsWithin_eq_nhds.mpr hS]
    exact Filter.tendsto_id.prodMk hy.continuousWithinAt
  have hφ : HasFDerivWithinAt (fun r : ℝ => (r, y r))
      (ContinuousLinearMap.toSpanSingleton ℝ (((1 : ℝ), y') : ℝ × E)) J t :=
    ((hasDerivWithinAt_id t J).prodMk hy).hasFDerivWithinAt
  have hcomp := hΘ.comp_of_tendsto t hφ htend
  refine hcomp.hasDerivWithinAt.congr_deriv ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply_one]
  rw [show (((1 : ℝ), y') : ℝ × E) = ((1 : ℝ), (0 : E)) + ((0 : ℝ), y') by simp, map_add]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CurveMap

def Field.SmoothOn {c : CurveMap M} (V : c.Field (I := I)) (J : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I.tangent ∞
    (fun p : ℝ × ℝ => (⟨c.lift p.1 p.2, V p.1 p.2⟩ : TangentBundle I M))
    (univ ×ˢ J)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem Field.smoothOn_X (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J) :
    CurveMap.Field.SmoothOn (I := I) (c.X) J := by
  have hc' : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ => c.lift p.1 p.2) (univ ×ˢ J) := by
    rw [CurveMap.SmoothOn] at hc
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hc
    exact hc
  have h := ContMDiffOn.time_mfderivWithin (I := 𝓘(ℝ, ℝ)) (I' := I) (N := M)
    (γ := fun x t => c.lift x t) (s := univ) (u := J) (n := ∞) (m := ∞)
    hc' uniqueDiffOn_univ le_rfl
  rw [CurveMap.Field.SmoothOn, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact h.congr (fun p hp => by
    simp only [CurveMap.X, mfderivWithin_univ]
    rfl)

omit [CompleteSpace E] in
theorem Field.smoothOn_inner {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) J)
    (V W : c.Field (I := I)) (hV : V.SmoothOn (I := I) J) (hW : W.SmoothOn (I := I) J) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => (g p.2).inner (c.lift p.1 p.2) (V p.1 p.2) (W p.1 p.2))
      (univ ×ˢ J) := by
  have hΨ := MetricFamilySmoothOn.metricCLMSection_contMDiffOn (I := I) (M := M) hG hJ
  intro p hp
  have hπ : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × ℝ => q.2) (univ ×ˢ J) p := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_snd
  have hΦ : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × ℝ => (q.2, c.lift q.1 q.2)) (univ ×ˢ J) p :=
    hπ.prodMk (hc p hp)
  have hmaps : MapsTo (fun q : ℝ × ℝ => (q.2, c.lift q.1 q.2)) (univ ×ˢ J)
      (J ×ˢ (univ : Set M)) := fun q hq => ⟨hq.2, mem_univ _⟩
  have hψ : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × ℝ => (⟨c.lift q.1 q.2, (g q.2).inner (c.lift q.1 q.2)⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (univ ×ˢ J) p :=
    (hΨ (p.2, c.lift p.1 p.2) ⟨hp.2, mem_univ _⟩).comp p hΦ hmaps
  have hv : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × ℝ => TotalSpace.mk' E (c.lift q.1 q.2) (V q.1 q.2)) (univ ×ˢ J) p :=
    hV p hp
  have hw : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × ℝ => TotalSpace.mk' E (c.lift q.1 q.2) (W q.1 q.2)) (univ ×ˢ J) p :=
    hW p hp
  have happ := ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ)
    (b := fun q : ℝ × ℝ => c.lift q.1 q.2) (s := univ ×ˢ J) (x := p)
    (ψ := fun q : ℝ × ℝ => (g q.2).inner (c.lift q.1 q.2))
    (v := fun q : ℝ × ℝ => V q.1 q.2) (w := fun q : ℝ × ℝ => W q.1 q.2)
    hψ hv hw
  rw [Bundle.contMDiffWithinAt_totalSpace] at happ
  exact happ.2.contDiffWithinAt

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem Field.smoothOn_const_smul (c : CurveMap M) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (a : ℝ → ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => a p.1 p.2) (univ ×ˢ J))
    (V : c.Field (I := I)) (hV : V.SmoothOn (I := I) J) :
    CurveMap.Field.SmoothOn (I := I) (fun x t => a x t • V x t) J := by
  intro p hp
  let e := trivializationAt E (TangentSpace I) (c.lift p.1 p.2)
  have hbase : c.lift p.1 p.2 ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (c.lift p.1 p.2)
  have hlift : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun q : ℝ × ℝ => c.lift q.1 q.2)
      (univ ×ˢ J) p := hc p hp
  have hVrep : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
      (fun q : ℝ × ℝ =>
        (e (⟨c.lift q.1 q.2, V q.1 q.2⟩ : TangentBundle I M)).2) (univ ×ˢ J) p :=
    (Bundle.contMDiffWithinAt_totalSpace.mp (hV p hp)).2
  have hsm : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
      (fun q : ℝ × ℝ =>
        a q.1 q.2 • (e (⟨c.lift q.1 q.2, V q.1 q.2⟩ : TangentBundle I M)).2)
      (univ ×ˢ J) p :=
    ((contMDiffWithinAt_iff_contDiffWithinAt.mpr (ha.contDiffWithinAt hp)).smul hVrep)
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨hlift, ?_⟩
  refine hsm.congr_of_eventuallyEq ?_ ?_
  · have hneigh : (fun q : ℝ × ℝ => c.lift q.1 q.2) ⁻¹' e.baseSet ∈ 𝓝[univ ×ˢ J] p :=
      hlift.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)
    filter_upwards [hneigh, self_mem_nhdsWithin] with q hq _
    exact (e.linear ℝ hq).map_smul (a q.1 q.2) (V q.1 q.2)
  · exact (e.linear ℝ hbase).map_smul (a p.1 p.2) (V p.1 p.2)

omit [CompleteSpace E] in
theorem Field.smoothOn_speed {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.speed g p.1 p.2) (univ ×ˢ J) := by
  have hX : CurveMap.Field.SmoothOn (I := I) (c.X) J := CurveMap.Field.smoothOn_X c J hc
  have hinner := Field.smoothOn_inner g hG hJ c hc (c.X) (c.X) hX hX
  have hfun : (fun p : ℝ × ℝ => c.speed g p.1 p.2) =
      fun p : ℝ × ℝ =>
        Real.sqrt ((g p.2).inner (c.lift p.1 p.2) (c.X p.1 p.2) (c.X p.1 p.2)) := rfl
  rw [hfun]
  refine hinner.sqrt ?_
  intro p hp
  exact ne_of_gt ((g p.2).pos (c.lift p.1 p.2) (c.X p.1 p.2) (hi p.1 p.2 hp.2))

omit [CompleteSpace E] in
theorem Field.smoothOn_unitTangent {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) :
    CurveMap.Field.SmoothOn (I := I) (c.unitTangent g) J := by
  have hX : CurveMap.Field.SmoothOn (I := I) (c.X) J := CurveMap.Field.smoothOn_X c J hc
  have hsp : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.speed g p.1 p.2) (univ ×ˢ J) :=
    Field.smoothOn_speed g hG hJ c hc hi
  have hinv : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (c.speed g p.1 p.2)⁻¹) (univ ×ˢ J) := by
    refine hsp.inv ?_
    intro p hp
    exact ne_of_gt (c.speed_pos g hi p.1 p.2 hp.2)
  have htan : c.unitTangent g = fun x t => (c.speed g x t)⁻¹ • c.X x t := rfl
  rw [htan]
  exact Field.smoothOn_const_smul c hc (fun x t => (c.speed g x t)⁻¹) hinv (c.X) hX


omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem Field.smoothOn_velocity (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hJ : UniqueDiffOn ℝ J) :
    CurveMap.Field.SmoothOn (I := I) (c.velocity (I := I) J) J := by
  have hc' : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ => c.lift p.1 p.2) (univ ×ˢ J) := by
    rw [CurveMap.SmoothOn] at hc
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hc
    exact hc
  have h := ContMDiffOn.mfderivWithin_snd (I' := I) (N := M)
    (γ := fun a b : ℝ => c.lift a b) (s := (univ : Set ℝ)) (u := J)
    (n := ∞) (m := ∞) hc' hJ le_rfl
  rw [CurveMap.Field.SmoothOn, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  refine h.congr (fun p hp => ?_)
  simp only [CurveMap.velocity]
  congr 1

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem Field.smoothOn_sub {c : CurveMap M} {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (V W : c.Field (I := I)) (hV : V.SmoothOn (I := I) J) (hW : W.SmoothOn (I := I) J) :
    CurveMap.Field.SmoothOn (I := I) (fun x t => V x t - W x t) J := by
  intro p hp
  let e := trivializationAt E (TangentSpace I) (c.lift p.1 p.2)
  have hbase : c.lift p.1 p.2 ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (c.lift p.1 p.2)
  have hVrep : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
      (fun q : ℝ × ℝ => (e (⟨c.lift q.1 q.2, V q.1 q.2⟩ : TangentBundle I M)).2)
      (univ ×ˢ J) p := (Bundle.contMDiffWithinAt_totalSpace.mp (hV p hp)).2
  have hWrep : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
      (fun q : ℝ × ℝ => (e (⟨c.lift q.1 q.2, W q.1 q.2⟩ : TangentBundle I M)).2)
      (univ ×ˢ J) p := (Bundle.contMDiffWithinAt_totalSpace.mp (hW p hp)).2
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨hc p hp, ?_⟩
  refine (hVrep.sub hWrep).congr_of_eventuallyEq ?_ ?_
  · have hneigh : (fun q : ℝ × ℝ => c.lift q.1 q.2) ⁻¹' e.baseSet ∈ 𝓝[univ ×ˢ J] p :=
      (hc p hp).continuousWithinAt.preimage_mem_nhdsWithin
        (e.open_baseSet.mem_nhds hbase)
    filter_upwards [hneigh, self_mem_nhdsWithin] with q hq _
    exact (e.linear ℝ hq).map_sub (V q.1 q.2) (W q.1 q.2)
  · exact (e.linear ℝ hbase).map_sub (V p.1 p.2) (W p.1 p.2)


omit [CompleteSpace E] in
theorem Dt_eq_covDerivAlong (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (V : c.Field (I := I)) (x t : ℝ) (ht : J ∈ 𝓝 t) :
    c.Dt g J V x t = covDerivAlong (g t) (c.lift x) (V x) t := by
  simp only [Dt, covDerivAlong, chartCovDerivAlong, derivWithin_of_mem_nhds ht]

end CurveMap

variable [SigmaCompactSpace M] [T2Space M]


def connectionVariation (G : SolutionFamily (I := I) (M := M)) (J : Set ℝ)
    (t : ℝ) (p : M) (A B : TangentSpace I p) : TangentSpace I p :=
  derivWithin (fun s => G.connection s (tangentConstAt (I := I) p B) p A) J t

def nablaRicci (G : SolutionFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (A B Z : TangentSpace I p) : ℝ :=
  totalNabla0SFun 2 (G.connection t) (G.ricci t) p (Fin.cons A (vec2 B Z))

def riemannVector (G : SolutionFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (A B Z : TangentSpace I p) : TangentSpace I p :=
  connectionRiemannCurvatureField (G.connection t)
    (tangentConstAt (I := I) p A) (tangentConstAt (I := I) p B)
    (tangentConstAt (I := I) p Z) p

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hasDerivWithinAt_of_metric_pairings
    (g : SmoothRiemannianMetric I M) (p : M) (V : ℝ → TangentSpace I p)
    (Z : TangentSpace I p) {J : Set ℝ} {t : ℝ}
    (h : ∀ w : TangentSpace I p,
      HasDerivWithinAt (fun r => g.inner p (V r) w) (g.inner p Z w) J t) :
    HasDerivWithinAt V Z J t := by
  classical
  let : FiniteDimensional ℝ (TangentSpace I p) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TangentSpace I p)
  have hrec (w : TangentSpace I p) :
      (∑ i, g.inner p w (metricSharp g p (b.coord i)) • b i) = w := by
    simp only [inner_metricSharp_right]
    exact b.sum_repr w
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ)
    (fun i _ => (h (metricSharp g p (b.coord i))).smul_const (b i))
  simpa only [hrec] using hsum

variable [hBoundary : I.Boundaryless]
include hBoundary

omit [SigmaCompactSpace M] in
private theorem hasDerivWithinAt_spatialConnection {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) (A V : TangentSpace I p) :
    HasDerivWithinAt
      (fun r => B.family.connection r (tangentConstAt (I := I) p V) p A)
      (connectionVariationSpeed (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩)
        t p V A) (Icc a b) t := by
  let S : SolutionOn (I := I) (M := M) D := ⟨B.family⟩
  let delta : ℝ → TangentSpace I p := fun r =>
    CovariantDerivative.difference (LeviCivita (S.base.metric r))
      (LeviCivita (S.base.metric 0)) p V A
  let Z := connectionVariationSpeed S t p V A
  have hvec : HasDerivWithinAt delta Z (Icc a b) t :=
    hasDerivWithinAt_of_metric_pairings (S.base.metric 0) p delta Z
      (fun w => hasDerivWithinAt_connectionDifference_pairing S B.equation
        (B.regular.trans D.regular_subset) (B.regular ht) p V A w)
  let fixed := B.family.connection 0 (tangentConstAt (I := I) p V) p A
  have hdelta (r : ℝ) : delta r =
      B.family.connection r (tangentConstAt (I := I) p V) p A - fixed := by
    have h := DifferentialGeometry.PDE.DeTurck.connectionDifference_apply
      (S.base.metric r) (S.base.metric 0)
      (mdifferentiableAt_tangentConstAt_self (I := I) p V) A
    simpa only [DifferentialGeometry.PDE.DeTurck.connectionDifference,
      tangentConstAt_self, delta, fixed, S, SolutionFamily.connection, LeviCivita] using h
  have hsum := hvec.add_const fixed
  have hf : (fun r => delta r + fixed) =
      (fun r => B.family.connection r (tangentConstAt (I := I) p V) p A) := by
    funext r
    rw [hdelta, sub_add_cancel]
  rw [hf] at hsum
  exact hsum

omit [SigmaCompactSpace M] in
private theorem connectionVariation_eq_nativeSpeed {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) (A V : TangentSpace I p) :
    connectionVariation B.family (Icc a b) t p A V =
      connectionVariationSpeed (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩)
        t p V A :=
  (hasDerivWithinAt_spatialConnection B t ht p A V).derivWithin
    ((uniqueDiffOn_Icc B.lt) t ht)

omit [SigmaCompactSpace M] hBoundary in
private theorem nablaRicci_eq_metricNablaRic
    (G : SolutionFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (A V Z : TangentSpace I p) :
    nablaRicci G t p A V Z = metricNablaRic (G.metric t) p (vec3 A V Z) := by
  change metricNablaRic (G.metric t) p (Fin.cons A (vec2 V Z)) = _
  congr 1
  funext i
  fin_cases i <;> rfl

omit [SigmaCompactSpace M] hBoundary in
private theorem nablaRicci_last_two_symm
    (G : SolutionFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (A V Z : TangentSpace I p) : nablaRicci G t p A V Z = nablaRicci G t p A Z V := by
  simpa only [nablaRicci_eq_metricNablaRic] using
    metricNablaRic_last_two_symm (G.metric t) p A V Z

omit [SigmaCompactSpace M] in
theorem rfs_csf_connection [_sigmaCompactM : SigmaCompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) (A V Z : TangentSpace I p) :
    (B.family.metric t).inner p (connectionVariation B.family (Icc a b) t p A V) Z =
      -nablaRicci B.family t p A V Z - nablaRicci B.family t p V A Z +
        nablaRicci B.family t p Z A V := by
  rw [connectionVariation_eq_nativeSpeed B t ht p A V]
  have hpair :
      (B.family.metric t).inner p
        (connectionVariationSpeed (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩)
          t p V A) Z =
      -nablaRicci B.family t p V A Z - nablaRicci B.family t p A V Z +
        nablaRicci B.family t p Z V A := by
    simp only [nablaRicci_eq_metricNablaRic]
    exact inner_metricSharp (B.family.metric t) p
      (koszulRicciCovector
        (DifferentialGeometry.PDE.RicciFlow.nablaRicci
          (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩) t p) V A) Z
  rw [hpair, nablaRicci_last_two_symm B.family t p Z V A]
  ring


theorem connectionVariation_tensor {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) :
    (∀ A V, connectionVariation B.family (Icc a b) t p A V =
      connectionVariation B.family (Icc a b) t p V A) ∧
    (∀ A A' V, connectionVariation B.family (Icc a b) t p (A + A') V =
      connectionVariation B.family (Icc a b) t p A V +
      connectionVariation B.family (Icc a b) t p A' V) ∧
    (∀ (r : ℝ) A V, connectionVariation B.family (Icc a b) t p (r • A) V =
      r • connectionVariation B.family (Icc a b) t p A V) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A V
    apply metricFlatLinear_injective (B.family.metric t) p
    ext Z
    change (B.family.metric t).inner p (connectionVariation B.family (Icc a b) t p A V) Z =
      (B.family.metric t).inner p (connectionVariation B.family (Icc a b) t p V A) Z
    rw [rfs_csf_connection B t ht p A V Z, rfs_csf_connection B t ht p V A Z,
      nablaRicci_last_two_symm B.family t p Z V A]
    ring
  · intro A A' V
    unfold connectionVariation
    simp only [map_add]
    exact derivWithin_fun_add
      (hasDerivWithinAt_spatialConnection B t ht p A V).differentiableWithinAt
      (hasDerivWithinAt_spatialConnection B t ht p A' V).differentiableWithinAt
  · intro r A V
    unfold connectionVariation
    simp only [map_smul]
    exact derivWithin_fun_const_smul r
      (hasDerivWithinAt_spatialConnection B t ht p A V).differentiableWithinAt


omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem chartGramOnE_sum_eq_inner
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {t : ℝ}
    (hγ : γ t ∈ (trivializationAt E (TangentSpace I) α).baseSet) (A B : E) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
          chartCoord (E := E) i A * chartCoord (E := E) j B) =
      g.inner (γ t)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t) A)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t) B) := by
  classical
  rw [inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α A B]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have hsrc : γ t ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := I)]
    rwa [TangentBundle.trivializationAt_baseSet] at hγ
  rw [chartGramOnE_def, chartCurve_def, (extChartAt I α).left_inv hsrc]

omit [SigmaCompactSpace M] in
lemma chartGramOnE_metricFamily_differentiableAt
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (α : M) (γ : ℝ → M) {t : ℝ} (ht : t ∈ D.regular) (hγt : γ t = α)
    (i j : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (fun q : ℝ × E => chartGramOnE (I := I) (B.family.metric q.1) α i j q.2)
      (t, chartCurve (I := I) α γ t) := by
  classical
  have hsrc : α ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H α
  have hUt : chartCurve (I := I) α γ t ∈ (extChartAt I α).target := by
    rw [chartCurve_def, hγt]
    exact (extChartAt I α).map_source hsrc
  have hinv : (extChartAt I α).symm (chartCurve (I := I) α γ t) = α := by
    rw [chartCurve_def, hγt]
    exact (extChartAt I α).left_inv hsrc
  let e := trivializationAt E (TangentSpace I) α
  let b := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) (e.localFrame b) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  have hcompOn := B.smooth.frameCompSmooth (e.localFrame b) hframe i j
  have hbase : α ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hcompAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun q : ℝ × M =>
        (B.family.metric q.1).inner q.2 (e.localFrame b i q.2) (e.localFrame b j q.2))
      (t, α) :=
    hcompOn.contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds ht) (e.open_baseSet.mem_nhds hbase))
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞)
      (extChartAt I α).symm (chartCurve (I := I) α γ t) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := (∞ : WithTop ℕ∞)) α).contMDiffAt
      ((isOpen_extChartAt_target (I := I) α).mem_nhds hUt)
  have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) (∞ : WithTop ℕ∞)
      (fun q : ℝ × E => (q.1, (extChartAt I α).symm q.2))
      (t, chartCurve (I := I) α γ t) :=
    contMDiffAt_fst.prodMk (hsymm.comp (t, chartCurve (I := I) α γ t) contMDiffAt_snd)
  have hjoint0 := hcompAt.comp_of_eq hmap (by simp only [hinv])
  have hjoint : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun q : ℝ × E =>
        (B.family.metric q.1).inner ((extChartAt I α).symm q.2)
          (e.localFrame b i ((extChartAt I α).symm q.2))
          (e.localFrame b j ((extChartAt I α).symm q.2)))
      (t, chartCurve (I := I) α γ t) := by
    change ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      ((fun q : ℝ × M =>
        (B.family.metric q.1).inner q.2 (e.localFrame b i q.2) (e.localFrame b j q.2)) ∘
        fun q : ℝ × E => (q.1, (extChartAt I α).symm q.2))
      (t, chartCurve (I := I) α γ t)
    exact hjoint0
  have htarget : ∀ᶠ q : ℝ × E in 𝓝 (t, chartCurve (I := I) α γ t),
      q.2 ∈ (extChartAt I α).target :=
    (continuous_snd.tendsto (t, chartCurve (I := I) α γ t)).eventually
      ((isOpen_extChartAt_target (I := I) α).mem_nhds hUt)
  have heq :
      (fun q : ℝ × E =>
        (B.family.metric q.1).inner ((extChartAt I α).symm q.2)
          (e.localFrame b i ((extChartAt I α).symm q.2))
          (e.localFrame b j ((extChartAt I α).symm q.2))) =ᶠ[𝓝 (t, chartCurve (I := I) α γ t)]
      (fun q : ℝ × E => chartGramOnE (I := I) (B.family.metric q.1) α i j q.2) := by
    filter_upwards [htarget] with q hq
    have hxsrc : (extChartAt I α).symm q.2 ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hq
    have hxbase : (extChartAt I α).symm q.2 ∈ e.baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      rw [← DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := I)]
      exact hxsrc
    rw [chartGramOnE_def, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
      e.localFrame_apply_of_mem_baseSet b hxbase,
      e.localFrame_apply_of_mem_baseSet b hxbase]
    simp only [e, b, Bundle.Trivialization.basisAt, Module.Basis.map_apply,
      Trivialization.linearEquivAt_symm_apply, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber,
      Trivialization.symmL_apply _ hxbase]
  have hcd : ContDiffAt ℝ (∞ : WithTop ℕ∞)
      (fun q : ℝ × E => chartGramOnE (I := I) (B.family.metric q.1) α i j q.2)
      (t, chartCurve (I := I) α γ t) := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hjoint.congr_of_eventuallyEq heq.symm
  exact hcd.differentiableAt (by simp)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H] [I.Boundaryless] in
lemma hasDerivWithinAt_diag {F : ℝ × ℝ → ℝ} {F' : (ℝ × ℝ) →L[ℝ] ℝ}
    {a b : ℝ} {J : Set ℝ} {t : ℝ}
    (hF : HasFDerivWithinAt F F' (J ×ˢ J) (t, t))
    (ha : HasDerivWithinAt (fun s => F (s, t)) a J t)
    (hb : HasDerivWithinAt (fun s => F (t, s)) b J t)
    (ht : t ∈ J) (huniq : UniqueDiffWithinAt ℝ J t) :
    HasDerivWithinAt (fun s => F (s, s)) (a + b) J t := by
  have hφ1 : HasDerivWithinAt (fun s : ℝ => (s, t)) ((1, 0) : ℝ × ℝ) J t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t t)).hasDerivWithinAt
  have h1 : HasDerivWithinAt (fun s => F (s, t)) (F' (1, 0)) J t :=
    hF.comp_hasDerivWithinAt (f := fun s : ℝ => (s, t)) (x := t) hφ1 (fun s hs => ⟨hs, ht⟩)
  have he1 : F' (1, 0) = a := (h1.derivWithin huniq).symm.trans (ha.derivWithin huniq)
  have hφ2 : HasDerivWithinAt (fun s : ℝ => (t, s)) ((0, 1) : ℝ × ℝ) J t :=
    ((hasDerivAt_const t t).prodMk (hasDerivAt_id t)).hasDerivWithinAt
  have h2 : HasDerivWithinAt (fun s => F (t, s)) (F' (0, 1)) J t :=
    hF.comp_hasDerivWithinAt (f := fun s : ℝ => (t, s)) (x := t) hφ2 (fun s hs => ⟨ht, hs⟩)
  have he2 : F' (0, 1) = b := (h2.derivWithin huniq).symm.trans (hb.derivWithin huniq)
  have hφ : HasDerivWithinAt (fun s : ℝ => (s, s)) ((1, 1) : ℝ × ℝ) J t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_id t)).hasDerivWithinAt
  have hd : HasDerivWithinAt (fun s => F (s, s)) (F' (1, 1)) J t :=
    hF.comp_hasDerivWithinAt (f := fun s : ℝ => (s, s)) (x := t) hφ (fun s hs => ⟨hs, hs⟩)
  refine hd.congr_deriv ?_
  calc F' (1, 1) = F' ((1, 0) + (0, 1)) := by norm_num
    _ = F' (1, 0) + F' (0, 1) := map_add F' (1, 0) (0, 1)
    _ = a + b := by rw [he1, he2]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem Dt_eq_symmL_chart (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (V : c.Field (I := I)) (x t : ℝ) :
    c.Dt g J V x t =
      (trivializationAt E (TangentSpace I) (c.lift x t)).symmL ℝ (c.lift x t)
        (derivWithin (chartRepAtBase (I := I) (c.lift x t) (fun r => c.lift x r)
            (fun r => V x r)) J t
          + chartChristoffelContraction (I := I) (g t) (c.lift x t)
              (derivWithin (chartCurve (I := I) (c.lift x t) (fun r => c.lift x r)) J t)
              (chartRepAtBase (I := I) (c.lift x t) (fun r => c.lift x r)
                (fun r => V x r) t)
              (chartCurve (I := I) (c.lift x t) (fun r => c.lift x r) t)) := rfl



omit [CompleteSpace E] [TopologicalSpace H] [I.Boundaryless] in
theorem chartCoord_comp_differentiableWithinAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X : F → E} {J : Set F} {t : F}
    (i : Fin (Module.finrank ℝ E)) (hX : DifferentiableWithinAt ℝ X J t) :
    DifferentiableWithinAt ℝ (fun s => chartCoord (E := E) i (X s)) J t := by
  set L : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i) with hLdef
  have hLapply : ∀ v : E, L v = chartCoord (E := E) i v := by
    intro v
    rw [hLdef]
    simp only [LinearMap.coe_toContinuousLinearMap']
    rfl
  have h3 : DifferentiableWithinAt ℝ (fun s => L (X s)) J t :=
    L.differentiableAt.comp_differentiableWithinAt (x := t) (f := X) hX
  exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => hLapply (X s)))
    (hLapply (X t))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
theorem chartRepAtBase_differentiableWithinAt
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} {J : Set ℝ} {t : ℝ}
    (hV : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent ∞
      (fun s : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (γ s) (V s) : TangentBundle I M)) J t) :
    DifferentiableWithinAt ℝ (chartRepAtBase (I := I) (γ t) γ V) J t := by
  classical
  let β : M := γ t
  let e := trivializationAt E (TangentSpace I) β
  have hpair := Bundle.contMDiffWithinAt_totalSpace.mp hV
  have hmem : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hpre : γ ⁻¹' (trivializationAt E (TangentSpace I) (γ t)).baseSet ∈ 𝓝[J] t :=
    hpair.1.continuousWithinAt.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) (γ t)).open_baseSet.mem_nhds hmem)
  have heq : (fun s : ℝ =>
        ((trivializationAt E (TangentSpace I) (γ t))
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ s) (V s) :
            TangentBundle I M)).2)
      =ᶠ[𝓝[J] t] chartRepAtBase (I := I) (γ t) γ V := by
    filter_upwards [hpre] with s hs
    rw [chartRepAtBase_apply]
    simp only [TotalSpace.mk']
    rw [(trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt_apply (R := ℝ)]
    rw [(trivializationAt E (TangentSpace I) (γ t)).coe_linearMapAt_of_mem hs]
  have hcd : ContDiffWithinAt ℝ ∞ (fun s : ℝ =>
        ((trivializationAt E (TangentSpace I) (γ t))
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ s) (V s) :
            TangentBundle I M)).2) J t :=
    contMDiffWithinAt_iff_contDiffWithinAt.mp hpair.2
  have hdiff : DifferentiableWithinAt ℝ (fun s : ℝ =>
        ((trivializationAt E (TangentSpace I) (γ t))
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ s) (V s) :
            TangentBundle I M)).2) J t :=
    hcd.differentiableWithinAt (by norm_num)
  refine hdiff.congr_of_eventuallyEq heq.symm ?_
  rw [chartRepAtBase_apply]
  simp only [TotalSpace.mk']
  rw [(trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt_apply (R := ℝ)]
  rw [(trivializationAt E (TangentSpace I) (γ t)).coe_linearMapAt_of_mem hmem]

omit [SigmaCompactSpace M] in
theorem hasDerivWithinAt_moving_inner {D : RealTimeInterval} {a b s u : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (V W : c.Field (I := I)) (hV : V.SmoothOn (I := I) (Icc s u))
    (hW : W.SmoothOn (I := I) (Icc s u)) (x t : ℝ) (ht : t ∈ Icc s u) :
    HasDerivWithinAt (fun r => (B.family.metric r).inner (c.lift x r) (V x r) (W x r))
      (-2 * B.family.ricciAt t (c.lift x t) (vec2 (V x t) (W x t)) +
        ((B.family.metric t).inner (c.lift x t)
          (c.Dt B.family.metric (Icc s u) V x t) (W x t) +
        (B.family.metric t).inner (c.lift x t) (V x t)
          (c.Dt B.family.metric (Icc s u) W x t)))
      (Icc s u) t := by
  classical
  set J : Set ℝ := Icc s u with hJ
  have htJ : t ∈ J := ht
  have huniq : UniqueDiffWithinAt ℝ J t := (uniqueDiffOn_Icc hsu) t htJ
  have hreg : t ∈ D.regular := B.regular (hwindow ht)
  have hsub : J ⊆ D.carrier := fun r hr => D.regular_subset (B.regular (hwindow hr))
  set γ : ℝ → M := fun r => c.lift x r with hγ
  set α : M := c.lift x t with hα
  set Vx : (r : ℝ) → TangentSpace I (γ r) := fun r => V x r with hVx
  set Wx : (r : ℝ) → TangentSpace I (γ r) := fun r => W x r with hWx
  set e := trivializationAt E (TangentSpace I) α with he
  set U : ℝ → E := chartCurve (I := I) α γ with hU
  set Vrep : ℝ → E := chartRepAtBase (I := I) α γ Vx with hVrep
  set Wrep : ℝ → E := chartRepAtBase (I := I) α γ Wx with hWrep
  set Q : ℝ × ℝ → ℝ := fun p => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) (B.family.metric p.1) α i j (U p.2) *
        chartCoord (E := E) i (Vrep p.2) * chartCoord (E := E) j (Wrep p.2) with hQ
  have hbase : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hγsm : ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ γ J t :=
    CurveMap.time_slice_contMDiffWithinAt (I := I) c J hc x t htJ
  have hVsm : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ r) (Vx r) :
        TangentBundle I M)) J t := by
    have h0 : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I.tangent ∞
        (fun p : ℝ × ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (c.lift p.1 p.2) (V p.1 p.2) : TangentBundle I M)) (univ ×ˢ J) (x, t) :=
      (show (V.SmoothOn (I := I) J) from hV) (x, t) ⟨mem_univ x, htJ⟩
    refine h0.comp t ?_ ?_
    · rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
    · intro r hr; exact ⟨mem_univ x, hr⟩
  have hWsm : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ r) (Wx r) :
        TangentBundle I M)) J t := by
    have h0 : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I.tangent ∞
        (fun p : ℝ × ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (c.lift p.1 p.2) (W p.1 p.2) : TangentBundle I M)) (univ ×ˢ J) (x, t) :=
      (show (W.SmoothOn (I := I) J) from hW) (x, t) ⟨mem_univ x, htJ⟩
    refine h0.comp t ?_ ?_
    · rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
    · intro r hr; exact ⟨mem_univ x, hr⟩
  have hUdiff : DifferentiableWithinAt ℝ U J t := by
    have hsm : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ U J t := by
      have hφ : ContMDiffWithinAt I 𝓘(ℝ, E) ∞ (extChartAt I α) univ (γ t) :=
        (contMDiffAt_extChartAt (I := I) (x := α) (n := (∞ : WithTop ℕ∞))).contMDiffWithinAt
      exact hφ.comp t hγsm (fun r _ => mem_univ (γ r))
    exact (contMDiffWithinAt_iff_contDiffWithinAt.mp hsm).differentiableWithinAt (by norm_num)
  have hVdiff : DifferentiableWithinAt ℝ Vrep J t :=
    chartRepAtBase_differentiableWithinAt (I := I) (γ := γ) (V := Vx) (J := J) (t := t) hVsm
  have hWdiff : DifferentiableWithinAt ℝ Wrep J t :=
    chartRepAtBase_differentiableWithinAt (I := I) (γ := γ) (V := Wx) (J := J) (t := t) hWsm
  have hsrc : α ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H α
  have hUt : U t ∈ (extChartAt I α).target := by
    simpa only [hU, chartCurve_def] using (extChartAt I α).map_source hsrc
  have hmem : U t ∈ interior (extChartAt I α).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α hUt
  have hVsymm : e.symmL ℝ (γ t) (Vrep t) = Vx t := by
    have h := e.symmL_continuousLinearMapAt (R := ℝ) hbase (Vx t)
    simpa only [hVrep, chartRepAtBase_apply] using h
  have hWsymm : e.symmL ℝ (γ t) (Wrep t) = Wx t := by
    have h := e.symmL_continuousLinearMapAt (R := ℝ) hbase (Wx t)
    simpa only [hWrep, chartRepAtBase_apply] using h
  have hUhas : HasDerivWithinAt U (derivWithin U J t) J t := hUdiff.hasDerivWithinAt
  have hVhas : HasDerivWithinAt Vrep (derivWithin Vrep J t) J t := hVdiff.hasDerivWithinAt
  have hWhas : HasDerivWithinAt Wrep (derivWithin Wrep J t) J t := hWdiff.hasDerivWithinAt
  have h2nd0 := DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartGramAlongCurve_hasDerivWithinAt_covariant (I := I)
    (B.family.metric t) α γ Vrep Wrep
    (uPrime := derivWithin U J) (Vprime := derivWithin Vrep J) (Wprime := derivWithin Wrep J)
    hUhas hmem hVhas hWhas
  set A : E := derivWithin Vrep J t + chartChristoffelContraction (I := I) (B.family.metric t)
    α (derivWithin U J t) (Vrep t) (U t) with hA
  set Bv : E := derivWithin Wrep J t + chartChristoffelContraction (I := I) (B.family.metric t)
    α (derivWithin U J t) (Wrep t) (U t) with hBv
  have hsum1 : (∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) (B.family.metric t) α l j (U t) *
          chartCoord (E := E) l A * chartCoord (E := E) j (Wrep t)) =
      (B.family.metric t).inner (γ t) (e.symmL ℝ (γ t) A) (e.symmL ℝ (γ t) (Wrep t)) :=
    chartGramOnE_sum_eq_inner (I := I) (B.family.metric t) α γ hbase A (Wrep t)
  have hsum2 : (∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) (B.family.metric t) α i l (U t) *
          chartCoord (E := E) i (Vrep t) * chartCoord (E := E) l Bv) =
      (B.family.metric t).inner (γ t) (e.symmL ℝ (γ t) (Vrep t)) (e.symmL ℝ (γ t) Bv) :=
    chartGramOnE_sum_eq_inner (I := I) (B.family.metric t) α γ hbase (Vrep t) Bv
  have hbridgeV : e.symmL ℝ (γ t) A = c.Dt B.family.metric J V x t :=
    Dt_eq_symmL_chart (c := c) (g := B.family.metric) (J := J) (V := V) (x := x) (t := t)
  have hbridgeW : e.symmL ℝ (γ t) Bv = c.Dt B.family.metric J W x t :=
    Dt_eq_symmL_chart (c := c) (g := B.family.metric) (J := J) (V := W) (x := x) (t := t)
  have h2nd : HasDerivWithinAt (fun s : ℝ => Q (t, s))
      ((B.family.metric t).inner (c.lift x t) (c.Dt B.family.metric J V x t) (W x t) +
        (B.family.metric t).inner (c.lift x t) (V x t) (c.Dt B.family.metric J W x t)) J t := by
    have hfun : (fun s : ℝ => chartGramAlongCurve (I := I) (B.family.metric t) α γ Vrep Wrep s) =
        (fun s : ℝ => Q (t, s)) := by
      funext s
      simp only [hQ, chartGramAlongCurve_def, hU]
    rw [hfun] at h2nd0
    refine h2nd0.congr_deriv ?_
    rw [hsum1, hsum2, hWsymm, hVsymm]
    rw [← hbridgeV, ← hbridgeW]
  have h1st : HasDerivWithinAt (fun r : ℝ => Q (r, t))
      (-2 * B.family.ricciAt t α (vec2 (Vx t) (Wx t))) J t := by
    have hm : HasDerivWithinAt (fun s : ℝ => (B.family.metric s).inner α (Vx t) (Wx t))
        (-2 * B.family.ricciAt t α (vec2 (Vx t) (Wx t))) D.carrier t :=
      metric_derivWithin_eq_neg_two_ricci (I := I) (D := D)
        (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩) B.equation
        (⟨t, hreg⟩ : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
        α (Vx t) (Wx t)
    refine (hm.mono hsub).congr_of_eventuallyEq ?_ ?_
    · filter_upwards with r
      simp only [hQ]
      rw [chartGramOnE_sum_eq_inner (I := I) (B.family.metric r) α γ (t := t) hbase (Vrep t) (Wrep t),
        hVsymm, hWsymm]
    · simp only [hQ]
      rw [chartGramOnE_sum_eq_inner (I := I) (B.family.metric t) α γ (t := t) hbase (Vrep t) (Wrep t),
        hVsymm, hWsymm]
  have hchart2 : ∀ i j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun q : ℝ × E => chartGramOnE (I := I) (B.family.metric q.1) α i j q.2) (t, U t) :=
    fun i j => chartGramOnE_metricFamily_differentiableAt (I := I) B α γ hreg rfl i j
  have hUpair : DifferentiableWithinAt ℝ (fun p : ℝ × ℝ => U p.2) (J ×ˢ J) (t, t) :=
    DifferentiableWithinAt.comp (x := (t, t)) (g := U) (f := fun p : ℝ × ℝ => p.2)
      (s := J ×ˢ J) (t := J) hUdiff (differentiableWithinAt_snd (p := (t, t)))
      (fun y hy => hy.2)
  have hVpair : DifferentiableWithinAt ℝ (fun p : ℝ × ℝ => Vrep p.2) (J ×ˢ J) (t, t) :=
    DifferentiableWithinAt.comp (x := (t, t)) (g := Vrep) (f := fun p : ℝ × ℝ => p.2)
      (s := J ×ˢ J) (t := J) hVdiff (differentiableWithinAt_snd (p := (t, t)))
      (fun y hy => hy.2)
  have hWpair : DifferentiableWithinAt ℝ (fun p : ℝ × ℝ => Wrep p.2) (J ×ˢ J) (t, t) :=
    DifferentiableWithinAt.comp (x := (t, t)) (g := Wrep) (f := fun p : ℝ × ℝ => p.2)
      (s := J ×ˢ J) (t := J) hWdiff (differentiableWithinAt_snd (p := (t, t)))
      (fun y hy => hy.2)
  have hinner2 : DifferentiableWithinAt ℝ (fun p : ℝ × ℝ => (p.1, U p.2)) (J ×ˢ J) (t, t) :=
    (differentiableWithinAt_fst (p := (t, t))).prodMk hUpair
  have hQdiff : DifferentiableWithinAt ℝ Q (J ×ˢ J) (t, t) := by
    simp only [hQ]
    refine DifferentiableWithinAt.fun_sum
      (fun i _ => DifferentiableWithinAt.fun_sum (fun j _ => ?_))
    have hG : DifferentiableWithinAt ℝ (fun p : ℝ × ℝ =>
        chartGramOnE (I := I) (B.family.metric p.1) α i j (U p.2)) (J ×ˢ J) (t, t) :=
      (HasFDerivWithinAt.comp (x := (t, t)) (f := fun p : ℝ × ℝ => (p.1, U p.2))
        (s := J ×ˢ J) (t := univ)
        (hchart2 i j).hasFDerivAt.hasFDerivWithinAt hinner2.hasFDerivWithinAt
        (fun y _ => mem_univ _)).differentiableWithinAt
    exact (hG.mul (chartCoord_comp_differentiableWithinAt i hVpair)).mul
      (chartCoord_comp_differentiableWithinAt j hWpair)
  have hdiag := hasDerivWithinAt_diag (F := Q) (F' := fderivWithin ℝ Q (J ×ˢ J) (t, t))
    hQdiff.hasFDerivWithinAt h1st h2nd htJ huniq
  have hEq : (fun r : ℝ => (B.family.metric r).inner (γ r) (Vx r) (Wx r)) =ᶠ[𝓝[J] t]
      (fun r : ℝ => Q (r, r)) := by
    have hcont : ContinuousWithinAt γ J t := hγsm.continuousWithinAt
    filter_upwards [hcont.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)] with r hr
    simp only [hQ]
    have hVs : e.symmL ℝ (γ r) (Vrep r) = Vx r := by
      have h := e.symmL_continuousLinearMapAt (R := ℝ) hr (Vx r)
      simpa only [hVrep, chartRepAtBase_apply] using h
    have hWs : e.symmL ℝ (γ r) (Wrep r) = Wx r := by
      have h := e.symmL_continuousLinearMapAt (R := ℝ) hr (Wx r)
      simpa only [hWrep, chartRepAtBase_apply] using h
    have hsrcr : γ r ∈ (extChartAt I α).source := by
      rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := I)]
      rwa [TangentBundle.trivializationAt_baseSet] at hr
    rw [← hVs, ← hWs,
      inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) (B.family.metric r) α (Vrep r) (Wrep r)]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [chartGramOnE_def,
      show (extChartAt I α).symm (U r) = γ r from by
        rw [hU, chartCurve_def]
        exact (extChartAt I α).left_inv hsrcr]
  have hcons := hdiag.congr_of_eventuallyEq hEq (hEq.eq_of_nhdsWithin htJ)
  simpa only [hJ, hα, hγ, hVx, hWx] using hcons

omit [SigmaCompactSpace M] in
theorem moving_inner_derivative {D : RealTimeInterval} {a b s u : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (V W : c.Field (I := I)) (hV : V.SmoothOn (I := I) (Icc s u))
    (hW : W.SmoothOn (I := I) (Icc s u)) (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (fun r => (B.family.metric r).inner (c.lift x r) (V x r) (W x r))
      (Icc s u) t =
      (B.family.metric t).inner (c.lift x t) (c.Dt B.family.metric (Icc s u) V x t) (W x t) +
      (B.family.metric t).inner (c.lift x t) (V x t) (c.Dt B.family.metric (Icc s u) W x t) -
      2 * B.family.ricciAt t (c.lift x t) (vec2 (V x t) (W x t)) := by
  have h := (hasDerivWithinAt_moving_inner B hsu hwindow c hc V W hV hW x t ht).derivWithin
    ((uniqueDiffOn_Icc hsu) t ht)
  rw [h]
  ring

omit [SigmaCompactSpace M] hBoundary in
theorem hasDerivWithinAt_chartChristoffel_metricFamily_fixed
    {D : RealTimeInterval} {a b : ℝ} (B : RicciBackground (I := I) (M := M) D a b)
    (β : M) (i j k : Fin (Module.finrank ℝ E)) {J : Set ℝ} {t : ℝ}
    (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (ht : t ∈ J)
    {y : E} (hy : y ∈ interior (extChartAt I β).target) :
    HasDerivWithinAt (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k y)
      (derivWithin (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k y) J t) J t := by
  have hcd : ContDiffOn ℝ ∞
      (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
      (J ×ˢ interior (extChartAt I β).target) :=
    MetricFamilySmoothOn.chartChristoffelOnE_contDiffOn (I := I) B.smooth hJreg hJ β i j k
  have hmem : (t, y) ∈ J ×ˢ interior (extChartAt I β).target := ⟨ht, hy⟩
  have hdiff : DifferentiableWithinAt ℝ
      (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
      (J ×ˢ interior (extChartAt I β).target) (t, y) :=
    (hcd.differentiableOn (by simp)) (t, y) hmem
  have hG := hdiff.hasFDerivWithinAt
  have hcurve : HasDerivWithinAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : E)) J t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y)).hasDerivWithinAt
  have hcomp := hG.comp_hasDerivWithinAt t hcurve (fun r hr => (⟨hr, hy⟩ :
    (r, y) ∈ J ×ˢ interior (extChartAt I β).target))
  have huniq : UniqueDiffWithinAt ℝ J t := hJ t ht
  have hcomp' : HasDerivWithinAt
      (fun r : ℝ => chartChristoffel (I := I) (B.family.metric r) β i j k y)
      (fderivWithin ℝ
        (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
        (J ×ˢ interior (extChartAt I β).target) (t, y) ((1 : ℝ), (0 : E))) J t := by
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using hcomp
  rw [hcomp'.derivWithin huniq]
  exact hcomp'


omit [SigmaCompactSpace M] hBoundary in
theorem hasDerivWithinAt_chartChristoffel_metricFamily_comp
    {D : RealTimeInterval} {a b : ℝ} (B : RicciBackground (I := I) (M := M) D a b)
    (β : M) (i j k : Fin (Module.finrank ℝ E)) {J : Set ℝ} {t : ℝ}
    (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (ht : t ∈ J)
    (R : ℝ → E) (R' : E) (hR : HasDerivWithinAt R R' J t)
    (hRint : R t ∈ interior (extChartAt I β).target)
    (hRmem : ∀ r ∈ J, R r ∈ interior (extChartAt I β).target) :
    HasDerivWithinAt (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k (R r))
      (derivWithin (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k (R t)) J t
        + fderiv ℝ (chartChristoffel (I := I) (B.family.metric t) β i j k) (R t) R') J t := by
  have hcd : ContDiffOn ℝ ∞
      (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
      (J ×ˢ interior (extChartAt I β).target) :=
    MetricFamilySmoothOn.chartChristoffelOnE_contDiffOn (I := I) B.smooth hJreg hJ β i j k
  have hmem : (t, R t) ∈ J ×ˢ interior (extChartAt I β).target := ⟨ht, hRint⟩
  have hdiff : DifferentiableWithinAt ℝ
      (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
      (J ×ˢ interior (extChartAt I β).target) (t, R t) :=
    (hcd.differentiableOn (by simp)) (t, R t) hmem
  have hG := hdiff.hasFDerivWithinAt
  have huniq : UniqueDiffWithinAt ℝ J t := hJ t ht
  have hcurve : HasDerivWithinAt (fun r : ℝ => (r, R r)) ((1 : ℝ), R') J t :=
    ((hasDerivAt_id t).hasDerivWithinAt).prodMk hR
  have hcomp := hG.comp_hasDerivWithinAt t hcurve (fun r hr => (⟨hr, hRmem r hr⟩ :
    (r, R r) ∈ J ×ˢ interior (extChartAt I β).target))
  have hcomp' : HasDerivWithinAt (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k (R r))
      (fderivWithin ℝ
        (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
        (J ×ˢ interior (extChartAt I β).target) (t, R t) ((1 : ℝ), R')) J t := by
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using hcomp
  have hf1 : HasDerivWithinAt (fun r : ℝ => chartChristoffel (I := I) (B.family.metric r) β i j k (R t))
      (fderivWithin ℝ
        (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
        (J ×ˢ interior (extChartAt I β).target) (t, R t) ((1 : ℝ), (0 : E))) J t := by
    have hc2 : HasDerivWithinAt (fun r : ℝ => (r, R t)) ((1 : ℝ), (0 : E)) J t :=
      ((hasDerivAt_id t).hasDerivWithinAt).prodMk
        (hasDerivWithinAt_const (c := R t) (s := J) (x := t))
    have h := hG.comp_hasDerivWithinAt t hc2 (fun r hr => (⟨hr, hRint⟩ :
      (r, R t) ∈ J ×ˢ interior (extChartAt I β).target))
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using h
  have hknown1 : HasDerivWithinAt
      (fun r : ℝ => chartChristoffel (I := I) (B.family.metric r) β i j k (R t))
      (derivWithin (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k (R t)) J t) J t :=
    hasDerivWithinAt_chartChristoffel_metricFamily_fixed B β i j k hJreg hJ ht hRint
  have hF1 : fderivWithin ℝ
        (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
        (J ×ˢ interior (extChartAt I β).target) (t, R t) ((1 : ℝ), (0 : E))
      = derivWithin (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k (R t)) J t :=
    (hf1.derivWithin huniq).symm.trans (hknown1.derivWithin huniq)
  have hslice : HasFDerivAt (fun y : E => chartChristoffel (I := I) (B.family.metric t) β i j k y)
      (fderiv ℝ (fun y : E => chartChristoffel (I := I) (B.family.metric t) β i j k y) (R t)) (R t) := by
    have hy_target : R t ∈ (extChartAt I β).target := interior_subset hRint
    have hcd2 : ContDiffOn ℝ ∞ (chartChristoffel (I := I) (B.family.metric t) β i j k)
        (interior (extChartAt I β).target) :=
      chartChristoffel_contDiffOn_interior (I := I) (B.family.metric t) β i j k
    exact ((hcd2.contDiffAt (isOpen_interior.mem_nhds hRint)).differentiableAt (by simp)).hasFDerivAt
  have hK : {s : ℝ | R t + s • R' ∈ interior (extChartAt I β).target} ∈ 𝓝 (0 : ℝ) := by
    have hcont : ContinuousAt (fun s : ℝ => R t + s • R') 0 := by fun_prop
    have h0 : R t + (0 : ℝ) • R' = R t := by simp
    rw [show (0 : ℝ) = 0 from rfl]
    refine hcont.eventually (isOpen_interior.mem_nhds ?_)
    simpa using hRint
  have hc3 : HasDerivWithinAt (fun s : ℝ => R t + s • R') R' {s : ℝ | R t + s • R' ∈ interior (extChartAt I β).target} 0 := by
    have h0 : (fun s : ℝ => R t + s • R') 0 = R t := by simp
    have hder : HasDerivAt (fun s : ℝ => R t + s • R') R' 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const R').const_add (R t)
    exact hder.hasDerivWithinAt
  have hcurve2 : HasDerivWithinAt (fun s : ℝ => (t, R t + s • R')) ((0 : ℝ), R')
      {s : ℝ | R t + s • R' ∈ interior (extChartAt I β).target} 0 :=
    (hasDerivWithinAt_const (c := t) (s := {s : ℝ | R t + s • R' ∈ interior (extChartAt I β).target})
      (x := (0 : ℝ))).prodMk hc3
  have h0c : (fun s : ℝ => (t, R t + s • R')) 0 = (t, R t) := by simp
  have hj2 := (h0c.symm ▸ hG).comp_hasDerivWithinAt (x := (0 : ℝ)) hcurve2
    (fun s hs => show (t, R t + s • R') ∈ J ×ˢ interior (extChartAt I β).target from ⟨ht, hs⟩)
  have hf2 : HasDerivWithinAt (fun s : ℝ => chartChristoffel (I := I) (B.family.metric t) β i j k (R t + s • R'))
      ((fderivWithin ℝ
        (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
        (J ×ˢ interior (extChartAt I β).target) (t, R t)) ((0 : ℝ), R'))
      {s : ℝ | R t + s • R' ∈ interior (extChartAt I β).target} 0 := by
    simpa only [Function.comp_def, Prod.fst, Prod.snd, zero_smul, add_zero] using hj2
  have hc30 : (fun s : ℝ => R t + s • R') 0 = R t := by simp
  have hknown2 : HasDerivWithinAt (fun s : ℝ => chartChristoffel (I := I) (B.family.metric t) β i j k (R t + s • R'))
      (fderiv ℝ (fun y : E => chartChristoffel (I := I) (B.family.metric t) β i j k y) (R t) R')
      {s : ℝ | R t + s • R' ∈ interior (extChartAt I β).target} 0 := by
    have h := (hc30.symm ▸ hslice).comp_hasDerivWithinAt (x := (0 : ℝ)) hc3
    simpa only [Function.comp_def, zero_smul, add_zero] using h
  have hKopen : IsOpen {s : ℝ | R t + s • R' ∈ interior (extChartAt I β).target} :=
    isOpen_interior.preimage (by fun_prop)
  have hKmem : (0 : ℝ) ∈ {s : ℝ | R t + s • R' ∈ interior (extChartAt I β).target} := by
    simpa using hRint
  have huniqK : UniqueDiffWithinAt ℝ {s : ℝ | R t + s • R' ∈ interior (extChartAt I β).target} 0 :=
    hKopen.uniqueDiffWithinAt hKmem
  have hF2 : (fderivWithin ℝ
        (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
        (J ×ˢ interior (extChartAt I β).target) (t, R t)) ((0 : ℝ), R')
      = fderiv ℝ (fun y : E => chartChristoffel (I := I) (B.family.metric t) β i j k y) (R t) R' :=
    (hf2.derivWithin huniqK).symm.trans (hknown2.derivWithin huniqK)
  have hval : (fderivWithin ℝ
        (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
        (J ×ˢ interior (extChartAt I β).target) (t, R t)) ((1 : ℝ), R')
      = derivWithin (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k (R t)) J t
        + fderiv ℝ (fun y : E => chartChristoffel (I := I) (B.family.metric t) β i j k y) (R t) R' := by
    have hsplit : ((1 : ℝ), R') = ((1 : ℝ), (0 : E)) + ((0 : ℝ), R') := by simp
    rw [hsplit, map_add, hF1, hF2]
  rw [hval] at hcomp'
  exact hcomp'


omit [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H] hBoundary in
theorem hasDerivAt_derivWithin_slice
    (F : ℝ × ℝ → E) (x t : ℝ) {J : Set ℝ}
    (huniqJ : UniqueDiffOn ℝ J) (htJ : t ∈ J) (hcl : t ∈ closure (interior J))
    (hF : ∀ᶠ z in 𝓝[univ ×ˢ J] (x, t), ContDiffWithinAt ℝ 2 F (univ ×ˢ J) z) :
    HasDerivAt (fun u : ℝ => derivWithin (fun v : ℝ => F (u, v)) J t)
      (derivWithin (fun v : ℝ => deriv (fun u : ℝ => F (u, v)) x) J t) x := by
  set S : Set (ℝ × ℝ) := univ ×ˢ J with hS
  have hSuniq : UniqueDiffOn ℝ S := by
    rw [hS]; exact UniqueDiffOn.prod uniqueDiffOn_univ huniqJ
  have hxS : (x, t) ∈ S := by rw [hS]; exact ⟨mem_univ x, htJ⟩
  have hclS : (x, t) ∈ closure (interior S) := by
    rw [hS, interior_prod_eq, closure_prod_eq]
    exact ⟨by simp, hcl⟩
  have hmem : ∀ u v : ℝ, v ∈ J → (u, v) ∈ S := fun u v hv => by
    rw [hS]; exact ⟨mem_univ u, hv⟩
  have hFt : ContDiffWithinAt ℝ 2 F S (x, t) := by
    rw [hS] at hF ⊢
    exact hF.self_of_nhdsWithin hxS
  have hsymm : IsSymmSndFDerivWithinAt ℝ F S (x, t) :=
    ContDiffWithinAt.isSymmSndFDerivWithinAt hFt
      (by rw [minSmoothness_of_isRCLikeNormedField]) hSuniq hclS hxS
  have hDd : DifferentiableWithinAt ℝ (fderivWithin ℝ F S) S (x, t) :=
    (hFt.fderivWithin_right hSuniq (m := 1) (by norm_num) hxS).differentiableWithinAt
      (by norm_num)
  set D : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] E) :=
    fderivWithin ℝ (fderivWithin ℝ F S) S (x, t) with hD
  have hsym : D (1, 0) (0, 1) = D (0, 1) (1, 0) := by
    rw [hD]; exact hsymm (1, 0) (0, 1)
  set ev₂ : ((ℝ × ℝ) →L[ℝ] E) →L[ℝ] E :=
    ContinuousLinearMap.apply ℝ E ((0 : ℝ), (1 : ℝ)) with hev₂
  have hev₂_apply : ∀ L : (ℝ × ℝ) →L[ℝ] E, ev₂ L = L (0, 1) := by
    intro L; simp [hev₂]
  have hQ : HasFDerivWithinAt (fun z : ℝ × ℝ => fderivWithin ℝ F S z (0, 1))
      (ev₂.comp D) S (x, t) :=
    HasFDerivAt.comp_hasFDerivWithinAt (x := (x, t))
      (ContinuousLinearMap.hasFDerivAt ev₂) hDd.hasFDerivWithinAt
  have hι : HasFDerivWithinAt (fun u : ℝ => (u, t)) (ContinuousLinearMap.inl ℝ ℝ ℝ) univ x :=
    (hasFDerivAt_prodMk_left x t).hasFDerivWithinAt
  have hmap : MapsTo (fun u : ℝ => (u, t)) univ S := fun u _ => hmem u t htJ
  have hcomp := HasFDerivWithinAt.comp (x := x) hQ hι hmap
  have h1 : fderivWithin ℝ (fun u : ℝ => fderivWithin ℝ F S (u, t) (0, 1)) univ x
      = (ev₂.comp D).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) :=
    hcomp.fderivWithin uniqueDiffWithinAt_univ
  have hQderiv : HasDerivAt (fun u : ℝ => fderivWithin ℝ F S (u, t) (0, 1)) (D (1, 0) (0, 1)) x := by
    have h := hcomp.hasDerivWithinAt
    have hval : ((ev₂.comp D).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) (1 : ℝ) = D (1, 0) (0, 1) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
      exact hev₂_apply (D (1, 0))
    rw [hval] at h
    exact h.hasDerivAt Filter.univ_mem
  have htendL : Filter.Tendsto (fun u : ℝ => ((u, t) : ℝ × ℝ)) (𝓝 x)
      (𝓝[univ ×ˢ J] ((x, t) : ℝ × ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · exact (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t).continuousAt.tendsto
    · filter_upwards with u
      exact ⟨mem_univ u, htJ⟩
  have hQid : ∀ᶠ u in 𝓝 x, fderivWithin ℝ F S (u, t) (0, 1)
      = fderivWithin ℝ (fun v => F (u, v)) J t 1 := by
    filter_upwards [htendL.eventually hF] with u hcu
    have hdu : DifferentiableWithinAt ℝ F (univ ×ˢ J) (u, t) :=
      hcu.differentiableWithinAt (by norm_num)
    have hd : DifferentiableWithinAt ℝ F S (u, t) := by rwa [hS]
    have hι2 : HasFDerivWithinAt (fun v : ℝ => (u, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) J t :=
      (hasFDerivAt_prodMk_right u t).hasFDerivWithinAt
    have hmap2 : MapsTo (fun v : ℝ => (u, v)) J S := fun v hv => by
      rw [hS]; exact ⟨mem_univ u, hv⟩
    have hcomp2 := HasFDerivWithinAt.comp (x := t) hd.hasFDerivWithinAt hι2 hmap2
    have h1' : fderivWithin ℝ (fun v : ℝ => F (u, v)) J t
        = (fderivWithin ℝ F S (u, t)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) :=
      hcomp2.fderivWithin (huniqJ t htJ)
    have h2' := congrArg (fun L : ℝ →L[ℝ] E => L 1) h1'
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at h2'
    exact h2'.symm
  have hQid2 : (fun u : ℝ => derivWithin (fun v : ℝ => F (u, v)) J t)
      =ᶠ[𝓝 x] (fun u : ℝ => fderivWithin ℝ F S (u, t) (0, 1)) := by
    filter_upwards [hQid] with u hu
    rw [derivWithin, hu]
  have hmain := hQderiv.congr_of_eventuallyEq (hQid2)
  have hcl := DifferentialGeometry.Geometry.Riemannian.Variation.mixed_partialFderivWithin_comm
    F x t huniqJ htJ hcl (by rw [← hS]; exact hF)
  have hderiv_eq : deriv (fun u : ℝ => fderivWithin ℝ (fun v : ℝ => F (u, v)) J t 1) x
      = D (1, 0) (0, 1) := (Filter.EventuallyEq.deriv_eq hQid).symm.trans hQderiv.deriv
  have hval2 : derivWithin (fun v : ℝ => deriv (fun u : ℝ => F (u, v)) x) J t = D (1, 0) (0, 1) :=
    hcl.trans hderiv_eq
  rwa [hval2]


omit [CompleteSpace E] [TopologicalSpace H] hBoundary in
theorem hasDerivWithinAt_chartCoord_comp {P : ℝ → E} {P' : E} {J : Set ℝ} {t : ℝ}
    (hP : HasDerivWithinAt P P' J t) (i : Fin (Module.finrank ℝ E)) :
    HasDerivWithinAt (fun r => chartCoord (E := E) i (P r)) (chartCoord (E := E) i P') J t := by
  set L : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i) with hLdef
  have hLapply : ∀ v : E, L v = chartCoord (E := E) i v := by
    intro v
    rw [hLdef]
    simp only [LinearMap.coe_toContinuousLinearMap']
    rfl
  have h := L.hasFDerivAt.comp_hasDerivWithinAt t hP
  simpa only [Function.comp_def, hLapply] using h

omit [SigmaCompactSpace M] hBoundary in
theorem hasDerivWithinAt_chartChristoffelContraction_metricFamily
    {D : RealTimeInterval} {a b : ℝ} (B : RicciBackground (I := I) (M := M) D a b)
    (β : M) {J : Set ℝ} {t : ℝ} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (ht : t ∈ J)
    (P Q R : ℝ → E) (P' Q' R' : E)
    (hP : HasDerivWithinAt P P' J t) (hQ : HasDerivWithinAt Q Q' J t)
    (hR : HasDerivWithinAt R R' J t)
    (hRint : R t ∈ interior (extChartAt I β).target)
    (hRmem : ∀ r ∈ J, R r ∈ interior (extChartAt I β).target) :
    HasDerivWithinAt
      (fun r => chartChristoffelContraction (I := I) (B.family.metric r) β (P r) (Q r) (R r))
      (∑ k : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ((derivWithin (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k (R t)) J t
              + fderiv ℝ (chartChristoffel (I := I) (B.family.metric t) β i j k) (R t) R')
              * chartCoord (E := E) i (P t) * chartCoord (E := E) j (Q t)
            + chartChristoffel (I := I) (B.family.metric t) β i j k (R t)
              * chartCoord (E := E) i P' * chartCoord (E := E) j (Q t)
            + chartChristoffel (I := I) (B.family.metric t) β i j k (R t)
              * chartCoord (E := E) i (P t) * chartCoord (E := E) j Q')) •
          DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k) J t := by
  classical
  have hfun : (fun r => chartChristoffelContraction (I := I) (B.family.metric r) β (P r) (Q r) (R r))
      = fun r => ∑ k : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) (B.family.metric r) β i j k (R r)
              * chartCoord (E := E) i (P r) * chartCoord (E := E) j (Q r)) •
            DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k := by
    funext r
    rw [chartChristoffelContraction_def]
  rw [hfun]
  refine HasDerivWithinAt.fun_sum (u := Finset.univ) (fun k _ => ?_)
  refine HasDerivWithinAt.smul_const ?_ _
  refine HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => ?_)
  refine HasDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ => ?_)
  have hG := hasDerivWithinAt_chartChristoffel_metricFamily_comp B β i j k hJreg hJ ht R R'
    hR hRint hRmem
  have hPi := hasDerivWithinAt_chartCoord_comp hP i
  have hQj := hasDerivWithinAt_chartCoord_comp hQ j
  have hprod := (hG.mul hPi).mul hQj
  refine hprod.congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private lemma sum_rotate {ι N : Type*} [Fintype ι] [AddCommMonoid N] (F : ι → ι → ι → N) :
    (∑ i, ∑ j, ∑ k, F i j k) = ∑ k, ∑ i, ∑ j, F i j k := by
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  exact Finset.sum_comm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private lemma sum_smul_univ {ι : Type*} [Fintype ι] (f : ι → ℝ) (b : E) :
    (∑ i, f i • b) = (∑ i, f i) • b :=
  (Finset.sum_smul (s := Finset.univ) (f := f) (x := b)).symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private lemma sum_sum_smul_univ {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) (b : E) :
    (∑ i, ∑ j, f i j • b) = (∑ i, ∑ j, f i j) • b := by
  simp only [Finset.sum_smul]

omit [SigmaCompactSpace M] in
private theorem trivToE_connection_apply_chart
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (β : M) (r : ℝ) (A W : TangentSpace I β) :
    trivToE (I := I) β β (B.family.connection r (tangentConstAt (I := I) β W) β A) =
      ∑ k, (∑ i, ∑ j,
        chartChristoffel (I := I) (B.family.metric r) β i j k (extChartAt I β β)
        * chartCoord (E := E) i (trivToE (I := I) β β A)
        * chartCoord (E := E) j (trivToE (I := I) β β W))
      • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k := by
  classical
  set σ : (p : M) → TangentSpace I p := tangentConstAt (I := I) β W with hσ
  have hbase : β ∈ (trivializationAt E (TangentSpace I) β).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) β
  have hgood : β ∈ chartLeviCivitaGoodSet (I := I) β := by
    rw [mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) β β]
    exact mem_extChartAt_source (I := I) β
  have hmd : MDiffAt (T% σ) β := by
    rw [hσ]
    exact mdifferentiableAt_tangentConstAt_self (I := I) β W
  have hrep : chartESectionRepr (I := I) β σ β = (trivToE (I := I) β β) W := by
    rw [chartE_section_repr_eq_trivToE, hσ, tangentConstAt_self]
  have hconst : ∀ y ∈ (extChartAt I β).target,
      chartESectionRepr (I := I) β σ ((extChartAt I β).symm y) = (trivToE (I := I) β β) W := by
    intro y hy
    rw [chartE_section_repr_eq_trivToE, hσ, tangentConstAt_apply]
    exact TensorLieDeriv.tangentFieldModelInChart_tangentConstInChart_apply_of_mem
      (I := I) β hy ((trivToE (I := I) β β) W)
  have hfderiv : fderiv ℝ (chartESectionRepr (I := I) β σ ∘ ((extChartAt I β).symm : E → M))
      (((extChartAt I β) : M → E) β) ((trivToE (I := I) β β) A) = 0 := by
    have hy₀ : ((extChartAt I β) : M → E) β ∈ (extChartAt I β).target :=
      (extChartAt I β).map_source (mem_extChartAt_source (I := I) β)
    have hev : (chartESectionRepr (I := I) β σ ∘ ((extChartAt I β).symm : E → M))
        =ᶠ[𝓝 (((extChartAt I β) : M → E) β)] Function.const E ((trivToE (I := I) β β) W) := by
      filter_upwards [(isOpen_extChartAt_target (I := I) β).mem_nhds hy₀] with y hy
      exact hconst y hy
    rw [Filter.EventuallyEq.fderiv_eq hev, fderiv_const]
    simp
  have hconn : B.family.connection r = LeviCivita (I := I) (B.family.metric r) :=
    (LeviCivita_eq_leviCivitaConnectionOfMetric (I := I) (B.family.metric r)).symm
  rw [hconn, LeviCivita_chart_apply (I := I) (B.family.metric r) β hgood hmd A,
    chartLeviCivita_apply (I := I) (B.family.metric r) β σ hgood A,
    trivToE_trivFromE (I := I) β hbase]
  rw [hfderiv, zero_add, hrep,
    christoffelCorrection_basepoint_apply (I := I) (B.family.metric r) β ((trivToE (I := I) β β) W) A]
  calc (∑ i, ∑ j, ∑ k,
        (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
              ((tangentSpaceModelContinuousLinearEquiv (I := I) β) A)) i *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
              ((trivToE (I := I) β β) W)) j *
          chartChristoffel (I := I) (B.family.metric r) β i j k (extChartAt I β β)) •
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)
      = ∑ i, ∑ j, ∑ k,
        (chartChristoffel (I := I) (B.family.metric r) β i j k (extChartAt I β β) *
          chartCoord (E := E) i (trivToE (I := I) β β A) *
          chartCoord (E := E) j (trivToE (I := I) β β W)) •
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
            Finset.sum_congr rfl (fun k _ => ?_)))
          rw [chartCoord_def, chartCoord_def]
          simp only [trivToE_basepoint]
          congr 1
          ring
    _ = ∑ k, ∑ i, ∑ j,
        (chartChristoffel (I := I) (B.family.metric r) β i j k (extChartAt I β β) *
          chartCoord (E := E) i (trivToE (I := I) β β A) *
          chartCoord (E := E) j (trivToE (I := I) β β W)) •
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k :=
        sum_rotate (fun i j k =>
          (chartChristoffel (I := I) (B.family.metric r) β i j k (extChartAt I β β) *
            chartCoord (E := E) i (trivToE (I := I) β β A) *
            chartCoord (E := E) j (trivToE (I := I) β β W)) •
          DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)
    _ = ∑ k, (∑ i, ∑ j,
        chartChristoffel (I := I) (B.family.metric r) β i j k (extChartAt I β β) *
          chartCoord (E := E) i (trivToE (I := I) β β A) *
          chartCoord (E := E) j (trivToE (I := I) β β W)) •
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          exact sum_sum_smul_univ (fun i j =>
            chartChristoffel (I := I) (B.family.metric r) β i j k (extChartAt I β β) *
              chartCoord (E := E) i (trivToE (I := I) β β A) *
              chartCoord (E := E) j (trivToE (I := I) β β W))
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)

omit [SigmaCompactSpace M] in
theorem trivToE_connectionVariation
    {D : RealTimeInterval} {a b s u : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (β : M) (t : ℝ) (ht : t ∈ Icc s u) (A W : TangentSpace I β) :
    trivToE (I := I) β β (connectionVariation B.family (Icc s u) t β A W) =
      ∑ k, (∑ i, ∑ j,
        (derivWithin (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k
          (extChartAt I β β)) (Icc s u) t)
        * chartCoord (E := E) i (trivToE (I := I) β β A)
        * chartCoord (E := E) j (trivToE (I := I) β β W))
      • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k := by
  classical
  have huniq : UniqueDiffWithinAt ℝ (Icc s u) t := (uniqueDiffOn_Icc hsu) t ht
  have hbase : β ∈ (trivializationAt E (TangentSpace I) β).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) β
  have hy₀int : ((extChartAt I β) : M → E) β ∈ interior (extChartAt I β).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) β ((extChartAt I β).map_source (mem_extChartAt_source (I := I) β))
  have hterm (i j k : Fin (Module.finrank ℝ E)) :
      HasDerivWithinAt
        (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k (extChartAt I β β))
        (derivWithin (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k
          (extChartAt I β β)) (Icc s u) t) (Icc s u) t := by
    have hcont : ContDiffOn ℝ ∞
        (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
        (Icc s u ×ˢ interior (extChartAt I β).target) :=
      MetricFamilySmoothOn.chartChristoffelOnE_contDiffOn (I := I) (D := D)
        (g_fam := B.family.metric) B.smooth (J := Icc s u)
        (fun r hr => B.regular (hwindow hr)) (uniqueDiffOn_Icc hsu) β i j k
    have hdiff : DifferentiableWithinAt ℝ
        (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
        (Icc s u ×ˢ interior (extChartAt I β).target)
        (t, ((extChartAt I β) : M → E) β) :=
      (hcont.differentiableOn (by simp)) _ ⟨ht, hy₀int⟩
    have hφ : HasDerivWithinAt (fun r : ℝ => (r, ((extChartAt I β) : M → E) β))
        (1, 0) (Icc s u) t :=
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t ((extChartAt I β : M → E) β))).hasDerivWithinAt
    have hcomp := hdiff.hasFDerivWithinAt.comp_hasDerivWithinAt t hφ
      (fun r hr => (show (r, ((extChartAt I β) : M → E) β) ∈
        Icc s u ×ˢ interior (extChartAt I β).target from ⟨hr, hy₀int⟩))
    exact hcomp.congr_deriv (hcomp.derivWithin huniq).symm
  have hsum : HasDerivWithinAt
      (fun r => ∑ k, (∑ i, ∑ j,
        chartChristoffel (I := I) (B.family.metric r) β i j k (extChartAt I β β)
        * chartCoord (E := E) i (trivToE (I := I) β β A)
        * chartCoord (E := E) j (trivToE (I := I) β β W))
        • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)
      (∑ k, (∑ i, ∑ j,
        (derivWithin (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k
          (extChartAt I β β)) (Icc s u) t)
        * chartCoord (E := E) i (trivToE (I := I) β β A)
        * chartCoord (E := E) j (trivToE (I := I) β β W))
        • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k) (Icc s u) t := by
    refine HasDerivWithinAt.fun_sum (u := Finset.univ) (fun k _ => ?_)
    refine (HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
      HasDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ => ?_))).smul_const _
    exact ((hterm i j k).mul_const _).mul_const _
  have hhas : HasDerivWithinAt
      (fun r => trivFromE (I := I) β β (∑ k, (∑ i, ∑ j,
        chartChristoffel (I := I) (B.family.metric r) β i j k (extChartAt I β β)
        * chartCoord (E := E) i (trivToE (I := I) β β A)
        * chartCoord (E := E) j (trivToE (I := I) β β W))
        • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k))
      (trivFromE (I := I) β β (∑ k, (∑ i, ∑ j,
        (derivWithin (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k
          (extChartAt I β β)) (Icc s u) t)
        * chartCoord (E := E) i (trivToE (I := I) β β A)
        * chartCoord (E := E) j (trivToE (I := I) β β W))
        • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)) (Icc s u) t :=
    (trivFromE (I := I) β β).hasFDerivAt.comp_hasDerivWithinAt t hsum
  have hpoint (r : ℝ) : B.family.connection r (tangentConstAt (I := I) β W) β A
      = trivFromE (I := I) β β (∑ k, (∑ i, ∑ j,
        chartChristoffel (I := I) (B.family.metric r) β i j k (extChartAt I β β)
        * chartCoord (E := E) i (trivToE (I := I) β β A)
        * chartCoord (E := E) j (trivToE (I := I) β β W))
        • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k) := by
    rw [← trivFromE_trivToE (I := I) β hbase
      (B.family.connection r (tangentConstAt (I := I) β W) β A)]
    exact congrArg (trivFromE (I := I) β β)
      (trivToE_connection_apply_chart B β r A W)
  have hderiv : HasDerivWithinAt
      (fun r => B.family.connection r (tangentConstAt (I := I) β W) β A)
      (trivFromE (I := I) β β (∑ k, (∑ i, ∑ j,
        (derivWithin (fun r => chartChristoffel (I := I) (B.family.metric r) β i j k
          (extChartAt I β β)) (Icc s u) t)
        * chartCoord (E := E) i (trivToE (I := I) β β A)
        * chartCoord (E := E) j (trivToE (I := I) β β W))
        • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)) (Icc s u) t :=
    hhas.congr (fun r _ => hpoint r) (hpoint t)
  rw [connectionVariation, hderiv.derivWithin huniq, trivToE_trivFromE (I := I) β hbase]


omit [SigmaCompactSpace M] in
theorem trivToE_connectionVariation_curveMap
    {D : RealTimeInterval} {a b s u : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (x t : ℝ) (ht : t ∈ Icc s u)
    (A W : TangentSpace I (c.lift x t)) :
    (trivializationAt E (TangentSpace I) (c.lift x t)).continuousLinearMapAt ℝ (c.lift x t)
        (connectionVariation B.family (Icc s u) t (c.lift x t) A W) =
      ∑ k, (∑ i, ∑ j,
        (derivWithin (fun r => chartChristoffel (I := I) (B.family.metric r) (c.lift x t) i j k
          (extChartAt I (c.lift x t) (c.lift x t))) (Icc s u) t)
        * chartCoord (E := E) i
            ((trivializationAt E (TangentSpace I) (c.lift x t)).continuousLinearMapAt ℝ (c.lift x t) A)
        * chartCoord (E := E) j
            ((trivializationAt E (TangentSpace I) (c.lift x t)).continuousLinearMapAt ℝ (c.lift x t) W))
      • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k :=
  trivToE_connectionVariation (I := I) (M := M) B hsu hwindow (c.lift x t) t ht A W



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
theorem chartRep_field_contDiffWithinAt
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (V : c.Field (I := I)) (hV : V.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    ∀ᶠ z in 𝓝[univ ×ˢ J] (x, t), ContDiffWithinAt ℝ ∞
      (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (c.lift x t)).continuousLinearMapAt ℝ
          (c.lift p.1 p.2) (V p.1 p.2)) (univ ×ˢ J) z := by
  classical
  set F : ℝ × ℝ → TangentBundle I M :=
    fun p => (⟨c.lift p.1 p.2, V p.1 p.2⟩ : TangentBundle I M) with hF
  have hcont : ContinuousWithinAt (fun p : ℝ × ℝ => c.lift p.1 p.2) (univ ×ˢ J) (x, t) :=
    (hc (x, t) ⟨mem_univ x, ht⟩).continuousWithinAt
  have hbase : c.lift x t
      ∈ (trivializationAt E (TangentSpace I) (c.lift x t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (c.lift x t)
  have hneigh : (fun p : ℝ × ℝ => c.lift p.1 p.2) ⁻¹'
      (trivializationAt E (TangentSpace I) (c.lift x t)).baseSet ∈ 𝓝[univ ×ˢ J] (x, t) :=
    hcont.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) (c.lift x t)).open_baseSet.mem_nhds hbase)
  filter_upwards [hneigh, self_mem_nhdsWithin] with z hz hzS
  have htotal : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I.tangent ∞ F (univ ×ˢ J) z := hV z hzS
  have hsrc : F z ∈ (trivializationAt E (TangentSpace I) (c.lift x t)).source := by
    rw [hF, Trivialization.mem_source]
    exact hz
  have hiff := (Bundle.Trivialization.contMDiffWithinAt_iff
    (e := trivializationAt E (TangentSpace I) (c.lift x t)) (f := F) hsrc).mp htotal
  have hcontz : ContinuousWithinAt (fun p : ℝ × ℝ => c.lift p.1 p.2) (univ ×ˢ J) z :=
    (hc z hzS).continuousWithinAt
  have hsrc' : (fun p : ℝ × ℝ => c.lift p.1 p.2) ⁻¹'
      (trivializationAt E (TangentSpace I) (c.lift x t)).baseSet ∈ 𝓝[univ ×ˢ J] z :=
    hcontz.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) (c.lift x t)).open_baseSet.mem_nhds hz)
  have heq : (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (c.lift x t) (F p)).2)
      =ᶠ[𝓝[univ ×ˢ J] z]
      fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (c.lift x t)).continuousLinearMapAt ℝ
          (c.lift p.1 p.2) (V p.1 p.2) := by
    filter_upwards [hsrc', self_mem_nhdsWithin] with p hp _
    have hp' : c.lift p.1 p.2
        ∈ (trivializationAt E (TangentSpace I) (c.lift x t)).baseSet := hp
    rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (e := trivializationAt E (TangentSpace I) (c.lift x t)) hp' (V p.1 p.2)]
  have hcd : ContDiffWithinAt ℝ ∞ (fun p : ℝ × ℝ =>
      (trivializationAt E (TangentSpace I) (c.lift x t) (F p)).2) (univ ×ˢ J) z :=
    contMDiffWithinAt_iff_contDiffWithinAt.mp hiff.2
  exact hcd.congr_of_eventuallyEq heq.symm (heq.symm.eq_of_nhdsWithin hzS)



omit [CompleteSpace E] [SigmaCompactSpace M] hBoundary in
theorem connectionForm_leviCivita_apply_chart
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (X : TangentSpace I x) (v : E) :
    (LeviCivita g).connectionForm (trivializationAt E (TangentSpace I) α) x X v =
      chartChristoffelContraction g α (trivToE (I := I) α x X) v (extChartAt I α x) := by
  let e := trivializationAt E (TangentSpace I) α
  have he : x ∈ e.baseSet := chartLeviCivitaGoodSet_mem_baseSet hx
  let σ := fun y => e.symmL ℝ y v
  have hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% σ) x := by
    rw [e.mdifferentiableAt_section_iff I σ he]
    apply (mdifferentiableAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hy]
    exact e.continuousLinearMapAt_symmL hy v
  have hrepr (y : M) (hy : y ∈ e.baseSet) : chartESectionRepr (I := I) α σ y = v := by
    rw [chartE_section_repr_eq_trivToE]
    exact e.continuousLinearMapAt_symmL hy v
  have hconst : (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm) =ᶠ[𝓝 (extChartAt I α x)]
      fun _ => v := by
    filter_upwards [isOpen_interior.mem_nhds
      (chartLeviCivitaGoodSet_extChartAt_mem_interior hx)] with z hz
    apply hrepr
    have h := (extChartAt I α).map_target (interior_subset hz)
    simpa only [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using h
  have hD : fderiv ℝ (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
      (extChartAt I α x) = 0 := by
    rw [hconst.fderiv_eq, fderiv_const_apply]
  rw [CovariantDerivative.connectionForm_apply _ _ he,
    LeviCivita_chart_apply g α hx hσ X, chartLeviCivita_apply g α σ hx X,
    hD, zero_apply, zero_add, hrepr x he]
  change e.continuousLinearMapAt ℝ x (e.symmL ℝ x (christoffelCorrection g α x v X)) = _
  rw [e.continuousLinearMapAt_symmL he, correction_eq_contr]

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem Dt_eq_derivAlongWithin (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (J : Set ℝ) (V : c.Field (I := I)) (x t : ℝ)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun r => c.lift x r) J t)
    (hγc : ContinuousWithinAt (fun r => c.lift x r) J t)
    (hxs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t) :
    c.Dt g J V x t =
      (LeviCivita (g t)).derivAlongWithin (fun r => c.lift x r) (fun r => V x r) J t := by
  classical
  set γ : ℝ → M := fun r => c.lift x r with hγdef
  set e := trivializationAt E (TangentSpace I) (γ t) with he
  have hgood : γ t ∈ chartLeviCivitaGoodSet (I := I) (γ t) :=
    self_mem_chartLeviCivitaGoodSet (I := I) (γ t)
  have hvel : trivToE (I := I) (γ t) (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
      = derivWithin (chartCurve (I := I) (γ t) γ) J t := by
    change (Trivialization.continuousLinearMapAt ℝ
          (trivializationAt E (TangentSpace I) (γ t)) (γ t))
        ((mfderivWithin 𝓘(ℝ, ℝ) I γ J t : ℝ →L[ℝ] _) (1 : ℝ))
      = (fderivWithin ℝ (fun s : ℝ => extChartAt I (γ t) (γ s)) J t) (1 : ℝ)
    exact Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderivWithin_along_curve_eq_fderivWithin
      (I := I) (γ := γ) (J := J) (t₀ := t) (α := γ t) hγ hγc hxs (mem_chart_source H (γ t))
  have hZ : (fun s : ℝ => e.continuousLinearMapAt ℝ (γ s) (V x s))
      = chartRepAt (I := I) γ (V x) t := rfl
  rw [Dt_eq_symmL_chart (c := c) (g := g) (J := J) (V := V) (x := x) (t := t)]
  simp only [CovariantDerivative.derivAlongWithin]
  rw [hZ, connectionForm_leviCivita_apply_chart (g t) (γ t) hgood
    (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))
    (e.continuousLinearMapAt ℝ (γ t) (V x t)), hvel]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem Dx_eq_derivAlongWithin (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (V : c.Field (I := I)) (x t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u => c.lift u t) x) :
    c.Dx g V x t =
      (LeviCivita (g t)).derivAlongWithin (fun u => c.lift u t) (fun u => V u t) univ x := by
  classical
  change covDerivAlong (I := I) (g t) (fun u => c.lift u t) (fun u => V u t) x = _
  rw [covDerivAlong_def]
  simp only [CovariantDerivative.derivAlongWithin, chartCovDerivAlong_def, derivWithin_univ,
    mfderivWithin_univ]
  congr 1
  rw [connectionForm_leviCivita_apply_chart (g t) (c.lift x t)
      (self_mem_chartLeviCivitaGoodSet (I := I) (c.lift x t))
      (mfderiv 𝓘(ℝ, ℝ) I (fun u => c.lift u t) x ((NormedSpace.fromTangentSpace x).symm 1))
      ((trivializationAt E (TangentSpace I) (c.lift x t)).continuousLinearMapAt ℝ
        (c.lift x t) (V x t))]
  congr 1
  congr 1
  change (fderiv ℝ (fun u : ℝ => extChartAt I (c.lift x t) (c.lift u t)) x) (1 : ℝ)
    = (Trivialization.continuousLinearMapAt ℝ
        (trivializationAt E (TangentSpace I) (c.lift x t)) (c.lift x t))
      ((mfderiv 𝓘(ℝ, ℝ) I (fun u => c.lift u t) x : ℝ →L[ℝ] _) (1 : ℝ))
  exact (Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
    (I := I) hγ (c.lift x t) (mem_chart_source H (c.lift x t))).symm


omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem trivToE_Dx_eq_chart
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M) (V : c.Field (I := I))
    (β : M) (u s : ℝ)
    (hgood : c.lift u s ∈ chartLeviCivitaGoodSet (I := I) β)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y : ℝ => c.lift y s) u)
    (hVtot : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E))
      (fun y : ℝ => (⟨c.lift y s, V y s⟩ : TotalSpace E (TangentSpace I))) univ u) :
    trivToE (I := I) β (c.lift u s) (c.Dx g V u s) =
      deriv (fun y : ℝ => trivToE (I := I) β (c.lift y s) (V y s)) u
        + chartChristoffelContraction (I := I) (g s) β
            (deriv (chartCurve (I := I) β (fun y : ℝ => c.lift y s)) u)
            (trivToE (I := I) β (c.lift u s) (V u s))
            (chartCurve (I := I) β (fun y : ℝ => c.lift y s) u) := by
  classical
  have hbase : c.lift u s ∈ (trivializationAt E (TangentSpace I) β).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hgood
  have hsrc : c.lift u s ∈ (chartAt H β).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hgood
  have hvel : trivToE (I := I) β (c.lift u s)
      (mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c.lift y s) u
        ((NormedSpace.fromTangentSpace u).symm 1))
      = deriv (chartCurve (I := I) β (fun y : ℝ => c.lift y s)) u := by
    have h1 : (mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c.lift y s) u
          ((NormedSpace.fromTangentSpace u).symm 1))
        = ((mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c.lift y s) u : ℝ →L[ℝ] _) 1) := rfl
    rw [h1]
    have h2 := Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        hγ β hsrc
    rw [fderiv_apply_one_eq_deriv] at h2
    exact h2
  rw [Dx_eq_derivAlongWithin (I := I) (M := M) g c V u s hγ]
  rw [CovariantDerivative.derivAlongWithin_coord (I := I) (cov := LeviCivita (g s))
    (e := trivializationAt E (TangentSpace I) β) (γ := fun y : ℝ => c.lift y s)
    (Z := fun y : ℝ => V y s) (J := univ) (t := u) hbase hVtot]
  simp only [derivWithin_univ, mfderivWithin_univ]
  rw [connectionForm_leviCivita_apply_chart (I := I) (M := M) (g s) β hgood, hvel]
  rfl


omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ E] hBoundary in
theorem Field.time_slice_contMDiffWithinAt (c : CurveMap M) (J : Set ℝ) (V : c.Field (I := I))
    (hV : V.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun s : ℝ => (⟨c.lift x s, V x s⟩ : TotalSpace E (TangentSpace I))) J t := by
  have hmem : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun s : ℝ => (x, s)) J t := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
  have hto : Set.MapsTo (fun s : ℝ => (x, s)) J ((univ : Set ℝ) ×ˢ J) :=
    fun s _ => ⟨mem_univ x, by assumption⟩
  exact hV (x, t) hmem |>.comp t hz hto

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ E] hBoundary in
theorem Field.space_slice_contMDiffWithinAt (c : CurveMap M) (J : Set ℝ) (V : c.Field (I := I))
    (hV : V.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun z : ℝ => (⟨c.lift z t, V z t⟩ : TotalSpace E (TangentSpace I))) univ x := by
  have hmem : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun z : ℝ => (z, t)) univ x := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_id.prodMk contMDiffWithinAt_const
  have hto : Set.MapsTo (fun z : ℝ => (z, t)) univ ((univ : Set ℝ) ×ˢ J) :=
    fun z _ => ⟨mem_univ z, ht⟩
  exact hV (x, t) hmem |>.comp x hz hto

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
theorem hasDerivWithinAt_chartChristoffelContraction_metricFamily_joint
    (g : ℝ → SmoothRiemannianMetric I M) (β : M) (P Q y : ℝ → E) (P' Q' y' : E)
    {J : Set ℝ} {t : ℝ}
    (huniqJ : UniqueDiffOn ℝ J) (htJ : t ∈ J) (hcl : t ∈ closure (interior J))
    (hy₀ : y t ∈ interior (extChartAt I β).target)
    (hP : HasDerivWithinAt P P' J t) (hQ : HasDerivWithinAt Q Q' J t)
    (hy : HasDerivWithinAt y y' J t)
    (hjoint : ∀ i j k, ContDiffWithinAt ℝ 2
        (fun p : ℝ × E => chartChristoffel (I := I) (g p.1) β i j k p.2)
        (J ×ˢ interior (extChartAt I β).target) (t, y t)) :
    HasDerivWithinAt (fun r => chartChristoffelContraction (I := I) (g r) β (P r) (Q r) (y r))
      (chartChristoffelContraction (I := I) (g t) β P' (Q t) (y t)
       + chartChristoffelContraction (I := I) (g t) β (P t) Q' (y t)
       + fderiv ℝ (chartChristoffelContraction (I := I) (g t) β (P t) (Q t)) (y t) y'
       + (∑ k : Fin (Module.finrank ℝ E),
            (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              (derivWithin (fun r => chartChristoffel (I := I) (g r) β i j k (y t)) J t)
                * chartCoord (E := E) i (P t) * chartCoord (E := E) j (Q t))
            • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)) J t := by
  classical
  have _ := hcl
  have huniqJt : UniqueDiffWithinAt ℝ J t := huniqJ t htJ
  have hy₀' : y t ∈ interior (extChartAt I β).target := hy₀
  have hS : interior (extChartAt I β).target ∈ 𝓝 (y t) :=
    isOpen_interior.mem_nhds hy₀'
  have hterm : ∀ i j k : Fin (Module.finrank ℝ E),
      HasDerivWithinAt
        (fun r => chartChristoffel (I := I) (g r) β i j k (y r))
        (derivWithin (fun r => chartChristoffel (I := I) (g r) β i j k (y t)) J t
          + fderiv ℝ (chartChristoffel (I := I) (g t) β i j k) (y t) y') J t := by
    intro i j k
    set L : (ℝ × E) →L[ℝ] ℝ := fderivWithin ℝ
      (fun p : ℝ × E => chartChristoffel (I := I) (g p.1) β i j k p.2)
      (J ×ˢ interior (extChartAt I β).target) (t, y t) with hLdef
    have hΘ : HasFDerivWithinAt
        (fun p : ℝ × E => chartChristoffel (I := I) (g p.1) β i j k p.2) L
        (J ×ˢ interior (extChartAt I β).target) (t, y t) :=
      (hjoint i j k).differentiableWithinAt (by norm_num) |>.hasFDerivWithinAt
    have hchain := hasDerivWithinAt_comp_pair_tendsto (E := E) (S := interior (extChartAt I β).target)
      hΘ hy hS
    have hslice1 : HasDerivWithinAt
        (fun r : ℝ => chartChristoffel (I := I) (g r) β i j k (y t)) (L (1, 0)) J t := by
      have hφ : HasDerivWithinAt (fun r : ℝ => (r, y t)) (((1 : ℝ), (0 : E))) J t :=
        (hasDerivWithinAt_id t J).prodMk ((hasDerivAt_const t (y t)).hasDerivWithinAt)
      exact hΘ.comp_hasDerivWithinAt t hφ (fun s hs => Set.mk_mem_prod hs hy₀')
    have hL10 : L (1, 0) =
        derivWithin (fun r => chartChristoffel (I := I) (g r) β i j k (y t)) J t :=
      (hslice1.derivWithin huniqJt).symm
    have hslice2 : HasFDerivWithinAt
        (fun u : E => chartChristoffel (I := I) (g t) β i j k u)
        (L.comp (ContinuousLinearMap.inr ℝ ℝ E)) (interior (extChartAt I β).target) (y t) := by
      have hφ : HasFDerivWithinAt (fun u : E => (t, u))
          (ContinuousLinearMap.inr ℝ ℝ E) (interior (extChartAt I β).target) (y t) :=
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (y t)).hasFDerivWithinAt
      exact hΘ.comp (y t) hφ (fun u hu => ⟨htJ, hu⟩)
    have hfd : fderiv ℝ (chartChristoffel (I := I) (g t) β i j k) (y t) =
        L.comp (ContinuousLinearMap.inr ℝ ℝ E) :=
      ((hasFDerivWithinAt_of_mem_nhds hS).mp hslice2).fderiv
    have hL0 : L (0, y') =
        fderiv ℝ (chartChristoffel (I := I) (g t) β i j k) (y t) y' := by
      rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    refine hchain.congr_deriv ?_
    rw [hL10, hL0]
  have hsumk : ∀ k : Fin (Module.finrank ℝ E),
      HasDerivWithinAt
        (fun r => (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) (g r) β i j k (y r) *
              chartCoord (E := E) i (P r) * chartCoord (E := E) j (Q r))
          • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)
        ((∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ((derivWithin (fun r => chartChristoffel (I := I) (g r) β i j k (y t)) J t
              + fderiv ℝ (chartChristoffel (I := I) (g t) β i j k) (y t) y')
              * chartCoord (E := E) i (P t) * chartCoord (E := E) j (Q t)
              + chartChristoffel (I := I) (g t) β i j k (y t) * chartCoord (E := E) i P'
                * chartCoord (E := E) j (Q t)
              + chartChristoffel (I := I) (g t) β i j k (y t) * chartCoord (E := E) i (P t)
                * chartCoord (E := E) j Q'))
          • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k) J t := by
    intro k
    have hinner : HasDerivWithinAt
        (fun r => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) (g r) β i j k (y r) *
              chartCoord (E := E) i (P r) * chartCoord (E := E) j (Q r))
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ((derivWithin (fun r => chartChristoffel (I := I) (g r) β i j k (y t)) J t
              + fderiv ℝ (chartChristoffel (I := I) (g t) β i j k) (y t) y')
              * chartCoord (E := E) i (P t) * chartCoord (E := E) j (Q t)
              + chartChristoffel (I := I) (g t) β i j k (y t) * chartCoord (E := E) i P'
                * chartCoord (E := E) j (Q t)
              + chartChristoffel (I := I) (g t) β i j k (y t) * chartCoord (E := E) i (P t)
                * chartCoord (E := E) j Q')) J t := by
      refine HasDerivWithinAt.fun_sum (fun i _ => ?_)
      refine HasDerivWithinAt.fun_sum (fun j _ => ?_)
      refine ((hterm i j k).mul (hasDerivWithinAt_chartCoord_comp (E := E) hP i)).mul
        (hasDerivWithinAt_chartCoord_comp (E := E) hQ j) |>.congr_deriv ?_
      simp only [Pi.mul_apply]
      ring
    simpa only [Finset.sum_apply] using
      hinner.smul_const (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)
  have hsum : HasDerivWithinAt
      (fun r => ∑ k : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) (g r) β i j k (y r) *
                chartCoord (E := E) i (P r) * chartCoord (E := E) j (Q r))
            • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)
      (∑ k : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              ((derivWithin (fun r => chartChristoffel (I := I) (g r) β i j k (y t)) J t
                + fderiv ℝ (chartChristoffel (I := I) (g t) β i j k) (y t) y')
                * chartCoord (E := E) i (P t) * chartCoord (E := E) j (Q t)
                + chartChristoffel (I := I) (g t) β i j k (y t) * chartCoord (E := E) i P'
                  * chartCoord (E := E) j (Q t)
                + chartChristoffel (I := I) (g t) β i j k (y t) * chartCoord (E := E) i (P t)
                  * chartCoord (E := E) j Q'))
            • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k) J t := by
    refine HasDerivWithinAt.fun_sum (fun k _ => ?_)
    exact hsumk k
  have hfuneq : (fun r => chartChristoffelContraction (I := I) (g r) β (P r) (Q r) (y r))
      = fun r => ∑ k : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) (g r) β i j k (y r) *
                chartCoord (E := E) i (P r) * chartCoord (E := E) j (Q r))
            • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k := by
    funext r
    rw [chartChristoffelContraction_def]
  rw [hfuneq]
  refine hsum.congr_deriv ?_
  rw [chartChristoffelContraction_def, chartChristoffelContraction_def,
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartChristoffelContraction_fderiv_apply
      (I := I) (g t) β (y t) hy₀' (P t) (Q t) y']
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← add_smul, ← add_smul, ← add_smul]
  congr 1
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring


omit [SigmaCompactSpace M] in
theorem pullback_commutator {D : RealTimeInterval} {a b s u : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (V : c.Field (I := I)) (hV : V.SmoothOn (I := I) (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    c.Dt B.family.metric (Icc s u) (c.Dx B.family.metric V) x t -
      c.Dx B.family.metric (c.Dt B.family.metric (Icc s u) V) x t =
    riemannVector B.family t (c.lift x t) (c.velocity (Icc s u) x t) (c.X x t) (V x t) +
      connectionVariation B.family (Icc s u) t (c.lift x t) (c.X x t) (V x t) := by
  classical
  set J : Set ℝ := Icc s u with hJ
  have htJ : t ∈ J := ht
  have huniqJ : UniqueDiffOn ℝ J := by rw [hJ]; exact uniqueDiffOn_Icc hsu
  have huniqJt : UniqueDiffWithinAt ℝ J t := huniqJ t htJ
  have hcl : t ∈ closure (interior J) := by
    rw [hJ, closure_interior_Icc (ne_of_lt hsu)]; exact ht
  have hJreg : J ⊆ D.regular := fun r hr => B.regular (hwindow (hJ ▸ hr))
  let β : M := c.lift x t
  let Φ : ℝ × ℝ → E := fun p => extChartAt I β (c.lift p.1 p.2)
  let Z : ℝ × ℝ → E := fun p => trivToE (I := I) β (c.lift p.1 p.2) (V p.1 p.2)
  have hΦsmooth : ∀ᶠ z in 𝓝[univ ×ˢ J] (x, t), ContDiffWithinAt ℝ 2 Φ (univ ×ˢ J) z := by
    have hct : ContinuousWithinAt (fun p : ℝ × ℝ => c.lift p.1 p.2) (univ ×ˢ J) (x, t) :=
      (hc (x, t) ⟨mem_univ x, htJ⟩).continuousWithinAt
    have hsrc : (fun p : ℝ × ℝ => c.lift p.1 p.2) ⁻¹' (chartAt H β).source
        ∈ 𝓝[univ ×ˢ J] (x, t) :=
      hct.preimage_mem_nhdsWithin ((chartAt H β).open_source.mem_nhds (mem_chart_source H β))
    filter_upwards [hsrc, self_mem_nhdsWithin] with z hz hzS
    have hz2 : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I ∞
        (fun p : ℝ × ℝ => c.lift p.1 p.2) (univ ×ˢ J) z := hc z hzS
    have hext : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I β) (c.lift z.1 z.2) :=
      contMDiffAt_extChartAt' (I := I) (n := ∞) (x := β) hz
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp
      ((hext.comp_contMDiffWithinAt z hz2).of_le (by decide))
  have hZsmooth : ∀ᶠ z in 𝓝[univ ×ˢ J] (x, t), ContDiffWithinAt ℝ 2 Z (univ ×ˢ J) z := by
    have h := chartRep_field_contDiffWithinAt (I := I) (M := M) c J hc V hV x t htJ
    filter_upwards [h] with z hz
    exact hz.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgood_self : β ∈ chartLeviCivitaGoodSet (I := I) β :=
    self_mem_chartLeviCivitaGoodSet (I := I) β
  have hDxChart : (fun r : ℝ => trivToE (I := I) β (c.lift x r) ((c.Dx B.family.metric V) x r))
      =ᶠ[𝓝[J] t]
      (fun r : ℝ => deriv (fun y : ℝ => Z (y, r)) x
        + chartChristoffelContraction (I := I) (B.family.metric r) β
            (deriv (fun y : ℝ => Φ (y, r)) x) (Z (x, r)) (Φ (x, r))) := by
    have ht' : ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ (fun r : ℝ => c.lift x r) J t :=
      c.time_slice_contMDiffWithinAt (I := I) J hc x t htJ
    have hgood_ev : (fun r : ℝ => c.lift x r) ⁻¹'
        (chartLeviCivitaGoodSet (I := I) β) ∈ 𝓝[J] t :=
      ht'.continuousWithinAt.preimage_mem_nhdsWithin
        ((chartLeviCivitaGoodSet_isOpen (I := I) β).mem_nhds hgood_self)
    filter_upwards [hgood_ev, self_mem_nhdsWithin] with r hgood_r hrJ
    have hV_r : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E))
        (fun y : ℝ => (⟨c.lift y r, V y r⟩ : TotalSpace E (TangentSpace I))) univ x :=
      (Field.space_slice_contMDiffWithinAt (I := I) c J V hV x r hrJ).mdifferentiableWithinAt
        (by norm_num)
    have hγ_r : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y : ℝ => c.lift y r) x :=
      (contMDiffWithinAt_univ.mp
        (c.space_slice_contMDiffWithinAt (I := I) J hc x r hrJ)).mdifferentiableAt (by norm_num)
    exact trivToE_Dx_eq_chart (I := I) (M := M) B.family.metric c V β x r hgood_r hγ_r hV_r
  have hDtChart : (fun u : ℝ => trivToE (I := I) β (c.lift u t)
        ((c.Dt B.family.metric J V) u t))
      =ᶠ[𝓝 x]
      (fun u : ℝ => derivWithin (fun r : ℝ => Z (u, r)) J t
        + chartChristoffelContraction (I := I) (B.family.metric t) β
            (derivWithin (fun r : ℝ => Φ (u, r)) J t) (Z (u, t)) (Φ (u, t))) := by
    have hcont : ContinuousAt (fun u : ℝ => c.lift u t) x :=
      (contMDiffWithinAt_univ.mp
        (c.space_slice_contMDiffWithinAt (I := I) J hc x t htJ)).continuousAt
    have hgood_ev : (fun u : ℝ => c.lift u t) ⁻¹'
        (chartLeviCivitaGoodSet (I := I) β) ∈ 𝓝 x :=
      hcont.preimage_mem_nhds ((chartLeviCivitaGoodSet_isOpen (I := I) β).mem_nhds hgood_self)
    filter_upwards [hgood_ev] with u hgood_u
    have hbase_u : c.lift u t ∈ (trivializationAt E (TangentSpace I) β).baseSet :=
      chartLeviCivitaGoodSet_mem_baseSet (I := I) hgood_u
    have hsrc_u : c.lift u t ∈ (chartAt H β).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hgood_u
    have hVtot_u : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E))
        (fun r : ℝ => (⟨c.lift u r, V u r⟩ : TotalSpace E (TangentSpace I))) J t :=
      (Field.time_slice_contMDiffWithinAt (I := I) c J V hV u t htJ).mdifferentiableWithinAt
        (by norm_num)
    have hγ_u : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun r : ℝ => c.lift u r) J t :=
      (c.time_slice_contMDiffWithinAt (I := I) J hc u t htJ).mdifferentiableWithinAt (by norm_num)
    have hγc_u : ContinuousWithinAt (fun r : ℝ => c.lift u r) J t :=
      (c.time_slice_contMDiffWithinAt (I := I) J hc u t htJ).continuousWithinAt
    have hvel : trivToE (I := I) β (c.lift u t)
        (mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => c.lift u r) J t
          ((NormedSpace.fromTangentSpace t).symm 1))
        = derivWithin (fun r : ℝ => Φ (u, r)) J t := by
      have h1 : (mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => c.lift u r) J t
            ((NormedSpace.fromTangentSpace t).symm 1))
          = ((mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => c.lift u r) J t : ℝ →L[ℝ] _) 1) :=
        rfl
      rw [h1]
      exact Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderivWithin_along_curve_eq_fderivWithin
        (I := I) (γ := fun r : ℝ => c.lift u r) (J := J) (t₀ := t) (α := β)
        hγ_u hγc_u (by rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]; exact huniqJt) hsrc_u
    rw [Dt_eq_derivAlongWithin (I := I) (M := M) B.family.metric c J V u t hγ_u hγc_u
      (by rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]; exact huniqJt)]
    rw [CovariantDerivative.derivAlongWithin_coord (I := I) (cov := LeviCivita (B.family.metric t))
      (e := trivializationAt E (TangentSpace I) β) (γ := fun r : ℝ => c.lift u r)
      (Z := fun r : ℝ => V u r) (J := J) (t := t) hbase_u hVtot_u]
    rw [connectionForm_leviCivita_apply_chart (I := I) (M := M) (B.family.metric t) β hgood_u,
      hvel]
  have hA1 : HasDerivWithinAt (fun r : ℝ => deriv (fun y : ℝ => Z (y, r)) x)
      (deriv (fun u : ℝ => derivWithin (fun r : ℝ => Z (u, r)) J t) x) J t := by
    have h := hasDerivWithinAt_fderiv_slice_fst_comm (F := Z) (x := x) (t := t) (J := J)
      huniqJ htJ hcl hZsmooth
    have hfun : (fun s : ℝ => fderiv ℝ (fun u : ℝ => Z (u, s)) x 1)
        = fun s : ℝ => deriv (fun u : ℝ => Z (u, s)) x := rfl
    rw [hfun] at h
    have hder : (fderiv ℝ (fun u : ℝ => fderivWithin ℝ (fun r : ℝ => Z (u, r)) J t 1) x 1)
        = deriv (fun u : ℝ => derivWithin (fun r : ℝ => Z (u, r)) J t) x := rfl
    rw [hder] at h
    exact h
  have hPc : HasDerivWithinAt (fun r : ℝ => deriv (fun y : ℝ => Φ (y, r)) x)
      (deriv (fun u : ℝ => derivWithin (fun r : ℝ => Φ (u, r)) J t) x) J t := by
    have h := hasDerivWithinAt_fderiv_slice_fst_comm (F := Φ) (x := x) (t := t) (J := J)
      huniqJ htJ hcl hΦsmooth
    have hfun : (fun s : ℝ => fderiv ℝ (fun u : ℝ => Φ (u, s)) x 1)
        = fun s : ℝ => deriv (fun u : ℝ => Φ (u, s)) x := rfl
    rw [hfun] at h
    have hder : (fderiv ℝ (fun u : ℝ => fderivWithin ℝ (fun r : ℝ => Φ (u, r)) J t 1) x 1)
        = deriv (fun u : ℝ => derivWithin (fun r : ℝ => Φ (u, r)) J t) x := rfl
    rw [hder] at h
    exact h
  have hQc : HasDerivWithinAt (fun r : ℝ => Z (x, r))
      (derivWithin (fun r : ℝ => Z (x, r)) J t) J t := by
    have hdiff : DifferentiableWithinAt ℝ (fun r : ℝ => Z (x, r)) J t :=
      chartRepAtBase_differentiableWithinAt (I := I) (γ := fun r : ℝ => c.lift x r)
        (V := fun r : ℝ => V x r) (J := J) (t := t)
        (Field.time_slice_contMDiffWithinAt (I := I) c J V hV x t htJ)
    exact hdiff.hasFDerivWithinAt.hasDerivWithinAt
  have hRcd : ContDiffWithinAt ℝ 2 (fun r : ℝ => Φ (x, r)) J t := by
    have hsrc : (fun r : ℝ => c.lift x r) ⁻¹' (chartAt H β).source ∈ 𝓝[J] t :=
      (c.time_slice_contMDiffWithinAt (I := I) J hc x t htJ).continuousWithinAt.preimage_mem_nhdsWithin
        ((chartAt H β).open_source.mem_nhds (mem_chart_source H β))
    have hext : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I β) (c.lift x t) :=
      contMDiffAt_extChartAt' (I := I) (n := ∞) (x := β) (mem_chart_source H β)
    have hcomp := hext.comp_contMDiffWithinAt t (c.time_slice_contMDiffWithinAt (I := I) J hc x t htJ)
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp (hcomp.of_le (by decide))
  have hRc : HasDerivWithinAt (fun r : ℝ => Φ (x, r))
      (derivWithin (fun r : ℝ => Φ (x, r)) J t) J t :=
    (hRcd.differentiableWithinAt (by norm_num)).hasFDerivWithinAt.hasDerivWithinAt
  have hRint : Φ (x, t) ∈ interior (extChartAt I β).target :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hgood_self
  have hjoint : ∀ i j k : Fin (Module.finrank ℝ E), ContDiffWithinAt ℝ 2
      (fun p : ℝ × E => chartChristoffel (I := I) (B.family.metric p.1) β i j k p.2)
      (J ×ˢ interior (extChartAt I β).target) (t, Φ (x, t)) := by
    intro i j k
    have hcd := MetricFamilySmoothOn.chartChristoffelOnE_contDiffOn (I := I) (D := D)
      (g_fam := B.family.metric) B.smooth hJreg huniqJ β i j k
    exact (hcd.contDiffWithinAt ⟨htJ, hRint⟩).of_le (by decide)
  set A2' : E := chartChristoffelContraction (I := I) (B.family.metric t) β
          (deriv (fun u : ℝ => derivWithin (fun r : ℝ => Φ (u, r)) J t) x) (Z (x, t)) (Φ (x, t))
        + chartChristoffelContraction (I := I) (B.family.metric t) β
          (deriv (fun y : ℝ => Φ (y, t)) x) (derivWithin (fun r : ℝ => Z (x, r)) J t) (Φ (x, t))
        + fderiv ℝ (chartChristoffelContraction (I := I) (B.family.metric t) β
            (deriv (fun y : ℝ => Φ (y, t)) x) (Z (x, t))) (Φ (x, t))
          (derivWithin (fun r : ℝ => Φ (x, r)) J t)
        + ∑ k : Fin (Module.finrank ℝ E),
            (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              (derivWithin (fun r : ℝ => chartChristoffel (I := I) (B.family.metric r) β
                  i j k (Φ (x, t))) J t)
                * chartCoord (E := E) i (deriv (fun y : ℝ => Φ (y, t)) x)
                * chartCoord (E := E) j (Z (x, t)))
            • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k with hA2'def
  have hA2 : HasDerivWithinAt
      (fun r : ℝ => chartChristoffelContraction (I := I) (B.family.metric r) β
        (deriv (fun y : ℝ => Φ (y, r)) x) (Z (x, r)) (Φ (x, r))) A2' J t := by
    rw [hA2'def]
    exact hasDerivWithinAt_chartChristoffelContraction_metricFamily_joint
      B.family.metric β _ _ _ _ _ _ huniqJ htJ hcl hRint hPc hQc hRc hjoint
  have hA2d : derivWithin (fun r : ℝ => chartChristoffelContraction (I := I) (B.family.metric r) β
        (deriv (fun y : ℝ => Φ (y, r)) x) (Z (x, r)) (Φ (x, r))) J t = A2' :=
    hA2.derivWithin huniqJt
  have hDxChart_self : trivToE (I := I) β (c.lift x t) ((c.Dx B.family.metric V) x t)
      = deriv (fun y : ℝ => Z (y, t)) x
        + chartChristoffelContraction (I := I) (B.family.metric t) β
            (deriv (fun y : ℝ => Φ (y, t)) x) (Z (x, t)) (Φ (x, t)) :=
    hDxChart.self_of_nhdsWithin htJ
  have hLt : trivToE (I := I) β β (c.Dt B.family.metric J (c.Dx B.family.metric V) x t)
      = (deriv (fun u : ℝ => derivWithin (fun r : ℝ => Z (u, r)) J t) x + A2')
        + chartChristoffelContraction (I := I) (B.family.metric t) β
            (derivWithin (fun r : ℝ => Φ (x, r)) J t)
            (deriv (fun y : ℝ => Z (y, t)) x
              + chartChristoffelContraction (I := I) (B.family.metric t) β
                  (deriv (fun y : ℝ => Φ (y, t)) x) (Z (x, t)) (Φ (x, t)))
            (Φ (x, t)) := by
    have hbase_β : β ∈ (trivializationAt E (TangentSpace I) β).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) β
    have hrep : chartRepAtBase (I := I) β (fun r : ℝ => c.lift x r)
        (fun r : ℝ => (c.Dx B.family.metric V) x r)
        = fun r : ℝ => trivToE (I := I) β (c.lift x r) ((c.Dx B.family.metric V) x r) := rfl
    have hcurve : chartCurve (I := I) β (fun r : ℝ => c.lift x r)
        = fun r : ℝ => Φ (x, r) := rfl
    rw [Dt_eq_symmL_chart (c := c) (g := B.family.metric) (J := J)
      (V := c.Dx B.family.metric V) (x := x) (t := t)]
    rw [(trivializationAt E (TangentSpace I) β).continuousLinearMapAt_symmL (R := ℝ) hbase_β]
    rw [hrep, hcurve]
    have hsum : HasDerivWithinAt
        (fun r : ℝ => deriv (fun y : ℝ => Z (y, r)) x
          + chartChristoffelContraction (I := I) (B.family.metric r) β
              (deriv (fun y : ℝ => Φ (y, r)) x) (Z (x, r)) (Φ (x, r)))
        (deriv (fun u : ℝ => derivWithin (fun r : ℝ => Z (u, r)) J t) x + A2') J t :=
      hA1.add hA2
    rw [Filter.EventuallyEq.derivWithin_eq hDxChart hDxChart_self, hsum.derivWithin huniqJt]
    dsimp only
    rw [hDxChart_self]
  let W1 : ℝ → E := fun u : ℝ => derivWithin (fun r : ℝ => Z (u, r)) J t
  let Uc : ℝ → E := fun u : ℝ => derivWithin (fun r : ℝ => Φ (u, r)) J t
  let Yc : ℝ → E := fun u : ℝ => Z (u, t)
  let Sc : ℝ → E := fun u : ℝ => Φ (u, t)
  let W2 : ℝ → E := fun u : ℝ => chartChristoffelContraction (I := I) (B.family.metric t) β
    (Uc u) (Yc u) (Sc u)
  have hΦself : Φ (x, t) = extChartAt I β β := rfl
  have hW1eq : W1 = fun u : ℝ => derivWithin (fun r : ℝ => Z (u, r)) J t := rfl
  have hUceq : Uc = fun u : ℝ => derivWithin (fun r : ℝ => Φ (u, r)) J t := rfl
  have hYceq : Yc = fun u : ℝ => Z (u, t) := rfl
  have hSceq : Sc = fun u : ℝ => Φ (u, t) := rfl
  have hW2eq : W2 = fun u : ℝ => chartChristoffelContraction (I := I) (B.family.metric t) β
      (derivWithin (fun r : ℝ => Φ (u, r)) J t) (Z (u, t)) (Φ (u, t)) := rfl
  have hW1d : HasDerivAt W1 (deriv W1 x) x := by
    have h := hasDerivAt_derivWithin_slice (F := Z) x t huniqJ htJ hcl hZsmooth
    exact h.congr_deriv (DifferentialGeometry.Geometry.Riemannian.Variation.mixed_partialFderivWithin_comm
      Z x t huniqJ htJ hcl hZsmooth)
  have hUcd : HasDerivAt Uc (deriv Uc x) x := by
    have h := hasDerivAt_derivWithin_slice (F := Φ) x t huniqJ htJ hcl hΦsmooth
    exact h.congr_deriv (DifferentialGeometry.Geometry.Riemannian.Variation.mixed_partialFderivWithin_comm
      Φ x t huniqJ htJ hcl hΦsmooth)
  have hZmem : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, htJ⟩
  have hmapst : Set.MapsTo (fun u : ℝ => (u, t)) univ ((univ : Set ℝ) ×ˢ J) :=
    fun u _ => ⟨mem_univ u, htJ⟩
  have hsliceY : ContDiffWithinAt ℝ 2 Yc univ x := by
    have hz : ContDiffWithinAt ℝ 2 (fun u : ℝ => (u, t)) univ x := by fun_prop
    have h := (hZsmooth.self_of_nhdsWithin hZmem).comp x hz hmapst
    simpa only [Function.comp_def, Yc] using h
  have hsliceS : ContDiffWithinAt ℝ 2 Sc univ x := by
    have hz : ContDiffWithinAt ℝ 2 (fun u : ℝ => (u, t)) univ x := by fun_prop
    have h := (hΦsmooth.self_of_nhdsWithin hZmem).comp x hz hmapst
    simpa only [Function.comp_def, Sc] using h
  have hYcd : HasDerivAt Yc (deriv Yc x) x :=
    (((hsliceY.differentiableWithinAt (by norm_num)).differentiableAt Filter.univ_mem).hasDerivAt)
  have hScd : HasDerivAt Sc (deriv Sc x) x :=
    (((hsliceS.differentiableWithinAt (by norm_num)).differentiableAt Filter.univ_mem).hasDerivAt)
  set W2' : E := ∑ k : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((fderiv ℝ (chartChristoffel (I := I) (B.family.metric t) β i j k) (Sc x) (deriv Sc x)) *
            chartCoord (E := E) i (Uc x) * chartCoord (E := E) j (Yc x)
          + chartChristoffel (I := I) (B.family.metric t) β i j k (Sc x) *
            chartCoord (E := E) i (deriv Uc x) * chartCoord (E := E) j (Yc x)
          + chartChristoffel (I := I) (B.family.metric t) β i j k (Sc x) *
            chartCoord (E := E) i (Uc x) * chartCoord (E := E) j (deriv Yc x))) •
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k with hW2'def
  have hW2d : HasDerivAt W2 W2' x := by
    rw [hW2'def]
    exact DifferentialGeometry.Geometry.Riemannian.Variation.hasDerivAt_chartChristoffelContraction
      (I := I) (B.family.metric t) β hUcd hYcd hScd
      (fun i j k => ((chartChristoffel_contDiffOn_interior (I := I) (B.family.metric t) β i j k).contDiffAt
        (isOpen_interior.mem_nhds hRint)).differentiableAt (by norm_num))
  have hLx : trivToE (I := I) β β (c.Dx B.family.metric (c.Dt B.family.metric J V) x t)
      = (deriv W1 x + W2')
        + chartChristoffelContraction (I := I) (B.family.metric t) β
            (deriv Sc x) (W1 x + W2 x) (Sc x) := by
    have hbase_β : β ∈ (trivializationAt E (TangentSpace I) β).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) β
    change trivToE (I := I) β β (covDerivAlong (I := I) (B.family.metric t)
      (fun u : ℝ => c.lift u t) (fun u : ℝ => (c.Dt B.family.metric J V) u t) x) = _
    rw [covDerivAlong_def, (trivializationAt E (TangentSpace I) β).continuousLinearMapAt_symmL
      (R := ℝ) hbase_β]
    rw [chartCovDerivAlong_def]
    have hcurve : chartCurve (I := I) (c.lift x t) (fun u : ℝ => c.lift u t) = Sc := rfl
    have hWu : (fun u : ℝ => chartRepAt (I := I) (fun u : ℝ => c.lift u t)
          (fun u : ℝ => (c.Dt B.family.metric J V) u t) x u) =ᶠ[𝓝 x] (W1 + W2) := by
      filter_upwards [hDtChart] with u hu
      exact hu
    have hWu_self : chartRepAt (I := I) (fun u : ℝ => c.lift u t)
        (fun u : ℝ => (c.Dt B.family.metric J V) u t) x x = W1 x + W2 x :=
      hWu.self_of_nhds
    rw [hcurve, Filter.EventuallyEq.deriv_eq hWu, hWu_self, (hW1d.add hW2d).deriv]
  have hγx : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => c.lift u t) x :=
    (contMDiffWithinAt_univ.mp
      (c.space_slice_contMDiffWithinAt (I := I) J hc x t htJ)).mdifferentiableAt (by norm_num)
  have hXcoord : trivToE (I := I) β β (c.X x t) = deriv Sc x := by
    have h := Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      hγx β (mem_chart_source H β)
    rw [fderiv_apply_one_eq_deriv] at h
    exact h
  have hVcoord : trivToE (I := I) β β (V x t) = Yc x := rfl
  have hvelCoord : trivToE (I := I) β β (c.velocity J x t) = Uc x := by
    have hγc : ContinuousWithinAt (fun r : ℝ => c.lift x r) J t :=
      (c.time_slice_contMDiffWithinAt (I := I) J hc x t htJ).continuousWithinAt
    have hγJ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun r : ℝ => c.lift x r) J t :=
      (c.time_slice_contMDiffWithinAt (I := I) J hc x t htJ).mdifferentiableWithinAt (by norm_num)
    have h := Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderivWithin_along_curve_eq_fderivWithin
      (I := I) (γ := fun r : ℝ => c.lift x r) (J := J) (t₀ := t) (α := β) hγJ hγc
      (by rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]; exact huniqJt)
      (mem_chart_source H β)
    exact h
  have hRv : trivToE (I := I) β β (connectionVariation B.family J t β (c.X x t) (V x t))
      = ∑ k : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (derivWithin (fun r : ℝ => chartChristoffel (I := I) (B.family.metric r) β i j k
                (Sc x)) J t)
              * chartCoord (E := E) i (deriv Sc x) * chartCoord (E := E) j (Yc x))
          • DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k := by
    rw [hJ, trivToE_connectionVariation (I := I) (M := M) B hsu hwindow β t ht (c.X x t) (V x t),
      hXcoord]
  have hRt : trivToE (I := I) β β
        (riemannVector B.family t β (c.velocity J x t) (c.X x t) (V x t))
      = DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) β
          (chartRiemannCLM (I := I) (B.family.metric t) β
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) β).symm (Uc x))
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) β).symm (deriv Sc x))
            ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) β).symm (Yc x))) := by
    have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (LeviCivita (I := I) (B.family.metric t)) ∞ :=
      leviCivita_contMDiffCovariantDerivativeLocally (I := I) (B.family.metric t)
    have hvec : riemannVector B.family t β (c.velocity J x t) (c.X x t) (V x t)
        = riemannOp (LeviCivita (I := I) (B.family.metric t)) β
            (c.velocity J x t) (c.X x t) (V x t) := by
      change connectionRiemannCurvatureField (B.family.connection t)
        (tangentConstAt (I := I) β (c.velocity J x t))
        (tangentConstAt (I := I) β (c.X x t))
        (tangentConstAt (I := I) β (V x t)) β = _
      exact connectionRiemannCurvatureField_tangentConst_eq_riemannOp (I := I)
        (cov := LeviCivita (I := I) (B.family.metric t)) hcov β (c.velocity J x t) (c.X x t) (V x t)
    have hbasis := DifferentialGeometry.Geometry.Connection.chartRiemannBasisIdentity_LeviCivita
      (I := I) (B.family.metric t) β
    have hclm := DifferentialGeometry.Geometry.Connection.riemannOp_eq_chartRiemannCLM_apply_of_basis_identity
      (I := I) (B.family.metric t) β hbasis
    have hvelT : c.velocity J x t = (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) β).symm (Uc x) := by
      apply (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) β).injective
      rw [ContinuousLinearEquiv.apply_symm_apply, DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply, ← trivToE_basepoint (I := I) β]
      exact hvelCoord
    have hXT : c.X x t = (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) β).symm (deriv Sc x) := by
      apply (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) β).injective
      rw [ContinuousLinearEquiv.apply_symm_apply, DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply, ← trivToE_basepoint (I := I) β]
      exact hXcoord
    have hVT : V x t = (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) β).symm (Yc x) := by
      apply (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) β).injective
      rw [ContinuousLinearEquiv.apply_symm_apply, DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply, ← trivToE_basepoint (I := I) β]
    rw [hvec, hclm, hvelT, hXT, hVT, trivToE_basepoint,
      DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply]
  have hRint' : Sc x ∈ interior (extChartAt I β).target := hRint
  have hcurv := DifferentialGeometry.Geometry.Riemannian.Variation.CurvatureCoordinateExpansion.curvPart_eq_chartRiemannCLM
    (I := I) (B.family.metric t) β (Uc x) (deriv Sc x) (Yc x)
  have hfd1 := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartChristoffelContraction_fderiv_apply
    (I := I) (B.family.metric t) β (Sc x) hRint' (deriv Sc x) (Yc x) (Uc x)
  have hkey : trivToE (I := I) β β (c.Dt B.family.metric J (c.Dx B.family.metric V) x t)
      = trivToE (I := I) β β (c.Dx B.family.metric (c.Dt B.family.metric J V) x t)
        + trivToE (I := I) β β (riemannVector B.family t β (c.velocity J x t) (c.X x t) (V x t))
        + trivToE (I := I) β β (connectionVariation B.family J t β (c.X x t) (V x t)) := by
    rw [hLt, hLx, hRt, hRv, ← hcurv, hA2'def, hW2'def, hfd1]
    rw [ChartChristoffel.contraction_add_right, ChartChristoffel.contraction_add_right]
    simp only [hW1eq, hW2eq, hUceq, hYceq, hSceq, hΦself, chartChristoffelContraction_def,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, add_smul, sub_smul]
    abel_nf
  have hbase_β : β ∈ (trivializationAt E (TangentSpace I) β).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) β
  have hfinal : trivToE (I := I) β β
        (c.Dt B.family.metric J (c.Dx B.family.metric V) x t -
          c.Dx B.family.metric (c.Dt B.family.metric J V) x t)
      = trivToE (I := I) β β
          (riemannVector B.family t β (c.velocity J x t) (c.X x t) (V x t) +
            connectionVariation B.family J t β (c.X x t) (V x t)) := by
    rw [map_sub, map_add, hkey]
    abel
  have hgoal := congrArg ((trivializationAt E (TangentSpace I) β).symmL ℝ β) hfinal
  simp only [map_sub, map_add,
    (trivializationAt E (TangentSpace I) β).symmL_continuousLinearMapAt (R := ℝ) hbase_β] at hgoal
  exact hgoal

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
theorem pullback_torsion_free {D : RealTimeInterval} {a b s u : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    c.Dt B.family.metric (Icc s u) c.X x t =
      c.Dx B.family.metric (c.velocity (Icc s u)) x t := by
  have _ := hwindow
  classical
  set J : Set ℝ := Icc s u with hJ
  have htJ : t ∈ J := ht
  have huniqJ : UniqueDiffOn ℝ J := by rw [hJ]; exact uniqueDiffOn_Icc hsu
  have huniqJt : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]; exact huniqJ t htJ
  have hcl : t ∈ closure (interior J) := by
    change t ∈ closure (interior (Icc s u))
    rw [closure_interior_Icc (ne_of_lt hsu)]; exact ht
  set β : M := c.lift x t with hβ
  set Φ : ℝ × ℝ → E := fun p => extChartAt I β (c.lift p.1 p.2) with hΦdef
  have hΦsmooth : ∀ᶠ z in 𝓝[univ ×ˢ J] (x, t), ContDiffWithinAt ℝ 2 Φ (univ ×ˢ J) z := by
    have hct : ContinuousWithinAt (fun p : ℝ × ℝ => c.lift p.1 p.2) (univ ×ˢ J) (x, t) :=
      (hc (x, t) ⟨mem_univ x, htJ⟩).continuousWithinAt
    have hsrc : (fun p : ℝ × ℝ => c.lift p.1 p.2) ⁻¹' (chartAt H β).source
        ∈ 𝓝[univ ×ˢ J] (x, t) :=
      hct.preimage_mem_nhdsWithin ((chartAt H β).open_source.mem_nhds (mem_chart_source H β))
    filter_upwards [hsrc, self_mem_nhdsWithin] with z hz hzS
    have hz2 : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I ∞
        (fun p : ℝ × ℝ => c.lift p.1 p.2) (univ ×ˢ J) z := hc z hzS
    have hext : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I β) (c.lift z.1 z.2) :=
      contMDiffAt_extChartAt' (I := I) (n := ∞) (x := β) hz
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp
      ((hext.comp_contMDiffWithinAt z hz2).of_le (by decide))
  have hclairaut := DifferentialGeometry.Geometry.Riemannian.Variation.mixed_partialFderivWithin_comm
    Φ x t huniqJ htJ hcl hΦsmooth
  have hrepL : (fun r : ℝ => chartRepAtBase (I := I) β (fun s : ℝ => c.lift x s)
        (fun s : ℝ => c.X x s) r)
      =ᶠ[𝓝[J] t] (fun r : ℝ => fderiv ℝ (fun u : ℝ => Φ (u, r)) x 1) := by
    have hslice : ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ (fun r : ℝ => c.lift x r) J t :=
      c.time_slice_contMDiffWithinAt (I := I) J hc x t htJ
    have hsr : (fun r : ℝ => c.lift x r) ⁻¹' (chartAt H β).source ∈ 𝓝[J] t :=
      hslice.continuousWithinAt.preimage_mem_nhdsWithin
        ((chartAt H β).open_source.mem_nhds (mem_chart_source H β))
    filter_upwards [hsr, self_mem_nhdsWithin] with r hr hrJ
    have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => c.lift u r) x :=
      (contMDiffWithinAt_univ.mp
        (c.space_slice_contMDiffWithinAt (I := I) J hc x r hrJ)).mdifferentiableAt (by norm_num)
    have hb := chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => c.lift u r) hγ β hr
    simpa only [chartRepAtBase_apply, CurveMap.X, hΦdef, Function.comp_def] using hb
  have hrepR : (fun u : ℝ => chartRepAtBase (I := I) β (fun s : ℝ => c.lift s t)
        (fun s : ℝ => c.velocity J s t) u)
      =ᶠ[𝓝 x] (fun u : ℝ => fderivWithin ℝ (fun v : ℝ => Φ (u, v)) J t 1) := by
    have hcont : ContinuousAt (fun u : ℝ => c.lift u t) x :=
      (contMDiffWithinAt_univ.mp
        (c.space_slice_contMDiffWithinAt (I := I) J hc x t htJ)).continuousAt
    have hsr : (fun u : ℝ => c.lift u t) ⁻¹' (chartAt H β).source ∈ 𝓝 x :=
      hcont.preimage_mem_nhds ((chartAt H β).open_source.mem_nhds (mem_chart_source H β))
    filter_upwards [hsr] with u hu
    have hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun v : ℝ => c.lift u v) J t :=
      (c.time_slice_contMDiffWithinAt (I := I) J hc u t htJ).mdifferentiableWithinAt (by norm_num)
    have hγc : ContinuousWithinAt (fun v : ℝ => c.lift u v) J t :=
      (c.time_slice_contMDiffWithinAt (I := I) J hc u t htJ).continuousWithinAt
    have hb := chartCoord_mfderivWithin_along_curve_eq_fderivWithin
      (I := I) (M := M) (γ := fun v : ℝ => c.lift u v) hγ hγc huniqJt hu
    simpa only [chartRepAtBase_apply, CurveMap.velocity, hΦdef, Function.comp_def] using hb
  have hLHS : c.Dt B.family.metric J c.X x t
      = (trivializationAt E (TangentSpace I) β).symmL ℝ β
          (derivWithin (fun v : ℝ => fderiv ℝ (fun u : ℝ => Φ (u, v)) x 1) J t
            + chartChristoffelContraction (I := I) (B.family.metric t) β
                (derivWithin (fun v : ℝ => Φ (x, v)) J t)
                (fderiv ℝ (fun u : ℝ => Φ (u, t)) x 1)
                (Φ (x, t))) := by
    rw [Dt_eq_symmL_chart]
    congr 1
    have hpt : chartRepAtBase (I := I) β (fun s : ℝ => c.lift x s) (fun s : ℝ => c.X x s) t
        = fderiv ℝ (fun u : ℝ => Φ (u, t)) x 1 := hrepL.self_of_nhdsWithin htJ
    have hderL : derivWithin (chartRepAtBase (I := I) β (fun s : ℝ => c.lift x s)
          (fun s : ℝ => c.X x s)) J t
        = derivWithin (fun r : ℝ => fderiv ℝ (fun u : ℝ => Φ (u, r)) x 1) J t :=
      Filter.EventuallyEq.derivWithin_eq hrepL hpt
    have hcurveL : chartCurve (I := I) β (fun s : ℝ => c.lift x s) = fun v : ℝ => Φ (x, v) := rfl
    rw [hderL, hpt, hcurveL]
  have hRHS : c.Dx B.family.metric (c.velocity J) x t
      = (trivializationAt E (TangentSpace I) β).symmL ℝ β
          (deriv (fun u : ℝ => fderivWithin ℝ (fun v : ℝ => Φ (u, v)) J t 1) x
            + chartChristoffelContraction (I := I) (B.family.metric t) β
                (deriv (fun u : ℝ => Φ (u, t)) x)
                (fderivWithin ℝ (fun v : ℝ => Φ (x, v)) J t 1)
                (Φ (x, t))) := by
    change (trivializationAt E (TangentSpace I) β).symmL ℝ β
        (chartCovDerivAlong (I := I) (B.family.metric t) β (fun u : ℝ => c.lift u t)
          (chartRepAtBase (I := I) β (fun s : ℝ => c.lift s t)
            (fun s : ℝ => c.velocity J s t)) x) = _
    rw [chartCovDerivAlong_def]
    congr 1
    have hpt : chartRepAtBase (I := I) β (fun s : ℝ => c.lift s t)
        (fun s : ℝ => c.velocity J s t) x
        = fderivWithin ℝ (fun v : ℝ => Φ (x, v)) J t 1 := hrepR.self_of_nhds
    have hderR : deriv (chartRepAtBase (I := I) β (fun s : ℝ => c.lift s t)
          (fun s : ℝ => c.velocity J s t)) x
        = deriv (fun u : ℝ => fderivWithin ℝ (fun v : ℝ => Φ (u, v)) J t 1) x :=
      Filter.EventuallyEq.deriv_eq hrepR
    have hcurveR : chartCurve (I := I) β (fun s : ℝ => c.lift s t) = fun u : ℝ => Φ (u, t) := rfl
    rw [hderR, hpt, hcurveR]
  have hAB : (derivWithin (fun v : ℝ => fderiv ℝ (fun u : ℝ => Φ (u, v)) x 1) J t
        + chartChristoffelContraction (I := I) (B.family.metric t) β
            (derivWithin (fun v : ℝ => Φ (x, v)) J t)
            (fderiv ℝ (fun u : ℝ => Φ (u, t)) x 1)
            (Φ (x, t)))
      = (deriv (fun u : ℝ => fderivWithin ℝ (fun v : ℝ => Φ (u, v)) J t 1) x
        + chartChristoffelContraction (I := I) (B.family.metric t) β
            (deriv (fun u : ℝ => Φ (u, t)) x)
            (fderivWithin ℝ (fun v : ℝ => Φ (x, v)) J t 1)
            (Φ (x, t))) := by
    rw [hclairaut]
    congr 1
    rw [show derivWithin (fun v : ℝ => Φ (x, v)) J t
        = fderivWithin ℝ (fun v : ℝ => Φ (x, v)) J t 1 from rfl,
      show deriv (fun u : ℝ => Φ (u, t)) x
        = fderiv ℝ (fun u : ℝ => Φ (u, t)) x 1 from rfl,
      chartChristoffelContraction_symm (I := I) (B.family.metric t) β
        (fderivWithin ℝ (fun v : ℝ => Φ (x, v)) J t 1)
        (fderiv ℝ (fun u : ℝ => Φ (u, t)) x 1) (Φ (x, t))]
  rw [hLHS, hRHS, hAB]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
theorem CurveMap.Dt_eq_covDerivAlong_of_mem_Ioo (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) (V : c.Field (I := I))
    {s u x t : ℝ} (ht : t ∈ Ioo s u) :
    c.Dt g (Icc s u) V x t = covDerivAlong (g t) (c.lift x) (V x) t :=
  CurveMap.Dt_eq_covDerivAlong c g (Icc s u) V x t (Icc_mem_nhds ht.1 ht.2)

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] hBoundary in
private theorem contDiffWithinAt_deriv_fst_strip {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    {F : ℝ × ℝ → G} {z : ℝ × ℝ} (hz : z ∈ (univ : Set ℝ) ×ˢ J)
    (hF : ∀ᶠ w in 𝓝[((univ : Set ℝ) ×ˢ J)] z,
      ContDiffWithinAt ℝ ∞ F ((univ : Set ℝ) ×ˢ J) w) :
    ContDiffWithinAt ℝ ∞ (fun q : ℝ × ℝ => deriv (fun u : ℝ => F (u, q.2)) q.1)
      ((univ : Set ℝ) ×ˢ J) z := by
  have hWon : UniqueDiffOn ℝ ((univ : Set ℝ) ×ˢ J) := UniqueDiffOn.prod uniqueDiffOn_univ hJ
  have hzat : ContDiffWithinAt ℝ ∞ F ((univ : Set ℝ) ×ˢ J) z := hF.self_of_nhdsWithin hz
  set v : ℝ × ℝ := (1, 0) with hv
  have hk : ContDiffWithinAt ℝ ∞ (fun _ : ℝ × ℝ => v) ((univ : Set ℝ) ×ˢ J) z :=
    contDiffWithinAt_const
  have hfd : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × ℝ => fderivWithin ℝ F ((univ : Set ℝ) ×ˢ J) q v)
      ((univ : Set ℝ) ×ˢ J) z :=
    ContDiffWithinAt.fderivWithin_right_apply (𝕜 := ℝ) (f := F)
      (k := fun _ => v) (s := (univ : Set ℝ) ×ˢ J) (x₀ := z) hzat hk hWon
      (by simp) hz
  have hkey (q : ℝ × ℝ) (hqF : ContDiffWithinAt ℝ ∞ F ((univ : Set ℝ) ×ˢ J) q)
      (hq : q ∈ (univ : Set ℝ) ×ˢ J) :
      deriv (fun u : ℝ => F (u, q.2)) q.1
        = fderivWithin ℝ F ((univ : Set ℝ) ×ˢ J) q v := by
    have hdiff : DifferentiableWithinAt ℝ F ((univ : Set ℝ) ×ˢ J) q :=
      hqF.differentiableWithinAt (by simp)
    have hFW := hdiff.hasFDerivWithinAt
    have hgin : HasFDerivWithinAt (fun u : ℝ => ((u, q.2) : ℝ × ℝ))
        (ContinuousLinearMap.inl ℝ ℝ ℝ) univ q.1 :=
      ((hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)).hasFDerivWithinAt
    have hmap : MapsTo (fun u : ℝ => ((u, q.2) : ℝ × ℝ)) univ ((univ : Set ℝ) ×ˢ J) :=
      fun u _ => ⟨mem_univ u, hq.2⟩
    have hcomp := hFW.comp q.1 hgin hmap
    have hderivAt : HasFDerivAt (fun u : ℝ => F (u, q.2))
        ((fderivWithin ℝ F ((univ : Set ℝ) ×ˢ J) q).comp (ContinuousLinearMap.inl ℝ ℝ ℝ))
        q.1 := hcomp.hasFDerivAt (by simp)
    calc deriv (fun u : ℝ => F (u, q.2)) q.1
        = (fderiv ℝ (fun u : ℝ => F (u, q.2)) q.1) 1 := rfl
      _ = (((fderivWithin ℝ F ((univ : Set ℝ) ×ˢ J) q).comp
            (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1) := by rw [hderivAt.fderiv]
      _ = fderivWithin ℝ F ((univ : Set ℝ) ×ˢ J) q v := by
            rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  refine hfd.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hF, self_mem_nhdsWithin] with q hqF hq
    exact hkey q hqF hq
  · exact hkey z hzat hz

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
theorem contDiffWithinAt_chartChristoffelOnE_comp
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {J : Set ℝ} (hJreg : J ⊆ D.regular) (hJun : UniqueDiffOn ℝ J)
    {β : M} {Φ : ℝ × ℝ → E} {z : ℝ × ℝ} (hz : z ∈ (univ : Set ℝ) ×ˢ J)
    (hΦ : ContDiffWithinAt ℝ ∞ Φ ((univ : Set ℝ) ×ˢ J) z)
    (hΦint : Φ z ∈ interior (extChartAt I β).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffWithinAt ℝ ∞
      (fun q : ℝ × ℝ => chartChristoffel (I := I) (g q.2) β i j k (Φ q))
      ((univ : Set ℝ) ×ˢ J) z := by
  have hWc : ((univ : Set ℝ) ×ˢ J) ∈ 𝓝[((univ : Set ℝ) ×ˢ J)] z := self_mem_nhdsWithin
  set Uset : Set (ℝ × ℝ) := ((univ : Set ℝ) ×ˢ J) ∩ Φ ⁻¹' interior (extChartAt I β).target
    with hUset
  have hcw : ContinuousWithinAt Φ ((univ : Set ℝ) ×ˢ J) z := hΦ.continuousWithinAt
  have hV : Φ ⁻¹' (interior (extChartAt I β).target : Set E) ∈ 𝓝[((univ : Set ℝ) ×ˢ J)] z :=
    hcw.preimage_mem_nhdsWithin (isOpen_interior.mem_nhds hΦint)
  have hcont : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => chartChristoffel (I := I) (g p.1) β i j k p.2)
      (J ×ˢ interior (extChartAt I β).target) (z.2, Φ z) :=
    (MetricFamilySmoothOn.chartChristoffelOnE_contDiffOn (I := I) (D := D)
      (g_fam := g) hG hJreg hJun β i j k).contDiffWithinAt ⟨hz.2, hΦint⟩
  have hψ : ContDiffWithinAt ℝ ∞ (fun q : ℝ × ℝ => (q.2, Φ q)) Uset z :=
    (contDiffWithinAt_snd (𝕜 := ℝ) (s := Uset) (p := z) :
      ContDiffWithinAt ℝ ∞ (fun q : ℝ × ℝ => q.2) Uset z).prodMk
      (hΦ.mono (t := Uset) (by rw [hUset]; exact Set.inter_subset_left))
  have hmaps : MapsTo (fun q : ℝ × ℝ => (q.2, Φ q)) Uset
      (J ×ˢ interior (extChartAt I β).target) :=
    fun q hq => ⟨hq.1.2, hq.2⟩
  have hcomp := hcont.comp z hψ hmaps
  refine hcomp.mono_of_mem_nhdsWithin ?_
  rw [hUset]
  simpa only [Set.inter_comm] using Filter.inter_mem hV hWc

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
theorem contDiffWithinAt_chartChristoffelContraction
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {J : Set ℝ} (hJreg : J ⊆ D.regular) (hJun : UniqueDiffOn ℝ J)
    {β : M} {P Q Φ : ℝ × ℝ → E} {z : ℝ × ℝ} (hz : z ∈ (univ : Set ℝ) ×ˢ J)
    (hP : ContDiffWithinAt ℝ ∞ P ((univ : Set ℝ) ×ˢ J) z)
    (hQ : ContDiffWithinAt ℝ ∞ Q ((univ : Set ℝ) ×ˢ J) z)
    (hΦ : ContDiffWithinAt ℝ ∞ Φ ((univ : Set ℝ) ×ˢ J) z)
    (hΦint : Φ z ∈ interior (extChartAt I β).target) :
    ContDiffWithinAt ℝ ∞
      (fun q : ℝ × ℝ => chartChristoffelContraction (I := I) (g q.2) β (P q) (Q q) (Φ q))
      ((univ : Set ℝ) ×ˢ J) z := by
  have hsum : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × ℝ => ∑ k : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) (g q.2) β i j k (Φ q) *
            chartCoord (E := E) i (P q) * chartCoord (E := E) j (Q q)) •
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)
      ((univ : Set ℝ) ×ˢ J) z := by
    refine ContDiffWithinAt.sum (s := Finset.univ) (fun k _ => ?_)
    refine ContDiffWithinAt.smul_const ?_ (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)
    refine ContDiffWithinAt.sum (s := Finset.univ) (fun i _ => ?_)
    refine ContDiffWithinAt.sum (s := Finset.univ) (fun j _ => ?_)
    have hPi : ContDiffWithinAt ℝ ∞ (fun q : ℝ × ℝ => chartCoord (E := E) i (P q))
        ((univ : Set ℝ) ×ˢ J) z := by
      have h1 : ContDiffWithinAt ℝ ∞
          (fun q : ℝ × ℝ =>
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM E i (P q))
          ((univ : Set ℝ) ×ˢ J) z :=
        hP.continuousLinearMap_comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM E i)
      refine h1.congr (fun q _ => ?_) ?_
      · simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM_apply,
          chartCoord_def, Module.Basis.equivFun_apply]
      · simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM_apply,
          chartCoord_def, Module.Basis.equivFun_apply]
    have hQj : ContDiffWithinAt ℝ ∞ (fun q : ℝ × ℝ => chartCoord (E := E) j (Q q))
        ((univ : Set ℝ) ×ˢ J) z := by
      have h1 : ContDiffWithinAt ℝ ∞
          (fun q : ℝ × ℝ =>
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM E j (Q q))
          ((univ : Set ℝ) ×ˢ J) z :=
        hQ.continuousLinearMap_comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM E j)
      refine h1.congr (fun q _ => ?_) ?_
      · simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM_apply,
          chartCoord_def, Module.Basis.equivFun_apply]
      · simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM_apply,
          chartCoord_def, Module.Basis.equivFun_apply]
    exact (((contDiffWithinAt_chartChristoffelOnE_comp (I := I) (D := D) (g := g) hG
      hJreg hJun hz hΦ hΦint i j k).mul
        hPi).mul hQj)
  refine hsum.congr (fun q _ => ?_) ?_
  · exact (chartChristoffelContraction_def (I := I) (g q.2) β (P q) (Q q) (Φ q)).symm
  · exact (chartChristoffelContraction_def (I := I) (g z.2) β (P z) (Q z) (Φ z)).symm

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem chartRep_Dx_contDiffWithinAt {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {J : Set ℝ} (hJreg : J ⊆ D.regular) (hJun : UniqueDiffOn ℝ J)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) J)
    (V : c.Field (I := I)) (hV : V.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × ℝ => trivToE (I := I) (c.lift x t) (c.lift p.1 p.2)
        (c.Dx g V p.1 p.2)) ((univ : Set ℝ) ×ˢ J) (x, t) := by
  classical
  let Z : ℝ × ℝ → E := fun q => trivToE (I := I) (c.lift x t) (c.lift q.1 q.2) (V q.1 q.2)
  let Φ : ℝ × ℝ → E := fun q => extChartAt I (c.lift x t) (c.lift q.1 q.2)
  have hz : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hZev : ∀ᶠ w in 𝓝[((univ : Set ℝ) ×ˢ J)] (x, t),
      ContDiffWithinAt ℝ ∞ Z ((univ : Set ℝ) ×ˢ J) w :=
    chartRep_field_contDiffWithinAt (I := I) (M := M) c J hc V hV x t ht
  have hΦev : ∀ᶠ w in 𝓝[((univ : Set ℝ) ×ˢ J)] (x, t),
      ContDiffWithinAt ℝ ∞ Φ ((univ : Set ℝ) ×ˢ J) w := by
    have hcont : ContinuousWithinAt (fun p : ℝ × ℝ => c.lift p.1 p.2)
        ((univ : Set ℝ) ×ˢ J) (x, t) :=
      (hc (x, t) ⟨mem_univ x, ht⟩).continuousWithinAt
    have hsrc : (fun p : ℝ × ℝ => c.lift p.1 p.2) ⁻¹' (chartAt H (c.lift x t)).source
        ∈ 𝓝[((univ : Set ℝ) ×ˢ J)] (x, t) :=
      hcont.preimage_mem_nhdsWithin
        ((chartAt H (c.lift x t)).open_source.mem_nhds (mem_chart_source H (c.lift x t)))
    filter_upwards [hsrc, self_mem_nhdsWithin] with q hqS hqW
    have hq2 : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun p : ℝ × ℝ => c.lift p.1 p.2)
        ((univ : Set ℝ) ×ˢ J) q := hc q hqW
    have hext : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (c.lift x t)) (c.lift q.1 q.2) :=
      contMDiffAt_extChartAt' (I := I) (n := ∞) (x := c.lift x t) hqS
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp (hext.comp_contMDiffWithinAt q hq2)
  have hdZ : ContDiffWithinAt ℝ ∞ (fun q : ℝ × ℝ => deriv (fun u : ℝ => Z (u, q.2)) q.1)
      ((univ : Set ℝ) ×ˢ J) (x, t) :=
    contDiffWithinAt_deriv_fst_strip hJun hz hZev
  have hdΦ : ContDiffWithinAt ℝ ∞ (fun q : ℝ × ℝ => deriv (fun u : ℝ => Φ (u, q.2)) q.1)
      ((univ : Set ℝ) ×ˢ J) (x, t) :=
    contDiffWithinAt_deriv_fst_strip hJun hz hΦev
  have hZat : ContDiffWithinAt ℝ ∞ Z ((univ : Set ℝ) ×ˢ J) (x, t) := hZev.self_of_nhdsWithin hz
  have hΦat : ContDiffWithinAt ℝ ∞ Φ ((univ : Set ℝ) ×ˢ J) (x, t) := hΦev.self_of_nhdsWithin hz
  have hΦint : Φ (x, t) ∈ interior (extChartAt I (c.lift x t)).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) (c.lift x t)
      ((extChartAt I (c.lift x t)).map_source (mem_extChartAt_source (I := I) (c.lift x t)))
  have hR : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × ℝ => deriv (fun u : ℝ => Z (u, q.2)) q.1 +
        chartChristoffelContraction (I := I) (g q.2) (c.lift x t)
          (deriv (fun u : ℝ => Φ (u, q.2)) q.1) (Z q) (Φ q))
      ((univ : Set ℝ) ×ˢ J) (x, t) :=
    hdZ.add (contDiffWithinAt_chartChristoffelContraction (I := I) (D := D) (g := g) hG
      hJreg hJun hz hdΦ hZat hΦat hΦint)
  have hev : (fun p : ℝ × ℝ => trivToE (I := I) (c.lift x t) (c.lift p.1 p.2)
        (c.Dx g V p.1 p.2))
      =ᶠ[𝓝[((univ : Set ℝ) ×ˢ J)] (x, t)]
      (fun q : ℝ × ℝ => deriv (fun u : ℝ => Z (u, q.2)) q.1 +
        chartChristoffelContraction (I := I) (g q.2) (c.lift x t)
          (deriv (fun u : ℝ => Φ (u, q.2)) q.1) (Z q) (Φ q)) := by
    have hgood : (fun q : ℝ × ℝ => c.lift q.1 q.2) ⁻¹'
        (chartLeviCivitaGoodSet (I := I) (c.lift x t)) ∈ 𝓝[((univ : Set ℝ) ×ˢ J)] (x, t) :=
      (hc (x, t) ⟨mem_univ x, ht⟩).continuousWithinAt.preimage_mem_nhdsWithin
        ((chartLeviCivitaGoodSet_isOpen (I := I) (c.lift x t)).mem_nhds
          (self_mem_chartLeviCivitaGoodSet (I := I) (c.lift x t)))
    filter_upwards [hgood, self_mem_nhdsWithin] with q hqg hqW
    have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y : ℝ => c.lift y q.2) q.1 :=
      (contMDiffWithinAt_univ.mp
        (c.space_slice_contMDiffWithinAt (I := I) J hc q.1 q.2 hqW.2)).mdifferentiableAt
        (by norm_num)
    have hVtot : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E))
        (fun y : ℝ => (⟨c.lift y q.2, V y q.2⟩ : TotalSpace E (TangentSpace I))) univ q.1 :=
      (Field.space_slice_contMDiffWithinAt (I := I) c J V hV q.1 q.2 hqW.2).mdifferentiableWithinAt
        (by norm_num)
    rw [trivToE_Dx_eq_chart (I := I) (M := M) g c V (c.lift x t) q.1 q.2 hqg hγ hVtot]
    simp only [Z, Φ, chartCurve]
    rfl
  exact hR.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin hz)

namespace CurveMap

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem Field.smoothOn_Dx {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (hJun : UniqueDiffOn ℝ J)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) J)
    (V : c.Field (I := I)) (hV : V.SmoothOn (I := I) J) :
    CurveMap.Field.SmoothOn (I := I) (c.Dx g V) J := by
  intro p hp
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨hc p hp, ?_⟩
  have hcd := chartRep_Dx_contDiffWithinAt (I := I) (M := M) (D := D) (g := g) hG hJ hJun
    c hc V hV p.1 p.2 hp.2
  have hcd' : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
      (fun q : ℝ × ℝ => trivToE (I := I) (c.lift p.1 p.2) (c.lift q.1 q.2)
        (c.Dx g V q.1 q.2)) ((univ : Set ℝ) ×ˢ J) p :=
    contMDiffWithinAt_iff_contDiffWithinAt.mpr hcd
  have hcont : ContinuousWithinAt (fun q : ℝ × ℝ => c.lift q.1 q.2) ((univ : Set ℝ) ×ˢ J) p :=
    (hc p hp).continuousWithinAt
  have hbase : c.lift p.1 p.2
      ∈ (trivializationAt E (TangentSpace I) (c.lift p.1 p.2)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (c.lift p.1 p.2)
  have hneigh : (fun q : ℝ × ℝ => c.lift q.1 q.2) ⁻¹'
      (trivializationAt E (TangentSpace I) (c.lift p.1 p.2)).baseSet
      ∈ 𝓝[((univ : Set ℝ) ×ˢ J)] p :=
    hcont.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) (c.lift p.1 p.2)).open_baseSet.mem_nhds hbase)
  have hev : (fun q : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (c.lift p.1 p.2)
          (⟨c.lift q.1 q.2, c.Dx g V q.1 q.2⟩ : TangentBundle I M)).2)
      =ᶠ[𝓝[((univ : Set ℝ) ×ˢ J)] p]
      (fun q : ℝ × ℝ => trivToE (I := I) (c.lift p.1 p.2) (c.lift q.1 q.2)
        (c.Dx g V q.1 q.2)) := by
    filter_upwards [hneigh, self_mem_nhdsWithin] with q hqB _
    exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (e := trivializationAt E (TangentSpace I) (c.lift p.1 p.2)) hqB
      (c.Dx g V q.1 q.2)).symm
  exact hcd'.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin hp)

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem Field.smoothOn_curvatureVector {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (hJun : UniqueDiffOn ℝ J)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) :
    CurveMap.Field.SmoothOn (I := I) (c.curvatureVector g) J := by
  have hsp : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.speed g p.1 p.2) ((univ : Set ℝ) ×ˢ J) :=
    Field.smoothOn_speed g hG hJ c hc hi
  have hinv : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (c.speed g p.1 p.2)⁻¹)
      ((univ : Set ℝ) ×ˢ J) := by
    refine hsp.inv ?_
    intro p hp
    exact ne_of_gt (c.speed_pos g hi p.1 p.2 hp.2)
  have hU : CurveMap.Field.SmoothOn (I := I) (c.unitTangent g) J :=
    Field.smoothOn_unitTangent g hG hJ c hc hi
  have hDxU : CurveMap.Field.SmoothOn (I := I) (c.Dx g (c.unitTangent g)) J :=
    Field.smoothOn_Dx g hG hJ hJun c hc (c.unitTangent g) hU
  have hDs : c.curvatureVector g = fun x t => (c.speed g x t)⁻¹ • c.Dx g (c.unitTangent g) x t := rfl
  rw [hDs]
  exact Field.smoothOn_const_smul c hc (fun x t => (c.speed g x t)⁻¹) hinv
    (c.Dx g (c.unitTangent g)) hDxU

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem Field.smoothOn_curvatureSq {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (hJun : UniqueDiffOn ℝ J)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.curvatureSq g p.1 p.2) ((univ : Set ℝ) ×ˢ J) := by
  have hk : CurveMap.Field.SmoothOn (I := I) (c.curvatureVector g) J :=
    Field.smoothOn_curvatureVector g hG hJ hJun c hc hi
  exact Field.smoothOn_inner g hG hJ c hc (c.curvatureVector g) (c.curvatureVector g) hk hk

end CurveMap

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
