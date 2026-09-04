import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator


noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

omit [NeZero (Module.finrank ℝ E)] in
private lemma christoffelCorrection_eq_chartChristoffelContraction
    (g : SmoothRiemannianMetric I M) (α x : M) (Y : E) (v : TangentSpace I x) :
    christoffelCorrection (I := I) g α x Y v =
      chartChristoffelContraction (I := I) g α (trivToE (I := I) α x v) Y
        (extChartAt I α x) := by
  classical
  rw [christoffelCorrection_apply, chartChristoffelContraction_def]
  set F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E :=
    fun i j k =>
      (chartChristoffel (I := I) g α i j k (extChartAt I α x) *
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v) i *
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y j) • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k with hF
  have hLHS :
      (∑ i, ∑ j, ∑ k,
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v) i *
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y j *
                chartChristoffel (I := I) g α i j k (extChartAt I α x)) •
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
        = ∑ i, ∑ j, ∑ k, F i j k := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => ?_)))
    rw [hF]; congr 1; ring
  have hRHS :
      (∑ k,
          (∑ i, ∑ j,
              chartChristoffel (I := I) g α i j k (extChartAt I α x) *
                chartCoord (E := E) i (trivToE (I := I) α x v) *
                chartCoord (E := E) j Y) •
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
        = ∑ i, ∑ j, ∑ k, F i j k := by
    have hstep1 :
        (∑ k,
            (∑ i, ∑ j,
                chartChristoffel (I := I) g α i j k (extChartAt I α x) *
                  chartCoord (E := E) i (trivToE (I := I) α x v) *
                  chartCoord (E := E) j Y) •
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
          = ∑ k, ∑ i, ∑ j, F i j k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hF, chartCoord_def, chartCoord_def]
    rw [hstep1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
  rw [hLHS, hRHS]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chartRepAt_restrict_eq_comp
    (γ : ℝ → M) (X : ∀ y : M, TangentSpace I y) (r₀ : ℝ) :
    chartRepAt (I := I) γ (fun r => X (γ r)) r₀ =
      chartESectionRepr (I := I) (γ r₀) X ∘ γ := by
  funext s
  rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma deriv_chartE_repr_comp_curve_eq
    [BoundarylessManifold I M]
    (γ : ℝ → M) (X : ∀ y : M, TangentSpace I y) (r₀ : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hX : MDiffAt (T% X) (γ r₀)) :
    deriv (chartESectionRepr (I := I) (γ r₀) X ∘ γ) r₀ =
      fderiv ℝ (chartESectionRepr (I := I) (γ r₀) X ∘ (extChartAt I (γ r₀)).symm)
          (extChartAt I (γ r₀) (γ r₀))
        (deriv (chartCurve (I := I) (γ r₀) γ) r₀) := by
  classical
  set α : M := γ r₀ with hα_def
  set f : E → E := chartESectionRepr (I := I) α X ∘ (extChartAt I α).symm with hf_def
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  have hgood : α ∈ chartLeviCivitaGoodSet (I := I) α :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := α)
  have hf_diff : DifferentiableAt ℝ f (extChartAt I α (γ r₀)) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hgood hX
  have hu_hd : HasDerivAt u (deriv u r₀) r₀ :=
    ((contDiffAt_chartCurve (I := I) hγ r₀).differentiableAt (by simp)).hasDerivAt
  have hxu : u r₀ = extChartAt I α (γ r₀) := by rw [hu_def, chartCurve_def]
  have hcomp_hd : HasDerivAt (f ∘ u) (fderiv ℝ f (extChartAt I α (γ r₀)) (deriv u r₀)) r₀ := by
    have hf_hd : HasFDerivAt f (fderiv ℝ f (extChartAt I α (γ r₀))) (u r₀) := by
      rw [hxu]; exact hf_diff.hasFDerivAt
    exact hf_hd.comp_hasDerivAt r₀ hu_hd
  have hsrc_nhds : γ ⁻¹' (extChartAt I α).source ∈ 𝓝 r₀ := by
    have hopen : IsOpen (extChartAt I α).source := isOpen_extChartAt_source (I := I) α
    have hmem : γ r₀ ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact mem_chart_source H (γ r₀)
    exact hγ.continuous.continuousAt.preimage_mem_nhds (hopen.mem_nhds hmem)
  have heq : (f ∘ u) =ᶠ[𝓝 r₀] chartESectionRepr (I := I) α X ∘ γ := by
    filter_upwards [hsrc_nhds] with s hs
    have hs' : γ s ∈ (extChartAt I α).source := hs
    simp only [Function.comp_apply, hf_def, hu_def, chartCurve_def]
    rw [PartialEquiv.left_inv (extChartAt I α) hs']
  rw [← heq.deriv_eq]
  exact hcomp_hd.deriv

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_eq_leviCivita_of_eventuallyEq [T2Space M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t)
    {X : Π x : M, TangentSpace I x} {V : ∀ s, TangentSpace I (γ s)}
    (hX : MDiffAt (T% X) (γ t))
    (hV : V =ᶠ[𝓝 t] (fun s => X (γ s))) :
    covDerivAlong (I := I) g γ V t =
      (LeviCivita (I := I) g).toFun X (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) := by
  classical
  set α : M := γ t with hα
  set U : ℝ → E := chartRepAt (I := I) γ V t with hU
  set XE : E → E := chartESectionRepr (I := I) α X ∘ (extChartAt I α).symm with hXE
  have hgood : γ t ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [hα]
    exact self_mem_chartLeviCivitaGoodSet (I := I) α
  have hLC : (LeviCivita (I := I) g).toFun X (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) =
      chartLeviCivita (I := I) g α X (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) := by
    exact LeviCivita_chart_apply (I := I) g α hgood hX
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
  have hLC' : chartLeviCivita (I := I) g α X (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) =
      trivFromE (I := I) α (γ t)
        (fderiv ℝ XE (extChartAt I α (γ t))
            (trivToE (I := I) α (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) +
          christoffelCorrection (I := I) g α (γ t)
            (chartESectionRepr (I := I) α X (γ t))
            (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) := by
    exact chartLeviCivita_apply (I := I) g α X hgood
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
  have hsrcγ : γ t ∈ (chartAt H α).source := by
    rw [hα]
    exact mem_chart_source H (γ t)
  have hvel : trivToE (I := I) α (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) =
      deriv (chartCurve (I := I) α γ) t := by
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
      hγ.mdifferentiableAt (by norm_num)
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) hmd α hsrcγ
    have hderiv : deriv (chartCurve (I := I) α γ) t =
        (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) := by
      have hφ : ContMDiffAt I 𝓘(ℝ, E) 1 (extChartAt I α) (γ t) :=
        contMDiffAt_extChartAt' (n := 1) (x := α) (x' := γ t) hsrcγ
      have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 ((extChartAt I α) ∘ γ) t :=
        hφ.comp t hγ
      have hd : DifferentiableAt ℝ ((extChartAt I α) ∘ γ) t :=
        (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt (by norm_num)
      exact hd.hasDerivAt.deriv
    rw [hderiv]
    exact hbridge
  have hbaseγ : γ t ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hsrcγ
  have hx_int : extChartAt I α (γ t) ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hα]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source (mem_extChartAt_source (I := I) α))
  have hXE_diff : DifferentiableAt ℝ XE (extChartAt I α (γ t)) :=
    (mdifferentiableAt_section_iff_chartE_fderiv (I := I) α X hsrcγ hbaseγ hx_int).mp hX
  have hchartCurve_diff : DifferentiableAt ℝ (chartCurve (I := I) α γ) t := by
    have hφ : ContMDiffAt I 𝓘(ℝ, E) 1 (extChartAt I α) (γ t) :=
      contMDiffAt_extChartAt' (n := 1) (x := α) (x' := γ t) hsrcγ
    have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 ((extChartAt I α) ∘ γ) t :=
      hφ.comp t hγ
    exact (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt (by norm_num)
  have hU_eq : chartRepAt (I := I) γ V t =ᶠ[𝓝 t]
      (fun s => XE (chartCurve (I := I) α γ s)) := by
    have hγcont : ContinuousAt γ t := hγ.continuousAt
    have hsrc : γ ⁻¹' (chartAt H α).source ∈ 𝓝 t :=
      hγcont.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hsrcγ)
    filter_upwards [hV, hsrc] with s hs hs0
    rw [chartRepAt_apply, hXE, hs]
    change (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s) (X (γ s)) =
      chartESectionRepr (I := I) α X ((extChartAt I α).symm (extChartAt I α (γ s)))
    have hsrc_s : γ s ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact hs0
    rw [chartE_section_repr_apply, (extChartAt I α).left_inv hsrc_s]
  have hU_t : U t = chartESectionRepr (I := I) α X (γ t) := by
    rw [hU, chartRepAt_apply, hV.eq_of_nhds]
    rfl
  have hchain : deriv (chartRepAt (I := I) γ V t) t =
      (fderiv ℝ XE (extChartAt I α (γ t)))
        (deriv (chartCurve (I := I) α γ) t) := by
    rw [hU_eq.deriv_eq]
    have hcomp : HasDerivAt (fun s : ℝ => XE (chartCurve (I := I) α γ s))
        ((fderiv ℝ XE (chartCurve (I := I) α γ t))
          (deriv (chartCurve (I := I) α γ) t)) t :=
      hXE_diff.hasFDerivAt.comp_hasDerivAt t hchartCurve_diff.hasDerivAt
    rw [hcomp.deriv]
    rfl
  have hcorr : christoffelCorrection (I := I) g α (γ t)
        (chartESectionRepr (I := I) α X (γ t))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) =
      chartChristoffelContraction (I := I) g α
        (deriv (chartCurve (I := I) α γ) t) (U t)
        (chartCurve (I := I) α γ t) := by
    rw [christoffelCorrection_eq_chartChristoffelContraction (I := I) g α (γ t)
      (chartESectionRepr (I := I) α X (γ t))
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))]
    rw [hvel, hU_t]
    rfl
  have hchartEq : fderiv ℝ XE (extChartAt I α (γ t))
          (trivToE (I := I) α (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) +
        christoffelCorrection (I := I) g α (γ t)
          (chartESectionRepr (I := I) α X (γ t))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) =
      chartCovDerivAlong (I := I) g α γ U t := by
    rw [hvel, hcorr, ← hchain, chartCovDerivAlong_def]
  rw [covDerivAlong_def, hLC, hLC', hchartEq]

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_restrict_eq_leviCivita
    [T2Space M] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (X : ∀ y : M, TangentSpace I y) (r₀ : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hX : MDiffAt (T% X) (γ r₀)) :
    covDerivAlong (I := I) g γ (fun r => X (γ r)) r₀ =
      (LeviCivita (I := I) g) X (γ r₀) ((mfderiv 𝓘(ℝ, ℝ) I γ r₀ : ℝ →L[ℝ] _) (1 : ℝ)) := by
  classical
  set α : M := γ r₀ with hα_def
  set v : TangentSpace I α := (mfderiv 𝓘(ℝ, ℝ) I γ r₀ : ℝ →L[ℝ] _) (1 : ℝ) with hv_def
  have hgood : α ∈ chartLeviCivitaGoodSet (I := I) α :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := α)
  have hsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hvel : trivToE (I := I) α α v = deriv (chartCurve (I := I) α γ) r₀ := by
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := γ) hγ α (t := r₀) hsrc
    rw [trivToE]
    rw [show v = (mfderiv 𝓘(ℝ, ℝ) I γ r₀ : ℝ →L[ℝ] _) (1 : ℝ) from rfl]
    rw [hbridge]
    rw [show (extChartAt I α ∘ γ) = chartCurve (I := I) α γ from rfl]
    exact fderiv_apply_one_eq_deriv
  have hXmd : MDiffAt (T% (fun y => X y)) α := hX
  rw [show (LeviCivita (I := I) g) X (γ r₀) ((mfderiv 𝓘(ℝ, ℝ) I γ r₀ : ℝ →L[ℝ] _) (1 : ℝ))
        = (LeviCivita (I := I) g).toFun X α v from rfl]
  rw [LeviCivita_chart_apply (I := I) g α hgood hXmd v]
  rw [chartLeviCivita_apply (I := I) g α X hgood v]
  rw [covDerivAlong_def, chartCovDerivAlong_def]
  rw [chartRepAt_restrict_eq_comp (I := I) γ X r₀]
  rw [show (trivializationAt E (TangentSpace I) α).symmL ℝ α = trivFromE (I := I) α α from rfl]
  congr 1
  have hchris :
      chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α γ) r₀)
          ((chartESectionRepr (I := I) α X ∘ γ) r₀)
          (chartCurve (I := I) α γ r₀)
        = christoffelCorrection (I := I) g α α
            (chartESectionRepr (I := I) α X α) v := by
    rw [christoffelCorrection_eq_chartChristoffelContraction (I := I) g α α
      (chartESectionRepr (I := I) α X α) v]
    rw [hvel]
    rw [Function.comp_apply, ← hα_def, chartCurve_def, ← hα_def]
  have hderiv :
      deriv (chartESectionRepr (I := I) α X ∘ γ) r₀ =
        fderiv ℝ (chartESectionRepr (I := I) α X ∘ (extChartAt I α).symm)
            (extChartAt I α α) (trivToE (I := I) α α v) := by
    rw [hvel]
    exact deriv_chartE_repr_comp_curve_eq (I := I) γ X r₀ hγ hX
  rw [hderiv, hchris]

end CovariantDerivativeAlong

end Riemannian
end Geometry
end DifferentialGeometry

end
