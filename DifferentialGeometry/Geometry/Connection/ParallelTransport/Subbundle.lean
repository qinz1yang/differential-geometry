import DifferentialGeometry.Bundle.Frame
import DifferentialGeometry.Bundle.SmoothSubbundle.Basic
import DifferentialGeometry.Geometry.Connection.Subbundle
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Kernel
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.ChainRule
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PrescribedTangentInOpenSet
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Connection

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

attribute [local instance] DifferentialGeometry.seminormedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedSpaceTangentSpace

local instance subbundleTangentT2Space (x : M) : T2Space (TangentSpace I x) :=
  FiberBundle.t2Space E (TangentSpace I) x

local instance subbundleTangentFiberBundle :
    FiberBundle E (TangentSpace I : M → Type _) :=
  TangentSpace.fiberBundle (I := I) (M := M)

local instance subbundleTangentVectorBundle :
    VectorBundle ℝ E (TangentSpace I : M → Type _) :=
  TangentSpace.vectorBundle (I := I) (M := M)

local instance subbundleTangentSmoothVectorBundle :
    ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I := by
  have h : IsManifold I ∞ M := inferInstance
  have : IsManifold I (∞ + 1) M := h
  exact TangentBundle.contMDiffVectorBundle (I := I) (M := M)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem sectionAlongCurve_chartRepAt_differentiableAt
    [I.Boundaryless]
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (s : ∀ y : M, TangentSpace I y) (t : ℝ)
    (hs : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% s) (γ t)) :
    DifferentiableAt ℝ
      (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
        (I := I) γ (fun r => s (γ r)) t) t := by
  classical
  let α : M := γ t
  let f : E → E :=
    chartESectionRepr (I := I) α (fun x => s x) ∘ (extChartAt I α).symm
  let u : ℝ → E :=
    DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ
  have hgood : α ∈ chartLeviCivitaGoodSet (I := I) α :=
    self_mem_chartLeviCivitaGoodSet (I := I) α
  have hf : DifferentiableAt ℝ f (extChartAt I α (γ t)) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hgood
      hs
  have hu : DifferentiableAt ℝ u t := by
    have hchart : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (fun r => extChartAt I α (γ r)) t :=
      (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (γ t))).comp t
        (hγ.contMDiffAt.mdifferentiableAt (by norm_num))
    exact mdifferentiableAt_iff_differentiableAt.mp hchart
  have hcomp : DifferentiableAt ℝ (f ∘ u) t := by
    apply hf.comp t hu
  have hsrc : γ ⁻¹' (extChartAt I α).source ∈ 𝓝 t := by
    apply hγ.continuous.continuousAt.preimage_mem_nhds
    apply (isOpen_extChartAt_source (I := I) α).mem_nhds
    exact mem_extChartAt_source (I := I) α
  have heq : (f ∘ u) =ᶠ[𝓝 t]
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
        (I := I) γ (fun r => s (γ r)) t := by
    filter_upwards [hsrc] with r hr
    simp only [Function.comp_apply, f, u,
      DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve,
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt_apply]
    rw [(extChartAt I α).left_inv hr]
    rfl
  exact hcomp.congr_of_eventuallyEq heq.symm

theorem ContMDiffVectorSubbundle.covariantDerivative_eq_zero_on_of_unit_of_rank_eq_one
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : IsParallelSubmoduleFamily g S.fiber)
    (U : Set M) (hU : IsOpen U)
    (s : ∀ y : M, TangentSpace I y)
    (hs : MDifferentiableOn I (I.prod 𝓘(ℝ, E)) (T% s) U)
    (hs_mem : ∀ y ∈ U, s y ∈ S.fiber y)
    (hs_unit : ∀ y ∈ U, g.inner y (s y) (s y) = 1) :
    ∀ y ∈ U, ∀ v : TangentSpace I y,
      (LeviCivita (I := I) g) s y v = 0 := by
  intro y hy v
  obtain ⟨eta, heta, hetaU, heta0, hetaVel⟩ :=
    Riemannian.Variation.exists_smooth_curve y v U hU hy
  subst y
  have heta2 : ContMDiff 𝓘(ℝ, ℝ) I 2 eta :=
    heta.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have h02 : (0 : ℝ) < 2 := by norm_num
  let V : ∀ t, TangentSpace I (eta t) :=
    Riemannian.Variation.parallelTransportSectionOnIcc
      (I := I) g eta heta2 h02 (s (eta 0))
  have hV_mem : ∀ t ∈ Set.Icc (0 : ℝ) 2, V t ∈ S.fiber (eta t) := by
    intro t ht
    exact hS.parallelTransportSectionOnIcc_mem eta heta2 h02
      (hs_mem (eta 0) (hetaU 0)) ht
  have hV0 : V 0 = s (eta 0) := by
    simp [V]
  have hV_unit : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      g.inner (eta t) (V t) (V t) = 1 := by
    intro t ht
    have hinner := Riemannian.Variation.parallel_transport_preserves_inner_product
      (I := I) g eta le_rfl heta2 V V
      (fun r hr => Riemannian.Variation.parallelTransportSectionOnIcc_differentiableAt
        (I := I) g eta heta2 h02 (s (eta 0)) hr)
      (fun r hr => Riemannian.Variation.parallelTransportSectionOnIcc_differentiableAt
        (I := I) g eta heta2 h02 (s (eta 0)) hr)
      (fun r hr => Riemannian.Variation.parallelTransportSectionOnIcc_covDerivAlong
        (I := I) g eta heta2 h02 (s (eta 0)) hr)
      (fun r hr => Riemannian.Variation.parallelTransportSectionOnIcc_covDerivAlong
        (I := I) g eta heta2 h02 (s (eta 0)) hr) t ht
    simpa [V, hs_unit (eta 0) (hetaU 0)] using hinner
  have hsAlongDiff : DifferentiableAt ℝ
      (Riemannian.CovariantDerivativeAlong.chartRepAt
        (I := I) eta (fun t => s (eta t)) 0) 0 :=
    sectionAlongCurve_chartRepAt_differentiableAt
      (I := I) eta (heta2.of_le (by norm_num)) s 0
      ((hs (eta 0) (hetaU 0)).mdifferentiableAt (hU.mem_nhds (hetaU 0)))
  have hVdiff : DifferentiableAt ℝ
      (Riemannian.CovariantDerivativeAlong.chartRepAt (I := I) eta V 0) 0 :=
    Riemannian.Variation.parallelTransportSectionOnIcc_differentiableAt
      (I := I) g eta heta2 h02 (s (eta 0))
      ⟨le_rfl, by norm_num⟩
  have hinnerDeriv := Riemannian.Variation.inner_deriv_at
    (I := I) (by norm_num : (1 : WithTop ℕ∞) ≤ 2) g eta
    (fun t => s (eta t)) V 0 heta2.contMDiffAt hsAlongDiff hVdiff
  have hinner0 : g.inner (eta 0) (s (eta 0)) (V 0) = 1 := by
    rw [hV0]
    exact hs_unit (eta 0) (hetaU 0)
  have hinnerPositive : ∀ᶠ t in nhds (0 : ℝ),
      0 < g.inner (eta t) (s (eta t)) (V t) := by
    apply hinnerDeriv.continuousAt.preimage_mem_nhds
    rw [hinner0]
    exact Ioi_mem_nhds (by norm_num)
  have hinnerPositiveWithin : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ici 0),
      0 < g.inner (eta t) (s (eta t)) (V t) :=
    hinnerPositive.filter_mono nhdsWithin_le_nhds
  have hltTwo : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ici 0), t < 2 :=
    (show ∀ᶠ t : ℝ in nhds 0, t < 2 from Iio_mem_nhds h02).filter_mono
      nhdsWithin_le_nhds
  have heqWithin : (fun t => s (eta t)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)] V := by
    filter_upwards [hinnerPositiveWithin, hltTwo, self_mem_nhdsWithin]
      with t htpos htlt htge
    have ht : t ∈ Set.Icc (0 : ℝ) 2 := ⟨htge, htlt.le⟩
    have hVunit := hV_unit t ht
    have hsunit := hs_unit (eta t) (hetaU t)
    have hVne : V t ≠ 0 := by
      intro hzero
      rw [hzero] at hVunit
      simp at hVunit
    have hfin : Module.finrank ℝ (S.fiber (eta t)) = 1 := by
      rw [S.finrank_fiber, hSrank]
    have hspan : S.fiber (eta t) = ℝ ∙ V t :=
      eq_span_singleton_of_mem_of_finrank_eq_one hfin
        (hV_mem t ht) hVne
    have hsmem := hs_mem (eta t) (hetaU t)
    rw [hspan, Submodule.mem_span_singleton] at hsmem
    obtain ⟨a, ha⟩ := hsmem
    have haInner : g.inner (eta t) (s (eta t)) (V t) = a := by
      rw [← ha, map_smul, smul_apply, smul_eq_mul, hVunit, mul_one]
    have haPos : 0 < a := by rwa [haInner] at htpos
    have haSq : a * a = 1 := by
      have hscaled : g.inner (eta t) (a • V t) (a • V t) = 1 := by
        simpa only [ha] using hsunit
      simpa only [map_smul, smul_apply, smul_eq_mul, hVunit, mul_one] using hscaled
    have haOne : a = 1 := by nlinarith
    rw [← ha, haOne, one_smul]
  let sRep : ℝ → E := Riemannian.CovariantDerivativeAlong.chartRepAt
    (I := I) eta (fun t => s (eta t)) 0
  let VRep : ℝ → E := Riemannian.CovariantDerivativeAlong.chartRepAt
    (I := I) eta V 0
  have hrepWithin : sRep =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)] VRep := by
    filter_upwards [heqWithin] with t ht
    simp only [sRep, VRep]
    rw [Riemannian.CovariantDerivativeAlong.chartRepAt_apply,
      Riemannian.CovariantDerivativeAlong.chartRepAt_apply, ht]
  have hrep0 : sRep 0 = VRep 0 := by
    simp [sRep, VRep, hV0]
  have hderivEq : deriv sRep 0 = deriv VRep 0 := by
    calc
      deriv sRep 0 = derivWithin sRep (Set.Ici 0) 0 :=
        (hsAlongDiff.derivWithin (uniqueDiffWithinAt_Ici 0)).symm
      _ = derivWithin VRep (Set.Ici 0) 0 :=
        hrepWithin.derivWithin_eq hrep0
      _ = deriv VRep 0 := hVdiff.derivWithin (uniqueDiffWithinAt_Ici 0)
  have hcovEq : Riemannian.CovariantDerivativeAlong.covDerivAlong
      (I := I) g eta (fun t => s (eta t)) 0 =
      Riemannian.CovariantDerivativeAlong.covDerivAlong (I := I) g eta V 0 := by
    rw [Riemannian.CovariantDerivativeAlong.covDerivAlong_def,
      Riemannian.CovariantDerivativeAlong.covDerivAlong_def]
    congr 1
    rw [Riemannian.AlongCurve.chartCovDerivAlong_def,
      Riemannian.AlongCurve.chartCovDerivAlong_def]
    rw [show Riemannian.CovariantDerivativeAlong.chartRepAt
        (I := I) eta (fun t => s (eta t)) 0 = sRep by rfl,
      show Riemannian.CovariantDerivativeAlong.chartRepAt (I := I) eta V 0 = VRep by rfl,
      hderivEq, hrep0]
  have hbridge := Riemannian.CovariantDerivativeAlong.covDerivAlong_eq_leviCivita_of_eventuallyEq
    (I := I) g eta 0 ((heta2.of_le (by norm_num)).contMDiffAt)
    ((hs (eta 0) (hetaU 0)).mdifferentiableAt (hU.mem_nhds (hetaU 0))) (hV := by rfl)
  have hLC :
      (LeviCivita (I := I) g) s (eta 0) v =
        Riemannian.CovariantDerivativeAlong.covDerivAlong
          (I := I) g eta (fun t => s (eta t)) 0 := by
    calc
      (LeviCivita (I := I) g) s (eta 0) v =
          (LeviCivita (I := I) g) s (eta 0)
            (mfderiv 𝓘(ℝ, ℝ) I eta 0 (1 : ℝ)) :=
        congrArg ((LeviCivita (I := I) g) s (eta 0)) hetaVel.symm
      _ = Riemannian.CovariantDerivativeAlong.covDerivAlong
          (I := I) g eta (fun t => s (eta t)) 0 := hbridge.symm
  calc
    (LeviCivita (I := I) g) s (eta 0) v =
        Riemannian.CovariantDerivativeAlong.covDerivAlong
          (I := I) g eta (fun t => s (eta t)) 0 := hLC
    _ = Riemannian.CovariantDerivativeAlong.covDerivAlong (I := I) g eta V 0 := hcovEq
    _ = 0 := Riemannian.Variation.parallelTransportSectionOnIcc_covDerivAlong
      (I := I) g eta heta2 h02 (s (eta 0)) ⟨le_rfl, by norm_num⟩

theorem ContMDiffVectorSubbundle.covariantDerivative_eq_zero_of_unit_of_rank_eq_one
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : IsParallelSubmoduleFamily g S.fiber)
    (U : Set M) (hU : IsOpen U)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hs_mem : ∀ y ∈ U, s y ∈ S.fiber y)
    (hs_unit : ∀ y ∈ U, g.inner y (s y) (s y) = 1) :
    ∀ y ∈ U, ∀ v : TangentSpace I y,
      (LeviCivita (I := I) g) s y v = 0 := by
  exact ContMDiffVectorSubbundle.covariantDerivative_eq_zero_on_of_unit_of_rank_eq_one
    g S hSrank hS U hU s (s.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
    hs_mem hs_unit

private theorem exists_local_unit_section_of_rank_eq_one
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (x : M) :
    ∃ (U : Set M) (s : Cₛ^∞⟮I; E, TangentSpace I⟯),
      IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, s y ∈ S.fiber y) ∧
      (∀ y ∈ U, g.inner y (s y) (s y) = 1) := by
  obtain ⟨U, e, hU, hxU, he⟩ := S.exists_frame x
  let i : Fin S.rank := ⟨0, by omega⟩
  let q : M → ℝ := fun y => g.inner y (e i y) (e i y)
  let u : ∀ y : M, TangentSpace I y := fun y => (Real.sqrt (q y))⁻¹ • e i y
  have he_ne : ∀ y ∈ U, e i y ≠ 0 := by
    intro y hy
    exact LinearIndependent.ne_zero i (he.linearIndependent hy)
  have hq_pos : ∀ y ∈ U, 0 < q y := by
    intro y hy
    exact g.pos y (e i y) (he_ne y hy)
  have hq_smooth : ContMDiffOn I 𝓘(ℝ) ∞ q U := by
    intro y hy
    exact DifferentialGeometry.Geometry.Curvature.CovariantDerivative.metric_inner_contMDiffAt
      (I := I) g
      ((he.contMDiffOn i y hy).contMDiffAt (hU.mem_nhds hy))
      ((he.contMDiffOn i y hy).contMDiffAt (hU.mem_nhds hy)) le_rfl |>.contMDiffWithinAt
  have hu_smooth : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% u) U := by
    apply ContMDiffOn.smul_section
    · intro y hy
      have hsqrt : ContMDiffAt I 𝓘(ℝ) ∞ (fun z => Real.sqrt (q z)) y :=
        (Real.contDiffAt_sqrt (ne_of_gt (hq_pos y hy))).contMDiffAt.comp y
          ((hq_smooth y hy).contMDiffAt (hU.mem_nhds hy))
      exact (hsqrt.inv₀ (ne_of_gt (Real.sqrt_pos.mpr (hq_pos y hy)))).contMDiffWithinAt
    · exact he.contMDiffOn i
  have hu_mem : ∀ y ∈ U, u y ∈ S.fiber y := by
    intro y hy
    exact (S.fiber y).smul_mem _ (he.mem_fiber hy i)
  have hu_unit : ∀ y ∈ U, g.inner y (u y) (u y) = 1 := by
    intro y hy
    simp only [u, map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt (q y))⁻¹ * ((Real.sqrt (q y))⁻¹ * q y) = 1
    have hsqrt_ne : Real.sqrt (q y) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hq_pos y hy))
    have hsqrt_sq : Real.sqrt (q y) * Real.sqrt (q y) = q y := by
      nlinarith [Real.sq_sqrt (le_of_lt (hq_pos y hy))]
    field_simp [hsqrt_ne]
    simpa [pow_two] using hsqrt_sq.symm
  obtain ⟨u', hu'⟩ := exists_contMDiffSection_eqOn_nhd
    (I := I) (F := E) (V := TangentSpace I) (s := fun _ : Unit => u)
    (fun _ => hu_smooth) hU hxU
  rw [eventually_iff_exists_mem] at hu'
  obtain ⟨V, hV, hu'V⟩ := hu'
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp hV
  let s : Cₛ^∞⟮I; E, TangentSpace I⟯ := u' ()
  let N := W ∩ U
  have hNopen : IsOpen N := hWopen.inter hU
  have hxN : x ∈ N := ⟨hxW, hxU⟩
  have hs_eq : ∀ y ∈ N, s y = u y := by
    intro y hy
    exact hu'V y (hWsub hy.1) ()
  have hs_mem : ∀ y ∈ N, s y ∈ S.fiber y := by
    intro y hy
    rw [hs_eq y hy]
    exact hu_mem y hy.2
  have hs_unit : ∀ y ∈ N, g.inner y (s y) (s y) = 1 := by
    intro y hy
    rw [hs_eq y hy]
    exact hu_unit y hy.2
  exact ⟨N, s, hNopen, hxN, hs_mem, hs_unit⟩

theorem ContMDiffVectorSubbundle.exists_local_parallel_unit_section_of_rank_eq_one_of_covariantly_invariant
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : IsCovariantlyInvariantSubmoduleFamily (LeviCivita (I := I) g) S.fiber)
    (x : M) :
    ∃ (U : Set M) (s : Cₛ^∞⟮I; E, TangentSpace I⟯),
      IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, s y ∈ S.fiber y) ∧
      (∀ y ∈ U, g.inner y (s y) (s y) = 1) ∧
      (∀ y ∈ U, ∀ v : TangentSpace I y,
        (LeviCivita (I := I) g) s y v = 0) := by
  obtain ⟨U, s, hUopen, hxU, hs_mem, hs_unit⟩ :=
    exists_local_unit_section_of_rank_eq_one g S hSrank x
  refine ⟨U, s, hUopen, hxU, hs_mem, hs_unit, ?_⟩
  intro y hy v
  have hcov_mem := hS s U hUopen hs_mem y hy v
  have hfin : Module.finrank ℝ (S.fiber y) = 1 := by
    rw [S.finrank_fiber, hSrank]
  have hs_ne : s y ≠ 0 := by
    intro hs0
    have := hs_unit y hy
    rw [hs0] at this
    simp at this
  have hspan : S.fiber y = ℝ ∙ s y :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin (hs_mem y hy) hs_ne
  rw [hspan, Submodule.mem_span_singleton] at hcov_mem
  obtain ⟨c, hc⟩ := hcov_mem
  have hmetric := (LeviCivita_isMetricCompatible (I := I) g).apply
    (s.contMDiff.mdifferentiableAt (by simp))
    (s.contMDiff.mdifferentiableAt (by simp)) v
  have hinner_local : (fun z => g.inner z (s z) (s z)) =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [hUopen.mem_nhds hy] with z hz
    exact hs_unit z hz
  rw [hinner_local.mfderiv_eq, mfderiv_const] at hmetric
  rw [← hc] at hmetric
  have hc0 : c = 0 := by
    rw [map_smul, smul_apply, smul_eq_mul, g.symm y (s y) (c • s y),
      map_smul, smul_apply, smul_eq_mul, hs_unit y hy] at hmetric
    simp at hmetric
    exact add_self_eq_zero.mp hmetric.symm
  rw [← hc, hc0, zero_smul]

theorem ContMDiffVectorSubbundle.exists_local_parallel_unit_section_of_rank_eq_one
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : IsParallelSubmoduleFamily g S.fiber)
    (x : M) :
    ∃ (U : Set M) (s : Cₛ^∞⟮I; E, TangentSpace I⟯),
      IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, s y ∈ S.fiber y) ∧
      (∀ y ∈ U, g.inner y (s y) (s y) = 1) ∧
      (∀ y ∈ U, ∀ v : TangentSpace I y,
        (LeviCivita (I := I) g) s y v = 0) := by
  obtain ⟨U, s, hUopen, hxU, hs_mem, hs_unit⟩ :=
    exists_local_unit_section_of_rank_eq_one g S hSrank x
  exact ⟨U, s, hUopen, hxU, hs_mem, hs_unit,
    ContMDiffVectorSubbundle.covariantDerivative_eq_zero_of_unit_of_rank_eq_one
      (I := I) g S hSrank hS U hUopen s hs_mem hs_unit⟩

theorem ContMDiffVectorSubbundle.isParallelSubmoduleFamily_of_rank_eq_one
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : IsCovariantlyInvariantSubmoduleFamily (LeviCivita (I := I) g) S.fiber) :
    IsParallelSubmoduleFamily g S.fiber := by
  intro γ hγ a b hab
  let δ : ℝ → M := fun r => γ (r + a)
  have hδ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) δ :=
    hγ.comp (contMDiff_id.add contMDiff_const)
  let L : ℝ := b - a
  have hL : 0 < L := sub_pos.mpr hab
  have hpreserves (v : TangentSpace I (δ 0)) (hv : v ∈ S.fiber (δ 0)) :
      parallelTransportLinearEquivOnIcc (I := I) g δ hδ hL v ∈ S.fiber (δ L) := by
    let V : ∀ r, TangentSpace I (δ r) :=
      parallelTransportSectionOnIcc (I := I) g δ hδ hL v
    have hVdiff : ∀ r ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) δ V r) r := by
      intro r hr
      exact parallelTransportSectionOnIcc_differentiableAt
        (I := I) g δ hδ hL v hr
    have hVpar : ∀ r ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g δ V r = 0 := by
      intro r hr
      exact parallelTransportSectionOnIcc_covDerivAlong
        (I := I) g δ hδ hL v hr
    let P : Set.Icc (0 : ℝ) L → Prop := fun r => V r ∈ S.fiber (δ r)
    let _ : PreconnectedSpace (Set.Icc (0 : ℝ) L) :=
      Subtype.preconnectedSpace isPreconnected_Icc
    have hlocal : ∀ r : Set.Icc (0 : ℝ) L,
        ∀ᶠ q in 𝓝 r, (P r ↔ P q) ∧ (P q ↔ P r) := by
      intro r
      obtain ⟨U, s, hU, hrU, hs_mem, hs_unit, hs_par⟩ :=
        ContMDiffVectorSubbundle.exists_local_parallel_unit_section_of_rank_eq_one_of_covariantly_invariant
          (I := I) g S hSrank hS (δ r)
      have hpre : δ ⁻¹' U ∈ 𝓝 (r : ℝ) :=
        (hU.preimage hδ.continuous).mem_nhds hrU
      obtain ⟨l, u, hrlu, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hpre
      have hnhd : ((fun q : Set.Icc (0 : ℝ) L => (q : ℝ)) ⁻¹' Set.Ioo l u) ∈ 𝓝 r :=
        (isOpen_Ioo.preimage continuous_subtype_val).mem_nhds hrlu
      filter_upwards [hnhd] with q hq
      have hsegment : ∀ z ∈ Set.Icc (min (r : ℝ) (q : ℝ)) (max (r : ℝ) (q : ℝ)),
          δ z ∈ U := by
        intro z hz
        apply hlu
        exact ⟨(lt_min hrlu.1 hq.1).trans_le hz.1,
          hz.2.trans_lt (max_lt hrlu.2 hq.2)⟩
      have himp : ∀ (r₀ r₁ : Set.Icc (0 : ℝ) L),
          (∀ z ∈ Set.Icc (min (r₀ : ℝ) (r₁ : ℝ)) (max (r₀ : ℝ) (r₁ : ℝ)),
            δ z ∈ U) → P r₀ → P r₁ := by
        intro r₀ r₁ hseg hr₀
        have hs_ne : s (δ r₀) ≠ 0 := by
          intro hs0
          have := hs_unit (δ r₀) (hseg r₀ ⟨min_le_left _ _, le_max_left _ _⟩)
          rw [hs0] at this
          simp at this
        have hfin : Module.finrank ℝ (S.fiber (δ r₀)) = 1 := by
          rw [S.finrank_fiber, hSrank]
        have hspan : S.fiber (δ r₀) = ℝ ∙ s (δ r₀) :=
          eq_span_singleton_of_mem_of_finrank_eq_one hfin
            (hs_mem (δ r₀) (hseg r₀ ⟨min_le_left _ _, le_max_left _ _⟩)) hs_ne
        change V r₀ ∈ S.fiber (δ r₀) at hr₀
        rw [hspan, Submodule.mem_span_singleton] at hr₀
        obtain ⟨c, hc⟩ := hr₀
        let W : ∀ z, TangentSpace I (δ z) := fun z => c • s (δ z)
        have hWdiff : ∀ z ∈ Set.Icc (min (r₀ : ℝ) (r₁ : ℝ))
            (max (r₀ : ℝ) (r₁ : ℝ)),
            DifferentiableAt ℝ (chartRepAt (I := I) δ W z) z := by
          intro z hz
          rw [show chartRepAt (I := I) δ W z =
            fun y => c • chartRepAt (I := I) δ (fun x => s (δ x)) z y by
              simpa [W] using chartRepAt_smul (I := I) δ c (fun x => s (δ x)) z]
          exact (sectionAlongCurve_chartRepAt_differentiableAt
            (I := I) δ (hδ.of_le (by norm_num)) s z s.mdifferentiableAt).const_smul c
        have hWpar : ∀ z ∈ Set.Icc (min (r₀ : ℝ) (r₁ : ℝ))
            (max (r₀ : ℝ) (r₁ : ℝ)), covDerivAlong (I := I) g δ W z = 0 := by
          intro z hz
          rw [show W = fun y => c • s (δ y) by rfl,
            covDerivAlong_smul (I := I) g δ c (fun y => s (δ y)) z]
          have hbridge := covDerivAlong_eq_leviCivita_of_eventuallyEq
            (I := I) g δ z ((hδ z).of_le (by norm_num))
            (s.contMDiff.mdifferentiableAt (by simp)) (hV := by rfl)
          rw [hbridge, hs_par (δ z) (hseg z hz)
            (mfderiv 𝓘(ℝ, ℝ) I δ z (1 : ℝ))]
          simp
        have hseg_global : Set.Icc (min (r₀ : ℝ) (r₁ : ℝ))
            (max (r₀ : ℝ) (r₁ : ℝ)) ⊆ Set.Icc (0 : ℝ) L := by
          intro z hz
          exact ⟨(le_min r₀.2.1 r₁.2.1).trans hz.1,
            hz.2.trans (max_le r₀.2.2 r₁.2.2)⟩
        have hagree : V r₀ = W r₀ := hc.symm
        have hEq := parallel_transport_unique_of_eq_at_point
          (I := I) g δ le_rfl hδ V W
            (fun z hz => hVdiff z (hseg_global hz)) hWdiff
            (fun z hz => hVpar z (hseg_global hz)) hWpar
            (t₀ := (r₀ : ℝ))
            ⟨min_le_left _ _, le_max_left _ _⟩ hagree
            (r₁ : ℝ) ⟨min_le_right _ _, le_max_right _ _⟩
        change V r₁ ∈ S.fiber (δ r₁)
        rw [hEq]
        exact (S.fiber (δ r₁)).smul_mem c
          (hs_mem (δ r₁)
            (hseg r₁ ⟨min_le_right _ _, le_max_right _ _⟩))
      have hrq : P r → P q := himp r q hsegment
      have hsegment' : ∀ z ∈ Set.Icc (min (q : ℝ) (r : ℝ)) (max (q : ℝ) (r : ℝ)),
          δ z ∈ U := by
        simpa [min_comm, max_comm] using hsegment
      have hqr : P q → P r := himp q r hsegment'
      exact ⟨⟨hrq, hqr⟩, ⟨hqr, hrq⟩⟩
    have hPall : ∀ r q : Set.Icc (0 : ℝ) L, P r ↔ P q := by
      intro r q
      exact PreconnectedSpace.induction₂' (fun x y => P x ↔ P y) hlocal
        ⟨fun _ _ _ => Iff.trans⟩ r q
    have hPzero : P ⟨0, le_rfl, le_of_lt hL⟩ := by
      change V 0 ∈ S.fiber (δ 0)
      change parallelTransportSectionOnIcc (I := I) g δ hδ hL v 0 ∈ S.fiber (δ 0)
      rw [parallelTransportSectionOnIcc_initial (I := I) g δ hδ hL]
      exact hv
    have hPL : P ⟨L, le_of_lt hL, le_rfl⟩ :=
      (hPall ⟨0, le_rfl, le_of_lt hL⟩ ⟨L, le_of_lt hL, le_rfl⟩).mp hPzero
    change V L ∈ S.fiber (δ L) at hPL
    simpa [V, parallelTransportLinearEquivOnIcc_apply] using hPL
  have hshiftMap :
      Submodule.map (parallelTransportLinearEquivOnIcc
        (I := I) g δ hδ hL).toLinearMap (S.fiber (δ 0)) = S.fiber (δ L) := by
    apply Submodule.eq_of_le_of_finrank_le
    · rintro w ⟨v, hv, rfl⟩
      exact hpreserves v hv
    · rw [← (Submodule.equivMapOfInjective
        (parallelTransportLinearEquivOnIcc (I := I) g δ hδ hL).toLinearMap
        (parallelTransportLinearEquivOnIcc (I := I) g δ hδ hL).injective
        (S.fiber (δ 0))).finrank_eq,
        S.finrank_fiber, S.finrank_fiber]
  dsimp only [δ, L] at hshiftMap
  rw [show (0 : ℝ) + a = a by ring, show (b - a) + a = b by ring] at hshiftMap
  unfold parallelTransportLinearEquivBetween
  exact hshiftMap

end DifferentialGeometry.Geometry.Connection
