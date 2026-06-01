import DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBound
import DifferentialGeometry.Geometry.Riemannian.BonnetMyers.LengthBound
import DifferentialGeometry.Geometry.Riemannian.HopfRinow
import DifferentialGeometry.Geometry.Riemannian.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Riemannian.Variation.PerpFrame
import DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Lifts
import DifferentialGeometry.Integral.Connection.ChartBridge.RiemannBasisBracket
import DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnected
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Covering.Basic
import Mathlib.Data.Finite.Defs

/-!
# Bonnet-Myers headline theorems

This file assembles the three top-level conclusions of the Bonnet-Myers
theorem from their supporting children. Under the hypotheses
`Ric ≥ (n-1) K · g` with `K > 0` and `n ≥ 2`:

* `bonnet_myers_diameter_of_ricci_bound` — the metric diameter is at most `π / √K`.
* `bonnet_myers_compactSpace_of_ricci_bound` — the manifold is compact.
* `bonnet_myers_finite_fundamentalGroup_of_ricci_bound` — the fundamental group is finite.

Two short supporting children are also stated here:

* `bonnet_myers_pairwise_edist_le_of_ricci_bound` — the uniform pairwise edist bound.
* The `bm_c_*` compactness sub-leaves
  (`tangent_closedBall_isCompact`, `isCompact_image_closedBall_under_expMap`,
  `isCompact_univ`).
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]

/-- The closed ball of radius `R` in the tangent space `T_p M` is compact,
because `T_p M` is finite-dimensional (it is canonically isomorphic to the
model fibre `E`). Pure composition of Mathlib `FiniteDimensional.proper_real`
and `isCompact_closedBall`. -/
theorem tangent_closedBall_isCompact
    {M : Type*}
    (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (p : M) {R : ℝ} (_hR : 0 ≤ R) :
    IsCompact (Metric.closedBall (0 : TangentSpace I p) R) := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  exact isCompact_closedBall (0 : TangentSpace I p) R

/-- Continuous image of a compact set is compact. Apply `IsCompact.image` to
`tangent_closedBall_isCompact` together with the continuity of `expMap`. -/
theorem isCompact_image_closedBall_under_expMap
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    (p : M) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact ((expMap g p) '' Metric.closedBall (0 : TangentSpace I p) R) := by
  have hcompact : IsCompact (Metric.closedBall (0 : TangentSpace I p) R) :=
    tangent_closedBall_isCompact (E := E) I p hR
  have hcont : Continuous (expMap (I := I) g p) :=
    DifferentialGeometry.Geometry.Riemannian.HopfRinow.bm_c_expMap_continuous_of_geodesic_complete
      g p
  exact hcompact.image hcont

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The uniform pairwise distance bound underlying Bonnet-Myers: for any two
points `x y` on a complete connected Riemannian manifold of dimension `n ≥ 2`
with Ricci curvature bounded below by `(n-1) K` (`K > 0`),
`edist x y ≤ π / √K`.

The hypothesis `hEnorm` is the supplied structural identity that the fibre
extended norm `‖·‖ₑ` equals `ofReal (√ g.inner)` (the Riemannian norm). The
proof composes three ingredients: a distance-realising launch velocity `v`
at `x` whose intrinsic exponential is `y` and whose `g`-norm equals the
intrinsic distance `r`, giving a unit-speed minimising geodesic `γ` of
parameter length `L = r`; the second-variation index-form length bound,
which combines with the Ricci lower bound to give `L ≤ π / √K`; and the
Riemannian-manifold identity `edist = riemannianEDist`. The
`attribute [-instance]` prefix suppresses the `Tensor0SBundle` tangent-norm
instance so every fibre `‖·‖ₑ` reduces to the Riemannian norm. -/
theorem bonnet_myers_pairwise_edist_le_of_ricci_bound
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnorm : ∀ (xb : M) (v : TangentSpace I xb),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner xb v v)))
    (x y : M) :
    edist x y ≤ ENNReal.ofReal (Real.pi / Real.sqrt K) := by
  classical
  haveI hCE : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [IsRiemannianManifold.out (I := I) x y]
  have hne_top : Manifold.riemannianEDist I x y ≠ (⊤ : ℝ≥0∞) :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
      (I := I) x y
  set r : ℝ := (Manifold.riemannianEDist I x y).toReal with hr_def
  have hr_nn : 0 ≤ r := ENNReal.toReal_nonneg
  have hdist_ofReal : Manifold.riemannianEDist I x y = ENNReal.ofReal r := by
    rw [hr_def, ENNReal.ofReal_toReal hne_top]
  rw [hdist_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  obtain ⟨v, hv_exp, hv_len⟩ :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm x y
  rw [← hr_def] at hv_len
  rcases eq_or_ne r 0 with hr0 | hr_ne
  · rw [hr0]
    have hpi_nn : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg K
    exact div_nonneg hpi_nn hsqrt_nn
  have hr_pos' : 0 < r := lt_of_le_of_ne hr_nn (Ne.symm hr_ne)
  set u : TangentSpace I x := r⁻¹ • v with hu_def
  set γ : ℝ → M :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic
      (I := I) g hEnorm x u with hγ_def
  set L : ℝ := r with hL_def
  have hL_nn : (0 : ℝ) ≤ L := hr_nn
  have hL_pos : (0 : ℝ) < L := hr_pos'
  have hvv_nn : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact le_of_lt (g.pos x v hv0)
  have hvv_sq : g.inner x v v = L ^ 2 := by
    have := congrArg (· ^ 2) hv_len
    simpa [Real.sq_sqrt hvv_nn] using this
  have hu_unit : g.inner x u u = 1 := by
    have hbil : g.inner x u u = L⁻¹ * (L⁻¹ * g.inner x v v) := by
      rw [hu_def]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hbil, hvv_sq]
    field_simp
  have hγ0 : γ 0 = x :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_zero
      (I := I) g hEnorm x u
  have hru : r • u = v := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hr_ne, one_smul]
  have hγL : γ L = y := by
    have hsmul :
        DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic
            (I := I) g hEnorm x (r • u) 1
          = γ r :=
      DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_smul
        (I := I) g hEnorm x u r
    rw [hL_def, ← hsmul, hru]
    have hexp :
        DifferentialGeometry.Geometry.Riemannian.Exponential.expMapIntrinsic
            (I := I) g hEnorm x v = y := hv_exp
    rw [DifferentialGeometry.Geometry.Riemannian.Exponential.expMapIntrinsic_def] at hexp
    exact hexp
  have hγ_isGeo :
      DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic (I := I) g γ :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_isGeodesic
      (I := I) g hEnorm x u
  have hγ_cont : Continuous γ :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_continuous
      (I := I) g hEnorm x u
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.isGeodesic_contMDiff
      (I := I) g hγ_isGeo hγ_cont
  have hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 L) :=
    (hγ_smooth.of_le (by exact_mod_cast le_top)).contMDiffOn
  have hγ_geoOn :
      DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOn
        (I := I) g γ (Set.Icc 0 L) :=
    hγ_isGeo.isGeodesicOn (Set.Icc 0 L)
  have hγ_unit_mfderiv :
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1 := by
    intro t _ht
    have hspeed :
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          = g.inner x u u :=
      DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_speedSq_eq
        (I := I) g hEnorm x u t
    rw [hspeed, hu_unit]
  have hUnit0 :
      g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 1 :=
    hγ_unit_mfderiv 0 ⟨le_refl 0, hL_nn⟩
  let uPrime : ℝ → E := fun t : ℝ =>
    (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E)
  have hγ_unit :
      ∀ t ∈ Set.Icc (0 : ℝ) L, g.inner (γ t) (uPrime t) (uPrime t) = 1 := by
    intro t ht
    exact hγ_unit_mfderiv t ht
  have hγ_edist : Manifold.riemannianEDist I x y = ENNReal.ofReal L := by
    rw [hL_def]; exact hdist_ofReal
  have hRic' :
      RicciBoundedBelow (I := I) g ((Module.finrank ℝ E - 1 : ℝ) * K) := _hRic
  have hγ_min :
      ∀ η : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) →
        η 0 = γ 0 → η L = γ L →
        DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
            (I := I) g γ 0 L ≤
          DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
            (I := I) g η 0 L := by
    have hγ_arcLength : DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
        (I := I) g γ 0 L = L := by
      unfold DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
      have hcongr :
          ∀ t ∈ Set.uIcc (0 : ℝ) L,
            Real.sqrt
                ((g.inner (γ t))
                  (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                  (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
              = (1 : ℝ) := by
        intro t ht
        have htIcc : t ∈ Set.Icc (0 : ℝ) L := by
          rw [Set.uIcc_of_le hL_nn] at ht
          exact ht
        have hone : (g.inner (γ t))
              (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1 :=
          hγ_unit_mfderiv t htIcc
        rw [hone, Real.sqrt_one]
      rw [intervalIntegral.integral_congr hcongr]
      simp
    have hdist_eq : Manifold.riemannianEDist I (γ 0) (γ L)
        = ENNReal.ofReal L := by
      have : Manifold.riemannianEDist I x y = ENNReal.ofReal L := hγ_edist
      rw [← hγ0, ← hγL] at this
      exact this
    intro η hη_C1 hη0 hηL
    have hη_arcLength_nn :
        0 ≤ DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
            (I := I) g η 0 L := by
      unfold DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
      exact intervalIntegral.integral_nonneg hL_nn (fun t _ => Real.sqrt_nonneg _)
    have hη_enorm :
        ∀ t ∈ Set.Icc (0 : ℝ) L,
          ‖mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)‖ₑ
            = ENNReal.ofReal (Real.sqrt
                (g.inner (η t)
                  (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
                  (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)))) :=
      fun t _ => hEnorm (η t) (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
    have hUniqueη : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) L) := by
      intro u hu
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact (uniqueDiffOn_Icc hL_pos) u hu
    have hLiftη : Continuous (fun u : ℝ =>
        (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
      have h_homeo :
          Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
            ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
        (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
      exact h_homeo.comp (continuous_id.prodMk continuous_const)
    have hMapsη : Set.MapsTo
        (fun u : ℝ => (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
        (Set.Icc (0 : ℝ) L) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc (0 : ℝ) L)) := by
      intro u hu; simpa using hu
    have hVWη : ContinuousOn
        (fun t : ℝ =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ)) :
              TangentBundle I M))
        (Set.Icc (0 : ℝ) L) := by
      have hTanη := hη_C1.continuousOn_tangentMapWithin (le_refl 1) hUniqueη
      have hCompη : ContinuousOn
          (fun t : ℝ => tangentMapWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L)
            (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
          (Set.Icc (0 : ℝ) L) :=
        hTanη.comp hLiftη.continuousOn hMapsη
      exact hCompη.congr (fun t _ => rfl)
    have hgSecη : ContinuousOn
        (fun t : ℝ => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          (η t) (g.inner (η t))))
        (Set.Icc (0 : ℝ) L) := by
      have hgCont : Continuous
          (fun b : M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
            b (g.inner b))) := g.contMDiff.continuous
      exact hgCont.comp_continuousOn hη_C1.continuousOn
    have hScalarTotalη : ContinuousOn
        (fun t : ℝ => (TotalSpace.mk' ℝ (E := fun _ : M => ℝ)
          (η t)
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ)))))
        (Set.Icc (0 : ℝ) L) :=
      ContinuousOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := η) hgSecη hVWη hVWη
    have hScalarWη : ContinuousOn
        (fun t : ℝ => g.inner (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ))
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ)))
        (Set.Icc (0 : ℝ) L) := by
      have hproj : Continuous
          (fun p : TotalSpace ℝ (fun _ : M => ℝ) => p.2) :=
        continuous_snd.comp ((Bundle.Trivial.homeomorphProd M ℝ).continuous)
      exact hproj.comp_continuousOn hScalarTotalη
    have hIntWη : MeasureTheory.IntegrableOn
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ))))
        (Set.Icc 0 L) MeasureTheory.volume :=
      (Real.continuous_sqrt.comp_continuousOn hScalarWη).integrableOn_Icc
    have hη_int :
        MeasureTheory.IntegrableOn
          (fun t : ℝ => Real.sqrt
            (g.inner (η t)
              (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))))
          (Set.Icc 0 L) MeasureTheory.volume := by
      refine hIntWη.congr ?_
      have hIoo_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) L)),
          t ∈ Set.Ioo (0 : ℝ) L := by
        rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
        exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
      filter_upwards [hIoo_ae] with t ht
      have hmem : Set.Icc (0 : ℝ) L ∈ nhds t := Icc_mem_nhds ht.1 ht.2
      rw [mfderivWithin_of_mem_nhds hmem]
    have hη_pathLen :
        Manifold.pathELength I η 0 L
          = ENNReal.ofReal
              (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
                (I := I) g η 0 L) := by
      set F : ℝ → ℝ := fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))) with hF_def
      have hF_nn : ∀ t : ℝ, 0 ≤ F t := fun t => Real.sqrt_nonneg _
      rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
      change ∫⁻ t in Set.Icc 0 L, (fun t : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)‖ₑ) t
        = ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
            (I := I) g η 0 L)
      have h_lint_eq :=
        MeasureTheory.setLIntegral_congr_fun (μ := MeasureTheory.volume)
          (f := fun t : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)‖ₑ)
          (g := fun t : ℝ => ENNReal.ofReal (F t))
          (s := Set.Icc 0 L)
          measurableSet_Icc
          (fun t ht => by simpa [hF_def] using hη_enorm t ht)
      rw [h_lint_eq]
      have h_ofReal :
          ENNReal.ofReal (∫ t in Set.Icc 0 L, F t)
            = ∫⁻ t in Set.Icc 0 L, ENNReal.ofReal (F t) := by
        have hF_nn_ae : 0 ≤ᵐ[(MeasureTheory.volume).restrict (Set.Icc 0 L)] F :=
          MeasureTheory.ae_of_all _ hF_nn
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hη_int hF_nn_ae
      rw [← h_ofReal]
      have h_Icc_Ioc :
          ∫ t in Set.Icc 0 L, F t = ∫ t in Set.Ioc 0 L, F t := by
        have h_set : Set.Icc (0 : ℝ) L = {(0 : ℝ)} ∪ Set.Ioc 0 L := by
          ext z
          simp only [Set.mem_Icc, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioc]
          constructor
          · rintro ⟨h1, h2⟩
            by_cases h : z = 0
            · left; exact h
            · right; exact ⟨lt_of_le_of_ne h1 (fun h' => h h'.symm), h2⟩
          · rintro (rfl | ⟨h1, h2⟩)
            · exact ⟨le_refl _, hL_nn⟩
            · exact ⟨le_of_lt h1, h2⟩
        rw [h_set]
        have hdisj : Disjoint ({(0 : ℝ)} : Set ℝ) (Set.Ioc 0 L) := by
          rw [Set.disjoint_left]
          rintro z hz hz'
          simp only [Set.mem_singleton_iff] at hz
          rw [hz] at hz'; exact lt_irrefl _ hz'.1
        have h_int_singleton :
            MeasureTheory.IntegrableOn F ({(0 : ℝ)} : Set ℝ) MeasureTheory.volume := by
          rw [MeasureTheory.integrableOn_singleton_iff]; exact Or.inr (by simp)
        have h_int_Ioc :
            MeasureTheory.IntegrableOn F (Set.Ioc 0 L) MeasureTheory.volume :=
          hη_int.mono_set Set.Ioc_subset_Icc_self
        rw [MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
          h_int_singleton h_int_Ioc]
        have h_singleton : ∫ t in ({(0 : ℝ)} : Set ℝ), F t = 0 := by simp
        rw [h_singleton, zero_add]
      have h_intInterval : ∫ t in (0 : ℝ)..L, F t = ∫ t in Set.Ioc 0 L, F t :=
        intervalIntegral.integral_of_le hL_nn
      have h_arcLength :
          DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g η 0 L
            = ∫ t in (0 : ℝ)..L, F t := rfl
      rw [h_arcLength, h_intInterval, h_Icc_Ioc]
    have hdist_le_pathLen :
        Manifold.riemannianEDist I (η 0) (η L)
          ≤ Manifold.pathELength I η 0 L :=
      Manifold.riemannianEDist_le_pathELength (I := I) (γ := η)
        (a := 0) (b := L) hη_C1 rfl rfl hL_nn
    have hL_le_pathLen :
        ENNReal.ofReal L ≤ Manifold.pathELength I η 0 L := by
      have hrewrite : Manifold.riemannianEDist I (γ 0) (γ L)
          ≤ Manifold.pathELength I η 0 L := by
        rw [← hη0, ← hηL]
        exact hdist_le_pathLen
      calc
        ENNReal.ofReal L = Manifold.riemannianEDist I (γ 0) (γ L) := hdist_eq.symm
        _ ≤ Manifold.pathELength I η 0 L := hrewrite
    have hL_le_arcLength :
        L ≤ DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
            (I := I) g η 0 L := by
      have hofReal_le :
          ENNReal.ofReal L
            ≤ ENNReal.ofReal
                (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
                  (I := I) g η 0 L) := by
        rw [← hη_pathLen]; exact hL_le_pathLen
      exact (ENNReal.ofReal_le_ofReal_iff hη_arcLength_nn).mp hofReal_le
    rw [hγ_arcLength]
    exact hL_le_arcLength
  have hL_le : L ≤ Real.pi / Real.sqrt K := by
      have huPrimeEq :
          ∀ t ∈ Set.Icc (0 : ℝ) L,
            (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = uPrime t := by
        intro t _ht; rfl
      obtain ⟨e, heDiff, hParallel, hON, hPerp_mfderiv, hEbundle⟩ :=
        DifferentialGeometry.Geometry.Riemannian.exists_parallel_perp_frame
          (I := I) g γ hγ_smooth hL_pos hγ_geoOn hUnit0
      have hPerp :
          ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
            g.inner (γ t) ((e i).toFun t) (uPrime t) = 0 := by
        intro t ht i
        exact hPerp_mfderiv t ht i
      have hIntegrandSum :
          ∀ i : Fin (Module.finrank ℝ E - 1),
            IntervalIntegrable
              (fun t : ℝ => indexFormIntegrand (I := I) g γ
                ((SectionAlongCurve.smulFun
                  (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
                ((SectionAlongCurve.smulFun
                  (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t)
              MeasureTheory.volume 0 L :=
        DifferentialGeometry.Geometry.Riemannian.Variation.indexFormIntegrand_intervalIntegrable
          (I := I) g γ L hL_pos hγ_C1 hγ_geoOn hγ_unit_mfderiv e heDiff hParallel hON hPerp
      have hRicIntegrable :
          IntervalIntegrable
            (fun t : ℝ => ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t))
            MeasureTheory.volume 0 L := by
        have hL_nn' : (0 : ℝ) ≤ L := le_of_lt hL_pos
        have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) L) := by
          intro u hu
          rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact (uniqueDiffOn_Icc hL_pos) u hu
        have hTan := hγ_C1.continuousOn_tangentMapWithin (le_refl 1) hUnique
        have hLift : Continuous (fun u : ℝ =>
            (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
          have h_homeo :
              Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
                ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
            (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
          exact h_homeo.comp (continuous_id.prodMk continuous_const)
        have hMaps : Set.MapsTo
            (fun u : ℝ => (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
            (Set.Icc (0 : ℝ) L) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc (0 : ℝ) L)) := by
          intro u hu
          simpa using hu
        have hVW : ContinuousOn
            (fun t : ℝ =>
              (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
                (γ t)
                (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)) :
                  TangentBundle I M))
            (Set.Icc (0 : ℝ) L) := by
          have hComp : ContinuousOn
              (fun t : ℝ => tangentMapWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L)
                (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
              (Set.Icc (0 : ℝ) L) :=
            hTan.comp hLift.continuousOn hMaps
          exact hComp.congr (fun t _ => rfl)
        have hRicSec : ContinuousOn
            (fun t : ℝ => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
              (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
              (γ t) (ricciTensor (I := I) g (γ t))))
            (Set.Icc (0 : ℝ) L) := by
          have hRicCont : Continuous
              (fun b : M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
                (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
                b (ricciTensor (I := I) g b))) :=
            (ricciTensor_contMDiff (I := I) g).continuous
          exact (hRicCont.comp_continuousOn hγ_C1.continuousOn)
        have hScalarTotal : ContinuousOn
            (fun t : ℝ => (TotalSpace.mk' ℝ (E := fun _ : M => ℝ)
              (γ t)
              (ricciTensor (I := I) g (γ t)
                (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
                (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))))
            (Set.Icc (0 : ℝ) L) :=
          ContinuousOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
            (b := γ) hRicSec hVW hVW
        have hScalarW : ContinuousOn
            (fun t : ℝ => ricciTensor (I := I) g (γ t)
              (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
              (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))
            (Set.Icc (0 : ℝ) L) := by
          have hproj : Continuous
              (fun p : TotalSpace ℝ (fun _ : M => ℝ) => p.2) :=
            continuous_snd.comp
              ((Bundle.Trivial.homeomorphProd M ℝ).continuous)
          exact hproj.comp_continuousOn hScalarTotal
        have hIntW : IntervalIntegrable
            (fun t : ℝ => ricciTensor (I := I) g (γ t)
              (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
              (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))
            MeasureTheory.volume 0 L := by
          apply ContinuousOn.intervalIntegrable
          rwa [Set.uIcc_of_le hL_nn']
        refine hIntW.congr_ae ?_
        have hIoo_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) L)),
            t ∈ Set.Ioo (0 : ℝ) L := by
          rw [Set.uIoc_of_le hL_nn', ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
          exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
        filter_upwards [hIoo_ae] with t ht
        have hmem : Set.Icc (0 : ℝ) L ∈ nhds t := Icc_mem_nhds ht.1 ht.2
        change ricciTensor (I := I) g (γ t)
            (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
          = ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t)
        rw [mfderivWithin_of_mem_nhds hmem]
      have hVbundle :
          ∀ i : Fin (Module.finrank ℝ E - 1),
            ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
              (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
                (γ t)
                ((SectionAlongCurve.smulFun
                  (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun t))) := by
        intro i
        have hχ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
            (fun s : ℝ => Real.sin (Real.pi * s / L)) := by
          rw [contMDiff_iff_contDiff]
          exact Real.contDiff_sin.comp
            ((contDiff_const.mul contDiff_id).div_const L)
        have hprod :=
          DifferentialGeometry.Geometry.Riemannian.Variation.contMDiff_smul_bundleField
            (I := I) hγ_smooth hχ_smooth (hEbundle i)
        exact hprod
      exact bonnet_myers_length_le_of_ricci_bound (I := I) g γ hL_pos hEnorm
        hγ_smooth hγ_C1 hγ_geoOn _hK _hdim hRic' uPrime huPrimeEq hγ_unit
        e heDiff hParallel hON hPerp hIntegrandSum hRicIntegrable hγ_min hVbundle
  exact hL_le

set_option linter.deprecated false in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Bonnet-Myers diameter theorem.** On a complete connected Riemannian
manifold of dimension `n ≥ 2` with Ricci curvature bounded below by
`(n-1) K` for some `K > 0`, the metric diameter `EMetric.diam univ` is at
most `π / √K`. The hypothesis `hEnorm` is the supplied structural identity
that the fibre extended norm equals `ofReal (√ g.inner)`. -/
theorem bonnet_myers_diameter_of_ricci_bound
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnorm : ∀ (xb : M) (v : TangentSpace I xb),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner xb v v))) :
    EMetric.diam (Set.univ : Set M) ≤
      ENNReal.ofReal (Real.pi / Real.sqrt K) := by
  refine Metric.ediam_le ?_
  intro x _ y _
  exact bonnet_myers_pairwise_edist_le_of_ricci_bound (E := E) g _hdim _hK _hRic hEnorm x y

set_option linter.deprecated false in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **bm-c-univ-compact.** The whole space `Set.univ : Set M` is compact.
Combines the diameter bound (sibling headline `bonnet_myers_diameter_of_ricci_bound`) with
exponential-map surjectivity on the closed ball of radius `π / √K` and
`IsCompact.of_isClosed_subset` together with `isClosed_univ`. -/
theorem isCompact_univ
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnorm : ∀ (xb : M) (v : TangentSpace I xb),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner xb v v))) :
    IsCompact (Set.univ : Set M) := by
  let p : M := Classical.arbitrary M
  set R : ℝ := Real.pi / Real.sqrt K with hR_def
  have hR_nn : 0 ≤ R := by
    have hpi_nn : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg K
    exact div_nonneg hpi_nn hsqrt_nn
  have hdiam : EMetric.diam (Set.univ : Set M) ≤ ENNReal.ofReal R :=
    bonnet_myers_diameter_of_ricci_bound (E := E) g _hdim _hK _hRic hEnorm
  have hsurj :=
    DifferentialGeometry.Geometry.Riemannian.HopfRinow.expMap_surjective_on_closedBall_of_ediam_le
      (I := I) g p hR_nn hdiam
  have himg :=
    isCompact_image_closedBall_under_expMap (I := I) (E := E) g p hR_nn
  exact himg.of_isClosed_subset isClosed_univ hsurj

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Bonnet-Myers compactness theorem.** On a complete connected Riemannian
manifold of dimension `n ≥ 2` with Ricci curvature bounded below by
`(n-1) K` for some `K > 0`, the manifold is compact (`CompactSpace M`). The
hypothesis `hEnorm` is the supplied structural identity that the fibre
extended norm equals `ofReal (√ g.inner)`. -/
theorem bonnet_myers_compactSpace_of_ricci_bound
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnorm : ∀ (xb : M) (v : TangentSpace I xb),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner xb v v))) :
    CompactSpace M :=
  isCompact_univ_iff.mp (isCompact_univ (E := E) g _hdim _hK _hRic hEnorm)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Bonnet-Myers finiteness of the fundamental group.** On a complete
connected Riemannian manifold of dimension `n ≥ 2` with Ricci curvature
bounded below by `(n-1) K` for some `K > 0`, the fundamental group
`π₁(M, x)` at any base point is finite. The proof passes to the universal
cover, pulls back the Ricci bound, applies the compactness theorem to the
lifted manifold, and identifies the cover fibre over `x` with `π₁(M, x)`
via monodromy. The hypothesis `hEnormBase` is the supplied structural
identity that the fibre extended norm on `M` equals `ofReal (√ g.inner)`.

One residual gap remains: the cross-instance norm-diamond bridge reconciling
the lifted `RiemannianBundle` extended norm with the project `Tensor0SBundle`
extended norm in the compactness application (the two agree pointwise as the
square root of the lifted metric, but the explicit identification is left as
a `sorry`). -/
theorem bonnet_myers_finite_fundamentalGroup_of_ricci_bound
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [LocPathConnectedSpace M]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
    [PseudoEMetricSpace M] [Inhabited M]
    [T2Space (TangentBundle I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnormBase : ∀ (xb : M) (v : TangentSpace I xb),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner xb v v)))
    (x : M) :
    Finite (FundamentalGroup M x) := by
  set UC := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
  set p :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj
  have hcov :
      IsCoveringMap
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.UniversalCover.proj_isCoveringMap
  haveI hpcM : PathConnectedSpace M :=
    PathConnectedSpace.of_locPathConnectedSpace
  let gLift :
      SmoothRiemannianMetric I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
      (I := I) g
  letI hRB :
      Bundle.RiemannianBundle
        (fun (xt :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
          TangentSpace I xt) :=
    ⟨gLift.toRiemannianMetric⟩
  haveI hSCH : SecondCountableTopology H :=
    ModelWithCorners.secondCountableTopology I
  haveI hSCM : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact H M
  have hBasisLift : ∀ x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
      DifferentialGeometry.Integral.Connection.chartRiemannBasisIdentity
        (I := I) gLift x' :=
    fun x' =>
      DifferentialGeometry.Integral.Connection.chartRiemannBasisIdentity_LeviCivita
        (I := I) gLift x'
  have hBasisBase : ∀ x : M,
      DifferentialGeometry.Integral.Connection.chartRiemannBasisIdentity
        (I := I) g x :=
    fun x =>
      DifferentialGeometry.Integral.Connection.chartRiemannBasisIdentity_LeviCivita
        (I := I) g x
  have hRicLift :
      RicciBoundedBelow (I := I) gLift (((Module.finrank ℝ E : ℝ) - 1) * K) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ricciBoundedBelow_liftedMetric_of_base
      (I := I) (g := g) _hRic hBasisLift hBasisBase
  haveI hRegUC :
      RegularSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_regularSpace
      (M := M) I
  have hEnormCover :
      ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (v : TangentSpace I x'),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gLift.inner x' v v)) := by
    intro x' v
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    have hinner : (inner ℝ v v : ℝ) = gLift.inner x' v v := rfl
    rw [hinner]
  letI hUCem :
      PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_pseudoEMetricSpace
      (I := I) (M := M) gLift
  haveI hRiemUC :
      IsRiemannianManifold I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.isRiemannianManifold
      (I := I) (M := M) gLift
  haveI hCompUC :
      CompleteSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.completeSpace_of_complete
      (I := I) (M := M) g hEnormBase hEnormCover
  haveI hCRBcover :
      IsContinuousRiemannianBundle E
        (fun (x' :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
          TangentSpace I x') :=
    ⟨gLift.inner, gLift.contMDiff.continuous, fun _ _ _ => rfl⟩
  haveI hT2TanCover :
      T2Space (TangentBundle I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)) :=
    inferInstance
  haveI hCompactUC :
      CompactSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    bonnet_myers_compactSpace_of_ricci_bound (E := E) gLift _hdim _hK hRicLift (by
      sorry)
  haveI hFinFibre :
      Finite
        ((DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
          ⁻¹' {x}) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.isCoveringMap_fibre_finite_of_compact
      hcov x
  obtain ⟨γ⟩ := PathConnectedSpace.joined (default : M) x
  let e' :
      ((DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        ⁻¹' {x}) :=
    ⟨⟨x, Path.Homotopic.Quotient.mk γ⟩,
      by
        change
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj
              (X := M)
              (⟨x, Path.Homotopic.Quotient.mk γ⟩ :
                DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
            = x
        rfl⟩
  have hEquiv :
      ((DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        ⁻¹' {x})
        ≃ FundamentalGroup M x :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.fibreEquivFundamentalGroup
      hcov x e'
  exact Finite.of_equiv _ hEquiv

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
