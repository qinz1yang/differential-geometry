import DifferentialGeometry.Analysis.Sobolev.Manifold.Lipschitz
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lp.Basic
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.CompactSupport
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.Support
import DifferentialGeometry.Geometry.Operator.Gradient.LipschitzBound
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact


open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace IntrinsicLp

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [FiniteDimensional ℝ E] in
private lemma mdiff_of_pull
    (α : M) {f : M → ℝ} {x : M}
    (hx : x ∈ (chartAt H α).source)
    (hf : DifferentiableAt ℝ (chartPullZero (I := I) α f)
      (extChartAt I α x)) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) f x := by
  let coord : M → E := fun y => extChartAt I α y
  have hcoord : MDifferentiableAt I 𝓘(ℝ, E) coord x := by
    change MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x
    exact mdifferentiableAt_extChartAt hx
  have hcomp : MDifferentiableAt I 𝓘(ℝ, ℝ)
      ((chartPullZero (I := I) α f) ∘ coord) x :=
    hf.comp_mdifferentiableAt hcoord
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt H α).open_source.mem_nhds hx] with y hy
  have hy_ext : y ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hy
  have hy_target : extChartAt I α y ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hy_ext
  rw [Function.comp_apply, chartPullZero_mem (I := I) α f hy_target]
  exact (scalarOnE_extChartAt (I := I) α f hy_ext).symm

private lemma chart_lip_ae_mdiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {φ : M → ℝ} {C : NNReal}
    (hφ : LipschitzWith C (chartPullZero (I := I) α φ)) :
    ∀ᵐ x ∂chartLocalMeasure (I := I) g α,
      x ∈ (chartAt H α).source → MDifferentiableAt I 𝓘(ℝ) φ x := by
  have hdiff : ∀ᵐ y ∂(modelHaar (E := E)),
      DifferentiableAt ℝ (chartPullZero (I := I) α φ) y :=
    hφ.ae_differentiableAt
  filter_upwards [ae_chart_of_haar (I := I) (M := M) g α
      (measurableSet_of_differentiableAt ℝ _) hdiff] with x hx
  exact fun hxsource => mdiff_of_pull (I := I) α hxsource (hx hxsource)

omit [IsManifold I ∞ M] in
private lemma pull_lipschitz_of_chartPushedRaw
    (α : M) (φ : M → ℝ) {C : NNReal}
    (hφ : LipschitzWith C (chartPushedRaw (I := I) (M := M) α φ)) :
    ∃ D : NNReal, LipschitzWith D (chartPullZero (I := I) α φ) := by
  have heq : chartPullZero (I := I) α φ =
      chartPushedRaw (I := I) (M := M) α φ ∘ (toEuclidean (E := E)) := by
    funext y
    by_cases hy : y ∈ (extChartAt I α).target
    · have hy' : toEuclidean y ∈ chartTargetEuclid (I := I) (M := M) α := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]
        simpa only [Set.mem_preimage,
          (toEuclidean (E := E)).symm_apply_apply] using hy
      rw [chartPullZero_mem (I := I) α φ hy, Function.comp_apply,
        chartPushedRaw_apply_of_mem (I := I) (M := M) α φ hy']
      simp only [scalarOnE_def, (toEuclidean (E := E)).symm_apply_apply]
    · have hy' : toEuclidean y ∉ chartTargetEuclid (I := I) (M := M) α := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]
        simpa only [Set.mem_preimage,
          (toEuclidean (E := E)).symm_apply_apply] using hy
      rw [chartPullZero_nmem (I := I) α φ hy, Function.comp_apply,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) α φ hy']
  refine ⟨C * ‖(toEuclidean (E := E)).toContinuousLinearMap‖₊, ?_⟩
  rw [heq]
  exact hφ.comp (toEuclidean (E := E)).lipschitz

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [IsManifold I ∞ M] in
theorem intrinsic_lip_cont
    [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {L : NNReal}
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y) :
    Continuous u := by
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  let : RegularSpace M := inferInstance
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  apply LipschitzWith.continuous (K := L)
  intro x y
  rw [IsRiemannianManifold.out (I := I) x y]
  simpa only [riemannianEDistOf] using hu x y

theorem integrable_tangentSectionAction_and_integral_eq_neg_integral_smul_divergence_of_lipschitz
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X)
    {u : M → ℝ} {L : NNReal}
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y) :
    Integrable (tangentSectionAction (I := I) X u)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      ∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, u x * divergenceG (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let ρ : SmoothPartitionOfUnity M I M (univ : Set M) := chartAtlasPOU I M
  let K : Set M := tsupport X
  have hK_compact : IsCompact K := hX
  let S : Finset M :=
    (pouFinset_for_compactSet (I := I) (M := M) hK_compact).toFinset
  have hSmem : ∀ {α : M}, α ∈ S ↔
      (tsupport ((chartAtlasPOU I M) α) ∩ K).Nonempty := fun {α} =>
    Set.Finite.mem_toFinset _
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) := by
    simpa only [ρ] using chartAtlasPOU_isSubordinate I M
  have hu_cont : Continuous u := intrinsic_lip_cont (I := I) g hu
  have hdiv_cont : Continuous (divergenceG (I := I) g X) :=
    (divergence_g_contMDiff (I := I) g X).continuous
  have hdiv_cs : HasCompactSupport (divergenceG (I := I) g X) :=
    hasCompactSupport_divergence_g (I := I) g hX
  have hdiv_supp : tsupport (divergenceG (I := I) g X) ⊆ K := by
    simpa only [K] using tsupport_divergence_g_subset (I := I) g X
  have hudiv_cont : Continuous (fun x => u x * divergenceG (I := I) g X x) :=
    hu_cont.mul hdiv_cont
  have hudiv_cs : HasCompactSupport (fun x => u x * divergenceG (I := I) g X x) :=
    hdiv_cs.mul_left
  let _ : IsLocallyFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  have hudiv_int : Integrable (fun x => u x * divergenceG (I := I) g X x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hudiv_cont.integrable_of_hasCompactSupport hudiv_cs
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_one_nhds⟩ :=
    DifferentialGeometry.Analysis.exists_bump_nhds (I := I) hK_compact
  have hχ_one_K : ∀ x ∈ K, χ x = 1 := by
    intro x hxK
    rcases Filter.eventually_iff_exists_mem.mp hχ_one_nhds with ⟨U, hU_nhds, hU_eq⟩
    have hU_open : K ⊆ interior U := by
      rwa [← subset_interior_iff_mem_nhdsSet] at hU_nhds
    exact hU_eq x (interior_subset (hU_open hxK))
  let a : M → M → ℝ := fun α x => χ x * (ρ α : M → ℝ) x
  let φ : M → M → ℝ := fun α x => a α x * u x
  have ha_smooth (α : M) : ContMDiff I 𝓘(ℝ) ∞ (a α) := by
    change ContMDiff I 𝓘(ℝ) ∞ (χ * (ρ α : M → ℝ))
    exact hχ_smooth.mul (ρ α).contMDiff
  have ha_cs (α : M) : HasCompactSupport (a α) := by
    change HasCompactSupport (χ * (ρ α : M → ℝ))
    exact hχ_cs.mul_right
  have ha_supp (α : M) : tsupport (a α) ⊆ (chartAt H α).source := by
    have hsub : tsupport (fun x => χ x * (ρ α : M → ℝ) x) ⊆
        tsupport (ρ α : M → ℝ) := tsupport_mul_subset_right
    simpa only [a] using hsub.trans (hρsub α)
  have hφ_cs (α : M) : HasCompactSupport (φ α) := by
    change HasCompactSupport ((a α) * u)
    exact (ha_cs α).mul_right
  have hφ_supp (α : M) : tsupport (φ α) ⊆ (chartAt H α).source := by
    have hsub : tsupport (fun x => a α x * u x) ⊆ tsupport (a α) :=
      tsupport_mul_subset_left
    simpa only [φ] using hsub.trans (ha_supp α)
  have hφ_lip (α : M) : ∃ C : NNReal,
      LipschitzWith C (chartPullZero (I := I) α (φ α)) := by
    simpa only [φ] using
      exists_lipschitzWith_chartPullZero_mul
        (I := I) g α (ha_smooth α) (ha_cs α) (ha_supp α) hu
  let D : M → NNReal := fun α => Classical.choose (hφ_lip α)
  have hD (α : M) : LipschitzWith (D α)
      (chartPullZero (I := I) α (φ α)) :=
    Classical.choose_spec (hφ_lip α)
  have hφ_mdiff_local (α : M) :
      ∀ᵐ x ∂chartLocalMeasure (I := I) g α,
        x ∈ (chartAt H α).source → MDifferentiableAt I 𝓘(ℝ) (φ α) x :=
    chart_lip_ae_mdiff (I := I) g α (hD α)
  have hφ_mdiff_global (α : M) :
      ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g,
        MDifferentiableAt I 𝓘(ℝ) (φ α) x := by
    have hrestrict :=
      riemannianVolumeMeasure_restrict_eq_chartLocalMeasure_restrict
        (I := I) (M := M) g α (hφ_cs α) (hφ_supp α)
    have hon : ∀ᵐ x ∂(riemannianVolumeMeasure (I := I) (M := M) g).restrict
        (tsupport (φ α)), MDifferentiableAt I 𝓘(ℝ) (φ α) x := by
      rw [hrestrict]
      filter_upwards [
        ae_restrict_mem (isClosed_tsupport (φ α)).measurableSet,
        ae_restrict_of_ae (hφ_mdiff_local α)] with x hxs hx
      exact hx (hφ_supp α hxs)
    have hon' : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g,
        x ∈ tsupport (φ α) → MDifferentiableAt I 𝓘(ℝ) (φ α) x := by
      rwa [ae_restrict_iff' (isClosed_tsupport (φ α)).measurableSet] at hon
    filter_upwards [hon'] with x hx
    by_cases hxs : x ∈ tsupport (φ α)
    · exact hx hxs
    · exact (mdifferentiableAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp hxs)
  have hφ_mdiff_all :
      ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g,
        ∀ α ∈ S, MDifferentiableAt I 𝓘(ℝ) (φ α) x := by
    exact (Filter.eventually_all_finset S).2 (fun α _ => hφ_mdiff_global α)
  have hρ_sum_K (x : M) (hxK : x ∈ K) : ∑ α ∈ S, (ρ α : M → ℝ) x = 1 := by
    have hfins : ρ.finsupport x ⊆ S := by
      intro α hα
      rw [hSmem]
      rw [ρ.mem_finsupport] at hα
      exact ⟨x, subset_tsupport _ hα, hxK⟩
    exact ρ.sum_finsupport' x (Set.mem_univ x) hfins
  have hφ_sum_nhds (x : M) (hxK : x ∈ K) :
      (∑ α ∈ S, φ α) =ᶠ[𝓝 x] u := by
    rcases Filter.eventually_iff_exists_mem.mp hχ_one_nhds with ⟨U, hU_nhds, hU_eq⟩
    have hU_int : K ⊆ interior U := by
      rwa [← subset_interior_iff_mem_nhdsSet] at hU_nhds
    have hxU : x ∈ interior U := hU_int hxK
    have hU_x_nhd : U ∈ 𝓝 x := mem_nhds_iff.mpr
      ⟨interior U, interior_subset, isOpen_interior, hxU⟩
    filter_upwards [hU_x_nhd, ρ.eventually_finsupport_subset x] with y hyU hy
    have hfins : ρ.finsupport y ⊆ S := by
      intro α hα
      rw [hSmem]
      rw [ρ.mem_finsupport] at hα
      have hαx : α ∈ ρ.fintsupport x := hy ((ρ.mem_finsupport y).mpr hα)
      have hxt : x ∈ tsupport (ρ α : M → ℝ) :=
        (ρ.mem_fintsupport_iff x α).mp hαx
      exact ⟨x, hxt, hxK⟩
    have hone : ∑ α ∈ S, (ρ α : M → ℝ) y = 1 :=
      ρ.sum_finsupport' y (Set.mem_univ y) hfins
    have hχy : χ y = 1 := by
      simpa only [Pi.one_apply] using hU_eq y hyU
    rw [Finset.sum_apply]
    change (∑ α ∈ S, (χ y * (ρ α : M → ℝ) y) * u y) = u y
    rw [← Finset.sum_mul, ← Finset.mul_sum, hone, hχy, one_mul, one_mul]
  have h_rhs_fun :
      (fun x => ∑ α ∈ S,
        (u x * divergenceG (I := I) g X x) * a α x) =
        (fun x => u x * divergenceG (I := I) g X x) := by
    funext x
    by_cases hxK : x ∈ K
    · simp only [a, ← mul_assoc]
      rw [← Finset.mul_sum, hρ_sum_K x hxK, mul_one, hχ_one_K x hxK, mul_one]
    · have hdiv_zero : divergenceG (I := I) g X x = 0 := by
        have hxnot : x ∉ tsupport (divergenceG (I := I) g X) :=
          fun hx => hxK (hdiv_supp hx)
        by_contra hne
        exact hxnot (subset_tsupport _ hne)
      simp only [hdiv_zero, mul_zero, zero_mul, Finset.sum_const_zero]
  have ha_cont (α : M) : Continuous (a α) := (ha_smooth α).continuous
  have hterm_cont (α : M) : Continuous
      (fun x => (u x * divergenceG (I := I) g X x) * a α x) :=
    hudiv_cont.mul (ha_cont α)
  have hterm_cs (α : M) : HasCompactSupport
      (fun x => (u x * divergenceG (I := I) g X x) * a α x) :=
    (ha_cs α).mul_left
  have hterm_supp (α : M) :
      tsupport (fun x => (u x * divergenceG (I := I) g X x) * a α x) ⊆
        (chartAt H α).source :=
    tsupport_mul_subset_right.trans (ha_supp α)
  have hterm_int (α : M) : Integrable
      (fun x => (u x * divergenceG (I := I) g X x) * a α x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (hterm_cont α).integrable_of_hasCompactSupport (hterm_cs α)
  have h_rhs_decomp :
      ∫ x, u x * divergenceG (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∑ α ∈ S, ∫ x, (u x * divergenceG (I := I) g X x) * a α x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [← h_rhs_fun]
    exact integral_finsetSum S (fun α _ => hterm_int α)
  have hterm_chart : ∀ α ∈ S,
      ∫ x, (u x * divergenceG (I := I) g X x) * a α x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (u x * divergenceG (I := I) g X x) * a α x
          ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    have hterm_local_int : Integrable
        (fun x => (u x * divergenceG (I := I) g X x) * a α x)
        (chartLocalMeasure (I := I) g α) :=
      integrable_chartLocalMeasure_of_compactSupport_subset_chartSource
        (I := I) g α (hterm_cont α) (hterm_cs α) (hterm_supp α)
    exact (integrable_riemannianVolumeMeasure_and_integral_eq_chartLocalMeasure
      (I := I) (M := M) g α
      hterm_local_int (hterm_cs α) (hterm_supp α)).2
  have hterm_local : ∀ α ∈ S,
      ∫ x, (u x * divergenceG (I := I) g X x) * a α x
          ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, localDivergence (I := I) g α X x * φ α x
          ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hxα : x ∈ (chartAt H α).source
    · change (u x * divergenceG (I := I) g X x) * a α x =
        localDivergence (I := I) g α X x * φ α x
      rw [voss_weyl_divergence_formula (I := I) g α X hxα]
      simp only [φ]
      ring
    · have hxnot : x ∉ tsupport (ρ α : M → ℝ) := fun hx => hxα (hρsub α hx)
      have hρzero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hxnot (subset_tsupport _ hne)
      simp only [a, φ, hρzero, mul_zero, zero_mul]
  have hibp : ∀ α ∈ S,
      ∫ x, localDivergence (I := I) g α X x * φ α x
          ∂(chartLocalMeasure (I := I) g α) =
        -∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    exact chart_local_ibp_lip (I := I) g α X (hD α) (hφ_cs α) (hφ_supp α)
  have hAct_supp (α : M) :
      tsupport (tangentSectionAction (I := I) X (φ α)) ⊆
        (chartAt H α).source :=
    (tsupport_tangentSectionAction_subset_right (I := I) X (φ α)).trans
      (hφ_supp α)
  have hAct_cs (α : M) :
      HasCompactSupport (tangentSectionAction (I := I) X (φ α)) :=
    (hφ_cs α).mono' ((subset_tsupport _).trans
      (tsupport_tangentSectionAction_subset_right (I := I) X (φ α)))
  have htrans : ∀ α ∈ S,
      Integrable (tangentSectionAction (I := I) X (φ α))
          (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    exact integrable_riemannianVolumeMeasure_and_integral_eq_chartLocalMeasure
      (I := I) (M := M) g α
      (tangent_lip_int (I := I) g α X (hD α) (hφ_cs α) (hφ_supp α))
      (hAct_cs α) (hAct_supp α)
  have hAct_int : ∀ α ∈ S, Integrable
      (tangentSectionAction (I := I) X (φ α))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    fun α hα => (htrans α hα).1
  have hact_ae :
      (fun x => ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      tangentSectionAction (I := I) X u := by
    filter_upwards [hφ_mdiff_all] with x hmdiff
    by_cases hXx : X x = (0 : TangentSpace I x)
    · calc
        ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x = 0 :=
          Finset.sum_eq_zero (fun α _ =>
            tangentSectionAction_zero_of_X_zero (I := I) X (φ α) hXx)
        _ = tangentSectionAction (I := I) X u x :=
          (tangentSectionAction_zero_of_X_zero (I := I) X u hXx).symm
    · have hxK : x ∈ K := by
        apply subset_tsupport
        exact hXx
      have hcomm := tangentSectionAction_finset_sum (I := I) X S φ x
        (fun α hα => hmdiff α hα)
      calc
        ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x =
            tangentSectionAction (I := I) X (∑ α ∈ S, φ α) x := hcomm.symm
        _ = tangentSectionAction (I := I) X u x := by
          unfold tangentSectionAction
          rw [Filter.EventuallyEq.mfderiv_eq (hφ_sum_nhds x hxK)]
          rfl
  have hsum_int : Integrable
      (fun x => ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_finsetSum S hAct_int
  have htu_int : Integrable (tangentSectionAction (I := I) X u)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hsum_int.congr hact_ae
  have hint_sum :
      ∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    calc
      _ = ∫ x, ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        (integral_finsetSum (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          S hAct_int).symm
      _ = _ := integral_congr_ae hact_ae
  have hdiv_eq :
      ∫ x, u x * divergenceG (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    calc
      _ = ∑ α ∈ S, ∫ x, (u x * divergenceG (I := I) g X x) * a α x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := h_rhs_decomp
      _ = ∑ α ∈ S, ∫ x, (u x * divergenceG (I := I) g X x) * a α x
          ∂(chartLocalMeasure (I := I) g α) :=
        Finset.sum_congr rfl hterm_chart
      _ = ∑ α ∈ S, ∫ x, localDivergence (I := I) g α X x * φ α x
          ∂(chartLocalMeasure (I := I) g α) :=
        Finset.sum_congr rfl hterm_local
      _ = ∑ α ∈ S, -∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(chartLocalMeasure (I := I) g α) :=
        Finset.sum_congr rfl hibp
      _ = ∑ α ∈ S, -∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        refine Finset.sum_congr rfl ?_
        intro α hα
        rw [(htrans α hα).2]
      _ = -(∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
        rw [Finset.sum_neg_distrib]
      _ = -∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        rw [hint_sum]
  refine ⟨htu_int, ?_⟩
  linarith

private theorem global_lip_ibp
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {u : M → ℝ} {L B : NNReal}
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) :
    Integrable (tangentSectionAction (I := I) X u)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      ∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, u x * divergenceG (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let ρ : SmoothPartitionOfUnity M I M (Set.univ : Set M) :=
    chartAtlasPOU I M
  let S : Finset M := chartAtlasPOUFinset (I := I) (M := M)
  let φ : M → M → ℝ := fun α x => ρ α x * u x
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) := by
    simpa only [ρ] using chartAtlasPOU_isSubordinate I M
  have hu_cont : Continuous u := intrinsic_lip_cont (I := I) g hu
  have hdiv_cont : Continuous (divergenceG (I := I) g X) :=
    (divergence_g_contMDiff (I := I) g X).continuous
  have : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hudiv_int : Integrable (fun x => u x * divergenceG (I := I) g X x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (hu_cont.mul hdiv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hφ_support (α : M) : tsupport (φ α) ⊆ (chartAt H α).source := by
    exact tsupport_mul_subset_left.trans (hρsub α)
  have hφ_compact (α : M) : HasCompactSupport (φ α) :=
    HasCompactSupport.of_compactSpace _
  have hφ_lip (α : M) : ∃ D : NNReal,
      LipschitzWith D (chartPullZero (I := I) α (φ α)) := by
    obtain ⟨C, hraw⟩ := chart_pou_lip (I := I) g α hu hB
    apply pull_lipschitz_of_chartPushedRaw (I := I) α (φ α)
    simpa only [φ, ρ] using hraw
  let D : M → NNReal := fun α => Classical.choose (hφ_lip α)
  have hD (α : M) : LipschitzWith (D α)
      (chartPullZero (I := I) α (φ α)) :=
    Classical.choose_spec (hφ_lip α)
  have hstep_a :
      ∑ α ∈ S, ∫ x,
          (u x * divergenceG (I := I) g X x) * ρ α x
            ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, u x * divergenceG (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa only [S, ρ] using chart_sum_integral (I := I) (M := M) g _ hudiv_int
  have hstep_b : ∀ α ∈ S,
      ∫ x, (u x * divergenceG (I := I) g X x) * ρ α x
          ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, localDivergence (I := I) g α X x * φ α x
          ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ (chartAt H α).source
    · simp only [φ]
      rw [voss_weyl_divergence_formula (I := I) g α X hx]
      ring
    · have hρzero : ρ α x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        exact fun h => hx (hρsub α h)
      simp only [φ, hρzero, mul_zero, zero_mul]
  have hstep_c : ∀ α ∈ S,
      ∫ x, localDivergence (I := I) g α X x * φ α x
          ∂(chartLocalMeasure (I := I) g α) =
        -∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    exact chart_local_ibp_lip (I := I) g α X (hD α)
      (hφ_compact α) (hφ_support α)
  have htrans : ∀ α ∈ S,
      Integrable (tangentSectionAction (I := I) X (φ α))
          (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    apply chart_int_eq_global (I := I) (M := M) g α
      (tangent_lip_int (I := I) g α X (hD α) (hφ_compact α) (hφ_support α))
    intro x hx
    have hxt : x ∉ tsupport (φ α) := fun h => hx (hφ_support α h)
    have hev : (φ α) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      change Filter.EventuallyEq (nhds x) (φ α) (0 : M → ℝ)
      exact notMem_tsupport_iff_eventuallyEq.mp hxt
    have hmfderiv_zero : mfderiv I 𝓘(ℝ) (φ α) x = 0 := by
      rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_const]
      rfl
    unfold tangentSectionAction
    rw [hmfderiv_zero]
    rfl
  have heach : ∀ α ∈ S, Integrable
      (tangentSectionAction (I := I) X (φ α))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    fun α hα => (htrans α hα).1
  have hsumφ : (∑ α ∈ S, φ α) = u := by
    funext x
    simp only [Finset.sum_apply, φ, ← Finset.sum_mul]
    have hone : ∑ α ∈ S, ρ α x = 1 := by
      simpa only [S, ρ] using
        chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
    rw [hone, one_mul]
  have hact_ae : (fun x => ∑ α ∈ S,
      tangentSectionAction (I := I) X (φ α) x) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      tangentSectionAction (I := I) X u := by
    filter_upwards [ae_mdiff_of_lip (I := I) g hu hB] with x hux
    have hφdiff : ∀ α ∈ S, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ α) x := by
      intro α _
      unfold φ
      have hmul := ((ρ α).contMDiff.mdifferentiableAt (by simp)).mul hux
      have hfun : ((↑(ρ α) : M → ℝ) * u) = fun y : M => (ρ α) y * u y := by
        rfl
      rw [← hfun]
      exact hmul
    have hcomm := tangentSectionAction_finset_sum (I := I) X S φ x hφdiff
    rw [hsumφ] at hcomm
    exact hcomm.symm
  have hsum_int : Integrable (fun x => ∑ α ∈ S,
      tangentSectionAction (I := I) X (φ α) x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_finsetSum S heach
  have htu_int : Integrable (tangentSectionAction (I := I) X u)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hsum_int.congr hact_ae
  have hint_sum :
      ∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    calc
      _ = ∫ x, ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        (integral_finsetSum (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          S heach).symm
      _ = _ := integral_congr_ae hact_ae
  have hdiv_eq :
      ∫ x, u x * divergenceG (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    calc
      _ = ∑ α ∈ S, ∫ x,
          (u x * divergenceG (I := I) g X x) * ρ α x
            ∂(chartLocalMeasure (I := I) g α) := hstep_a.symm
      _ = ∑ α ∈ S, ∫ x, localDivergence (I := I) g α X x * φ α x
            ∂(chartLocalMeasure (I := I) g α) :=
        Finset.sum_congr rfl hstep_b
      _ = ∑ α ∈ S, -∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α) :=
        Finset.sum_congr rfl hstep_c
      _ = ∑ α ∈ S, -∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        refine Finset.sum_congr rfl ?_
        intro α hα
        rw [(htrans α hα).2]
      _ = -(∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
        rw [Finset.sum_neg_distrib]
      _ = -∫ x, tangentSectionAction (I := I) X u x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        rw [hint_sum]
  refine ⟨htu_int, ?_⟩
  linarith

theorem weak_grad_of_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {L B : NNReal}
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) :
    HasWeakRiemannianGradLp (I := I) (M := M) g u
      (fun x => (gradFun (I := I) g u x : E)) := by
  refine ⟨?_, ?_⟩
  · intro Y
    have hint := (global_lip_ibp (I := I) g Y hu hB).1
    apply hint.aestronglyMeasurable.congr
    exact Filter.Eventually.of_forall fun x => by
      simpa only [tangentSectionAction] using
        (inner_gradFun (I := I) g u x (Y x)).symm
  · intro X _
    have hibp := (global_lip_ibp (I := I) g X hu hB).2
    calc
      ∫ x, g.inner x (gradFun (I := I) g u x) (X x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simpa only [tangentSectionAction] using
            inner_gradFun (I := I) g u x (X x)
      _ = _ := hibp

omit [IsManifold I ∞ M] in
theorem grad_norm_aesm
    [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (hu : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      MDifferentiableAt I 𝓘(ℝ, ℝ) u x) :
    AEStronglyMeasurable
      (fun x : M => Real.sqrt
        (g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let source : M → Set M := fun α => (chartAt H α).source
  let gram : M → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → M → ℝ :=
    fun α i j => (source α).piecewise
      (fun x => chartInvGramMatrix (I := I) g α x i j) (fun _ => 0)
  let part : M → Fin (Module.finrank ℝ E) → M → ℝ := fun α i x =>
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α u)
      (extChartAtExt (I := I) α x)
  let q : M → M → ℝ := fun α x =>
    ∑ i, ∑ j, gram α i j x * part α j x * part α i x
  let ρ : M → M → ℝ := fun α x => (chartAtlasPOU I M α) x
  let S : Finset M := chartAtlasPOUFinset (I := I) (M := M)
  let qsum : M → ℝ := fun x => ∑ α ∈ S, ρ α x * q α x
  have hsource (α : M) : MeasurableSet (source α) := by
    simpa only [source] using (chartAt H α).open_source.measurableSet
  have hgram (α : M) (i j : Fin (Module.finrank ℝ E)) :
      Measurable (gram α i j) := by
    have hcont : ContinuousOn
        (fun x : M => chartInvGramMatrix (I := I) g α x i j) (source α) := by
      have h :=
        (chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j).continuousOn
      simpa only [source, trivializationAt_baseSet_eq_chartAt_source] using h
    exact ContinuousOn.measurable_piecewise hcont continuous_const.continuousOn
      (hsource α)
  have hpart (α : M) (i : Fin (Module.finrank ℝ E)) :
      Measurable (part α i) := by
    unfold part DifferentialGeometry.Tensor.Coordinates.partialDeriv
    exact (measurable_fderiv_apply_const ℝ
      (scalarOnE (I := I) α u) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)).comp
        (extChartAtExt_measurable (I := I) (α := α))
  have hq (α : M) : Measurable (q α) := by
    unfold q
    refine Finset.measurable_fun_sum Finset.univ fun i _ => ?_
    refine Finset.measurable_fun_sum Finset.univ fun j _ => ?_
    exact ((hgram α i j).mul (hpart α j)).mul (hpart α i)
  have hρ (α : M) : Measurable (ρ α) := by
    exact ((chartAtlasPOU I M α).contMDiff.continuous).measurable
  have hqsum : Measurable qsum := by
    unfold qsum
    refine Finset.measurable_fun_sum S fun α _ => ?_
    exact (hρ α).mul (hq α)
  have hqsum_eq : ∀ᵐ x ∂(riemannianVolumeMeasure (I := I) (M := M) g),
      qsum x = g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x) := by
    filter_upwards [hu] with x hx
    have hterm : ∀ α ∈ S,
        ρ α x * q α x = ρ α x *
          g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x) := by
      intro α _
      by_cases hρα : ρ α x = 0
      · simp only [hρα, zero_mul]
      · have hxs : x ∈ source α := by
          apply (chartAtlasPOU_isSubordinate I M) α
          apply subset_closure
          simpa only [Function.mem_support, ρ] using hρα
        congr 1
        unfold q gram part
        simp only [Set.piecewise_eq_of_mem (source α) _ _ hxs]
        rw [extChartAtExt_apply_of_mem (I := I) (α := α)]
        · exact (grad_norm_sq_chart (I := I) g α hx hxs).symm
        · simpa only [source] using hxs
    calc
      qsum x = ∑ α ∈ S, ρ α x * q α x := rfl
      _ = ∑ α ∈ S, ρ α x *
          g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x) :=
        Finset.sum_congr rfl hterm
      _ = (∑ α ∈ S, ρ α x) *
          g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x) := by
        rw [Finset.sum_mul]
      _ = _ := by
        have hone : ∑ α ∈ S, ρ α x = 1 := by
          simpa only [S, ρ] using
            chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
        rw [hone, one_mul]
  apply (Real.continuous_sqrt.measurable.comp hqsum).aestronglyMeasurable.congr
  filter_upwards [hqsum_eq] with x hx
  simpa only [Function.comp_apply] using congrArg Real.sqrt hx

theorem memW1p_of_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : ENNReal)
    {u : M → ℝ} {L B : NNReal}
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) :
    MemW1pIntrinsicLp (I := I) (M := M) g p u := by
  have : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  refine ⟨MemLp.of_bound (intrinsic_lip_cont (I := I) g hu).aestronglyMeasurable
      (B : ℝ) ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x => by
      exact_mod_cast hB x
  · refine ⟨(fun x => (gradFun (I := I) g u x : E)),
      weak_grad_of_lip (I := I) g hu hB, ?_⟩
    refine MemLp.of_bound (grad_norm_aesm (I := I) g
      (ae_mdiff_of_lip (I := I) g hu hB)) (L : ℝ) ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Geometry.Riemannian.grad_norm_le_lip_all (I := I) g hu

end IntrinsicLp
end Sobolev
end Analysis
end DifferentialGeometry
