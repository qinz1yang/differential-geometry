import DifferentialGeometry.Analysis.Calculus.MapConvergence.LocalPullback
import DifferentialGeometry.Analysis.Calculus.MapConvergence.LocalGerm
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import DifferentialGeometry.Topology.Manifold.OpenSubtype

section

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology
namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)]

theorem pullbackMetricCoefficients_convergence_of_chart_convergence
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (Φ : ∀ k, PartialDiffeomorph 𝓘(ℝ, E) I E (M k) ∞)
    (hsource : ∀ k, (Φ k).source = V)
    (P : ∀ k, E → M k) (hP : ∀ k, ContMDiffOn 𝓘(ℝ, E) I ∞ (P k) U)
    (hcapture : ∀ K, IsCompact K → K ⊆ U →
      ∀ᶠ k in atTop, MapsTo (P k) K (Φ k).target)
    (hcoord : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (Φ k).symm ∘ P k) id)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : CheegerGromovCompactness.MapCInfConvergenceOnCompacts V
      (fun k => pullbackMetricCoefficients (g k) (Φ k)) B)
    (hBC : ContDiffOn ℝ ∞ B V) :
    CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => pullbackMetricCoefficients (g k) (P k)) B := by
  let A : ℕ → E → E := fun k => (Φ k).symm ∘ P k
  have hlocal : ∀ K, IsCompact K → K ⊆ U →
      ∃ W, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
        ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W ∧ MapsTo (A k) W V := by
    intro K hK hKU
    obtain ⟨W, hW, hKW, hWU, hcompact⟩ :=
      exists_open_between_and_isCompact_closure hK hU hKU
    have hWU' : W ⊆ U := subset_closure.trans hWU
    refine ⟨W, hW, hKW, hWU', ?_⟩
    filter_upwards [hcapture (closure W) hcompact hWU] with k hk
    have hmap : MapsTo (P k) W (Φ k).target := hk.mono_left subset_closure
    refine ⟨((Φ k).contMDiffOn_invFun.comp ((hP k).mono hWU') hmap).contDiffOn, ?_⟩
    intro z hz
    rw [← hsource k]
    exact (Φ k).toOpenPartialHomeomorph.map_target (hmap hz)
  have hBkc : ∀ k, ContDiffOn ℝ ∞ (pullbackMetricCoefficients (g k) (Φ k)) V := by
    intro k
    exact contDiffOn_pullback_metric_coefficients (g k) hV
      (by simpa only [hsource k] using (Φ k).contMDiffOn_toFun)
  have hconv := hcoord.pullbackForm_comp_fderiv_locally hV hB hlocal
    contDiff_id.contDiffOn hBkc hBC hUV
  apply hconv.congr_eventually_locally
  · intro K hK hKU
    obtain ⟨W, hW, hKW, hWU, hcompact⟩ :=
      exists_open_between_and_isCompact_closure hK hU hKU
    have hWU' : W ⊆ U := subset_closure.trans hWU
    refine ⟨W, hW, hKW, hWU', ?_⟩
    filter_upwards [hcapture (closure W) hcompact hWU] with k hk
    intro z hz
    ext v w
    exact (pullbackMetricCoefficients_fderiv_symm (g k) (Φ k)
      (((hP k).contMDiffAt (hU.mem_nhds (hWU' hz))).mdifferentiableAt (by simp))
      (hk (subset_closure hz)) v w).symm
  · intro z _
    ext v w
    simp

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology
namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

theorem pullbackMetricCoefficients_convergence_of_local_inclusion
    (U : TopologicalSpace.Opens E) {W : Set E} (hW : IsOpen W) (hUW : (U : Set E) ⊆ W)
    (j : U → Q) (hj : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ j)
    (jbar : E → Q) (hjbar : ∀ z : U, jbar z = j z)
    (V : TopologicalSpace.Opens Q)
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (gQ : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (Φ : ∀ k, PartialDiffeomorph 𝓘(ℝ, E) I E (M k) ∞)
    (hsource : ∀ k, (Φ k).source = W)
    (F : ∀ k, Q → M k) (hF : ∀ k, ContMDiffOn 𝓘(ℝ, E) I ∞ (F k) V)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : CheegerGromovCompactness.MapCInfConvergenceOnCompacts W
      (fun k => pullbackMetricCoefficients (g k) (Φ k)) B)
    (hBC : ContDiffOn ℝ ∞ B W)
    (hmetric : ∀ (z : U) (v w : E),
      gQ.inner (j z) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) j z v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) j z w) = B z v w)
    (hcapture : ∀ K, IsCompact K → K ⊆ Subtype.val '' (j ⁻¹' (V : Set Q)) →
      ∀ᶠ k in atTop, MapsTo (F k ∘ jbar) K (Φ k).target)
    (hcoord : CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Subtype.val '' (j ⁻¹' (V : Set Q)))
      (fun k => (Φ k).symm ∘ (F k ∘ jbar)) id) :
    CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Subtype.val '' (j ⁻¹' (V : Set Q)))
      (fun k => pullbackMetricCoefficients (g k) (F k ∘ jbar))
      (pullbackMetricCoefficients gQ jbar) := by
  let D : Set E := Subtype.val '' (j ⁻¹' (V : Set Q))
  have hD : IsOpen D := U.isOpen.isOpenMap_subtype_val _ (V.isOpen.preimage hj.continuous)
  have hDU : D ⊆ U := by
    rintro z ⟨x, _, rfl⟩
    exact x.property
  have hjbar' : (fun z : U => jbar z) = j := funext hjbar
  have hjbarC : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ jbar U := by
    intro z hz
    have h := hj.contMDiffAt (x := (⟨z, hz⟩ : U))
    rw [← hjbar'] at h
    exact (contMDiffAt_subtype_iff.mp h).contMDiffWithinAt
  have hjbarV : MapsTo jbar D V := by
    rintro z ⟨x, hx, rfl⟩
    change jbar (x : E) ∈ V
    rw [hjbar x]
    exact hx
  have hcomp : ∀ k, ContMDiffOn 𝓘(ℝ, E) I ∞ (F k ∘ jbar) D :=
    fun k => (hF k).comp (hjbarC.mono hDU) hjbarV
  have hconv := pullbackMetricCoefficients_convergence_of_chart_convergence
    hD hW (hDU.trans hUW) g Φ hsource (fun k => F k ∘ jbar) hcomp
    hcapture hcoord hB hBC
  apply hconv.congr_eventually hD (Filter.Eventually.of_forall fun _ _ _ => rfl)
  rintro z ⟨x, hx, rfl⟩
  ext v w
  have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) j x =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) jbar (x : E) := by
    rw [← hjbar']
    exact DifferentialGeometry.mfderiv_restrict_open jbar U x
  change gQ.inner (jbar (x : E))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) jbar (x : E) v)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) jbar (x : E) w) = _
  rw [← hd]
  rw [hjbar x]
  exact hmetric x v w

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
open scoped Manifold Topology ContDiff
namespace DifferentialGeometry.Geometry

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem pullbackMetricCoefficients_eq_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) {f h : V → M} {x : V}
    (heq : f =ᶠ[𝓝 x] h) :
    pullbackMetricCoefficients g f x = pullbackMetricCoefficients g h x := by
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, V)) (I' := I)
  ext v w
  rw [pullbackMetricCoefficients_apply, pullbackMetricCoefficients_apply, hd]
  rw [heq.eq_of_nhds]

theorem pullbackMetricCoefficients_eventuallyEq_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) {f h : V → M} {x : V}
    (heq : f =ᶠ[𝓝 x] h) :
    pullbackMetricCoefficients g f =ᶠ[𝓝 x] pullbackMetricCoefficients g h :=
  heq.eventuallyEq_nhds.mono fun _ hz => pullbackMetricCoefficients_eq_of_eventuallyEq g hz

end DifferentialGeometry.Geometry


end

section

set_option autoImplicit false
open Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry

variable {V E H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)]

theorem pullbackMetricCoefficients_convergence_congr_eventually_germ
    {U : Set V} (g : ∀ k, SmoothRiemannianMetric I (M k))
    {P Q : ∀ k, V → M k} {B : V → V →L[ℝ] V →L[ℝ] ℝ}
    (h : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => pullbackMetricCoefficients (g k) (P k)) B)
    (heq : ∀ K, IsCompact K → K ⊆ U →
      ∀ᶠ k in atTop, ∀ z ∈ K, Q k =ᶠ[𝓝 z] P k) :
    CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => pullbackMetricCoefficients (g k) (Q k)) B := by
  apply h.congr_eventually_germ
  · intro K hK hKU
    filter_upwards [heq K hK hKU] with k hk
    intro z hz
    exact pullbackMetricCoefficients_eventuallyEq_of_eventuallyEq (g k) (hk z hz)
  · exact fun _ _ => Filter.EventuallyEq.rfl

end DifferentialGeometry.Geometry


end
