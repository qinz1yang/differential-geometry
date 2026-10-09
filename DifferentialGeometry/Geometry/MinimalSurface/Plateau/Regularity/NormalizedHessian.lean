import DifferentialGeometry.Analysis.Calculus.Composition.VanishingHessian
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientNormalHessian
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientLeadingPlane
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientZero

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

/-- The supplied coordinate of the same original Morrey disk carries its normal
height to a `C²` height at the branch center. This intermediate receiving
interface names the inverse-Hessian bound explicitly; the inverse adaptation
must supply it from the bound on the same forward coordinate. -/
theorem DiskRegularity.ConsumerAudit.morrey_normalized_height_hessian_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1)
    {m : ℕ} (hm : 1 ≤ m) {B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)}
    (hB : ContDiffAt ℝ 1 B a) (hBne : B a ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient (diskExtension u a) (diskExtension u) i z) =
        (z - a) ^ m • B z)
    {N : E}
    (hN : chartLeadingPlaneProjection g (diskExtension u a) (diskExtension u a)
      (B a) N = 0)
    (e : OpenPartialHomeomorph ℂ ℂ) (hae : a ∈ e.source) (hea : e a = 0)
    (hei1 : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    (hei2 : ContDiffOn ℝ 2 (e.symm : ℂ → ℂ) (e.target \ {(0 : ℂ)}))
    (heiBound : ∃ K > 0, ∀ᶠ w in 𝓝[≠] (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ (e.symm : ℂ → ℂ)) w‖ ≤ K)
    (hepower :
      let p := diskExtension u a
      let proj := chartLeadingPlaneProjection g p p (B a)
      let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (diskExtension u z))
      ∀ z ∈ e.source, F z = F a + (e z) ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) :
    let p := diskExtension u a
    let Q := chartGramBilin g p p
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (diskExtension u z)
    let F : ℂ → ℂ := fun z => chartLeadingPlaneProjection g p p (B a) (X z)
    let H : ℂ → ℝ := fun w => Q N (X (e.symm w) - X a)
    (∀ w ∈ e.target, F (e.symm w) = F a + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) ∧
      ContDiffAt ℝ 2 H 0 ∧ fderiv ℝ H 0 = 0 ∧
      fderiv ℝ (fderiv ℝ H) 0 = 0 ∧
      ∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
        ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m := by
  let p := diskExtension u a
  let Q := chartGramBilin g p p
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (diskExtension u z)
  let h : ℂ → ℝ := fun z => Q N (X z)
  have hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u)
      (ball (0 : ℂ) 1) := hu.smoothInterior.of_le (by norm_num)
  have hUa := hU.contMDiffAt (isOpen_ball.mem_nhds ha)
  have hsrc : diskExtension u a ∈ (chartAt E p).source := mem_chart_source E p
  have hnull := chartComplexGradient_leading_isotropic g isOpen_ball hU hu.conformal
    ha hsrc hB.continuousAt hfactor
  have hzero := chartLeadingPlaneProjection_normal_coefficient_eq_zero g
    hsrc hBne hnull hN
  obtain ⟨C, hC, hHess⟩ := chartComplexGradient_normal_hessian_bound
    hUa hsrc hB hfactor (Q N) hzero
  have hU2 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 2 (diskExtension u) a :=
    (hu.smoothInterior.contMDiffAt (isOpen_ball.mem_nhds ha)).of_le (by norm_num)
  have hX : ContDiffAt ℝ 2 X a :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 2) hsrc).comp a hU2).contDiffAt
  have hh : ContDiffAt ℝ 2 h a := (Q N).contDiff.contDiffAt.comp a hX
  have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hm)
  have hgradzero (i : Fin (Module.finrank ℝ E)) :
      chartComplexGradient p (diskExtension u) i a = 0 := by
    have hi := congrFun hfactor.self_of_nhds i
    simpa only [sub_self, zero_pow hm0, zero_smul, Pi.zero_apply] using hi
  have hDu := (chartComplexGradient_eq_zero_iff_mfderiv_eq_zero hUa hsrc).mp hgradzero
  have hDX : fderiv ℝ X a = 0 := by
    ext v
    have hc := mfderiv_comp_apply a
      ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) hsrc).mdifferentiableAt
        (by norm_num)) (hUa.mdifferentiableAt (by norm_num)) v
    rw [mfderiv_eq_fderiv] at hc
    change fderiv ℝ X a v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) (diskExtension u a)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) a v) at hc
    rw [hDu] at hc
    change fderiv ℝ X a v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) (diskExtension u a)
        (0 : E) at hc
    exact hc.trans (map_zero _)
  have hDh : fderiv ℝ h a = 0 := by
    have hd : HasFDerivAt h ((Q N).comp (fderiv ℝ X a)) a :=
      (Q N).hasFDerivAt.comp a (hX.differentiableAt (by norm_num)).hasFDerivAt
    rw [hd.fderiv, hDX, ContinuousLinearMap.comp_zero]
  have h0t : (0 : ℂ) ∈ e.target := by simpa only [hea] using e.map_source hae
  have hi0 : e.symm 0 = a := by rw [← hea]; exact e.left_inv hae
  have hσ : ContDiffAt ℝ 1 (e.symm : ℂ → ℂ) 0 :=
    hei1.contDiffAt (e.open_target.mem_nhds h0t)
  have hσ2 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ContDiffAt ℝ 2 (e.symm : ℂ → ℂ) w := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds h0t),
      self_mem_nhdsWithin] with w hw hw0
    exact hei2.contDiffAt ((e.open_target.sdiff isClosed_singleton).mem_nhds ⟨hw, hw0⟩)
  have htransport := DifferentialGeometry.Analysis.contDiffAt_comp_of_vanishing_hessian
    hm hh hDh ⟨C, hC, hHess.mono fun _ hz => hz.2⟩ hσ hi0 hσ2 heiBound
  refine ⟨?_, ?_⟩
  · intro w hw
    have hp := hepower (e.symm w) (e.map_target hw)
    rw [e.right_inv hw] at hp
    exact hp
  · simpa only [h, map_sub] using htransport
