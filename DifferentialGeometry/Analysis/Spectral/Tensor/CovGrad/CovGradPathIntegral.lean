import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Interval

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (covGrad covGrad_toSection_apply
  pathIntegralCoeffField pathIntegralFib pathIntegralCoeffField_toSection
  pathIntegralCoeffField_toModel pathIntegralFib_toModel tensorCovDerivAt tensorCovDerivAt_def)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (contMDiffOn_clm_section_of_pointwise_joint_manifold_time
  jointContMDiff_toModel_continuous_slice)
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.TensorRSNabla

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance tensorRSModelNormedAddCommGroup_local (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup r s

private local instance tensorRSModelNormedSpace_local (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace r s

private theorem intervalIntegrable_continuousLinearMap_apply_local
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ℝ → V →L[ℝ] W) (hf : ContinuousOn f (Set.uIcc (0 : ℝ) 1)) (v : V) :
    IntervalIntegrable (fun t : ℝ => f t v) volume 0 1 :=
  ((ContinuousLinearMap.apply ℝ W v).continuous.comp_continuousOn hf).intervalIntegrable

private theorem intervalIntegrable_finset_sum_local
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ι → ℝ → V) (hf : ∀ i, IntervalIntegrable (f i) volume 0 1) :
    IntervalIntegrable (fun t : ℝ => ∑ i, f i t) volume 0 1 := by
  have hsum := IntervalIntegrable.sum (Finset.univ : Finset ι) (fun i _ => hf i)
  have heq : (fun t : ℝ => ∑ i, f i t) = ∑ i, f i := by
    funext t
    rw [Finset.sum_apply]
  rw [heq]
  exact hsum

private theorem finset_sum_eq_intervalIntegral_sum_local
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : ι → V) (f : ι → ℝ → V)
    (hcomm : ∀ i, a i = ∫ t in (0 : ℝ)..1, f i t)
    (hf : ∀ i, IntervalIntegrable (f i) volume 0 1) :
    (∑ i, a i) = ∫ t in (0 : ℝ)..1, ∑ i, f i t := by
  rw [intervalIntegral.integral_finset_sum]
  · exact Finset.sum_congr rfl (fun i _ => hcomm i)
  · exact fun i _ => hf i

section PathIntegralComm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private theorem toModel_section_intervalIntegrable
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) :
    IntervalIntegrable
      (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x)) volume 0 1 :=
  ((jointContMDiff_toModel_continuous_slice (I := I) g₀ r s Φ S hjoint x).mono
    hSI).intervalIntegrable

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M]
    in
private theorem chartRepr_pathIntegralCoeffField_eq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (α b : M) :
    DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection
          y) b =
      ∫ t in (0 : ℝ)..1,
        DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => (Φ t).toSection y) b := by
  set L : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b).comp
      (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) r s b).symm.toContinuousLinearMap
    with hL
  have hIIm : IntervalIntegrable
      (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection b)) volume 0 1 :=
    toModel_section_intervalIntegrable (I := I) g₀ r s Φ S hSI hjoint b
  rw [DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply]
  have hLHS : (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection b) =
      L (∫ t in (0 : ℝ)..1, TensorRSSpace.toModel ((Φ t).toSection b)) := by
    rw [hL, ContinuousLinearMap.comp_apply]
    congr 1
  rw [hLHS, ← ContinuousLinearMap.intervalIntegral_comp_comm L hIIm]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply, hL,
    ContinuousLinearMap.comp_apply]
  congr 1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private theorem chartRepr_comp_symm_jointContDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (F q.1).toSection z) ((extChartAt I α).symm q.2))
      (S ×ˢ (extChartAt I α).target) := by
  intro q hq
  obtain ⟨hqS, hqtgt⟩ := hq
  exact chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s F S α hF hqS hqtgt

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private theorem fderiv_chartRepr_jointContinuousOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (_hS : IsOpen S) (α : M) {U : Set E} (hU : IsOpen U)
    (hUtgt : U ⊆ (extChartAt I α).target)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn
      (fun q : ℝ × E => fderiv ℝ (fun y : E =>
          DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
            (I := I) r s α (fun z : M => (F q.1).toSection z) ((extChartAt I α).symm y)) q.2)
      (S ×ˢ U) := by
  intro q hq
  obtain ⟨hqS, hqU⟩ := hq
  set G : ℝ × E → E → TensorRSModel r s ℝ E :=
    fun p y => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
      (I := I) r s α (fun z : M => (F p.1).toSection z) ((extChartAt I α).symm y) with hG
  have huncurry : ContDiffWithinAt ℝ ∞
      (Function.uncurry (fun (p : ℝ × E) (y : E) => G p y))
      ((S ×ˢ U) ×ˢ U) ((q, (fun p : ℝ × E => p.2) q)) := by
    have hbrick : ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => G p p.2)
        (S ×ˢ (extChartAt I α).target) q :=
      chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s F S α hF hqS (hUtgt hqU)
    have hproj : ContDiffWithinAt ℝ ∞
        (fun w : (ℝ × E) × E => (w.1.1, w.2))
        ((S ×ˢ U) ×ˢ U) (q, q.2) :=
      (contDiffWithinAt_fst.fst).prodMk contDiffWithinAt_snd
    refine hbrick.comp (q, q.2) hproj ?_
    rintro ⟨⟨t, y⟩, y'⟩ ⟨⟨ht, _⟩, hy'⟩
    exact ⟨ht, hUtgt hy'⟩
  have hg : ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => p.2) (S ×ˢ U) q := contDiffWithinAt_snd
  have hud : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
  have hsub : (S ×ˢ U) ⊆ (fun p : ℝ × E => p.2) ⁻¹' U := by intro p hp; exact hp.2
  have hfdw := ContDiffWithinAt.fderivWithin huncurry hg hud h_le ⟨hqS, hqU⟩ hsub
  have hcont := hfdw.continuousWithinAt
  refine hcont.congr ?_ ?_
  · intro p hp
    exact (fderivWithin_of_isOpen hU hp.2).symm
  · exact (fderivWithin_of_isOpen hU hqU).symm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M]
    in
private theorem hasFDerivAt_chartRepr_pathIntegral
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (α : M) {y₀ : E} (hy₀ : y₀ ∈ interior ((extChartAt I α).target : Set E)) :
    HasFDerivAt
      (fun y : E => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s α
        (fun z : M =>
          (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection z)
        ((extChartAt I α).symm y))
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y : E =>
          DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
            (I := I) r s α (fun z : M => (Φ t).toSection z) ((extChartAt I α).symm y)) y₀)
      y₀ := by
  classical
  set Gfn : ℝ → E → TensorRSModel r s ℝ E :=
    fun t y => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
      (I := I) r s α (fun z : M => (Φ t).toSection z) ((extChartAt I α).symm y) with hGfn
  set F : E → ℝ → TensorRSModel r s ℝ E := fun y t => Gfn t y with hF
  set F' : E → ℝ → E →L[ℝ] TensorRSModel r s ℝ E :=
    fun y t => fderiv ℝ (Gfn t) y with hF'
  have hInt_open : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
  have hInt_sub : interior ((extChartAt I α).target : Set E) ⊆ (extChartAt I α).target :=
    interior_subset
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hInt_open y₀ hy₀
  set ε2 : ℝ := ε / 2 with hε2
  have hε2_pos : 0 < ε2 := by positivity
  have hclosed_sub : Metric.closedBall y₀ ε2 ⊆ interior ((extChartAt I α).target : Set E) := by
    intro y hy
    apply hε_ball
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hy
    calc dist y y₀ ≤ ε2 := hy
      _ < ε := by rw [hε2]; linarith
  have hball_sub : Metric.ball y₀ ε2 ⊆ interior ((extChartAt I α).target : Set E) :=
    (Metric.ball_subset_closedBall).trans hclosed_sub
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall y₀ ε2) :=
    isCompact_Icc.prod (isCompact_closedBall y₀ ε2)
  have hfderiv_cont : ContinuousOn
      (fun q : ℝ × E => F' q.2 q.1)
      (S ×ˢ interior ((extChartAt I α).target : Set E)) := by
    have := fderiv_chartRepr_jointContinuousOn (I := I) g₀ r s Φ S hS α
      (U := interior ((extChartAt I α).target : Set E)) hInt_open hInt_sub hjoint
    exact this
  have hfderiv_cont_swap : ContinuousOn
      (fun q : ℝ × E => F' q.2 q.1)
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall y₀ ε2) := by
    refine hfderiv_cont.mono ?_
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    exact ⟨hSI ((Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)).symm ▸ ht), hclosed_sub hy⟩
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hfderiv_cont_swap
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Metric.closedBall y₀ ε2, ‖F' y t‖ ≤ C := by
    intro t ht y hy
    exact hC (t, y) ⟨ht, hy⟩
  have hdiff_all : ∀ t : ℝ, t ∈ S → ∀ y ∈ interior ((extChartAt I α).target : Set E),
      HasFDerivAt (fun y => F y t) (F' y t) y := by
    intro t ht y hy
    have hy_tgt : y ∈ (extChartAt I α).target := hInt_sub hy
    have hjoint_at : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => Gfn q.1 q.2) (S ×ˢ (extChartAt I α).target) (t, y) :=
      chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s Φ S α hjoint ht hy_tgt
    have hslice : ContDiffWithinAt ℝ ∞ (fun y' : E => Gfn t y')
        (extChartAt I α).target y := by
      have hcomp : ContDiffWithinAt ℝ ∞ (fun y' : E => (t, y'))
          (extChartAt I α).target y :=
        contDiffWithinAt_const.prodMk contDiffWithinAt_id
      have hmaps : Set.MapsTo (fun y' : E => (t, y')) (extChartAt I α).target
          (S ×ˢ (extChartAt I α).target) := fun y' hy' => ⟨ht, hy'⟩
      have hc := ContDiffWithinAt.comp (𝕜 := ℝ) (n := ∞)
        (g := fun q : ℝ × E => Gfn q.1 q.2) (f := fun y' : E => (t, y'))
        y hjoint_at hcomp hmaps
      exact hc
    have htgt_nhds : (extChartAt I α).target ∈ 𝓝 y :=
      Filter.mem_of_superset (hInt_open.mem_nhds hy) hInt_sub
    have hslice_at : ContDiffAt ℝ ∞ (fun y' : E => Gfn t y') y :=
      hslice.contDiffAt htgt_nhds
    exact (hslice_at.differentiableAt (by norm_num)).hasFDerivAt
  set μ : Measure ℝ := volume with hμ
  have hGfn_slice_cont : ∀ y ∈ interior ((extChartAt I α).target : Set E),
      ContinuousOn (fun t : ℝ => Gfn t y) (Set.uIcc (0:ℝ) 1) := by
    intro y hy
    have hy_tgt : y ∈ (extChartAt I α).target := hInt_sub hy
    intro t ht
    have hts : t ∈ S := hSI ht
    have hjoint_at : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => Gfn q.1 q.2) (S ×ˢ (extChartAt I α).target) (t, y) :=
      chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s Φ S α hjoint hts hy_tgt
    have hsliceT : ContDiffWithinAt ℝ ∞ (fun t' : ℝ => Gfn t' y) S t := by
      have hcomp : ContDiffWithinAt ℝ ∞ (fun t' : ℝ => (t', y)) S t :=
        contDiffWithinAt_id.prodMk contDiffWithinAt_const
      have hmaps : Set.MapsTo (fun t' : ℝ => (t', y)) S
          (S ×ˢ (extChartAt I α).target) := fun t' ht' => ⟨ht', hy_tgt⟩
      have hc := ContDiffWithinAt.comp (𝕜 := ℝ) (n := ∞)
        (g := fun q : ℝ × E => Gfn q.1 q.2) (f := fun t' : ℝ => (t', y))
        t hjoint_at hcomp hmaps
      exact hc
    have hsliceAt : ContDiffAt ℝ ∞ (fun t' : ℝ => Gfn t' y) t :=
      hsliceT.contDiffAt (hS.mem_nhds hts)
    exact hsliceAt.continuousAt.continuousWithinAt
  have hF_meas : ∀ᶠ y in 𝓝 y₀, AEStronglyMeasurable (F y) (μ.restrict (Ι (0:ℝ) 1)) := by
    filter_upwards [hInt_open.mem_nhds hy₀] with y hy_mem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine (hGfn_slice_cont y hy_mem).mono ?_
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Ioc_subset_Icc_self
  have hF_int : IntervalIntegrable (F y₀) μ 0 1 :=
    (hGfn_slice_cont y₀ hy₀).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable (F' y₀) (μ.restrict (Ι (0:ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    have hcont : ContinuousOn (fun t : ℝ => F' y₀ t) (Set.Icc (0:ℝ) 1) := by
      have hmapsto : Set.MapsTo (fun t : ℝ => (t, y₀))
          (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1 ×ˢ Metric.closedBall y₀ ε2) :=
        fun t ht => ⟨ht, Metric.mem_closedBall_self hε2_pos.le⟩
      have hmap_cont : ContinuousOn (fun t : ℝ => (t, y₀)) (Set.Icc (0:ℝ) 1) :=
        (continuous_id.prodMk continuous_const).continuousOn
      exact (hfderiv_cont_swap.comp hmap_cont hmapsto)
    exact hcont.mono Set.Ioc_subset_Icc_self
  have h_bound : ∀ᵐ t ∂μ.restrict (Ι (0:ℝ) 1), ∀ y ∈ Metric.ball y₀ ε2, ‖F' y t‖ ≤ C := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
    intro t ht y hy
    exact hbound t (Set.Ioc_subset_Icc_self ht) y (Metric.ball_subset_closedBall hy)
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C) μ 0 1 :=
    intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂μ.restrict (Ι (0:ℝ) 1), ∀ y ∈ Metric.ball y₀ ε2,
      HasFDerivAt (fun y => F y t) (F' y t) y := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
    intro t _ht y hy
    exact hdiff_all t (hSI (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact
                                 Set.Ioc_subset_Icc_self _ht))
      y (hball_sub hy)
  have hsmem : Metric.ball y₀ ε2 ∈ 𝓝 y₀ := Metric.ball_mem_nhds y₀ hε2_pos
  have hkey := hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := F) (F' := F') (bound := fun _ => C) (a := 0) (b := 1) (μ := μ) (x₀ := y₀)
    (s := Metric.ball y₀ ε2) hsmem hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hLHSeq : (fun y : E => ∫ t in (0:ℝ)..1, F y t ∂μ) =
      (fun y : E => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s α
        (fun z : M =>
          (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection z)
        ((extChartAt I α).symm y)) := by
    funext y
    rw [hF, hGfn]
    exact (chartRepr_pathIntegralCoeffField_eq (I := I) g₀ r s Φ S hS hSI hjoint α
      ((extChartAt I α).symm y)).symm
  rw [hLHSeq] at hkey
  exact hkey

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M]
  in
private theorem fderiv_chartRepr_pathIntegral_apply_data
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (α : M) {y₀ : E} (hy₀ : y₀ ∈ interior ((extChartAt I α).target : Set E)) (dir : E) :
    (fderiv ℝ (fun y : E => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s α
        (fun z : M =>
          (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection z)
        ((extChartAt I α).symm y)) y₀ dir =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y : E =>
        DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
          (I := I) r s α (fun z : M => (Φ t).toSection z) ((extChartAt I α).symm y)) y₀ dir) ∧
    IntervalIntegrable (fun t : ℝ => fderiv ℝ (fun y : E =>
      DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (Φ t).toSection z) ((extChartAt I α).symm y)) y₀ dir)
      volume 0 1 := by
  have hhas := hasFDerivAt_chartRepr_pathIntegral (I := I) g₀ r s Φ S hS hSI hjoint α hy₀
  have hcont : ContinuousOn (fun t : ℝ => fderiv ℝ (fun y : E =>
      DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (Φ t).toSection z) ((extChartAt I α).symm y)) y₀)
      (Set.uIcc (0 : ℝ) 1) := by
    have hjc := fderiv_chartRepr_jointContinuousOn (I := I) g₀ r s Φ S hS α
      (U := interior ((extChartAt I α).target : Set E)) isOpen_interior interior_subset hjoint
    have hmaps : Set.MapsTo (fun t : ℝ => (t, y₀)) (Set.uIcc (0:ℝ) 1)
        (S ×ˢ interior ((extChartAt I α).target : Set E)) := fun t ht => ⟨hSI ht, hy₀⟩
    exact hjc.comp ((continuous_id.prodMk continuous_const).continuousOn) hmaps
  have hII : IntervalIntegrable (fun t : ℝ => fderiv ℝ (fun y : E =>
      DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (Φ t).toSection z) ((extChartAt I α).symm y)) y₀)
      volume 0 1 := hcont.intervalIntegrable
  constructor
  · rw [hhas.fderiv, ContinuousLinearMap.intervalIntegral_apply hII dir]
  · exact intervalIntegrable_continuousLinearMap_apply_local _ hcont dir

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private theorem chartE_repr_slice_continuousOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (α x : M) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S) :
    ContinuousOn
      (fun t : ℝ => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (Φ t).toSection z) x) (Set.uIcc (0:ℝ) 1) := by
  set L : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ x).comp
      (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap
    with hL
  have hm : ContinuousOn (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x))
      (Set.uIcc (0:ℝ) 1) :=
    (jointContMDiff_toModel_continuous_slice (I := I) g₀ r s Φ S hjoint x).mono hSI
  refine ContinuousOn.congr (L.continuous.comp_continuousOn hm) ?_
  intro t _
  change DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
      (I := I) r s α (fun z : M => (Φ t).toSection z) x = L
        (TensorRSSpace.toModel ((Φ t).toSection x))
  rw [DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply, hL,
    ContinuousLinearMap.comp_apply]
  congr 1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private theorem intervalIntegrable_slotInput
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hx_src : x ∈ (chartAt H x).source) (k : Fin r) :
    IntervalIntegrable
      (fun t : ℝ =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀
            x
            (fun z : M => (Φ t).toSection z) B.toFun x k)) volume 0 1 := by
  have hcont : ContinuousOn
      (fun t : ℝ =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀
            x
            (fun z : M => (Φ t).toSection z) B.toFun x k)) (Set.uIcc (0:ℝ) 1) := by
    have hbase := chartE_repr_slice_continuousOn (I := I) g₀ r s Φ S hjoint x x hSI
    refine ContinuousOn.congr
      (((DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel
        (I := I) g₀ r s x B.toFun k x).continuous).comp_continuousOn hbase) ?_
    intro t _
    change (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀
            x
            (fun z : M => (Φ t).toSection z) B.toFun x k) =
        DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel (I := I) g₀ r s x B.toFun k x
          (DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
            (I := I) r s x (fun z : M => (Φ t).toSection z) x)
    rw [chartTensorRSInputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s x
      (fun z : M => (Φ t).toSection z) B.toFun hx_src k,
      DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply]
  exact hcont.intervalIntegrable

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private theorem intervalIntegrable_slotOutput
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hx_src : x ∈ (chartAt H x).source) (l : Fin s) :
    IntervalIntegrable
      (fun t : ℝ =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r s
            g₀ x
            (fun z : M => (Φ t).toSection z) B.toFun x l)) volume 0 1 := by
  have hcont : ContinuousOn
      (fun t : ℝ =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r s
            g₀ x
            (fun z : M => (Φ t).toSection z) B.toFun x l)) (Set.uIcc (0:ℝ) 1) := by
    have hbase := chartE_repr_slice_continuousOn (I := I) g₀ r s Φ S hjoint x x hSI
    refine ContinuousOn.congr
      (((DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel
        (I := I) g₀ r s x B.toFun l x).continuous).comp_continuousOn hbase) ?_
    intro t _
    change (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r s
            g₀ x
            (fun z : M => (Φ t).toSection z) B.toFun x l) =
        DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel (I := I) g₀ r s x B.toFun l x
          (DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
            (I := I) r s x (fun z : M => (Φ t).toSection z) x)
    rw [chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s x
      (fun z : M => (Φ t).toSection z) B.toFun hx_src l,
      DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply]
  exact hcont.intervalIntegrable

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M]
  in
private theorem inputSlotCorrection_pathIntegral_comm
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (k : Fin r) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
      (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ x
        (fun z : M => (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection
          z)
        B.toFun x k) =
      ∫ t in (0 : ℝ)..1,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀
            x
            (fun z : M => (Φ t).toSection z) B.toFun x k) := by
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  have hIIΦ : IntervalIntegrable
      (fun t : ℝ => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s x (fun z : M => (Φ t).toSection z) x) volume 0 1 :=
    (chartE_repr_slice_continuousOn (I := I) g₀ r s Φ S hjoint x x hSI).intervalIntegrable
  rw [chartTensorRSInputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s x
    (fun z : M => (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection z)
    B.toFun hx_src k,
    ← DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply (I := I) r s x
      (fun z : M => (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection z)
        x,
    chartRepr_pathIntegralCoeffField_eq (I := I) g₀ r s Φ S hS hSI hjoint x x]
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm
    (DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel (I := I) g₀ r s x B.toFun k x)
      hIIΦ]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [chartTensorRSInputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s x
    (fun z : M => (Φ t).toSection z) B.toFun hx_src k,
    DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M]
  in
private theorem outputSlotCorrection_pathIntegral_comm
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (l : Fin s) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
      (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ x
        (fun z : M => (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection
          z)
        B.toFun x l) =
      ∫ t in (0 : ℝ)..1,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r s
            g₀ x
            (fun z : M => (Φ t).toSection z) B.toFun x l) := by
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  have hIIΦ : IntervalIntegrable
      (fun t : ℝ => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr
        (I := I) r s x (fun z : M => (Φ t).toSection z) x) volume 0 1 :=
    (chartE_repr_slice_continuousOn (I := I) g₀ r s Φ S hjoint x x hSI).intervalIntegrable
  rw [chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s x
    (fun z : M => (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection z)
    B.toFun hx_src l,
    ← DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply (I := I) r s x
      (fun z : M => (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection z)
        x,
    chartRepr_pathIntegralCoeffField_eq (I := I) g₀ r s Φ S hS hSI hjoint x x]
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm
    (DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel (I := I) g₀ r s x B.toFun l x)
      hIIΦ]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s x
    (fun z : M => (Φ t).toSection z) B.toFun hx_src l,
    DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covApply_chartE_pathIntegral_comm
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun
          (fun z : M =>
            (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection z)) x =
      ∫ t in (0 : ℝ)..1,
        DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z)) x := by
  classical
  set α : M := x with hα
  set φ := extChartAt I α with hφ
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) α :=
    DifferentialGeometry.Geometry.Connection.self_mem_chartLeviCivitaGoodSet (I := I) α
  have hx_src : x ∈ (chartAt H α).source :=
    DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_chartAt_source
      (I := I) hx_good
  have hx_tgt : φ x ∈ φ.target := φ.map_source (by rw [hφ, extChartAt_source]; exact hx_src)
  have hx_round : φ.symm (φ x) = x := φ.left_inv (by rw [hφ, extChartAt_source]; exact hx_src)
  have hx_int : φ x ∈ interior ((φ).target : Set E) := by
    rw [hφ, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hx_tgt
  set W : SmoothCcTensor g₀ r s :=
    pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint with hW
  have hform_W := chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M)
    g₀ r s α W B hx_tgt (by rw [hx_round]; exact hx_good)
  have hform_Φ : ∀ t : ℝ,
      (DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z)) ∘ φ.symm) (φ x) =
        fderiv ℝ
          (DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => (Φ t).toSection z) ∘ φ.symm) (φ x)
          (DifferentialGeometry.Geometry.Connection.trivToE (I := I) α (φ.symm (φ x))
            (B.toFun (φ.symm (φ x))))
        + ∑ k : Fin r,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ (φ.symm (φ x))
              (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r
                s g₀ α
                (fun z : M => (Φ t).toSection z) B.toFun (φ.symm (φ x)) k)
        - ∑ l : Fin s,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ (φ.symm (φ x))
              (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r
                s g₀ α
                (fun z : M => (Φ t).toSection z) B.toFun (φ.symm (φ x)) l) := fun t =>
    chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M)
      g₀ r s α (Φ t) B hx_tgt (by rw [hx_round]; exact hx_good)
  set dir : E := DifferentialGeometry.Geometry.Connection.trivToE (I := I) α x (B.toFun x) with hdir
  set Wchart : E → TensorRSModel r s ℝ E :=
    fun y => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => W.toSection z) (φ.symm y) with hWchart
  set Φchart : ℝ → E → TensorRSModel r s ℝ E :=
    fun t y => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => (Φ t).toSection z) (φ.symm y) with hΦchart
  have hfderiv_data :=
    fderiv_chartRepr_pathIntegral_apply_data (I := I) g₀ r s Φ S hS hSI hjoint α hx_int dir
  have hfderiv_comm :
      fderiv ℝ Wchart (φ x) dir =
        ∫ t in (0 : ℝ)..1, fderiv ℝ (Φchart t) (φ x) dir := by
    rw [hWchart, hΦchart, hW, hφ]
    exact hfderiv_data.1
  have hWchart_eq : ∀ y : E, Wchart y =
      ∫ t in (0 : ℝ)..1, Φchart t y := by
    intro y
    rw [hWchart, hΦchart]
    exact chartRepr_pathIntegralCoeffField_eq (I := I) g₀ r s Φ S hS hSI hjoint α (φ.symm y)
  have hinput_comm : ∀ k : Fin r,
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
        (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
          (fun z : M => W.toSection z) B.toFun x k) =
      ∫ t in (0 : ℝ)..1,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀
            α
            (fun z : M => (Φ t).toSection z) B.toFun x k) := by
    intro k
    rw [hW, hα]
    exact inputSlotCorrection_pathIntegral_comm (I := I) g₀ r s Φ S hS hSI hjoint B x k
  have houtput_comm : ∀ l : Fin s,
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
        (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀
          α
          (fun z : M => W.toSection z) B.toFun x l) =
      ∫ t in (0 : ℝ)..1,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r s
            g₀ α
            (fun z : M => (Φ t).toSection z) B.toFun x l) := by
    intro l
    rw [hW, hα]
    exact outputSlotCorrection_pathIntegral_comm (I := I) g₀ r s Φ S hS hSI hjoint B x l
  have hLHS_eq : DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => W.toSection z)) x =
      fderiv ℝ Wchart (φ x) dir
        + (∑ k : Fin r,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
              (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r
                s g₀ α
                (fun z : M => W.toSection z) B.toFun x k))
        - (∑ l : Fin s,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
              (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r
                s g₀ α
                (fun z : M => W.toSection z) B.toFun x l)) := by
    have h := hform_W
    rw [← hφ] at h
    simp only [Function.comp_apply] at h
    rw [hx_round] at h
    rw [hWchart, hdir]
    exact h
  have hRHS_eq : ∀ t : ℝ,
      DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (Φ t).toSection z)) x =
      fderiv ℝ (Φchart t) (φ x) dir
        + (∑ k : Fin r,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
              (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r
                s g₀ α
                (fun z : M => (Φ t).toSection z) B.toFun x k))
        - (∑ l : Fin s,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
              (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r
                s g₀ α
                (fun z : M => (Φ t).toSection z) B.toFun x l)) := by
    intro t
    have h := hform_Φ t
    simp only [Function.comp_apply] at h
    rw [hx_round] at h
    rw [hΦchart, hdir]
    exact h
  rw [hLHS_eq, hfderiv_comm]
  have hsum_input : (∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀
            α
            (fun z : M => W.toSection z) B.toFun x k)) =
      ∫ t in (0 : ℝ)..1, ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀
            α
            (fun z : M => (Φ t).toSection z) B.toFun x k) := by
    refine finset_sum_eq_intervalIntegral_sum_local _ _ hinput_comm ?_
    exact fun k => intervalIntegrable_slotInput (I := I) g₀ r s Φ S hjoint B x hSI hx_src k
  have hsum_output : (∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r s
            g₀ α
            (fun z : M => W.toSection z) B.toFun x l)) =
      ∫ t in (0 : ℝ)..1, ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r s
            g₀ α
            (fun z : M => (Φ t).toSection z) B.toFun x l) := by
    refine finset_sum_eq_intervalIntegral_sum_local _ _ houtput_comm ?_
    exact fun l => intervalIntegrable_slotOutput (I := I) g₀ r s Φ S hjoint B x hSI hx_src l
  rw [hsum_input, hsum_output]
  have hII_fderivApply : IntervalIntegrable
      (fun t : ℝ => fderiv ℝ (Φchart t) (φ x) dir) volume 0 1 := by
    rw [hΦchart, hφ]
    exact hfderiv_data.2
  have hII_inputSum : IntervalIntegrable
      (fun t : ℝ => ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀
            α
            (fun z : M => (Φ t).toSection z) B.toFun x k)) volume 0 1 := by
    refine intervalIntegrable_finset_sum_local _ ?_
    exact fun k => intervalIntegrable_slotInput (I := I) g₀ r s Φ S hjoint B x hSI hx_src k
  have hII_outputSum : IntervalIntegrable
      (fun t : ℝ => ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r s
            g₀ α
            (fun z : M => (Φ t).toSection z) B.toFun x l)) volume 0 1 := by
    refine intervalIntegrable_finset_sum_local _ ?_
    exact fun l => intervalIntegrable_slotOutput (I := I) g₀ r s Φ S hjoint B x hSI hx_src l
  rw [← intervalIntegral.integral_add hII_fderivApply hII_inputSum,
    ← intervalIntegral.integral_sub (hII_fderivApply.add hII_inputSum) hII_outputSum]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [hRHS_eq t]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorCovDerivAt_pathIntegralCoeffField_eq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) (v : E) :
    TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s
        (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint) x v) =
      ∫ t in (0 : ℝ)..1,
        TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x v) := by
  classical
  set W : SmoothCcTensor g₀ r s :=
    pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint with hW
  obtain ⟨B, hB⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (show TangentSpace I x from v)
  have hBx : B.toFun x = v := hB
  set e := trivializationAt (TensorRSModel r s ℝ E) (fun y : M => TensorRSSpace r s I y) x with he
  have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hcomm := covApply_chartE_pathIntegral_comm (I := I) g₀ r s Φ S hS hSI hjoint B x
  have hjapply := covApply_section_jointContMDiffOn (I := I) g₀ r s Φ S B hjoint
  have hfibre_model : ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (Φ t).toSection z) x)) (Set.uIcc (0:ℝ) 1) := by
    have hmap : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (x, t)) :=
      (contMDiff_const).prodMk contMDiff_id
    have hmaps : Set.MapsTo (fun t : ℝ => (x, t)) (Set.uIcc (0:ℝ) 1) ((Set.univ : Set M) ×ˢ S) :=
      fun t ht => ⟨Set.mem_univ _, hSI ht⟩
    have hsliceTot : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun t : ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z) x)) (Set.uIcc (0:ℝ) 1) :=
      hjapply.comp hmap.contMDiffOn hmaps
    have hchart : ContinuousOn (fun t : ℝ =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) x).continuousLinearMapAt ℝ x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z) x)) (Set.uIcc (0:ℝ) 1) := by
      have hcoord : ContinuousOn (fun t : ℝ =>
          (e (TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun z : M => TensorRSSpace r s I z) x
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
              B.toFun (fun z : M => (Φ t).toSection z) x))).2) (Set.uIcc (0:ℝ) 1) :=
        continuous_snd.comp_continuousOn (e.continuousOn_toFun.comp hsliceTot.continuousOn
          (fun t _ => e.mem_source.mpr hxbase))
      refine hcoord.congr (fun t _ => ?_)
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hxbase]
    set K' : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
      (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) r s x).toContinuousLinearMap.comp
        (e.symmL ℝ x) with hK'
    refine ContinuousOn.congr (K'.continuous.comp_continuousOn hchart) ?_
    intro t _
    change TensorRSSpace.toModel
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z) x) =
        K' ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) x).continuousLinearMapAt ℝ x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z) x))
    rw [hK', ContinuousLinearMap.comp_apply,
      Bundle.Trivialization.symmL_continuousLinearMapAt e hxbase]
    rfl
  set K : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
    (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) r s x).toContinuousLinearMap.comp
      (e.symmL ℝ x) with hK
  have hKbridge : ∀ (Y : SmoothCcTensor g₀ r s),
      TensorRSSpace.toModel
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => Y.toSection z) x) =
      K (DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => Y.toSection z)) x) := by
    intro Y
    rw [hK, ContinuousLinearMap.comp_apply,
      DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply,
      Bundle.Trivialization.symmL_continuousLinearMapAt e hxbase]
    rfl
  have hII_chartΦ : IntervalIntegrable
      (fun t : ℝ => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r
        s x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (Φ t).toSection z)) x) volume 0 1 := by
    have hcont : ContinuousOn
        (fun t : ℝ => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I)
          r s x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z)) x) (Set.uIcc (0:ℝ) 1) := by
      set Lc : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) x).continuousLinearMapAt ℝ x).comp
          (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) r s
            x).symm.toContinuousLinearMap
        with hLc
      refine ContinuousOn.congr (Lc.continuous.comp_continuousOn hfibre_model) ?_
      intro t _
      change DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z)) x =
          Lc (TensorRSSpace.toModel
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
                B.toFun (fun z : M => (Φ t).toSection z) x))
      rw [DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply, hLc,
        ContinuousLinearMap.comp_apply]
      congr 1
    exact hcont.intervalIntegrable
  have hgoalL : TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s W x v) =
      K (DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => W.toSection z)) x) := by
    rw [← hKbridge W]
    change TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s W x v) =
        TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s W x (B.toFun x))
    rw [hBx]
  have hgoalΦ : ∀ t : ℝ,
      TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x v) =
      K (DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z)) x) := by
    intro t
    rw [← hKbridge (Φ t)]
    change TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x v) =
        TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (B.toFun x))
    rw [hBx]
  rw [hgoalL, hcomm, ← ContinuousLinearMap.intervalIntegral_comp_comm K hII_chartΦ]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  exact (hgoalΦ t).symm

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGradParametric_tcd_toModel_continuousOn [SigmaCompactSpace M]
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) (v : E) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S) :
    ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x v))
      (Set.uIcc (0:ℝ) 1) := by
  classical
  obtain ⟨B, hB⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (show TangentSpace I x from v)
  have hBx : B.toFun x = v := hB
  set e := trivializationAt (TensorRSModel r s ℝ E) (fun y : M => TensorRSSpace r s I y) x with he
  have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hjapply := covApply_section_jointContMDiffOn (I := I) g₀ r s Φ S B hjoint
  have hmap : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (x, t)) :=
    (contMDiff_const).prodMk contMDiff_id
  have hmaps : Set.MapsTo (fun t : ℝ => (x, t)) (Set.uIcc (0:ℝ) 1) ((Set.univ : Set M) ×ˢ S) :=
    fun t ht => ⟨Set.mem_univ _, hSI ht⟩
  have hsliceTot : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun t : ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (Φ t).toSection z) x)) (Set.uIcc (0:ℝ) 1) :=
    hjapply.comp hmap.contMDiffOn hmaps
  have hchart : ContinuousOn (fun t : ℝ =>
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) x).continuousLinearMapAt ℝ x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (Φ t).toSection z) x)) (Set.uIcc (0:ℝ) 1) := by
    have hcoord : ContinuousOn (fun t : ℝ =>
        (e (TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z) x))).2) (Set.uIcc (0:ℝ) 1) :=
      continuous_snd.comp_continuousOn (e.continuousOn_toFun.comp hsliceTot.continuousOn
        (fun t _ => e.mem_source.mpr hxbase))
    refine hcoord.congr (fun t _ => ?_)
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hxbase]
  set K' : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
    (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) r s x).toContinuousLinearMap.comp
      (e.symmL ℝ x) with hK'
  refine ContinuousOn.congr (K'.continuous.comp_continuousOn hchart) ?_
  intro t _
  change TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x v) =
      K' ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) x).continuousLinearMapAt ℝ x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (Φ t).toSection z) x))
  rw [hK', ContinuousLinearMap.comp_apply,
    Bundle.Trivialization.symmL_continuousLinearMapAt e hxbase, ← hBx]
  rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem toModel_covGrad_pathIntegralCoeffField_eq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hjg : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (s + 1) I z) q.1
        ((covGrad (I := I) (M := M) g₀ r s (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) :
    TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g₀ r s
          (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint)).toSection x) =
      ∫ t in (0 : ℝ)..1,
        TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x) := by
  classical
  set W : SmoothCcTensor g₀ r s :=
    pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint with hW
  apply ContinuousLinearMap.ext
  intro D
  apply ContinuousMultilinearMap.ext
  intro v
  have hkeyW : (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s W).toSection x) D) v =
      (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s W x (v 0)) D)
        (Matrix.vecTail v) :=
    covGrad_toSection_apply_eval (I := I) (M := M) g₀ r s W x D v
  have hkeyΦ : ∀ t : ℝ,
      (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x) D) v =
        (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (v 0)) D)
          (Matrix.vecTail v) := fun t =>
    covGrad_toSection_apply_eval (I := I) (M := M) g₀ r s (Φ t) x D v
  have hcore := tensorCovDerivAt_pathIntegralCoeffField_eq (I := I) g₀ r s Φ S hS hSI hjoint x (v 0)
  have hcontcd : ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (v 0)))
      (Set.uIcc (0:ℝ) 1) :=
    covGradParametric_tcd_toModel_continuousOn (I := I) g₀ r s Φ S hjoint x (v 0) hSI
  have hIIcd : IntervalIntegrable
      (fun t : ℝ => TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (v 0)))
      volume 0 1 := hcontcd.intervalIntegrable
  have hIIcdD : IntervalIntegrable
      (fun t : ℝ =>
        (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (v 0))) D)
      volume 0 1 := by
    have hc : ContinuousOn
        ((fun w : TensorRSModel r s ℝ E => w D) ∘
          (fun t : ℝ => TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (v 0))))
        (Set.uIcc (0:ℝ) 1) :=
      (ContinuousLinearMap.apply ℝ (Tensor0SModel s ℝ E) D).continuous.comp_continuousOn hcontcd
    exact hc.intervalIntegrable
  have hcontgrad : ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x))
      (Set.uIcc (0:ℝ) 1) :=
    (jointContMDiff_toModel_continuous_slice (I := I) g₀ r (s + 1)
      (fun t => covGrad (I := I) (M := M) g₀ r s (Φ t)) S hjg x).mono hSI
  have hIIgrad : IntervalIntegrable
      (fun t : ℝ => TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x))
      volume 0 1 := hcontgrad.intervalIntegrable
  have hIIgradD : IntervalIntegrable
      (fun t : ℝ => (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x))
        D)
      volume 0 1 := by
    have hc : ContinuousOn
        ((fun w : TensorRSModel r (s + 1) ℝ E => w D) ∘
          (fun t : ℝ => TensorRSSpace.toModel
            ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x)))
        (Set.uIcc (0:ℝ) 1) :=
      (ContinuousLinearMap.apply ℝ (Tensor0SModel (s + 1) ℝ E) D).continuous.comp_continuousOn
        hcontgrad
    exact hc.intervalIntegrable
  have hLHSval : ((TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s W).toSection x)) D) v =
      ∫ t in (0:ℝ)..1,
        (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (v 0)) D)
          (Matrix.vecTail v) := by
    rw [hkeyW, hcore, ContinuousLinearMap.intervalIntegral_apply hIIcd D]
    exact (ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ (Matrix.vecTail v)) hIIcdD).symm
  have hRHSval : ((∫ t in (0:ℝ)..1,
        TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x)) D) v =
      ∫ t in (0:ℝ)..1,
        (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x) D) v := by
    rw [ContinuousLinearMap.intervalIntegral_apply hIIgrad D]
    exact (ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (s + 1) => E) ℝ v) hIIgradD).symm
  rw [hLHSval, hRHSval]
  refine (intervalIntegral.integral_congr (fun t _ => ?_))
  exact (hkeyΦ t).symm

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_pathIntegral_comm
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hjg : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (s + 1) I z) q.1
        ((covGrad (I := I) (M := M) g₀ r s (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    covGrad (I := I) (M := M) g₀ r s
        (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint) =
      pathIntegralCoeffField (I := I) (M := M) g₀ r (s + 1)
        (fun t => covGrad (I := I) (M := M) g₀ r s (Φ t)) S hS hSI hjg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply Tensor0SBundle.TensorRSSpace.toModel_injective
  change TensorRSSpace.toModel
      ((covGrad (I := I) (M := M) g₀ r s
        (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint)).toSection x) =
    TensorRSSpace.toModel
      ((pathIntegralCoeffField (I := I) (M := M) g₀ r (s + 1)
        (fun t => covGrad (I := I) (M := M) g₀ r s (Φ t)) S hS hSI hjg).toSection x)
  rw [pathIntegralCoeffField_toSection, pathIntegralFib_toModel]
  exact toModel_covGrad_pathIntegralCoeffField_eq (I := I) g₀ r s Φ S hS hSI hjoint hjg x

end PathIntegralComm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

