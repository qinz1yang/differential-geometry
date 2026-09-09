import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientSourceExpansion
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MixedTimeSpatialRegularity

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

section

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem spatial_derivative_contDiffOn {S : Set ℝ} {W : Set E}
    (hS : IsOpen S) (hW : IsOpen W) {b : ℝ × E → ℝ}
    (hb : ContDiffOn ℝ ∞ b (S ×ˢ W)) (v : E) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      fderiv ℝ (fun x => b (p.1, x)) p.2 v) (S ×ˢ W) :=
  (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := fun t x => b (t, x)) hS.uniqueDiffOn hW hb).clm_apply contDiffOn_const

private theorem slice_contDiffOn {S : Set ℝ} {W : Set E} {b : ℝ × E → ℝ}
    (hb : ContDiffOn ℝ ∞ b (S ×ˢ W)) {t : ℝ} (ht : t ∈ S) :
    ContDiffOn ℝ ∞ (fun x => b (t, x)) W :=
  hb.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨ht, hx⟩)

private theorem coefficient_regular_of_eq_sub_mul
    {S J : Set ℝ} {W Ω : Set E} (hS : IsOpen S) (hW : IsOpen W)
    (hJ : IsCompact J) (hJS : J ⊆ S) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩW : closure Ω ⊆ W)
    {b L P : ℝ × E → ℝ} {a : ℝ → ℝ}
    (hL : ContDiffOn ℝ ∞ L (S ×ˢ W)) (hP : ContDiffOn ℝ ∞ P (S ×ˢ W))
    (ha : ContinuousOn a J)
    (heq : ∀ t ∈ J, ∀ x ∈ W, b (t, x) = L (t, x) - a t * P (t, x)) :
    let ν := (volume.restrict J).prod (volume.restrict Ω)
    MemLp b ∞ ν ∧
      (∀ j : Fin d, MemLp (fun p : ℝ × E =>
        fderiv ℝ (fun x => b (p.1, x)) p.2 (EuclideanSpace.single j 1)) ∞ ν) ∧
      (∀ᵐ t ∂volume.restrict J, ContDiffOn ℝ ∞ (fun x => b (t, x)) Ω) := by
  intro ν
  have hderiv (t) (ht : t ∈ J) (x) (hx : x ∈ W) (v : E) :
      fderiv ℝ (fun y => b (t, y)) x v =
        fderiv ℝ (fun y => L (t, y)) x v -
          a t * fderiv ℝ (fun y => P (t, y)) x v := by
    have hLs := ((slice_contDiffOn hL (hJS ht)).contDiffAt (hW.mem_nhds hx)).differentiableAt
      (by simp)
    have hPs := ((slice_contDiffOn hP (hJS ht)).contDiffAt (hW.mem_nhds hx)).differentiableAt
      (by simp)
    have hg : (fun y => b (t, y)) =ᶠ[𝓝 x] (fun y => L (t, y) - a t * P (t, y)) :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx) (fun y hy => heq t ht y hy)
    rw [hg.fderiv_eq, fderiv_fun_sub hLs (hPs.const_mul _), fderiv_const_mul hPs]
    rfl
  have hcont : ContinuousOn b (J ×ˢ closure Ω) :=
    ((hL.continuousOn.mono (prod_mono hJS hΩW)).sub
      ((ha.comp continuousOn_fst (fun _ hp => hp.1)).mul
        (hP.continuousOn.mono (prod_mono hJS hΩW)))).congr
          (fun p hp => heq p.1 hp.1 p.2 (hΩW hp.2))
  have hbound {f : ℝ × E → ℝ} (hf : ContinuousOn f (J ×ˢ closure Ω)) : MemLp f ∞ ν := by
    have h := hf.memLp_top_of_subset_isCompact (hJ.prod hΩc)
      (hJ.measurableSet.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := volume.prod volume)
    simpa only [ν, Measure.prod_restrict] using h
  refine ⟨hbound hcont, ?_, ?_⟩
  · intro j
    apply hbound
    exact (((spatial_derivative_contDiffOn hS hW hL _).continuousOn.mono
      (prod_mono hJS hΩW)).sub
        ((ha.comp continuousOn_fst (fun _ hp => hp.1)).mul
          ((spatial_derivative_contDiffOn hS hW hP _).continuousOn.mono
            (prod_mono hJS hΩW)))).congr
              (fun p hp => hderiv p.1 hp.1 p.2 (hΩW hp.2) _)
  · filter_upwards [ae_restrict_mem hJ.measurableSet] with t ht
    apply (((slice_contDiffOn hL (hJS ht)).sub
      (contDiffOn_const.mul (slice_contDiffOn hP (hJS ht)))).congr
        (fun x hx => heq t ht x hx)).mono
    exact subset_closure.trans hΩW

private theorem gradient_source_coefficient_regular
    {S J : Set ℝ} {W Ω : Set E} (hS : IsOpen S) (hW : IsOpen W)
    (hJ : IsCompact J) (hJS : J ⊆ S) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩW : closure Ω ⊆ W)
    {ρ Q : ℝ × E → ℝ} {A : Fin d → Fin d → ℝ × E → ℝ}
    {C : Fin d → ℝ × E → ℝ} {a : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ (S ×ˢ W)) (hQ : ContDiffOn ℝ ∞ Q (S ×ˢ W))
    (hA : ∀ i j, ContDiffOn ℝ ∞ (A i j) (S ×ˢ W))
    (hC : ∀ i, ContDiffOn ℝ ∞ (C i) (S ×ˢ W)) (ha : ContinuousOn a J)
    (k : Fin d) (s : ((Fin d × Fin d) × Bool) ⊕ (Fin d × Bool) ⊕ (Bool × Bool)) :
    let b := gradientSourceCoefficient ρ A C (fun p => Q p - a p.1 * ρ p) k s
    let ν := (volume.restrict J).prod (volume.restrict Ω)
    MemLp b ∞ ν ∧
      (∀ j : Fin d, MemLp (fun p : ℝ × E =>
        fderiv ℝ (fun x => b (p.1, x)) p.2 (EuclideanSpace.single j 1)) ∞ ν) ∧
      (∀ᵐ t ∂volume.restrict J, ContDiffOn ℝ ∞ (fun x => b (t, x)) Ω) := by
  have hjoint (v : ℝ × E) : ContDiffOn ℝ ∞ (fun p => fderiv ℝ ρ p v) (S ×ˢ W) :=
    (hρ.fderiv_of_isOpen (m := ∞) (hS.prod hW) (by simp)).clm_apply contDiffOn_const
  have hsmooth {b : ℝ × E → ℝ} (hb : ContDiffOn ℝ ∞ b (S ×ˢ W)) :
      MemLp b ∞ ((volume.restrict J).prod (volume.restrict Ω)) ∧
        (∀ j : Fin d, MemLp (fun p : ℝ × E =>
          fderiv ℝ (fun x => b (p.1, x)) p.2 (EuclideanSpace.single j 1)) ∞
            ((volume.restrict J).prod (volume.restrict Ω))) ∧
        (∀ᵐ t ∂volume.restrict J, ContDiffOn ℝ ∞ (fun x => b (t, x)) Ω) := by
    apply coefficient_regular_of_eq_sub_mul hS hW hJ hJS hΩ hΩc hΩW hb
      (contDiffOn_const (c := 0)) ha
    intro t ht x hx
    simp
  rcases s with ⟨ij, b⟩ | (⟨i, b⟩ | ⟨b, c⟩)
  · cases b
    · exact hsmooth (spatial_derivative_contDiffOn hS hW (hA ij.1 ij.2) _)
    · exact hsmooth (spatial_derivative_contDiffOn hS hW
        (spatial_derivative_contDiffOn hS hW (hA ij.1 ij.2) _) _)
  · cases b
    · exact hsmooth (spatial_derivative_contDiffOn hS hW (hC i) _)
    · exact hsmooth (hC i)
  · cases b <;> cases c
    · refine coefficient_regular_of_eq_sub_mul hS hW hJ hJS hΩ hΩc hΩW
        (spatial_derivative_contDiffOn hS hW hQ (EuclideanSpace.single k 1))
        (spatial_derivative_contDiffOn hS hW hρ (EuclideanSpace.single k 1)) ha ?_
      intro t ht x hx
      change fderiv ℝ (fun y => Q (t, y) - a t * ρ (t, y)) x _ = _
      have hQs := ((slice_contDiffOn hQ (hJS ht)).contDiffAt (hW.mem_nhds hx)).differentiableAt
        (by simp)
      have hρs := ((slice_contDiffOn hρ (hJS ht)).contDiffAt (hW.mem_nhds hx)).differentiableAt
        (by simp)
      rw [fderiv_fun_sub hQs (hρs.const_mul _), fderiv_const_mul hρs]
      rfl
    · exact hsmooth (((hjoint (0, EuclideanSpace.single k 1)).fderiv_of_isOpen
        (m := ∞) (hS.prod hW) (by simp)).clm_apply
          (contDiffOn_const (c := ((1, 0) : ℝ × E)))).neg
    · exact coefficient_regular_of_eq_sub_mul hS hW hJ hJS hΩ hΩc hΩW hQ hρ ha
        (fun _ _ _ _ => rfl)
    · exact hsmooth (hjoint (0, EuclideanSpace.single k 1)).neg

private theorem exists_gradient_source_weak_partials
    {μ : Measure ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    (U : ℝ × E → ℝ) (V : Fin d → ℝ × E → ℝ)
    (U₀ : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (V₀ : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (H : Fin d → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (R : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (K : Fin d → Fin d → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (DR : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (F : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (Co : Fin d → ((Fin d × Fin d) × Bool) ⊕ (Fin d × Bool) ⊕ (Bool × Bool) → ℝ × E → ℝ)
    (hU₀ : U₀ =ᵐ[μ.prod (volume.restrict Ω)] U)
    (hV₀ : ∀ i, V₀ i =ᵐ[μ.prod (volume.restrict Ω)] V i)
    (hUweak : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => V₀ j (t, x)) (fun x => U₀ (t, x)) Ω)
    (hVweak : ∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (t, x)) (fun x => V₀ i (t, x)) Ω)
    (hK : ∀ i j l, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv l
      (fun x => K i j l (t, x)) (fun x => H i j (t, x)) Ω)
    (hDR : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => DR j (t, x)) (fun x => R (t, x)) Ω)
    (hCo : ∀ k s, MemLp (Co k s) ∞ (μ.prod (volume.restrict Ω)) ∧
      (∀ j, MemLp (fun p : ℝ × E => fderiv ℝ (fun x => Co k s (p.1, x)) p.2
        (EuclideanSpace.single j 1)) ∞ (μ.prod (volume.restrict Ω))) ∧
      ∀ᵐ t ∂μ, ContDiffOn ℝ ∞ (fun x => Co k s (t, x)) Ω)
    (hFormula : ∀ k, F k =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ s,
      Co k s p * gradientSourceField U V (fun i j p => H i j p) (fun p => R p) k s p) :
    ∃ DF : Fin d → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (∀ k j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun x => DF k j (t, x)) (fun x => F k (t, x)) Ω) ∧
      (∀ k j, DF k j =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ s,
        (Co k s p * gradientSourceField (fun p => V j p) (fun i p => H i j p)
          (fun i l p => K i l j p) (fun p => DR j p) k s p +
          fderiv ℝ (fun x => Co k s (p.1, x)) p.2 (EuclideanSpace.single j 1) *
            gradientSourceField U V (fun i l p => H i l p) (fun p => R p) k s p)) ∧
      (∀ k, ∀ᵐ t ∂μ, MemWkp 1 2 (fun x => F k (t, x)) Ω) ∧
      ∀ k, MemLp (fun t => (iteratedWeakSobolevNorm 1 2
        (fun x => F k (t, x)) Ω).toReal) 2 μ := by
  classical
  let ν := μ.prod (volume.restrict Ω)
  let Y := gradientSourceField U₀ V₀ H R
  let DY := fun k s j => gradientSourceField (V₀ j) (fun i => H i j)
    (fun i l => K i l j) (DR j) k s
  have hYweak (k s j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => DY k s j (t, x)) (fun x => Y k s (t, x)) Ω := by
    rcases s with ⟨il, b⟩ | (⟨i, b⟩ | ⟨b, c⟩)
    · cases b
      · exact hK il.1 il.2 j
      · exact hVweak il.1 j
    · cases b
      · exact hVweak i j
      · exact hK i k j
    · cases b <;> cases c
      · exact hUweak j
      · exact hUweak j
      · exact hVweak k j
      · exact hDR j
  have hYeq (k s) : Y k s =ᵐ[ν] fun p => gradientSourceField (fun p => U p)
      (fun i p => V i p) (fun i j p => H i j p) (fun p => R p) k s p := by
    rcases s with ⟨il, b⟩ | (⟨i, b⟩ | ⟨b, c⟩)
    · cases b
      · exact Filter.EventuallyEq.rfl
      · exact hV₀ il.1
    · cases b
      · exact hV₀ i
      · exact Filter.EventuallyEq.rfl
    · cases b <;> cases c
      · exact hU₀
      · exact hU₀
      · exact hV₀ k
      · exact Filter.EventuallyEq.rfl
  have hDYeq (k s j) : DY k s j =ᵐ[ν] fun p => gradientSourceField (fun p => V j p)
      (fun i p => H i j p) (fun i l p => K i l j p) (fun p => DR j p) k s p := by
    rcases s with ⟨il, b⟩ | (⟨i, b⟩ | ⟨b, c⟩)
    · cases b <;> exact Filter.EventuallyEq.rfl
    · cases b <;> exact Filter.EventuallyEq.rfl
    · cases b <;> cases c
      · exact hV₀ j
      · exact hV₀ j
      · exact Filter.EventuallyEq.rfl
      · exact Filter.EventuallyEq.rfl
  have hFformula (k) : F k =ᵐ[ν] fun p => ∑ s, Co k s p * Y k s p := by
    filter_upwards [hFormula k, ae_all_iff.mpr (hYeq k)] with p hp hy
    rw [hp]
    exact Finset.sum_congr rfl (fun s _ => congrArg (fun y => Co k s p * y) (hy s).symm)
  have hex (k) := exists_lp_spatial_weak_partials_of_ae_eq_finite_sum hΩ
    (F k) (Y k) (DY k) (Co k) (fun s => (hCo k s).1)
      (fun s j => (hCo k s).2.1 j) (fun s => (hCo k s).2.2) (hYweak k) (hFformula k)
  choose DF hDF hDFformula hDFnorm hWkp hNorm using hex
  refine ⟨DF, hDF, ?_, hWkp, hNorm⟩
  · intro k j
    filter_upwards [hDFformula k j, ae_all_iff.mpr (hYeq k),
      ae_all_iff.mpr (fun s => hDYeq k s j)] with p hp hy hdy
    rw [hp]
    apply Finset.sum_congr rfl
    intro s hs
    rw [hy s, hdy s]


end

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

private theorem exists_local_spatial_weak_jet
    (q : SmoothRiemannianMetric I_hs M) {T t₀ t₁ : ℝ}
    (u : timeL2 (H1ComplDirichlet q) T) (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∀ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∃ U₀ : Lp ℝ 2 ν, ∃ V₀ : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (U₀ =ᵐ[ν] U) ∧ (∀ i, V₀ i =ᵐ[ν] V i) ∧
        (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
          (fun z => H i j (t, z)) (fun z => V₀ i (t, z)) Ω₀) ∧
        ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
          (fun z => V₀ j (t, z)) (fun z => U₀ (t, z)) Ω₀ := by
  intro μ ν U V H hH
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  let U₀ := hU.toLp U
  let V₀ := fun i => (hV i).toLp (V i)
  have hU₀ : U₀ =ᵐ[ν] U := hU.coeFn_toLp
  have hV₀ (i) : V₀ i =ᵐ[ν] V i := (hV i).coeFn_toLp
  have hVweak (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun z => H i j (t, z)) (fun z => V₀ i (t, z)) Ω₀ := by
    have hVi := ae_restrict_of_ae (s := Icc t₀ t₁)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hH i j, Measure.ae_ae_of_ae_prod (hV₀ i), hVi] with t ht he hv
    change (fun z => V₀ i (t, z)) =ᵐ[volume.restrict Ω₀] (fun z => V i (t, z)) at he
    exact hasWeakPartialDeriv_congr_ae hΩ₀ j
      (he.trans (hv.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))).symm ht
  have hUweak (j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun z => V₀ j (t, z)) (fun z => U₀ (t, z)) Ω₀ := by
    have hbase := ae_restrict_of_ae (s := Icc t₀ t₁)
      (hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) j u)
    filter_upwards [hbase, Measure.ae_ae_of_ae_prod hU₀,
      Measure.ae_ae_of_ae_prod (hV₀ j)] with t ht hu hv
    change (fun z => U₀ (t, z)) =ᵐ[volume.restrict Ω₀] (fun z => U (t, z)) at hu
    change (fun z => V₀ j (t, z)) =ᵐ[volume.restrict Ω₀] (fun z => V j (t, z)) at hv
    have he := hasWeakPartialDeriv_congr_ae hΩ₀ j hu.symm (ht.restrict hΩ₀ hsub)
    intro φ hφ hφc hφs
    rw [he φ hφ hφc hφs]
    congr 1
    apply integral_congr_ae
    filter_upwards [hv] with z hz
    rw [hz]
  exact ⟨U₀, V₀, hU₀, hV₀, hVweak, hUweak⟩

omit [T2Space M] [CompactSpace M] in
private theorem local_gradient_source_coefficients_regular
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let τ := fun (p : ℝ × EuStd) => traceTimeDerivMetric (I := I_hs) G.metric p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
    let C := fun i (p : ℝ × EuStd) => ρ p * B i p
    let C₀ := fun (p : ℝ × EuStd) => ρ p * ((1 / 2 : ℝ) * τ p - a p.1)
    ∀ k s, MemLp (gradientSourceCoefficient ρ A C C₀ k s) ∞ ν ∧
      (∀ j, MemLp (fun p : ℝ × EuStd => fderiv ℝ
        (fun x => gradientSourceCoefficient ρ A C C₀ k s (p.1, x)) p.2
          (EuclideanSpace.single j 1)) ∞ ν) ∧
      ∀ᵐ t ∂μ, ContDiffOn ℝ ∞
        (fun x => gradientSourceCoefficient ρ A C C₀ k s (t, x)) Ω₀ := by
  intro μ ν ρ A B τ C C₀
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀W : closure Ω₀ ⊆ W := hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hρ : ContDiffOn ℝ ∞ ρ (D.regular ×ˢ W) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))
  have hτ : ContDiffOn ℝ ∞ τ (D.regular ×ˢ W) :=
    MetricExtension.traceTimeDerivMetric_comp_chartInverse_contDiffOn hG Subset.rfl α Subset.rfl
  let Q := fun p : ℝ × EuStd => ρ p * ((1 / 2 : ℝ) * τ p)
  have hQ : ContDiffOn ℝ ∞ Q (D.regular ×ˢ W) :=
    hρ.mul (contDiffOn_const.mul hτ)
  have hA (i j) : ContDiffOn ℝ ∞ (A i j) (D.regular ×ˢ W) :=
    MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α Subset.rfl i j
  have hC (i) : ContDiffOn ℝ ∞ (C i) (D.regular ×ˢ W) :=
    hρ.mul ((MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_contDiffOn X α
      hXsmooth i).mono (prod_mono Subset.rfl (image_mono interior_subset)))
  have hC₀ : C₀ = fun p => Q p - a p.1 * ρ p := by
    funext p
    dsimp only [C₀, Q]
    ring
  have hI : Icc t₀ t₁ ⊆ Icc (0 : ℝ) T := Icc_subset_Icc ht₀.le ht₁.le
  have hμ : μ = volume.restrict (Icc t₀ t₁) :=
    timeMeasure_restrict_Icc_eq_volume_restrict_Icc hI
  let Co := gradientSourceCoefficient ρ A C C₀
  have hCo (k s) : MemLp (Co k s) ∞ ν ∧
      (∀ j, MemLp (fun p : ℝ × EuStd => fderiv ℝ (fun x => Co k s (p.1, x)) p.2
        (EuclideanSpace.single j 1)) ∞ ν) ∧
      (∀ᵐ t ∂μ, ContDiffOn ℝ ∞ (fun x => Co k s (t, x)) Ω₀) := by
    have h := gradient_source_coefficient_regular D.regular_isOpen hW isCompact_Icc
      (hI.trans hreg) hΩ₀ hΩ₀c hΩ₀W hρ hQ hA hC (hacont.mono hI) k s
    simpa only [Co, hC₀, ν, hμ] using h
  exact hCo

private theorem source_spatial_derivative_of_weak_gradient_equation
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T) (ht₀₁ : t₀ ≤ t₁)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let τ := fun (p : ℝ × EuStd) => traceTimeDerivMetric (I := I_hs) G.metric p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
    let C := fun i (p : ℝ × EuStd) => ρ p * B i p
    let C₀ := fun (p : ℝ × EuStd) => ρ p * ((1 / 2 : ℝ) * τ p - a p.1)
    ∀ R : Lp ℝ 2 ν,
      ∀ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∀ F : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) →
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      (∀ k, F k =ᵐ[ν] fun p => ∑ s,
        gradientSourceCoefficient ρ A C C₀ k s p *
          gradientSourceField (fun p => U p) (fun i p => V i p)
            (fun i j p => H i j p) (fun p => R p) k s p) →
      ∃ K : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ DR : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ DF : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (∀ i j l, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv l
          (fun z => K i j l (t, z)) (fun z => H i j (t, z)) Ω₀) ∧
        (∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
          (fun z => DR j (t, z)) (fun z => R (t, z)) Ω₀) ∧
        (∀ k j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
          (fun z => DF k j (t, z)) (fun z => F k (t, z)) Ω₀) ∧
        (∀ k j, DF k j =ᵐ[ν] fun p => ∑ s,
          (gradientSourceCoefficient ρ A C C₀ k s p *
            gradientSourceField (fun p => V j p) (fun i p => H i j p)
              (fun i l p => K i l j p) (fun p => DR j p) k s p +
            fderiv ℝ (fun x => gradientSourceCoefficient ρ A C C₀ k s (p.1, x)) p.2
              (EuclideanSpace.single j 1) *
              gradientSourceField (fun p => U p) (fun i p => V i p)
                (fun i l p => H i l p) (fun p => R p) k s p)) ∧
        (∀ k, ∀ᵐ t ∂μ, MemWkp 1 2 (fun x => F k (t, x)) Ω₀) ∧
        ∀ k, MemLp (fun t => (iteratedWeakSobolevNorm 1 2
          (fun x => F k (t, x)) Ω₀).toReal) 2 μ := by
  intro μ ν ρ A U V B τ C C₀ R H F hR hH hFinite
  obtain ⟨K, hK⟩ := hu.exists_local_third_weak_derivative hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω H hH
  obtain ⟨DR, hDR, _, _⟩ := hu.exists_spatial_weak_derivative_time_derivative hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω R hR
  obtain ⟨U₀, V₀, hU₀, hV₀, hVweak, hUweak⟩ :=
    exists_local_spatial_weak_jet q u α hΩ hΩc hΩs hΩ₀ hΩ₀Ω H hH
  let Co := gradientSourceCoefficient ρ A C C₀
  have hCo := local_gradient_source_coefficients_regular (hG := hG) (hreg := hreg)
    hacont α hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  obtain ⟨DF, hDF, hDFformula, hWkp, hNorm⟩ := exists_gradient_source_weak_partials hΩ₀
    (fun p => U p) (fun i p => V i p) U₀ V₀ H R K DR F Co hU₀ hV₀ hUweak hVweak hK hDR hCo hFinite
  exact ⟨K, DR, DF, hK, hDR, hDF, hDFformula, hWkp, hNorm⟩


theorem IsWeakEvolutionSolution.exists_lp_weak_gradient_equation_with_source_spatial_derivative
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T) (ht₀₁ : t₀ ≤ t₁)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let τ := fun (p : ℝ × EuStd) => traceTimeDerivMetric (I := I_hs) G.metric p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
    let C := fun i (p : ℝ × EuStd) => ρ p * B i p
    let C₀ := fun (p : ℝ × EuStd) => ρ p * ((1 / 2 : ℝ) * τ p - a p.1)
    ∃ R : Lp ℝ 2 ν,
      ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ F : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i j, H i j = H j i) ∧
      (∀ k, F k =ᵐ[ν] fun p => ∑ s,
        gradientSourceCoefficient ρ A C C₀ k s p *
          gradientSourceField (fun p => U p) (fun i p => V i p)
            (fun i j p => H i j p) (fun p => R p) k s p) ∧
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F k p * φ p ∂ν) ∧
      ∃ K : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ DR : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ DF : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (∀ i j l, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv l
          (fun z => K i j l (t, z)) (fun z => H i j (t, z)) Ω₀) ∧
        (∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
          (fun z => DR j (t, z)) (fun z => R (t, z)) Ω₀) ∧
        (∀ k j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
          (fun z => DF k j (t, z)) (fun z => F k (t, z)) Ω₀) ∧
        (∀ k j, DF k j =ᵐ[ν] fun p => ∑ s,
          (gradientSourceCoefficient ρ A C C₀ k s p *
            gradientSourceField (fun p => V j p) (fun i p => H i j p)
              (fun i l p => K i l j p) (fun p => DR j p) k s p +
            fderiv ℝ (fun x => gradientSourceCoefficient ρ A C C₀ k s (p.1, x)) p.2
              (EuclideanSpace.single j 1) *
              gradientSourceField (fun p => U p) (fun i p => V i p)
                (fun i l p => H i l p) (fun p => R p) k s p)) ∧
        (∀ k, ∀ᵐ t ∂μ, MemWkp 1 2 (fun x => F k (t, x)) Ω₀) ∧
        ∀ k, MemLp (fun t => (iteratedWeakSobolevNorm 1 2
          (fun x => F k (t, x)) Ω₀).toReal) 2 μ := by
  intro μ ν ρ A U V B τ C C₀
  classical
  obtain ⟨R, H, F, hR, hH, hHsym, hFormula, hF⟩ :=
    hu.exists_lp_weak_gradient_equation_with_source_formula hXcont hacont
      α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  have hFinite (k) : F k =ᵐ[ν] fun p => ∑ s,
      gradientSourceCoefficient ρ A C C₀ k s p *
        gradientSourceField (fun p => U p) (fun i p => V i p)
          (fun i j p => H i j p) (fun p => R p) k s p := by
    simpa only [sum_gradientSourceCoefficient_mul_field] using hFormula k
  have hsource := source_spatial_derivative_of_weak_gradient_equation
    hXcont hacont α hΩ hΩc hΩs hu hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω R H F hR hH hFinite
  exact ⟨R, H, F, hR, hH, hHsym, hFinite, hF, hsource⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
