import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialSource

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem exists_lp_weak_gradient_source_spatial_derivative
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (U R : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (K T DF S : Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (H DDF : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (J : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
      Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => K k (t, x)) (fun x => U (t, x)) Ω)
    (hsecond : ∀ i k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => H i k (t, x)) (fun x => K i (t, x)) Ω)
    (hthird : ∀ i j k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => J i j k (t, x)) (fun x => H i j (t, x)) Ω)
    (hDDF : ∀ i k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => DDF i k (t, x)) (fun x => DF i (t, x)) Ω)
    (hRspace : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => T k (t, x)) (fun x => R (t, x)) Ω)
    (hsource :
      let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
      let ρ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric p.1) α p.2
      let A := fun i j (p : ℝ × EuStd) =>
        MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
      ∀ k, S k =ᵐ[ν] fun p => DF k p +
        (∑ i, ∑ j, (fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * H i j p +
          fderiv ℝ (fun q => fderiv ℝ (A i j) q (0, EuclideanSpace.single k 1)) p
            (0, EuclideanSpace.single j 1) * K i p)) -
        (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p +
          fderiv ℝ (fun q => fderiv ℝ ρ q (0, EuclideanSpace.single k 1)) p (1, 0) * U p)) :
    let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
    let B := fun k i j (p : ℝ × EuStd) =>
      fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1)
    let C := fun k i j (p : ℝ × EuStd) =>
      fderiv ℝ (B k i j) p (0, EuclideanSpace.single j 1)
    let r := fun k (p : ℝ × EuStd) => fderiv ℝ ρ p (0, EuclideanSpace.single k 1)
    let s := fun k (p : ℝ × EuStd) => fderiv ℝ (r k) p (1, 0)
    ∃ DS : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ k l, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv l
        (fun x => DS k l (t, x)) (fun x => S k (t, x)) Ω) ∧
      ∀ k l, DS k l =ᵐ[ν] fun p => DDF k l p +
        (∑ i, ∑ j, (B k i j p * J i j l p +
          fderiv ℝ (fun x => B k i j (p.1, x)) p.2 (EuclideanSpace.single l 1) * H i j p +
          C k i j p * H i l p +
          fderiv ℝ (fun x => C k i j (p.1, x)) p.2 (EuclideanSpace.single l 1) * K i p)) -
        (r k p * T l p +
          fderiv ℝ (fun x => r k (p.1, x)) p.2 (EuclideanSpace.single l 1) * R p +
          s k p * K l p +
          fderiv ℝ (fun x => s k (p.1, x)) p.2 (EuclideanSpace.single l 1) * U p) := by
  intro ν ρ A B C r s
  classical
  let μ := volume.restrict (Icc a b)
  let O := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hO : IsOpen O := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
  have hOt : O ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    image_mono interior_subset
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ O) :=
    MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α Subset.rfl i j
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ O) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl hOt)
  have hd (f : ℝ × EuStd → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (D.regular ×ˢ O))
      (v : ℝ × EuStd) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ f p v) (D.regular ×ˢ O) :=
    (hf.fderiv_of_isOpen (D.regular_isOpen.prod hO) (by simp)).clm_apply contDiffOn_const
  have hB (k i j) : ContDiffOn ℝ (⊤ : ℕ∞) (B k i j) (D.regular ×ˢ O) :=
    hd _ (hA i j) _
  have hC (k i j) : ContDiffOn ℝ (⊤ : ℕ∞) (C k i j) (D.regular ×ˢ O) := hd _ (hB k i j) _
  have hr (k) : ContDiffOn ℝ (⊤ : ℕ∞) (r k) (D.regular ×ˢ O) := hd _ hρ _
  have hs (k) : ContDiffOn ℝ (⊤ : ℕ∞) (s k) (D.regular ×ˢ O) := hd _ (hr k) _
  have hlift (f : ℝ × EuStd → ℝ) (hf : ContinuousOn f (D.regular ×ˢ O)) : MemLp f ∞ ν := by
    have hm := (hf.mono (Set.prod_mono hreg hΩs)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (Set.prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hm
    exact hm
  let ι := ((Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
    (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN))) ⊕ (Unit ⊕ Bool)
  let Y : Fin (Module.finrank ℝ EuN) → ι → Lp ℝ 2 ν := fun k =>
    Sum.elim (Sum.elim (fun ij => H ij.1 ij.2) (fun ij => K ij.1))
      (Sum.elim (fun _ => DF k) (fun z => if z then R else U))
  let DY : Fin (Module.finrank ℝ EuN) → ι → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν :=
    fun k => Sum.elim (Sum.elim (fun ij l => J ij.1 ij.2 l) (fun ij l => H ij.1 l))
      (Sum.elim (fun _ l => DDF k l) (fun z l => if z then T l else K l))
  let Q : Fin (Module.finrank ℝ EuN) → ι → ℝ × EuStd → ℝ := fun k =>
    Sum.elim (Sum.elim (fun ij => B k ij.1 ij.2) (fun ij => C k ij.1 ij.2))
      (Sum.elim (fun _ _ => 1) (fun z p => if z then -(r k p) else -(s k p)))
  have hQs (k) (i : ι) : ContDiffOn ℝ (⊤ : ℕ∞) (Q k i) (D.regular ×ˢ O) := by
    rcases i with (⟨i, j⟩ | ⟨i, j⟩) | (_ | z)
    · exact hB k i j
    · exact hC k i j
    · exact contDiffOn_const
    · cases z
      · exact (hs k).neg
      · exact (hr k).neg
  have hQ (k i) : MemLp (Q k i) ∞ ν := hlift _ (hQs k i).continuousOn
  have hDQ (k i l) : MemLp
      (fun p => fderiv ℝ (fun x => Q k i (p.1, x)) p.2 (EuclideanSpace.single l 1)) ∞ ν :=
    hlift _ ((DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t x => Q k i (t, x)) D.regular_isOpen.uniqueDiffOn hO
      (hQs k i)).clm_apply contDiffOn_const).continuousOn
  have hQslice (k i) : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => Q k i (t, x)) Ω := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hQs k i).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x hx => ⟨hreg ht, hΩs (subset_closure hx)⟩)
  have hY (k) (i : ι) (l) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv l
      (fun x => DY k i l (t, x)) (fun x => Y k i (t, x)) Ω := by
    rcases i with (⟨i, j⟩ | ⟨i, j⟩) | (_ | z)
    · exact hthird i j l
    · exact hsecond i l
    · exact hDDF k l
    · cases z
      · exact hspatial l
      · exact hRspace l
  have hSsum (k) : S k =ᵐ[ν] fun p => ∑ i : ι, Q k i p * Y k i p := by
    filter_upwards [hsource k] with p hp
    change S k p = DF k p +
      (∑ i, ∑ j, (B k i j p * H i j p + C k i j p * K i p)) -
        (r k p * R p + s k p * U p) at hp
    rw [hp]
    change _ = ∑ i : ((Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
      (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN))) ⊕ (Unit ⊕ Bool),
        Q k i p * Y k i p
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Q, Y, Fintype.sum_prod_type,
      Fintype.sum_bool, Fintype.sum_unique, Sum.elim_inl, Sum.elim_inr,
      Bool.false_eq_true, ↓reduceIte, one_mul]
    simp_rw [Finset.sum_add_distrib]
    ring
  obtain ⟨DS, hDS, hDSformula, _⟩ :=
    Sobolev.Euclidean.exists_lp_spatial_weak_partials_of_ae_eq_finite_sum_family
      hΩ S Y DY Q hQ hDQ hQslice hY hSsum
  refine ⟨DS, hDS, ?_⟩
  intro k l
  filter_upwards [hDSformula k l] with p hp
  rw [hp]
  change (∑ i : ((Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
    (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN))) ⊕ (Unit ⊕ Bool),
      (Q k i p * DY k i l p + fderiv ℝ (fun x => Q k i (p.1, x)) p.2
        (EuclideanSpace.single l 1) * Y k i p)) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Q, Y, DY, Fintype.sum_prod_type,
    Fintype.sum_bool, Fintype.sum_unique, Sum.elim_inl, Sum.elim_inr,
      Bool.false_eq_true, ↓reduceIte,
    fderiv_const_apply, zero_apply, zero_mul, one_mul, add_zero,
    fderiv_fun_neg, neg_apply, neg_mul]
  simp_rw [Finset.sum_add_distrib]
  ring

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
