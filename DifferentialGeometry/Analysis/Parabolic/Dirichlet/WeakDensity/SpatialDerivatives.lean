import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakDensityGradientEquation
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree.Extension
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree.Restriction
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialUniqueness
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree.WeightedDivergenceSource
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree.WeightedGradientSource

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
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

private theorem exists_local_lp_second_partial_tree
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (U F : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (K : Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => K k (t, x)) (fun x => U (t, x)) Ω)
    (hweak : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, MetricExtension.densityOnEuclid (G.metric p.1) α p.2 * U p *
        fderiv ℝ φ p (1, 0) ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        (∑ j, ∫ p, (∑ i, MetricExtension.weightedInvGramOnEuclid
            (G.metric p.1) α i j p.2 * K i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) -
        ∫ p, F p * φ p ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let ν := (volume.restrict (Icc c d)).prod (volume.restrict Ω₀)
    ∃ V : ∀ j : ℕ, (Fin j → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν,
      (V 0 (fun i => Fin.elim0 i) =ᵐ[ν] U) ∧
      (∀ k, V 1 (Fin.cons k (fun i => Fin.elim0 i)) =ᵐ[ν] K k) ∧
      ∀ j, j < 2 → ∀ β i, ∀ᵐ t ∂volume.restrict (Icc c d),
        DeGiorgi.HasWeakPartialDeriv i
          (fun x => V (j + 1) (Fin.cons i β) (t, x)) (fun x => V j β (t, x)) Ω₀ := by
  intro ν
  classical
  let μ := volume.restrict (Icc c d)
  have hI : Icc c d ⊆ Icc a b := Icc_subset_Icc hac.le hdb.le
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hμ : μ ≤ volume.restrict (Icc a b) := Measure.restrict_mono hI le_rfl
  have hν : ν ≤ (volume.restrict (Icc a b)).prod (volume.restrict Ω) :=
    Measure.prod_mono hμ (Measure.restrict_mono hsub le_rfl)
  obtain ⟨H, _, hH, _, _, _⟩ :=
    exists_local_lp_time_weak_derivative_of_weighted_weak_equation
      hG hab hreg α hΩ hΩc hΩs U F K hspatial hweak hac hdb hΩ₀ hΩ₀Ω
  have hUmem : MemLp U 2 ν := (Lp.memLp U).mono_measure hν
  have hKmem (i) : MemLp (K i) 2 ν := (Lp.memLp (K i)).mono_measure hν
  let U₀ := hUmem.toLp U
  let K₀ := fun i => (hKmem i).toLp (K i)
  have hU₀ : U₀ =ᵐ[ν] U := hUmem.coeFn_toLp
  have hK₀ (i) : K₀ i =ᵐ[ν] K i := (hKmem i).coeFn_toLp
  have hfirst (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => K₀ i (t, x)) (fun x => U₀ (t, x)) Ω₀ := by
    filter_upwards [(hspatial i).filter_mono (ae_mono hμ),
      Measure.ae_ae_of_ae_prod hU₀, Measure.ae_ae_of_ae_prod (hK₀ i)] with t ht hu hk
    exact (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht).congr_ae
      (Filter.EventuallyEq.symm hu) (Filter.EventuallyEq.symm hk)
  have hsecond (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (t, x)) (fun x => K₀ i (t, x)) Ω₀ := by
    filter_upwards [hH i j, Measure.ae_ae_of_ae_prod (hK₀ i)] with t ht hk
    exact ht.congr_ae (Filter.EventuallyEq.symm hk) Filter.EventuallyEq.rfl
  choose W hroot _ hW using fun i =>
    Sobolev.Euclidean.exists_lp_weak_partial_tree_succ_of_weak_partials
      0 (K₀ i) (H i) (fun j _ _ => H i j) (fun _ => rfl) (hsecond i)
      (fun _ j hj => (Nat.not_lt_zero j hj).elim)
  obtain ⟨V, hVroot, hVone, hVweak⟩ :=
    Sobolev.Euclidean.exists_lp_weak_partial_tree_succ_of_weak_partials
      1 U₀ K₀ W hroot hfirst hW
  refine ⟨V, ?_, ?_, hVweak⟩
  · simpa only [hVroot] using hU₀
  · intro i
    simpa only [hVone] using hK₀ i

theorem exists_local_lp_spatial_weak_partial_tree_of_weighted_weak_equation
    (m : ℕ)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (U F : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (K : Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => K k (t, x)) (fun x => U (t, x)) Ω)
    (hweak : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, MetricExtension.densityOnEuclid (G.metric p.1) α p.2 * U p *
        fderiv ℝ φ p (1, 0) ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        (∑ j, ∫ p, (∑ i, MetricExtension.weightedInvGramOnEuclid
            (G.metric p.1) α i j p.2 * K i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) -
        ∫ p, F p * φ p ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    (FTree : ∀ j : ℕ, (Fin j → Fin (Module.finrank ℝ EuN)) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hFroot : FTree 0 (fun i => Fin.elim0 i) = F)
    (hFweak : ∀ j, j < m → ∀ β i, ∀ᵐ t ∂volume.restrict (Icc a b),
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => FTree (j + 1) (Fin.cons i β) (t, x))
        (fun x => FTree j β (t, x)) Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let ν := (volume.restrict (Icc c d)).prod (volume.restrict Ω₀)
    ∃ V : ∀ j : ℕ, (Fin j → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν,
      (V 0 (fun i => Fin.elim0 i) =ᵐ[ν] U) ∧
      (∀ k, V 1 (Fin.cons k (fun i => Fin.elim0 i)) =ᵐ[ν] K k) ∧
      ∀ j, j < m + 2 → ∀ β i, ∀ᵐ t ∂volume.restrict (Icc c d),
        DeGiorgi.HasWeakPartialDeriv i
          (fun x => V (j + 1) (Fin.cons i β) (t, x)) (fun x => V j β (t, x)) Ω₀ := by
  dsimp only
  classical
  induction m generalizing a b Ω U F K c d Ω₀ with
  | zero =>
      exact exists_local_lp_second_partial_tree hG hab hreg α hΩ hΩc hΩs
        U F K hspatial hweak hac hdb hΩ₀ hΩ₀Ω
  | succ m ih =>
      by_cases hcd : c ≤ d
      swap
      · refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩ <;>
          simp [Icc_eq_empty_of_lt (lt_of_not_ge hcd), Filter.EventuallyEq]
      let e : Fin 0 → Fin (Module.finrank ℝ EuN) := fun i => Fin.elim0 i
      let ρ := fun q : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric q.1) α q.2
      let A := fun i j (q : ℝ × EuStd) =>
        MetricExtension.weightedInvGramOnEuclid (G.metric q.1) α i j q.2
      have hΩ₀c : IsCompact (closure Ω₀) :=
        hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
      obtain ⟨Ω₁, hΩ₁, hΩ₀₁, hΩ₁Ω⟩ :=
        hΩ₀c.exists_isOpen_closure_subset (hΩ.mem_nhdsSet.mpr hΩ₀Ω)
      have hΩ₁c : IsCompact (closure Ω₁) :=
        hΩc.of_isClosed_subset isClosed_closure (hΩ₁Ω.trans subset_closure)
      have hΩ₁s := hΩ₁Ω.trans (subset_closure.trans hΩs)
      let c₁ := (a + c) / 2
      let d₁ := (d + b) / 2
      have hac₁ : a < c₁ := by dsimp [c₁]; linarith
      have hc₁c : c₁ < c := by dsimp [c₁]; linarith
      have hdd₁ : d < d₁ := by dsimp [d₁]; linarith
      have hd₁b : d₁ < b := by dsimp [d₁]; linarith
      have hc₁d₁ : c₁ < d₁ := hc₁c.trans_le (hcd.trans hdd₁.le)
      have hI₁ : Icc c₁ d₁ ⊆ Icc a b := Icc_subset_Icc hac₁.le hd₁b.le
      have hI₀ : Icc c d ⊆ Icc c₁ d₁ := Icc_subset_Icc hc₁c.le hdd₁.le
      have hsub₁ : Ω₁ ⊆ Ω := subset_closure.trans hΩ₁Ω
      have hsub₀ : Ω₀ ⊆ Ω₁ := subset_closure.trans hΩ₀₁
      let μ₁ := volume.restrict (Icc c₁ d₁)
      let ν₁ := μ₁.prod (volume.restrict Ω₁)
      let ν₀ := (volume.restrict (Icc c d)).prod (volume.restrict Ω₀)
      have hμ₁ : μ₁ ≤ volume.restrict (Icc a b) := Measure.restrict_mono hI₁ le_rfl
      have hμ₀ : volume.restrict (Icc c d) ≤ μ₁ := Measure.restrict_mono hI₀ le_rfl
      have hν₀ : ν₀ ≤ ν₁ :=
        Measure.prod_mono hμ₀ (Measure.restrict_mono hsub₀ le_rfl)
      have hν₁ : ν₁ ≤ (volume.restrict (Icc a b)).prod (volume.restrict Ω) :=
        Measure.prod_mono hμ₁ (Measure.restrict_mono hsub₁ le_rfl)
      obtain ⟨V, hVzero, hVone, hVweak⟩ :=
        ih hab hreg hΩ hΩc hΩs U F K hspatial hweak FTree hFroot
          (fun j hj => hFweak j (by omega)) hac₁ hd₁b hΩ₁ hΩ₁Ω
      have hFroot' : FTree 0 e = F := hFroot
      let DF := fun k => FTree 1 (Fin.cons k e)
      have hDF (k) : ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
          (fun x => DF k (t, x)) (fun x => F (t, x)) Ω := by
        simpa only [DF, hFroot'] using hFweak 0 (by omega) e k
      obtain ⟨H, R, S, hH, hHcomm, _, hRformula, hSformula, hSeq⟩ :=
        exists_local_lp_weak_gradient_equation_of_weighted_weak_equation
          hG hab hreg α hΩ hΩc hΩs U F K hspatial hweak DF hDF
          hac₁ hd₁b hΩ₁ hΩ₁Ω
      have hHmatch (i j) : H i j = V 2 (Fin.cons j (Fin.cons i e)) := by
        apply Sobolev.Euclidean.lp_eq_of_ae_hasWeakPartialDeriv hΩ₁ (by norm_num) j
          (fun t x => K i (t, x)) (H i j) (V 2 (Fin.cons j (Fin.cons i e))) (hH i j)
        filter_upwards [hVweak 1 (by omega) (Fin.cons i e) j,
          Measure.ae_ae_of_ae_prod (hVone i)] with t ht he
        exact ht.congr_ae he Filter.EventuallyEq.rfl
      obtain ⟨F₁, hF₁eq, hF₁weak⟩ :=
        Sobolev.Euclidean.exists_lp_weak_partial_tree_restrict
          hμ₁ hΩ₁ hsub₁ (m + 1) FTree hFweak
      have hF₁root : F₁ 0 e =ᵐ[ν₁] F := by
        simpa only [hFroot'] using hF₁eq 0 e
      let O := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
      have hO : IsOpen O := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
      have hOt : O ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
        image_mono interior_subset
      have hAsmooth (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ O) :=
        MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α
          Subset.rfl i j
      have hρsmooth : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ O) :=
        (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
          (prod_mono Subset.rfl hOt)
      have hρne (q : ℝ × EuStd) (hq : q ∈ D.regular ×ˢ O) : ρ q ≠ 0 :=
        (MetricExtension.densityOnEuclid_pos (G.metric q.1) α (hOt hq.2)).ne'
      have hRformulaV : R =ᵐ[ν₁] fun q => (ρ q)⁻¹ *
          ((∑ i, ∑ j, (A i j q * V 2 (Fin.cons j (Fin.cons i e)) q +
            fderiv ℝ (fun x => A i j (q.1, x)) q.2 (EuclideanSpace.single j 1) *
              V 1 (Fin.cons i e) q)) +
                F₁ 0 e q - fderiv ℝ ρ q (1, 0) * V 0 e q) := by
        filter_upwards [hRformula, hVzero, ae_all_iff.mpr hVone, hF₁root]
          with q hq hu hk hf
        simpa only [hHmatch, ← hu, ← hk, ← hf] using hq
      obtain ⟨RTree, hRroot, hRweak⟩ :=
        Sobolev.Euclidean.exists_lp_weak_partial_tree_of_weighted_divergence_source
          (by norm_num) D.regular_isOpen isCompact_Icc (hI₁.trans hreg) hO hΩ₁ hΩ₁c hΩ₁s m
          ρ A hρsmooth hρne hAsmooth V F₁ R hVweak
          (fun j hj => hF₁weak j (by omega)) hRformulaV
      have hRroot' : RTree 0 e = R := hRroot
      have hSformulaV (k) : S k =ᵐ[ν₁] fun q => F₁ 1 (Fin.cons k e) q +
          (∑ i, ∑ j, (fderiv ℝ (A i j) q (0, EuclideanSpace.single k 1) *
            V 2 (Fin.cons j (Fin.cons i e)) q +
            fderiv ℝ (fun w => fderiv ℝ (A i j) w (0, EuclideanSpace.single k 1)) q
              (0, EuclideanSpace.single j 1) * V 1 (Fin.cons i e) q)) -
          (fderiv ℝ ρ q (0, EuclideanSpace.single k 1) * RTree 0 e q +
            fderiv ℝ (fun w => fderiv ℝ ρ w (0, EuclideanSpace.single k 1)) q (1, 0) *
              V 0 e q) := by
        filter_upwards [hSformula k, hVzero, ae_all_iff.mpr hVone,
          hF₁eq 1 (Fin.cons k e)] with q hq hu hk hf
        simpa only [hHmatch, ← hu, ← hk, hRroot', DF, ← hf] using hq
      obtain ⟨STree, hSroot, hSweak⟩ :=
        Sobolev.Euclidean.exists_lp_weak_partial_tree_of_weighted_gradient_source
          (by norm_num) D.regular_isOpen isCompact_Icc (hI₁.trans hreg) hO hΩ₁ hΩ₁c hΩ₁s m
          ρ A hρsmooth hAsmooth V F₁ RTree S hVweak hF₁weak hRweak hSformulaV
      have hKspatial (k i) : ∀ᵐ t ∂μ₁, DeGiorgi.HasWeakPartialDeriv i
          (fun x => H i k (t, x)) (fun x => V 1 (Fin.cons k e) (t, x)) Ω₁ := by
        filter_upwards [hHcomm i k, Measure.ae_ae_of_ae_prod (hVone k)] with t ht he
        exact ht.congr_ae (Filter.EventuallyEq.symm he) Filter.EventuallyEq.rfl
      have hKweak (k) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
          (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c₁ d₁ ×ˢ Ω₁) :
          (∫ q, ρ q * V 1 (Fin.cons k e) q * fderiv ℝ φ q (1, 0) ∂ν₁) =
            (∑ j, ∫ q, (∑ i, A i j q * H i k q) *
              fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν₁) -
              ∫ q, S k q * φ q ∂ν₁ := by
        calc
          _ = ∫ q, ρ q * K k q * fderiv ℝ φ q (1, 0) ∂ν₁ := by
            apply integral_congr_ae
            filter_upwards [hVone k] with q hq
            rw [hq]
          _ = _ := hSeq k φ hφ hφc hφs
      have hKregular (k) :=
        ih hc₁d₁ (hI₁.trans hreg) hΩ₁ hΩ₁c hΩ₁s
          (V 1 (Fin.cons k e)) (S k) (fun i => H i k) (hKspatial k) (hKweak k)
          (STree k) (hSroot k) (hSweak k) hc₁c hdd₁ hΩ₀ hΩ₀₁
      choose W hWzero _ hWweak using hKregular
      have hUmem : MemLp U 2 ν₀ := (Lp.memLp U).mono_measure (hν₀.trans hν₁)
      let U₀ := hUmem.toLp U
      have hU₀ : U₀ =ᵐ[ν₀] U := hUmem.coeFn_toLp
      have hK₀ (k) : W k 0 e =ᵐ[ν₀] K k :=
        (hWzero k).trans ((hVone k).filter_mono (ae_mono hν₀))
      have hfirst (k) : ∀ᵐ t ∂volume.restrict (Icc c d), DeGiorgi.HasWeakPartialDeriv k
          (fun x => W k 0 e (t, x)) (fun x => U₀ (t, x)) Ω₀ := by
        filter_upwards [(hspatial k).filter_mono (ae_mono (hμ₀.trans hμ₁)),
          Measure.ae_ae_of_ae_prod hU₀, Measure.ae_ae_of_ae_prod (hK₀ k)] with t ht hu hk
        exact (DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ (hsub₀.trans hsub₁) ht).congr_ae
          (Filter.EventuallyEq.symm hu) (Filter.EventuallyEq.symm hk)
      obtain ⟨Y, hYroot, hYone, hYweak⟩ :=
        Sobolev.Euclidean.exists_lp_weak_partial_tree_succ_of_weak_partials
          (m + 2) U₀ (fun k => W k 0 e) W (fun _ => rfl) hfirst hWweak
      refine ⟨Y, ?_, ?_, ?_⟩
      · simpa only [hYroot] using hU₀
      · intro k
        simpa only [hYone] using hK₀ k
      · simpa only [Nat.add_assoc, Nat.add_comm 1 2] using hYweak

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
