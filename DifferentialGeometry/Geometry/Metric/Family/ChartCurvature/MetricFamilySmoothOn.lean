import DifferentialGeometry.Analysis.Calculus.TimeJetCommute
import DifferentialGeometry.Geometry.Connection.ChartBridge.Christoffel
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Metric.Family.PairSmoothness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

namespace MetricFamilySmoothOn

omit [FiniteDimensional Real E] [CompleteSpace E] in
private theorem spatialJet_contDiffOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    {G : Real → E → F} {J : Set Real} {V : Set E}
    (hJ : UniqueDiffOn Real J) (hV : IsOpen V)
    (hG : ContDiffOn Real ∞ (Function.uncurry G) (J ×ˢ V))
    (k : Nat) (hk : k ≤ 2) :
    ContDiffOn Real ∞
      (Function.uncurry (fun t y => iteratedFDeriv Real k (G t) y)) (J ×ˢ V) := by
  interval_cases k
  · refine ((continuousMultilinearCurryFin0 Real E F).symm.contDiff.comp_contDiffOn hG).congr ?_
    rintro ⟨t, y⟩ _
    rfl
  · have hfd := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn hJ hV hG
    refine ((continuousMultilinearCurryFin1 Real E F).symm.contDiff.comp_contDiffOn hfd).congr ?_
    rintro ⟨t, y⟩ _
    ext v
    simp only [Function.comp_apply, Function.uncurry_apply_pair,
      continuousMultilinearCurryFin1_symm_apply, iteratedFDeriv_one_apply]
  · have hfd := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn hJ hV hG
    have hfd2 := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t y => fderiv Real (G t) y) hJ hV hfd
    have hcurried :=
      (continuousMultilinearCurryFin1 Real E (E →L[Real] F)).symm.contDiff.comp_contDiffOn hfd2
    let :
        NormedAddCommGroup
          (ContinuousMultilinearMap Real (fun _ : Fin 1 => E) (E →L[Real] F)) :=
      ContinuousMultilinearMap.normedAddCommGroup
    refine ((continuousMultilinearCurryRightEquiv' Real 1 E F).symm.contDiff.comp_contDiffOn
      hcurried).congr ?_
    rintro ⟨t, y⟩ _
    ext v
    simp only [Function.comp_apply, Function.uncurry_apply_pair, iteratedFDeriv_two_apply]
    rfl

omit [CompleteSpace E] in
theorem chartGramOnE_contDiffOn
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJ : J ⊆ D.regular) (α : M)
    (i j : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E => chartGramOnE (I := I) (g_fam p.1) α i j p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) α
  let b := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) (e.localFrame b) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  have hsmooth := hG.frameCompSmooth (e.localFrame b) hframe i j
  have hsymm : ContMDiffOn 𝓘(Real, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hσ1 : ContMDiffOn 𝓘(Real, Real × E) 𝓘(Real, Real) ∞
      (fun p : Real × E => p.1) (J ×ˢ interior (extChartAt I α).target) :=
    (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffOn
  have hsnd : ContMDiffOn 𝓘(Real, Real × E) 𝓘(Real, E) ∞
      (fun p : Real × E => p.2) (J ×ˢ interior (extChartAt I α).target) :=
    (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffOn
  have hmaps2 : MapsTo (fun p : Real × E => p.2)
      (J ×ˢ interior (extChartAt I α).target) (extChartAt I α).target :=
    fun p hp => interior_subset hp.2
  have hσ2 : ContMDiffOn 𝓘(Real, Real × E) I ∞
      (fun p : Real × E => (extChartAt I α).symm p.2)
      (J ×ˢ interior (extChartAt I α).target) :=
    hsymm.comp hsnd hmaps2
  have hσ : ContMDiffOn 𝓘(Real, Real × E) (𝓘(Real, Real).prod I) ∞
      (fun p : Real × E => (p.1, (extChartAt I α).symm p.2))
      (J ×ˢ interior (extChartAt I α).target) := hσ1.prodMk hσ2
  have hmaps : MapsTo (fun p : Real × E => (p.1, (extChartAt I α).symm p.2))
      (J ×ˢ interior (extChartAt I α).target) (D.regular ×ˢ e.baseSet) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    refine ⟨hJ ht, ?_⟩
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target (interior_subset hy)
    change (extChartAt I α).symm y ∈ (chartAt H α).source
    rwa [← extChartAt_source_eq_chartAt_source (I := I)]
  have hcomp := hsmooth.comp hσ hmaps
  refine hcomp.contDiffOn.congr ?_
  rintro ⟨t, y⟩ hp
  change chartGramOnE (I := I) (g_fam t) α i j y =
    (g_fam t).inner ((extChartAt I α).symm y)
      (e.localFrame b i ((extChartAt I α).symm y))
      (e.localFrame b j ((extChartAt I α).symm y))
  rw [e.localFrame_apply_of_mem_baseSet b (hmaps hp).2,
    e.localFrame_apply_of_mem_baseSet b (hmaps hp).2]
  have hbase : (extChartAt I α).symm y ∈
      (trivializationAt E (TangentSpace I) α).baseSet := (hmaps hp).2
  simp only [chartGramOnE, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix, Matrix.of_apply, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber,
    Trivialization.basisAt, Module.Basis.map_apply, e, b,
    Trivialization.linearEquivAt_symm_apply]
  rw [Trivialization.symmL_apply _ hbase, Trivialization.symmL_apply _ hbase]

omit [CompleteSpace E] in
theorem chartGram_jet_continuousOn
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) {S : Set (Real × M)}
    (hS : S ⊆ J ×ˢ chartLeviCivitaGoodSet (I := I) α)
    (k : Nat) (hk : k ≤ 2) (i j : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun q : Real × M =>
        iteratedFDeriv Real k
          (chartGramOnE (I := I) (g_fam q.1) α i j)
          (extChartAt I α q.2)) S := by
  have hF := chartGramOnE_contDiffOn (I := I) hG hJreg α i j
  have hcore := (spatialJet_contDiffOn
    (G := fun t y => chartGramOnE (I := I) (g_fam t) α i j y)
    hJ isOpen_interior hF k hk).continuousOn
  have hΨcont : ContinuousOn (fun q : Real × M => (q.1, extChartAt I α q.2)) S :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) α).comp continuous_snd.continuousOn
        (fun q hq => chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) (hS hq).2))
  have hΨmaps : MapsTo (fun q : Real × M => (q.1, extChartAt I α q.2)) S
      (J ×ˢ interior (extChartAt I α).target) :=
    fun q hq => ⟨(hS hq).1,
      chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) (hS hq).2⟩
  exact (hcore.comp hΨcont hΨmaps).congr fun _ _ => rfl

omit [CompleteSpace E] in
theorem chartGramPartialOnE_contDiffOn
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) (m i j : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E =>
        partialDeriv (E := E) m (chartGramOnE (I := I) (g_fam p.1) α i j) p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  have hF := chartGramOnE_contDiffOn (I := I) hG hJreg α i j
  have hfd := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := fun t y => chartGramOnE (I := I) (g_fam t) α i j y)
    hJ isOpen_interior hF
  exact (hfd.clm_apply (contDiffOn_const (c := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E m))).congr fun _ _ => rfl

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [FiniteDimensional Real E] [CompleteSpace E] in
private theorem matrixDet_contDiffOn {s : Set (Real × E)}
    {A : Real × E → Matrix n n Real}
    (hA : ∀ i j, ContDiffOn Real ∞ (fun p : Real × E => A p i j) s) :
    ContDiffOn Real ∞ (fun p : Real × E => (A p).det) s := by
  classical
  simp_rw [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ => ?_
  exact contDiffOn_const.mul (contDiffOn_prod fun i _ => hA (σ i) i)

omit [FiniteDimensional Real E] [CompleteSpace E] in
private theorem matrixAdjugate_contDiffOn {s : Set (Real × E)}
    {A : Real × E → Matrix n n Real}
    (hA : ∀ i j, ContDiffOn Real ∞ (fun p : Real × E => A p i j) s)
    (a b : n) :
    ContDiffOn Real ∞ (fun p : Real × E => (A p).adjugate a b) s := by
  classical
  simp_rw [Matrix.adjugate_apply]
  refine matrixDet_contDiffOn (A := fun p => (A p).updateRow b (Pi.single a 1)) ?_
  intro i j
  by_cases hij : i = b
  · subst hij
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simpa only [Matrix.updateRow_ne hij] using hA i j

omit [FiniteDimensional Real E] [CompleteSpace E] in
private theorem matrixInv_entry_contDiffOn {s : Set (Real × E)}
    {A : Real × E → Matrix n n Real}
    (hA : ∀ i j, ContDiffOn Real ∞ (fun p : Real × E => A p i j) s)
    (hdet : ∀ p ∈ s, (A p).det ≠ 0) (a b : n) :
    ContDiffOn Real ∞ (fun p : Real × E => (A p)⁻¹ a b) s := by
  classical
  have hrewrite : (fun p : Real × E => (A p)⁻¹ a b) =
      fun p : Real × E => (A p).det⁻¹ * (A p).adjugate a b := by
    funext p
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hrewrite]
  exact ((matrixDet_contDiffOn hA).inv hdet).mul
    (matrixAdjugate_contDiffOn hA a b)

omit [CompleteSpace E] in
theorem chartInvGramOnE_contDiffOn
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJreg : J ⊆ D.regular) (α : M)
    (a b : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E => chartInvGramOnE (I := I) (g_fam p.1) α a b p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  let A : Real × E →
      Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    fun p => Matrix.of fun i j => chartGramOnE (I := I) (g_fam p.1) α i j p.2
  have hA : ∀ i j, ContDiffOn Real ∞ (fun p : Real × E => A p i j)
      (J ×ˢ interior (extChartAt I α).target) := by
    intro i j
    simpa [A] using chartGramOnE_contDiffOn (I := I) hG hJreg α i j
  have hdet : ∀ p ∈ J ×ˢ interior (extChartAt I α).target, (A p).det ≠ 0 := by
    intro p hp
    have hbase : (extChartAt I α).symm p.2 ∈
        (trivializationAt E (TangentSpace I) α).baseSet := by
      have hsource : (extChartAt I α).symm p.2 ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target (interior_subset hp.2)
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
      rwa [trivializationAt_baseSet_eq_chartAt_source]
    have hpos : 0 < (A p).det := by
      rw [show A p = DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.1) α
          ((extChartAt I α).symm p.2) by
        ext i j
        rfl]
      exact DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) (g_fam p.1) α hbase
    exact ne_of_gt hpos
  have hinv := matrixInv_entry_contDiffOn (A := A) hA hdet a b
  refine hinv.congr ?_
  intro p _
  simp only [A, chartInvGramOnE_def]
  rfl

omit [CompleteSpace E] in
theorem chartInvGramOnE_continuousOn
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJreg : J ⊆ D.regular) (α : M)
    (a b : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × E => chartInvGramOnE (I := I) (g_fam p.1) α a b p.2)
      (J ×ˢ interior (extChartAt I α).target) :=
  (chartInvGramOnE_contDiffOn (I := I) hG hJreg α a b).continuousOn

omit [CompleteSpace E] in
theorem chartChristoffelOnE_contDiffOn
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) (i j k : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E => chartChristoffel (I := I) (g_fam p.1) α i j k p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  rw [show (fun p : Real × E =>
      chartChristoffel (I := I) (g_fam p.1) α i j k p.2) =
      fun p : Real × E => (1 / 2 : Real) *
        ∑ l : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) (g_fam p.1) α k l p.2 *
            (partialDeriv (E := E) i
                (chartGramOnE (I := I) (g_fam p.1) α l j) p.2 +
              partialDeriv (E := E) j
                (chartGramOnE (I := I) (g_fam p.1) α l i) p.2 -
              partialDeriv (E := E) l
                (chartGramOnE (I := I) (g_fam p.1) α i j) p.2) by
    funext p
    rw [chartChristoffel_def]
    rfl]
  refine contDiffOn_const.mul (ContDiffOn.sum fun l _ => ?_)
  exact (chartInvGramOnE_contDiffOn (I := I) hG hJreg α k l).mul
    (((chartGramPartialOnE_contDiffOn (I := I) hG hJreg hJ α i l j).add
      (chartGramPartialOnE_contDiffOn (I := I) hG hJreg hJ α j l i)).sub
      (chartGramPartialOnE_contDiffOn (I := I) hG hJreg hJ α l i j))

omit [CompleteSpace E] in
theorem chartChristoffelOnE_continuousOn
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) (i j k : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × E => chartChristoffel (I := I) (g_fam p.1) α i j k p.2)
      (J ×ˢ interior (extChartAt I α).target) :=
  (chartChristoffelOnE_contDiffOn (I := I) hG hJreg hJ α i j k).continuousOn

end MetricFamilySmoothOn

end DifferentialGeometry.Geometry.Curvature
