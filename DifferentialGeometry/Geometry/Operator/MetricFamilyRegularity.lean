import DifferentialGeometry.Analysis.Calculus.TimeJetCommute
import DifferentialGeometry.Geometry.Connection.ChartBridge.Laplacian
import DifferentialGeometry.Geometry.Curvature.Realized.Operators
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyPair
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Operator.HessianTraceChartGramRegularity

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
    letI :
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
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJ : J ⊆ D.regular) (α : M)
    (i j : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E => chartGramOnE (I := I) (G.metric p.1) α i j p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) α
  let b := chartModelBasis E
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
  change chartGramOnE (I := I) (G.metric t) α i j y =
    (G.metric t).inner ((extChartAt I α).symm y)
      (e.localFrame b i ((extChartAt I α).symm y))
      (e.localFrame b j ((extChartAt I α).symm y))
  rw [e.localFrame_apply_of_mem_baseSet b (hmaps hp).2,
    e.localFrame_apply_of_mem_baseSet b (hmaps hp).2]
  rfl

omit [CompleteSpace E] in
theorem chartGram_jet_continuousOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) {S : Set (Real × M)}
    (hS : S ⊆ J ×ˢ chartLeviCivitaGoodSet (I := I) α)
    (k : Nat) (hk : k ≤ 2) (i j : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun q : Real × M =>
        iteratedFDeriv Real k
          (chartGramOnE (I := I) (G.metric q.1) α i j)
          (extChartAt I α q.2)) S := by
  have hF := chartGramOnE_contDiffOn (I := I) hG hJreg α i j
  have hcore := (spatialJet_contDiffOn
    (G := fun t y => chartGramOnE (I := I) (G.metric t) α i j y)
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
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) (m i j : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E =>
        partialDeriv (E := E) m (chartGramOnE (I := I) (G.metric p.1) α i j) p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  have hF := chartGramOnE_contDiffOn (I := I) hG hJreg α i j
  have hfd := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := fun t y => chartGramOnE (I := I) (G.metric t) α i j y)
    hJ isOpen_interior hF
  exact (hfd.clm_apply (contDiffOn_const (c := chartModelBasis E m))).congr fun _ _ => rfl

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
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (α : M)
    (a b : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E => chartInvGramOnE (I := I) (G.metric p.1) α a b p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  let A : Real × E →
      Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    fun p => Matrix.of fun i j => chartGramOnE (I := I) (G.metric p.1) α i j p.2
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
      rw [show A p = chartGramMatrix (I := I) (G.metric p.1) α
          ((extChartAt I α).symm p.2) by
        ext i j
        rfl]
      exact chartGramMatrix_det_pos (I := I) (G.metric p.1) α hbase
    exact ne_of_gt hpos
  have hinv := matrixInv_entry_contDiffOn (A := A) hA hdet a b
  refine hinv.congr ?_
  intro p _
  simp only [A, chartInvGramOnE_def]
  rfl

omit [CompleteSpace E] in
theorem chartInvGramOnE_continuousOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (α : M)
    (a b : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × E => chartInvGramOnE (I := I) (G.metric p.1) α a b p.2)
      (J ×ˢ interior (extChartAt I α).target) :=
  (chartInvGramOnE_contDiffOn (I := I) hG hJreg α a b).continuousOn

omit [CompleteSpace E] in
theorem chartChristoffelOnE_contDiffOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) (i j k : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E => chartChristoffel (I := I) (G.metric p.1) α i j k p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  rw [show (fun p : Real × E =>
      chartChristoffel (I := I) (G.metric p.1) α i j k p.2) =
      fun p : Real × E => (1 / 2 : Real) *
        ∑ l : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) (G.metric p.1) α k l p.2 *
            (partialDeriv (E := E) i
                (chartGramOnE (I := I) (G.metric p.1) α l j) p.2 +
              partialDeriv (E := E) j
                (chartGramOnE (I := I) (G.metric p.1) α l i) p.2 -
              partialDeriv (E := E) l
                (chartGramOnE (I := I) (G.metric p.1) α i j) p.2) by
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
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) (i j k : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × E => chartChristoffel (I := I) (G.metric p.1) α i j k p.2)
      (J ×ˢ interior (extChartAt I α).target) :=
  (chartChristoffelOnE_contDiffOn (I := I) hG hJreg hJ α i j k).continuousOn

omit [CompleteSpace E] in
private theorem partialDeriv_contDiffOn
    {f : E → Real} {V : Set E} (hV : IsOpen V)
    (hf : ContDiffOn Real ∞ f V) (i : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞ (partialDeriv (E := E) i f) V := by
  have hfd : ContDiffOn Real ∞ (fderiv Real f) V :=
    hf.fderiv_of_isOpen hV (by rw [ENat.coe_top_add_one])
  exact hfd.clm_apply contDiffOn_const

omit [CompleteSpace E] in
private theorem scalarPartialOnE_continuousOn
    (α : M) {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ)
    (J : Set Real) (i : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × E =>
        partialDeriv (E := E) i (scalarOnE (I := I) α ρ) p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  have hρE : ContDiffOn Real ∞ (scalarOnE (I := I) α ρ)
      (interior (extChartAt I α).target) :=
    (scalarOnE_contDiffOn (I := I) α hρ).mono interior_subset
  have hpartial := partialDeriv_contDiffOn isOpen_interior hρE i
  exact hpartial.continuousOn.comp continuousOn_snd fun p hp => hp.2

omit [CompleteSpace E] in
private theorem scalarSecondPartialOnE_continuousOn
    (α : M) {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ)
    (J : Set Real) (i j : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × E =>
        partialDeriv (E := E) i
          (partialDeriv (E := E) j (scalarOnE (I := I) α ρ)) p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  have hρE : ContDiffOn Real ∞ (scalarOnE (I := I) α ρ)
      (interior (extChartAt I α).target) :=
    (scalarOnE_contDiffOn (I := I) α hρ).mono interior_subset
  have hfirst := partialDeriv_contDiffOn isOpen_interior hρE j
  have hsecond := partialDeriv_contDiffOn isOpen_interior hfirst i
  exact hsecond.continuousOn.comp continuousOn_snd fun p hp => hp.2

omit [CompleteSpace E] in
private theorem gradientCoeffOnE_continuousOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    (α : M) {ρ : M → Real}
    (hρ : ContMDiff I (modelWithCornersSelf Real Real) ∞ ρ)
    (i : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × E =>
        ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) (G.metric p.1) α i j p.2 *
            partialDeriv (E := E) j (scalarOnE (I := I) α ρ) p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  refine continuousOn_finset_sum _ fun j _ => ?_
  exact (chartInvGramOnE_continuousOn (I := I) hG hJreg α i j).mul
    (scalarPartialOnE_continuousOn (I := I) α hρ J j)

omit [CompleteSpace E] in
theorem gradient_continuousOn [I.Boundaryless]
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    {ρ : M → Real}
    (hρ : ContMDiff I (modelWithCornersSelf Real Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        (TotalSpace.mk' E p.2
          (gradFun (I := I) (G.metric p.1) ρ p.2) : TangentBundle I M))
      (J ×ˢ (Set.univ : Set M)) := by
  classical
  refine continuousOn_of_locally_continuousOn ?_
  intro p hp
  let α := p.2
  let e := trivializationAt E (TangentSpace I : M → Type _) α
  let U : Set (Real × M) := Set.univ ×ˢ e.baseSet
  have hpU : p ∈ U := ⟨Set.mem_univ _, by simp [e, α]⟩
  refine ⟨U, isOpen_univ.prod e.open_baseSet, hpU, ?_⟩
  let S : Set (Real × M) := J ×ˢ e.baseSet
  let ψ : Real × M → Real × E := fun q => (q.1, extChartAt I α q.2)
  have hψ : ContinuousOn ψ S :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) α).comp continuous_snd.continuousOn
        fun q hq => by
          rw [extChartAt_source_eq_chartAt_source (I := I)]
          simpa [e] using hq.2)
  have hmapsψ : MapsTo ψ S
      (J ×ˢ interior (extChartAt I α).target) := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    apply extChartAt_target_subset_interior_of_boundaryless (I := I) α
    apply (extChartAt I α).map_source
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    simpa [e] using hq.2
  let coeff : Fin (Module.finrank Real E) → Real × M → Real := fun i q =>
    ∑ j : Fin (Module.finrank Real E),
      chartInvGramOnE (I := I) (G.metric q.1) α i j (extChartAt I α q.2) *
        partialDeriv (E := E) j (scalarOnE (I := I) α ρ) (extChartAt I α q.2)
  have hcoeff : ∀ i, ContinuousOn (coeff i) S := by
    intro i
    simpa only [coeff, ψ, Function.comp_apply] using
      (gradientCoeffOnE_continuousOn (I := I) hG hJreg α hρ i).comp hψ hmapsψ
  let coord : Real × M → E := fun q =>
    ∑ i : Fin (Module.finrank Real E), coeff i q • chartModelBasis E i
  have hcoord : ContinuousOn coord S := by
    refine continuousOn_finset_sum _ fun i _ => ?_
    exact (hcoeff i).smul continuousOn_const
  let toPair : Real × M → M × E := fun q => (q.2, coord q)
  have hpair : ContinuousOn toPair S :=
    continuous_snd.continuousOn.prodMk hcoord
  have hmapsPair : MapsTo toPair S (e.baseSet ×ˢ (Set.univ : Set E)) := by
    intro q hq
    exact ⟨hq.2, Set.mem_univ _⟩
  have htotal := e.continuousOn_symm.comp hpair hmapsPair
  refine (htotal.congr ?_).mono ?_
  · intro q hq
    have hbase : q.2 ∈ e.baseSet := hq.2
    have hsource : q.2 ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      simpa [e] using hbase
    have hcoord_eq : coord q =
        ∑ i : Fin (Module.finrank Real E),
          gradChartCoeff (I := I) (G.metric q.1) α ρ i q.2 • chartModelBasis E i := by
      simp only [coord, coeff, gradChartCoeff_def, chartInvGramOnE_def]
      rw [(extChartAt I α).left_inv hsource]
    change (TotalSpace.mk' E q.2
      (gradFun (I := I) (G.metric q.1) ρ q.2) : TangentBundle I M) =
        TotalSpace.mk' E q.2 (e.symm q.2 (coord q))
    congr 1
    change gradFun (I := I) (G.metric q.1) ρ q.2 =
      e.symmL Real q.2 (coord q)
    rw [hcoord_eq, map_sum]
    simp only [map_smul]
    rw [← gradChartLocal_eq_gradFun (I := I) (G.metric q.1) α
      (hρ.mdifferentiable (by simp) q.2) hbase
      (extChartAt_target_subset_interior_of_boundaryless (I := I) α
        ((extChartAt I α).map_source hsource))]
    symm
    unfold gradChartLocal
    apply Finset.sum_congr rfl
    intro i _
    rw [chartBasisVecFiber, Trivialization.symmL_apply]
  · intro q hq
    exact ⟨hq.1.1, hq.2.2⟩

omit [CompleteSpace E] in
private theorem gradientNormSqOnE_continuousOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    (α : M) {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × E =>
        ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) (G.metric p.1) α i j p.2 *
            partialDeriv (E := E) j (scalarOnE (I := I) α ρ) p.2 *
            partialDeriv (E := E) i (scalarOnE (I := I) α ρ) p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  refine continuousOn_finset_sum _ fun i _ =>
    continuousOn_finset_sum _ fun j _ => ?_
  exact ((chartInvGramOnE_continuousOn (I := I) hG hJreg α i j).mul
    (scalarPartialOnE_continuousOn (I := I) α hρ J j)).mul
    (scalarPartialOnE_continuousOn (I := I) α hρ J i)

omit [CompleteSpace E] in
private theorem leviCivitaLaplacianOnE_continuousOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × E =>
        ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) (G.metric p.1) α i j p.2 *
            (partialDeriv (E := E) i
                (partialDeriv (E := E) j (scalarOnE (I := I) α ρ)) p.2 -
              ∑ k : Fin (Module.finrank Real E),
                chartChristoffel (I := I) (G.metric p.1) α i j k p.2 *
                  partialDeriv (E := E) k (scalarOnE (I := I) α ρ) p.2))
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  refine continuousOn_finset_sum _ fun i _ =>
    continuousOn_finset_sum _ fun j _ => ?_
  refine (chartInvGramOnE_continuousOn (I := I) hG hJreg α i j).mul ?_
  refine (scalarSecondPartialOnE_continuousOn (I := I) α hρ J i j).sub ?_
  refine continuousOn_finset_sum _ fun k _ => ?_
  exact (chartChristoffelOnE_continuousOn (I := I) hG hJreg hJ α i j k).mul
    (scalarPartialOnE_continuousOn (I := I) α hρ J k)

omit [CompleteSpace E] in
theorem gradient_norm_sq_continuousOn [I.Boundaryless]
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) ρ p.2)
          (gradientFun (I := I) (G.metric p.1) ρ p.2))
      (J ×ˢ (Set.univ : Set M)) := by
  classical
  refine continuousOn_of_locally_continuousOn ?_
  intro p hp
  let α := p.2
  let U : Set (Real × M) := Set.univ ×ˢ chartLeviCivitaGoodSet (I := I) α
  have hpU : p ∈ U := ⟨Set.mem_univ _, self_mem_chartLeviCivitaGoodSet (I := I) (α := α)⟩
  refine ⟨U, isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) α), hpU, ?_⟩
  let S : Set (Real × M) := J ×ˢ chartLeviCivitaGoodSet (I := I) α
  have hψ : ContinuousOn (fun q : Real × M => (q.1, extChartAt I α q.2)) S :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) α).comp continuous_snd.continuousOn
        fun q hq => chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq.2)
  have hmaps : MapsTo (fun q : Real × M => (q.1, extChartAt I α q.2)) S
      (J ×ˢ interior (extChartAt I α).target) :=
    fun q hq => ⟨hq.1,
      chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hq.2⟩
  have hlocal := (gradientNormSqOnE_continuousOn (I := I) hG hJreg α hρ).comp hψ hmaps
  refine (hlocal.congr ?_).mono ?_
  · intro q hq
    simp only [Function.comp_apply]
    change (G.metric q.1).inner q.2
        (gradFun (I := I) (G.metric q.1) ρ q.2)
        (gradFun (I := I) (G.metric q.1) ρ q.2) = _
    rw [grad_norm_sq_chart (I := I) (G.metric q.1) α (hρ.mdifferentiable (by simp) q.2)
      (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hq.2)]
    simp only [chartInvGramOnE_def]
    rw [(extChartAt I α).left_inv
      (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq.2)]
  · intro q hq
    exact ⟨hq.1.1, hq.2.2⟩

omit [CompleteSpace E] in
theorem leviCivitaLaplacian_continuousOn [I.Boundaryless] [T2Space M]
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        laplacian (I := I) (LeviCivita (I := I) (G.metric p.1))
          (G.metric p.1) ρ p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  classical
  refine continuousOn_of_locally_continuousOn ?_
  intro p hp
  let α := p.2
  let U : Set (Real × M) := Set.univ ×ˢ chartLeviCivitaGoodSet (I := I) α
  have hpU : p ∈ U := ⟨Set.mem_univ _, self_mem_chartLeviCivitaGoodSet (I := I) (α := α)⟩
  refine ⟨U, isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) α), hpU, ?_⟩
  let S : Set (Real × M) := J ×ˢ chartLeviCivitaGoodSet (I := I) α
  have hψ : ContinuousOn (fun q : Real × M => (q.1, extChartAt I α q.2)) S :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) α).comp continuous_snd.continuousOn
        fun q hq => chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq.2)
  have hmaps : MapsTo (fun q : Real × M => (q.1, extChartAt I α q.2)) S
      (J ×ˢ interior (extChartAt I α).target) :=
    fun q hq => ⟨hq.1,
      chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hq.2⟩
  have hlocal :=
    (leviCivitaLaplacianOnE_continuousOn (I := I) hG hJreg hJ α hρ).comp hψ hmaps
  refine (hlocal.congr ?_).mono ?_
  · intro q hq
    simp only [Function.comp_apply]
    rw [laplacian_eq_chart_hessian_trace (I := I) (G.metric q.1) α hρ
      (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hq.2)]
    simp only [chartHessianTensor_def, chartIteratedPartialDeriv_def,
      chartInvGramOnE_def]
    rw [(extChartAt I α).left_inv
      (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq.2)]
  · intro q hq
    exact ⟨hq.1.1, hq.2.2⟩

end MetricFamilySmoothOn

namespace MetricConnectionFamily

omit [CompleteSpace E] in
theorem gradientAt_continuousOn [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    {ρ : M → Real}
    (hρ : ContMDiff I (modelWithCornersSelf Real Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        (TotalSpace.mk' E p.2
          (gradientAt (I := I) G p.1 ρ p.2) : TangentBundle I M))
      (J ×ˢ (Set.univ : Set M)) := by
  simpa only [MetricConnectionFamily.restrict_metric, gradientAt_eq] using
    MetricFamilySmoothOn.gradient_continuousOn
      (I := I) (G := G.restrict D) hG hJreg hρ

omit [CompleteSpace E] in
theorem gradient_norm_sq_continuousOn [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) ρ p.2)
          (gradientFun (I := I) (G.metric p.1) ρ p.2))
      (J ×ˢ (Set.univ : Set M)) := by
  simpa only [MetricConnectionFamily.restrict_metric] using
    MetricFamilySmoothOn.gradient_norm_sq_continuousOn
      (I := I) (G := G.restrict D) hG hJreg hρ

omit [CompleteSpace E] in
theorem laplacianAt_continuousOn [I.Boundaryless] [T2Space M]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (hconn : ∀ t ∈ J,
      G.connection t = LeviCivita (I := I) (G.metric t))
    {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn (fun p : Real × M => laplacianAt (I := I) G p.1 ρ p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  have hlevi := MetricFamilySmoothOn.leviCivitaLaplacian_continuousOn
    (I := I) (G := G.restrict D) hG hJreg hJ hρ
  refine hlevi.congr ?_
  intro p hp
  simp only [MetricConnectionFamily.restrict_metric]
  rw [laplacianAt_eq, hconn p.1 hp.1]

omit [CompleteSpace E] in
theorem heatOperatorWithDrift_continuousOn [I.Boundaryless] [T2Space M]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (hconn : ∀ t ∈ J,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (X : Real → (x : M) → TangentSpace I x)
    {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ)
    (hdrift : ContinuousOn (fun p : Real × M =>
      driftTerm (I := I) G p.1 (X p.1) ρ p.2)
      (J ×ˢ (Set.univ : Set M))) :
    ContinuousOn (fun p : Real × M =>
      heatOperatorWithDrift (I := I) G p.1 (X p.1) ρ p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  simpa only [heatOperatorWithDrift] using
    (G.laplacianAt_continuousOn hG hJreg hJ hconn hρ).add hdrift

end MetricConnectionFamily

end DifferentialGeometry.Geometry.Curvature
