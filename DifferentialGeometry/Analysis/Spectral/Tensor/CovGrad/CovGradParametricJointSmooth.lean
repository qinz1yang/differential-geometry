import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricChartRepr
open DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
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

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covApply_chartRepr_euclid_jointContDiffWithinAt [SigmaCompactSpace M]
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    {t₀ : ℝ} {b : M} (ht₀ : t₀ ∈ S)
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F q.1).toSection z)) ((extChartAt I α).symm q.2))
      (S ×ˢ (extChartAt I α).target) (t₀, extChartAt I α b) := by
  classical
  set φ := extChartAt I α with hφ
  set chartRep : ℝ → E → TensorRSModel r s ℝ E :=
    fun t y => DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => (F t).toSection z) (φ.symm y) with hchartRep
  set U : Set E := φ '' chartLeviCivitaGoodSet (I := I) α with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : φ b ∈ U := ⟨b, hb_good, rfl⟩
  have hb_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
  have hyb_tgt : φ b ∈ φ.target :=
    φ.map_source (by rw [hφ, extChartAt_source]; exact hb_src)
  have hchartRep_w : ∀ y₀ : E, y₀ ∈ φ.target →
      ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => chartRep q.1 q.2) (S ×ˢ φ.target) (t₀, y₀) := by
    intro y₀ hy₀
    exact chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s F S α hF ht₀ hy₀
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := B.contMDiff.contMDiffOn
  have hvec_cd : ContDiffOn ℝ ∞
      (DifferentialGeometry.Geometry.Connection.chartE_section_repr (I := I) α B.toFun ∘ φ.symm)
        U :=
    chartE_pullback_contDiffOn_goodSet (I := I) α hB_on
  have hvec_at : ContDiffAt ℝ ∞
      (DifferentialGeometry.Geometry.Connection.chartE_section_repr (I := I) α B.toFun ∘ φ.symm)
      (φ b) :=
    (hvec_cd (φ b) hx_mem).contDiffAt (hU_open.mem_nhds hx_mem)
  have hvec_q : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => DifferentialGeometry.Geometry.Connection.chartE_section_repr
        (I := I) α B.toFun (φ.symm q.2)) (S ×ˢ φ.target) (t₀, φ b) :=
    (hvec_at.comp (t₀, φ b) contDiffAt_snd).contDiffWithinAt
  have h_intrinsic : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => fderiv ℝ (fun y' : E => chartRep q.1 y') q.2
        (DifferentialGeometry.Geometry.Connection.chartE_section_repr (I := I) α B.toFun
          (φ.symm q.2)))
      (S ×ˢ φ.target) (t₀, φ b) := by
    have huncurry : ContDiffWithinAt ℝ ∞
        (Function.uncurry (fun (q : ℝ × E) (y' : E) => chartRep q.1 y'))
        ((S ×ˢ φ.target) ×ˢ φ.target)
        ((t₀, φ b), (fun q : ℝ × E => q.2) (t₀, φ b)) := by
      have hbrick : ContDiffWithinAt ℝ ∞ (fun r : ℝ × E => chartRep r.1 r.2)
          (S ×ˢ φ.target) (t₀, φ b) := hchartRep_w (φ b) hyb_tgt
      have hproj : ContDiffWithinAt ℝ ∞
          (fun r : (ℝ × E) × E => (r.1.1, r.2))
          ((S ×ˢ φ.target) ×ˢ φ.target) ((t₀, φ b), φ b) :=
        (contDiffWithinAt_fst.fst).prodMk contDiffWithinAt_snd
      refine hbrick.comp ((t₀, φ b), φ b) hproj ?_
      rintro ⟨⟨t, y⟩, y'⟩ ⟨⟨ht, _⟩, hy'⟩
      exact ⟨ht, hy'⟩
    have hg : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => q.2) (S ×ˢ φ.target) (t₀, φ b) :=
      contDiffWithinAt_snd
    have htgt_open : IsOpen φ.target := isOpen_extChartAt_target (I := I) α
    have hud : UniqueDiffOn ℝ φ.target := htgt_open.uniqueDiffOn
    have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
    have hsub : (S ×ˢ φ.target) ⊆ (fun q : ℝ × E => q.2) ⁻¹' φ.target := by
      intro q hq; exact hq.2
    have hfdw := ContDiffWithinAt.fderivWithin huncurry hg hud h_le ⟨ht₀, hyb_tgt⟩ hsub
    have hfd_eq : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => fderiv ℝ (fun y' : E => chartRep q.1 y') q.2) (S ×ˢ φ.target)
          (t₀, φ b) := by
      refine hfdw.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with q hq
        exact (fderivWithin_of_isOpen htgt_open hq.2).symm
      · exact (fderivWithin_of_isOpen htgt_open hyb_tgt).symm
    exact hfd_eq.clm_apply hvec_q
  have hchartRep_q : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => chartRep q.1 q.2)
      (S ×ˢ φ.target) (t₀, φ b) := hchartRep_w (φ b) hyb_tgt
  have h_input : ∀ k : Fin r, ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          (φ.symm q.2)
          (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀
            α
            (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) k))
      (S ×ˢ φ.target) (t₀, φ b) := by
    intro k
    obtain ⟨Ker, hKer, hK_at⟩ :
        ∃ Ker : E → (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E),
          (Ker = fun y : E => DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel
            (I := I) g₀ r s α B.toFun k (φ.symm y)) ∧
          ContDiffAt ℝ ∞ Ker (φ b) :=
      ⟨_, rfl, inputSlotChartKernel_contDiffAt_chart_pulled (I := I) (M := M) g₀ r s α B k hb_good⟩
    have hK_q : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => Ker q.2) (S ×ˢ φ.target) (t₀, φ b) :=
      (ContDiffAt.comp (t₀, φ b) hK_at contDiffAt_snd).contDiffWithinAt
    have h_apply : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => Ker q.2 (chartRep q.1 q.2)) (S ×ˢ φ.target) (t₀, φ b) :=
      hK_q.clm_apply hchartRep_q
    refine h_apply.congr_of_eventuallyEq ?_ ?_
    · have hUprod : (Set.univ : Set ℝ) ×ˢ U ∈ nhds (t₀, φ b) :=
        (isOpen_univ.prod hU_open).mem_nhds ⟨Set.mem_univ _, hx_mem⟩
      refine Filter.eventually_of_mem (nhdsWithin_le_nhds hUprod) ?_
      rintro ⟨t, y⟩ hq
      have hy : y ∈ U := hq.2
      obtain ⟨x', hx'_good, hx'y⟩ := hy
      have hx'_src : x' ∈ (chartAt H α).source :=
        chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
      have hx'_extsrc : x' ∈ φ.source := by rw [hφ, extChartAt_source]; exact hx'_src
      have hx'_inv : φ.symm y = x' := by rw [← hx'y]; exact φ.left_inv hx'_extsrc
      change _ = Ker y (chartRep t y)
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSInputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
        (fun b' : M => (F t).toSection b') B.toFun
        (b := φ.symm y) (by rw [hx'_inv]; exact hx'_src) k)
    · have hgood_inv : φ.symm (φ b) = b := φ.left_inv (by rw [hφ, extChartAt_source]; exact hb_src)
      change _ = Ker (φ b) (chartRep t₀ (φ b))
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSInputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
        (fun b' : M => (F t₀).toSection b') B.toFun
        (b := φ.symm (φ b)) (by rw [hgood_inv]; exact hb_src) k)
  have h_output : ∀ l : Fin s, ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          (φ.symm q.2)
          (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r s
            g₀ α
            (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) l))
      (S ×ˢ φ.target) (t₀, φ b) := by
    intro l
    obtain ⟨Ker, hKer, hK_at⟩ :
        ∃ Ker : E → (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E),
          (Ker = fun y : E => DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel
            (I := I) g₀ r s α B.toFun l (φ.symm y)) ∧
          ContDiffAt ℝ ∞ Ker (φ b) :=
      ⟨_, rfl, outputSlotChartKernel_contDiffAt_chart_pulled (I := I) (M := M) g₀ r s α B l hb_good⟩
    have hK_q : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => Ker q.2) (S ×ˢ φ.target) (t₀, φ b) :=
      (ContDiffAt.comp (t₀, φ b) hK_at contDiffAt_snd).contDiffWithinAt
    have h_apply : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => Ker q.2 (chartRep q.1 q.2)) (S ×ˢ φ.target) (t₀, φ b) :=
      hK_q.clm_apply hchartRep_q
    refine h_apply.congr_of_eventuallyEq ?_ ?_
    · have hUprod : (Set.univ : Set ℝ) ×ˢ U ∈ nhds (t₀, φ b) :=
        (isOpen_univ.prod hU_open).mem_nhds ⟨Set.mem_univ _, hx_mem⟩
      refine Filter.eventually_of_mem (nhdsWithin_le_nhds hUprod) ?_
      rintro ⟨t, y⟩ hq
      have hy : y ∈ U := hq.2
      obtain ⟨x', hx'_good, hx'y⟩ := hy
      have hx'_src : x' ∈ (chartAt H α).source :=
        chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
      have hx'_extsrc : x' ∈ φ.source := by rw [hφ, extChartAt_source]; exact hx'_src
      have hx'_inv : φ.symm y = x' := by rw [← hx'y]; exact φ.left_inv hx'_extsrc
      change _ = Ker y (chartRep t y)
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
        (fun b' : M => (F t).toSection b') B.toFun
        (b := φ.symm y) (by rw [hx'_inv]; exact hx'_src) l)
    · have hgood_inv : φ.symm (φ b) = b := φ.left_inv (by rw [hφ, extChartAt_source]; exact hb_src)
      change _ = Ker (φ b) (chartRep t₀ (φ b))
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
        (fun b' : M => (F t₀).toSection b') B.toFun
        (b := φ.symm (φ b)) (by rw [hgood_inv]; exact hb_src) l)
  have h_sum : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        fderiv ℝ (fun y' : E => chartRep q.1 y') q.2
          (DifferentialGeometry.Geometry.Connection.chartE_section_repr (I := I) α B.toFun
            (φ.symm q.2))
        + (∑ k : Fin r,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
              (φ.symm q.2)
              (DifferentialGeometry.Geometry.Connection.chartTensorRSInputSlotCorrection (I := I) r
                s g₀ α
                (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) k))
        - (∑ l : Fin s,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
              (φ.symm q.2)
              (DifferentialGeometry.Geometry.Connection.chartTensorRSOutputSlotCorrection (I := I) r
                s g₀ α
                (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) l)))
      (S ×ˢ φ.target) (t₀, φ b) := by
    refine (h_intrinsic.add (ContDiffWithinAt.sum (fun k _ => h_input k))).sub
      (ContDiffWithinAt.sum (fun l _ => h_output l))
  refine h_sum.congr_of_eventuallyEq ?_ ?_
  · have hUprod : (Set.univ : Set ℝ) ×ˢ U ∈ nhds (t₀, φ b) :=
      (isOpen_univ.prod hU_open).mem_nhds ⟨Set.mem_univ _, hx_mem⟩
    refine Filter.eventually_of_mem (nhdsWithin_le_nhds hUprod) ?_
    rintro ⟨t, y⟩ hq
    have hy : y ∈ U := hq.2
    obtain ⟨x', hx'_good, hx'y⟩ := hy
    have hx'_extsrc : x' ∈ φ.source := by
      rw [hφ, extChartAt_source]; exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
    have hy_tgt : y ∈ φ.target := hx'y ▸ φ.map_source hx'_extsrc
    have hy_good : φ.symm y ∈ chartLeviCivitaGoodSet (I := I) α := by
      rw [← hx'y, φ.left_inv hx'_extsrc]; exact hx'_good
    have hform := chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M)
      g₀ r s α (F t) B hy_tgt hy_good
    change DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (F t).toSection z)) (φ.symm y) = _
    rw [hchartRep]
    simp only [Function.comp_apply] at hform
    exact hform
  · have hgood_inv : φ.symm (φ b) = b := φ.left_inv (by rw [hφ, extChartAt_source]; exact hb_src)
    have hform := chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M)
      g₀ r s α (F t₀) B hyb_tgt (by rw [hgood_inv]; exact hb_good)
    change DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (F t₀).toSection z)) (φ.symm (φ b)) = _
    rw [hchartRep]
    simp only [Function.comp_apply] at hform
    exact hform

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covApply_chartRepr_manifold_jointContMDiffOn [SigmaCompactSpace M]
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F p.2).toSection z)) p.1)
      ((chartAt H α).source ×ˢ S) := by
  classical
  set φ := extChartAt I α with hφ
  intro p hp
  obtain ⟨hpx, hps⟩ := hp
  have hpx_good : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source]; exact hpx
  have hEu := covApply_chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s F S α B hF hps
    hpx_good
  have hmove : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
      (fun q : M × ℝ => (q.2, φ q.1))
      ((chartAt H α).source ×ˢ S) p := by
    have hmoveOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
        (fun q : M × ℝ => (q.2, φ q.1))
        ((chartAt H α).source ×ˢ S) := by
      refine ContMDiffOn.prodMk contMDiffOn_snd ?_
      exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun q hq => hq.1)
    have hm := hmoveOn p ⟨hpx, hps⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  have hEuM : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun q : ℝ × E =>
        DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F q.1).toSection z)) (φ.symm q.2))
      (S ×ˢ φ.target) (p.2, φ p.1) := by
    rw [contMDiffWithinAt_iff_contDiffWithinAt]
    exact hEu
  have hmaps : Set.MapsTo (fun q : M × ℝ => (q.2, φ q.1))
      ((chartAt H α).source ×ˢ S) (S ×ˢ φ.target) := by
    intro q hq
    obtain ⟨hqx, hqs⟩ := hq
    refine ⟨hqs, ?_⟩
    exact φ.map_source (by rw [hφ, extChartAt_source]; exact hqx)
  have hcomp := hEuM.comp p hmove hmaps
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    obtain ⟨hqx, _⟩ := hq
    have hqsrc : q.1 ∈ φ.source := by rw [hφ, extChartAt_source]; exact hqx
    simp only [Function.comp_apply]
    rw [φ.left_inv hqsrc]
  · simp only [Function.comp_apply]
    have hpsrc : p.1 ∈ φ.source := by rw [hφ, extChartAt_source]; exact hpx
    rw [φ.left_inv hpsrc]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covApply_section_jointContMDiffOn [SigmaCompactSpace M]
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (F p.2).toSection z) p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  classical
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  set α : M := x₀ with hα
  have hsub_eq : ((Set.univ : Set M) ×ˢ S) ∩ ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ S := by
    ext ⟨y, u⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  rw [hsub_eq]
  have hCR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F p.2).toSection z)) p.1)
      ((chartAt H α).source ×ˢ S) :=
    covApply_chartRepr_manifold_jointContMDiffOn (I := I) g₀ r s F S α B hF
  intro p₀ hp₀
  obtain ⟨hx₀src, hs₀'⟩ := hp₀
  have hbaseSet : p₀.1 ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change p₀.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) α).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        rw [hα]; exact hx₀src
  have hsource : (⟨p₀.1,
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
        B.toFun (fun z : M => (F p₀.2).toSection z) p₀.1⟩ :
      TotalSpace (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z)) ∈
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).source := by
    rw [Bundle.Trivialization.mem_source]; exact hbaseSet
  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ =>
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α)
          ⟨p.1,
            covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
              B.toFun (fun z : M => (F p.2).toSection z) p.1⟩).2)
      ((chartAt H α).source ×ˢ S) p₀ := by
    refine (hCR p₀ ⟨hx₀src, hs₀'⟩).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with p hp
      obtain ⟨hpx, _⟩ := hp
      have hpbase : p.1 ∈ (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet := by
        change p.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) α).baseSet) ∩
            ((trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) α).baseSet)
        refine ⟨?_, ?_⟩ <;>
          · change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
            rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
              TangentBundle.trivializationAt_baseSet (I := I) α]
            exact hpx
      rw [DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hpbase]
    · rw [DifferentialGeometry.Geometry.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hbaseSet]
  refine ((Bundle.Trivialization.contMDiffWithinAt_iff
    (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
    (f := fun p : M × ℝ => (⟨p.1,
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
        B.toFun (fun z : M => (F p.2).toSection z) p.1⟩ :
      TotalSpace (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z)))
    (s := (chartAt H α).source ×ˢ S) (x₀ := p₀)
    (e := trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α) hsource).mpr
    ⟨contMDiffWithinAt_fst, hfib⟩)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_step_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + 1) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + 1) I z) q.1
        ((covGrad (I := I) (M := M) g₀ r sIdx (Ψ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) := by
  classical
  set φfield : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TensorRSSpace r sIdx I p.1 :=
    fun p => tensorRSCovariantDerivative I M r sIdx (LeviCivita (I := I) g₀)
      (fun y : M => (Ψ p.2).toSection y) p.1 with hφfield
  have hCLM : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r sIdx ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] TensorRSModel r sIdx ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TensorRSSpace r sIdx I x) p.1 (φfield p))
      ((Set.univ : Set M) ×ˢ S) := by
    refine contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := TensorRSModel r sIdx ℝ E) (V₂ := fun x : M => TensorRSSpace r sIdx I x)
      (φ := φfield) (S := S) ?_
    intro Y
    have hYapply := covApply_section_jointContMDiffOn (I := I) g₀ r sIdx Ψ S Y hjoint
    refine hYapply.congr ?_
    rintro ⟨x, t⟩ -
    rfl
  have hcomp := (covGradBundleSmoothEquiv (I := I) (M := M) r
    sIdx).toDiffeomorph.contMDiff.comp_contMDiffOn
    hCLM
  refine hcomp.congr ?_
  rintro ⟨x, t⟩ -
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r sIdx x (φfield (x, t))]
  rw [covGrad_toSection_apply]


end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
