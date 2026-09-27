import DifferentialGeometry.Geometry.Comparison.Soul.InducedSliceMetric
import DifferentialGeometry.Geometry.Comparison.Soul.SoulSubmanifold
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PrescribedTangentInOpenSet
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.ChainRule
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CorrectionContraction
import DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Torsion
import Mathlib.Analysis.LocallyConvex.SeparatingDual

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {S : Set M} {d : ℕ}

def embeddedSliceTangentProjection (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    TangentSpace I p.1 →L[ℝ] TangentSpace 𝓘(ℝ, Fin d → ℝ) p := by
  let _ := embeddedSliceChartedSpace hS
  exact (ContinuousLinearMap.fst ℝ _ _).comp
    (normalSplitting g hS p).symm.toContinuousLinearMap

private theorem tangentProjection_decomposition (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) (p : S) (w : TangentSpace I p.1) :
    let _ := embeddedSliceChartedSpace hS
    mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p
        (embeddedSliceTangentProjection g hS p w) +
      ((normalSplitting g hS p).symm w).2.1 = w := by
  let _ := embeddedSliceChartedSpace hS
  have h := (normalSplitting g hS p).apply_symm_apply w
  rw [normalSplitting_apply] at h
  exact h

@[simp] theorem embeddedSliceTangentProjection_inclusion
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    ∀ v : TangentSpace 𝓘(ℝ, Fin d → ℝ) p,
      embeddedSliceTangentProjection g hS p
        (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v) = v := by
  let _ := embeddedSliceChartedSpace hS
  dsimp only
  intro v
  have he : normalSplitting g hS p (v, 0) =
      mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v := by
    rw [normalSplitting_apply]
    exact add_zero _
  change ((normalSplitting g hS p).symm
    (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v)).1 = v
  rw [← he, (normalSplitting g hS p).symm_apply_apply]

theorem embeddedSliceTangentProjection_inner
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I d S) (p : S)
    (w : TangentSpace I p.1) :
    let _ := embeddedSliceChartedSpace hS
    ∀ v : TangentSpace 𝓘(ℝ, Fin d → ℝ) p,
      g.inner p.1
        (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p
          (embeddedSliceTangentProjection g hS p w))
        (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v) =
      g.inner p.1 w
        (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v) := by
  let _ := embeddedSliceChartedSpace hS
  dsimp only
  intro v
  have hv : mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v ∈
      sliceTangent I S p.1 := by
    rw [← embeddedSlice_inclusion_range_mfderiv hS p]
    exact ⟨v, rfl⟩
  have hn := (mem_normalSpace_iff g S p.1 _).mp
    ((normalSplitting g hS p).symm w).2.2 _ hv
  have hsum := tangentProjection_decomposition g hS p w
  conv_rhs => rw [← hsum]
  simp only [map_add, add_apply, hn, add_zero]

private theorem inclusion_tangentProjection_of_normal_pairing_zero
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I d S) (p : S)
    (w : TangentSpace I p.1)
    (hw : ∀ n : TangentSpace I p.1, n ∈ normalSpace (I := I) g S p.1 →
      g.inner p.1 w n = 0) :
    let _ := embeddedSliceChartedSpace hS
    mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p
      (embeddedSliceTangentProjection g hS p w) = w := by
  let _ := embeddedSliceChartedSpace hS
  let n := ((normalSplitting g hS p).symm w).2
  have ht : mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p
      (embeddedSliceTangentProjection g hS p w) ∈ sliceTangent I S p.1 := by
    rw [← embeddedSlice_inclusion_range_mfderiv hS p]
    exact ⟨_, rfl⟩
  have horth : g.inner p.1
      (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p
        (embeddedSliceTangentProjection g hS p w)) n.1 = 0 := by
    rw [g.symm]
    exact (mem_normalSpace_iff g S p.1 n.1).mp n.2 _ ht
  have hsum := tangentProjection_decomposition g hS p w
  have hself : g.inner p.1 n.1 n.1 = 0 := by
    have h := hw n.1 n.2
    rw [← hsum, map_add, add_apply, horth, zero_add] at h
    exact h
  have hn : n.1 = 0 := by
    by_contra hne
    exact (ne_of_gt (g.pos p.1 n.1 hne)) hself
  change _ + n.1 = w at hsum
  simpa only [hn, add_zero] using hsum

def projectedSliceCovDerivAlong (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    ∀ (γ : ℝ → S), (∀ s : ℝ, TangentSpace 𝓘(ℝ, Fin d → ℝ) (γ s)) →
      ∀ t : ℝ, TangentSpace 𝓘(ℝ, Fin d → ℝ) (γ t) := by
  let _ := embeddedSliceChartedSpace hS
  exact fun γ V t => embeddedSliceTangentProjection g hS (γ t)
    (covDerivAlong (I := I) g (fun s => (γ s).1)
      (fun s => mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) (γ s) (V s)) t)

theorem projectedSliceCovDerivAlong_commute
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ f : ℝ → ℝ → S,
      ContMDiff (ModelWithCorners.prod 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ))
        𝓘(ℝ, Fin d → ℝ) ∞ (fun q : ℝ × ℝ => f q.1 q.2) →
      ∀ t : ℝ,
        projectedSliceCovDerivAlong g hS (fun s => f s t)
            (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) (fun u => f s u) t 1) 0 =
          projectedSliceCovDerivAlong g hS (fun v => f 0 v)
            (fun v => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) (fun u => f u v) 0 1) t := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro f hf t
  have hi := embeddedSlice_inclusion_contMDiff hS
  have hfirst (s : ℝ) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) ∞
      (fun u => f s u) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hsecond (v : ℝ) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) ∞
      (fun u => f u v) :=
    hf.comp (contMDiff_id.prodMk contMDiff_const)
  have hfM : IsSmoothVariation (I := I) (fun s u => (f s u).1) :=
    (hi.comp hf).of_le
      (WithTop.coe_le_coe.mpr (le_top : (8 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hcomm := commute_ds_dt_intrinsic (I := I) g (fun s u => (f s u).1) hfM t
  have hleft :
      (fun s => mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) (f s t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) (fun u => f s u) t 1)) =
      fun s => mfderiv 𝓘(ℝ, ℝ) I (fun u => (f s u).1) t 1 := by
    funext s
    exact (mfderiv_comp_apply (x := t)
      (hi.mdifferentiableAt (by simp))
      ((hfirst s).mdifferentiableAt (by simp)) 1).symm
  have hright :
      (fun v => mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) (f 0 v)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) (fun u => f u v) 0 1)) =
      fun v => mfderiv 𝓘(ℝ, ℝ) I (fun u => (f u v).1) 0 1 := by
    funext v
    exact (mfderiv_comp_apply (x := 0)
      (hi.mdifferentiableAt (by simp))
      ((hsecond v).mdifferentiableAt (by simp)) 1).symm
  change embeddedSliceTangentProjection g hS (f 0 t)
      (covDerivAlong (I := I) g (fun s => (f s t).1) _ 0) =
    embeddedSliceTangentProjection g hS (f 0 t)
      (covDerivAlong (I := I) g (fun v => (f 0 v).1) _ t)
  rw [hleft, hright]
  exact congrArg (fun w : E => embeddedSliceTangentProjection g hS (f 0 t) w) hcomm

omit [FiniteDimensional ℝ E] in
private theorem chartRepAt_differentiable_of_mdifferentiableAt
    (γ : ℝ → M) (V : ∀ s : ℝ, TangentSpace I (γ s)) (t : ℝ)
    (hV : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun s => (⟨γ s, V s⟩ : TangentBundle I M)) t) :
    DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
  have hsplit := hV
  rw [mdifferentiableAt_totalSpace] at hsplit
  have hnbd : ∀ᶠ s in 𝓝 t,
      γ s ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    hsplit.1.continuousAt.preimage_mem_nhds
      ((Trivialization.open_baseSet _).mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  have heq : chartRepAt (I := I) γ V t =ᶠ[𝓝 t]
      (fun s : ℝ => (trivializationAt E (TangentSpace I) (γ t)
        (⟨γ s, V s⟩ : TangentBundle I M)).2) := by
    filter_upwards [hnbd] with s hs
    change (trivializationAt E (TangentSpace I) (γ t)).linearMapAt ℝ (γ s) (V s) = _
    rw [Trivialization.coe_linearMapAt_of_mem _ hs]
  exact (mdifferentiableAt_iff_differentiableAt.mp hsplit.2).congr_of_eventuallyEq heq

omit [FiniteDimensional ℝ E] in
private theorem chartRepAt_differentiable_of_contMDiffAt
    (γ : ℝ → M) (V : ∀ s : ℝ, TangentSpace I (γ s)) (t : ℝ)
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (⟨γ s, V s⟩ : TangentBundle I M)) t) :
    DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t :=
  chartRepAt_differentiable_of_mdifferentiableAt γ V t (hV.mdifferentiableAt one_ne_zero)

private def inclusionFieldRep (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    (∀ q : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) q) → S → E := by
  let _ := embeddedSliceChartedSpace hS
  exact fun Y q => trivToE (I := I) p.1 q.1
    (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) q (Y q))

private theorem inclusionFieldRep_mdifferentiableAt
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ Y : ∀ q : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) q,
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ)
        (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun q => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) p →
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) (inclusionFieldRep hS p Y) p := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro Y hY
  have hi := embeddedSlice_inclusion_contMDiff hS
  have htangent := hi.contMDiff_tangentMap (m := 1)
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hmap : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) I.tangent
      (fun q : S => (⟨q.1,
        mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) q (Y q)⟩ : TangentBundle I M)) p :=
    (htangent.mdifferentiableAt one_ne_zero).comp p hY
  rw [mdifferentiableAt_totalSpace] at hmap
  refine hmap.2.congr_of_eventuallyEq ?_
  have hnbd : ∀ᶠ q : S in 𝓝 p,
      q.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((Trivialization.open_baseSet _).mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) p.1))
  filter_upwards [hnbd] with q hq
  change (trivializationAt E (TangentSpace I) p.1).linearMapAt ℝ q.1 _ = _
  rw [Trivialization.coe_linearMapAt_of_mem _ hq]

def projectedSliceCovariantDerivative (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    (∀ q : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) q) →
      ∀ p : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) p →L[ℝ]
        TangentSpace 𝓘(ℝ, Fin d → ℝ) p := by
  let _ := embeddedSliceChartedSpace hS
  exact fun Y p => by
    let D : TangentSpace 𝓘(ℝ, Fin d → ℝ) p →L[ℝ] E :=
      mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) (inclusionFieldRep hS p Y) p
    exact (embeddedSliceTangentProjection g hS p).comp
      ((trivFromE (I := I) p.1 p.1).comp
        (D +
        (christoffelCorrection (I := I) g p.1 p.1 (inclusionFieldRep hS p Y p)).comp
          (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p)))

private theorem inclusionFieldRep_commutator
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ X Y : ∀ q : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) q,
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ)
        (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun q => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) p →
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ)
        (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun q => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) p →
      let A : E := mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) (inclusionFieldRep hS p Y) p (X p)
      let B : E := mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) (inclusionFieldRep hS p X) p (Y p)
      A - B =
        inclusionFieldRep hS p (VectorField.mlieBracket 𝓘(ℝ, Fin d → ℝ) X Y) p := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro X Y hX hY
  let F : S → E := (extChartAt I p.1) ∘ (Subtype.val : S → M)
  have hi := embeddedSlice_inclusion_contMDiff hS
  have hp : p.1 ∈ (chartAt H p.1).source := mem_chart_source H p.1
  have hF (q : S) (hq : q.1 ∈ (chartAt H p.1).source) :
      ContMDiffAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) 2 F q := by
    have hchart : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I p.1) q.1 :=
      contMDiffAt_extChartAt' hq
    exact hchart.comp q ((hi.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))).contMDiffAt)
  have hrep (W : ∀ q : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) q)
      (q : S) (hq : q.1 ∈ (chartAt H p.1).source) :
      mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) F q (W q) =
        inclusionFieldRep hS p W q := by
    change mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E)
      ((extChartAt I p.1) ∘ (Subtype.val : S → M)) q (W q) = _
    rw [mfderiv_comp_apply (x := q)
      (mdifferentiableAt_extChartAt (I := I) hq)
      (hi.mdifferentiableAt (by simp))]
    exact congrArg
      (fun L : TangentSpace I q.1 →L[ℝ] E =>
        L (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) q (W q)))
      (TangentBundle.continuousLinearMapAt_trivializationAt
        (𝕜 := ℝ) (I := I) (x₀ := p.1) (x := q.1) hq).symm
  have hclm (ℓ : E →L[ℝ] ℝ) (R : S → E) (q : S)
      (hR : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) R q)
      (v : TangentSpace 𝓘(ℝ, Fin d → ℝ) q) :
      mvfderiv (I := 𝓘(ℝ, Fin d → ℝ)) (ℓ ∘ R) q v =
        ℓ (mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) R q v) := by
    change mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) (ℓ ∘ R) q v = _
    rw [mfderiv_comp_apply (x := q) ℓ.mdifferentiableAt hR, ℓ.mfderiv_eq]
    rfl
  have hnbd : ∀ᶠ q : S in 𝓝 p, q.1 ∈ (chartAt H p.1).source :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((chartAt H p.1).open_source.mem_nhds hp)
  have hpint : extChartAt 𝓘(ℝ, Fin d → ℝ) p p ∈
      interior ((extChartAt 𝓘(ℝ, Fin d → ℝ) p).target : Set (Fin d → ℝ)) := by
    rw [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin d → ℝ)) p).interior_eq]
    exact mem_extChartAt_target p
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
  intro ℓ
  have hscalar : ContMDiffAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) 2 (ℓ ∘ F) p :=
    ℓ.contMDiffAt.comp p (hF p hp)
  have hscalarAlong (W : ∀ q : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) q)
      (hW : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ)
        (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun q => (⟨q, W q⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) p)
      (v : TangentSpace 𝓘(ℝ, Fin d → ℝ) p) :
      mvfderiv (I := 𝓘(ℝ, Fin d → ℝ))
          (fun q => mvfderiv (I := 𝓘(ℝ, Fin d → ℝ)) (ℓ ∘ F) q (W q)) p v =
        ℓ (mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) (inclusionFieldRep hS p W) p v) := by
    have heq :
        (fun q => mvfderiv (I := 𝓘(ℝ, Fin d → ℝ)) (ℓ ∘ F) q (W q)) =ᶠ[𝓝 p]
          ℓ ∘ inclusionFieldRep hS p W := by
      filter_upwards [hnbd] with q hq
      rw [hclm ℓ F q ((hF q hq).mdifferentiableAt (by simp)) (W q), hrep W q hq]
      rfl
    have hderiv :
        mvfderiv (I := 𝓘(ℝ, Fin d → ℝ))
            (fun q => mvfderiv (I := 𝓘(ℝ, Fin d → ℝ)) (ℓ ∘ F) q (W q)) p =
          mvfderiv (I := 𝓘(ℝ, Fin d → ℝ)) (ℓ ∘ inclusionFieldRep hS p W) p := by
      change mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ)
          (fun q => mvfderiv (I := 𝓘(ℝ, Fin d → ℝ)) (ℓ ∘ F) q (W q)) p =
        mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) (ℓ ∘ inclusionFieldRep hS p W) p
      exact heq.mfderiv_eq
    rw [hderiv]
    exact hclm ℓ (inclusionFieldRep hS p W) p
      (inclusionFieldRep_mdifferentiableAt hS p W hW) v
  have hbr := DifferentialGeometry.Geometry.Connection.mvfderiv_apply_mlieBracket
    (I := 𝓘(ℝ, Fin d → ℝ)) hX hY hscalar hpint
  rw [hclm ℓ F p ((hF p hp).mdifferentiableAt (by simp)),
    hrep (VectorField.mlieBracket 𝓘(ℝ, Fin d → ℝ) X Y) p hp,
    hscalarAlong Y hY (X p), hscalarAlong X hX (Y p)] at hbr
  exact (map_sub ℓ _ _).trans hbr.symm

theorem projectedSliceCovariantDerivative_torsion
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ (X Y : ∀ q : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) q) (p : S),
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ)
        (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun q => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) p →
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ)
        (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun q => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) p →
      projectedSliceCovariantDerivative g hS Y p (X p) -
          projectedSliceCovariantDerivative g hS X p (Y p) =
        VectorField.mlieBracket 𝓘(ℝ, Fin d → ℝ) X Y p := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro X Y p hX hY
  let di := mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p
  let A : E := mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) (inclusionFieldRep hS p Y) p (X p)
  let B : E := mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) (inclusionFieldRep hS p X) p (Y p)
  have hcancel :
      christoffelCorrection (I := I) g p.1 p.1 (inclusionFieldRep hS p Y p) (di (X p)) =
        christoffelCorrection (I := I) g p.1 p.1 (inclusionFieldRep hS p X p) (di (Y p)) :=
    christoffelCorrection_symm_cancel (I := I) g p.1 p.1 (di (X p)) (di (Y p))
  change embeddedSliceTangentProjection g hS p
      (trivFromE (I := I) p.1 p.1
        (A + christoffelCorrection (I := I) g p.1 p.1
          (inclusionFieldRep hS p Y p) (di (X p)))) -
    embeddedSliceTangentProjection g hS p
      (trivFromE (I := I) p.1 p.1
        (B + christoffelCorrection (I := I) g p.1 p.1
          (inclusionFieldRep hS p X p) (di (Y p)))) = _
  rw [← map_sub, ← map_sub, hcancel, add_sub_add_right_eq_sub]
  have hbr : A - B =
      inclusionFieldRep hS p (VectorField.mlieBracket 𝓘(ℝ, Fin d → ℝ) X Y) p :=
    inclusionFieldRep_commutator hS p X Y hX hY
  rw [hbr]
  change embeddedSliceTangentProjection g hS p
    (trivFromE (I := I) p.1 p.1 (trivToE (I := I) p.1 p.1
      (di (VectorField.mlieBracket 𝓘(ℝ, Fin d → ℝ) X Y p)))) = _
  rw [trivFromE_trivToE (I := I) p.1
    (mem_baseSet_trivializationAt E (TangentSpace I) p.1)]
  exact embeddedSliceTangentProjection_inclusion g hS p _

theorem projectedSliceCovDerivAlong_restrict
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ (γ : ℝ → S) (Y : ∀ q : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) q) (t : ℝ),
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) 1 γ t →
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ)
        (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun q => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) (γ t) →
      projectedSliceCovDerivAlong g hS γ (fun s => Y (γ s)) t =
        projectedSliceCovariantDerivative g hS Y (γ t)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) γ t (1 : ℝ)) := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro γ Y t hγ hY
  let p := γ t
  let δ : ℝ → M := fun s => (γ s).1
  let YM : ∀ s : ℝ, TangentSpace I (δ s) :=
    fun s => mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) (γ s) (Y (γ s))
  let v := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) γ t (1 : ℝ)
  let R := inclusionFieldRep hS p Y
  let DR : TangentSpace 𝓘(ℝ, Fin d → ℝ) p →L[ℝ] E :=
    mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) R p
  have hi := embeddedSlice_inclusion_contMDiff hS
  have hγd := hγ.mdifferentiableAt one_ne_zero
  have hδd : MDifferentiableAt 𝓘(ℝ, ℝ) I δ t :=
    (hi.mdifferentiableAt (by simp)).comp t hγd
  have hRd : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) R p :=
    inclusionFieldRep_mdifferentiableAt hS p Y hY
  have hRder : deriv (R ∘ γ) t = DR v := by
    have hchain := mfderiv_comp_apply (x := t) hRd hγd (1 : ℝ)
    rw [mfderiv_eq_fderiv] at hchain
    exact fderiv_apply_one_eq_deriv.symm.trans hchain
  have hvel : mfderiv 𝓘(ℝ, ℝ) I δ t 1 =
      mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v :=
    mfderiv_comp_apply (x := t) (hi.mdifferentiableAt (by simp)) hγd 1
  have hvelcoord : trivToE (I := I) p.1 p.1
      (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v) =
      deriv (AlongCurve.chartCurve (I := I) p.1 δ) t := by
    rw [← hvel]
    calc
      trivToE (I := I) p.1 p.1 (mfderiv 𝓘(ℝ, ℝ) I δ t 1) =
          fderiv ℝ ((extChartAt I p.1) ∘ δ) t 1 :=
        MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
          hδd p.1 (mem_chart_source H p.1)
      _ = deriv (AlongCurve.chartCurve (I := I) p.1 δ) t :=
        fderiv_apply_one_eq_deriv
  have hcorr : christoffelCorrection (I := I) g p.1 p.1 (R p)
      (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v) =
      Geodesic.chartChristoffelContraction (I := I) g p.1
        (deriv (AlongCurve.chartCurve (I := I) p.1 δ) t) (R p)
        (AlongCurve.chartCurve (I := I) p.1 δ t) := by
    rw [correction_eq_contr, hvelcoord]
    rfl
  have hcov : covDerivAlong (I := I) g δ YM t =
      trivFromE (I := I) p.1 p.1
        (DR v +
          christoffelCorrection (I := I) g p.1 p.1 (R p)
            (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v)) := by
    rw [covDerivAlong_def, AlongCurve.chartCovDerivAlong_def]
    change trivFromE (I := I) p.1 p.1
        (deriv (R ∘ γ) t +
          Geodesic.chartChristoffelContraction (I := I) g p.1
            (deriv (AlongCurve.chartCurve (I := I) p.1 δ) t) (R p)
            (AlongCurve.chartCurve (I := I) p.1 δ t)) = _
    rw [hRder, hcorr]
  change embeddedSliceTangentProjection g hS p (covDerivAlong (I := I) g δ YM t) =
    embeddedSliceTangentProjection g hS p
      (trivFromE (I := I) p.1 p.1
        (DR v +
          christoffelCorrection (I := I) g p.1 p.1 (R p)
            (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v)))
  rw [hcov]

section InducedMetric

variable [T2Space M]

theorem projectedSliceCovDerivAlong_metric_compat_of_mdifferentiableAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ (γ : ℝ → S) (V W : ∀ s : ℝ, TangentSpace 𝓘(ℝ, Fin d → ℝ) (γ s)) (t : ℝ),
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) 1 γ t →
      MDifferentiableAt 𝓘(ℝ, ℝ) (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun s => (⟨γ s, V s⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) t →
      MDifferentiableAt 𝓘(ℝ, ℝ) (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun s => (⟨γ s, W s⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) t →
      HasDerivAt (fun s => (inducedSliceMetric g hS).inner (γ s) (V s) (W s))
        ((inducedSliceMetric g hS).inner (γ t)
            (projectedSliceCovDerivAlong g hS γ V t) (W t) +
          (inducedSliceMetric g hS).inner (γ t) (V t)
            (projectedSliceCovDerivAlong g hS γ W t)) t := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro γ V W t hγ hV hW
  let γM : ℝ → M := fun s => (γ s).1
  let VM : ∀ s : ℝ, TangentSpace I (γM s) :=
    fun s => mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) (γ s) (V s)
  let WM : ∀ s : ℝ, TangentSpace I (γM s) :=
    fun s => mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) (γ s) (W s)
  have hi := embeddedSlice_inclusion_contMDiff hS
  have hγM : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γM t :=
    (hi.of_le (by simp)).contMDiffAt.comp t hγ
  have htangent := hi.contMDiff_tangentMap (m := 1)
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hVM : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun s => (⟨γM s, VM s⟩ : TangentBundle I M)) t :=
    (htangent.mdifferentiableAt one_ne_zero).comp t hV
  have hWM : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun s => (⟨γM s, WM s⟩ : TangentBundle I M)) t :=
    (htangent.mdifferentiableAt one_ne_zero).comp t hW
  have h := inner_deriv_at (I := I) (n := 1) le_rfl g γM VM WM t hγM
    (chartRepAt_differentiable_of_mdifferentiableAt γM VM t hVM)
    (chartRepAt_differentiable_of_mdifferentiableAt γM WM t hWM)
  have hfun : (fun s => (inducedSliceMetric g hS).inner (γ s) (V s) (W s)) =
      fun s => g.inner (γM s) (VM s) (WM s) := by
    funext s
    exact inducedSliceMetric_inner g hS (γ s) (V s) (W s)
  have hleft : (inducedSliceMetric g hS).inner (γ t)
      (projectedSliceCovDerivAlong g hS γ V t) (W t) =
      g.inner (γM t) (covDerivAlong (I := I) g γM VM t) (WM t) := by
    rw [inducedSliceMetric_inner]
    exact embeddedSliceTangentProjection_inner g hS (γ t)
      (covDerivAlong (I := I) g γM VM t) (W t)
  have hright : (inducedSliceMetric g hS).inner (γ t) (V t)
      (projectedSliceCovDerivAlong g hS γ W t) =
      g.inner (γM t) (VM t) (covDerivAlong (I := I) g γM WM t) := by
    rw [(inducedSliceMetric g hS).symm, inducedSliceMetric_inner]
    exact (embeddedSliceTangentProjection_inner g hS (γ t)
      (covDerivAlong (I := I) g γM WM t) (V t)).trans (g.symm (γM t) _ _)
  rw [hfun, hleft, hright]
  exact h

theorem projectedSliceCovDerivAlong_metric_compat [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ (γ : ℝ → S) (V W : ∀ s : ℝ, TangentSpace 𝓘(ℝ, Fin d → ℝ) (γ s)) (t : ℝ),
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) 1 γ t →
      ContMDiffAt 𝓘(ℝ, ℝ) (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ)) 1
        (fun s => (⟨γ s, V s⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) t →
      ContMDiffAt 𝓘(ℝ, ℝ) (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ)) 1
        (fun s => (⟨γ s, W s⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) t →
      HasDerivAt (fun s => (inducedSliceMetric g hS).inner (γ s) (V s) (W s))
        ((inducedSliceMetric g hS).inner (γ t)
            (projectedSliceCovDerivAlong g hS γ V t) (W t) +
          (inducedSliceMetric g hS).inner (γ t) (V t)
            (projectedSliceCovDerivAlong g hS γ W t)) t := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro γ V W t hγ hV hW
  exact projectedSliceCovDerivAlong_metric_compat_of_mdifferentiableAt g hS γ V W t hγ
    (hV.mdifferentiableAt one_ne_zero) (hW.mdifferentiableAt one_ne_zero)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem slice_metric_inner_mdifferentiableAt
    (g : SmoothRiemannianMetric I M)
    {Y Z : ∀ p : M, TangentSpace I p} {p : M}
    (hY : MDifferentiableAt I I.tangent
      (fun q => (⟨q, Y q⟩ : TangentBundle I M)) p)
    (hZ : MDifferentiableAt I I.tangent
      (fun q => (⟨q, Z q⟩ : TangentBundle I M)) p) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun q => g.inner q (Y q) (Z q)) p := by
  have hg : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
      (fun q : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun q : M => TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ)
        q (g.inner q)) p :=
    g.contMDiff.mdifferentiableAt (by simp)
  have htotal : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun q : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) q
        (g.inner q (Y q) (Z q))) p :=
    MDifferentiableAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hg hY hZ
  rw [mdifferentiableAt_totalSpace] at htotal
  exact htotal.2

theorem projectedSliceCovariantDerivative_isMetricCompatibleOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    IsMetricCompatibleOn (projectedSliceCovariantDerivative g hS)
      (inducedSliceMetric g hS) Set.univ := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro Y Z p hY hZ _ v
  obtain ⟨γ, hγ, _, hγ0, hγv⟩ := exists_smooth_curve
    (I := 𝓘(ℝ, Fin d → ℝ)) p v Set.univ isOpen_univ (Set.mem_univ p)
  subst p
  let f : S → ℝ := fun q => (inducedSliceMetric g hS).inner q (Y q) (Z q)
  have hγ1 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) 1 γ 0 :=
    (hγ.of_le (by simp)).contMDiffAt
  have hγd := hγ1.mdifferentiableAt one_ne_zero
  have hfd : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) f (γ 0) :=
    slice_metric_inner_mdifferentiableAt (inducedSliceMetric g hS) hY hZ
  have hder : deriv (f ∘ γ) 0 =
      mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) f (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) γ 0 (1 : ℝ)) := by
    have hchain := mfderiv_comp_apply (x := 0) hfd hγd (1 : ℝ)
    rw [mfderiv_eq_fderiv] at hchain
    exact fderiv_apply_one_eq_deriv.symm.trans hchain
  have hp := projectedSliceCovDerivAlong_metric_compat_of_mdifferentiableAt
    g hS γ (fun s => Y (γ s)) (fun s => Z (γ s)) 0 hγ1
    (hY.comp 0 hγd) (hZ.comp 0 hγd)
  rw [projectedSliceCovDerivAlong_restrict g hS γ Y 0 hγ1 hY,
    projectedSliceCovDerivAlong_restrict g hS γ Z 0 hγ1 hZ, hγv] at hp
  have hvalue := hp.deriv
  change deriv (f ∘ γ) 0 = _ at hvalue
  rw [hder, hγv] at hvalue
  exact hvalue

theorem projectedSliceCovariantDerivative_eq_leviCivita [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ (Y : ∀ q : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) q) (p : S),
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ)
        (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun q => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) p →
      ∀ v : TangentSpace 𝓘(ℝ, Fin d → ℝ) p,
        projectedSliceCovariantDerivative g hS Y p v =
          (LeviCivita (I := 𝓘(ℝ, Fin d → ℝ)) (inducedSliceMetric g hS)).toFun Y p v := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro Y p hY v
  obtain ⟨X, hXp⟩ := ContMDiffSection.exists_eq_at
    (I := 𝓘(ℝ, Fin d → ℝ)) (n := (⊤ : ℕ∞)) (F := Fin d → ℝ)
    (V := (TangentSpace 𝓘(ℝ, Fin d → ℝ) : S → Type _)) p v
  have hTF₁ : ∀ ⦃A B : ∀ q : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) q⦄ ⦃q : S⦄,
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun r => (⟨r, A r⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) q →
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun r => (⟨r, B r⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) q →
      q ∈ (Set.univ : Set S) →
      projectedSliceCovariantDerivative g hS B q (A q) -
        projectedSliceCovariantDerivative g hS A q (B q) =
          VectorField.mlieBracket 𝓘(ℝ, Fin d → ℝ) A B q := by
    intro A B q hA hB _
    exact projectedSliceCovariantDerivative_torsion g hS A B q hA hB
  have hTF₂ : ∀ ⦃A B : ∀ q : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) q⦄ ⦃q : S⦄,
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun r => (⟨r, A r⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) q →
      MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun r => (⟨r, B r⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) q →
      q ∈ (Set.univ : Set S) →
      (LeviCivita (I := 𝓘(ℝ, Fin d → ℝ)) (inducedSliceMetric g hS)).toFun B q (A q) -
        (LeviCivita (I := 𝓘(ℝ, Fin d → ℝ)) (inducedSliceMetric g hS)).toFun A q (B q) =
          VectorField.mlieBracket 𝓘(ℝ, Fin d → ℝ) A B q := by
    intro A B q hA hB _
    exact (CovariantDerivative.torsion_eq_zero_iff _).mp
      (LeviCivita_torsion_eq_zero (inducedSliceMetric g hS)) hA hB
  have hloc := koszul_local_uniqueness (I := 𝓘(ℝ, Fin d → ℝ))
    (g := inducedSliceMetric g hS) (s := Set.univ) hTF₁ hTF₂
    (projectedSliceCovariantDerivative_isMetricCompatibleOn g hS)
    (LeviCivita_isMetricCompatible (inducedSliceMetric g hS))
    X.mdifferentiableAt hY (Set.mem_univ p)
  simpa only [hXp] using hloc

theorem projectedSliceCovDerivAlong_eq_covDerivAlong [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ (γ : ℝ → S) (V : ∀ s : ℝ, TangentSpace 𝓘(ℝ, Fin d → ℝ) (γ s)) (t : ℝ),
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) 1 γ t →
      MDifferentiableAt 𝓘(ℝ, ℝ) (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
        (fun s => (⟨γ s, V s⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) t →
      projectedSliceCovDerivAlong g hS γ V t =
        covDerivAlong (I := 𝓘(ℝ, Fin d → ℝ)) (inducedSliceMetric g hS) γ V t := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro γ V t hγ hV
  apply SmoothRiemannianMetric.eq_of_inner_eq (inducedSliceMetric g hS)
  intro ζ
  obtain ⟨Z, hZt⟩ := ContMDiffSection.exists_eq_at
    (I := 𝓘(ℝ, Fin d → ℝ)) (n := (⊤ : ℕ∞)) (F := Fin d → ℝ)
    (V := (TangentSpace 𝓘(ℝ, Fin d → ℝ) : S → Type _)) (γ t) ζ
  let W : ∀ s : ℝ, TangentSpace 𝓘(ℝ, Fin d → ℝ) (γ s) := fun s => Z (γ s)
  have hZ : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ)
      (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
      (fun q => (⟨q, Z q⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) (γ t) :=
    Z.mdifferentiableAt
  have hW : MDifferentiableAt 𝓘(ℝ, ℝ)
      (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ))
      (fun s => (⟨γ s, W s⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) t :=
    hZ.comp t (hγ.mdifferentiableAt one_ne_zero)
  have hWconn : projectedSliceCovDerivAlong g hS γ W t =
      covDerivAlong (I := 𝓘(ℝ, Fin d → ℝ)) (inducedSliceMetric g hS) γ W t := by
    rw [projectedSliceCovDerivAlong_restrict g hS γ (fun q => Z q) t hγ hZ,
      projectedSliceCovariantDerivative_eq_leviCivita g hS (fun q => Z q) (γ t) hZ]
    exact (covDerivAlong_eq_leviCivita_of_eventuallyEq
      (inducedSliceMetric g hS) γ t hγ hZ (Filter.EventuallyEq.rfl)).symm
  have hp := projectedSliceCovDerivAlong_metric_compat_of_mdifferentiableAt
    g hS γ V W t hγ hV hW
  have hi := inner_deriv_at (I := 𝓘(ℝ, Fin d → ℝ)) (n := 1) le_rfl
    (inducedSliceMetric g hS) γ V W t hγ
    (chartRepAt_differentiable_of_mdifferentiableAt γ V t hV)
    (chartRepAt_differentiable_of_mdifferentiableAt γ W t hW)
  have heq := hp.unique hi
  rw [hWconn] at heq
  have hpair := add_right_cancel heq
  simpa only [W, hZt] using hpair

theorem projectedSliceCovDerivAlong_difference_pairing [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ (γ : ℝ → S) (V W : ∀ s : ℝ, TangentSpace 𝓘(ℝ, Fin d → ℝ) (γ s)) (t : ℝ),
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin d → ℝ) 1 γ t →
      ContMDiffAt 𝓘(ℝ, ℝ) (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ)) 1
        (fun s => (⟨γ s, V s⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) t →
      ContMDiffAt 𝓘(ℝ, ℝ) (ModelWithCorners.tangent 𝓘(ℝ, Fin d → ℝ)) 1
        (fun s => (⟨γ s, W s⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) S)) t →
      (inducedSliceMetric g hS).inner (γ t)
          (projectedSliceCovDerivAlong g hS γ V t -
            covDerivAlong (I := 𝓘(ℝ, Fin d → ℝ)) (inducedSliceMetric g hS) γ V t) (W t) +
        (inducedSliceMetric g hS).inner (γ t) (V t)
          (projectedSliceCovDerivAlong g hS γ W t -
            covDerivAlong (I := 𝓘(ℝ, Fin d → ℝ)) (inducedSliceMetric g hS) γ W t) = 0 := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro γ V W t hγ hV hW
  have hp := projectedSliceCovDerivAlong_metric_compat g hS γ V W t hγ hV hW
  have hi := inner_deriv_at (I := 𝓘(ℝ, Fin d → ℝ)) (n := 1) le_rfl
    (inducedSliceMetric g hS) γ V W t hγ
    (chartRepAt_differentiable_of_contMDiffAt γ V t hV)
    (chartRepAt_differentiable_of_contMDiffAt γ W t hW)
  have heq := hp.unique hi
  simp only [map_sub, sub_apply]
  linarith

theorem embeddedSlice_inclusion_covDerivAlong_dim_zero
    (g : SmoothRiemannianMetric I M) (hS : IsEmbeddedSlice I 0 S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ (γ : ℝ → S) (V : ∀ s : ℝ, TangentSpace 𝓘(ℝ, Fin 0 → ℝ) (γ s)) (t : ℝ),
      mfderiv 𝓘(ℝ, Fin 0 → ℝ) I (Subtype.val : S → M) (γ t)
          (covDerivAlong (I := 𝓘(ℝ, Fin 0 → ℝ)) (inducedSliceMetric g hS) γ V t) =
        covDerivAlong (I := I) g (fun s => (γ s).1)
          (fun s => mfderiv 𝓘(ℝ, Fin 0 → ℝ) I (Subtype.val : S → M) (γ s) (V s)) t := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro γ V t
  have hV (s : ℝ) : V s = 0 := by
    let _ : Subsingleton (TangentSpace 𝓘(ℝ, Fin 0 → ℝ) (γ s)) :=
      inferInstanceAs (Subsingleton (Fin 0 → ℝ))
    exact Subsingleton.elim _ _
  have hcov : covDerivAlong (I := 𝓘(ℝ, Fin 0 → ℝ)) (inducedSliceMetric g hS) γ V t = 0 := by
    change (_ : Fin 0 → ℝ) = 0
    exact Subsingleton.elim _ _
  have hpush : (fun s => mfderiv 𝓘(ℝ, Fin 0 → ℝ) I
      (Subtype.val : S → M) (γ s) (V s)) = fun s => (0 : TangentSpace I (γ s).1) := by
    funext s
    rw [hV s, map_zero]
  rw [hcov, map_zero, hpush, covDerivAlong_zero]

end InducedMetric

section TotalConvex

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [SigmaCompactSpace M'] [ConnectedSpace M']
  [RiemannianBundle (fun x : M' => TangentSpace I x)]
  [IsRiemannianManifold I M'] [CompleteSpace M']
  [IsContinuousRiemannianBundle E (fun x : M' => TangentSpace I x)]
  [T2Space (TangentBundle I M')]

theorem embeddedSlice_inclusion_projectedCovDerivAlong
    (g : SmoothRiemannianMetric I M') (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M'} (hconv : IsTotallyConvex (I := I) g S) (hclosed : IsClosed S)
    (hB : relBoundary I S = ∅) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ γ : ℝ → S,
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) ∞ γ →
      ∀ V : ∀ s : ℝ, TangentSpace 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) (γ s),
        ContMDiff 𝓘(ℝ, ℝ)
          (ModelWithCorners.tangent 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)) ∞
          (fun s => (⟨γ s, V s⟩ : TangentBundle 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) S)) →
        ∀ t : ℝ,
          mfderiv 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) I (Subtype.val : S → M') (γ t)
              (projectedSliceCovDerivAlong g hS γ V t) =
            covDerivAlong (I := I) g (fun s => (γ s).1)
              (fun s => mfderiv 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) I
                (Subtype.val : S → M') (γ s) (V s)) t := by
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro γ hγ V hV t
  exact inclusion_tangentProjection_of_normal_pairing_zero g hS (γ t) _
    (embeddedSlice_inclusion_normal_covDerivAlong_eq_zero g hEnorm hconv hclosed hB
      γ hγ V hV t)

theorem embeddedSlice_inclusion_covDerivAlong
    (g : SmoothRiemannianMetric I M') (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M'} (hconv : IsTotallyConvex (I := I) g S) (hclosed : IsClosed S)
    (hB : relBoundary I S = ∅) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ γ : ℝ → S,
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) ∞ γ →
      ∀ V : ∀ s : ℝ, TangentSpace 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) (γ s),
        ContMDiff 𝓘(ℝ, ℝ)
          (ModelWithCorners.tangent 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)) ∞
          (fun s => (⟨γ s, V s⟩ : TangentBundle 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) S)) →
        ∀ t : ℝ,
          mfderiv 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) I (Subtype.val : S → M') (γ t)
              (covDerivAlong (I := 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ))
                (inducedSliceMetric g hS) γ V t) =
            covDerivAlong (I := I) g (fun s => (γ s).1)
              (fun s => mfderiv 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) I
                (Subtype.val : S → M') (γ s) (V s)) t := by
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro γ hγ V hV t
  have hproj := embeddedSlice_inclusion_projectedCovDerivAlong
    g hEnorm hconv hclosed hB γ hγ V hV t
  rw [projectedSliceCovDerivAlong_eq_covDerivAlong g hS γ V t
    ((hγ.of_le (by simp)).contMDiffAt)
    (hV.mdifferentiableAt (by simp))] at hproj
  exact hproj

end TotalConvex

end DifferentialGeometry.Geometry.Topology
