import DifferentialGeometry.Geometry.Comparison.Variation.Flow
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import DifferentialGeometry.Geometry.Metric.LieDerivative.Cartan

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Variation

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.PDE.DeTurck

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem spatial_pushforward_chartCoord_contMDiffAt
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v : TangentSpace I x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (5 : ℕ)
      (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
          ((Φ_fam p.2 : M → M) x) (mfderiv I I (Φ_fam p.2 : M → M) x v)) (t, t) := by
  classical
  have h8le : ((8 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.mpr (le_top : ((8 : ℕ) : ℕ∞) ≤ ⊤)
  set α : M := (Φ_fam t : M → M) x with hα
  have hflow_at : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I (8 : ℕ)
      (Function.uncurry (fun q : ℝ × ℝ => fun y : M => (Φ_fam q.2 : M → M) y)) ((t, t), x) := by
    have hcompfun : (Function.uncurry (fun q : ℝ × ℝ => fun y : M => (Φ_fam q.2 : M → M) y))
        = (fun r : ((ℝ × ℝ) × M) => (Φ_fam r.1.2 : M → M) r.2) := rfl
    rw [hcompfun]
    have hmaps : (fun r : ((ℝ × ℝ) × M) => (r.1.2, r.2)) ((t, t), x)
        ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) := ⟨ht, Set.mem_univ _⟩
    have hmem_nhds : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M)
        ∈ nhds ((fun r : ((ℝ × ℝ) × M) => (r.1.2, r.2)) ((t, t), x)) :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds hmaps
    have hjoint_at : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I (8 : ℕ)
        (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
        ((fun r : ((ℝ × ℝ) × M) => (r.1.2, r.2)) ((t, t), x)) :=
      ((hjoint.of_le h8le).contMDiffAt hmem_nhds)
    have hinner : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, ℝ).prod I) (8 : ℕ)
        (fun r : ((ℝ × ℝ) × M) => (r.1.2, r.2)) ((t, t), x) :=
      (contMDiffAt_fst.snd).prodMk contMDiffAt_snd
    exact hjoint_at.comp ((t, t), x) hinner
  have h_smooth_mfd := ContMDiffAt.mfderiv_apply
    (I := I) (I' := I)
    (f := fun q : ℝ × ℝ => fun y : M => (Φ_fam q.2 : M → M) y)
    (g := fun _ : ℝ × ℝ => x)
    (g₁ := id) (g₂ := fun _ : ℝ × ℝ => v)
    (x₀ := (t, t)) (n := (8 : ℕ)) (m := (5 : ℕ))
    (by simpa using hflow_at) contMDiffAt_const contMDiffAt_id contMDiffAt_const
    (by exact_mod_cast (by norm_num : (5 : ℕ) + 1 ≤ 8))
  refine h_smooth_mfd.congr_of_eventuallyEq ?_
  have hcontAt : ContinuousAt (fun p : ℝ × ℝ => (Φ_fam p.2 : M → M) x) (t, t) := by
    have hflowAt : ContinuousAt (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (t, x) := by
      have hmem : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) ∈ nhds (t, x) :=
        (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, Set.mem_univ _⟩
      exact hjoint.continuousOn.continuousAt hmem
    have hcomp : ContinuousAt (fun p : ℝ × ℝ => ((p.2, x) : ℝ × M)) (t, t) :=
      (continuous_snd.prodMk continuous_const).continuousAt
    exact ContinuousAt.comp (g := fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (x := (t, t)) (by simpa using hflowAt) hcomp
  have hαsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hpre : (fun p : ℝ × ℝ => (Φ_fam p.2 : M → M) x) ⁻¹' (chartAt H α).source ∈ nhds (t, t) :=
    hcontAt.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds (by rw [hα]; exact hαsrc))
  filter_upwards [hpre] with p hp
  have hxsrc : (id ((fun _ : ℝ × ℝ => x) p)) ∈
    (chartAt H ((fun _ : ℝ × ℝ => x) (t, t))).source := by
    simp [mem_chart_source]
  have hysrc : ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) p)
      ∈ (chartAt H ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) (t, t))).source := by
    simpa [hα] using hp
  symm
  simp only [id_eq]
  rw [inTangentCoordinates_eq (I := I) (I' := I)
        (f := fun _ : ℝ × ℝ => x) (g := fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x)
        (ϕ := fun q : ℝ × ℝ => mfderiv I I (fun y : M => (Φ_fam q.2 : M → M) y) x) hxsrc hysrc]
  have htarget_eq : (tangentBundleCore I M).coordChange
        (achart H ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) p))
        (achart H ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) (t, t)))
        ((fun q : ℝ × ℝ => (Φ_fam q.2 : M → M) x) p)
      = (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
        ((Φ_fam p.2 : M → M) x) := by
    change (tangentBundleCore I M).coordChange (achart H ((Φ_fam p.2 : M → M) x)) (achart H α)
        ((Φ_fam p.2 : M → M) x)
      = (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ ((Φ_fam p.2 : M → M) x)
    have hsrcα : (Φ_fam p.2 : M → M) x ∈ (chartAt H α).source := hp
    exact (TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (b₀ := α) (b := (Φ_fam p.2 : M → M) x) hsrcα).symm
  rw [htarget_eq]
  change (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
      ((Φ_fam p.2 : M → M) x)
        (mfderiv I I (Φ_fam p.2 : M → M) x
          ((tangentBundleCore I M).coordChange (achart H x) (achart H x) x v)) =
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
      ((Φ_fam p.2 : M → M) x) (mfderiv I I (Φ_fam p.2 : M → M) x v)
  rw [show ((tangentBundleCore I M).coordChange (achart H x) (achart H x) x) v = v from
    (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v]

omit [SigmaCompactSpace M] [CompactSpace M] [NeZero (Module.finrank ℝ E)] in
theorem flow_metric_pairing_hasDerivWithinAt_of_neg_velocity
    (g : SmoothRiemannianMetric I M)
    (X : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-(X t ((Φ_fam t : M → M) x)))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => g.inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w))
      (-lieDerivMetric (I := I) g (X t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t := by
  classical
  set γ : ℝ → M := fun s : ℝ => (Φ_fam s : M → M) x with hγ
  set V : ∀ s : ℝ, TangentSpace I (γ s) :=
    fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x v with hV
  set W : ∀ s : ℝ, TangentSpace I (γ s) :=
    fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x w with hW
  have h8le : ((8 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.mpr (le_top : ((8 : ℕ) : ℕ∞) ≤ ⊤)
  have hchartRepDiff : ∀ u : TangentSpace I x,
      DifferentiableAt ℝ (chartRepAt (I := I) γ
        (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x u) t) t := by
    intro u
    have hlin := spatial_pushforward_chartCoord_contMDiffAt (I := I) T Φ_fam hjoint t ht x u
    have hrestr : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (5 : ℕ)
        (fun s : ℝ =>
          (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
            ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) t := by
      have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (5 : ℕ)
          (fun s : ℝ => (t, s)) t := contMDiffAt_const.prodMk contMDiffAt_id
      exact hlin.comp t hincl
    have hcd : ContDiffAt ℝ (5 : ℕ)
        (fun s : ℝ =>
          (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
            ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) t := by
      rw [← contMDiffAt_iff_contDiffAt]
      exact hrestr
    have hdiffAt : DifferentiableAt ℝ
        (fun s : ℝ =>
          (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
            ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) t :=
      hcd.differentiableAt (by norm_num)
    have hfun : chartRepAt (I := I) γ
        (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x u) t =
      (fun s : ℝ =>
        (trivializationAt E (TangentSpace I) ((Φ_fam t : M → M) x)).continuousLinearMapAt ℝ
          ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) := by
      funext s
      rw [chartRepAt_apply]
    rw [hfun]
    exact hdiffAt
  have hγ_at : ContMDiffAt 𝓘(ℝ, ℝ) I (8 : ℕ) γ t := by
    have hmem : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) ∈ nhds (t, x) :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, Set.mem_univ _⟩
    have hflow_tx : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I (8 : ℕ)
        (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (t, x) :=
      (hjoint.of_le h8le).contMDiffAt hmem
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (8 : ℕ)
        (fun s : ℝ => ((s, x) : ℝ × M)) t := contMDiffAt_id.prodMk contMDiffAt_const
    exact ContMDiffAt.comp (g := fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) (x := t)
      (by simpa using hflow_tx) hincl
  have hchartDeriv : DifferentiableAt ℝ (chartCurve (I := I) (γ t) γ) t := by
    have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (8 : ℕ) ((extChartAt I (γ t)) ∘ γ) t := by
      have hφ : ContMDiffAt I 𝓘(ℝ, E) (8 : ℕ) (extChartAt I (γ t)) (γ t) :=
        (contMDiffAt_extChartAt (I := I) (x := γ t)).of_le h8le
      exact hφ.comp t hγ_at
    exact (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt (by norm_num)
  have hmc := metric_compat_hasDerivAt_inner_of_chartCurveDeriv (I := I)
    g γ V W t hγ_at.continuousAt hchartDeriv (hchartRepDiff v) (hchartRepDiff w)
  have hG2v := flow_cov_variation (I := I) g X T Φ_fam hΦode hjoint t ht x v
  have hG2w := flow_cov_variation (I := I) g X T Φ_fam hΦode hjoint t ht x w
  have hAval : g.inner (γ t) (covDerivAlong (I := I) g γ V t) (W t)
      = -g.inner ((Φ_fam t : M → M) x)
          ((LeviCivita (I := I) g) (X t : ∀ y : M, TangentSpace I y)
            ((Φ_fam t : M → M) x)
            (mfderiv I I (Φ_fam t : M → M) x v))
          (mfderiv I I (Φ_fam t : M → M) x w) := by
    rw [hV, hG2v, map_neg]
    rfl
  have hBval : g.inner (γ t) (V t) (covDerivAlong (I := I) g γ W t)
      = -g.inner ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          ((LeviCivita (I := I) g) (X t : ∀ y : M, TangentSpace I y)
            ((Φ_fam t : M → M) x)
            (mfderiv I I (Φ_fam t : M → M) x w)) := by
    rw [hW, hG2w, map_neg]
  have hsumval : g.inner (γ t) (covDerivAlong (I := I) g γ V t) (W t)
        + g.inner (γ t) (V t) (covDerivAlong (I := I) g γ W t)
      = -lieDerivMetric (I := I) g (X t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w) := by
    rw [hAval, hBval,
      DifferentialGeometry.PDE.RicciFlow.Pullback.cartan_formula_for_lie_deriv_metric]
    ring
  have hmc' : HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (W s))
      (-lieDerivMetric (I := I) g (X t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) t := by
    rw [← hsumval]
    exact hmc
  exact hmc'.hasDerivWithinAt

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem flow_metric_pairing_hasDerivWithinAt
    (g : SmoothRiemannianMetric I M)
    (X : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t ((Φ_fam t : M → M) x))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => g.inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (lieDerivMetric (I := I) g (X t) ((Φ_fam t : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t := by
  have hneg : ∀ z : M, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) z)
        (Set.Ici (0 : ℝ)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-((-X s) ((Φ_fam s : M → M) z)))) := by
    intro z s hs
    simpa using hΦode z s hs
  have h := flow_metric_pairing_hasDerivWithinAt_of_neg_velocity
    (I := I) g (fun s => -X s) T Φ_fam hneg hjoint t ht x v w
  convert h using 1
  rw [show -X t = (-1 : ℝ) • X t by simp,
    lieDerivMetric_smul_vectorField]
  ring

end DifferentialGeometry.Geometry.Riemannian.Variation

end
