import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBarrierTransferA_O27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterTransferFinal_S40

set_option autoImplicit false

/-! CH12-O27 G1 (part B) — count-free copy of the S41 curvature bridge and the S40 transfer assembly
(`hTrans_of_curv_S40`, `hUp_S41`, `hLow_S41`, `hC0_S40`) for ONE model datum `hD`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {Hm : FiniteVolumeHyperbolicModel.{u}} {st : ℝ} {acc : ℝ → ℝ}
  {dom : ℝ → TopologicalSpace.Opens Hm.Carrier}
  {mp : (t : ℝ) → st ≤ t → Hm.Carrier → (postStage F.observation t).Carrier}

/-- Count-free copy of `accuracy_inv_large_S29`. -/
theorem accuracy_inv_large_O27 (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
      (∀ t (ht : st ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : dom t => mp t ht x)) ∧
      (∀ t, st ≤ t → riemannianBallOf Hm.metric Hm.basepoint (2 * (acc t)⁻¹) ⊆ dom t) ∧
      (∀ t (ht : st ≤ t),
        let h := Hm.metric; let error := fun p : Hm.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (mp t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(acc t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h Hm.basepoint (2 * (acc t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < acc t) ∧
      (∀ t, st ≤ t → 0 < acc t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → acc t < ε))) (N : ℝ) :
    ∃ T₀ : ℝ, st ≤ T₀ ∧ ∀ t, T₀ ≤ t → N ≤ (acc t)⁻¹ := by
  obtain ⟨T, hT⟩ := hD.2.2.2.2.2 (1 / (max N 1)) (by positivity)
  refine ⟨max st T, le_max_left _ _, fun t ht => ?_⟩
  have h1 := hT t ((le_max_right _ _).trans ht)
  have hp := hD.2.2.2.2.1 t ((le_max_left _ _).trans ht)
  have hm : 0 < max N 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have : max N 1 < (acc t)⁻¹ := by
    rw [lt_inv_comm₀ hm hp]
    simpa [one_div] using h1
  exact (le_max_left _ _).trans this.le

theorem bufferedMap_partialDiffeo_O27 (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
      (∀ t (ht : st ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : dom t => mp t ht x)) ∧
      (∀ t, st ≤ t → riemannianBallOf Hm.metric Hm.basepoint (2 * (acc t)⁻¹) ⊆ dom t) ∧
      (∀ t (ht : st ≤ t),
        let h := Hm.metric; let error := fun p : Hm.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (mp t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(acc t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h Hm.basepoint (2 * (acc t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < acc t) ∧
      (∀ t, st ≤ t → 0 < acc t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → acc t < ε)))
    (t : ℝ) (ht : st ≤ t) (z : (Hm).Carrier)
    (hz : z ∈ dom t) :
    ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) (Hm).Carrier
        (postStage F.observation t).Carrier ∞,
      Φ.source = (dom t : Set (Hm).Carrier) ∧
      ∀ x ∈ (dom t : Set (Hm).Carrier), Φ x = mp t ht x := by
  obtain ⟨hf, hinj⟩ := bufferedMap_localDiffeo_O27 hD t ht
  let p : dom t := ⟨z, hz⟩
  let V := hf.image
  let e : Diffeomorph (𝓡 3) (𝓡 3) (dom t) V ∞ :=
    DifferentialGeometry.Topology.diffeomorphRangeOfInjective hf hinj
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) (dom t) ⟨p⟩
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) V ⟨e p⟩
  let Φ := (iU.symm.trans e.toPartialDiffeomorph).trans iV
  have hsrc : Φ.source = (dom t : Set (Hm).Carrier) := by
    ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (univ : Set (dom t))) ∧
      e (iU.symm x) ∈ (univ : Set V)) ↔ x ∈ dom t
    simp only [mem_univ, and_true, iU,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  refine ⟨Φ, hsrc, fun x hx => ?_⟩
  change (e (iU.symm x) : (postStage F.observation t).Carrier) = _
  rw [show iU.symm x = (⟨x, hx⟩ : dom t) from
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply (𝓡 3) (dom t)
      ⟨p⟩ hx]
  rfl

theorem bufferedMap_pullbackGerm_O27 (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
      (∀ t (ht : st ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : dom t => mp t ht x)) ∧
      (∀ t, st ≤ t → riemannianBallOf Hm.metric Hm.basepoint (2 * (acc t)⁻¹) ⊆ dom t) ∧
      (∀ t (ht : st ≤ t),
        let h := Hm.metric; let error := fun p : Hm.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (mp t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(acc t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h Hm.basepoint (2 * (acc t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < acc t) ∧
      (∀ t, st ≤ t → 0 < acc t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → acc t < ε)))
    (t : ℝ) (ht : st ≤ t)
    (gb : SmoothRiemannianMetric (𝓡 3) (postStage F.observation t).Carrier)
    (z : (Hm).Carrier) (hz : z ∈ dom t) :
    ∃ q : SmoothRiemannianMetric (𝓡 3) (Hm).Carrier,
      (∀ᶠ w in 𝓝 z, q.inner w = localPullInner gb (mp t ht) w) ∧
      ∀ κ : ℝ, SectionalBoundedBelowAt q z κ ↔
        SectionalBoundedBelowAt gb (mp t ht z) κ := by
  obtain ⟨Φ, hsrc, hΦ⟩ := bufferedMap_partialDiffeo_O27 hD t ht z hz
  have hzΦ : z ∈ Φ.source := by rw [hsrc]; exact hz
  have hK : ({Φ z} : Set (postStage F.observation t).Carrier) ⊆ Φ.symm.source := by
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact Φ.map_source' hzΦ
  obtain ⟨q, U, hKU, _, hmetric, _⟩ :=
    Φ.symm.exists_metric_preserving_on_neighborhood_of_is_compact
      gb (Hm).metric isCompact_singleton hK
  let O : TopologicalSpace.Opens (Hm).Carrier :=
    ⟨Φ.source ∩ (Φ : (Hm).Carrier → (postStage F.observation t).Carrier) ⁻¹' U,
      Φ.toOpenPartialHomeomorph.isOpen_inter_preimage U.isOpen⟩
  have hzO : z ∈ O := ⟨hzΦ, hKU (by simp)⟩
  have hiso : ∀ x ∈ (O : Set (Hm).Carrier), ∀ a b : TangentSpace (𝓡 3) x,
      q.inner x a b = gb.inner (Φ x) (mfderiv (𝓡 3) (𝓡 3) Φ x a) (mfderiv (𝓡 3) (𝓡 3) Φ x b) := by
    intro x hx a b
    have hxsource : x ∈ Φ.source := hx.1
    have hxd : MDifferentiableAt (𝓡 3) (𝓡 3) Φ x :=
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds hxsource)).mdifferentiableAt (by simp)
    have hyd : MDifferentiableAt (𝓡 3) (𝓡 3) Φ.symm (Φ x) :=
      (Φ.contMDiffOn_invFun.contMDiffAt
        (Φ.open_target.mem_nhds (Φ.map_source' hxsource))).mdifferentiableAt (by simp)
    have heq : (Φ.symm : (postStage F.observation t).Carrier → (Hm).Carrier) ∘ Φ
        =ᶠ[𝓝 x] id := by
      filter_upwards [Φ.open_source.mem_nhds hxsource] with y hy
      exact Φ.left_inv' hy
    have hinverse (v : TangentSpace (𝓡 3) x) :
        mfderiv (𝓡 3) (𝓡 3) Φ.symm (Φ x) (mfderiv (𝓡 3) (𝓡 3) Φ x v) = v := by
      have hc := mfderiv_comp_apply x hyd hxd v
      rw [heq.mfderiv_eq, mfderiv_id] at hc
      exact hc.symm
    have hg := hmetric (Φ x) hx.2 (mfderiv (𝓡 3) (𝓡 3) Φ x a) (mfderiv (𝓡 3) (𝓡 3) Φ x b)
    rw [hinverse a, hinverse b] at hg
    exact (congrArg (fun y : (Hm).Carrier => q.inner y a b)
      (Φ.left_inv' hxsource)).symm.trans hg.symm
  refine ⟨q, ?_, fun κ => ?_⟩
  · filter_upwards [O.isOpen.mem_nhds hzO, (dom t).isOpen.mem_nhds hz] with w hwO hwU
    have hev : (Φ : (Hm).Carrier → _) =ᶠ[𝓝 w] mp t ht := by
      filter_upwards [(dom t).isOpen.mem_nhds hwU] with y hy using hΦ y hy
    ext a b
    rw [hiso w hwO a b, localPullInner_apply, hev.mfderiv_eq, hΦ w hwU]
    rfl
  · have h := sectionalBoundedBelowAt_iff_of_isometricOnOpen_BDRY1 q gb Φ O.isOpen
      (fun _ hx => hx.1) hiso hzO (κ := κ)
    rwa [hΦ z hz] at h

theorem bufferedMap_curvature_bridge_O27 (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
      (∀ t (ht : st ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : dom t => mp t ht x)) ∧
      (∀ t, st ≤ t → riemannianBallOf Hm.metric Hm.basepoint (2 * (acc t)⁻¹) ⊆ dom t) ∧
      (∀ t (ht : st ≤ t),
        let h := Hm.metric; let error := fun p : Hm.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (mp t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(acc t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h Hm.basepoint (2 * (acc t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < acc t) ∧
      (∀ t, st ≤ t → 0 < acc t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → acc t < ε)))
    (t : ℝ) (ht : st ≤ t)
    (gb : SmoothRiemannianMetric (𝓡 3) (postStage F.observation t).Carrier)
    (hgb : ∀ w, localPullInner (I := 𝓡 3) (J := 𝓡 3) gb (mp t ht) w =
      (t⁻¹ : ℝ) • localPullInner (I := 𝓡 3) (J := 𝓡 3) (postMetric F.observation t)
        (mp t ht) w)
    (z : (Hm).Carrier)
    (hz : z ∈ riemannianBallOf (Hm).metric (Hm).basepoint (2 * (acc t)⁻¹))
    (hk : 2 ≤ max K ⌈(acc t)⁻¹⌉₊) :
    ∃ q : SmoothRiemannianMetric (𝓡 3) (Hm).Carrier,
      (∀ j : ℕ, j ≤ 2 → metricDerivNorm j q (Hm).metric (Hm).metric z <
        acc t) ∧
      ∀ κ : ℝ, SectionalBoundedBelowAt q z κ ↔
        SectionalBoundedBelowAt gb (mp t ht z) κ := by
  have hzd : z ∈ dom t := hD.2.2.1 t ht hz
  obtain ⟨q, hgerm, hiff⟩ := bufferedMap_pullbackGerm_O27 hD t ht gb z hzd
  refine ⟨q, fun j hj => ?_, hiff⟩
  have hzint : (𝓡 3).IsInteriorPoint z := BoundarylessManifold.isInteriorPoint
  have hf : ContMDiffAt (𝓡 3) (𝓡 3) (2 + 1 : ℕ) (mp t ht) z :=
    ((hD.1 t ht).contMDiffAt ((dom t).isOpen.mem_nhds hzd)).of_le (by simp)
  have key := DifferentialGeometry.Geometry.metricDerivNorm_eq_raw_pullbackError_of_map_jets
    gb (Hm).metric q (f := mp t ht) (h := mp t ht) (p := z) (n := 2)
    hzint BoundarylessManifold.isInteriorPoint rfl hf hf (fun _ _ => rfl) hgerm j hj
  have herr := hD.2.2.2.1 t ht j (hj.trans hk) z hz
  simp only [← hgb] at herr
  rw [key]
  exact herr

theorem hUp_O27 (hst : 0 < st) (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
      (∀ t (ht : st ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : dom t => mp t ht x)) ∧
      (∀ t, st ≤ t → riemannianBallOf Hm.metric Hm.basepoint (2 * (acc t)⁻¹) ⊆ dom t) ∧
      (∀ t (ht : st ≤ t),
        let h := Hm.metric; let error := fun p : Hm.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (mp t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(acc t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h Hm.basepoint (2 * (acc t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < acc t) ∧
      (∀ t, st ≤ t → 0 < acc t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → acc t < ε))) :
    ∃ T₁ : ℝ, ∀ t (ht : st ≤ t), T₁ ≤ t → ∀ y ∈ riemannianBallOf (Hm).metric (Hm).basepoint (acc t)⁻¹,
        ¬ SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht))
            (postMetric F.observation t)) (mp t ht y) (-(1 / 8 : ℝ)) := by
  obtain ⟨T₀, -, hT₀⟩ := accuracy_inv_large_O27 hD 10000
  refine ⟨T₀, fun t ht hT y hy => ?_⟩
  have hn : (10000 : ℝ) ≤ (acc t)⁻¹ := hT₀ t hT
  have hpos : 0 < acc t := hD.2.2.2.2.1 t ht
  have hacc : acc t ≤ 1 / 10000 := by
    rw [le_inv_comm₀ (by norm_num) hpos] at hn
    simpa using hn
  have hceil : 2 ≤ ⌈(acc t)⁻¹⌉₊ := by
    have h2 : (2 : ℝ) ≤ ⌈(acc t)⁻¹⌉₊ := (by linarith : (2 : ℝ) ≤ (acc t)⁻¹).trans
      (Nat.le_ceil _)
    exact_mod_cast h2
  have hk : 2 ≤ max K ⌈(acc t)⁻¹⌉₊ := hceil.trans (le_max_right _ _)
  have hy2 : y ∈ riemannianBallOf (Hm).metric (Hm).basepoint
      (2 * (acc t)⁻¹) :=
    riemannianBallOf_mono _ _ (by linarith) hy
  obtain ⟨q, hq, hiff⟩ := bufferedMap_curvature_bridge_O27 hD t ht
    (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t))
    (fun w => by
      ext a b
      simp only [localPullInner_apply, scaleMetric_inner, smul_apply, smul_eq_mul])
    y hy2 hk
  obtain ⟨u, v, hu, hv, huv⟩ := exists_orthonormal_pair_model_S41 (Hm) y
  have href : ∀ a b : TangentSpace (𝓡 3) y,
      metricRm04StandardAt (Hm).metric y a b b a =
        -(1 / 4 : ℝ) * ((Hm).metric.inner y a a * (Hm).metric.inner y b b -
          (Hm).metric.inner y a b ^ 2) := fun a b => by
    rw [metricRm_eq_neg_quarter_S26 (Hm) y a b]; ring
  have hcurv : metricRm04StandardAt (Hm).metric y u v v u ≤ -(1 / 4 : ℝ) := by
    rw [href u v, hu, hv, huv]; norm_num
  have hmodel : Real.sqrt ((Hm).metric.inner y
      (riemannOp (LeviCivita (Hm).metric) y u v v)
      (riemannOp (LeviCivita (Hm).metric) y u v v)) ≤ 2 :=
    (sqrt_inner_riemannOp_self_eq_abs_of_constant_sectional_numerator
      (Hm).metric y (-(1 / 4 : ℝ)) href u v hu hv huv).trans_le (by norm_num)
  have hnot := not_sectionalBoundedBelowAt_neg_one_eighth_of_small_metric_derivatives q
    (Hm).metric y (eps := acc t) hacc (fun j hj => (hq j hj).le) u v hu hv hcurv
    hmodel
  exact fun hs => hnot ((hiff _).mpr hs)


theorem hLow_O27 (hst : 0 < st) (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
      (∀ t (ht : st ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : dom t => mp t ht x)) ∧
      (∀ t, st ≤ t → riemannianBallOf Hm.metric Hm.basepoint (2 * (acc t)⁻¹) ⊆ dom t) ∧
      (∀ t (ht : st ≤ t),
        let h := Hm.metric; let error := fun p : Hm.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (mp t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(acc t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h Hm.basepoint (2 * (acc t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < acc t) ∧
      (∀ t, st ≤ t → 0 < acc t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → acc t < ε)))
    (hC0 : ∃ T₀ : ℝ, ∀ t (ht : st ≤ t), T₀ ≤ t → ∀ y ∈ riemannianBallOf (Hm).metric (Hm).basepoint (acc t)⁻¹,
      ∀ x ∈ riemannianClosedBallOf (Hm).metric y 4, ∀ v : TangentSpace (𝓡 3) x,
        (Hm).metric.inner x v v ≤
          (2 : ℝ) ^ 2 * (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht))
            (postMetric F.observation t)).inner (mp t ht x)
            (mfderiv (𝓡 3) (𝓡 3) (mp t ht) x v)
            (mfderiv (𝓡 3) (𝓡 3) (mp t ht) x v)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ T₁ : ℝ, ∀ t (ht : st ≤ t), T₁ ≤ t → ∀ y ∈ riemannianBallOf (Hm).metric (Hm).basepoint (acc t)⁻¹,
      ∀ q ∈ riemannianBallOf (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht))
          (postMetric F.observation t)) (mp t ht y) c₀,
        SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht))
          (postMetric F.observation t)) q (-(c₀ ^ 2)⁻¹) := by
  obtain ⟨T₀, hT₀C⟩ := hC0
  obtain ⟨C0, hCpos0, hCC⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_pos_bound_intrinsic_curvature_derivative_of_metric_error
      (I := 𝓡 3) (M := (Hm).Carrier) 0 (1 / 2) 1 (by norm_num)
  set Cs : ℝ := 1 + C0 with hCs
  have hCs1 : 1 ≤ Cs := by linarith
  have hCle : C0 ≤ Cs := by linarith
  obtain ⟨T₁, -, hT₁⟩ := accuracy_inv_large_O27 hD 10000
  refine ⟨min 1 (1 / Cs), lt_min one_pos (by positivity), max T₀ T₁, fun t ht hT y hy q hq => ?_⟩
  have hn : (10000 : ℝ) ≤ (acc t)⁻¹ := hT₁ t ((le_max_right _ _).trans hT)
  have hpos : 0 < acc t := hD.2.2.2.2.1 t ht
  have hacc : acc t ≤ 1 / 2 := by
    rw [le_inv_comm₀ (by norm_num) hpos] at hn
    have : acc t ≤ (10000 : ℝ)⁻¹ := by simpa using hn
    linarith
  have hceil : 2 ≤ ⌈(acc t)⁻¹⌉₊ := by
    have h2 : (2 : ℝ) ≤ ⌈(acc t)⁻¹⌉₊ := (by linarith : (2 : ℝ) ≤ (acc t)⁻¹).trans
      (Nat.le_ceil _)
    exact_mod_cast h2
  have hk : 2 ≤ max K ⌈(acc t)⁻¹⌉₊ := hceil.trans (le_max_right _ _)
  have hyd : y ∈ dom t := hD.2.2.1 t ht
    (riemannianBallOf_mono _ _ (by linarith) hy)
  -- first exit
  have hsource : riemannianClosedBallOf (Hm).metric y 4 ⊆ (dom t : Set _) := by
    intro z hz
    apply hD.2.2.1 t ht
    have hy' : riemannianEDistOf (Hm).metric (Hm).basepoint y <
        ENNReal.ofReal (acc t)⁻¹ := hy
    have hz' : riemannianEDistOf (Hm).metric y z ≤ ENNReal.ofReal 4 := hz
    change riemannianEDistOf (Hm).metric (Hm).basepoint z <
      ENNReal.ofReal (2 * (acc t)⁻¹)
    calc riemannianEDistOf (Hm).metric (Hm).basepoint z
        ≤ riemannianEDistOf (Hm).metric (Hm).basepoint y +
          riemannianEDistOf (Hm).metric y z := riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (acc t)⁻¹ + ENNReal.ofReal 4 :=
          ENNReal.add_lt_add_of_lt_of_le (ne_of_lt (lt_of_le_of_lt hz' (by simp))) hy' hz'
      _ = ENNReal.ofReal ((acc t)⁻¹ + 4) :=
          (ENNReal.ofReal_add (by positivity) (by norm_num)).symm
      _ ≤ ENNReal.ofReal (2 * (acc t)⁻¹) :=
          ENNReal.ofReal_le_ofReal (by linarith)
  have hcap := ambient_ball_subset_image_O27 hD t ht
    (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t))
    y hyd (R := 4) (L := 2) (by norm_num) (by norm_num) hsource
    (hT₀C t ht ((le_max_left _ _).trans hT) y hy)
  have hc1 : min 1 (1 / Cs) ≤ 4 / 2 := (min_le_left _ _).trans (by norm_num)
  obtain ⟨z, hz4, rfl⟩ := hcap (riemannianBallOf_mono _ _ hc1 hq)
  have hz2 : z ∈ riemannianBallOf (Hm).metric (Hm).basepoint
      (2 * (acc t)⁻¹) := by
    have hy' : riemannianEDistOf (Hm).metric (Hm).basepoint y <
        ENNReal.ofReal (acc t)⁻¹ := hy
    have hz' : riemannianEDistOf (Hm).metric y z ≤ ENNReal.ofReal 4 := hz4
    change riemannianEDistOf (Hm).metric (Hm).basepoint z <
      ENNReal.ofReal (2 * (acc t)⁻¹)
    calc riemannianEDistOf (Hm).metric (Hm).basepoint z
        ≤ riemannianEDistOf (Hm).metric (Hm).basepoint y +
          riemannianEDistOf (Hm).metric y z := riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (acc t)⁻¹ + ENNReal.ofReal 4 :=
          ENNReal.add_lt_add_of_lt_of_le (ne_of_lt (lt_of_le_of_lt hz' (by simp))) hy' hz'
      _ = ENNReal.ofReal ((acc t)⁻¹ + 4) :=
          (ENNReal.ofReal_add (by positivity) (by norm_num)).symm
      _ ≤ ENNReal.ofReal (2 * (acc t)⁻¹) :=
          ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨q', hq', hiff⟩ := bufferedMap_curvature_bridge_O27 hD t ht
    (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t))
    (fun w => by
      ext a b
      simp only [localPullInner_apply, scaleMetric_inner, smul_apply, smul_eq_mul])
    z hz2 hk
  -- reference norm bound
  have hsec : ∀ a b : TangentSpace (𝓡 3) z,
      metricRm04StandardAt (Hm).metric z a b b a =
        -(1 / 4 : ℝ) * ((Hm).metric.inner z a a * (Hm).metric.inner z b b -
          (Hm).metric.inner z a b ^ 2) := fun a b => by
    rw [metricRm_eq_neg_quarter_S26 (Hm) z a b]; ring
  have hnorm := normSq0S_metricRm04At_eq_of_constant_sectional_numerator
    (Hm).metric z (-(1 / 4 : ℝ)) hsec
  have hrank : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3 := by simp
  rw [hrank] at hnorm
  have hRef : ∀ s ≤ 0, Real.sqrt (normSq0S (Hm).metric z (4 + s)
      (iterCov (Hm).metric 4 (metricRm04 (Hm).metric) s z)) ≤ 1 := by
    intro s hs
    obtain rfl : s = 0 := Nat.le_zero.mp hs
    refine Real.sqrt_le_one.mpr ?_
    have h0 : normSq0S (Hm).metric z (4 + 0)
        (iterCov (Hm).metric 4 (metricRm04 (Hm).metric) 0 z) =
        normSq0S (Hm).metric z 4 (metricRm04At (Hm).metric z) := rfl
    rw [h0, hnorm]; norm_num
  have hbd := hCC (Hm).metric q' z
    (fun s hs => (hq' s (by omega)).le.trans hacc) hRef
  have hbd' : normSq0S q' z 4 (metricRm04At q' z) ≤ C0 ^ 2 := by
    have h0 : normSq0S q' z (4 + 0) (iterCov q' 4 (metricRm04 q') 0 z) =
        normSq0S q' z 4 (metricRm04At q' z) := rfl
    rw [h0] at hbd
    have := Real.sqrt_le_left hCpos0.le |>.mp hbd
    exact this
  have hsecq := DifferentialGeometry.PDE.RicciFlow.sectionalBoundedBelowAt_neg_sqrt_of_normSq0S_le
    (I := 𝓡 3) q' z hbd'
  rw [Real.sqrt_sq hCpos0.le] at hsecq
  refine ((hiff _).mp hsecq).mono ?_
  -- `Cs ≤ (c₀²)⁻¹`
  have hc0 : 0 < min 1 (1 / Cs) := lt_min one_pos (by positivity)
  have hc1' : min 1 (1 / Cs) ≤ 1 := min_le_left _ _
  have hc2 : min 1 (1 / Cs) ≤ 1 / Cs := min_le_right _ _
  have hsq : (min 1 (1 / Cs)) ^ 2 ≤ 1 / Cs := by nlinarith
  have hinv : Cs ≤ ((min 1 (1 / Cs)) ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by linarith) (by positivity)]
    simpa [one_div] using hsq
  linarith [hCle]


theorem accuracy_lt_quarter_O27 (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
      (∀ t (ht : st ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : dom t => mp t ht x)) ∧
      (∀ t, st ≤ t → riemannianBallOf Hm.metric Hm.basepoint (2 * (acc t)⁻¹) ⊆ dom t) ∧
      (∀ t (ht : st ≤ t),
        let h := Hm.metric; let error := fun p : Hm.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (mp t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(acc t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h Hm.basepoint (2 * (acc t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < acc t) ∧
      (∀ t, st ≤ t → 0 < acc t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → acc t < ε))) :
    ∃ T : ℝ, ∀ t (_ : st ≤ t), T ≤ t → acc t < 1 / 4 := by
  obtain ⟨T, hT⟩ := hD.2.2.2.2.2 (1 / 4) (by norm_num)
  exact ⟨T, fun t _ ht => hT t ht⟩

theorem hC0_O27 (hst : 0 < st) (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
      (∀ t (ht : st ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : dom t => mp t ht x)) ∧
      (∀ t, st ≤ t → riemannianBallOf Hm.metric Hm.basepoint (2 * (acc t)⁻¹) ⊆ dom t) ∧
      (∀ t (ht : st ≤ t),
        let h := Hm.metric; let error := fun p : Hm.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (mp t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(acc t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h Hm.basepoint (2 * (acc t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < acc t) ∧
      (∀ t, st ≤ t → 0 < acc t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → acc t < ε))) :
    ∃ T₀ : ℝ, ∀ t (ht : st ≤ t), T₀ ≤ t → ∀ y ∈ riemannianBallOf (Hm).metric (Hm).basepoint (acc t)⁻¹,
      ∀ x ∈ riemannianClosedBallOf (Hm).metric y 4, ∀ v : TangentSpace (𝓡 3) x,
        (Hm).metric.inner x v v ≤
          (2 : ℝ) ^ 2 *
            (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht))
              (postMetric F.observation t)).inner (mp t ht x)
              (mfderiv (𝓡 3) (𝓡 3) (mp t ht) x v)
              (mfderiv (𝓡 3) (𝓡 3) (mp t ht) x v) := by
  obtain ⟨T, hT⟩ := accuracy_lt_quarter_O27 hD
  refine ⟨T, fun t ht hTt y hy x hx v => ?_⟩
  have hδ := hT t ht hTt
  have hn4 : 4 ≤ (acc t)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (hD.2.2.2.2.1 t ht)]
    norm_num
    exact hδ.le
  have hlow := bufferedMap_metric_lower_O27 hst hD t ht x
    (closedBall_subset_buffer_O27 hD t ht y hy hn4 hx) v
  have hnn := metric_inner_self_nonneg (Hm).metric x v
  nlinarith

theorem hTrans_of_curv_O27 (hst : 0 < st) (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
      (∀ t (ht : st ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : dom t => mp t ht x)) ∧
      (∀ t, st ≤ t → riemannianBallOf Hm.metric Hm.basepoint (2 * (acc t)⁻¹) ⊆ dom t) ∧
      (∀ t (ht : st ≤ t),
        let h := Hm.metric; let error := fun p : Hm.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (mp t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(acc t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h Hm.basepoint (2 * (acc t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < acc t) ∧
      (∀ t, st ≤ t → 0 < acc t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → acc t < ε)))
    (hUp : ∃ T₁ : ℝ, ∀ t (ht : st ≤ t), T₁ ≤ t → ∀ y ∈ riemannianBallOf (Hm).metric (Hm).basepoint (acc t)⁻¹,
        ¬ SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht))
          (postMetric F.observation t)) (mp t ht y) (-(1 / 8 : ℝ)))
    (hLow : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ T₁ : ℝ, ∀ t (ht : st ≤ t), T₁ ≤ t → ∀ y ∈ riemannianBallOf (Hm).metric (Hm).basepoint (acc t)⁻¹,
      ∀ q ∈ riemannianBallOf (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht))
          (postMetric F.observation t)) (mp t ht y) c₀,
        SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht))
          (postMetric F.observation t)) q (-(c₀ ^ 2)⁻¹)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ T₁ : ℝ, ∀ t (ht : st ≤ t), T₁ ≤ t →
      ∀ y ∈ riemannianBallOf (Hm).metric (Hm).basepoint (acc t)⁻¹,
        (∀ q ∈ riemannianBallOf (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht))
            (postMetric F.observation t)) (mp t ht y) c₀,
          SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht))
            (postMetric F.observation t)) q (-(c₀ ^ 2)⁻¹)) ∧
        ¬ SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht))
            (postMetric F.observation t)) (mp t ht y) (-(1 / 8 : ℝ)) ∧
        ∀ r : ℝ, 0 < r → r ^ 2 ≤ 8 →
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht))
            (postMetric F.observation t)) (mp t ht y) r ≤
          ENNReal.ofReal 2 * ballVolume (Hm).metric y 4 := by
  obtain ⟨Tu, hTu⟩ := hUp
  obtain ⟨c₀, hc₀, Tl, hTl⟩ := hLow
  obtain ⟨Tv, hTv⟩ := accuracy_lt_quarter_O27 hD
  refine ⟨c₀, hc₀, max (max Tl Tu) Tv, fun t ht hT y hy => ⟨?_, ?_, ?_⟩⟩
  · exact hTl t ht ((le_max_left _ _).trans ((le_max_left _ _).trans hT)) y hy
  · exact hTu t ht ((le_max_right _ _).trans ((le_max_left _ _).trans hT)) y hy
  · intro r hr hr8
    exact bufferedMap_ballVolume_le_O27 hst hD t ht y hy (hTv t ht ((le_max_right _ _).trans hT)).le
      hr hr8

end GC.LongTime.Ch12
