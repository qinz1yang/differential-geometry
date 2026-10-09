import DifferentialGeometry.Geometry.Collapse.CuspEmbeddingDiffeomorph
import DifferentialGeometry.Geometry.Collapse.CuspEmbeddingPathLength
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.FirstExit

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Topology.Manifold GC.Endpoint Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

private theorem isCompact_cusp_height_le (H : ℝ) :
    IsCompact {q : CuspHalfSpace | q.2.val 0 ≤ H} := by
  let f : Torus × Icc (0 : ℝ) H → CuspHalfSpace := fun q =>
    (q.1, halfSpaceOneHomeomorph.symm ⟨q.2.val, q.2.property.1⟩)
  have hf : Continuous f := by
    refine continuous_fst.prodMk ?_
    exact halfSpaceOneHomeomorph.symm.continuous.comp
      ((continuous_subtype_val.comp continuous_snd).subtype_mk fun q => q.2.property.1)
  have hrange : range f = {q : CuspHalfSpace | q.2.val 0 ≤ H} := by
    ext q
    constructor
    · rintro ⟨a, rfl⟩
      have hheight :
          (halfSpaceOneHomeomorph.symm ⟨a.2.val, a.2.property.1⟩).val 0 = a.2.val :=
        by
        have h := congrArg Subtype.val
          (halfSpaceOneHomeomorph.apply_symm_apply ⟨a.2.val, a.2.property.1⟩)
        exact h
      change (halfSpaceOneHomeomorph.symm ⟨a.2.val, a.2.property.1⟩).val 0 ≤ H
      rw [hheight]
      exact a.2.property.2
    · intro hq
      refine ⟨(q.1, ⟨q.2.val 0, q.2.property, hq⟩), ?_⟩
      change (q.1, halfSpaceOneHomeomorph.symm (halfSpaceOneHomeomorph q.2)) = q
      rw [halfSpaceOneHomeomorph.symm_apply_apply]
  rw [← hrange]
  exact isCompact_range hf

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem metricPathELength_congr_path
    {W : CompactCarrier.{u}} (g : SmoothRiemannianMetric W.model W.Carrier)
    {γ γ' : ℝ → W.Carrier} {a b : ℝ} (heq : EqOn γ γ' (Icc a b)) :
    metricPathELength g γ a b = metricPathELength g γ' a b := by
  let : RiemannianBundle (fun p : W.Carrier => TangentSpace W.model p) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.pathELength_congr heq

theorem CuspEmbedding.riemannianBallOf_subset_image_height_lt_of_lt_one
    {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier}
    {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (hδ : δ < 1)
    {H r : ℝ} {p : CuspHalfSpace}
    (hp : p.2.val 0 < H) (hH : H < cuspDepth)
    (hr : r ≤ (H - p.2.val 0) / Real.sqrt ((1 - δ)⁻¹)) :
    riemannianBallOf g (e.toFun p) r ⊆
      e.toFun '' {q : CuspHalfSpace | q.2.val 0 < H} := by
  let F : PartialDiffeomorph halfCollarModel W.model CuspHalfSpace W.Carrier 1 :=
    (e.restrictOrder (Nat.zero_le K)).toPartialDiffeomorph
  have hF : (F : CuspHalfSpace → W.Carrier) = e.toFun := rfl
  let z : CuspHalfSpace → ℝ := fun q => q.2.val 0
  let S : Set CuspHalfSpace := {q | z q ≤ H}
  have hz : Continuous z :=
    (contMDiff_halfSpaceOneCoordinate.comp (contMDiff_snd (I := torusModel) (J := 𝓡∂ 1))).continuous
  have hSclosed : IsClosed S := isClosed_le hz continuous_const
  have hSsource : S ⊆ F.source := by
    intro q hq
    change q.2.val 0 < cuspDepth
    exact hq.trans_lt hH
  have hSdomain : S ⊆ cuspDomain := by
    intro q hq
    exact hq.trans_lt hH
  have hScompact : IsCompact S := isCompact_cusp_height_le H
  have himageClosed : IsClosed ((F : CuspHalfSpace → W.Carrier) '' S) :=
    (hScompact.image_of_continuousOn
      (F.contMDiffOn_toFun.continuousOn.mono hSsource)).isClosed
  have hfrontier {q : CuspHalfSpace} (hq : q ∈ frontier S) : z q = H := by
    have hqS : q ∈ S := hSclosed.closure_eq ▸ hq.1
    have hle : z q ≤ H := hqS
    apply le_antisymm hle
    by_contra! hlt
    have hopen : IsOpen {q : CuspHalfSpace | z q < H} :=
      isOpen_lt hz continuous_const
    have hsub : {q : CuspHalfSpace | z q < H} ⊆ interior S :=
      interior_maximal (fun x hx => show z x ≤ H from le_of_lt hx) hopen
    exact hq.2 (hsub hlt)
  let c : ℝ := Real.sqrt ((1 - δ)⁻¹)
  have hc : 0 < c := Real.sqrt_pos.mpr (inv_pos.mpr (sub_pos.mpr hδ))
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hcr : c * r ≤ H - z p := by
    have h := (le_div_iff₀ hc).mp hr
    simpa only [mul_comm] using h
  intro q hqball
  by_contra hq
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := exists_lt_of_edistOf_lt g hqball
  have hshort : ENNReal.ofReal c * metricPathELength g γ 0 1 <
      ENNReal.ofReal (H - z p) := by
    calc
      ENNReal.ofReal c * metricPathELength g γ 0 1 <
          ENNReal.ofReal c * ENNReal.ofReal r :=
        ENNReal.mul_lt_mul_right hc0 ENNReal.ofReal_ne_top hlength
      _ = ENNReal.ofReal (c * r) := (ENNReal.ofReal_mul hc.le).symm
      _ ≤ ENNReal.ofReal (H - z p) := ENNReal.ofReal_le_ofReal hcr
  have hforbidden (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (β : ℝ → CuspHalfSpace)
      (hβ : ContMDiffOn 𝓘(ℝ) halfCollarModel 1 β (Icc 0 t))
      (hβS : MapsTo β (Icc 0 t) S) (hβ0 : β 0 = p)
      (hβt : z (β t) = H) (heq : EqOn (e.toFun ∘ β) γ (Icc 0 t)) : False := by
    have hheight := e.height_edist_le_metricPathELength hδ ht.1 hβ
      (fun s hs => hSdomain (hβS hs))
    have hdist : edist ((β 0).2.val 0) ((β t).2.val 0) =
        ENNReal.ofReal (H - z p) := by
      rw [hβ0, show (β t).2.val 0 = H from hβt, edist_dist, Real.dist_eq]
      change ENNReal.ofReal |z p - H| = ENNReal.ofReal (H - z p)
      rw [abs_of_nonpos (sub_nonpos.mpr hp.le), neg_sub]
    rw [hdist, metricPathELength_congr_path g heq] at hheight
    have hprefix := metricPathELength_mono g γ (a := 0) (b := t)
      (a' := 0) (b' := 1) le_rfl ht.2
    exact (not_lt_of_ge (hheight.trans (mul_le_mul_right hprefix _))) hshort
  have hstart : γ 0 ∈ (F : CuspHalfSpace → W.Carrier) '' S := by
    refine ⟨p, hp.le, ?_⟩
    exact hγ0.symm
  by_cases hstay : MapsTo γ (Icc (0 : ℝ) 1)
      ((F : CuspHalfSpace → W.Carrier) '' S)
  · let β : ℝ → CuspHalfSpace := (F.symm : W.Carrier → CuspHalfSpace) ∘ γ
    have htarget : MapsTo γ (Icc (0 : ℝ) 1) F.target := by
      intro s hs
      obtain ⟨x, hx, hFx⟩ := hstay hs
      exact hFx ▸ F.map_source' (hSsource hx)
    have hβ : ContMDiffOn 𝓘(ℝ) halfCollarModel 1 β (Icc 0 1) :=
      F.symm.contMDiffOn_toFun.comp hγ htarget
    have hβS : MapsTo β (Icc (0 : ℝ) 1) S := by
      intro s hs
      obtain ⟨x, hx, hFx⟩ := hstay hs
      change (F.symm : W.Carrier → CuspHalfSpace) (γ s) ∈ S
      have hleft : (F.symm : W.Carrier → CuspHalfSpace) (F x) = x :=
        F.left_inv' (hSsource hx)
      rw [← hFx, hleft]
      exact hx
    have heq : EqOn (e.toFun ∘ β) γ (Icc (0 : ℝ) 1) := by
      intro s hs
      exact F.right_inv' (htarget hs)
    have hβ0 : β 0 = p := by
      change (F.symm : W.Carrier → CuspHalfSpace) (γ 0) = p
      rw [hγ0]
      exact F.left_inv' (hSsource hp.le)
    have hβ1 : z (β 1) = H := by
      apply le_antisymm (hβS (right_mem_Icc.mpr zero_le_one))
      by_contra! hlt
      apply hq
      exact ⟨β 1, hlt, (heq (right_mem_Icc.mpr zero_le_one)).trans hγ1⟩
    exact hforbidden 1 ⟨zero_le_one, le_rfl⟩ β hβ hβS hβ0 hβ1 heq
  · obtain ⟨t, β, ht, hβ, heqF, hβS, _, hβfront, _⟩ :=
      DifferentialGeometry.Topology.PartialDiffeomorph.exists_contMDiffOn_first_exit_lift_of_closed_image
        F S hSsource himageClosed γ hγ hstart hstay
    have heq : EqOn (e.toFun ∘ β) γ (Icc (0 : ℝ) t) := by
      simpa only [hF] using heqF
    have hβ0 : β 0 = p := by
      apply F.toOpenPartialHomeomorph.injOn
        (hSsource (hβS ⟨le_rfl, ht.1⟩)) (hSsource hp.le)
      calc
        F (β 0) = γ 0 := heqF ⟨le_rfl, ht.1⟩
        _ = F p := hγ0
    exact hforbidden t ⟨ht.1, ht.2.le⟩ β hβ hβS hβ0 (hfrontier hβfront) heq

end DifferentialGeometry.Geometry.Collapse
