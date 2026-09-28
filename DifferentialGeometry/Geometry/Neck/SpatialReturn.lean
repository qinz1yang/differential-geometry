import DifferentialGeometry.Topology.Connected.ComplementSides
import DifferentialGeometry.Geometry.Neck.SpatialCollar

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem SpatialNeck.return_path_or_two_complement_components
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (q : Sphere 2) :
    let S := range (fun u : Sphere 2 => nk.map (u, t))
    let a := nk.map (q, (-1 + t) / 2)
    let b := nk.map (q, (t + 1) / 2)
    (IsConnected Sᶜ ∧ ∃ γ : Path a b, ∀ s, γ s ∉ S) ∨
      (Disjoint (connectedComponentIn Sᶜ a) (connectedComponentIn Sᶜ b) ∧
        connectedComponentIn Sᶜ a ∪ connectedComponentIn Sᶜ b = Sᶜ ∧
        IsConnected (connectedComponentIn Sᶜ a) ∧
        IsConnected (connectedComponentIn Sᶜ b) ∧
        IsOpen (connectedComponentIn Sᶜ a) ∧ IsOpen (connectedComponentIn Sᶜ b)) := by
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace ThreeSpace M
  let S := range (fun u : Sphere 2 => nk.map (u, t))
  let O := nk.map '' (univ ×ˢ Ioo (-1 : ℝ) 1)
  let L := nk.map '' (univ ×ˢ Ioo (-1 : ℝ) t)
  let U := nk.map '' (univ ×ˢ Ioo t 1)
  let a := nk.map (q, (-1 + t) / 2)
  let b := nk.map (q, (t + 1) / 2)
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk.eps_pos).mpr (nk.eps_small.trans (by norm_num))
  have hsource : (univ ×ˢ Ioo (-1 : ℝ) 1 : Set Cylinder) ⊆ nk.map.source := by
    intro x hx
    exact nk.domain ⟨hx.1, (neg_lt_neg hlen).trans hx.2.1, hx.2.2.trans hlen⟩
  have hSO : S ⊆ O := by rintro y ⟨u, rfl⟩; exact ⟨(u, t), ⟨mem_univ _, ht⟩, rfl⟩
  have hS : IsClosed S := by
    have hcont : Continuous (fun u : Sphere 2 => nk.map (u, t)) := by
      exact nk.map.contMDiffOn_toFun.continuousOn.comp_continuous
        (continuous_id.prodMk continuous_const) (fun u => hsource ⟨mem_univ _, ht⟩)
    exact (isCompact_range hcont).isClosed
  have hSne : S.Nonempty := ⟨nk.map (q, t), q, rfl⟩
  have hO : IsOpen O := nk.map.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo) hsource
  obtain ⟨_, _, hL, hU, _, hlocal⟩ := nk.unit_slab_local_sides ht
  have ha : a ∈ L := ⟨(q, (-1 + t) / 2), ⟨mem_univ _, by constructor <;> linarith [ht.1]⟩, rfl⟩
  have hb : b ∈ U := ⟨(q, (t + 1) / 2), ⟨mem_univ _, by constructor <;> linarith [ht.2]⟩, rfl⟩
  have haS : a ∈ Sᶜ := (hlocal.symm ▸ Or.inl ha : a ∈ O \ S).2
  have hbS : b ∈ Sᶜ := (hlocal.symm ▸ Or.inr hb : b ∈ O \ S).2
  rcases DifferentialGeometry.Topology.joinedIn_or_disjoint_components_of_two_local_sides
    hS hSne hO hSO hlocal hL.isPreconnected hU.isPreconnected ha hb with h | h
  · exact Or.inl ⟨h.1, h.2.somePath, h.2.somePath_mem⟩
  · exact Or.inr ⟨h.1, h.2, isConnected_connectedComponentIn_iff.mpr haS,
      isConnected_connectedComponentIn_iff.mpr hbS,
      hS.isOpen_compl.connectedComponentIn, hS.isOpen_compl.connectedComponentIn⟩

private theorem SpatialNeck.exists_loop_crossing_center_once_of_return_path
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    (q : Sphere 2)
    (γ : Path (nk.map (q, (-1 : ℝ) / 2)) (nk.map (q, (1 : ℝ) / 2)))
    (hγ : ∀ s, γ s ∉ range (fun u : Sphere 2 => nk.map (u, 0))) :
    ∃ l : Path (nk.map (q, (-1 : ℝ) / 2)) (nk.map (q, (-1 : ℝ) / 2)),
      (∀ s, l s ∈ range (fun u : Sphere 2 => nk.map (u, 0)) ↔ (s : ℝ) = 1 / 4) ∧
      ∀ s : unitInterval, (s : ℝ) ≤ 1 / 2 → l s = nk.map (q, 2 * (s : ℝ) - 1 / 2) := by
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk.eps_pos).mpr (nk.eps_small.trans (by norm_num))
  have hsource (s : unitInterval) : (q, (s : ℝ) - 1 / 2) ∈ nk.map.source := by
    apply nk.domain
    exact ⟨mem_univ _, by constructor <;> linarith [s.property.1, s.property.2]⟩
  let α : Path (nk.map (q, (-1 : ℝ) / 2)) (nk.map (q, (1 : ℝ) / 2)) := {
    toFun := fun s => nk.map (q, (s : ℝ) - 1 / 2)
    continuous_toFun := nk.map.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_const.prodMk (continuous_subtype_val.sub continuous_const)) hsource
    source' := by norm_num
    target' := by norm_num }
  have hcross (s : unitInterval) :
      α s ∈ range (fun u : Sphere 2 => nk.map (u, 0)) ↔ (s : ℝ) = 1 / 2 := by
    constructor
    · rintro ⟨u, hu⟩
      have huSource : (u, (0 : ℝ)) ∈ nk.map.source :=
        nk.domain ⟨mem_univ _, by constructor <;> linarith⟩
      have heq := nk.map.injOn huSource (hsource s) hu
      have hh := congrArg Prod.snd heq
      dsimp only at hh
      linarith
    · intro hs
      refine ⟨q, ?_⟩
      change nk.map (q, 0) = nk.map (q, (s : ℝ) - 1 / 2)
      rw [hs, sub_self]
  refine ⟨α.trans γ.symm, ?_, ?_⟩
  · intro s
    rw [Path.trans_apply]
    split_ifs with hs
    · rw [hcross]
      constructor <;> intro h <;> dsimp at h ⊢ <;> linarith
    · have hn := hγ (unitInterval.symm ⟨2 * s - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.mp hs).le, s.property.2⟩⟩)
      simp only [Path.symm_apply]
      constructor
      · intro h
        exact False.elim (hn h)
      · intro h
        exact False.elim (hs (by linarith))
  · intro s hs
    rw [Path.trans_apply, dite_eq_left hs]
    rfl

theorem SpatialNeck.loop_crossing_center_once_or_two_complement_components
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    (q : Sphere 2) :
    let S := range (fun u : Sphere 2 => nk.map (u, 0))
    let a := nk.map (q, (-1 : ℝ) / 2)
    let b := nk.map (q, (1 : ℝ) / 2)
    (IsConnected Sᶜ ∧ ∃ l : Path a a,
      (∀ s, l s ∈ S ↔ (s : ℝ) = 1 / 4) ∧
      (∀ s : unitInterval, (s : ℝ) ≤ 1 / 2 → l s = nk.map (q, 2 * (s : ℝ) - 1 / 2))) ∨
      (Disjoint (connectedComponentIn Sᶜ a) (connectedComponentIn Sᶜ b) ∧
        connectedComponentIn Sᶜ a ∪ connectedComponentIn Sᶜ b = Sᶜ ∧
        IsConnected (connectedComponentIn Sᶜ a) ∧
        IsConnected (connectedComponentIn Sᶜ b) ∧
        IsOpen (connectedComponentIn Sᶜ a) ∧ IsOpen (connectedComponentIn Sᶜ b)) := by
  have h := nk.return_path_or_two_complement_components (t := 0) (by norm_num) q
  dsimp only at h ⊢
  simp only [add_zero, zero_add] at h
  rcases h with ⟨hconn, γ, hγ⟩ | hsep
  · exact Or.inl ⟨hconn, nk.exists_loop_crossing_center_once_of_return_path q γ hγ⟩
  · exact Or.inr hsep

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
