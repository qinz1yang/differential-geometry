import DifferentialGeometry.Topology.Manifold.SphereGraphExtension
import DifferentialGeometry.Geometry.Neck.SpatialReflection
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.SupportedExtension
import DifferentialGeometry.Geometry.Neck.SpatialExtension
import DifferentialGeometry.Topology.SphereSeparation.Transport
import DifferentialGeometry.Topology.SphereSeparation.BallSideRelations
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Topology.MetricSpace.Cover

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.SphereSeparation

universe u

private theorem SpatialNeck.exists_diffeomorph_center_eq_graph
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p) (h : Sphere 2 → ℝ) (hh : ContMDiff I2 𝓘(ℝ) ∞ h)
    (hb : ∀ q, (1 / 2 : ℝ) < h q ∧ h q < 3 / 2) :
    ∃ F : M ≃ₘ⟮I3, I3⟯ M, ∀ q : Sphere 2, F (nk.map (q, 0)) = nk.map (q, h q) := by
  classical
  obtain ⟨D, hD, K, hK, hKU, hfix, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_supported_diffeomorph_eq_graph_collar
      h hh 0 0 (-2) 2 (by norm_num) (fun q => by constructor <;> linarith [(hb q).1, (hb q).2])
  have hlen : (2 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
    (by linarith [nk.eps_small])
  have hKs : K ⊆ nk.map.source := by
    intro z hz
    have hx := hKU hz
    exact nk.domain ⟨hx.1, (neg_lt_neg hlen).trans hx.2.1, hx.2.2.trans hlen⟩
  obtain ⟨F, _, _, heval, _, _, _⟩ := nk.map.exists_diffeomorph_family_extension
    (IP := 𝓘(ℝ)) (fun _ : ℝ => D) (D.contMDiff.comp contMDiff_snd)
    (D.symm.contMDiff.comp contMDiff_snd) hK hKs (fun _ z hz => hfix hz)
  refine ⟨F 0, ?_⟩
  intro q
  have hsrc : (q, (0 : ℝ)) ∈ nk.map.source :=
    nk.domain ⟨mem_univ _, by constructor <;> linarith⟩
  rw [(heval 0 (nk.map (q, 0))).1]
  change (if nk.map (q, 0) ∈ nk.map.target then
    nk.map (D (nk.map.symm (nk.map (q, 0)))) else nk.map (q, 0)) = _
  rw [if_pos (nk.map.map_source hsrc)]
  have hinv := nk.map.left_inv hsrc
  change nk.map.symm (nk.map (q, 0)) = (q, 0) at hinv
  rw [hinv]
  have he := hD q 0 (by norm_num)
  simpa only [zero_add, add_zero] using congrArg nk.map he




private theorem SpatialNeck.isConnected_slab
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    {a b : ℝ} (ha : -eps⁻¹ < a) (hb : b < eps⁻¹) (hab : a ≤ b) :
    IsConnected (nk.map '' (univ ×ˢ Icc a b)) := by
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  apply (isConnected_univ.prod (isConnected_Icc hab)).image nk.map
  apply nk.map.contMDiffOn_toFun.continuousOn.mono
  intro z hz
  exact nk.domain ⟨hz.1, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩

private theorem SpatialNeck.compact_side_shrink_of_positive_graph
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p)
    (d : SphereSides (range (fun q : Sphere 2 => nk.map (q, 0))))
    (hin : ∀ q t, 0 < t → t < 2 → nk.map (q, t) ∈ d.compactSide)
    (h : Sphere 2 → ℝ) (hh : ContMDiff I2 𝓘(ℝ) ∞ h)
    (hb : ∀ q, (1 / 2 : ℝ) < h q ∧ h q < 3 / 2) :
    ∃ d' : SphereSides (range (fun q : Sphere 2 => nk.map (q, h q))),
      closure d'.compactSide ⊆ d.compactSide ∧
      Disjoint (closure d'.compactSide)
        (nk.map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2))) := by
  obtain ⟨F, hF⟩ := nk.exists_diffeomorph_center_eq_graph h hh hb
  have himage : F '' range (fun q : Sphere 2 => nk.map (q, 0)) =
      range (fun q : Sphere 2 => nk.map (q, h q)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, (hF q).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨nk.map (q, 0), ⟨q, rfl⟩, hF q⟩
  let d' : SphereSides (range (fun q : Sphere 2 => nk.map (q, h q))) :=
    himage ▸ d.imageDiffeomorph F
  have hlen : (2 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
    (by linarith [nk.eps_small])
  have hsrc (q : Sphere 2) (t : ℝ) (ht : t ∈ Icc (-2 : ℝ) 2) : (q, t) ∈ nk.map.source :=
    nk.domain ⟨mem_univ _, (neg_lt_neg hlen).trans_le ht.1, ht.2.trans_lt hlen⟩
  have hgraph (q : Sphere 2) : (q, h q) ∈ nk.map.source :=
    hsrc q (h q) ⟨by linarith [(hb q).1], by linarith [(hb q).2]⟩
  have hdisj : Disjoint (range (fun q : Sphere 2 => nk.map (q, 0)))
      (range (fun q : Sphere 2 => nk.map (q, h q))) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨q, rfl⟩ ⟨r, hr⟩
    have he := nk.map.injOn (hgraph r) (hsrc q 0 (by norm_num)) hr
    have hz := congrArg Prod.snd he
    linarith [(hb r).1]
  have hconn : IsConnected (range (fun q : Sphere 2 => nk.map (q, h q))) := by
    let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
        (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
    apply isConnected_range
    exact nk.map.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_id.prodMk hh.continuous) hgraph
  have hsub := d.closure_compactSide_subset_of_sphere_subset d' hdisj hconn
    (by rintro x ⟨q, rfl⟩; exact hin q (h q) (by linarith [(hb q).1]) (by linarith [(hb q).2]))
  let B := nk.map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2))
  have hBconn : IsConnected B := nk.isConnected_slab (by linarith) (by linarith) (by norm_num)
  have hBavoid : B ⊆ (range (fun q : Sphere 2 => nk.map (q, h q)))ᶜ := by
    rintro x ⟨z, hz, rfl⟩ ⟨q, hq⟩
    have he := nk.map.injOn (hgraph q)
      (hsrc z.1 z.2 ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩) hq
    have hheight := congrArg Prod.snd he
    linarith [(hb q).1, hz.2.2]
  have hBE : B ⊆ d'.endSide := by
    rcases d'.subset_compactSide_or_subset_endSide hBconn.isPreconnected hBavoid with hC | hE
    · exfalso
      have hpB : p ∈ B := ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, nk.center_eq⟩
      have hpS : p ∈ range (fun q : Sphere 2 => nk.map (q, 0)) := ⟨nk.center, nk.center_eq⟩
      exact d.compactSide_disjoint_sphere.le_bot ⟨hsub (subset_closure (hC hpB)), hpS⟩
    · exact hE
  refine ⟨d', hsub, ?_⟩
  rw [d'.closure_compactSide_eq_compl]
  exact disjoint_compl_left.mono_right hBE

private theorem SpatialNeck.local_sides_of_two
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p) :
    let S := range (fun q : Sphere 2 => nk.map (q, 0))
    let O := nk.map '' (univ ×ˢ Ioo (-2 : ℝ) 2)
    let N := nk.map '' (univ ×ˢ Ioo (-2 : ℝ) 0)
    let P := nk.map '' (univ ×ˢ Ioo (0 : ℝ) 2)
    IsOpen O ∧ S ⊆ O ∧ IsConnected N ∧ IsConnected P ∧ O \ S = N ∪ P := by
  have hlen : (2 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
    (by linarith [nk.eps_small])
  have hsrc : (univ ×ˢ Ioo (-2 : ℝ) 2 : Set Cylinder) ⊆ nk.map.source := by
    intro z hz
    exact nk.domain ⟨hz.1, (neg_lt_neg hlen).trans hz.2.1, hz.2.2.trans hlen⟩
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hc {a b : ℝ} (hab : a < b) (ha : -2 ≤ a) (hb : b ≤ 2) :
      IsConnected (nk.map '' (univ ×ˢ Ioo a b)) := by
    apply (isConnected_univ.prod (isConnected_Ioo hab)).image nk.map
    apply nk.map.contMDiffOn_toFun.continuousOn.mono
    intro z hz
    exact hsrc ⟨hz.1, ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩
  refine ⟨nk.map.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_univ.prod isOpen_Ioo) hsrc, ?_, hc (by norm_num) le_rfl (by norm_num),
    hc (by norm_num) (by norm_num) le_rfl, ?_⟩
  · rintro x ⟨q, rfl⟩
    exact ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  · ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hnot⟩
      have hne : z.2 ≠ 0 := by intro he; exact hnot ⟨z.1, by rw [← he]⟩
      rcases lt_or_gt_of_ne hne with hn | hp
      · exact Or.inl ⟨z, ⟨hz.1, hz.2.1, hn⟩, rfl⟩
      · exact Or.inr ⟨z, ⟨hz.1, hp, hz.2.2⟩, rfl⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · have hzs : z ∈ univ ×ˢ Ioo (-2 : ℝ) 2 := ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
        refine ⟨⟨z, hzs, rfl⟩, ?_⟩
        rintro ⟨q, hq⟩
        have he := nk.map.injOn (hsrc ⟨mem_univ _, by norm_num⟩) (hsrc hzs) hq
        have hh := congrArg Prod.snd he
        linarith [hz.2.2]
      · have hzs : z ∈ univ ×ˢ Ioo (-2 : ℝ) 2 := ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
        refine ⟨⟨z, hzs, rfl⟩, ?_⟩
        rintro ⟨q, hq⟩
        have he := nk.map.injOn (hsrc ⟨mem_univ _, by norm_num⟩) (hsrc hzs) hq
        have hh := congrArg Prod.snd he
        linarith [hz.2.1]

private theorem SpatialNeck.exists_orientation_into_compact_side
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    (d : SphereSides (range (fun q : Sphere 2 => nk.map (q, 0)))) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ q t, 0 < t → t < 2 → nk.map (q, σ * t) ∈ d.compactSide := by
  obtain ⟨hO, hSO, hN, hP, hparts⟩ := nk.local_sides_of_two
  let N := nk.map '' (univ ×ˢ Ioo (-2 : ℝ) 0)
  let P := nk.map '' (univ ×ˢ Ioo (0 : ℝ) 2)
  have hsubN : N ⊆ (range (fun q : Sphere 2 => nk.map (q, 0)))ᶜ := by
    intro x hx
    have hh : x ∈ nk.map '' (univ ×ˢ Ioo (-2 : ℝ) 0) ∪
        nk.map '' (univ ×ˢ Ioo (0 : ℝ) 2) := Or.inl hx
    rw [← hparts] at hh
    exact hh.2
  have hsubP : P ⊆ (range (fun q : Sphere 2 => nk.map (q, 0)))ᶜ := by
    intro x hx
    have hh : x ∈ nk.map '' (univ ×ˢ Ioo (-2 : ℝ) 0) ∪
        nk.map '' (univ ×ˢ Ioo (0 : ℝ) 2) := Or.inr hx
    rw [← hparts] at hh
    exact hh.2
  rcases d.subset_compactSide_or_subset_endSide hP.isPreconnected hsubP with hpc | hpe
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro q t ht htwo
    simp only [one_mul]
    exact hpc ⟨(q, t), ⟨mem_univ _, ht, htwo⟩, rfl⟩
  · have hnc : N ⊆ d.compactSide := by
      rcases d.subset_compactSide_or_subset_endSide hN.isPreconnected hsubN with hnc | hne
      · exact hnc
      · exfalso
        have hpS : p ∈ range (fun q : Sphere 2 => nk.map (q, 0)) := ⟨nk.center, nk.center_eq⟩
        have hpcl : p ∈ closure d.compactSide := d.closure_compactSide.symm ▸ Or.inr hpS
        obtain ⟨x, hxO, hxc⟩ := mem_closure_iff.mp hpcl _ hO (hSO hpS)
        have hxparts := hparts ▸ (show x ∈ _ \ range (fun q : Sphere 2 => nk.map (q, 0)) from
          ⟨hxO, d.compactSide_subset_compl hxc⟩)
        exact d.disjoint.le_bot ⟨hxc, hxparts.elim (fun h => hne h) (fun h => hpe h)⟩
    refine ⟨-1, Or.inr rfl, ?_⟩
    intro q t ht htwo
    simp only [neg_one_mul]
    exact hnc ⟨(q, -t), ⟨mem_univ _, by constructor <;> linarith⟩, rfl⟩

private theorem compactSide_cast
    {X : Type*} [TopologicalSpace X] {S T : Set X} (h : S = T) (d : SphereSides S) :
    (h ▸ d).compactSide = d.compactSide := by
  cases h
  rfl

private theorem reflection_center_range
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p) :
    range (fun q : Sphere 2 => nk.axialReflection.map (q, 0)) =
      range (fun q : Sphere 2 => nk.map (q, 0)) := by
  simp only [SpatialNeck.axialReflection_apply, neg_zero]

private theorem reflection_half_slab
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p) :
    nk.axialReflection.map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) =
      nk.map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) := by
  ext x
  constructor
  · rintro ⟨⟨q,t⟩, ht, rfl⟩
    exact ⟨(q,-t), ⟨mem_univ _, by constructor <;> linarith [ht.2.1,ht.2.2]⟩, rfl⟩
  · rintro ⟨⟨q,t⟩, ht, rfl⟩
    refine ⟨(q,-t), ⟨mem_univ _, by constructor <;> linarith [ht.2.1,ht.2.2]⟩, ?_⟩
    simp only [SpatialNeck.axialReflection_apply, neg_neg]


private theorem exists_spatial_neck_compact_side_step_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p : M) (nk : SpatialNeck g eps p)
          (d : SphereSides (range (fun q : Sphere 2 => nk.map (q, 0)))),
          (∀ x ∈ d.compactSide, Nonempty (SpatialNeck g eps x)) →
          ∃ p' : M, p' ∈ d.compactSide ∧ ∃ nk' : SpatialNeck g eps p',
            ∃ d' : SphereSides (range (fun q : Sphere 2 => nk'.map (q, 0))),
              closure d'.compactSide ⊆ d.compactSide ∧
              Disjoint (closure d'.compactSide)
                (nk.map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2))) := by
  obtain ⟨eta, heta, hstep⟩ := exists_spatial_neck_frontier_step_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p nk d hnecks
  have hpos (nk₀ : SpatialNeck g eps p)
      (hcenter : range (fun q : Sphere 2 => nk₀.map (q, 0)) =
        range (fun q : Sphere 2 => nk.map (q, 0)))
      (hslab : nk₀.map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) =
        nk.map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)))
      (hin : ∀ q t, 0 < t → t < 2 → nk₀.map (q,t) ∈ d.compactSide) :
      ∃ p' : M, p' ∈ d.compactSide ∧ ∃ nk' : SpatialNeck g eps p',
        ∃ d' : SphereSides (range (fun q : Sphere 2 => nk'.map (q, 0))),
          closure d'.compactSide ⊆ d.compactSide ∧
          Disjoint (closure d'.compactSide)
            (nk.map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2))) := by
    let p' := nk₀.map (nk₀.center, 1)
    have hp' : p' ∈ d.compactSide := hin _ _ (by norm_num) (by norm_num)
    obtain ⟨nk'⟩ := hnecks p' hp'
    obtain ⟨η,h,hh,hb,_,heq⟩ := hstep eps heps M g p p' nk₀ nk' nk₀.center rfl
    let d₀ : SphereSides (range (fun q : Sphere 2 => nk₀.map (q,0))) := hcenter.symm ▸ d
    have hd₀ : d₀.compactSide = d.compactSide := by
      exact compactSide_cast hcenter.symm d
    have hin₀ : ∀ q t, 0 < t → t < 2 → nk₀.map (q,t) ∈ d₀.compactSide := by
      intro q t ht ht2
      rw [hd₀]
      exact hin q t ht ht2
    obtain ⟨d₁, hsub, hdisj⟩ := nk₀.compact_side_shrink_of_positive_graph d₀ hin₀ h hh hb
    have hsphere : range (fun q : Sphere 2 => nk₀.map (q,h q)) =
        range (fun q : Sphere 2 => nk'.map (q,0)) := by
      ext x
      constructor
      · rintro ⟨q,rfl⟩
        exact ⟨η q,(heq q).symm⟩
      · rintro ⟨q,rfl⟩
        obtain ⟨r,rfl⟩ := η.surjective q
        exact ⟨r,heq r⟩
    let d₂ : SphereSides (range (fun q : Sphere 2 => nk'.map (q, 0))) := hsphere ▸ d₁
    have hd₂ : d₂.compactSide = d₁.compactSide := compactSide_cast hsphere d₁
    refine ⟨p',hp',nk',d₂,?_,?_⟩
    · rw [hd₂]
      simpa only [hd₀] using hsub
    · rw [hd₂]
      simpa only [hslab] using hdisj
  obtain ⟨σ,hσ,hin⟩ := nk.exists_orientation_into_compact_side d
  rcases hσ with rfl | rfl
  · exact hpos nk rfl rfl (by simpa only [one_mul] using hin)
  · exact hpos nk.axialReflection (reflection_center_range nk) (reflection_half_slab nk)
      (by simpa only [SpatialNeck.axialReflection_apply, neg_one_mul] using hin)

private theorem not_infinite_uniformly_separated_in_totallyBounded
    {X : Type*} [PseudoEMetricSpace X] {K : Set X} (hK : TotallyBounded K)
    (p : ℕ → X) (hp : ∀ n, p n ∈ K) {r : ℝ≥0} (hr : 0 < r)
    (hsep : ∀ i j : ℕ, i ≠ j → (r : ℝ≥0∞) ≤ edist (p i) (p j)) : False := by
  classical
  obtain ⟨T, _, hT, hcover⟩ := Metric.exists_finite_isCover_of_totallyBounded
    (show r / 4 ≠ 0 by positivity) hK
  let f : ℕ → T := fun n => ⟨(hcover (hp n)).choose, (hcover (hp n)).choose_spec.1⟩
  have hf (n : ℕ) : edist (p n) (f n) ≤ (r / 4 : ℝ≥0) :=
    (hcover (hp n)).choose_spec.2
  let : Finite T := hT.to_subtype
  obtain ⟨i,j,hij,heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hdist : edist (p i) (p j) ≤ (r / 4 : ℝ≥0) + (r / 4 : ℝ≥0) := by
    apply (edist_triangle (p i) (f i) (p j)).trans
    rw [heq, edist_comm (f j : X) (p j)]
    exact add_le_add (by simpa only [heq] using hf i) (hf j)
  have hsmall : ((r / 4 : ℝ≥0) : ℝ≥0∞) + (r / 4 : ℝ≥0) < (r : ℝ≥0∞) := by
    rw [← ENNReal.coe_add]
    exact_mod_cast (show r / 4 + r / 4 < r by
      have hrR : (0 : ℝ) < r := hr
      change (r : ℝ) / 4 + (r : ℝ) / 4 < r
      linarith)
  exact (not_lt_of_ge (hsep i j hij)) (hdist.trans_lt hsmall)

private theorem exists_half_slab_avoiding_sequence
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M) {eps : ℝ}
    (hstep : ∀ p : M, ∀ nk : SpatialNeck g eps p,
      ∀ d : SphereSides (range (fun q : Sphere 2 => nk.map (q,0))),
      (∀ x ∈ d.compactSide, Nonempty (SpatialNeck g eps x)) →
      ∃ p' ∈ d.compactSide, ∃ nk' : SpatialNeck g eps p',
        ∃ d' : SphereSides (range (fun q : Sphere 2 => nk'.map (q,0))),
          closure d'.compactSide ⊆ d.compactSide ∧ Disjoint (closure d'.compactSide)
            (nk.map '' (univ ×ˢ Icc (-1/2 : ℝ) (1/2))))
    (p₀ : M) (nk₀ : SpatialNeck g eps p₀)
    (d₀ : SphereSides (range (fun q : Sphere 2 => nk₀.map (q,0))))
    (hnecks : ∀ x ∈ d₀.compactSide, Nonempty (SpatialNeck g eps x)) :
    ∃ p : ℕ → M, ∃ neck : ∀ n, SpatialNeck g eps (p n),
      (∀ n, p n ∈ closure d₀.compactSide) ∧
      ∀ i j : ℕ, i<j → p j ∉ (neck i).map '' (univ ×ˢ Icc (-1/2 : ℝ) (1/2)) := by
  classical
  let State := Σ (p : M) (nk : SpatialNeck g eps p),
    {d : SphereSides (range (fun q : Sphere 2 => nk.map (q, 0))) // d.compactSide ⊆ d₀.compactSide}
  let center (s : State) : M := s.1
  let neck (s : State) : SpatialNeck g eps (center s) := s.2.1
  let side (s : State) : Set M := s.2.2.1.compactSide
  have hchoose (s : State) : ∃ s' : State,
      closure (side s') ⊆ side s ∧
      Disjoint (closure (side s')) ((neck s).map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2))) := by
    obtain ⟨p, hp, nk, d, hsub, hdisj⟩ := hstep s.1 s.2.1 s.2.2.1
      (fun x hx => hnecks x (s.2.2.2 hx))
    exact ⟨⟨p,nk,d,subset_closure.trans (hsub.trans s.2.2.2)⟩,hsub,hdisj⟩
  let next (s : State) : State := (hchoose s).choose
  have hnext (s : State) : closure (side (next s)) ⊆ side s ∧
      Disjoint (closure (side (next s)))
        ((neck s).map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2))) := (hchoose s).choose_spec
  let seq : ℕ → State := fun n => (next^[n]) ⟨p₀,nk₀,d₀,subset_rfl⟩
  have hsucc (n : ℕ) : seq (n+1) = next (seq n) := Function.iterate_succ_apply' next n _
  have hnest (n : ℕ) : closure (side (seq (n+1))) ⊆ side (seq n) := by
    rw [hsucc]
    exact (hnext (seq n)).1
  have hdisj (n : ℕ) : Disjoint (closure (side (seq (n+1))))
      ((neck (seq n)).map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2))) := by
    rw [hsucc]
    exact (hnext (seq n)).2
  have hanti : Antitone (fun n => closure (side (seq n))) := by
    apply antitone_nat_of_succ_le
    intro n
    exact (hnest n).trans subset_closure
  have hcenter (s : State) : center s ∈ closure (side s) := by
    change s.1 ∈ closure s.2.2.1.compactSide
    rw [s.2.2.1.closure_compactSide]
    exact Or.inr ⟨s.2.1.center,s.2.1.center_eq⟩
  have hK (n : ℕ) : center (seq n) ∈ closure d₀.compactSide :=
    closure_mono (seq n).2.2.2 (hcenter (seq n))
  refine ⟨fun n => center (seq n), fun n => neck (seq n), hK, ?_⟩
  intro i j hij hj
  exact Set.disjoint_left.mp (hdisj i)
    (hanti (Nat.succ_le_of_lt hij) (hcenter (seq j))) hj

private theorem mem_slab_of_edist_lt
    {M : Type*} [EMetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    {eps : ℝ} {p x : M} (nk : SpatialNeck g eps p) {r b : ℝ}
    (hr : 0 < r) (hreps : r < eps⁻¹) (hb : 0 < b)
    (hscale : Real.sqrt (metricScalarAt g p) ≤ b)
    (hd : edist p x < ENNReal.ofReal (r / (4 * b))) :
    x ∈ nk.map '' (univ ×ˢ Icc (-r) r) := by
  have hcap := nk.ball_subset_closed_slab hr hreps
  have hball : x ∈ riemannianBallOf
      (scaleMetric (metricScalarAt g p) nk.Q_pos g) p (r / 2) := by
    change riemannianEDistOf _ p x < _
    rw [edistOf_scale, ← hmetric]
    calc
      _ ≤ ENNReal.ofReal b * ENNReal.ofReal (r / (4 * b)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hscale) hd.le
      _ = ENNReal.ofReal (r / 4) := by
        rw [← ENNReal.ofReal_mul hb.le]
        congr 1
        field_simp
      _ < ENNReal.ofReal (r / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  exact hcap hball

open scoped Bundle in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem not_slab_avoiding_sequence_in_compact
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] (g : SmoothRiemannianMetric I3 M) {eps : ℝ} {K : Set M} (hK : IsCompact K)
    (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n)) (hp : ∀ n, p n ∈ K)
    (r : ℝ) (hr : 0 < r) (hreps : r < eps⁻¹)
    (havoid : ∀ i j : ℕ, i < j → p j ∉ (neck i).map '' (univ ×ˢ Icc (-r) r)) : False := by
  let : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  let : T3Space M := inferInstance
  let : Bundle.RiemannianBundle (fun x : M => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : M => TangentSpace I3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I3 M
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (Real.continuous_sqrt.comp (metricScalar_smooth g).continuous).continuousOn
  let b : ℝ := max B 1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let delta : ℝ≥0 := ⟨r / (4 * b), by positivity⟩
  have hdelta : 0 < delta := by change (0 : ℝ) < r / (4 * b); positivity
  have hlt (i j : ℕ) (hij : i < j) : (delta : ℝ≥0∞) ≤ edist (p i) (p j) := by
    apply le_of_not_gt
    intro hd
    have hd' : edist (p i) (p j) < ENNReal.ofReal (r / (4 * b)) := by
      rw [← ENNReal.ofReal_coe_nnreal] at hd
      exact hd
    exact havoid i j hij (mem_slab_of_edist_lt g (fun _ _ => rfl) (neck i) hr hreps hb
      ((hB ⟨p i, hp i, rfl⟩).trans (le_max_left _ _)) hd')
  have hsep (i j : ℕ) (hij : i ≠ j) : (delta : ℝ≥0∞) ≤ edist (p i) (p j) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlt i j h
    · simpa only [edist_comm] using hlt j i h
  exact not_infinite_uniformly_separated_in_totallyBounded hK.totallyBounded p hp hdelta hsep

private theorem not_half_slab_avoiding_sequence_in_compact
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] (g : SmoothRiemannianMetric I3 M) {eps : ℝ} {K : Set M} (hK : IsCompact K)
    (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n)) (hp : ∀ n, p n ∈ K)
    (havoid : ∀ i j : ℕ, i < j →
      p j ∉ (neck i).map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2))) : False := by
  have hlen : (1 / 2 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) (neck 0).eps_pos).mpr (by linarith [(neck 0).eps_small])
  apply not_slab_avoiding_sequence_in_compact g hK p neck hp (1 / 2) (by norm_num) hlen
  simpa only [neg_div] using havoid


theorem exists_spatial_neck_compact_side_exclusion_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p : M) (nk : SpatialNeck g eps p)
          (d : SphereSides (range (fun q : Sphere 2 => nk.map (q, 0)))),
          ¬ ∀ x ∈ d.compactSide, Nonempty (SpatialNeck g eps x) := by
  obtain ⟨eta, heta, hstep⟩ := exists_spatial_neck_compact_side_step_tolerance
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p nk d hnecks
  obtain ⟨p,neck,hp,havoid⟩ :=
    exists_half_slab_avoiding_sequence g (hstep eps heps M g) p nk d hnecks
  exact not_half_slab_avoiding_sequence_in_compact g
    d.isCompact_closure_compactSide p neck hp havoid

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] (g : SmoothRiemannianMetric I3 M) {eps : ℝ} {K : Set M}
  (hK : IsCompact K) (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
  (hp : ∀ n, p n ∈ K)

include hK hp

theorem exists_spatial_neck_slab_return_in_compact (r : ℝ) (hr : 0 < r) (hreps : r < eps⁻¹) :
    ∃ i j : ℕ, i < j ∧ p j ∈ (neck i).map '' (univ ×ˢ Icc (-r) r) := by
  by_contra h
  apply not_slab_avoiding_sequence_in_compact g hK p neck hp r hr hreps
  intro i j hij hj
  exact h ⟨i, j, hij, hj⟩

theorem exists_spatial_neck_half_slab_return_in_compact :
    ∃ i j : ℕ, i < j ∧
      p j ∈ (neck i).map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) := by
  have hlen : (1 / 2 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) (neck 0).eps_pos).mpr (by linarith [(neck 0).eps_small])
  simpa only [neg_div] using
    exists_spatial_neck_slab_return_in_compact g hK p neck hp (1 / 2) (by norm_num) hlen

theorem exists_spatial_neck_first_half_slab_return_in_compact :
    ∃ i j : ℕ, i < j ∧
      p j ∈ (neck i).map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) ∧
      ∀ k l : ℕ, k < l → l < j →
        p l ∉ (neck k).map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) := by
  classical
  have hreturn : ∃ j : ℕ, ∃ i : ℕ, i < j ∧
      p j ∈ (neck i).map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) := by
    obtain ⟨i, j, hij, hj⟩ := exists_spatial_neck_half_slab_return_in_compact g hK p neck hp
    exact ⟨j, i, hij, hj⟩
  obtain ⟨i, hij, hj⟩ := Nat.find_spec hreturn
  refine ⟨i, Nat.find hreturn, hij, hj, ?_⟩
  intro k l hkl hlj hl
  exact Nat.find_min hreturn hlj ⟨k, hkl, hl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
