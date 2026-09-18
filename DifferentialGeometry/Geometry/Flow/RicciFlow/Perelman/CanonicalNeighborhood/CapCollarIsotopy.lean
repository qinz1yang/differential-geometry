import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCollarDepth
import DifferentialGeometry.Topology.Manifold.CollarReparametrization
import DifferentialGeometry.Topology.Compactness.ProductChartThickening

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {eps t : ℝ} {x : M} {U : Set M}

theorem LocalCap.exists_isotopy_image_tube_strip
    (cap : LocalCap S eps x t U) :
    ∃ d : ℝ, 0 < d ∧ d < 1 ∧ ∃ F : ℝ → M ≃ₘ⟮I3, I3⟯ M,
      ContMDiff (𝓘(ℝ).prod I3) I3 ∞ (fun q : ℝ × M => F q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod I3) I3 ∞ (fun q : ℝ × M => (F q.1).symm q.2) ∧
      F 0 = Diffeomorph.refl I3 M ∞ ∧
      (∀ s, F s x = x ∧ (F s).symm x = x) ∧
      (∀ s, F s '' U = U ∧ (F s).symm '' U = U) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        F s '' cap.tube = cap.tube_map '' (univ ×ˢ Icc (s * d) 1)) ∧
      ∃ K : Set M, IsCompact K ∧ K ⊆ interior U \ {x} ∧
        ∀ s, EqOn (F s) id Kᶜ ∧ EqOn (F s).symm id Kᶜ := by
  have hsource : univ ×ˢ Icc (0 : ℝ) 0 ⊆ cap.tube_map.source := by
    intro z hz
    exact cap.tube_domain ⟨hz.1, hz.2.1, hz.2.2.trans zero_le_one⟩
  have hband : cap.tube_map '' (univ ×ˢ Icc (0 : ℝ) 0) ⊆ interior U \ {x} := by
    rintro y ⟨⟨z, a⟩, ha, rfl⟩
    have ha0 : a = 0 := le_antisymm ha.2.2 ha.2.1
    subst a
    have hfront : cap.tube_map (z, 0) ∈ frontier cap.core.carrier :=
      cap.inner_boundary ▸ ⟨(z, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    refine ⟨cap.core_inside (cap.core.compact.isClosed.frontier_subset hfront), ?_⟩
    intro heq
    have heq' : cap.tube_map (z, 0) = x := heq
    rw [heq'] at hfront
    exact hfront.2 cap.center_inside
  obtain ⟨l, u, hl, hu, hsrc, himg⟩ :=
    DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_band
      cap.tube_map.toOpenPartialHomeomorph le_rfl hsource
      (isOpen_interior.sdiff isClosed_singleton) hband
  let b := min u (1 / 2 : ℝ)
  have hb : 0 < b := lt_min hu (by norm_num)
  have hbu : b ≤ u := min_le_left _ _
  have hb1 : b < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let d := b / 2
  have hd : 0 < d := half_pos hb
  have hdb : d < b := half_lt_self hb
  have hsub : (univ : Set (Sphere 2)) ×ˢ Ioo l b ⊆ univ ×ˢ Ioo l u :=
    Set.prod_mono (subset_refl _) (Ioo_subset_Ioo le_rfl hbu)
  obtain ⟨φ, _, _, _, hmove, hpos, hfix, F, hF, hFi, hF0, htrack, _, K, hK, hKU, hFfix⟩ :=
    cap.tube_map.exists_collar_reparametrization_isotopy ⟨hl, hb⟩
      ⟨hl.trans hd, hdb⟩ (hsub.trans hsrc)
  have hKO : K ⊆ interior U \ {x} := hKU.trans ((Set.image_mono hsub).trans himg)
  have hxK : x ∉ K := fun hx => (hKO hx).2 (mem_singleton x)
  have hKU' : K ⊆ U := fun y hy => interior_subset (hKO hy).1
  refine ⟨d, hd, hdb.trans hb1, F, hF, hFi, hF0, ?_, ?_, ?_, K, hK, hKO, hFfix⟩
  · intro s
    exact ⟨(hFfix s).1 hxK, (hFfix s).2 hxK⟩
  · intro s
    have hfixU := (hFfix s).1.mono (compl_subset_compl.mpr hKU')
    have hfixUi := (hFfix s).2.mono (compl_subset_compl.mpr hKU')
    constructor
    · apply compl_injective
      exact ((F s).toEquiv.image_compl U).symm.trans hfixU.image_eq_self
    · apply compl_injective
      exact ((F s).symm.toEquiv.image_compl U).symm.trans hfixUi.image_eq_self
  · intro s hs
    have hzero : φ s 0 = s * d := by
      simpa only [sub_zero, zero_add] using hmove s hs
    have hone : φ s 1 = 1 := (hfix s).1 (by
      intro h
      exact (not_lt_of_ge hb1.le) h.2)
    have hinterval : φ s '' Icc (0 : ℝ) 1 = Icc (s * d) 1 := by
      rw [(φ s).continuous.image_Icc_of_strictMono (strictMono_of_deriv_pos (hpos s)), hzero, hone]
    calc
      F s '' cap.tube =
          cap.tube_map '' ((Prod.map id (φ s)) '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
        rw [← cap.tube_eq, image_image, image_image]
        exact image_congr fun z hz => htrack s z (cap.tube_domain hz)
      _ = cap.tube_map '' (univ ×ˢ Icc (s * d) 1) := by
        rw [prodMap_image_prod, image_id, hinterval]

theorem LocalCap.exists_isotopy_with_strict_tube_depth [PreconnectedSpace M]
    (cap : LocalCap S eps x t U) (g : SmoothRiemannianMetric I3 M) {r : ℝ}
    (hdepth : ∀ y ∈ frontier cap.core.carrier, r ≤ metricDistance g x y) :
    ∃ F : ℝ → M ≃ₘ⟮I3, I3⟯ M,
      ContMDiff (𝓘(ℝ).prod I3) I3 ∞ (fun q : ℝ × M => F q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod I3) I3 ∞ (fun q : ℝ × M => (F q.1).symm q.2) ∧
      F 0 = Diffeomorph.refl I3 M ∞ ∧
      (∀ s, F s x = x ∧ (F s).symm x = x) ∧
      (∀ s, F s '' U = U ∧ (F s).symm '' U = U) ∧
      (∀ s ∈ Ioc (0 : ℝ) 1, ∃ r' : ℝ, r < r' ∧
        ∀ y ∈ F s '' cap.tube, r' ≤ metricDistance g x y) ∧
      ∃ K : Set M, IsCompact K ∧ K ⊆ interior U \ {x} ∧
        ∀ s, EqOn (F s) id Kᶜ ∧ EqOn (F s).symm id Kᶜ := by
  obtain ⟨d, hd, hd1, F, hF, hFi, hF0, hFx, hFU, htube, hsupport⟩ :=
    cap.exists_isotopy_image_tube_strip
  refine ⟨F, hF, hFi, hF0, hFx, hFU, ?_, hsupport⟩
  intro s hs
  rw [htube s ⟨hs.1.le, hs.2⟩]
  exact cap.exists_uniform_depth_on_tube_strip g hdepth (mul_pos hs.1 hd)
    ((mul_le_mul_of_nonneg_right hs.2 hd.le).trans (by simpa only [one_mul] using hd1.le))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
