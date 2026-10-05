import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingPath
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckArmNoReturn
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckHeightDistance

section
set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps : ℝ} {x : M} {t : ℝ}

theorem StrongNeck.exists_arm_slice_crossing
    (neck : StrongNeck S eps x t) (a : MinimizingArm (S.base.metric t) x)
    {s h : ℝ} (hs : s ∈ Ioc 0 a.length) (hh : h ≠ 0)
    (himage : ∀ v ∈ Icc 0 s, a.point v ∈ neck.map.target)
    (hbetween : h ∈ uIcc 0 (neck.map.symm (a.point s)).2) :
    ∃ s' ∈ Ioc 0 s, ∃ p : Sphere 2, a.point s' = neck.map (p, h) := by
  have hgamma : ContinuousOn (fun v => (neck.map.symm (a.point v)).2) (Icc 0 s) :=
    continuous_snd.continuousOn.comp
      (neck.map.symm.contMDiffOn_toFun.continuousOn.comp
        (a.continuousOn_point.mono (Icc_subset_Icc le_rfl hs.2)) himage)
      (mapsTo_univ _ _)
  have hzero : (neck.map.symm (a.point 0)).2 = 0 := by
    have hcenter : (neck.center, (0 : ℝ)) ∈ neck.map.source :=
      neck.domain ⟨mem_univ _, by constructor <;> linarith [inv_pos.mpr neck.eps_pos]⟩
    have heq : a.point 0 = neck.map (neck.center, 0) := a.start.trans neck.center_eq.symm
    exact (congrArg (fun q => (neck.map.symm q).2) heq).trans
      (congrArg Prod.snd (neck.map.left_inv' hcenter))
  have hex : h ∈ (fun v => (neck.map.symm (a.point v)).2) '' Icc 0 s := by
    rcases le_total 0 (neck.map.symm (a.point s)).2 with he | he
    · apply intermediate_value_Icc hs.1.le hgamma
      rw [hzero]
      simpa only [uIcc_of_le he] using hbetween
    · apply intermediate_value_Icc' hs.1.le hgamma
      rw [hzero]
      simpa only [uIcc_of_ge he] using hbetween
  obtain ⟨s', hs', heq⟩ := hex
  have hs'pos : 0 < s' := by
    by_contra hnot
    have heq0 : s' = 0 := le_antisymm (le_of_not_gt hnot) hs'.1
    exact hh (heq.symm.trans (by simpa only [heq0] using hzero))
  refine ⟨s', ⟨hs'pos, hs'.2⟩, (neck.map.symm (a.point s')).1, ?_⟩
  have hpair : ((neck.map.symm (a.point s')).1, h) = neck.map.symm (a.point s') :=
    Prod.ext rfl heq.symm
  rw [hpair]
  exact (neck.map.right_inv' (himage s' hs')).symm



end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end

section
noncomputable section
open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]

theorem MinimizingArm.not_mem_centralSphere_of_scaled_radius
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {eps : ℝ} {x : M} {t : ℝ}
    (a : MinimizingArm (S.base.metric t) x) (nk : StrongNeck S eps x t)
    {s : ℝ} (hfar : 17 ≤ Real.sqrt (S.scalar t x) * s) :
    ∀ w ∈ Icc s a.length, a.point w ∉ nk.map '' (univ ×ˢ ({0} : Set ℝ)) := by
  have hQ : 0 < Real.sqrt (S.scalar t x) := Real.sqrt_pos.mpr nk.Q_pos
  have hs : 0 < s := (mul_pos_iff_of_pos_left hQ).mp (lt_of_lt_of_le (by norm_num) hfar)
  intro w hw hmem
  have hw0 : w ∈ Icc (0 : ℝ) a.length := ⟨hs.le.trans hw.1, hw.2⟩
  have hregion : a.point w ∈ nk.region := by
    obtain ⟨z, hz, hzw⟩ := hmem
    refine ⟨z, ⟨hz.1, ?_⟩, hzw⟩
    have hz0 : z.2 = 0 := hz.2
    rw [hz0]
    norm_num
  have hball := nk.region_subset_ball hregion
  change riemannianEDistOf (S.base.metric t) x (a.point w) <
    ENNReal.ofReal (17 / Real.sqrt (S.scalar t x)) at hball
  rw [a.edistOf_start hw0] at hball
  have hwlt : w < 17 / Real.sqrt (S.scalar t x) :=
    (ENNReal.ofReal_lt_ofReal_iff (div_pos (by norm_num) hQ)).mp hball
  have hh := (lt_div_iff₀ hQ).mp hwlt
  have hmono := mul_le_mul_of_nonneg_left hw.1 hQ.le
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end

section
noncomputable section
open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem MinimizingArm.not_mem_centralSphere_of_height_reserve
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {eps : ℝ} {x : M} {t : ℝ}
    (a : MinimizingArm (S.base.metric t) x) (nk : StrongNeck S eps x t)
    {R : ℝ} (hR : 0 < R) (hreserve : 17 ≤ Real.sqrt (1 - eps) * R)
    {s : ℝ} (hs : s ∈ Icc 0 a.length)
    {p : Sphere 2} {l : ℝ} (hpoint : a.point s = nk.map (p, l))
    (hheight : R < |l|) (hinside : |l| < eps⁻¹) :
    ∀ w ∈ Icc s a.length, a.point w ∉ nk.map '' (univ ×ˢ ({0} : Set ℝ)) := by
  have hlow := nk.sqrt_one_sub_mul_le_edistOf_of_height (q := p) hR hheight hinside
  rw [← hpoint, edistOf_rescaledMetric_zero, a.edistOf_start hs,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hlow
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlow
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) hR.le),
    ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) hs.1)] at hreal
  exact a.not_mem_centralSphere_of_scaled_radius nk (hreserve.trans hreal)

theorem exists_transversePath_of_opposite_slices_of_radial_reserve
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t)
    {R H : ℝ} (hR : 0 < R) (hRH : R < H)
    (hreserve : 17 ≤ Real.sqrt (1 - eps) * R) (hinside : H < eps⁻¹)
    (a b : MinimizingArm (S.base.metric t) x) {s v : ℝ}
    (hs : s ∈ Icc 0 a.length) (hv : v ∈ Icc 0 b.length) {p q : Sphere 2}
    (hsides : (a.point s = nk.map (p, -H) ∧ b.point v = nk.map (q, H)) ∨
      (a.point s = nk.map (p, H) ∧ b.point v = nk.map (q, -H))) :
    (∀ w ∈ Icc s a.length, a.point w ∉ nk.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
      (∀ w ∈ Icc v b.length, b.point w ∉ nk.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
      ∃ path : TransversePath (a.point a.length) (b.point b.length)
          (nk.map '' (univ ×ˢ ({0} : Set ℝ))),
        path.intersection = 1 ∨ path.intersection = -1 := by
  have hH : 0 < H := hR.trans hRH
  have hp : |H| < eps⁻¹ := by simpa only [abs_of_pos hH] using hinside
  have hn : |-H| < eps⁻¹ := by simpa only [abs_neg] using hp
  have hpos : R < |H| := by simpa only [abs_of_pos hH] using hRH
  have hneg : R < |-H| := by simpa only [abs_neg] using hpos
  rcases hsides with hsides | hsides
  · have hano := a.not_mem_centralSphere_of_height_reserve nk hR hreserve hs hsides.1 hneg hn
    have hbno := b.not_mem_centralSphere_of_height_reserve nk hR hreserve hv hsides.2 hpos hp
    obtain ⟨path, hinter, _⟩ := exists_transversePath_of_opposite_arms nk a b hs hv
      hsides.1 hsides.2 (mul_neg_of_neg_of_pos (neg_neg_of_pos hH) hH) hn hp hano hbno
    exact ⟨hano, hbno, path, Or.inl (hinter hH)⟩
  · have hano := a.not_mem_centralSphere_of_height_reserve nk hR hreserve hs hsides.1 hpos hp
    have hbno := b.not_mem_centralSphere_of_height_reserve nk hR hreserve hv hsides.2 hneg hn
    obtain ⟨path, _, hinter⟩ := exists_transversePath_of_opposite_arms nk a b hs hv
      hsides.1 hsides.2 (mul_neg_of_pos_of_neg hH (neg_neg_of_pos hH)) hp hn hano hbno
    exact ⟨hano, hbno, path, Or.inr (hinter (neg_neg_of_pos hH))⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end
