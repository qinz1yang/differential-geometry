import DifferentialGeometry.Topology.PiecewiseLinear.PlanarBoundaryCollars
import DifferentialGeometry.Topology.PiecewiseLinear.LateralAnnulusLevels
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskPrism
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonChartTransport
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphOpen

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.exists_boundary_arc_chart_of_exterior_collar
    {D W G : Set (ℝ × ℝ)} {q : (Fin 3 → ℝ) → ℝ × ℝ}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {γ : ℝ → ℝ × ℝ}
    (hγ : IsPLHomeomorphOn γ (Icc (-d) d) G)
    (hG : G ⊆ q '' stdSimplexBoundary 2) {ρ : (ℝ × ℝ) × ℝ → ℝ × ℝ}
    (hρ : IsPLHomeomorphOn ρ ((q '' stdSimplexBoundary 2) ×ˢ Icc 0 c) W)
    (hzero : ∀ x ∈ q '' stdSimplexBoundary 2, ρ (x, 0) = x)
    (hWD : W ∩ D = q '' stdSimplexBoundary 2) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      e.source = Ioo (-d) d ×ˢ Ioo (-1 : ℝ) c ∧
      IsPLHomeomorphOn e e.source e.target ∧
      (∀ t ∈ Ioo (-d) d, ∀ r ∈ Ico (0 : ℝ) c, e (t, r) = ρ (γ t, r)) ∧
      (∀ t ∈ Ioo (-d) d, e (t, 0) = γ t) ∧
      ∀ t ∈ Ioo (-d) d, ∀ r ∈ Ioo (-1 : ℝ) 0,
        e (t, r) ∈ D \ (q '' stdSimplexBoundary 2) := by
  let B := q '' stdSimplexBoundary 2
  have hB : IsPolyhedron B :=
    isPolyhedron_stdSimplexBoundary_two.image_of_isPiecewiseAffineOn
      (hq.restrict isPolyhedron_stdSimplexBoundary_two
        (fun _ hx => hx.1)).isPiecewiseAffineOn
      (hq.bijOn.injOn.mono (fun _ hx => hx.1))
  obtain ⟨A, K, σ, -, -, -, hcover, hσ, hσone, -, -, hσinside⟩ :=
    hq.exists_disk_boundary_collar (U := univ) (by simp)
  have hAD : A ⊆ D := hcover ▸ subset_union_right
  have hBA : B ⊆ A := fun x hx => hσone x hx ▸ hσ.bijOn.mapsTo ⟨hx, by norm_num⟩
  have hAW : A ∩ W = B := Subset.antisymm
    (fun _ hx => hWD.subset ⟨hx.2, hAD hx.1⟩)
    (fun x hx => ⟨hBA hx, hzero x hx ▸ hρ.bijOn.mapsTo ⟨hx, le_rfl, hc.le⟩⟩)
  have hshift : IsPLHomeomorphOn (fun r : ℝ => r + 1) (Icc (-1) 0) (Icc 0 1) := by
    simpa only [one_mul, zero_add] using isPLHomeomorphOn_mul_add_Icc
      (by norm_num : (0 : ℝ) < 1) (a := -1) (b := 0) (a' := 0) (b' := 1)
      (by norm_num : (1 : ℝ) * (-1) + 1 = 0) (by norm_num : (1 : ℝ) * 0 + 1 = 1)
  let σ' := σ ∘ Prod.map id (fun r : ℝ => r + 1)
  have hσ' : IsPLHomeomorphOn σ' (B ×ˢ Icc (-1 : ℝ) 0) A :=
    (hB.isPLHomeomorphOn_id.prodMap hshift).trans hσ
  have hσ'zero (x) (hx : x ∈ B) : σ' (x, 0) = x := by
    simpa [σ'] using hσone x hx
  have hagree : EqOn σ' ρ ((B ×ˢ Icc (-1 : ℝ) 0) ∩ (B ×ˢ Icc 0 c)) := by
    rintro ⟨x, r⟩ hr
    have hr0 : r = 0 := le_antisymm hr.1.2.2 hr.2.2.1
    subst r
    exact (hσ'zero x hr.1.1).trans (hzero x hr.1.1).symm
  have hsurj : SurjOn σ' ((B ×ˢ Icc (-1 : ℝ) 0) ∩ (B ×ˢ Icc 0 c)) (A ∩ W) := by
    intro x hx
    have hxB := hAW.subset hx
    exact ⟨(x, 0), ⟨⟨hxB, by norm_num⟩, hxB, le_rfl, hc.le⟩, hσ'zero x hxB⟩
  obtain ⟨ψ, hψ, hleft, hright⟩ := exists_isPLHomeomorphOn_union
    (hB.prod isHPolytope_Icc.isPolyhedron) (hB.prod isHPolytope_Icc.isPolyhedron)
    hσ' hρ hagree hsurj
  have hunion : (B ×ˢ Icc (-1 : ℝ) 0) ∪ (B ×ˢ Icc 0 c) = B ×ˢ Icc (-1 : ℝ) c := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact ⟨hz.1, hz.2.1, hz.2.2.trans hc.le⟩
      · exact ⟨hz.1, (by norm_num : (-1 : ℝ) ≤ 0).trans hz.2.1, hz.2.2⟩
    · rintro ⟨hzB, ha, hb⟩
      by_cases hr : z.2 ≤ 0
      · exact Or.inl ⟨hzB, ha, hr⟩
      · exact Or.inr ⟨hzB, (lt_of_not_ge hr).le, hb⟩
  rw [hunion] at hψ
  let T := Icc (-d) d ×ˢ Icc (-1 : ℝ) c
  have hdom : G ×ˢ Icc (-1 : ℝ) c ⊆ B ×ˢ Icc (-1 : ℝ) c := prod_mono_left hG
  have hGpoly : IsPolyhedron G := by
    rw [← hγ.image_eq]
    exact (isPLBall_Icc (by linarith : -d < d)).isPolyhedron.image_of_isPiecewiseAffineOn
      hγ.isPiecewiseAffineOn hγ.bijOn.injOn
  have hφ := (hγ.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans
    (hψ.restrict (hGpoly.prod isHPolytope_Icc.isPolyhedron) hdom)
  let U := Ioo (-d) d ×ˢ Ioo (-1 : ℝ) c
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hUT : U ⊆ T := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  obtain ⟨e, heU, heφ⟩ :=
    DifferentialGeometry.Topology.exists_openPartialHomeomorph_of_continuousOn_injOn_finrank
      rfl hU (hφ.isPiecewiseAffineOn.continuousOn.mono hUT) (hφ.bijOn.injOn.mono hUT)
  have hepl : IsPiecewiseAffineOn e e.source := by
    rw [heU]
    exact (hφ.isPiecewiseAffineOn.mono hU hUT).congr (fun x _ => heφ x)
  refine ⟨e, heU, isPLHomeomorphOn_openPartialHomeomorph e hepl, ?_, ?_, ?_⟩
  · intro t ht r hr
    rw [heφ]
    exact hright ⟨hG (hγ.bijOn.mapsTo (Ioo_subset_Icc_self ht)), hr.1, hr.2.le⟩
  · intro t ht
    rw [heφ]
    exact (hright ⟨hG (hγ.bijOn.mapsTo (Ioo_subset_Icc_self ht)), le_rfl, hc.le⟩).trans
      (hzero _ (hG (hγ.bijOn.mapsTo (Ioo_subset_Icc_self ht))))
  · intro t ht r hr
    rw [heφ]
    change ψ (γ t, r) ∈ D \ (q '' stdSimplexBoundary 2)
    rw [hleft ⟨hG (hγ.bijOn.mapsTo (Ioo_subset_Icc_self ht)), hr.1.le, hr.2.le⟩]
    change σ (γ t, r + 1) ∈ D \ (q '' stdSimplexBoundary 2)
    exact hσinside ⟨hG (hγ.bijOn.mapsTo (Ioo_subset_Icc_self ht)),
      by linarith [hr.1], by linarith [hr.2]⟩

end DifferentialGeometry.Topology.PiecewiseLinear
