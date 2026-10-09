/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutExtension
import DifferentialGeometry.External.Schoenflies.PolyArcRealize
import DifferentialGeometry.External.Schoenflies.AccessibleJoin

open Set Metric

namespace Schoenflies

theorem PolyArc.polyAccessible_compl_start {n : ℕ} (A : PolyArc n) :
    PolyAccessible A.carrierᶜ (A.vertex 0) := by
  let K := ⋃ i ∈ (Finset.Icc 1 n : Finset ℕ), A.edge i
  have hK : IsCompact K :=
    (Finset.finite_toSet _).isCompact_biUnion fun i _ => A.isCompact_edge (i := i)
  have hpK : A.vertex 0 ∉ K := by
    simp only [K, mem_iUnion, exists_prop, Finset.mem_Icc]
    rintro ⟨i, hi, hx⟩
    exact A.vertex_notMem_edge (by omega) hi.2 (by omega) (by omega) hx
  obtain ⟨ε, hε, hball⟩ := isOpen_iff.mp hK.isClosed.isOpen_compl _ hpK
  have hnegative (c : ℝ) (hc : c < 0) : A.pt 0 c ∉ A.edge 0 := by
    intro hx
    obtain ⟨d, hd, hcd⟩ := A.mem_edge_iff.mp hx
    rw [A.pt_eq, A.pt_eq, add_right_inj] at hcd
    have hdir : A.tang 0 ≠ 0 := by
      intro hz
      have hh := A.isDirection_tang (i := 0)
      simp [Plane.IsDirection, hz] at hh
    have heq : c = d := (smul_left_injective ℝ hdir) hcd
    linarith [hd.1]
  have havoid (c : ℝ) (hc : c < 0) (hsize : |c| < ε) : A.pt 0 c ∈ A.carrierᶜ := by
    intro hx
    obtain ⟨i, hi, hxi⟩ := A.mem_carrier_iff.mp hx
    by_cases hi0 : i = 0
    · subst i
      exact hnegative c hc hxi
    · have hxball : A.pt 0 c ∈ ball (A.vertex 0) ε := by
        rw [mem_ball, A.dist_pt_vertex]
        exact hsize
      exact hball hxball (mem_iUnion₂.mpr ⟨i, Finset.mem_Icc.mpr ⟨by omega, hi⟩, hxi⟩)
  have hq := havoid (-ε / 2) (by linarith) (by rw [abs_of_neg (by linarith)]; linarith)
  refine PolyAccessible.of_openSegment hq ?_
  rintro x ⟨a, b, ha, hb, hab, rfl⟩
  have heq : a • A.vertex 0 + b • A.pt 0 (-ε / 2) = A.pt 0 (b * (-ε / 2)) := by
    rw [A.pt_eq, A.pt_eq]
    match_scalars <;> nlinarith
  rw [heq]
  apply havoid
  · exact mul_neg_of_pos_of_neg hb (by linarith)
  · rw [abs_of_neg (mul_neg_of_pos_of_neg hb (by linarith))]
    nlinarith

theorem IsArcBetween.polyAccessible_compl_left {A : Set Plane} {a b : Plane}
    (hA : IsArcBetween A a b) (hpoly : IsPolygonal A) : PolyAccessible Aᶜ a := by
  obtain ⟨n, P, hP, hp, -⟩ := isPolyArcCarrier_of_isPolygonal hA hpoly
  simpa only [hP, hp] using P.polyAccessible_compl_start

end Schoenflies
