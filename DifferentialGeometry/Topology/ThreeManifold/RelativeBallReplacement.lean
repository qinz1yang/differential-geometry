import DifferentialGeometry.Topology.Diffeomorph.SphereGermExtension
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CompactGluing
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {Z M : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] [T3Space Z]
  [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]

theorem exists_partialDiffeomorph_ball_replacement_eqOn_complement
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hb : closedBall (0 : E3) 1 ⊆ b.source)
    (hG : closedBall (0 : E3) 1 ⊆ G.source)
    {Ω : Set Z} (hΩ : IsCompact Ω)
    (hbΩ : b '' closedBall (0 : E3) 1 ⊆ interior Ω)
    (hP : Ω \ b '' ball (0 : E3) 1 ⊆ P.source)
    (hboundary : P '' (b '' sphere (0 : E3) 1) = G '' sphere (0 : E3) 1)
    (hinter : P '' (Ω \ b '' ball (0 : E3) 1) ∩ G '' closedBall (0 : E3) 1 ⊆
      G '' sphere (0 : E3) 1) :
    ∃ (J : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
      (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      Ω ⊆ J.source ∧
      J '' Ω = P '' (Ω \ b '' ball (0 : E3) 1) ∪ G '' closedBall (0 : E3) 1 ∧
      D '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1 ∧
      (∀ z ∈ closedBall (0 : E3) 1, J (b z) = G (D z)) ∧
      ∃ O : Set Z, IsOpen O ∧ Ω \ b '' ball (0 : E3) 1 ⊆ O ∧
        O ⊆ P.source ∧ EqOn J P O := by
  let K := Ω \ b '' ball (0 : E3) 1
  have hbB : ball (0 : E3) 1 ⊆ b.source := ball_subset_closedBall.trans hb
  have hbS : sphere (0 : E3) 1 ⊆ b.source := sphere_subset_closedBall.trans hb
  have hK : IsCompact K := hΩ.inter_right
    (b.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball hbB).isClosed_compl
  have hbsK : b '' sphere (0 : E3) 1 ⊆ K := by
    rintro y ⟨z, hz, rfl⟩
    refine ⟨interior_subset (hbΩ ⟨z, sphere_subset_closedBall hz, rfl⟩), ?_⟩
    rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := b.toPartialEquiv.injOn (hbB hw) (hbS hz) hwz
    exact (mem_ball_zero_iff.mp (hwz' ▸ hw)).ne (mem_sphere_zero_iff_norm.mp hz)
  let P₀ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict P (interior Ω) isOpen_interior
  let A := (b.trans P₀).trans G.symm
  have hAs : sphere (0 : E3) 1 ⊆ A.source := by
    intro z hz
    have hzK := hbsK ⟨z, hz, rfl⟩
    refine ⟨⟨hbS hz, hP hzK, hbΩ ⟨z, sphere_subset_closedBall hz, rfl⟩⟩, ?_⟩
    obtain ⟨w, hw, heq⟩ := hboundary ▸ mem_image_of_mem P (mem_image_of_mem b hz)
    change P (b z) ∈ G.target
    exact heq ▸ G.map_source (hG (sphere_subset_closedBall hw))
  have hAsphere : A '' sphere (0 : E3) 1 = sphere (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, heq⟩ := hboundary ▸ mem_image_of_mem P (mem_image_of_mem b hz)
      change G.symm (P (b z)) ∈ sphere (0 : E3) 1
      rw [← heq]
      exact (G.toPartialEquiv.left_inv (hG (sphere_subset_closedBall hw))).symm ▸ hw
    · intro hy
      obtain ⟨_, ⟨z, hz, rfl⟩, heq⟩ := hboundary.symm ▸ mem_image_of_mem G hy
      refine ⟨z, hz, ?_⟩
      change G.symm (P (b z)) = y
      rw [heq]
      exact G.toPartialEquiv.left_inv (hG (sphere_subset_closedBall hy))
  have hAout : MapsTo A ((ball (0 : E3) 1)ᶜ ∩ A.source) (ball (0 : E3) 1)ᶜ := by
    intro z hz hAin
    have hbzK : b z ∈ K := by
      refine ⟨interior_subset hz.2.1.2.2, ?_⟩
      rintro ⟨w, hw, heq⟩
      exact hz.1 ((b.toPartialEquiv.injOn (hbB hw) hz.2.1.1 heq) ▸ hw)
    have hPbinG : P (b z) ∈ G '' closedBall (0 : E3) 1 := by
      exact ⟨A z, ball_subset_closedBall hAin, G.right_inv hz.2.2⟩
    obtain ⟨w, hw, heq⟩ := hinter ⟨mem_image_of_mem P hbzK, hPbinG⟩
    have he : A z = w := by
      change G.symm (P (b z)) = w
      rw [← heq]
      exact G.toPartialEquiv.left_inv (hG (sphere_subset_closedBall hw))
    exact (mem_ball_zero_iff.mp (he ▸ hAin)).ne (mem_sphere_zero_iff_norm.mp hw)
  obtain ⟨D, hDball, V, hV, hSV, hVA, hDA⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph_of_compl_ball
      A hAs hAsphere hAout
  let Q := (b.symm.trans D.toPartialDiffeomorph).trans G
  have hQsource : b '' closedBall (0 : E3) 1 ⊆ Q.source := by
    rintro y ⟨z, hz, rfl⟩
    refine ⟨⟨b.map_source (hb hz), mem_univ _⟩, ?_⟩
    change D (b.symm (b z)) ∈ G.source
    have hbz : b.symm.toPartialEquiv (b.toPartialEquiv z) = z :=
      b.toPartialEquiv.left_inv (hb hz)
    rw [hbz]
    exact hG (hDball ▸ mem_image_of_mem D hz)
  have hQapply (z : E3) (hz : z ∈ closedBall (0 : E3) 1) : Q (b z) = G (D z) := by
    change G (D (b.symm (b z))) = G (D z)
    have hbz : b.symm.toPartialEquiv (b.toPartialEquiv z) = z :=
      b.toPartialEquiv.left_inv (hb hz)
    rw [hbz]
  have hQimage : Q '' (b '' closedBall (0 : E3) 1) = G '' closedBall (0 : E3) 1 := by
    calc
      _ = G '' (D '' closedBall (0 : E3) 1) := by
        ext y
        constructor
        · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨D z, mem_image_of_mem D hz, (hQapply z hz).symm⟩
        · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨b z, mem_image_of_mem b hz, hQapply z hz⟩
      _ = _ := by rw [hDball]
  let O := b '' V
  have hVb : V ⊆ b.source := fun z hz => (hVA hz).1.1
  have hO : IsOpen O := b.toOpenPartialHomeomorph.isOpen_image_of_subset_source hV hVb
  have hPQ : EqOn P Q O := by
    rintro y ⟨z, hz, rfl⟩
    change P (b z) = G (D (b.symm (b z)))
    have hbz : b.symm.toPartialEquiv (b.toPartialEquiv z) = z :=
      b.toPartialEquiv.left_inv (hVb hz)
    rw [hbz, hDA hz]
    exact (G.right_inv (hVA hz).2).symm
  have hKball : K ∩ (b '' closedBall (0 : E3) 1) = b '' sphere (0 : E3) 1 := by
    apply subset_antisymm
    · rintro y ⟨hyK, z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      rw [mem_sphere_zero_iff_norm]
      exact le_antisymm (mem_closedBall_zero_iff.mp hz)
        (not_lt.mp (fun h => hyK.2 ⟨z, mem_ball_zero_iff.mpr h, rfl⟩))
    · exact fun y hy => ⟨hbsK hy, image_mono sphere_subset_closedBall hy⟩
  have himage : P '' K ∩ Q '' (b '' closedBall (0 : E3) 1) ⊆
      P '' (K ∩ (b '' closedBall (0 : E3) 1)) := by
    rw [hQimage, hKball, hboundary]
    exact hinter
  have hbc : IsCompact (b '' closedBall (0 : E3) 1) :=
    (isCompact_closedBall _ _).image_of_continuousOn (b.contMDiffOn_toFun.continuousOn.mono hb)
  obtain ⟨J, O₀, O₁, hO₀, _, hKO₀, hBO₁, hJO, hJP, hJQ⟩ :=
    PartialDiffeomorph.exists_eqOn_neighborhoods_of_isCompact P Q hK hbc hP hQsource
      hO (hKball ▸ image_mono hSV) hPQ himage
  have hcover : K ∪ (b '' closedBall (0 : E3) 1) = Ω := by
    apply subset_antisymm
    · exact union_subset sdiff_subset (hbΩ.trans interior_subset)
    · intro x hx
      by_cases hb : x ∈ b '' ball (0 : E3) 1
      · exact Or.inr (image_mono ball_subset_closedBall hb)
      · exact Or.inl ⟨hx, hb⟩
  have hJsource : Ω ⊆ J.source := by
    rw [← hcover]
    exact (union_subset_union hKO₀ hBO₁).trans hJO
  refine ⟨J, D, hJsource, ?_, hDball, ?_, O₀ ∩ P.source, hO₀.inter P.open_source,
    subset_inter hKO₀ hP, inter_subset_right, fun z hz => hJP hz.1⟩
  · calc
      J '' Ω = J '' (K ∪ b '' closedBall (0 : E3) 1) := congrArg (Set.image J) hcover.symm
      _ = P '' K ∪ G '' closedBall (0 : E3) 1 := by
        rw [image_union, (hJP.mono hKO₀).image_eq, (hJQ.mono hBO₁).image_eq, hQimage]
  · exact fun z hz => (hJQ (hBO₁ (mem_image_of_mem b hz))).trans (hQapply z hz)

end DifferentialGeometry.Topology.Manifold
