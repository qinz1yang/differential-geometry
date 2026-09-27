import DifferentialGeometry.Topology.Diffeomorph.SphereGermExtension
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CompactGluing
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Globalization

section

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Z M : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z]
  [IsManifold (𝓡 3) ∞ Z] [T2Space Z] [CompactSpace Z]
  [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M]

omit [IsManifold (𝓡 3) ∞ Z] [IsManifold (𝓡 3) ∞ M] in
theorem exists_diffeomorph_of_ball_complement_and_ball
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hb1 : closedBall (0 : E3) 1 ⊆ b.source)
    (hP : (b '' ball (0 : E3) 1)ᶜ ⊆ P.source)
    (hG : closedBall (0 : E3) 1 ⊆ G.source)
    {U : Set M} (hPU : P '' (b '' ball (0 : E3) 1)ᶜ = U)
    (hGo : G '' ball (0 : E3) 1 = Uᶜ)
:
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) Z M ∞,
      EqOn e P (b '' ball (0 : E3) 1)ᶜ ∧
      e '' (b '' ball (0 : E3) 1) = Uᶜ ∧
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        D '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1 ∧
        (∀ z ∈ closedBall (0 : E3) 1, e (b z) = G (D z)) ∧
        ∃ O : Set Z, IsOpen O ∧ (b '' ball (0 : E3) 1)ᶜ ⊆ O ∧
          O ⊆ P.source ∧ EqOn e P O := by
  let K := (b '' ball (0 : E3) 1)ᶜ
  have hbS : sphere (0 : E3) 1 ⊆ b.source := sphere_subset_closedBall.trans hb1
  have hbB : ball (0 : E3) 1 ⊆ b.source := ball_subset_closedBall.trans hb1
  have hKc : IsCompact K :=
    (DifferentialGeometry.image_opens_isOpen b (U := ⟨_, isOpen_ball⟩) hbB).isClosed_compl.isCompact
  have hUc : IsClosed U := by
    rw [← hPU]
    exact (hKc.image_of_continuousOn (P.contMDiffOn_toFun.continuousOn.mono hP)).isClosed
  have hGc : G '' closedBall (0 : E3) 1 = closure Uᶜ := by
    rw [← closure_image_ball_of_partialDiffeomorph G hG, hGo]
  have hGs : G '' sphere (0 : E3) 1 = frontier U := by
    rw [← frontier_image_ball_of_partialDiffeomorph G hG, hGo, frontier_compl]
  have hPs : P '' (b '' sphere (0 : E3) 1) = frontier U := by
    rw [← hPU]
    exact image_sphere_eq_frontier_of_ball_complement b P hb1 hKc hP
  have hbsK : b '' sphere (0 : E3) 1 ⊆ K := by
    rintro y ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    have heq' : w = z := b.toPartialEquiv.injOn (hbB hw) (hbS hz) heq
    subst w
    exact (ne_of_lt hw) hz
  let A := (b.trans P).trans G.symm
  have hAsource : sphere (0 : E3) 1 ⊆ A.source := by
    intro z hz
    refine ⟨⟨hbS hz, hP (hbsK (mem_image_of_mem _ hz))⟩, ?_⟩
    have hzF : P (b z) ∈ frontier U := hPs ▸ mem_image_of_mem P (mem_image_of_mem b hz)
    obtain ⟨w, hw, heq⟩ := hGs.symm ▸ hzF
    change P (b z) ∈ G.target
    rw [← heq]
    exact G.map_source' (hG (sphere_subset_closedBall hw))
  have hAsphere : A '' sphere (0 : E3) 1 = sphere (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzF : P (b z) ∈ frontier U := hPs ▸ mem_image_of_mem P (mem_image_of_mem b hz)
      obtain ⟨w, hw, heq⟩ := hGs.symm ▸ hzF
      change G.symm (P (b z)) ∈ sphere (0 : E3) 1
      rw [← heq]
      have hleft : G.symm (G w) = w := G.left_inv' (hG (sphere_subset_closedBall hw))
      rwa [hleft]
    · intro hy
      have hyF : G y ∈ frontier U := hGs ▸ mem_image_of_mem G hy
      obtain ⟨_, ⟨z, hz, rfl⟩, heq⟩ := hPs.symm ▸ hyF
      refine ⟨z, hz, ?_⟩
      change G.symm (P (b z)) = y
      rw [heq]
      exact G.left_inv' (hG (sphere_subset_closedBall hy))
  have hAmap : MapsTo A (closedBall (0 : E3) 1 ∩ A.source) (closedBall (0 : E3) 1) := by
    intro z hz
    by_cases hzS : z ∈ sphere (0 : E3) 1
    · exact sphere_subset_closedBall (hAsphere ▸ mem_image_of_mem A hzS)
    · have hzB : z ∈ ball (0 : E3) 1 := lt_of_le_of_ne hz.1 hzS
      have hnotU : P (b z) ∉ U := by
        rw [← hPU]
        rintro ⟨w, hw, heq⟩
        have hwz : w = b z := P.toPartialEquiv.injOn (hP hw) hz.2.1.2 heq
        exact hw (hwz ▸ mem_image_of_mem b hzB)
      obtain ⟨w, hw, heq⟩ := hGo.symm.subset hnotU
      change G.symm (P (b z)) ∈ closedBall (0 : E3) 1
      rw [← heq]
      have hleft : G.symm (G w) = w := G.left_inv' (hG (ball_subset_closedBall hw))
      rw [hleft]
      exact ball_subset_closedBall hw
  obtain ⟨D, hDball, V, hVo, hSV, hVA, hDA⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph A hAsource hAsphere hAmap
  let Q := (b.symm.trans D.toPartialDiffeomorph).trans G
  have hQsource : b '' closedBall (0 : E3) 1 ⊆ Q.source := by
    rintro y ⟨z, hz, rfl⟩
    have hbz : b.symm (b z) = z := b.left_inv' (hb1 hz)
    refine ⟨⟨b.map_source' (hb1 hz), mem_univ _⟩, ?_⟩
    change D (b.symm (b z)) ∈ G.source
    rw [hbz]
    exact hG (hDball ▸ mem_image_of_mem D hz)
  have hQapply {z : E3} (hz : z ∈ closedBall (0 : E3) 1) : Q (b z) = G (D z) := by
    change G (D (b.symm (b z))) = G (D z)
    rw [show b.symm (b z) = z from b.left_inv' (hb1 hz)]
  have hQimage : Q '' (b '' closedBall (0 : E3) 1) = closure Uᶜ := by
    calc
      Q '' (b '' closedBall (0 : E3) 1) = G '' (D '' closedBall (0 : E3) 1) := by
        ext y
        constructor
        · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨D z, mem_image_of_mem D hz, (hQapply hz).symm⟩
        · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨b z, mem_image_of_mem b hz, hQapply hz⟩
      _ = closure Uᶜ := by rw [hDball, hGc]
  let O := b '' V
  have hVb : V ⊆ b.source := fun z hz => (hVA hz).1.1
  have hOo : IsOpen O := DifferentialGeometry.image_opens_isOpen b (U := ⟨V, hVo⟩) hVb
  have hPQ : EqOn P Q O := by
    rintro y ⟨z, hz, rfl⟩
    have hbz : b.symm (b z) = z := b.left_inv' (hVb hz)
    change P (b z) = G (D (b.symm (b z)))
    rw [hbz, hDA hz]
    exact (G.right_inv' (hVA hz).2).symm
  have hK1c : IsCompact (b '' closedBall (0 : E3) 1) :=
    (isCompact_closedBall (0 : E3) 1).image_of_continuousOn (b.contMDiffOn_toFun.continuousOn.mono hb1)
  have hinter : K ∩ (b '' closedBall (0 : E3) 1) = b '' sphere (0 : E3) 1 := by
    apply subset_antisymm
    · rintro y ⟨hyK, z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      exact le_antisymm hz (not_lt.mp fun h => hyK (mem_image_of_mem b h))
    · rintro y ⟨z, hz, rfl⟩
      exact ⟨hbsK (mem_image_of_mem b hz), mem_image_of_mem b (sphere_subset_closedBall hz)⟩
  have hKO : K ∩ (b '' closedBall (0 : E3) 1) ⊆ O := by rw [hinter]; exact image_mono hSV
  have himage : P '' K ∩ Q '' (b '' closedBall (0 : E3) 1) ⊆ P '' (K ∩ (b '' closedBall (0 : E3) 1)) := by
    rw [hPU, hQimage, hinter, hPs, closure_compl, hUc.frontier_eq]
    exact subset_rfl
  obtain ⟨J, O0, O1, hO0o, _hO1o, hKO0, hK1O1, hOsrc, hJP, hJQ⟩ :=
    PartialDiffeomorph.exists_eqOn_neighborhoods_of_isCompact P Q hKc hK1c hP hQsource hOo hKO hPQ himage
  have hcover : K ∪ (b '' closedBall (0 : E3) 1) = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z ∈ b '' ball (0 : E3) 1
    · exact Or.inr (image_mono ball_subset_closedBall hz)
    · exact Or.inl hz
  have hJsrc : J.source = univ := eq_univ_of_univ_subset (by
    rw [← hcover]
    exact (union_subset_union hKO0 hK1O1).trans hOsrc)
  have hJtarget : J.target = univ := eq_univ_of_forall fun y => by
    by_cases hy : y ∈ U
    · obtain ⟨z, hz, hzy⟩ := hPU.symm.subset hy
      have hJz : J z = P z := hJP (hKO0 hz)
      rw [← hzy, ← hJz]
      exact J.map_source' (by rw [hJsrc]; trivial)
    · obtain ⟨z, hz, hzy⟩ := hQimage.symm.subset (subset_closure hy)
      have hJz : J z = Q z := hJQ (hK1O1 hz)
      rw [← hzy, ← hJz]
      exact J.map_source' (by rw [hJsrc]; trivial)
  let e := PDE.RicciFlow.Perelman.KappaSolutions.globalDiffeomorphOfUniv J hJsrc hJtarget
  have heP : EqOn e P K := fun z hz => hJP (hKO0 hz)
  refine ⟨e, heP, ?_, D, hDball, ?_, O0 ∩ P.source, hO0o.inter P.open_source,
    subset_inter hKO0 hP, inter_subset_right, fun z hz => hJP hz.1⟩
  · have heK : e '' K = U := (heP.image_eq).trans hPU
    have hcomp : e '' Kᶜ = Uᶜ := by
      change e.toHomeomorph '' Kᶜ = Uᶜ
      rw [e.toHomeomorph.image_compl]
      exact congrArg compl heK
    simpa only [K, compl_compl] using hcomp
  · intro z hz
    exact (hJQ (hK1O1 (mem_image_of_mem b hz))).trans (hQapply hz)

end DifferentialGeometry.Topology.Manifold

end

end
