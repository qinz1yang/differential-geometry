import DifferentialGeometry.Topology.PiecewiseLinear.BranchCollarPrismLevel
import DifferentialGeometry.Topology.PiecewiseLinear.ArcSubset

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Circle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.isPLBall_one_of_isClosed_of_isConnected_of_ssubset {S C : Set E}
    (hS : IsPLSphere 1 S) (hclosed : IsClosed C) (hconn : IsConnected C)
    (hne : C.Nontrivial) (hCS : C ⊂ S) : IsPLBall 1 C := by
  obtain ⟨A, hA, hCA, -⟩ := hS.exists_isPLBall_one_superset_of_ssubset hclosed hCS
  exact hA.isPLBall_one_of_isCompact_of_isConnected
    (hS.isPolyhedron.isCompact.of_isClosed_subset hclosed hCS.1) hconn hne hCA

theorem IsPLSphere.isPLBall_one_closure_of_isConnected_of_ssubset {S W : Set E}
    (hS : IsPLSphere 1 S) (hconn : IsConnected W) (hne : W.Nontrivial)
    (hproper : closure W ⊂ S) : IsPLBall 1 (closure W) :=
  hS.isPLBall_one_of_isClosed_of_isConnected_of_ssubset isClosed_closure hconn.closure
    (hne.mono subset_closure) hproper

theorem IsPLSphere.exists_isPLHomeomorphOn_Icc_closure_of_isConnected_of_ssubset {S W : Set E}
    (hS : IsPLSphere 1 S) (hconn : IsConnected W) (hne : W.Nontrivial)
    (hproper : closure W ⊂ S) :
    ∃ θ : ℝ → E, IsPLHomeomorphOn θ (Icc (0 : ℝ) 1) (closure W) :=
  exists_isPLHomeomorphOn_Icc_of_isPLBall_one
    (hS.isPLBall_one_closure_of_isConnected_of_ssubset hconn hne hproper)

theorem sdiff_subset_endpoints_of_isConnected_of_closure_eq {J W : Set E} {θ : ℝ → E}
    (hθ : IsPLHomeomorphOn θ (Icc (0 : ℝ) 1) J) (hconn : IsConnected W)
    (hcl : closure W = J) : J \ W ⊆ {θ 0, θ 1} := by
  classical
  have hJball : IsPLBall 1 J :=
    (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hθ
  have hJclosed : IsClosed J := hJball.isPolyhedron.isCompact.isClosed
  have hgcont : ContinuousOn (Function.invFunOn θ (Icc (0 : ℝ) 1)) J :=
    hθ.isPiecewiseAffineOn_invFunOn.continuousOn
  have hginj : InjOn (Function.invFunOn θ (Icc (0 : ℝ) 1)) J := hθ.symm.bijOn.injOn
  have hgmem : ∀ x ∈ J, Function.invFunOn θ (Icc (0 : ℝ) 1) x ∈ Icc (0 : ℝ) 1 :=
    fun x hx => hθ.bijOn.surjOn.mapsTo_invFunOn hx
  have hg0 : Function.invFunOn θ (Icc (0 : ℝ) 1) (θ 0) = 0 :=
    hθ.bijOn.invOn_invFunOn.1 ⟨le_rfl, zero_le_one⟩
  have hg1 : Function.invFunOn θ (Icc (0 : ℝ) 1) (θ 1) = 1 :=
    hθ.bijOn.invOn_invFunOn.1 ⟨zero_le_one, le_rfl⟩
  have hθ0J : θ 0 ∈ J := hθ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hθ1J : θ 1 ∈ J := hθ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hWJ : W ⊆ J := hcl ▸ subset_closure
  rintro z ⟨hzJ, hzW⟩
  by_contra hcon
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hcon
  obtain ⟨hz0, hz1⟩ := hcon
  have htmem : Function.invFunOn θ (Icc (0 : ℝ) 1) z ∈ Icc (0 : ℝ) 1 := hgmem z hzJ
  have ht0 : Function.invFunOn θ (Icc (0 : ℝ) 1) z ≠ 0 := by
    intro h
    exact hz0 (hginj hzJ hθ0J (by rw [h, hg0]))
  have ht1 : Function.invFunOn θ (Icc (0 : ℝ) 1) z ≠ 1 := by
    intro h
    exact hz1 (hginj hzJ hθ1J (by rw [h, hg1]))
  have hWne : ∀ x ∈ W, Function.invFunOn θ (Icc (0 : ℝ) 1) x
      ≠ Function.invFunOn θ (Icc (0 : ℝ) 1) z := by
    intro x hx hxt
    exact hzW (hginj (hWJ hx) hzJ hxt ▸ hx)
  have himg : IsConnected (Function.invFunOn θ (Icc (0 : ℝ) 1) '' W) :=
    hconn.image _ (hgcont.mono hWJ)
  have hdisj : Disjoint (Iio (Function.invFunOn θ (Icc (0 : ℝ) 1) z))
      (Ioi (Function.invFunOn θ (Icc (0 : ℝ) 1) z)) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd (lt_trans hx hx') (lt_irrefl x)
  have hcover : Function.invFunOn θ (Icc (0 : ℝ) 1) '' W
      ⊆ Iio (Function.invFunOn θ (Icc (0 : ℝ) 1) z)
        ∪ Ioi (Function.invFunOn θ (Icc (0 : ℝ) 1) z) := by
    rintro _ ⟨x, hx, rfl⟩
    rcases lt_or_gt_of_ne (hWne x hx) with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases himg.isPreconnected.subset_or_subset isOpen_Iio isOpen_Ioi hdisj hcover with hlt | hgt
  · have hclosedset : IsClosed (J ∩ Function.invFunOn θ (Icc (0 : ℝ) 1) ⁻¹'
        Iic (Function.invFunOn θ (Icc (0 : ℝ) 1) z)) :=
      hgcont.preimage_isClosed_of_isClosed hJclosed isClosed_Iic
    have hWsub : W ⊆ J ∩ Function.invFunOn θ (Icc (0 : ℝ) 1) ⁻¹'
        Iic (Function.invFunOn θ (Icc (0 : ℝ) 1) z) :=
      fun x hx => ⟨hWJ hx, mem_preimage.mpr (mem_Iic.mpr (le_of_lt (hlt ⟨x, hx, rfl⟩)))⟩
    have hsub0 : closure W ⊆ J ∩ Function.invFunOn θ (Icc (0 : ℝ) 1) ⁻¹'
        Iic (Function.invFunOn θ (Icc (0 : ℝ) 1) z) := closure_minimal hWsub hclosedset
    have hsub : J ⊆ J ∩ Function.invFunOn θ (Icc (0 : ℝ) 1) ⁻¹'
        Iic (Function.invFunOn θ (Icc (0 : ℝ) 1) z) := by rwa [hcl] at hsub0
    have hle := (hsub hθ1J).2
    rw [mem_preimage, hg1, mem_Iic] at hle
    exact ht1 (le_antisymm htmem.2 hle)
  · have hclosedset : IsClosed (J ∩ Function.invFunOn θ (Icc (0 : ℝ) 1) ⁻¹'
        Ici (Function.invFunOn θ (Icc (0 : ℝ) 1) z)) :=
      hgcont.preimage_isClosed_of_isClosed hJclosed isClosed_Ici
    have hWsub : W ⊆ J ∩ Function.invFunOn θ (Icc (0 : ℝ) 1) ⁻¹'
        Ici (Function.invFunOn θ (Icc (0 : ℝ) 1) z) :=
      fun x hx => ⟨hWJ hx, mem_preimage.mpr (mem_Ici.mpr (le_of_lt (hgt ⟨x, hx, rfl⟩)))⟩
    have hsub0 : closure W ⊆ J ∩ Function.invFunOn θ (Icc (0 : ℝ) 1) ⁻¹'
        Ici (Function.invFunOn θ (Icc (0 : ℝ) 1) z) := closure_minimal hWsub hclosedset
    have hsub : J ⊆ J ∩ Function.invFunOn θ (Icc (0 : ℝ) 1) ⁻¹'
        Ici (Function.invFunOn θ (Icc (0 : ℝ) 1) z) := by rwa [hcl] at hsub0
    have hge := (hsub hθ0J).2
    rw [mem_preimage, hg0, mem_Ici] at hge
    exact ht0 (le_antisymm hge htmem.1)

end Circle

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_isPLHomeomorphOn_Icc_displacedArc_of_isConnected (D : SingularTwoCell M)
    {W : Set (EuclideanSpace ℝ (Fin 2))} (hconn : IsConnected W) (hne : W.Nontrivial)
    (hproper : closure W ⊂ frontier D.domain) :
    ∃ θ : ℝ → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn θ (Icc (0 : ℝ) 1) (closure W) ∧
      closure W ⊆ frontier D.domain ∧ closure W \ W ⊆ {θ 0, θ 1} := by
  obtain ⟨θ, hθ⟩ :=
    D.isPLBall_domain.isPLSphere_frontier.exists_isPLHomeomorphOn_Icc_closure_of_isConnected_of_ssubset
      hconn hne hproper
  exact ⟨θ, hθ, hproper.1,
    sdiff_subset_endpoints_of_isConnected_of_closure_eq hθ hconn rfl⟩

open Classical in
theorem exists_collarExtension_image_inter_boundary_of_displacedArc
    [HasGroupoid M (plGroupoid 3)]
    {D : SingularTwoCell M} {BdM N : Set M} {hslide : M → M}
    {P A B W Δ' : Set (EuclideanSpace ℝ (Fin 2))} {θ : ℝ → EuclideanSpace ℝ (Fin 2)}
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (n : EuclideanSpace ℝ (Fin 3)) (hn : ℓ n = 1)
    (hBd : ∀ y ∈ ec.target, ec.symm y ∈ BdM ↔ ℓ y = 0)
    (hbdpre : D.domain ∩ D ⁻¹' BdM ⊆ frontier D.domain)
    (hDN : MapsTo D D.domain N)
    (hrefl : ∀ x ∈ N, hslide x ∈ BdM → x ∈ BdM)
    (hgpl : IsPLOn 2 3 (P.piecewise (hslide ∘ D) D) D.domain)
    (hΔ'ball : IsPLBall 2 Δ') (hsubint : D.domain ⊆ interior Δ')
    (hρid : ∀ x ∈ D.domain, ρ x = x)
    (hρfr : MapsTo ρ (Δ' \ D.domain) (frontier D.domain))
    (hρsurj : frontier D.domain ⊆ ρ '' frontier Δ')
    (hτ0 : ∀ x ∈ D.domain, τ x = 0) (hτ1 : ∀ x ∈ frontier Δ', τ x = 1)
    (hconn : IsConnected W)
    (hθ : IsPLHomeomorphOn θ (Icc (0 : ℝ) 1) (closure W))
    (hWfr : closure W ⊆ frontier D.domain)
    (hinj : InjOn (P.piecewise (hslide ∘ D) D) (closure W))
    (hqsrc : MapsTo (P.piecewise (hslide ∘ D) D) (closure W) ec.source)
    (hfr : ∀ z ∈ frontier D.domain, z ∉ closure W → P.piecewise (hslide ∘ D) D z ∈ BdM)
    (hApoly : IsPolyhedron A) (hBpoly : IsPolyhedron B)
    (hunion : A ∪ B = Δ' \ interior D.domain)
    (hρA : IsPiecewiseAffineOn ρ A) (hτA : IsPiecewiseAffineOn τ A)
    (hρB : IsPiecewiseAffineOn ρ B)
    (hmapA : MapsTo (fun x => (ρ x, τ x)) A (closure W ×ˢ Icc (0 : ℝ) 1))
    (hmapB : MapsTo ρ B (frontier D.domain))
    (hBbd : ∀ x ∈ B, P.piecewise (hslide ∘ D) D (ρ x) ∈ BdM)
    {c : ℝ} (hc : 0 < c)
    (hle : ∀ z ∈ closure W, ℓ (ec (P.piecewise (hslide ∘ D) D z)) ≤ 0)
    (hge : ∀ z ∈ closure W, -c ≤ ℓ (ec (P.piecewise (hslide ∘ D) D z)))
    (hWdisp : ∀ z ∈ closure W, ℓ (ec (P.piecewise (hslide ∘ D) D z)) = 0 ↔ z ∉ W)
    (hθ0 : θ 0 ∉ W) (hθ1 : θ 1 ∉ W)
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : Convex ℝ S)
    (hbS : MapsTo (fun z => ec (P.piecewise (hslide ∘ D) D z)) (closure W) S)
    (hdS : MapsTo (fun z => boundaryDrop ℓ n (ec (P.piecewise (hslide ∘ D) D z)))
      (closure W) S)
    (hslab : ∀ v ∈ S, ∀ r : ℝ, 0 ≤ r → r ≤ c → boundaryDrop ℓ n v - r • n ∈ ec.target) :
    ∃ G : SingularTwoCell M, G.domain = Δ' ∧
      EqOn G (P.piecewise (hslide ∘ D) D) D.domain ∧
      Set.range G.boundary ⊆ BdM ∧
      G '' G.domain ∩ BdM = Set.range G.boundary := by
  have hJW : closure W \ W ⊆ {θ 0, θ 1} :=
    sdiff_subset_endpoints_of_isConnected_of_closure_eq hθ hconn rfl
  have hθ0J : θ 0 ∈ closure W := hθ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hθ1J : θ 1 ∈ closure W := hθ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  refine exists_collarExtension_image_inter_boundary_of_levelPrism_over_arc ec hec ℓ n hn hBd
    hbdpre hDN hrefl hgpl hΔ'ball hsubint hρid hρfr hρsurj hτ0 hτ1 hθ hWfr hinj hqsrc hfr
    hApoly hBpoly hunion hρA hτA hρB hmapA hmapB hBbd hc hle hge
    ((hWdisp _ hθ0J).mpr hθ0) ((hWdisp _ hθ1J).mpr hθ1) ?_ hS hbS hdS hslab
  intro z hz hz0
  exact hJW ⟨hz, (hWdisp z hz).mp hz0⟩

end DifferentialGeometry.Topology.PiecewiseLinear
