import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierSubfamilyDescent
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RegularCircleCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusProduct

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_essential_subfamily_motion
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ I : Set (Fin (cnt e)), I.Nonempty ∧
      (∀ j : Fin (cnt e), CarriesFundamentalGroupOnto (Pg e j.val) (Sp e) → j ∈ I) ∧
      (∀ j : I, CarriesFundamentalGroupOnto (Pg e j.1.val) (Sp e)) ∧
      ∃ (K : Set M₂) (ψ : M₂ ≃ₜ M₂), IsCompact K ∧ K ⊆ interior (Sp e) ∧ EqOn ψ id Kᶜ ∧
        IsPLOn 3 3 ψ (interior (G (ends e).1 '' Cc (ends e).1)) ∧
        Disjoint K (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) ∧
        Disjoint K (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) ∧
        Disjoint K (closure (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e)) ∧
        (∀ j : I, Disjoint K (Pg e j.1.val)) ∧
        (∀ j : I, ∀ x ∈ Pg e j.1.val, ψ =ᶠ[𝓝 x] id) ∧
        G (ends e).1 '' CpBd (ends e).1 ∩ ψ '' (G (ends e).2 '' CpBd (ends e).2) =
          ⋃ j : I, Pg e j.1.val := by
  obtain ⟨k, hk, hcarry, -, -⟩ :=
    exists_section34_piercing_circle_carrying_generators hprep hpack e
  obtain ⟨P, u, R, f, hP, hu, huP, hRfin, hRP, huR, hR, hf, hfends⟩ :=
    exists_section34_outer_tube_cylindrical_model hprep hpack e
  let _ : Finite R.faces := hRfin.to_subtype
  have hRT := hf.isTopologicalSolidTorus_of_eq_ends (isPLBall_stdSimplex 2) hfends
  have hTS := section34_inner_tube_subset_interior_outer hprep hpack e
  have hann := section34_piercing_annuli hprep hpack e
  obtain ⟨-, -, hCpCc, -, hCp, -, -, -, -, -, -, -, -, -, hAa, hBb, -⟩ := id hprep
  obtain ⟨-, -, -, htube, -, -, hbound, -, hBaS, -, hGp, -, -, -, -, -, hcount,
    hPg, hdis, -⟩ := id hpack
  have hAB : Aa e ⊆ CpBd (ends e).1 := (hAa e).1 ▸ inter_subset_left
  have hBB := (hBb e).1
  have hAaB := image_mono (f := G (ends e).1) hAB
  have hBaB := image_mono (f := G (ends e).2) hBB
  have hAT : G (ends e).1 '' Aa e ⊆ interior (u '' R.space) := by
    rw [huR]
    apply Subset.trans _ hTS
    rw [(htube e).2]
    exact image_mono ((hAa e).1 ▸ inter_subset_right)
  have hBT : G (ends e).2 '' Bb e ⊆ interior (u '' R.space) := huR.symm ▸ (hBaS e).1
  have hAP : G (ends e).1 '' Cp (ends e).1 ⊆ u '' P := by
    rw [huP]
    exact image_mono (hCpCc _).2.1
  have hJA (j : Fin (cnt e)) : Pg e j.val ⊆ G (ends e).1 '' Aa e :=
    fun _ hx => image_mono sdiff_subset ((hPg e j.val j.isLt).2 hx).1
  have hJB (j : Fin (cnt e)) : Pg e j.val ⊆ G (ends e).2 '' Bb e :=
    fun _ hx => image_mono sdiff_subset ((hPg e j.val j.isLt).2 hx).2
  have hArim (j : Fin (cnt e)) : Disjoint (Pg e j.val)
      (G (ends e).1 '' Ab₀ e ∪ G (ends e).1 '' Ab₁ e) := by
    rw [← image_union]
    have hsub : Pg e j.val ⊆
        G (ends e).1 '' Aa e \ G (ends e).1 '' (Ab₀ e ∪ Ab₁ e) := by
      rw [← ((hGp _).injOn.mono (hAB.trans (hCp _).boundary_subset)).image_sdiff_subset
        (union_subset (hAa e).2.first_subset (hAa e).2.second_subset)]
      exact fun _ hx => ((hPg e j.val j.isLt).2 hx).1
    exact disjoint_left.mpr fun _ hx hy => (hsub hx).2 hy
  have hBrim (j : Fin (cnt e)) : Disjoint (Pg e j.val)
      (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    rw [← image_union]
    have hsub : Pg e j.val ⊆
        G (ends e).2 '' Bb e \ G (ends e).2 '' (Bb₀ e ∪ Bb₁ e) := by
      rw [← ((hGp _).injOn.mono (hBB.trans (hCp _).boundary_subset)).image_sdiff_subset
        (union_subset (hBb e).2.first_subset (hBb e).2.second_subset)]
      exact fun _ hx => ((hPg e j.val j.isLt).2 hx).2
    exact disjoint_left.mpr fun _ hx hy => (hsub hx).2 hy
  have hpair : Pairwise fun j l : Fin (cnt e) => Disjoint (Pg e j.val) (Pg e l.val) :=
    fun j l hjl => hdis e j.val j.isLt l.val l.isLt (fun heq => hjl (Fin.ext heq))
  have htrace : G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 =
      ⋃ j : Fin (cnt e), Pg e j.val := by
    apply Subset.antisymm
    · intro x hx
      have hxAB := (hbound e hx).1
      have hxann := (hcount e).2.subset
        ⟨image_mono sdiff_subset hxAB.1, image_mono sdiff_subset hxAB.2⟩
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxann
      exact mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩
    · intro x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact ⟨hAaB (hJA j hxj), hBaB (hJB j hxj)⟩
  obtain ⟨I, hkI, hcarriers, hess, K, ψ, hK, hKS, hfix, hψ, hKA, hKB, hout,
    hkeep, hnear, hcancel⟩ :=
    hu.exists_carrier_subfamily_without_annular_disks hP R hR hRP hRT
      ((hCp _).image (hGp _)) hAP ((hCp _).image (hGp _)) hann.1 hAaB hAT
      hann.2 hBaB hBT (fun j : Fin (cnt e) => (hPg e j.val j.isLt).1)
      hJA hJB hArim hBrim hpair htrace ⟨k, hk⟩ (huR.symm ▸ hcarry)
  rw [huR] at hKS hcarriers
  rw [huP] at hψ
  rw [← image_union] at hKA hKB
  refine ⟨I, ⟨⟨k, hk⟩, hkI⟩, hcarriers, ?_, K, ψ, hK, hKS, hfix, hψ,
    hKA, hKB, hout, hkeep, hnear, hcancel⟩
  intro j
  exact (section34_piercing_generators_of_essential_first hprep hpack e j.1.isLt
    (hess j)).1

end DifferentialGeometry.Topology.PiecewiseLinear
