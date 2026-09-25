import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PLCompactModelEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CapDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.SphereInnermostDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_innermost_boundary_disk {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B : Set M}
    (hS : IsPLCellOn 3 S B) {ι : Type*} [Finite ι] [Nonempty ι] {J : ι → Set M}
    (hJ : ∀ i, IsPolyhedralSphere (n := 3) 1 (J i)) (hJB : ∀ i, J i ⊆ B)
    (hdisj : Pairwise fun i j => Disjoint (J i) (J j)) :
    ∃ (i : ι) (D : Set M), IsPLCellOn 2 D (J i) ∧ D ⊆ B ∧
      IsConnected (D \ J i) ∧ ∀ j, j ≠ i → Disjoint D (J j) := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hJP : ∀ i, J i ⊆ u '' P :=
    fun i => (hJB i).trans (hB ▸ image_mono hfront)
  let J' : ι → Set (EuclideanSpace ℝ (Fin 3)) := fun i => Function.invFunOn u P '' J i
  have hJ' : ∀ i, IsPLSphere 1 (J' i) :=
    fun i => hu.isPLSphere_invFunOn_image (hJ i) (hJP i)
  have hJ'S : ∀ i, J' i ⊆ frontier P := by
    rintro i _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ : x ∈ u '' frontier P := hB ▸ hJB i hx
    rw [hu.injOn.leftInvOn_invFunOn (hfront hy)]
    exact hy
  have hsec : ∀ i, u '' J' i = J i := by
    intro i
    dsimp only [J']
    rw [image_image]
    exact (image_congr fun x hx =>
      hu.injOn.bijOn_image.invOn_invFunOn.2 (hJP i hx)).trans (image_id' _)
  have hdisj' : Pairwise fun i j => Disjoint (J' i) (J' j) := by
    intro i j hij
    refine disjoint_left.mpr fun x hxi hxj => ?_
    exact disjoint_left.mp (hdisj hij)
      ((hsec i).subset (mem_image_of_mem u hxi))
      ((hsec j).subset (mem_image_of_mem u hxj))
  obtain ⟨i, D, q, hq, hDS, hqJ, hDj⟩ :=
    hP.isPLSphere_frontier.exists_innermost_disk hJ' hJ'S hdisj'
  have hDP : D ⊆ P := hDS.trans hfront
  have hJD : J' i ⊆ D := by
    rw [← hqJ, ← hq.image_eq]
    exact image_mono fun x hx => hx.1
  have hmodel := isPLCellOn_id_of_isPLBall hq
  have hDpoly : IsPolyhedron D := IsPLBall.isPolyhedron ⟨q, hq⟩
  have huD : IsPLHomeomorphInto 3 u D :=
    (hu.isPLOn.mono_of_isPolyhedron hDpoly hDP).isPLHomeomorphInto_model
      hDpoly.isCompact (hu.injOn.mono hDP)
  have hcell : IsPLCellOn 2 (u '' D) (J i) := by
    have hcell := hmodel.image huD
    rwa [hqJ, hsec] at hcell
  have hconn : IsConnected (u '' D \ J i) := by
    have hconn : IsConnected (D \ J' i) :=
      hqJ ▸ hq.isConnected_sdiff_image_stdSimplexBoundary
    have himg := hconn.image u (hu.continuousOn.mono (sdiff_subset.trans hDP))
    rwa [(hu.injOn.mono hDP).image_sdiff_subset hJD, hsec] at himg
  refine ⟨i, u '' D, hcell, hB ▸ image_mono hDS, hconn, ?_⟩
  intro j hji
  refine disjoint_left.mpr ?_
  rintro _ ⟨x, hx, rfl⟩ hxJ
  have hxJ' : x ∈ J' j :=
    ⟨u x, hxJ, hu.injOn.leftInvOn_invFunOn (hDP hx)⟩
  exact disjoint_left.mp (hDj j hji) hx hxJ'

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

theorem exists_section34_boundary_innermost_disk
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ (i : ℕ) (D : Set M₂), i < cnt e ∧ IsPLCellOn 2 D (Pg e i) ∧
      D ⊆ G (ends e).2 '' CpBd (ends e).2 ∧
      D ∩ G (ends e).1 '' CpBd (ends e).1 = Pg e i ∧ IsConnected (D \ Pg e i) ∧
      (D \ Pg e i ⊆ interior (G (ends e).1 '' Cp (ends e).1) ∨
        Disjoint (D \ Pg e i) (G (ends e).1 '' Cp (ends e).1)) := by
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, hbd, -, -, -, hGCp, -, -, -, -, -, hcnt, hPg, hPgdis, -⟩ := hpack
  have hAaBd : Aa e ⊆ CpBd (ends e).1 := by
    rw [(hAa e).1]
    exact inter_subset_left
  have hJleft : ∀ i < cnt e, Pg e i ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    fun i hi x hx => image_mono (sdiff_subset.trans hAaBd) ((hPg e i hi).2 hx).1
  have hJright : ∀ i < cnt e, Pg e i ⊆ G (ends e).2 '' CpBd (ends e).2 :=
    fun i hi x hx => image_mono (sdiff_subset.trans (hBb e).1) ((hPg e i hi).2 hx).2
  let _ : Nonempty (Fin (cnt e)) := ⟨⟨0, (hcnt e).1⟩⟩
  obtain ⟨i, D, hD, hDB, hconn, hDj⟩ :=
    ((hCp (ends e).2).image (hGCp (ends e).2)).exists_innermost_boundary_disk
      (J := fun j : Fin (cnt e) => Pg e j)
      (fun j => (hPg e j j.2).1) (fun j => hJright j j.2)
      (fun j k hjk => hPgdis e j j.2 k k.2 (fun hjk' => hjk (Fin.ext hjk')))
  have hmeet : D ∩ G (ends e).1 '' CpBd (ends e).1 = Pg e i := by
    apply Subset.antisymm
    · intro x hx
      have htrace : x ∈ G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e :=
        ⟨image_mono sdiff_subset (hbd e ⟨hx.2, hDB hx.1⟩).1.1,
          image_mono sdiff_subset (hbd e ⟨hx.2, hDB hx.1⟩).1.2⟩
      rw [(hcnt e).2] at htrace
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp htrace
      by_cases hji : j = i
      · simpa only [hji] using hxj
      · exact (disjoint_left.mp (hDj ⟨j, hj⟩ (fun heq => hji (congrArg Fin.val heq)))
          hx.1 hxj).elim
    · exact fun x hx => ⟨hD.boundary_subset hx, hJleft i i.2 hx⟩
  have hA := (hCp (ends e).1).image (hGCp (ends e).1)
  have havoid : Disjoint (D \ Pg e i) (frontier (G (ends e).1 '' Cp (ends e).1)) := by
    rw [← hA.boundary_eq_frontier]
    exact disjoint_left.mpr fun x hx hxA => hx.2 (hmeet.subset ⟨hx.1, hxA⟩)
  refine ⟨i, D, i.2, hD, hDB, hmeet, hconn, ?_⟩
  by_cases hnonempty : ((D \ Pg e i) ∩ G (ends e).1 '' Cp (ends e).1).Nonempty
  · have hsub := IsPreconnected.subset_of_disjoint_frontier hconn.isPreconnected hnonempty havoid
    refine Or.inl fun x hx => by_contra fun hnot => ?_
    exact disjoint_left.mp havoid hx
      (hA.isCompact.isClosed.frontier_eq ▸ ⟨hsub hx, hnot⟩)
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnonempty))

end DifferentialGeometry.Topology.PiecewiseLinear
