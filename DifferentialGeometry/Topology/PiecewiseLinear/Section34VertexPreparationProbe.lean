import DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeEnds
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCores
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LensImages
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LensIsolation
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnStabilityScales

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U W : Set M₁} {h : M₁ → M₂}
  {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
  {Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34VertexPreparation [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQint : ∀ w, h '' src (Section34Label.vertexBall w) ⊆ interior (Q w))
    (hCchart : ∀ w : Section34VertexIndex 𝒦 𝒦', ∃ c ∈ (plGroupoid 3).maximalAtlas M₂,
      h '' src (Section34Label.vertexBall w) ⊆ c.source) :
    ∃ (Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁)
      (ends : Section34EdgeIndex 𝒦 𝒦' →
        Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
      (Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁)
      (ε : Section34VertexIndex 𝒦 𝒦' → ℝ),
      Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
        Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε := by
  obtain ⟨ends, hends⟩ := exists_section34_edge_ends hframe
  have exists_locally_finite_pierced_cells_with_isolated_lenses :
      ∃ (Cp CpBd Cc CcBd : Section34VertexIndex 𝒦 𝒦' → Set M₁),
      (∀ w, IsPLCellOn 3 (Cc w) (CcBd w)) ∧
      (∀ w, src (.vertexBall w) ⊆ Cc w ∧ Cp w ⊆ Cc w ∧ Cc w ⊆ U) ∧
      (∀ w, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, h '' Cc w ⊆ c.source) ∧
      (∀ w, IsPLCellOn 3 (Cp w) (CpBd w)) ∧
      (∀ w, simplexBody 𝒦' w.1 ⊆ interior (Cp w)) ∧
      (∀ w, h '' Cc w ⊆ interior (Q w)) ∧
      (∀ x ∈ ⋃ w, Cc w, ∃ V ∈ 𝓝 x, {w | (Cc w ∩ V).Nonempty}.Finite) ∧
      (∀ e, IsPolyhedralSphere (n := 3) 1 (CpBd (ends e).1 ∩ CpBd (ends e).2) ∧
          CpBd (ends e).1 ∩ CpBd (ends e).2 ⊆ src (.splitDisk e)) ∧
      (∀ w w', w ≠ w' → (¬ ∃ e : Section34EdgeIndex 𝒦 𝒦',
            (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1)) →
          Disjoint (Cp w) (Cp w')) ∧
      (∀ w, Cp w ⊆ interior (Cc w)) ∧
      graphSkeletonSpace 𝒦 ⊆ (⋃ w, interior (Cp w)) ∧
      (LocallyFinite fun w => {x : U | (x : M₁) ∈ Cp w}) ∧
      (∀ e d, e ≠ d → Disjoint (Cp (ends e).1 ∩ Cp (ends e).2)
        (Cp (ends d).1 ∩ Cp (ends d).2)) ∧
      ∀ w w', w ≠ w' → Disjoint (Cp w') (simplexBody 𝒦' w.1) := by
    sorry
  obtain ⟨Cp, CpBd, Cc, CcBd, hcc, hsub, hchart, hcp, hvertex, hQ, hLF, hcircle,
    hnonadj, hCpCc, hcover, hCpLF, hlens, hvdisj⟩ :=
    exists_locally_finite_pierced_cells_with_isolated_lenses
  have hCpU : ∀ w, Cp w ⊆ U := fun w => (hsub w).2.1.trans (hsub w).2.2
  obtain ⟨Kcore, hcore, hcoreCover⟩ :=
    exists_section34_graph_cores_of_isPLCellOn hcp hCpU hvertex hcover
  have exists_marked_nested_piercing_annuli :
      ∃ (Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁),
      (∀ e, IsLocallyFiniteRegularNeighborhoodOf (n := 3) (Sn e)
            (CpBd (ends e).1 ∩ CpBd (ends e).2) U ∧
          IsLocallyFiniteRegularNeighborhoodOf (n := 3) (Tn e)
            (CpBd (ends e).1 ∩ CpBd (ends e).2) U) ∧
      (∀ e, Tn e ⊆ interior (Sn e) ∧ IsTopologicalSolidTorus (Sn e) ∧
          IsTopologicalSolidTorus (Tn e) ∧ Disjoint (Sn e) (graphSkeletonSpace 𝒦)) ∧
      (∀ e, ∀ w, w = (ends e).1 ∨ w = (ends e).2 → Sn e ⊆ Cc w) ∧
      (∀ e d, e ≠ d → Disjoint (Sn e) (Sn d)) ∧
      (∀ e, Aa e = CpBd (ends e).1 ∩ Tn e ∧ IsAnnulusOn (Aa e) (Ab₀ e) (Ab₁ e)) ∧
      (∀ e, Bb e ⊆ CpBd (ends e).2 ∧ IsAnnulusOn (Bb e) (Bb₀ e) (Bb₁ e)) ∧
      (∀ e, Tn e ∩ CpBd (ends e).2 ⊆ Bb e \ (Bb₀ e ∪ Bb₁ e)) ∧
      (∀ e, Bb e ⊆ interior (Sn e) ∧ Bb₀ e ∪ Bb₁ e ⊆ Sn e \ Tn e) ∧
      (∀ e, IsAnnulusOn (Bc e) (Bc₀ e) (Bc₁ e) ∧ Bc e ⊆ Bb e ∩ interior (Tn e)) ∧
      (∀ e, CpBd (ends e).1 ∩ CpBd (ends e).2 ⊆ Bc e \ (Bc₀ e ∪ Bc₁ e)) ∧
      (∀ e, Ab₀ e ⊆ interior (Cp (ends e).2) ∧ Ab₁ e ∩ Cp (ends e).2 = ∅) ∧
      (∀ e, (∃ y₀ ∈ Bb e ∩ Cp (ends e).1, ∀ z ∈ Bb e ∩ Cp (ends e).1, z ∉ Tn e →
            z ∈ connectedComponentIn (Bb e ∩ Cp (ends e).1) y₀) ∧
          ∃ y₀ ∈ Bb e \ Cp (ends e).1, ∀ z ∈ Bb e \ Cp (ends e).1, z ∉ Tn e →
            z ∈ connectedComponentIn (Bb e \ Cp (ends e).1) y₀) ∧
      (∀ e, CarriesFundamentalGroupOnto (Ab₀ e) (Tn e) ∧
          CarriesFundamentalGroupOnto (Ab₁ e) (Tn e) ∧
          CarriesFundamentalGroupOnto (Ab₀ e) (Sn e)) ∧
      (LocallyFinite fun e => {x : U | (x : M₁) ∈ Sn e}) ∧
      (∀ e w, Disjoint (Sn e) (Kcore w)) ∧
      ∀ e w, w ≠ (ends e).1 → w ≠ (ends e).2 → Disjoint (Sn e) (CpBd w) := by
    sorry
  obtain ⟨Sn, Tn, Aa, Ab₀, Ab₁, Bb, Bb₀, Bb₁, Bc, Bc₀, Bc₁,
    hreg, htorus, hincident, htubes, haa, hbb, htb, hbs, hbc, hcirclebc, hab, hcomp, hgen,
    hSnLF, hSnK, hSnBd⟩ := exists_marked_nested_piercing_annuli
  have exists_vertex_scales_with_sum_margins :
      ∃ μ : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < μ w) ∧
      (∀ w, ∀ x ∈ Cc w, Metric.ball (h x) (μ w) ⊆ interior (Q w)) ∧
      (∀ e, ∀ x ∈ Sn e, Metric.ball (h x) (μ (ends e).1 + μ (ends e).2) ⊆
          interior (Q (ends e).1) ∩ interior (Q (ends e).2)) ∧
      (∀ w, ∀ x ∈ CcBd w, ∀ y ∈ h '' simplexBody 𝒦' w.1, μ w < dist (h x) y) ∧
      (∀ w, ∀ x ∈ CpBd w, ∀ y ∈ h '' simplexBody 𝒦' w.1, μ w < dist (h x) y) ∧
      (∀ e, ∀ x ∈ Bb₀ e ∪ Bb₁ e, ∀ y ∈ Tn e,
          μ (ends e).1 + μ (ends e).2 < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ CpBd (ends e).1 \ (Aa e \ (Ab₀ e ∪ Ab₁ e)), ∀ y ∈ CpBd (ends e).2,
          μ (ends e).1 + μ (ends e).2 < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ CpBd (ends e).1, ∀ y ∈ CpBd (ends e).2 \ (Bb e \ (Bb₀ e ∪ Bb₁ e)),
          μ (ends e).1 + μ (ends e).2 < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ Ab₁ e, ∀ y ∈ Cp (ends e).2,
          μ (ends e).1 + μ (ends e).2 < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ Bb e, ∀ y ∈ Cc (ends e).1 \ interior (Sn e),
          μ (ends e).1 + μ (ends e).2 < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ Bc₀ e ∪ Bc₁ e, ∀ y ∈ Sn e \ interior (Tn e),
          μ (ends e).1 + μ (ends e).2 < dist (h x) (h y)) ∧
      (∀ e, ∀ w, w = (ends e).1 ∨ w = (ends e).2 →
          ∀ x ∈ Sn e, ∀ y ∈ graphSkeletonSpace 𝒦, μ w < dist (h x) (h y)) ∧
      (∀ e w, ∀ x ∈ Sn e, ∀ y ∈ simplexBody 𝒦' w.1,
          μ (ends e).1 + μ w < dist (h x) (h y)) ∧
      (∀ e w, w ≠ (ends e).1 → w ≠ (ends e).2 → ∀ x ∈ Sn e, ∀ y ∈ CpBd w,
          μ (ends e).1 + μ w < dist (h x) (h y)) ∧
      (∀ w w', Disjoint (Cp w) (Cp w') → ∀ x ∈ Cp w, ∀ y ∈ Cp w',
          μ w + μ w' < dist (h x) (h y)) ∧
      (∀ e d, e ≠ d → ∀ x ∈ Sn e, ∀ y ∈ Sn d,
          μ (ends e).1 + μ (ends d).1 < dist (h x) (h y)) ∧
      (∀ e w, ∀ x ∈ Sn e, ∀ y ∈ Kcore w, μ (ends e).1 + μ w < dist (h x) (h y)) ∧
      (∀ w w', w ≠ w' → ∀ x ∈ Cp w', ∀ y ∈ simplexBody 𝒦' w.1, μ w' < dist (h x) (h y)) := by
    sorry
  obtain ⟨μ, hμ, hball, hballSum, hccDist, hcpDist, hbbDist, haaDist, hbbDist', habDist,
    hbccDist, hbcsDist, hgraphDist, hmarkDist, hforeignDist, hdisjDist, hsnDist,
    hcoreDist, hvertexDist⟩ := exists_vertex_scales_with_sum_margins
  obtain ⟨δ, hδ, hδμ, hstable⟩ := exists_core_stability_scales_lt hh hcp hCpU
    (fun w => (hcore w).1) (fun w => (hcore w).2.2) hμ
  obtain ⟨ε, hε, hεδ, hoverlap⟩ :=
    exists_section34_overlap_isolation_scales hU hh (fun e => (hends e).2.1)
      (fun w => (hcp w).isCompact) hCpU hCpLF hlens δ hδ
  have hεμ (w : Section34VertexIndex 𝒦 𝒦') : ε w ≤ μ w :=
    (hεδ w).le.trans (hδμ w).le
  have hsum (v w : Section34VertexIndex 𝒦 𝒦') : ε v + ε w ≤ μ v + μ w :=
    add_le_add (hεμ v) (hεμ w)
  refine ⟨Cp, CpBd, Cc, CcBd, Kcore, ends, Sn, Tn, Aa, Ab₀, Ab₁, Bb, Bb₀, Bb₁,
    Bc, Bc₀, Bc₁, ε, hε, hcc, hsub, hchart, hcp, hvertex, hQ, hLF, hends, hcircle,
    hreg, htorus, hincident, htubes, haa, hbb, htb, hbs, hbc, hcirclebc, hab, hcomp, hgen,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcore, hcoreCover,
    ?_, ?_, ?_, hnonadj, hoverlap⟩
  · intro w x hx
    exact (Metric.ball_subset_ball (hεμ w)).trans (hball w x hx)
  · intro e x hx
    exact (Metric.ball_subset_ball (hsum _ _)).trans (hballSum e x hx)
  · intro w x hx y hy
    exact (hεμ w).trans_lt (hccDist w x hx y hy)
  · intro w x hx y hy
    exact (hεμ w).trans_lt (hcpDist w x hx y hy)
  · intro e x hx y hy
    exact (hsum _ _).trans_lt (hbbDist e x hx y hy)
  · intro e x hx y hy
    exact (hsum _ _).trans_lt (haaDist e x hx y hy)
  · intro e x hx y hy
    exact (hsum _ _).trans_lt (hbbDist' e x hx y hy)
  · intro e x hx y hy
    exact (hsum _ _).trans_lt (habDist e x hx y hy)
  · intro e x hx y hy
    exact (hsum _ _).trans_lt (hbccDist e x hx y hy)
  · intro e x hx y hy
    exact (hsum _ _).trans_lt (hbcsDist e x hx y hy)
  · intro e w hw x hx y hy
    exact (hεμ w).trans_lt (hgraphDist e w hw x hx y hy)
  · intro e w x hx y hy
    exact (hsum _ _).trans_lt (hmarkDist e w x hx y hy)
  · intro e w hwa hwb x hx y hy
    exact (hsum _ _).trans_lt (hforeignDist e w hwa hwb x hx y hy)
  · intro w w' hw x hx y hy
    exact (hsum _ _).trans_lt (hdisjDist w w' hw x hx y hy)
  · intro e d hed x hx y hy
    exact (hsum _ _).trans_lt (hsnDist e d hed x hx y hy)
  · intro w F hF hclose
    exact hstable w F hF fun x hx => (hclose x hx).trans (hεδ w)
  · intro e w x hx y hy
    exact (hsum _ _).trans_lt (hcoreDist e w x hx y hy)
  · intro w w' hww x hx y hy
    exact (hεμ w').trans_lt (hvertexDist w w' hww x hx y hy)

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
