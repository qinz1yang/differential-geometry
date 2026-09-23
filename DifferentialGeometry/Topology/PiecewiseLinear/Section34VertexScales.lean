import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdgeFinite

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}

theorem exists_section34_vertex_scales_with_sum_margins
    (hends : ∀ e, (e.1 : Set Ea) =
      ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (cap : Section34VertexIndex 𝒦 𝒦' → ℝ) (hcap : ∀ w, 0 < cap w)
    (margin : Section34EdgeIndex 𝒦 𝒦' → ℝ) (hmargin : ∀ e, 0 < margin e) :
    ∃ ε : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < ε w) ∧ (∀ w, ε w < cap w) ∧
      ∀ e, ε (ends e).1 + ε (ends e).2 < margin e := by
  classical
  have hw (w : Section34VertexIndex 𝒦 𝒦') :
      ∃ r : ℝ, 0 < r ∧ r < cap w ∧
        ∀ e, w = (ends e).1 ∨ w = (ends e).2 → r < margin e / 2 := by
    let I := {e : Section34EdgeIndex 𝒦 𝒦' // w = (ends e).1 ∨ w = (ends e).2}
    let : Finite I := section34_incident_edges_finite hends w
    let d : Option I → ℝ := fun i => i.elim (cap w) (fun e => margin e.1 / 2)
    have hd : ∀ i, 0 < d i := by
      intro i
      cases i with
      | none => exact hcap w
      | some e => exact half_pos (hmargin e.1)
    obtain ⟨i, hi⟩ := Finite.exists_min d
    refine ⟨d i / 2, half_pos (hd i), ?_, ?_⟩
    · exact (half_lt_self (hd i)).trans_le (hi none)
    · intro e he
      exact (half_lt_self (hd i)).trans_le (hi (some ⟨e, he⟩))
  choose ε hε hcapε hmarginε using hw
  refine ⟨ε, hε, hcapε, ?_⟩
  intro e
  have ha := hmarginε (ends e).1 e (Or.inl rfl)
  have hb := hmarginε (ends e).2 e (Or.inr rfl)
  linarith

variable {M₂ : Type u} [MetricSpace M₂]
  {h : M₁ → M₂} {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε δ : Section34VertexIndex 𝒦 𝒦' → ℝ}

theorem section34CellThickening_mono (hδε : ∀ w, δ w ≤ ε w)
    (w : Section34VertexIndex 𝒦 𝒦') :
    section34CellThickening h Cp δ w ⊆ section34CellThickening h Cp ε w := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp hy
  exact mem_iUnion₂.mpr ⟨x, hx, Metric.ball_subset_ball (hδε w) hxy⟩

variable [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem Section34VertexPreparation.mono
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends
      Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hδ : ∀ w, 0 < δ w) (hδε : ∀ w, δ w ≤ ε w) :
    Section34VertexPreparation U 𝒦 𝒦' h src Q ends
      Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ δ := by
  rcases hprep with
    ⟨_, hcc, hsub, hchart, hcp, hmark, hQ, hlf, hends, hcircle, hreg, htorus,
      hincident, hdisj, haa, hbb, htb, hbs, hbc, hcirclebc, hab, hcomp, hgen,
      hball, hballSum, hccDist, hcpDist, hbbDist, haaDist, hbbDist', habDist,
      hbccDist, hbcsDist, hgraphDist, hmarkDist, hforeignDist, hdisjDist, hsnDist,
      hcore, hcover, hstable, hcoreDist, hvertexDist, hnonadj, hoverlap⟩
  have hsum (v w : Section34VertexIndex 𝒦 𝒦') : δ v + δ w ≤ ε v + ε w :=
    add_le_add (hδε v) (hδε w)
  refine ⟨hδ, hcc, hsub, hchart, hcp, hmark, hQ, hlf, hends, hcircle, hreg, htorus,
    hincident, hdisj, haa, hbb, htb, hbs, hbc, hcirclebc, hab, hcomp, hgen,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hcore, hcover, ?_, ?_, ?_, hnonadj, ?_⟩
  · intro w x hx
    exact (Metric.ball_subset_ball (hδε w)).trans (hball w x hx)
  · intro e x hx
    exact (Metric.ball_subset_ball (hsum _ _)).trans (hballSum e x hx)
  · intro w x hx y hy
    exact (hδε w).trans_lt (hccDist w x hx y hy)
  · intro w x hx y hy
    exact (hδε w).trans_lt (hcpDist w x hx y hy)
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
    exact (hδε w).trans_lt (hgraphDist e w hw x hx y hy)
  · intro e w x hx y hy
    exact (hsum _ _).trans_lt (hmarkDist e w x hx y hy)
  · intro e w hwa hwb x hx y hy
    exact (hsum _ _).trans_lt (hforeignDist e w hwa hwb x hx y hy)
  · intro w w' hd x hx y hy
    exact (hsum _ _).trans_lt (hdisjDist w w' hd x hx y hy)
  · intro e d hed x hx y hy
    exact (hsum _ _).trans_lt (hsnDist e d hed x hx y hy)
  · intro w F hF hdist
    exact hstable w F hF (fun z hz => (hdist z hz).trans_le (hδε w))
  · intro e w x hx y hy
    exact (hsum _ _).trans_lt (hcoreDist e w x hx y hy)
  · intro w w' hww' x hx y hy
    exact (hδε w').trans_lt (hvertexDist w w' hww' x hx y hy)
  · intro e d hed
    exact (hoverlap e d hed).mono
      (inter_subset_inter (section34CellThickening_mono hδε _)
        (section34CellThickening_mono hδε _))
      (inter_subset_inter (section34CellThickening_mono hδε _)
        (section34CellThickening_mono hδε _))

end DifferentialGeometry.Topology.PiecewiseLinear
