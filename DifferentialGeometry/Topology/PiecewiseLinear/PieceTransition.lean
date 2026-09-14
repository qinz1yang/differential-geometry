import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronIn

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem PLPieceIn.isPiecewiseAffineOn_transition {Y : Set X} (T₁ : PLPieceIn E n X Y)
    (T₂ : PLPieceIn F n X Y) :
    IsPiecewiseAffineOn (Function.invFunOn T₂.map T₂.complex.space ∘ T₁.map)
      T₁.complex.space := by
  intro x hx
  let e := chartAt (EuclideanSpace ℝ (Fin n)) (T₁.map x)
  have he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X := chart_mem_atlas _ _
  have hxe : T₁.map x ∈ e.source := mem_chart_source _ _
  have h₁ := T₁.isPiecewiseAffineOn_chart e he x ⟨hx, hxe⟩
  have h₂ := T₂.isPiecewiseAffineOn_chart_symm e he (e (T₁.map x))
    ⟨e.map_source hxe, by
      change e.symm (e (T₁.map x)) ∈ Y
      rw [e.left_inv hxe]
      exact T₁.bijOn.mapsTo hx⟩
  have h := h₂.comp (f := e ∘ T₁.map) (x := x) h₁
  have hsub : T₁.complex.space ∩ T₁.map ⁻¹' e.source ⊆
      (e ∘ T₁.map) ⁻¹' (e.target ∩ e.symm ⁻¹' Y) := by
    intro z hz
    refine ⟨e.map_source hz.2, ?_⟩
    change e.symm (e (T₁.map z)) ∈ Y
    rw [e.left_inv hz.2]
    exact T₁.bijOn.mapsTo hz.1
  rw [inter_eq_left.mpr hsub] at h
  have hlocal : IsPiecewiseAffineWithinAt
      (Function.invFunOn T₂.map T₂.complex.space ∘ T₁.map)
      (T₁.complex.space ∩ T₁.map ⁻¹' e.source) x := h.congr fun z hz => by
    simp only [Function.comp_apply]
    rw [e.left_inv hz.2]
  obtain ⟨O, hO, hpre⟩ := continuousOn_iff'.mp T₁.continuousOn e.source e.open_source
  have hset : T₁.complex.space ∩ T₁.map ⁻¹' e.source = T₁.complex.space ∩ O := by
    rw [inter_comm, hpre, inter_comm]
  have hxO : x ∈ O := (hpre ▸ (show x ∈ T₁.map ⁻¹' e.source ∩ T₁.complex.space from
    ⟨hxe, hx⟩)).1
  rw [hset] at hlocal
  exact hlocal.of_inter_of_mem_nhds (hO.mem_nhds hxO)

theorem PLPieceIn.isPLHomeomorphOn_transition {Y : Set X} (T₁ : PLPieceIn E n X Y)
    (T₂ : PLPieceIn F n X Y) :
    IsPLHomeomorphOn (Function.invFunOn T₂.map T₂.complex.space ∘ T₁.map)
      T₁.complex.space T₂.complex.space := by
  have h₂ : BijOn (Function.invFunOn T₂.map T₂.complex.space) Y T₂.complex.space :=
    T₂.bijOn.invOn_invFunOn.symm.bijOn T₂.bijOn.surjOn.mapsTo_invFunOn T₂.bijOn.mapsTo
  have hbij := h₂.comp T₁.bijOn
  refine ⟨hbij, T₁.isPiecewiseAffineOn_transition T₂, ?_⟩
  refine (T₂.isPiecewiseAffineOn_transition T₁).congr fun z hz => ?_
  have h₁ : Function.invFunOn
      (Function.invFunOn T₂.map T₂.complex.space ∘ T₁.map) T₁.complex.space z ∈
      T₁.complex.space := hbij.surjOn.mapsTo_invFunOn hz
  have h₃ : Function.invFunOn T₁.map T₁.complex.space (T₂.map z) ∈ T₁.complex.space :=
    T₁.bijOn.surjOn.mapsTo_invFunOn (T₂.bijOn.mapsTo hz)
  apply hbij.injOn h₁ h₃
  rw [hbij.invOn_invFunOn.2 hz]
  change z = Function.invFunOn T₂.map T₂.complex.space
    (T₁.map (Function.invFunOn T₁.map T₁.complex.space (T₂.map z)))
  rw [T₁.bijOn.invOn_invFunOn.2 (T₂.bijOn.mapsTo hz), T₂.bijOn.invOn_invFunOn.1 hz]

theorem IsPolyhedralBall.isPLBall_of_piece {m : ℕ} {P : Set X}
    (hB : IsPolyhedralBall (n := n) m P) (T : PLPiece n X P) :
    IsPLBall m T.piece.complex.space := by
  obtain ⟨T₀, hT₀⟩ := hB
  exact hT₀.of_isPLHomeomorphOn (T₀.piece.isPLHomeomorphOn_transition T.piece)

theorem IsPolyhedralSphere.isPLSphere_of_piece {m : ℕ} {P : Set X}
    (hS : IsPolyhedralSphere (n := n) m P) (T : PLPiece n X P) :
    IsPLSphere m T.piece.complex.space := by
  obtain ⟨T₀, hT₀⟩ := hS
  exact hT₀.of_isPLHomeomorphOn (T₀.piece.isPLHomeomorphOn_transition T.piece)

theorem isPolyhedralBall_of_pieceIn {m : ℕ} {P : Set X} (T : PLPieceIn E n X P)
    (hT : IsPLBall m T.complex.space) : IsPolyhedralBall (n := n) m P := by
  obtain ⟨T'⟩ := T.exists_pLPiece
  exact ⟨T', hT.of_isPLHomeomorphOn (T.isPLHomeomorphOn_transition T'.piece)⟩

theorem isPolyhedralSphere_of_pieceIn {m : ℕ} {P : Set X} (T : PLPieceIn E n X P)
    (hT : IsPLSphere m T.complex.space) : IsPolyhedralSphere (n := n) m P := by
  obtain ⟨T'⟩ := T.exists_pLPiece
  exact ⟨T', hT.of_isPLHomeomorphOn (T.isPLHomeomorphOn_transition T'.piece)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
