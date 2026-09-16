import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronIn
import DifferentialGeometry.Topology.PiecewiseLinear.Manifold

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
theorem PLPieceIn.isPiecewiseAffineOn_invFunOn_comp {Y : Set X} (T : PLPieceIn E n X Y)
    {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → X}
    {S : Set (EuclideanSpace ℝ (Fin m))} (hf : IsPLOn m n f S) :
    IsPiecewiseAffineOn (Function.invFunOn T.map T.complex.space ∘ f) (S ∩ f ⁻¹' Y) := by
  intro x hx
  let e := chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  have he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X := chart_mem_atlas _ _
  have hxe : f x ∈ e.source := mem_chart_source _ _
  have h₁ := (hf x hx.1).prop
  change IsPiecewiseAffineWithinAt (e ∘ f) S x at h₁
  have h₂ := T.isPiecewiseAffineOn_chart_symm e he (e (f x))
    ⟨e.map_source hxe, by
      change e.symm (e (f x)) ∈ Y
      rw [e.left_inv hxe]
      exact hx.2⟩
  have hcomp := h₂.comp (f := e ∘ f) (x := x) h₁
  have hfcont : ContinuousOn f S := fun z hz => (hf z hz).continuousWithinAt
  obtain ⟨O, hO, hpre⟩ := continuousOn_iff'.mp hfcont e.source e.open_source
  have hxO : x ∈ O := (hpre ▸ (show x ∈ f ⁻¹' e.source ∩ S from ⟨hxe, hx.1⟩)).1
  have hlocal := hcomp.inter_of_mem_nhds (hO.mem_nhds hxO)
  have hdomain :
      (S ∩ (e ∘ f) ⁻¹' (e.target ∩ e.symm ⁻¹' Y)) ∩ O = (S ∩ f ⁻¹' Y) ∩ O := by
    ext z
    constructor
    · rintro ⟨⟨hzS, hztarget, hzY⟩, hzO⟩
      have hzsource : f z ∈ e.source := by
        have hz : z ∈ f ⁻¹' e.source ∩ S := by
          rw [hpre]
          exact ⟨hzO, hzS⟩
        exact hz.1
      refine ⟨⟨hzS, ?_⟩, hzO⟩
      change e.symm (e (f z)) ∈ Y at hzY
      change f z ∈ Y
      simpa only [e.left_inv hzsource] using hzY
    · rintro ⟨⟨hzS, hzY⟩, hzO⟩
      have hzsource : f z ∈ e.source := by
        have hz : z ∈ f ⁻¹' e.source ∩ S := by
          rw [hpre]
          exact ⟨hzO, hzS⟩
        exact hz.1
      refine ⟨⟨hzS, e.map_source hzsource, ?_⟩, hzO⟩
      change f z ∈ Y at hzY
      change e.symm (e (f z)) ∈ Y
      simpa only [e.left_inv hzsource] using hzY
  rw [hdomain] at hlocal
  apply (hlocal.congr fun z hz => ?_).of_inter_of_mem_nhds (hO.mem_nhds hxO)
  have hzsource : f z ∈ e.source := by
    have hz' : z ∈ f ⁻¹' e.source ∩ S := by
      rw [hpre]
      exact ⟨hz.2, hz.1.1⟩
    exact hz'.1
  simp only [Function.comp_apply, e.left_inv hzsource]

omit [FiniteDimensional ℝ F] in
theorem PLPieceIn.isPiecewiseAffineOn_transition_of_subset {Y₁ Y₂ : Set X} (T₁ : PLPieceIn E n X Y₁)
    (T₂ : PLPieceIn F n X Y₂) (hY : Y₁ ⊆ Y₂) :
    IsPiecewiseAffineOn (Function.invFunOn T₂.map T₂.complex.space ∘ T₁.map)
      T₁.complex.space := by
  intro x hx
  let e := chartAt (EuclideanSpace ℝ (Fin n)) (T₁.map x)
  have he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X := chart_mem_atlas _ _
  have hxe : T₁.map x ∈ e.source := mem_chart_source _ _
  have h₁ := T₁.isPiecewiseAffineOn_chart e he x ⟨hx, hxe⟩
  have h₂ := T₂.isPiecewiseAffineOn_chart_symm e he (e (T₁.map x))
    ⟨e.map_source hxe, by
      change e.symm (e (T₁.map x)) ∈ Y₂
      rw [e.left_inv hxe]
      exact hY (T₁.bijOn.mapsTo hx)⟩
  have h := h₂.comp (f := e ∘ T₁.map) (x := x) h₁
  have hsub : T₁.complex.space ∩ T₁.map ⁻¹' e.source ⊆
      (e ∘ T₁.map) ⁻¹' (e.target ∩ e.symm ⁻¹' Y₂) := by
    intro z hz
    refine ⟨e.map_source hz.2, ?_⟩
    change e.symm (e (T₁.map z)) ∈ Y₂
    rw [e.left_inv hz.2]
    exact hY (T₁.bijOn.mapsTo hz.1)
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

omit [FiniteDimensional ℝ F] in
theorem PLPieceIn.isPiecewiseAffineOn_transition {Y : Set X} (T₁ : PLPieceIn E n X Y)
    (T₂ : PLPieceIn F n X Y) :
    IsPiecewiseAffineOn (Function.invFunOn T₂.map T₂.complex.space ∘ T₁.map)
      T₁.complex.space := T₁.isPiecewiseAffineOn_transition_of_subset T₂ Subset.rfl

theorem PLPieceIn.isPLHomeomorphOn_transition_of_subset {Y₁ Y₂ : Set X}
    (T₁ : PLPieceIn E n X Y₁) (T₂ : PLPieceIn F n X Y₂) (hY : Y₁ ⊆ Y₂) :
    IsPLHomeomorphOn (Function.invFunOn T₂.map T₂.complex.space ∘ T₁.map)
      T₁.complex.space (T₂.complex.space ∩ T₂.map ⁻¹' Y₁) := by
  let g := Function.invFunOn T₂.map T₂.complex.space ∘ T₁.map
  have hgK : MapsTo g T₁.complex.space T₂.complex.space := fun _ hx =>
    T₂.bijOn.surjOn.mapsTo_invFunOn (hY (T₁.bijOn.mapsTo hx))
  have hcancel : ∀ x ∈ T₁.complex.space, T₂.map (g x) = T₁.map x := fun _ hx =>
    T₂.bijOn.invOn_invFunOn.2 (hY (T₁.bijOn.mapsTo hx))
  have hbij : BijOn g T₁.complex.space (T₂.complex.space ∩ T₂.map ⁻¹' Y₁) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      refine ⟨hgK hx, ?_⟩
      change T₂.map (g x) ∈ Y₁
      rw [hcancel x hx]
      exact T₁.bijOn.mapsTo hx
    · intro x hx y hy hxy
      apply T₁.bijOn.injOn hx hy
      exact (hcancel x hx).symm.trans ((congrArg T₂.map hxy).trans (hcancel y hy))
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := T₁.bijOn.surjOn hy.2
      refine ⟨x, hx, ?_⟩
      change Function.invFunOn T₂.map T₂.complex.space (T₁.map x) = y
      rw [hxy, T₂.bijOn.invOn_invFunOn.1 hy.1]
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn T₁.isPolyhedron_space
    (T₁.isPiecewiseAffineOn_transition_of_subset T₂ hY) hbij

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
