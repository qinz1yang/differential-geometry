/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem exists_splitDisk_src_eq_inter_vertexBall
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) {w w' : Section34VertexIndex 𝒦 𝒦'}
    (hww : w ≠ w')
    (hmeet : (src (Section34Label.vertexBall w) ∩
      src (Section34Label.vertexBall w')).Nonempty) :
    ∃ e : Section34EdgeIndex 𝒦 𝒦', src (Section34Label.splitDisk e) =
      src (Section34Label.vertexBall w) ∩ src (Section34Label.vertexBall w') := by
  classical
  obtain ⟨-, -, -, hcell, -, hinter, hdim, -, -, harc, hmark, hpatch, hedge,
    hfaceVertex, -, htetraVertex, -, -, -, -, -, hvertexEdge, hends, -, -⟩ := id hcut
  have hsameDim (l m : Section34CutLabelOf 𝒦 𝒦')
      (hd : section34Dim l = section34Dim m) (hsub : src l ⊆ src m) : l = m := by
    rcases hdim m l hsub with heq | hlt
    · exact heq
    · rw [hd] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
  have hfaceNotSubset (s : Section34SimplexIndex 𝒦 3)
      (v : Section34VertexIndex 𝒦 𝒦') :
      ¬ src (Section34Label.faceDisk s) ⊆ src (Section34Label.vertexBall v) := by
    intro hsub
    obtain ⟨x, hx⟩ := (hcell (Section34Label.faceDisk s)).nonempty
    have hi : Section34Incident v.1 s.1 := by
      by_contra hi
      have hx' : x ∈ src (Section34Label.faceDisk s) ∩
          src (Section34Label.vertexBall v) := ⟨hx, hsub hx⟩
      rw [hfaceVertex s v hi] at hx'
      exact hx'
    let a : Section34ArcIndex 𝒦 𝒦' := ⟨(s, v), hi⟩
    have hsubArc : src (Section34Label.faceDisk s) ⊆ src (Section34Label.faceArc a) := by
      rw [harc a]
      exact fun y hy => ⟨hsub hy, hy⟩
    rcases hdim (Section34Label.faceArc a) (Section34Label.faceDisk s) hsubArc with heq | hlt
    · cases heq
    · simp only [section34Dim] at hlt
      omega
  have hpatchVertex (p : Section34PatchIndex 𝒦 𝒦')
      (v : Section34VertexIndex 𝒦 𝒦')
      (hsub : src (Section34Label.patch p) ⊆ src (Section34Label.vertexBall v)) :
      p.1.2 = v := by
    have hsubT : src (Section34Label.patch p) ⊆
        src (Section34Label.tetraBall p.1.1) := by
      rw [hpatch p]
      exact inter_subset_left
    obtain ⟨x, hx⟩ := (hcell (Section34Label.patch p)).nonempty
    have hi : Section34Incident v.1 p.1.1.1 := by
      by_contra hi
      have hx' : x ∈ src (Section34Label.tetraBall p.1.1) ∩
          src (Section34Label.vertexBall v) := ⟨hsubT hx, hsub hx⟩
      rw [htetraVertex p.1.1 v hi] at hx'
      exact hx'
    let q : Section34PatchIndex 𝒦 𝒦' := ⟨(p.1.1, v), hi⟩
    have hpq : src (Section34Label.patch p) ⊆ src (Section34Label.patch q) := by
      rw [hpatch q]
      exact fun y hy => ⟨hsubT hy, hsub hy⟩
    have hpq' := hsameDim (Section34Label.patch p) (Section34Label.patch q) rfl hpq
    exact congrArg (fun r : Section34PatchIndex 𝒦 𝒦' => r.1.2)
      (Section34Label.patch.inj hpq')
  have harcVertex (a : Section34ArcIndex 𝒦 𝒦')
      (v : Section34VertexIndex 𝒦 𝒦')
      (hsub : src (Section34Label.faceArc a) ⊆ src (Section34Label.vertexBall v)) :
      a.1.2 = v := by
    have hsubF : src (Section34Label.faceArc a) ⊆ src (Section34Label.faceDisk a.1.1) := by
      rw [harc a]
      exact inter_subset_right
    obtain ⟨x, hx⟩ := (hcell (Section34Label.faceArc a)).nonempty
    have hi : Section34Incident v.1 a.1.1.1 := by
      by_contra hi
      have hx' : x ∈ src (Section34Label.faceDisk a.1.1) ∩
          src (Section34Label.vertexBall v) := ⟨hsubF hx, hsub hx⟩
      rw [hfaceVertex a.1.1 v hi] at hx'
      exact hx'
    let b : Section34ArcIndex 𝒦 𝒦' := ⟨(a.1.1, v), hi⟩
    have hab : src (Section34Label.faceArc a) ⊆ src (Section34Label.faceArc b) := by
      rw [harc b]
      exact fun y hy => ⟨hsub hy, hsubF hy⟩
    have hab' := hsameDim (Section34Label.faceArc a) (Section34Label.faceArc b) rfl hab
    exact congrArg (fun r : Section34ArcIndex 𝒦 𝒦' => r.1.2)
      (Section34Label.faceArc.inj hab')
  obtain ⟨x, hxw, hxw'⟩ := hmeet
  have hx : x ∈ src (Section34Label.vertexBall w) ∩
      src (Section34Label.vertexBall w') := ⟨hxw, hxw'⟩
  rw [hinter] at hx
  obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.mp hx
  have hlw : src l ⊆ src (Section34Label.vertexBall w) := hl.1
  have hlw' : src l ⊆ src (Section34Label.vertexBall w') := hl.2
  have hsplit : ∃ e : Section34EdgeIndex 𝒦 𝒦', x ∈ src (Section34Label.splitDisk e) := by
    cases l with
    | vertexBall v =>
      have hvw := hsameDim (Section34Label.vertexBall v) (Section34Label.vertexBall w) rfl hlw
      have hvw' :=
        hsameDim (Section34Label.vertexBall v) (Section34Label.vertexBall w') rfl hlw'
      exact (hww (Section34Label.vertexBall.inj (hvw.symm.trans hvw'))).elim
    | tetraBall t =>
      have htv := hsameDim (Section34Label.tetraBall t) (Section34Label.vertexBall w) rfl hlw
      cases htv
    | splitDisk e => exact ⟨e, hxl⟩
    | faceDisk s => exact (hfaceNotSubset s w hlw).elim
    | patch p => exact (hww ((hpatchVertex p w hlw).symm.trans (hpatchVertex p w' hlw'))).elim
    | faceArc a => exact (hww ((harcVertex a w hlw).symm.trans (harcVertex a w' hlw'))).elim
    | edgeArc i =>
      rw [hedge i] at hxl
      exact ⟨i.1.2, hxl.2⟩
    | markedPoint p =>
      rw [hmark p] at hxl
      exact ⟨p.1.2, hxl.1⟩
  obtain ⟨e, hxe⟩ := hsplit
  have hwe := hvertexEdge w e ⟨x, hxw, hxe⟩
  have hw'e := hvertexEdge w' e ⟨x, hxw', hxe⟩
  obtain ⟨a, b, -, hab, he⟩ := hends e
  have hvertexEq {v v' : Section34VertexIndex 𝒦 𝒦'} {z : Ea}
      (hz : z ∈ v.1) (hz' : z ∈ v'.1) : v = v' := by
    apply Subtype.ext
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp v.2.2.1
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp v'.2.2.1
    have hpq : p = q := (Finset.mem_singleton.mp (hp ▸ hz)).symm.trans
      (Finset.mem_singleton.mp (hq ▸ hz'))
    exact hp.trans ((congrArg (fun z : Ea => ({z} : Finset Ea)) hpq).trans hq.symm)
  have hvertexEnds (v : Section34VertexIndex 𝒦 𝒦') (hve : v.1 ⊆ e.1) : v = a ∨ v = b := by
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp v.2.2.1
    have hzv : z ∈ v.1 := hz.symm ▸ Finset.mem_singleton_self z
    have hze : z ∈ (e.1 : Set Ea) := hve hzv
    rw [hab] at hze
    exact hze.elim (fun hza => Or.inl (hvertexEq hzv hza))
      (fun hzb => Or.inr (hvertexEq hzv hzb))
  rcases hvertexEnds w hwe with hw | hw <;> rcases hvertexEnds w' hw'e with hw' | hw'
  · exact (hww (hw.trans hw'.symm)).elim
  · exact ⟨e, by rw [hw, hw']; exact he⟩
  · exact ⟨e, by rw [hw, hw']; exact he.trans (inter_comm _ _)⟩
  · exact (hww (hw.trans hw'.symm)).elim

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
