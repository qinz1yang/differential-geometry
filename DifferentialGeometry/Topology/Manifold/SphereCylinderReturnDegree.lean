import DifferentialGeometry.Topology.Manifold.BoundaryFrameOrientationSign
import DifferentialGeometry.Topology.Manifold.RoundCylinderBoundaryOrientation
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.OrientationSign
import DifferentialGeometry.Topology.Manifold.CylinderCollar.BoundaryNormal
import DifferentialGeometry.Topology.Manifold.SphereDiffeomorphDegree

set_option autoImplicit false
noncomputable section
open Set Function Module Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

private theorem normalFirstOrientation_eq_of_map
    {G : Type*} [AddCommGroup G] [Module ℝ G]
    (e : (ℝ × F) ≃ₗ[ℝ] E) (g : E ≃ₗ[ℝ] G) (b : Basis (Fin 2) ℝ F)
    (o : Orientation ℝ E (Fin 3)) (o' : Orientation ℝ G (Fin 3))
    (h : Orientation.map (Fin 3) g o = o') :
    normalFirstOrientation (e.trans g) b o' = normalFirstOrientation e b o := by
  rw [← h]
  exact normalFirstOrientation_map e g b o

private theorem normalFirstOrientation_eq_neg_of_map_neg
    {G : Type*} [AddCommGroup G] [Module ℝ G]
    (e : (ℝ × F) ≃ₗ[ℝ] E) (g : E ≃ₗ[ℝ] G) (b : Basis (Fin 2) ℝ F)
    (o : Orientation ℝ E (Fin 3)) (o' : Orientation ℝ G (Fin 3))
    (h : Orientation.map (Fin 3) g o = -o') :
    normalFirstOrientation (e.trans g) b o' = -normalFirstOrientation e b o := by
  have h' : o' = -(Orientation.map (Fin 3) g o) := by rw [h]; exact (_root_.neg_neg o').symm
  rw [h', normalFirstOrientation_neg, normalFirstOrientation_map]


private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev EC := E2 × ℝ
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private def referenceCylinderOrientation : SmoothOrientation IC (S2 × ℝ) :=
  roundCylinderSmoothOrientation
    (Orientation.reindex ℝ E3 (finCongr (by simp : 3 = Module.finrank ℝ E3))
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation)
private def basis2 : Basis (Fin 2) ℝ E2 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]

private def ambientNormalOrientation
    (c : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) M ∞)
    (o : SmoothOrientation (𝓡 3) M) (p : S2 × ℝ) (hp : p ∈ c.source) :
    Orientation ℝ E2 (Fin 2) :=
  normalFirstOrientation ((LinearEquiv.prodComm ℝ ℝ E2).trans
    ((c.isLocalDiffeomorphAt IC (𝓡 3) ∞ hp).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv) basis2
    (Orientation.reindex ℝ E3 (finCongr (by simp : Module.finrank ℝ E3 = 3)) (o.val (c p)))

private theorem ambientNormalOrientation_eq_of_preserves
    (c : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) M ∞)
    (o : SmoothOrientation (𝓡 3) M) (p : S2 × ℝ) (hp : p ∈ c.source)
    (h : tangentOrientationEquiv
      ((c.isLocalDiffeomorphAt IC (𝓡 3) ∞ hp).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv (referenceCylinderOrientation.val p) = o.val (c p)) :
    ambientNormalOrientation c o p hp =
      (DifferentialGeometry.sphereOrientation 2 (by decide)).orientation p.1 := by
  have hmap := orientation_map_reindex_of_tangentOrientationEquiv _
    (by simp [Module.finrank_prod] : Module.finrank ℝ EC = 3) (by simp : Module.finrank ℝ E3 = 3)
    _ _ h
  exact (normalFirstOrientation_eq_of_map _ _ basis2 _ _ hmap).trans
    (normalFirstOrientation_roundCylinderSmoothOrientation p.1 p.2 basis2)

private theorem ambientNormalOrientation_eq_neg_of_reverses
    (c : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) M ∞)
    (o : SmoothOrientation (𝓡 3) M) (p : S2 × ℝ) (hp : p ∈ c.source)
    (h : tangentOrientationEquiv
      ((c.isLocalDiffeomorphAt IC (𝓡 3) ∞ hp).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv (referenceCylinderOrientation.val p) = -o.val (c p)) :
    ambientNormalOrientation c o p hp =
      -(DifferentialGeometry.sphereOrientation 2 (by decide)).orientation p.1 := by
  have hmap := orientation_map_reindex_of_tangentOrientationEquiv _
    (by simp [Module.finrank_prod] : Module.finrank ℝ EC = 3) (by simp : Module.finrank ℝ E3 = 3)
    _ _ h
  rw [Orientation.reindex_neg] at hmap
  exact (normalFirstOrientation_eq_neg_of_map_neg _ _ basis2 _ _ hmap).trans
    (congrArg Neg.neg (normalFirstOrientation_roundCylinderSmoothOrientation p.1 p.2 basis2))

private theorem ambientNormalOrientation_map_of_negative_transition
    (a c : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) M ∞)
    (o : SmoothOrientation (𝓡 3) M) (f : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (r : ℝ) (ha : ∀ z, (z, r) ∈ a.source) (hc : ∀ z, (z, r) ∈ c.source)
    (hseam : ∀ z, a (z, r) = c (f z, r))
    (hneg : ∀ z, deriv (fun t => (c.symm (a (z, t))).2) r < 0) (z : S2) :
    Orientation.map (Fin 2) (f.mfderivToContinuousLinearEquiv (by simp) z).toLinearEquiv
      (ambientNormalOrientation a o (z, r) (ha z)) =
        -ambientNormalOrientation c o (f z, r) (hc (f z)) := by
  let T := a.trans c.symm
  have hsource (w : S2) : (w, r) ∈ T.source := by
    refine ⟨ha w, ?_⟩
    change a (w, r) ∈ c.target
    rw [hseam]
    exact c.map_source' (hc (f w))
  have hsection (w : S2) : T (w, r) = (f w, r) := by
    change c.symm (a (w, r)) = _
    rw [hseam]
    exact c.left_inv' (hc (f w))
  have hT := T.mdifferentiableAt (by simp) (hsource z)
  let DA : EC ≃ₗ[ℝ] E3 := ((a.isLocalDiffeomorphAt IC (𝓡 3) ∞ (ha z)).mfderivToContinuousLinearEquiv
    (by simp)).toLinearEquiv
  let DC : EC ≃ₗ[ℝ] E3 :=
    ((c.isLocalDiffeomorphAt IC (𝓡 3) ∞ (hc (f z))).mfderivToContinuousLinearEquiv
    (by simp)).toLinearEquiv
  let DT : EC →L[ℝ] EC := mfderiv IC IC T (z, r)
  let F : E2 ≃ₗ[ℝ] E2 :=
    (f.mfderivToContinuousLinearEquiv (by simp) z).toLinearEquiv
  have hcomp (v : EC) : DC (DT v) = DA v := by
    have hcT : MDifferentiableAt IC (𝓡 3) c (T (z, r)) := by
      rw [hsection]
      exact c.mdifferentiableAt (by simp) (hc (f z))
    have hder := mfderiv_comp_apply (z, r) hcT hT v
    have hevent : (c ∘ T) =ᶠ[nhds (z, r)] a := by
      filter_upwards [T.open_source.mem_nhds (hsource z)] with y hy
      exact c.right_inv' hy.2
    have heq := hevent.mfderiv_eq (I := IC) (I' := 𝓡 3)
    rw [heq, hsection] at hder
    exact hder.symm
  have ht (v : E2) : DA (v, 0) = DC (F v, 0) := by
    rw [← hcomp]
    exact congrArg DC (mfderiv_horizontal_of_section_eq hT
      (f.contMDiff.mdifferentiableAt (by simp)) hsection v)
  have hd : (DT (0, 1)).2 < 0 := by
    have hh := hneg z
    change deriv (fun t => (T (z, t)).2) r < 0 at hh
    rw [deriv_axial_eq_mfderiv_apply hT] at hh
    exact hh
  have hn : DA (0, 1) = (DT (0, 1)).2 • DC (0, 1) + DC ((DT (0, 1)).1, 0) := by
    rw [← hcomp, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have h := orientation_map_normalFirstOrientation_of_negative_normal
    ((LinearEquiv.prodComm ℝ ℝ E2).trans DA)
    ((LinearEquiv.prodComm ℝ ℝ E2).trans DC) F basis2
    (DT (0, 1)).2 hd (DT (0, 1)).1 hn ht
    (Orientation.reindex ℝ E3 (finCongr (by simp : Module.finrank ℝ E3 = 3))
      (o.val (a (z, r))))
  change Orientation.map (Fin 2) F (ambientNormalOrientation a o (z, r) (ha z)) =
    -normalFirstOrientation ((LinearEquiv.prodComm ℝ ℝ E2).trans DC) basis2
      (Orientation.reindex ℝ E3 (finCongr (by simp : Module.finrank ℝ E3 = 3))
        (o.val (a (z, r)))) at h
  rw [hseam] at h
  exact h

private theorem ambientNormalOrientation_eq_or_eq_neg_on_unit
    (c : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) M ∞)
    (o : SmoothOrientation (𝓡 3) M) (hc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ c.source) :
    (∀ z t (ht : t ∈ Icc (0 : ℝ) 1),
      ambientNormalOrientation c o (z, t) (hc ⟨mem_univ _, ht⟩) =
        (DifferentialGeometry.sphereOrientation 2 (by decide)).orientation z) ∨
    (∀ z t (ht : t ∈ Icc (0 : ℝ) 1),
      ambientNormalOrientation c o (z, t) (hc ⟨mem_univ _, ht⟩) =
        -(DifferentialGeometry.sphereOrientation 2 (by decide)).orientation z) := by
  have hconnected : IsPreconnected (univ ×ˢ Icc (0 : ℝ) 1 : Set (S2 × ℝ)) := by
    have hrank : 1 < Module.rank ℝ E3 := by
      apply Module.one_lt_rank_of_one_lt_finrank
      norm_num
    let _ : PreconnectedSpace S2 := Subtype.preconnectedSpace (isPreconnected_sphere hrank 0 1)
    exact isPreconnected_univ.prod isPreconnected_Icc
  have hsign :=
    DifferentialGeometry.PartialDiffeomorph.tangentOrientationEquiv_eq_or_eq_neg_of_isPreconnected
    c referenceCylinderOrientation o hconnected hc
  rcases hsign with h | h
  · exact Or.inl (fun z t ht => ambientNormalOrientation_eq_of_preserves c o (z,t) _
        (h _ ⟨mem_univ _, ht⟩))
  · exact Or.inr (fun z t ht => ambientNormalOrientation_eq_neg_of_reverses c o (z,t) _
        (h _ ⟨mem_univ _, ht⟩))

private theorem preservesOrientation_of_normal_orientations
    (f : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (A C : S2 → unitInterval → Orientation ℝ E2 (Fin 2))
    (haN : (∀ z t, A z t = (DifferentialGeometry.sphereOrientation 2 (by decide)).orientation z) ∨
      (∀ z t, A z t = -(DifferentialGeometry.sphereOrientation 2 (by decide)).orientation z))
    (hcN : (∀ z t, C z t = (DifferentialGeometry.sphereOrientation 2 (by decide)).orientation z) ∨
      (∀ z t, C z t = -(DifferentialGeometry.sphereOrientation 2 (by decide)).orientation z))
    (hlow : ∀ z, A z 0 = -C z 0)
    (hupp : ∀ z, Orientation.map (Fin 2)
      (f.mfderivToContinuousLinearEquiv (by simp) z).toLinearEquiv (A z 1) = -C (f z) 1) :
    f.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)) := by
  let so := DifferentialGeometry.sphereOrientation 2 (by decide)
  let z0 : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  rcases haN with haN | haN <;> rcases hcN with hcN | hcN
  · have hb := hlow z0
    rw [haN, hcN] at hb
    exact (Module.Ray.ne_neg_self _ hb).elim
  · intro z
    have hh := hupp z
    rw [haN, hcN] at hh
    exact hh.trans (_root_.neg_neg (so.orientation (f z)))
  · intro z
    have hh := hupp z
    rw [haN, hcN, Orientation.map_neg] at hh
    exact neg_injective hh
  · have hb := hlow z0
    rw [haN, hcN] at hb
    have he := hb.trans (_root_.neg_neg (so.orientation z0))
    exact (Module.Ray.ne_neg_self _ he.symm).elim

private theorem ambientNormalOrientation_lower
    (a c : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) M ∞)
    (o : SmoothOrientation (𝓡 3) M)
    (ha : ∀ z, (z, (0 : ℝ)) ∈ a.source) (hc : ∀ z, (z, (0 : ℝ)) ∈ c.source)
    (hzero : ∀ z, a (z, 0) = c (z, 0))
    (hneg0 : ∀ z, deriv (fun t => (c.symm (a (z, t))).2) 0 < 0) (z : S2) :
    ambientNormalOrientation a o (z, 0) (ha z) =
      -ambientNormalOrientation c o (z, 0) (hc z) := by
  have h := ambientNormalOrientation_map_of_negative_transition a c o
    (Diffeomorph.refl (𝓡 2) S2 ∞) 0 ha hc hzero hneg0 z
  have hid : ((Diffeomorph.refl (𝓡 2) S2 ∞).mfderivToContinuousLinearEquiv
      (by simp) z).toLinearEquiv = LinearEquiv.refl ℝ E2 := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 2) (𝓡 2) (id : S2 → S2) z v = v
    rw [mfderiv_id]
    rfl
  rw [hid] at h
  change Orientation.map (Fin 2) (LinearEquiv.refl ℝ E2)
    (ambientNormalOrientation a o (z, 0) (ha z)) =
      -ambientNormalOrientation c o (z, 0) (hc z) at h
  rw [Orientation.map_refl] at h
  exact h

private theorem preservesOrientation_of_boundary_normal_relations
    (a c : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) M ∞)
    (o : SmoothOrientation (𝓡 3) M)
    (ha : univ ×ˢ Icc (0 : ℝ) 1 ⊆ a.source)
    (hc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ c.source)
    (f : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (hlow : ∀ z : S2,
      ambientNormalOrientation a o (z, 0) (ha ⟨mem_univ _, by norm_num⟩) =
        -ambientNormalOrientation c o (z, 0) (hc ⟨mem_univ _, by norm_num⟩))
    (hupp : ∀ z : S2,
      Orientation.map (Fin 2) (f.symm.mfderivToContinuousLinearEquiv (by simp) z).toLinearEquiv
        (ambientNormalOrientation a o (z, 1) (ha ⟨mem_univ _, by norm_num⟩)) =
          -ambientNormalOrientation c o (f.symm z, 1) (hc ⟨mem_univ _, by norm_num⟩)) :
    f.symm.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)) := by
  let so := DifferentialGeometry.sphereOrientation 2 (by decide)
  have haN := ambientNormalOrientation_eq_or_eq_neg_on_unit a o ha
  have hcN := ambientNormalOrientation_eq_or_eq_neg_on_unit c o hc
  let A : S2 → unitInterval → Orientation ℝ E2 (Fin 2) :=
    fun z t => ambientNormalOrientation a o (z, t.val) (ha ⟨mem_univ _, t.property⟩)
  let C : S2 → unitInterval → Orientation ℝ E2 (Fin 2) :=
    fun z t => ambientNormalOrientation c o (z, t.val) (hc ⟨mem_univ _, t.property⟩)
  have haN' : (∀ z t, A z t = so.orientation z) ∨ (∀ z t, A z t = -so.orientation z) :=
    haN.imp (fun h z t => h z t.val t.property) (fun h z t => h z t.val t.property)
  have hcN' : (∀ z t, C z t = so.orientation z) ∨ (∀ z t, C z t = -so.orientation z) :=
    hcN.imp (fun h z t => h z t.val t.property) (fun h z t => h z t.val t.property)
  exact preservesOrientation_of_normal_orientations f.symm A C haN' hcN' hlow hupp

private theorem preservesOrientation_symm_of_closed_cylinder_return
    (a c : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) M ∞)
    (o : SmoothOrientation (𝓡 3) M)
    (ha : univ ×ˢ Icc (0 : ℝ) 1 ⊆ a.source)
    (hc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ c.source)
    (hoverlap : (a '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
      (c '' (univ ×ˢ Icc (0 : ℝ) 1)) ⊆
      (c '' (univ ×ˢ ({0} : Set ℝ))) ∪ (c '' (univ ×ˢ ({1} : Set ℝ))))
    (f : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (hzero : ∀ z : S2, a (z, 0) = c (z, 0))
    (hone : ∀ z : S2, a (z, 1) = c (f.symm z, 1)) :
    f.symm.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by decide))
      (DifferentialGeometry.sphereOrientation 2 (by decide)) := by
  obtain ⟨hneg0,hneg1⟩ :=
    axial_derivative_neg_of_closed_slab_overlap a c ha hc hoverlap f hzero hone
  have hlow (z : S2) :
      ambientNormalOrientation a o (z, 0) (ha ⟨mem_univ _, by norm_num⟩) =
        -ambientNormalOrientation c o (z, 0) (hc ⟨mem_univ _, by norm_num⟩) :=
    ambientNormalOrientation_lower a c o
      (fun z => ha ⟨mem_univ _, by norm_num⟩) (fun z => hc ⟨mem_univ _, by norm_num⟩)
      hzero hneg0 z
  have hupp (z : S2) :
      Orientation.map (Fin 2) (f.symm.mfderivToContinuousLinearEquiv (by simp) z).toLinearEquiv
        (ambientNormalOrientation a o (z, 1) (ha ⟨mem_univ _, by norm_num⟩)) =
          -ambientNormalOrientation c o (f.symm z, 1) (hc ⟨mem_univ _, by norm_num⟩) :=
    ambientNormalOrientation_map_of_negative_transition a c o f.symm 1
      (fun z => ha ⟨mem_univ _, by norm_num⟩) (fun z => hc ⟨mem_univ _, by norm_num⟩)
      hone hneg1 z
  exact preservesOrientation_of_boundary_normal_relations a c o ha hc f hlow hupp

theorem sphereDiffeomorphDegree_eq_one_of_closed_cylinder_return
    (a c : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) M ∞)
    (o : SmoothOrientation (𝓡 3) M)
    (ha : univ ×ˢ Icc (0 : ℝ) 1 ⊆ a.source)
    (hc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ c.source)
    (hoverlap : (a '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
      (c '' (univ ×ˢ Icc (0 : ℝ) 1)) ⊆
      (c '' (univ ×ˢ ({0} : Set ℝ))) ∪ (c '' (univ ×ˢ ({1} : Set ℝ))))
    (f : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (hzero : ∀ z : S2, a (z, 0) = c (z, 0))
    (hone : ∀ z : S2, a (z, 1) = c (f.symm z, 1)) :
    sphereDiffeomorphDegree f = 1 := by
  have hp := preservesOrientation_symm_of_closed_cylinder_return a c o ha hc hoverlap f hzero hone
  exact sphereDiffeomorphDegree_eq_one_of_preservesOrientation f
    (Diffeomorph.preservesOrientation_symm (f := f.symm)
      (oM := DifferentialGeometry.sphereOrientation 2 (by decide))
      (oN := DifferentialGeometry.sphereOrientation 2 (by decide)) hp)

end DifferentialGeometry.Topology.Manifold
