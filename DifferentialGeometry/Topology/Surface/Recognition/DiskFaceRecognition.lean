import DifferentialGeometry.Topology.Surface.Recognition.DiskAnnulusSphere
import DifferentialGeometry.Topology.Connected.DiskFaceCount

/-!
# FC40b: the sphere/torus decision for the disk faces of a closed surface

Lane W4-FCb's FC40a (`disk_face_count_dichotomy`) shows, for a connected `Y` cut into pairwise disjoint
closed disks `D i` and circle-bundle components `B j` (each with `0` or `2` attached disks), that there is
exactly one bundle component and `0` or `2` disks.  FC40 (blueprint B:7457) needs the decision

* `Y ≅ S²` ⇒ two disks: with no disk, `Y` is one circle bundle over a circle, whose projection is an open
  map to the circle; a two-sphere has none (R1, `not_isOpenMap_circle`).
* `Y ≅ T²` ⇒ no disk: with two disks, `Y` = disk ∪ annulus ∪ disk is a two-sphere (R2), which has no open
  map to the circle, while the torus does.

The hypotheses `hbase`, `hdisk`, `hann` are the face data of the decomposition (the bundle projection of a
component without boundary circles, whose base is a circle by lane N1; the disk and annulus
parametrizations), not conclusions.  No Euler characteristic is used.
-/

set_option autoImplicit false

open Set Function Topology

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

section Sphere

variable {Y ι κ : Type*} [TopologicalSpace Y] [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- **FC40b, sphere side (kernel).** If `Y` has no continuous open map to the circle, a
decomposition as in FC40a has exactly two disks. -/
theorem disk_face_count_of_not_isOpenMap [ConnectedSpace Y]
    (hY : ∀ p : Y → Circle, Continuous p → ¬ IsOpenMap p)
    (D : ι → Set Y) (B : κ → Set Y) (hD : ∀ i, IsClosed (D i)) (hB : ∀ j, IsClosed (B j))
    (hBne : ∀ j, (B j).Nonempty) (hcover : (⋃ i, D i) ∪ (⋃ j, B j) = univ)
    (hDD : Pairwise (Disjoint on D)) (hBB : Pairwise (Disjoint on B))
    (side : ι → κ) (hDB : ∀ i j, (D i ∩ B j).Nonempty → side i = j)
    (hdeg : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 ∨
      (Finset.univ.filter (fun i => side i = j)).card = 2)
    (hbase : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 →
      ∃ p : B j → Circle, Continuous p ∧ IsOpenMap p) :
    Fintype.card κ = 1 ∧ Fintype.card ι = 2 := by
  obtain ⟨hκ, hι⟩ := disk_face_count_dichotomy D B hD hB hBne hcover hDD hBB side hDB hdeg
  refine ⟨hκ, hι.resolve_left fun h0 => ?_⟩
  obtain ⟨j₀, hj₀⟩ := Fintype.card_eq_one_iff.mp hκ
  have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
  have hfilter : (Finset.univ.filter (fun i => side i = j₀)).card = 0 := by
    rw [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty]
  obtain ⟨p, hp, hpo⟩ := hbase j₀ hfilter
  have hBuniv : B j₀ = univ := by
    refine eq_univ_of_forall fun y => ?_
    have hy : y ∈ (⋃ i, D i) ∪ (⋃ j, B j) := hcover ▸ mem_univ y
    rcases hy with hy | hy
    · obtain ⟨i, -⟩ := mem_iUnion.mp hy
      exact hempty.elim i
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      rwa [hj₀ j] at hj
  let φ : Y ≃ₜ B j₀ := (Homeomorph.Set.univ Y).symm.trans (Homeomorph.setCongr hBuniv.symm)
  exact hY _ (hp.comp φ.continuous) (hpo.comp φ.isOpenMap)

/-- **FC40b, sphere side.** On a compact, simply connected, locally path-connected `Y`, a
decomposition as in FC40a has exactly two disks. -/
theorem disk_face_count_simplyConnected [CompactSpace Y] [SimplyConnectedSpace Y]
    [LocallyPathConnectedSpace Y]
    (D : ι → Set Y) (B : κ → Set Y) (hD : ∀ i, IsClosed (D i)) (hB : ∀ j, IsClosed (B j))
    (hBne : ∀ j, (B j).Nonempty) (hcover : (⋃ i, D i) ∪ (⋃ j, B j) = univ)
    (hDD : Pairwise (Disjoint on D)) (hBB : Pairwise (Disjoint on B))
    (side : ι → κ) (hDB : ∀ i j, (D i ∩ B j).Nonempty → side i = j)
    (hdeg : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 ∨
      (Finset.univ.filter (fun i => side i = j)).card = 2)
    (hbase : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 →
      ∃ p : B j → Circle, Continuous p ∧ IsOpenMap p) :
    Fintype.card κ = 1 ∧ Fintype.card ι = 2 :=
  disk_face_count_of_not_isOpenMap (fun _ hp => not_isOpenMap_circle hp) D B hD hB hBne hcover
    hDD hBB side hDB hdeg hbase

/-- **FC40 for a sphere face.** A face homeomorphic to `S²` has exactly two disks. -/
theorem disk_face_count_sphereTwo (φ : Y ≃ₜ SphereTwo)
    (D : ι → Set Y) (B : κ → Set Y) (hD : ∀ i, IsClosed (D i)) (hB : ∀ j, IsClosed (B j))
    (hBne : ∀ j, (B j).Nonempty) (hcover : (⋃ i, D i) ∪ (⋃ j, B j) = univ)
    (hDD : Pairwise (Disjoint on D)) (hBB : Pairwise (Disjoint on B))
    (side : ι → κ) (hDB : ∀ i j, (D i ∩ B j).Nonempty → side i = j)
    (hdeg : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 ∨
      (Finset.univ.filter (fun i => side i = j)).card = 2)
    (hbase : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 →
      ∃ p : B j → Circle, Continuous p ∧ IsOpenMap p) :
    Fintype.card κ = 1 ∧ Fintype.card ι = 2 := by
  have : ConnectedSpace Y := φ.symm.surjective.connectedSpace φ.symm.continuous
  exact disk_face_count_of_not_isOpenMap
    (fun _ hp => not_isOpenMap_circle_of_homeomorph_sphereTwo φ hp) D B hD hB hBne hcover hDD hBB
    side hDB hdeg hbase

end Sphere

section Torus

variable {Y ι κ : Type*} [TopologicalSpace Y] [T2Space Y] [Fintype ι] [Fintype κ]
  [DecidableEq κ]

/-- **FC40b, torus side (kernel).** If `Y` has a continuous open map to the circle, a
decomposition as in FC40a, with disk and annulus parametrizations, has no disk. -/
theorem disk_face_count_of_isOpenMap_circle [ConnectedSpace Y]
    (D : ι → Set Y) (B : κ → Set Y) (hD : ∀ i, IsClosed (D i)) (hB : ∀ j, IsClosed (B j))
    (hBne : ∀ j, (B j).Nonempty) (hcover : (⋃ i, D i) ∪ (⋃ j, B j) = univ)
    (hDD : Pairwise (Disjoint on D)) (hBB : Pairwise (Disjoint on B))
    (side : ι → κ) (hDB : ∀ i j, (D i ∩ B j).Nonempty → side i = j)
    (hdeg : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 ∨
      (Finset.univ.filter (fun i => side i = j)).card = 2)
    {q : Y → Circle} (hq : Continuous q) (hqo : IsOpenMap q)
    (hdisk : ∀ i, ∃ h : Disk 2 → Y, Continuous h ∧ Injective h ∧ range h = D i ∧
      h '' diskSphere 2 = D i ∩ B (side i))
    (hann : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 2 →
      ∃ e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → Y, Continuous e ∧
        Injective e ∧ range e = B j ∧ ∀ i, side i = j →
          D i ∩ B j = e '' {q | (q.2 : ℝ) = 0} ∨ D i ∩ B j = e '' {q | (q.2 : ℝ) = 1}) :
    Fintype.card κ = 1 ∧ Fintype.card ι = 0 := by
  classical
  obtain ⟨hκ, hι⟩ := disk_face_count_dichotomy D B hD hB hBne hcover hDD hBB side hDB hdeg
  refine ⟨hκ, hι.resolve_right fun h2 => ?_⟩
  obtain ⟨j₀, hj₀⟩ := Fintype.card_eq_one_iff.mp hκ
  obtain ⟨i₁, i₂, hne, huniv⟩ :=
    Finset.card_eq_two.mp (by rw [Finset.card_univ]; exact h2 : (Finset.univ : Finset ι).card = 2)
  have hi : ∀ i, i = i₁ ∨ i = i₂ := by
    intro i
    have : i ∈ ({i₁, i₂} : Finset ι) := huniv ▸ Finset.mem_univ i
    simpa using this
  have hside : ∀ i, side i = j₀ := fun i => hj₀ _
  have hfilter : (Finset.univ.filter (fun i => side i = j₀)).card = 2 := by
    rw [Finset.filter_true_of_mem (fun i _ => hside i), Finset.card_univ, h2]
  obtain ⟨e, he, he', hre, hends⟩ := hann j₀ hfilter
  obtain ⟨h₁, hh₁, hh₁', hr₁, hb₁⟩ := hdisk i₁
  obtain ⟨h₂, hh₂, hh₂', hr₂, hb₂⟩ := hdisk i₂
  rw [hside] at hb₁ hb₂
  have hcov : range h₁ ∪ range e ∪ range h₂ = univ := by
    refine eq_univ_of_forall fun y => ?_
    have hy : y ∈ (⋃ i, D i) ∪ (⋃ j, B j) := hcover ▸ mem_univ y
    rw [hr₁, hre, hr₂]
    rcases hy with hy | hy
    · obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
      rcases hi i with rfl | rfl
      · exact Or.inl (Or.inl hyi)
      · exact Or.inr hyi
    · obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
      rw [hj₀ j] at hyj
      exact Or.inl (Or.inr hyj)
  have h12 : Disjoint (range h₁) (range h₂) := by
    rw [hr₁, hr₂]
    exact hDD hne
  have h1 : range h₁ ∩ range e = h₁ '' diskSphere 2 := by rw [hr₁, hre, hb₁]
  have h2' : range h₂ ∩ range e = h₂ '' diskSphere 2 := by rw [hr₂, hre, hb₂]
  have hS : ∀ t : Icc (0 : ℝ) 1, (e '' {q | (q.2 : ℝ) = t}).Nonempty := fun t =>
    ⟨e (collarSpherePoint 1, t), ⟨_, rfl, rfl⟩⟩
  have hsame : ∀ t : Icc (0 : ℝ) 1, D i₁ ∩ B j₀ = e '' {q | (q.2 : ℝ) = t} →
      D i₂ ∩ B j₀ = e '' {q | (q.2 : ℝ) = t} → False := by
    intro t a1 a2
    obtain ⟨y, hy⟩ := hS t
    have hy1 : y ∈ D i₁ ∩ B j₀ := a1 ▸ hy
    have hy2 : y ∈ D i₂ ∩ B j₀ := a2 ▸ hy
    exact Set.disjoint_left.mp (hDD hne) hy1.1 hy2.1
  rcases hends i₁ (hside i₁) with a1 | a1 <;> rcases hends i₂ (hside i₂) with a2 | a2
  · exact hsame ⟨0, left_mem_Icc.mpr zero_le_one⟩ a1 a2
  · exact not_isOpenMap_circle_of_disk_annulus_disk hh₁ hh₁' hh₂ hh₂' he he' hcov h12 h1
      (hb₁.trans a1) h2' (hb₂.trans a2) hq hqo
  · have hcov' : range h₂ ∪ range e ∪ range h₁ = univ := by
      rw [← hcov]
      ext y
      simp only [mem_union]
      tauto
    exact not_isOpenMap_circle_of_disk_annulus_disk hh₂ hh₂' hh₁ hh₁' he he' hcov' h12.symm h2'
      (hb₂.trans a2) h1 (hb₁.trans a1) hq hqo
  · exact hsame ⟨1, right_mem_Icc.mpr zero_le_one⟩ a1 a2

end Torus

/-- **FC40 for a torus face.** A face homeomorphic to `T² = S¹ × S¹`, cut as in FC40a with disk
and annulus parametrizations, has no disk. -/
theorem disk_face_count_torus {Y ι κ : Type*} [TopologicalSpace Y] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (φ : Y ≃ₜ Circle × Circle)
    (D : ι → Set Y) (B : κ → Set Y) (hD : ∀ i, IsClosed (D i)) (hB : ∀ j, IsClosed (B j))
    (hBne : ∀ j, (B j).Nonempty) (hcover : (⋃ i, D i) ∪ (⋃ j, B j) = univ)
    (hDD : Pairwise (Disjoint on D)) (hBB : Pairwise (Disjoint on B))
    (side : ι → κ) (hDB : ∀ i j, (D i ∩ B j).Nonempty → side i = j)
    (hdeg : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 ∨
      (Finset.univ.filter (fun i => side i = j)).card = 2)
    (hdisk : ∀ i, ∃ h : Disk 2 → Y, Continuous h ∧ Injective h ∧ range h = D i ∧
      h '' diskSphere 2 = D i ∩ B (side i))
    (hann : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 2 →
      ∃ e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → Y, Continuous e ∧
        Injective e ∧ range e = B j ∧ ∀ i, side i = j →
          D i ∩ B j = e '' {q | (q.2 : ℝ) = 0} ∨ D i ∩ B j = e '' {q | (q.2 : ℝ) = 1}) :
    Fintype.card κ = 1 ∧ Fintype.card ι = 0 := by
  have : T2Space Y := φ.isEmbedding.t2Space
  have : ConnectedSpace Y := φ.symm.surjective.connectedSpace φ.symm.continuous
  exact disk_face_count_of_isOpenMap_circle D B hD hB hBne hcover hDD hBB side hDB hdeg
    (continuous_fst.comp φ.continuous) (isOpenMap_fst.comp φ.isOpenMap) hdisk hann

end DifferentialGeometry.Topology.Surface
