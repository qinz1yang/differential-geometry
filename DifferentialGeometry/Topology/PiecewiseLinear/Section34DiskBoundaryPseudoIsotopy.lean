import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PeriodicLateralExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BallMarkedExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_PL_disk_pseudoisotopy_with_prescribed_side
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    {u : E → E} (hu : IsPLHomeomorphOn u D D) {φ : E × ℝ → E × ℝ}
    (hφ : IsPLHomeomorphOn φ ((r '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1)
      ((r '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1))
    (hφ₀ : ∀ x ∈ r '' stdSimplexBoundary 2, φ (x, 0) = (x, 0))
    (hφ₁ : ∀ x ∈ r '' stdSimplexBoundary 2, φ (x, 1) = (u x, 1)) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ (D ×ˢ Icc (0 : ℝ) 1) (D ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ D, Φ (x, 0) = (x, 0)) ∧ (∀ x ∈ D, Φ (x, 1) = (u x, 1)) ∧
      EqOn Φ φ ((r '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) := by
  classical
  let _ : DecidableEq E := Classical.decEq _
  let J := r '' stdSimplexBoundary 2
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hJ : IsPolyhedron J := hr.isPLSphere_image_stdSimplexBoundary.isPolyhedron
  have hJD : J ⊆ D := (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have huJ : u '' J = J := by
    have h := (hr.trans hu).image_stdSimplexBoundary_congr hr
    rwa [image_comp] at h
  have husing : IsPolyhedron ({1} : Set ℝ) := (isHPolytope_singleton 1).isPolyhedron
  have hzero := isPolyhedron_prod_singleton hD.isPolyhedron 0
  have hone := isPolyhedron_prod_singleton hD.isPolyhedron 1
  have hdis : Disjoint (D ×ˢ ({0} : Set ℝ)) (D ×ˢ ({1} : Set ℝ)) := by
    exact disjoint_left.mpr fun x hx hy => zero_ne_one (hx.2.symm.trans hy.2)
  obtain ⟨c, hc, hc₀, hc₁⟩ := exists_isPLHomeomorphOn_union hzero hone
    hzero.isPLHomeomorphOn_id (hu.prodMap husing.isPLHomeomorphOn_id)
    (by rw [hdis.inter_eq]; exact eqOn_empty _ _)
    (by rw [hdis.inter_eq]; exact surjOn_empty _ _)
  have hc0 (x : E) (hx : x ∈ D) : c (x, 0) = (x, 0) := hc₀ ⟨hx, rfl⟩
  have hc1 (x : E) (hx : x ∈ D) : c (x, 1) = (u x, 1) := hc₁ ⟨hx, rfl⟩
  rw [← prod_union, singleton_union] at hc
  have hcaps := hzero.union hone
  rw [← prod_union, singleton_union] at hcaps
  have hside := hJ.prod (show IsPolyhedron (Icc (0 : ℝ) 1) from
    isHPolytope_Icc.isPolyhedron)
  have hcompat : EqOn c φ ((D ×ˢ ({0, 1} : Set ℝ)) ∩ (J ×ˢ Icc (0 : ℝ) 1)) := by
    intro x hx
    rcases hx.1.2 with hz | ho
    · have heq : x = (x.1, 0) := Prod.ext rfl hz
      rw [heq, hc0 x.1 hx.1.1, hφ₀ x.1 hx.2.1]
    · have heq : x = (x.1, 1) := Prod.ext rfl ho
      rw [heq, hc1 x.1 hx.1.1, hφ₁ x.1 hx.2.1]
  have hsurj : SurjOn c ((D ×ˢ ({0, 1} : Set ℝ)) ∩ (J ×ˢ Icc (0 : ℝ) 1))
      ((D ×ˢ ({0, 1} : Set ℝ)) ∩ (J ×ˢ Icc (0 : ℝ) 1)) := by
    intro z hz
    rcases hz.1.2 with hz0 | hz1
    · refine ⟨(z.1, 0), ⟨⟨hz.1.1, Or.inl rfl⟩, hz.2.1, by norm_num⟩, ?_⟩
      exact (hc0 z.1 hz.1.1).trans (Prod.ext rfl hz0.symm)
    · obtain ⟨x, hx, hux⟩ := huJ.symm.subset hz.2.1
      refine ⟨(x, 1), ⟨⟨hJD hx, Or.inr rfl⟩, hx, by norm_num⟩, ?_⟩
      exact (hc1 x (hJD hx)).trans (Prod.ext hux hz1.symm)
  obtain ⟨b, hb, hbcap, hbside⟩ :=
    exists_isPLHomeomorphOn_union hcaps hside hc hφ hcompat hsurj
  obtain ⟨K, hKfin, hKspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKspace.symm ▸ hD
  have hKbd : (boundaryComplex 2 K).space = J :=
    (hr.image_stdSimplexBoundary_eq_boundaryComplex K hKspace).symm
  have hprism := isPLBall_three_prod hD (isPLBall_Icc (zero_lt_one' ℝ))
  obtain ⟨L, hLfin, hLspace⟩ := hprism.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall 3 L.space := hLspace.symm ▸ hprism
  have hbd := boundaryComplex_space_prism K hK (zero_lt_one' ℝ) L
    (hLspace.trans (congrArg (· ×ˢ Icc (0 : ℝ) 1) hKspace.symm))
  rw [hKspace, hKbd] at hbd
  have hbb : IsPLHomeomorphOn b (boundaryComplex 3 L).space
      (boundaryComplex 3 L).space := by rw [hbd]; exact hb
  obtain ⟨Φ, hΦ, hΦb⟩ := exists_isPLHomeomorphOn_of_boundaryComplex L L hL hL hbb
  rw [hLspace] at hΦ
  rw [hbd] at hΦb
  refine ⟨Φ, hΦ, ?_, ?_, fun z hz => (hΦb (Or.inr hz)).trans (hbside hz)⟩
  · intro x hx
    have hc : (x, (0 : ℝ)) ∈ D ×ˢ ({0, 1} : Set ℝ) := ⟨hx, Or.inl rfl⟩
    exact (hΦb (Or.inl hc)).trans ((hbcap hc).trans (hc0 x hx))
  · intro x hx
    have hc : (x, (1 : ℝ)) ∈ D ×ˢ ({0, 1} : Set ℝ) := ⟨hx, Or.inr rfl⟩
    exact (hΦb (Or.inl hc)).trans ((hbcap hc).trans (hc1 x hx))

theorem exists_PL_disk_family_pseudoisotopy_with_prescribed_sides
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] {D : ι → Set E} {r : ι → (Fin 3 → ℝ) → E}
    (hr : ∀ i, IsPLHomeomorphOn (r i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hinter : ∀ i j, i ≠ j → D i ∩ D j ⊆ r i '' stdSimplexBoundary 2)
    {u : E → E} (hu : ∀ i, IsPLHomeomorphOn u (D i) (D i)) {φ : E × ℝ → E × ℝ}
    (hφ : IsPLHomeomorphOn φ ((⋃ i, r i '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1)
      ((⋃ i, r i '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1))
    (hφrim : ∀ i, φ '' ((r i '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) =
      (r i '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1)
    (hφ₀ : ∀ x ∈ ⋃ i, r i '' stdSimplexBoundary 2, φ (x, 0) = (x, 0))
    (hφ₁ : ∀ x ∈ ⋃ i, r i '' stdSimplexBoundary 2, φ (x, 1) = (u x, 1)) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ ((⋃ i, D i) ×ˢ Icc (0 : ℝ) 1)
        ((⋃ i, D i) ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ⋃ i, D i, Φ (x, 0) = (x, 0)) ∧
      (∀ x ∈ ⋃ i, D i, Φ (x, 1) = (u x, 1)) ∧
      EqOn Φ φ ((⋃ i, r i '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) ∧
      ∀ i, Φ '' (D i ×ˢ Icc (0 : ℝ) 1) = D i ×ˢ Icc (0 : ℝ) 1 := by
  classical
  let J : ι → Set E := fun i => r i '' stdSimplexBoundary 2
  have hJ (i : ι) : IsPolyhedron (J i) :=
    (hr i).isPLSphere_image_stdSimplexBoundary.isPolyhedron
  have hJD (i : ι) : J i ⊆ D i :=
    (image_mono (fun _ hx => hx.1)).trans (hr i).image_eq.subset
  have hsub (i : ι) : J i ×ˢ Icc (0 : ℝ) 1 ⊆ (⋃ i, J i) ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono_left (subset_iUnion J i)
  have hφi (i : ι) : IsPLHomeomorphOn φ (J i ×ˢ Icc (0 : ℝ) 1)
      (J i ×ˢ Icc (0 : ℝ) 1) := by
    have h := hφ.restrict ((hJ i).prod isHPolytope_Icc.isPolyhedron) (hsub i)
    rwa [hφrim i] at h
  choose Ψ hΨ hΨ₀ hΨ₁ hfix using fun i =>
    exists_PL_disk_pseudoisotopy_with_prescribed_side (hr i) (hu i) (hφi i)
      (fun x hx => hφ₀ x (mem_iUnion.mpr ⟨i, hx⟩))
      (fun x hx => hφ₁ x (mem_iUnion.mpr ⟨i, hx⟩))
  have hmeet (i j : ι) (hij : i ≠ j) :
      (D i ×ˢ Icc (0 : ℝ) 1) ∩ (D j ×ˢ Icc (0 : ℝ) 1) =
        (J i ×ˢ Icc (0 : ℝ) 1) ∩ (J j ×ˢ Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · exact fun x hx => ⟨⟨hinter i j hij ⟨hx.1.1, hx.2.1⟩, hx.1.2⟩,
        hinter j i hij.symm ⟨hx.2.1, hx.1.1⟩, hx.2.2⟩
    · exact inter_subset_inter (prod_mono_left (hJD i)) (prod_mono_left (hJD j))
  have hcompat (i j : ι) : EqOn (Ψ i) (Ψ j)
      ((D i ×ˢ Icc (0 : ℝ) 1) ∩ (D j ×ˢ Icc (0 : ℝ) 1)) := by
    rcases eq_or_ne i j with rfl | hij
    · exact fun _ _ => rfl
    · rw [hmeet i j hij]
      exact fun _ hx => (hfix i hx.1).trans (hfix j hx.2).symm
  have hmeetImage (i j : ι) :
      Ψ i '' ((D i ×ˢ Icc (0 : ℝ) 1) ∩ (D j ×ˢ Icc (0 : ℝ) 1)) =
        (D i ×ˢ Icc (0 : ℝ) 1) ∩ (D j ×ˢ Icc (0 : ℝ) 1) := by
    rcases eq_or_ne i j with rfl | hij
    · rw [inter_self]
      exact (hΨ i).image_eq
    · rw [hmeet i j hij, ((hfix i).mono inter_subset_left).image_eq,
        hφ.bijOn.injOn.image_inter (hsub i) (hsub j), hφrim i, hφrim j]
  obtain ⟨Φ, hΦ, hΦi⟩ := exists_isPLHomeomorphOn_iUnion
    (fun i => (show IsPLBall 2 (D i) from ⟨r i, hr i⟩).isPolyhedron.prod
      isHPolytope_Icc.isPolyhedron) hΨ hcompat hmeetImage
  rw [← iUnion_prod_const] at hΦ
  refine ⟨Φ, hΦ, ?_, ?_, ?_, fun i => (hΦi i).image_eq.trans (hΨ i).image_eq⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (hΦi i ⟨hi, by norm_num⟩).trans (hΨ₀ i x hi)
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (hΦi i ⟨hi, by norm_num⟩).trans (hΨ₁ i x hi)
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx.1
    exact (hΦi i ⟨hJD i hi, hx.2⟩).trans (hfix i ⟨hi, hx.2⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
