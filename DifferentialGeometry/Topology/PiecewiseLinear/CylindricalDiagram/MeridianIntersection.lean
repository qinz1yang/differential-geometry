import DifferentialGeometry.Topology.PiecewiseLinear.CylinderCut
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.PLCompactModelEmbedding

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsCylindricalDiagram.exists_strip_containing_of_disjoint_bottom
    {f : E × ℝ → F} {S K : Set F} {D : Set E}
    (hf : IsCylindricalDiagram f D S) (hD : IsCompact D) (hK : IsClosed K)
    (hKS : K ⊆ S) (hne : K.Nonempty) (hdis : Disjoint K (f '' (D ×ˢ {0}))) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧ K ⊆ f '' (D ×ˢ Icc a b) := by
  let L := (D ×ˢ Icc (0 : ℝ) 1) ∩ f ⁻¹' K
  have hT : IsCompact (D ×ˢ Icc (0 : ℝ) 1) := hD.prod isCompact_Icc
  have hL : IsCompact L := hT.of_isClosed_subset
    (hf.isPiecewiseAffineOn.continuousOn.preimage_isClosed_of_isClosed hT.isClosed hK)
    inter_subset_left
  have hLne : L.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨p, hp, hpx⟩ := hf.image_eq.symm ▸ hKS hx
    exact ⟨p, hp, by change f p ∈ K; exact hpx.symm ▸ hx⟩
  have hstrict (p : E × ℝ) (hp : p ∈ L) : 0 < p.2 ∧ p.2 < 1 := by
    have hzero : p.2 ≠ 0 := by
      intro heq
      exact disjoint_left.mp hdis hp.2 ⟨p, ⟨hp.1.1, heq⟩, rfl⟩
    have hone : p.2 ≠ 1 := by
      intro heq
      apply disjoint_left.mp hdis hp.2
      rw [← hf.image_top_eq_bottom]
      exact ⟨p, ⟨hp.1.1, heq⟩, rfl⟩
    exact ⟨lt_of_le_of_ne hp.1.2.1 (Ne.symm hzero), lt_of_le_of_ne hp.1.2.2 hone⟩
  obtain ⟨p, hp, hmin⟩ := hL.exists_isMinOn hLne continuous_snd.continuousOn
  obtain ⟨q, hq, hmax⟩ := hL.exists_isMaxOn hLne continuous_snd.continuousOn
  have hp0 := (hstrict p hp).1
  have hq1 := (hstrict q hq).2
  have hpq : p.2 ≤ q.2 := hmin hq
  refine ⟨p.2 / 2, (q.2 + 1) / 2, by linarith, by linarith, by linarith, ?_⟩
  intro x hx
  obtain ⟨r, hr, hrx⟩ := hf.image_eq.symm ▸ hKS hx
  have hrL : r ∈ L := ⟨hr, by change f r ∈ K; exact hrx.symm ▸ hx⟩
  have hpr : p.2 ≤ r.2 := hmin hrL
  have hrq : r.2 ≤ q.2 := hmax hrL
  exact ⟨r, ⟨hr.1, by constructor <;> linarith⟩, hrx⟩

theorem IsPLHomeomorphInto.inter_nonempty_cylindrical_meridian_of_carrier
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set E} (hP : IsPLBall 2 P)
    {f : E × ℝ → EuclideanSpace ℝ (Fin 3)} {S V : Set (EuclideanSpace ℝ (Fin 3))}
    (hf : IsCylindricalDiagram f P S) {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u V) (hSV : S ⊆ V)
    (hS : IsTopologicalSolidTorus (u '' S)) {J : Set M}
    (hJ : IsCompact J) (hne : J.Nonempty) (hgen : CarriesFundamentalGroupOnto J (u '' S)) :
    (J ∩ u '' (f '' (P ×ˢ {(0 : ℝ)}))).Nonempty := by
  by_contra hnone
  have hdis : Disjoint J (u '' (f '' (P ×ˢ {(0 : ℝ)}))) :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnone)
  have hSc : IsCompact S := hf.image_eq ▸
    (hP.isPolyhedron.isCompact.prod isCompact_Icc).image_of_continuousOn
      hf.isPiecewiseAffineOn.continuousOn
  let K := S ∩ u ⁻¹' J
  have hK : IsClosed K :=
    (hu.continuousOn.mono hSV).preimage_isClosed_of_isClosed hSc.isClosed hJ.isClosed
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨p, hp, hpx⟩ := hgen.1 hx
    exact ⟨p, hp, by change u p ∈ J; exact hpx.symm ▸ hx⟩
  have hKdis : Disjoint K (f '' (P ×ˢ {(0 : ℝ)})) := by
    exact disjoint_left.mpr fun x hx hxb => disjoint_left.mp hdis hx.2 ⟨x, hxb, rfl⟩
  obtain ⟨a, b, ha, hab, hb, hKB⟩ := hf.exists_strip_containing_of_disjoint_bottom
    hP.isPolyhedron.isCompact hK inter_subset_left hKne hKdis
  let B := f '' (P ×ˢ Icc a b)
  have hB : IsPLBall 3 B := (isPLBall_three_prod hP (isPLBall_Icc hab)).of_isPLHomeomorphOn
    (hf.isPLHomeomorphOn_strip hP.isPolyhedron ha.le hb.le (Or.inl ha))
  have hBS : B ⊆ S := by
    rw [← hf.image_eq]
    exact image_mono fun x hx => ⟨hx.1, ha.le.trans hx.2.1, hx.2.2.trans hb.le⟩
  have huB : IsPLHomeomorphInto 3 u B :=
    (hu.isPLOn.mono_of_isPolyhedron hB.isPolyhedron (hBS.trans hSV)).isPLHomeomorphInto_model
      hB.isPolyhedron.isCompact (hu.injOn.mono (hBS.trans hSV))
  obtain ⟨r, hr⟩ := hB
  have hcell := (isPLCellOn_id_of_isPLBall hr).image huB
  have hJB : J ⊆ u '' B := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hgen.1 hx
    exact ⟨p, hKB ⟨hp, by change u p ∈ J; exact hpx.symm ▸ hx⟩, hpx⟩
  exact hS.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hcell
    (image_mono hBS) hne hJB hgen

end DifferentialGeometry.Topology.PiecewiseLinear
