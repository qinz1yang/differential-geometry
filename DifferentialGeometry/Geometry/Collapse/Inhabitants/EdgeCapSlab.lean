import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapFlow
import DifferentialGeometry.Geometry.Collapse.EdgeModelFibreDisk
import DifferentialGeometry.Geometry.Collapse.EdgeRowSequence
import DifferentialGeometry.Topology.Diffeomorph.Restriction
import Mathlib.Analysis.Calculus.FDeriv.Norm
import DifferentialGeometry.Topology.Embedding.Diffeomorph
set_option autoImplicit false
noncomputable section
open Bundle Set Function Manifold Metric
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapDistance
open DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
open DifferentialGeometry.Geometry.Collapse.EdgeCapHeight
open DifferentialGeometry.Geometry.Collapse.EdgeCapFlow
open DifferentialGeometry.Analysis DifferentialGeometry.Topology
attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Collapse.EdgeCapSlab

theorem delta_pos : 0 < capExampleDelta :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 100000000) capExampleDelta_large

def radialHeight (z : E2) : ℝ := capCollarHeight capExampleEpsilon z

theorem radialHeight_smooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ radialHeight :=
  (capCollarHeight_smooth _).contMDiff

def productSlab : TopologicalSpace.Opens (ℝ × E2) :=
  ⟨{p | |p.1| < 5 * capExampleDelta ∧ radialHeight p.2 < 5 * capExampleDelta},
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      (isOpen_lt (radialHeight_smooth.continuous.comp continuous_snd) continuous_const)⟩

def rowHeight (p : ℝ × E2) : ℝ :=
  edgeRowHeight capExampleDelta (fun q => radialHeight q.2) (fun _ => 1) p

theorem rowHeight_smooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ rowHeight := by
  unfold rowHeight edgeRowHeight
  simp only [div_one]
  exact contMDiff_const.mul
    (contDiff_edgeSublevelProfile.contMDiff.comp
      ((radialHeight_smooth.comp contMDiff_snd).div_const capExampleDelta))

def slabCoord (p : productSlab) : ℝ := (p : ℝ × E2).1

def slabBoundary (p : productSlab) : ℝ := 4 * capExampleDelta - rowHeight p

theorem slabCoord_smooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ slabCoord :=
  contMDiff_fst.comp contMDiff_subtype_val

theorem slabBoundary_smooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ slabBoundary :=
  contMDiff_const.sub (rowHeight_smooth.comp contMDiff_subtype_val)

theorem slabCoord_regular (p : productSlab) :
    Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) slabCoord p) := by
  change Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ)
    ((fun q : ℝ × E2 => q.1) ∘ Subtype.val) p)
  rw [mfderiv_comp p mdifferentiableAt_fst
    (DifferentialGeometry.hasMFDerivAt_subtype_val productSlab p).mdifferentiableAt,
    DifferentialGeometry.mfderiv_subtype_val, mfderiv_fst]
  intro r
  exact ⟨(r, 0), rfl⟩

theorem rowHeight_boundary_radius (p : ℝ × E2)
    (hb : rowHeight p = 4 * capExampleDelta) :
    capExampleEpsilon * ‖p.2‖ = 4 * capExampleDelta := by
  have hF : radialHeight p.2 = 4 * capExampleDelta := by
    by_cases hq : radialHeight p.2 / capExampleDelta ≤ 2
    · have hh := edgeSublevelProfile_le_two hq
      unfold rowHeight edgeRowHeight at hb
      simp only [div_one] at hb
      nlinarith [delta_pos]
    · unfold rowHeight edgeRowHeight at hb
      simp only [div_one] at hb
      rw [edgeSublevelProfile_eq_self (le_of_lt (lt_of_not_ge hq))] at hb
      have hmul : capExampleDelta * (radialHeight p.2 / capExampleDelta) =
          radialHeight p.2 := by field_simp [delta_pos.ne']
      rwa [hmul] at hb
  have hle := capCollarHeight_le_radius capExampleEpsilon capExampleEpsilon_pos.le p.2
  have hn : 9 ≤ ‖p.2‖ := by
    change radialHeight p.2 ≤ capExampleEpsilon * ‖p.2‖ at hle
    have he := capExampleDelta_height_error
    rw [hF] at hle
    nlinarith [capExampleEpsilon_pos]
  unfold radialHeight capCollarHeight at hF
  rwa [capRadialProfile_linear hn] at hF

theorem rowHeight_boundary_eventually (p : ℝ × E2)
    (hb : rowHeight p = 4 * capExampleDelta) :
    rowHeight =ᶠ[𝓝 p] fun q => capExampleEpsilon * ‖q.2‖ := by
  have hr := rowHeight_boundary_radius p hb
  have hn : 9 < ‖p.2‖ := by
    have he := capExampleDelta_height_error
    nlinarith [capExampleEpsilon_pos]
  have hfar : ∀ᶠ q : ℝ × E2 in 𝓝 p, 9 < ‖q.2‖ :=
    ((continuous_norm.comp continuous_snd).continuousAt).eventually (lt_mem_nhds hn)
  have hscaled : ∀ᶠ q : ℝ × E2 in 𝓝 p,
      2 * capExampleDelta < capExampleEpsilon * ‖q.2‖ :=
    ((continuous_const.mul (continuous_norm.comp continuous_snd)).continuousAt).eventually
      (lt_mem_nhds (by
        change 2 * capExampleDelta < capExampleEpsilon * ‖p.2‖
        rw [hr]; linarith [delta_pos]))
  filter_upwards [hfar, hscaled] with q hq hq'
  change capExampleDelta * edgeSublevelProfile
    (capExampleEpsilon * capRadialProfile ‖q.2‖ / 1 / capExampleDelta) = _
  rw [capRadialProfile_linear hq.le]
  simp only [div_one]
  rw [edgeSublevelProfile_eq_self (by
    rw [le_div_iff₀ delta_pos]; linarith)]
  field_simp [delta_pos.ne']

theorem slabBoundary_regular (p : productSlab) (hb : slabBoundary p = 0) :
    Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
      (fun q : productSlab => (slabCoord q, slabBoundary q)) p) := by
  have hh : rowHeight (p : ℝ × E2) = 4 * capExampleDelta := by
    change 4 * capExampleDelta - rowHeight (p : ℝ × E2) = 0 at hb
    linarith
  have hr := rowHeight_boundary_radius (p : ℝ × E2) hh
  have hz : (p : ℝ × E2).2 ≠ 0 := by
    intro hz
    rw [hz, norm_zero, mul_zero] at hr
    linarith [delta_pos]
  have hn : DifferentiableAt ℝ (norm : E2 → ℝ) (p : ℝ × E2).2 :=
    (contDiffAt_norm (n := (1 : ℕ∞ω)) ℝ hz).differentiableAt (by norm_num)
  let L : E2 →L[ℝ] ℝ := fderiv ℝ (norm : E2 → ℝ) (p : ℝ × E2).2
  have hL : L (p : ℝ × E2).2 = ‖(p : ℝ × E2).2‖ := hn.fderiv_norm_self
  have hN : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ)
      (fun q : ℝ × E2 => ‖q.2‖) (p : ℝ × E2)
      (L.comp (ContinuousLinearMap.snd ℝ ℝ E2)) :=
    hn.hasFDerivAt.hasMFDerivAt.comp (p : ℝ × E2)
      (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2) (p : ℝ × E2))
  have hB := (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ).prod (𝓡 2))
    (I' := 𝓘(ℝ, ℝ)) (4 * capExampleDelta) (p : ℝ × E2)).sub
    (hN.const_smul capExampleEpsilon)
  have hfst := hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2) (p : ℝ × E2)
  have hpair : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
      (fun q : ℝ × E2 => (q.1, 4 * capExampleDelta - capExampleEpsilon * ‖q.2‖))
      (p : ℝ × E2)
      ((ContinuousLinearMap.fst ℝ ℝ E2).prod
        (0 - capExampleEpsilon • L.comp (ContinuousLinearMap.snd ℝ ℝ E2))) :=
    ⟨hfst.1.prodMk hB.1, hfst.2.prodMk hB.2⟩
  have he := rowHeight_boundary_eventually (p : ℝ × E2) hh
  have hepair : (fun q : ℝ × E2 => (q.1, 4 * capExampleDelta - rowHeight q)) =ᶠ[𝓝 ↑p]
      fun q => (q.1, 4 * capExampleDelta - capExampleEpsilon * ‖q.2‖) := by
    filter_upwards [he] with q hq
    rw [hq]
  have hactual := hpair.congr_of_eventuallyEq_abuse hepair
  change Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
    (fun q : productSlab => ((q : ℝ × E2).1, 4 * capExampleDelta - rowHeight q)) p)
  rw [DifferentialGeometry.mfderiv_restrict_open
    (fun q : ℝ × E2 => (q.1, 4 * capExampleDelta - rowHeight q)) productSlab p,
    hactual.mfderiv]
  intro v
  refine ⟨(v.1, (-(v.2) / (4 * capExampleDelta)) • (p : ℝ × E2).2), ?_⟩
  apply Prod.ext
  · rfl
  · simp only [zero_sub]
    change -(capExampleEpsilon * L ((-(v.2) / (4 * capExampleDelta)) •
      (p : ℝ × E2).2)) = v.2
    rw [map_smul, smul_eq_mul, hL]
    rw [mul_left_comm, hr]
    field_simp [delta_pos.ne']

def diskRadius : ℝ := 4 * capExampleDelta / capExampleEpsilon

theorem diskRadius_pos : 0 < diskRadius :=
  div_pos (mul_pos (by norm_num) delta_pos) capExampleEpsilon_pos

def diskScaling : E2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ E2 :=
  (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E2)
    (Units.mk0 diskRadius diskRadius_pos.ne')).toDiffeomorph

def diskEmbedding (z : ClosedCell 2) : E2 := diskScaling z

theorem diskEmbedding_smoothEmbedding :
    IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ diskEmbedding :=
  (Handle.closedCellInclusion_isSmoothEmbedding 1).diffeomorph_comp diskScaling

theorem diskEmbedding_range : range diskEmbedding = {z : E2 | ‖z‖ ≤ diskRadius} := by
  ext z
  constructor
  · rintro ⟨b, rfl⟩
    change ‖diskRadius • (b : E2)‖ ≤ diskRadius
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos diskRadius_pos]
    nlinarith [b.2, diskRadius_pos]
  · intro hz
    let b : ClosedCell 2 := ⟨diskRadius⁻¹ • z, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr diskRadius_pos)]
      exact (inv_mul_le_iff₀ diskRadius_pos).mpr (by simpa using hz)⟩
    refine ⟨b, ?_⟩
    change diskRadius • (diskRadius⁻¹ • z) = z
    rw [smul_smul, mul_inv_cancel₀ diskRadius_pos.ne', one_smul]

theorem diskEmbedding_fibre_range : range diskEmbedding =
    {z : E2 | ((0 : ℝ), z) ∈ productSlab ∧ rowHeight (0, z) ≤ 4 * capExampleDelta} := by
  rw [diskEmbedding_range]
  ext z
  have hr : 9 * capExampleEpsilon ≤ 4 * capExampleDelta := by
    linarith [capExampleDelta_height_error, delta_pos]
  have hH : rowHeight (0, z) ≤ 4 * capExampleDelta ↔
      capExampleEpsilon * ‖z‖ ≤ 4 * capExampleDelta := by
    change edgeRowHeight capExampleDelta _ _ (0, z) ≤ _ ↔ _
    rw [edgeRowHeight_le_iff delta_pos]
    simp only [div_one]
    exact capCollarHeight_sublevel capExampleEpsilon_pos hr
  constructor
  · intro hz
    change ‖z‖ ≤ diskRadius at hz
    have hn : capExampleEpsilon * ‖z‖ ≤ 4 * capExampleDelta := by
      rw [diskRadius, le_div_iff₀ capExampleEpsilon_pos] at hz
      nlinarith
    refine ⟨?_, hH.mpr hn⟩
    change |(0 : ℝ)| < 5 * capExampleDelta ∧ radialHeight z < 5 * capExampleDelta
    refine ⟨by simp only [abs_zero]; exact mul_pos (by norm_num) delta_pos, ?_⟩
    exact (capCollarHeight_le_radius _ capExampleEpsilon_pos.le z).trans_lt
      (by linarith [delta_pos])
  · intro hz
    change ‖z‖ ≤ diskRadius
    rw [diskRadius, le_div_iff₀ capExampleEpsilon_pos]
    nlinarith [hH.mp hz.2]

def diskLift (c : ClosedCell 2) : productSlab :=
  ⟨(0, diskEmbedding c), ((diskEmbedding_fibre_range ▸ mem_range_self c)).1⟩

theorem diskLift_smooth : ContMDiff (𝓡∂ 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ diskLift := by
  apply (ContMDiff.subtypeVal_comp_iff productSlab diskLift).mp
  exact contMDiff_const.prodMk diskEmbedding_smoothEmbedding.contMDiff

theorem diskLift_surjective (p : productSlab) (hp : slabCoord p = 0)
    (hB : 0 ≤ slabBoundary p) : ∃ c : ClosedCell 2, diskLift c = p := by
  have hmem : (p : ℝ × E2).2 ∈ range diskEmbedding := by
    rw [diskEmbedding_fibre_range]
    refine ⟨?_, ?_⟩
    · have he : ((0 : ℝ), (p : ℝ × E2).2) = (p : ℝ × E2) :=
        Prod.ext hp.symm rfl
      rw [he]
      exact p.2
    · exact sub_nonneg.mp hB
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  apply Subtype.ext
  exact Prod.ext hp.symm hc

theorem fibre_disk :
    let _ := DifferentialGeometry.Manifold.RegularLevel.regularSublevelChartedSpace
      finrank_real_prod_euclideanTwo slabCoord_smooth slabBoundary_smooth
      (fun p _ _ => slabCoord_regular p) (fun p _ hb => slabBoundary_regular p hb)
    Nonempty (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯
      {p : productSlab // slabCoord p = 0 ∧ 0 ≤ slabBoundary p}) := by
  refine nonempty_diffeomorph_regularSublevel_of_lift
    finrank_real_prod_euclideanTwo slabCoord_smooth slabBoundary_smooth
    (fun p _ _ => slabCoord_regular p) (fun p _ hb => slabBoundary_regular p hb)
    diskEmbedding_smoothEmbedding
    (show ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun p : productSlab => (p : ℝ × E2).2) from
      contMDiff_snd.comp contMDiff_subtype_val) diskLift_smooth ?_ ?_ ?_
  · intro c
    refine ⟨rfl, ?_⟩
    apply sub_nonneg.mpr
    exact ((diskEmbedding_fibre_range ▸ mem_range_self c)).2
  · intro c
    rfl
  · exact diskLift_surjective

def ambientFlow (t : ℝ) :
    (ℝ × E2) ≃ₘ⟮𝓘(ℝ, ℝ).prod (𝓡 2), 𝓘(ℝ, ℝ).prod (𝓡 2)⟯ (ℝ × E2) :=
  (capScalarFlow capExampleDelta delta_pos t).prodCongr (Diffeomorph.refl (𝓡 2) E2 ∞)

theorem ambientFlow_joint :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (𝓡 2))) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (fun q : ℝ × (ℝ × E2) => ambientFlow q.1 q.2) :=
  ((capScalarFlow_joint capExampleDelta delta_pos).comp
    (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
      (contMDiff_snd.comp contMDiff_snd)

theorem ambientFlow_preserves (t : ℝ) {p : ℝ × E2} :
    p ∈ productSlab ↔ ambientFlow t p ∈ productSlab := by
  change (|p.1| < 5 * capExampleDelta ∧ radialHeight p.2 < 5 * capExampleDelta) ↔
    (|capScalarFlow capExampleDelta delta_pos t p.1| < 5 * capExampleDelta ∧
      radialHeight p.2 < 5 * capExampleDelta)
  constructor
  · intro h
    exact ⟨capScalarFlow_preserves_interval _ _ _ h.1 t, h.2⟩
  · intro h
    have hn := capScalarFlow_preserves_interval capExampleDelta delta_pos
      (capScalarFlow capExampleDelta delta_pos t p.1) h.1 (-t)
    rw [← capScalarFlow_symm] at hn
    simpa only [Diffeomorph.symm_apply_apply] using And.intro hn h.2

theorem ambientFlow_zero :
    ambientFlow 0 = Diffeomorph.refl (𝓘(ℝ, ℝ).prod (𝓡 2)) (ℝ × E2) ∞ := by
  apply DFunLike.ext
  intro p
  exact Prod.ext
    (congrArg (fun D => D p.1) (capScalarFlow_zero capExampleDelta delta_pos)) rfl

theorem ambientFlow_add (s t : ℝ) :
    (ambientFlow s).trans (ambientFlow t) = ambientFlow (s + t) := by
  apply DFunLike.ext
  intro p
  exact Prod.ext
    (congrArg (fun D => D p.1) (capScalarFlow_add capExampleDelta delta_pos s t)) rfl

def slabFlow (t : ℝ) :
    productSlab ≃ₘ⟮𝓘(ℝ, ℝ).prod (𝓡 2), 𝓘(ℝ, ℝ).prod (𝓡 2)⟯ productSlab :=
  (ambientFlow t).restrict (fun p => ambientFlow_preserves t (p := p))

theorem slabFlow_joint :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (𝓡 2))) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (fun q : ℝ × productSlab => slabFlow q.1 q.2) :=
  Diffeomorph.contMDiff_restrict ambientFlow ambientFlow_joint
    (fun t p => ambientFlow_preserves t (p := p))

theorem slabFlow_zero :
    slabFlow 0 = Diffeomorph.refl (𝓘(ℝ, ℝ).prod (𝓡 2)) productSlab ∞ := by
  apply DFunLike.ext
  intro p
  apply Subtype.ext
  exact congrArg (fun D => D (p : ℝ × E2)) ambientFlow_zero

theorem slabFlow_add (s t : ℝ) : (slabFlow s).trans (slabFlow t) = slabFlow (s + t) := by
  apply DFunLike.ext
  intro p
  apply Subtype.ext
  exact congrArg (fun D => D (p : ℝ × E2)) (ambientFlow_add s t)

theorem slabFlow_height (t : ℝ) (p : productSlab) :
    rowHeight (slabFlow t p) = rowHeight p := rfl

theorem slabFlow_central (p : productSlab) (hp : slabCoord p = 0) (t : ℝ)
    (ht : |t| < 4 * capExampleDelta) : slabCoord (slabFlow t p) = t := by
  change capScalarFlow capExampleDelta delta_pos t (p : ℝ × E2).1 = t
  change (p : ℝ × E2).1 = 0 at hp
  rw [hp]
  exact capScalarFlow_translation _ _ _ ht

def sourceSlab : TopologicalSpace.Opens E3 :=
  ⟨capProductCoordinates.symm ⁻¹' (productSlab : Set (ℝ × E2)),
    productSlab.isOpen.preimage capProductCoordinates.symm.continuous⟩

def slabCoordinates :
    productSlab ≃ₘ⟮𝓘(ℝ, ℝ).prod (𝓡 2), 𝓡 3⟯ sourceSlab :=
  capProductCoordinates.restrict (fun p => by
    change p ∈ productSlab ↔ capProductCoordinates.symm (capProductCoordinates p) ∈ productSlab
    rw [Diffeomorph.symm_apply_apply])

def nativeSlabCoordinates :
    letI := DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph
      (M := sourceSlab) euclideanThreeProdHomeomorph
    productSlab ≃ₘ⟮𝓘(ℝ, ℝ).prod (𝓡 2), 𝓘(ℝ, ℝ).prod (𝓡 2)⟯ sourceSlab := by
  letI := DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph
    (M := sourceSlab) euclideanThreeProdHomeomorph
  exact {
    toEquiv := slabCoordinates.toEquiv
    contMDiff_toFun := (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
      (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) euclideanThreeProdHomeomorph
      euclideanThreeProdEquiv euclideanThreeProd_compat
      (𝓘(ℝ, ℝ).prod (𝓡 2))).mpr slabCoordinates.contMDiff
    contMDiff_invFun :=
      (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_source_iff
        (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) euclideanThreeProdHomeomorph
        euclideanThreeProdEquiv euclideanThreeProd_compat
        (𝓘(ℝ, ℝ).prod (𝓡 2))).mpr slabCoordinates.symm.contMDiff }

section NativeSource
local instance sourceNativeChart : ChartedSpace (ModelProd ℝ E2) sourceSlab :=
  DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph
    (M := sourceSlab) euclideanThreeProdHomeomorph
local instance sourceNativeManifold :
    IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ sourceSlab := edgeSource_isManifold

def sourceCoord (x : sourceSlab) : ℝ := capThreeCoord x

def sourceBoundary (x : sourceSlab) : ℝ :=
  slabBoundary (nativeSlabCoordinates.symm x)

theorem nativeSlabCoordinates_symm_val (x : sourceSlab) :
    (nativeSlabCoordinates.symm x : ℝ × E2) = capProductCoordinates.symm x := rfl

theorem sourceBoundary_literal (x : sourceSlab) : sourceBoundary x =
    4 * capExampleDelta - edgeRowHeight capExampleDelta capExampleF (fun _ => 1) x := by
  change 4 * capExampleDelta - rowHeight (nativeSlabCoordinates.symm x) = _
  unfold rowHeight edgeRowHeight radialHeight
  rw [nativeSlabCoordinates_symm_val]
  rfl

theorem sourceCoord_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ sourceCoord :=
  slabCoord_smooth.comp nativeSlabCoordinates.symm.contMDiff

theorem sourceBoundary_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ sourceBoundary :=
  slabBoundary_smooth.comp nativeSlabCoordinates.symm.contMDiff

theorem sourceCoord_regular (x : sourceSlab) :
    Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) sourceCoord x) := by
  change Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ)
    (slabCoord ∘ nativeSlabCoordinates.symm) x)
  rw [mfderiv_comp x
    ((slabCoord_smooth _).mdifferentiableAt (by simp))
    ((nativeSlabCoordinates.symm.contMDiff _).mdifferentiableAt (by simp))]
  exact (slabCoord_regular (nativeSlabCoordinates.symm x)).comp
    (nativeSlabCoordinates.symm.mfderivToContinuousLinearEquiv (by simp) x).surjective

theorem sourceBoundary_regular (x : sourceSlab) (hb : sourceBoundary x = 0) :
    Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
      (fun q : sourceSlab => (sourceCoord q, sourceBoundary q)) x) := by
  change Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
    ((fun q : productSlab => (slabCoord q, slabBoundary q)) ∘ nativeSlabCoordinates.symm) x)
  rw [mfderiv_comp x
    (((slabCoord_smooth _).mdifferentiableAt (by simp)).prodMk_space
      ((slabBoundary_smooth _).mdifferentiableAt (by simp)))
    ((nativeSlabCoordinates.symm.contMDiff _).mdifferentiableAt (by simp))]
  exact (slabBoundary_regular (nativeSlabCoordinates.symm x) hb).comp
    (nativeSlabCoordinates.symm.mfderivToContinuousLinearEquiv (by simp) x).surjective
theorem sourceCoord_model (x : sourceSlab) :
    sourceCoord x = slabCoord (nativeSlabCoordinates.symm x) := rfl

def sourceDiskLift (c : ClosedCell 2) : sourceSlab := nativeSlabCoordinates (diskLift c)

theorem sourceDiskLift_val (c : ClosedCell 2) :
    (sourceDiskLift c : E3) = capProductCoordinates (0, diskEmbedding c) := rfl

def sourceRadialProjection (x : sourceSlab) : E2 :=
  (nativeSlabCoordinates.symm x : ℝ × E2).2

theorem sourceDiskLift_smooth :
    ContMDiff (𝓡∂ 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ sourceDiskLift :=
  nativeSlabCoordinates.contMDiff.comp diskLift_smooth

theorem sourceRadialProjection_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ sourceRadialProjection :=
  (contMDiff_snd.comp contMDiff_subtype_val).comp nativeSlabCoordinates.symm.contMDiff

theorem sourceDiskLift_coord (c : ClosedCell 2) : sourceCoord (sourceDiskLift c) = 0 := by
  rw [sourceCoord_model]
  change slabCoord (nativeSlabCoordinates.symm (nativeSlabCoordinates (diskLift c))) = 0
  rw [Diffeomorph.symm_apply_apply]
  rfl

theorem sourceDiskLift_boundary (c : ClosedCell 2) :
    0 ≤ sourceBoundary (sourceDiskLift c) := by
  change 0 ≤ slabBoundary (nativeSlabCoordinates.symm
    (nativeSlabCoordinates (diskLift c)))
  rw [Diffeomorph.symm_apply_apply]
  apply sub_nonneg.mpr
  exact ((diskEmbedding_fibre_range ▸ mem_range_self c)).2

theorem sourceDiskLift_projection (c : ClosedCell 2) :
    sourceRadialProjection (sourceDiskLift c) = diskEmbedding c := by
  unfold sourceRadialProjection sourceDiskLift
  rw [Diffeomorph.symm_apply_apply]
  rfl

theorem sourceDiskLift_surjective (x : sourceSlab) (hc : sourceCoord x = 0)
    (hB : 0 ≤ sourceBoundary x) : ∃ c : ClosedCell 2, sourceDiskLift c = x := by
  rw [sourceCoord_model] at hc
  obtain ⟨c, hce⟩ := diskLift_surjective (nativeSlabCoordinates.symm x) hc hB
  refine ⟨c, ?_⟩
  unfold sourceDiskLift
  rw [hce, Diffeomorph.apply_symm_apply]

theorem sourceFibre_disk :
    let _ := DifferentialGeometry.Manifold.RegularLevel.regularSublevelChartedSpace
      finrank_real_prod_euclideanTwo sourceCoord_smooth sourceBoundary_smooth
      (fun x _ _ => sourceCoord_regular x) (fun x _ hb => sourceBoundary_regular x hb)
    Nonempty (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯
      {x : sourceSlab // sourceCoord x = 0 ∧ 0 ≤ sourceBoundary x}) := by
  exact nonempty_diffeomorph_regularSublevel_of_lift
    finrank_real_prod_euclideanTwo sourceCoord_smooth sourceBoundary_smooth
    (fun x _ _ => sourceCoord_regular x) (fun x _ hb => sourceBoundary_regular x hb)
    diskEmbedding_smoothEmbedding sourceRadialProjection_smooth sourceDiskLift_smooth
    (fun c => ⟨sourceDiskLift_coord c, sourceDiskLift_boundary c⟩)
    sourceDiskLift_projection sourceDiskLift_surjective
theorem sourceFibre_boundary :
    let _ := DifferentialGeometry.Manifold.RegularLevel.regularSublevelChartedSpace
      finrank_real_prod_euclideanTwo sourceCoord_smooth sourceBoundary_smooth
      (fun x _ _ => sourceCoord_regular x) (fun x _ hb => sourceBoundary_regular x hb)
    ∀ {x : {x : sourceSlab // sourceCoord x = 0 ∧ 0 ≤ sourceBoundary x}},
      (𝓡∂ 2).IsBoundaryPoint x ↔
        edgeRowHeight capExampleDelta capExampleF (fun _ => 1) (x : sourceSlab) =
          4 * capExampleDelta := by
  let _ := DifferentialGeometry.Manifold.RegularLevel.regularSublevelChartedSpace
    finrank_real_prod_euclideanTwo sourceCoord_smooth sourceBoundary_smooth
    (fun x _ _ => sourceCoord_regular x) (fun x _ hb => sourceBoundary_regular x hb)
  intro x
  refine (DifferentialGeometry.Manifold.RegularLevel.regularSublevel_isBoundaryPoint_iff
    finrank_real_prod_euclideanTwo sourceCoord_smooth sourceBoundary_smooth
    (fun x _ _ => sourceCoord_regular x) (fun x _ hb => sourceBoundary_regular x hb)).trans ?_
  rw [sourceBoundary_literal]
  constructor <;> intro h <;> linarith
end NativeSource

section ActualDistance
attribute [local instance] capExampleSigma capExampleMetricSpace capExampleEDist
  capExampleDist capExampleUniform capExampleEMetric capExamplePseudo capExampleBundle
  capExampleRiemannian capExampleContinuous capExampleComplete capExampleProper capExampleDimension

theorem sourceSlab_subset_ball :
    (sourceSlab : Set E3) ⊆ ball (capExampleAxis 0) (20 * capExampleDelta) := by
  intro x hx
  change |capThreeCoord x| < 5 * capExampleDelta ∧
    capExampleF x < 5 * capExampleDelta at hx
  exact capExample_open_slab_bound x hx.1 hx.2

theorem whole_closed_slab_subset {x : E3}
    (hc : |capThreeCoord x| ≤ 4 * capExampleDelta)
    (hH : edgeRowHeight capExampleDelta capExampleF (fun _ => 1) x ≤ 4 * capExampleDelta) :
    x ∈ sourceSlab := by
  have hF := (edgeRowHeight_le_iff delta_pos).mp hH
  simp only [div_one] at hF
  change |capThreeCoord x| < 5 * capExampleDelta ∧ capExampleF x < 5 * capExampleDelta
  constructor <;> linarith [delta_pos]
end ActualDistance

end DifferentialGeometry.Geometry.Collapse.EdgeCapSlab
