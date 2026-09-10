import DifferentialGeometry.Topology.Manifold.RegularLevel.Coordinates
import DifferentialGeometry.Topology.VectorField.Transport
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

set_option autoImplicit false

open Bundle Set Manifold
open scoped Topology ContDiff
open DifferentialGeometry.Topology.Morse Poincare.VectorField

noncomputable section
namespace Poincare.Manifold.RegularLevel

variable {m : ℕ} {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

theorem exists_local_unitSpeedField
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hr : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ V : (y : M) → TangentSpace I y,
        ContMDiffOn I I.tangent ∞ (fun y => (⟨y, V y⟩ : TangentBundle I M)) U ∧
        ∀ y ∈ U, (mfderiv I 𝓘(ℝ, ℝ) f y) (V y) = (-1 : ℝ) := by
  obtain ⟨Φ, hx, _, hcoord⟩ := exists_coordinates_of_contMDiffOn I isOpen_univ
    hf.contMDiffOn (mem_univ x) hr 0
  let J := 𝓘(ℝ, MorseModel (m + 1))
  let p : MorseModel (m + 1) →L[ℝ] ℝ := ContinuousLinearMap.proj (Fin.last m)
  let B : ∀ z : MorseModel (m + 1), TangentSpace J z := fun _ => levelSetLastBasis
  let V := _root_.VectorField.mpullback I J Φ B
  have hB : ContMDiff J J.tangent ∞
      (fun z => (⟨z, B z⟩ : TangentBundle J (MorseModel (m + 1)))) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_id, ?_⟩
    simpa [B, J] using (contMDiffAt_const (c := (levelSetLastBasis : MorseModel (m + 1))))
  refine ⟨Φ.source, Φ.open_source, hx, V,
    contMDiffOn_mpullback_partialDiffeomorph Φ (by simp) hB.contMDiffOn, ?_⟩
  intro y hy
  have heq : f ∘ Φ.symm =ᶠ[𝓝 (Φ y)] (fun z => -p z) := by
    filter_upwards [Φ.open_target.mem_nhds (Φ.map_source hy)] with z hz
    have hc := hcoord (Φ.symm z) (Φ.map_target hz)
    erw [Φ.right_inv hz] at hc
    change f (Φ.symm z) = -z (Fin.last m)
    linarith
  have hD := mfderiv_comp (Φ y) ((hf (Φ.symm (Φ y))).mdifferentiableAt (by simp))
    (Φ.symm.mdifferentiableAt (by simp) (Φ.map_source hy))
  have hneg : mfderiv J 𝓘(ℝ, ℝ) (fun z => -p z) (Φ y) = -p := by
    rw [mfderiv_eq_fderiv]
    exact (-p).fderiv
  erw [heq.mfderiv_eq, hneg, Φ.left_inv hy] at hD
  have hv := DFunLike.congr_fun hD (B (Φ y))
  change (mfderiv I 𝓘(ℝ, ℝ) f y)
    ((mfderiv I J Φ y).inverse (B (Φ y))) = (-1 : ℝ)
  rw [inverse_mfderiv_partialDiffeomorph Φ (by simp) hy]
  change -p (B (Φ y)) = (mfderiv I 𝓘(ℝ, ℝ) f y)
    ((mfderiv J I Φ.symm (Φ y)) (B (Φ y))) at hv
  exact hv.symm.trans (by simp [p, B, levelSetLastBasis])

theorem exists_unitSpeed_near_compact_regularSet_manifold
    [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {K : Set M} (hK : IsCompact K)
    (hr : ∀ x ∈ K, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ O : Set M, IsOpen O ∧ K ⊆ O ∧
      ∃ V : (y : M) → TangentSpace I y,
        ContMDiff I I.tangent ∞ (fun y => (⟨y, V y⟩ : TangentBundle I M)) ∧
        IsCompact (tsupport V) ∧
        ∀ y ∈ O, (mfderiv I 𝓘(ℝ, ℝ) f y) (V y) = (-1 : ℝ) := by
  classical
  have hlocal := fun x : K => exists_local_unitSpeedField I hf (hr x x.2)
  choose U hU hxU V hV hdf using hlocal
  have hcover : K ⊆ ⋃ x : K, U x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨W, hW, hKW, hclW, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK (isOpen_iUnion hU) hcover
  obtain ⟨O, hO, hKO, hclO, hOc⟩ :=
    exists_open_between_and_isCompact_closure hK hW hKW
  have hcoverO : closure O ⊆ ⋃ x : K, U x :=
    hclO.trans (subset_closure.trans hclW)
  obtain ⟨s, hs⟩ := hOc.elim_finite_subcover U hU hcoverO
  let A : Type _ := ↥s
  let D : A → Set M := fun i => U i.1 ∩ W
  have hD : ∀ i, IsOpen (D i) := fun i => (hU i.1).inter hW
  have hcoverD : closure O ⊆ ⋃ i : A, D i := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hs hy)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hyi, hclO hy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := I)
    isClosed_closure D hD hcoverD
  have hρzero : ∀ i : A, ∀ y ∉ D i, ρ i y = 0 := by
    intro i y hy
    exact image_eq_zero_of_notMem_tsupport (fun h => hy (hρ i h))
  let Z : (y : M) → TangentSpace I y := fun y => ∑ i : A, ρ i y • V i.1 y
  have hZ : ContMDiff I I.tangent ∞
      (fun y => (⟨y, Z y⟩ : TangentBundle I M)) := by
    apply ContMDiff.sum_section
    intro i _
    exact ContMDiffOn.smul_section_of_tsupport
      (ρ i).contMDiff.contMDiffOn (hD i) (hρ i)
      ((hV i.1).mono inter_subset_left)
  have hsupp : Function.support Z ⊆ W := by
    intro y hy
    by_contra hn
    apply hy
    change ∑ i : A, ρ i y • V i.1 y = 0
    apply Finset.sum_eq_zero
    intro i _
    rw [hρzero i y (fun hyD => hn hyD.2), zero_smul]
  refine ⟨O, hO, hKO, Z, hZ,
    hWc.of_isClosed_subset (isClosed_tsupport Z) (closure_mono hsupp), ?_⟩
  intro y hy
  let L : TangentSpace I y →L[ℝ] ℝ :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f y) : TangentSpace 𝓘(ℝ, ℝ) (f y) →L[ℝ] ℝ).comp
      (mfderiv I 𝓘(ℝ, ℝ) f y)
  change L (Z y) = -1
  have hterm : ∀ i : A, L (ρ i y • V i.1 y) = -(ρ i y) := by
    intro i
    by_cases hyD : y ∈ D i
    · have hv : L (V i.1 y) = -1 := hdf i.1 y hyD.1
      rw [map_smul, hv]
      simp
    · rw [hρzero i y hyD, zero_smul, map_zero, neg_zero]
  have hsum : ∑ i : A, ρ i y = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (subset_closure hy)
  change L (∑ i : A, ρ i y • V i.1 y) = -1
  rw [map_sum]
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib, hsum]

end Poincare.Manifold.RegularLevel
