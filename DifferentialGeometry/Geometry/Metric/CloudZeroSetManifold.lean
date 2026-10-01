import DifferentialGeometry.Geometry.Metric.CloudSubmersion
import DifferentialGeometry.Topology.Manifold.LocalZeroSetManifold
import DifferentialGeometry.Topology.Maps.RelativeZeroSet

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open scoped BigOperators NNReal ContDiff Manifold Topology
namespace GC.MetricGeometry
universe u

theorem exists_buffered_normal_zero_set_manifold
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (k : ℕ) (I : Set H) (r : H → ℝ)
    (P : H → Submodule ℝ H) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hr : ∀ i ∈ I, 0 < r i) (hP : ∀ i ∈ I, Module.finrank ℝ (P i) = k)
    (η : H → H)
    (hη : ContDiffOn ℝ ∞ η (⋃ i ∈ I, ball i (6 * ℓ * r i)))
    (hlocal : ∀ i ∈ I, ∀ v ∈ ball i (5 * ℓ * r i),
      (∀ z ∈ ball v (ℓ * r i), Manifold.IsSubmersionAt
        𝓘(ℝ, H) 𝓘(ℝ, (P i)ᗮ) ∞ (fun y => (P i)ᗮ.orthogonalProjectionOnto (η y)) z) ∧
      {z : H | z ∈ ball v (ℓ * r i) ∧ (P i)ᗮ.orthogonalProjectionOnto (η z) = 0} =
      {z : H | z ∈ ball v (ℓ * r i) ∧ η z = 0}) :
    let Ω : Set H := ⋃ i ∈ I, ball i (6 * ℓ * r i)
    let Z : Set H := {z | z ∈ Ω ∧ η z = 0}
    ∃ cs : ChartedSpace (Fin k → ℝ) Z,
      let _ := cs
      IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H) := by
  classical
  let Ω : Set H := ⋃ i ∈ I, ball i (6 * ℓ * r i)
  let Z : Set H := {z | z ∈ Ω ∧ η z = 0}
  have hcover (x : Z) : ∃ i ∈ I, ∃ v ∈ ball i (5 * ℓ * r i), (x : H) ∈ ball v (ℓ * r i) := by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp x.property.1
    have hri := hr i hi
    have hsum : 6 * ℓ * r i = 5 * ℓ * r i+ℓ * r i := by ring
    rw [hsum, ← Metric.biUnion_ball_of_mem_ball_eq_ball_add i
      (by positivity : 0 < 5 * ℓ * r i) (mul_pos hℓ (hr i hi))] at hxi
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxi
    exact ⟨i, hi, v, hv, hxv⟩
  choose i hi v hv hx using hcover
  let F : Z → Type u := fun x => (P (i x))ᗮ
  let U : Z → Set H := fun x => ball (v x) (ℓ*r (i x))
  let f : ∀ x : Z, H → F x := fun x y => (P (i x))ᗮ.orthogonalProjectionOnto (η y)
  let n := Module.finrank ℝ H - k
  have hsum (x : Z) : k + Module.finrank ℝ (F x) = Module.finrank ℝ H := by
    have hh := (P (i x)).finrank_add_finrank_orthogonal
    rwa [hP (i x) (hi x)] at hh
  have hF (x : Z) : Module.finrank ℝ (F x) = n := by
    have hh := hsum x
    dsimp [n]
    omega
  have hdim (x : Z) : Module.finrank ℝ H = n + k := by
    have hh := hsum x
    rw [hF x] at hh
    omega
  have hUΩ (x : Z) : U x ⊆ Ω := by
    intro y hy
    apply mem_iUnion₂.mpr ⟨i x, hi x, ?_⟩
    have hdist := dist_triangle y (v x) (i x)
    have hv' : dist (v x) (i x) < 5*ℓ*r (i x) := hv x
    have hy' : dist y (v x) < ℓ*r (i x) := hy
    change dist y (i x) < 6*ℓ*r (i x)
    linarith
  have hf (x : Z) : ContDiffOn ℝ ∞ (f x) (U x) :=
    (P (i x))ᗮ.orthogonalProjectionOnto.contDiff.comp_contDiffOn (hη.mono (hUΩ x))
  have hsurj (x : Z) : Function.Surjective (fderiv ℝ (f x) (x : H)) := by
    have hs := mfderiv_hasRightInverse_of_isSubmersionAt
      ((hlocal (i x) (hi x) (v x) (hv x)).1 x (hx x))
    intro y
    obtain ⟨v, hv⟩ := hs.surjective ((NormedSpace.fromTangentSpace (f x (x : H))).symm y)
    refine ⟨NormedSpace.fromTangentSpace (x : H) v, ?_⟩
    have hh := congrArg (NormedSpace.fromTangentSpace (f x (x : H))) hv
    simpa only [f, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using hh
  have hzero (x : Z) (y : H) (hy : y ∈ U x) : y ∈ Z ↔ f x y = 0 := by
    have hh := Set.ext_iff.mp ((hlocal (i x) (hi x) (v x) (hv x)).2) y
    have heq : f x y = 0 ↔ η y = 0 := by
      change (y ∈ U x ∧ f x y = 0) ↔ (y ∈ U x ∧ η y = 0) at hh
      simpa only [hy, true_and] using hh
    change (y ∈ Ω ∧ η y = 0) ↔ f x y = 0
    simpa only [hUΩ x hy, true_and] using heq.symm
  exact exists_local_zero_set_manifold Z n k hdim F hF U (fun _ => isOpen_ball) hx f hf hsurj hzero

theorem exists_uniform_cloud_zero_set_manifold
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ →
        (∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x)) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        let ℓ : ℝ := 1 / (100 * (C + 1))
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (ℓ * r i)) ∧
          ((⋃ x ∈ S, ball x (ℓ * r x)) ⊆ ⋃ i ∈ I, ball i (5 * ℓ * r i)) ∧
          let w : H → H → ℝ := fun i y =>
            ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)
          let Q : H → Submodule ℝ H := fun y =>
            ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          let η : H → H := fun y => (Q y).starProjection
            (y - ∑ i ∈ hI.toFinset, w i y • i)
          let Ω : Set H := ⋃ i ∈ I, ball i (6 * ℓ * r i)
          ContDiffOn ℝ ∞ η Ω ∧
          (IsClosed {z : Ω | η z = 0} ∧
            IsProperMap (fun z : {z : Ω | η z = 0} => (z : Ω))) ∧
          (∀ z ∈ ⋃ i ∈ I, ball i (6 * ℓ * r i),
            Module.finrank ℝ (Q z) = Module.finrank ℝ H - k) ∧
          let Z : Set H := {z | z ∈ Ω ∧ η z = 0}
          IsProperMap (fun z : Z => (⟨z.1, z.2.1⟩ : Ω)) ∧
          ∃ cs : ChartedSpace (Fin k → ℝ) Z,
            let _ := cs
            IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z ∧
            Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H) := by
  obtain ⟨δ₀, hδ₀, hprod⟩ := exists_uniform_cloud_local_submersion.{u} k C hC
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall hscale hcloud
  obtain ⟨I, hI, hIS, hdisj, hcover, hη, hproper, hrank, hlocal⟩ :=
    hprod H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall hscale hcloud
  refine ⟨I, hI, hIS, hdisj, hcover, hη, hproper, hrank, ?_⟩
  refine ⟨DifferentialGeometry.Topology.isProperMap_relativeZeroSetInclusion _ _
    hη.continuousOn, ?_⟩
  exact exists_buffered_normal_zero_set_manifold k I r P _ (by positivity)
    (fun i hi => hrmin.trans_le (hlower i (hIS hi)))
    (fun i hi => hdim i (hIS hi)) _ hη hlocal

end GC.MetricGeometry
