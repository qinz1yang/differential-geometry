import DifferentialGeometry.Geometry.Neck.SpatialFreshBand
import DifferentialGeometry.Topology.OpenPartialHomeomorph.CollarComponent

noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_spatial_neck_slab_return_of_compact_exterior
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I3 M) {eps : ℝ} (heps : eps ≤ 1 / 156000)
    (point : ℕ → M) (neck : ∀ n, SpatialNeck g eps (point n))
    (A : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞)
    (hsource : ∀ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (A n).source)
    (f : ℕ → Sphere 2 → ℝ) (hf : ∀ n q, |f n q| < 1 / 10)
    (κ μ : ℕ → Sphere 2 → Sphere 2)
    (hlower : ∀ n q, A n (q, 0) = (neck n).map (κ n q, f n (κ n q)))
    (hseam : ∀ n q, A (n + 1) (q, 0) = A n (μ n q, 1))
    (hband : ∀ n, (neck n).map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆
      A n '' (univ ×ˢ Icc (0 : ℝ) 1))
    (W : ℕ → Set M)
    (hW : ∀ n, W (n + 1) = W n ∪ A n '' (univ ×ˢ Icc (0 : ℝ) 1))
    {x : M} (hx : x ∈ (interior (W 0))ᶜ)
    (hstart : ∃ q, A 0 (q, 0) = x)
    (hcompact : IsCompact (connectedComponentIn (interior (W 0))ᶜ x)) :
    ∃ n : ℕ, ∃ y : M,
      y ∈ A n '' (univ ×ˢ Icc (0 : ℝ) 1) ∧ y ∈ W n ∧
        y ∉ A n '' (univ ×ˢ ({0} : Set ℝ)) := by
  classical
  by_contra hreturn
  have hinter (n : ℕ) :
      (A n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩ W n ⊆ A n '' (univ ×ˢ ({0} : Set ℝ)) := by
    intro y hy
    by_contra hyface
    exact hreturn ⟨n, y, hy.1, hy.2, hyface⟩
  have hmono : Monotone W := monotone_nat_of_le_succ (fun n => by
    rw [hW n]
    exact subset_union_left)
  let C := connectedComponentIn (interior (W 0))ᶜ x
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hcontained (n : ℕ) : A n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ C := by
    induction n with
    | zero =>
      apply (A 0).toOpenPartialHomeomorph.image_closed_slab_subset_connectedComponentIn_closed_exterior
        (by norm_num : (0 : ℝ) < 1) (hsource 0) Subset.rfl (hinter 0)
      obtain ⟨q, hq⟩ := hstart
      exact ⟨x, ⟨(q, 0), ⟨mem_univ _, rfl⟩, hq⟩, mem_connectedComponentIn hx⟩
    | succ n ih =>
      apply (A (n + 1)).toOpenPartialHomeomorph.image_closed_slab_subset_connectedComponentIn_closed_exterior
        (by norm_num : (0 : ℝ) < 1) (hsource (n + 1))
        (hmono (Nat.zero_le _)) (hinter (n + 1))
      let q := (neck (n + 1)).center
      refine ⟨A (n + 1) (q, 0), ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩, ?_⟩
      rw [hseam]
      exact ih ⟨(μ n q, 1), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hmidpoint (n : ℕ) : (neck n).map ((neck n).center, 3 / 2) ∈ C :=
    hcontained n (hband n ⟨((neck n).center, 3 / 2), ⟨mem_univ _, by norm_num⟩, rfl⟩)
  obtain ⟨n, hn⟩ := exists_spatial_neck_midpoint_mem_of_monotone g hcompact heps
    point neck hmidpoint W hmono (fun n y hy => by
      rw [hW n]
      exact Or.inr (hband n hy))
  have hmidband : (neck n).map ((neck n).center, 3 / 2) ∈
      A n '' (univ ×ˢ Icc (0 : ℝ) 1) :=
    hband n ⟨((neck n).center, 3 / 2), ⟨mem_univ _, by norm_num⟩, rfl⟩
  obtain ⟨⟨q, t⟩, ht, heq⟩ := hinter n ⟨hmidband, hn⟩
  have ht0 : t = 0 := ht.2
  subst t
  rw [hlower] at heq
  have hlen : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) (neck n).eps_pos).mpr
      (by linarith [(neck n).eps_small])
  have hqmem : (κ n q, f n (κ n q)) ∈ (neck n).map.source :=
    (neck n).domain ⟨mem_univ _, by constructor <;>
      linarith [(abs_lt.mp (hf n (κ n q))).1, (abs_lt.mp (hf n (κ n q))).2]⟩
  have hmidmem : ((neck n).center, (3 / 2 : ℝ)) ∈ (neck n).map.source :=
    (neck n).domain ⟨mem_univ _, by constructor <;> linarith⟩
  have hheight := congrArg Prod.snd ((neck n).map.injOn hqmem hmidmem heq)
  linarith [(abs_lt.mp (hf n (κ n q))).2]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
