import SigmaRealTreesProbability

namespace Sigma
noncomputable section
open MeasureTheory
open scoped BigOperators

/-- A finite rooted tree whose vertex labels increase along every edge away from the root.
The strictly decreasing parent label proves that every nonroot vertex reaches vertex zero. -/
structure IncreasingRootedTree where
  order : ℕ
  positive : 0 < order
  parent : Fin order → Fin order
  root_parent : parent ⟨0, positive⟩ = ⟨0, positive⟩
  parent_decreases : ∀ i, i.val ≠ 0 → (parent i).val < i.val


theorem IncreasingRootedTree.every_vertex_reaches_root (T : IncreasingRootedTree)
    (i : Fin T.order) : ∃ k : ℕ, T.parent^[k] i = ⟨0, T.positive⟩ := by
  have h : ∀ n : ℕ, ∀ j : Fin T.order, j.val = n →
      ∃ k : ℕ, T.parent^[k] j = ⟨0, T.positive⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      by_cases hz : j.val = 0
      · refine ⟨0,?_⟩
        apply Fin.ext
        exact hz
      · have hlt : (T.parent j).val < n := hj ▸ T.parent_decreases j hz
        obtain ⟨k,hk⟩ := ih (T.parent j).val hlt (T.parent j) rfl
        refine ⟨k+1,?_⟩
        simpa only [Function.iterate_succ_apply] using hk
  exact h i.val i rfl

def rootedPath (n : ℕ) : IncreasingRootedTree where
  order := n + 1
  positive := Nat.succ_pos n
  parent i := ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  root_parent := by apply Fin.ext; simp
  parent_decreases i hi := Nat.sub_lt (Nat.pos_of_ne_zero hi) (by norm_num)

def rootedStar (n : ℕ) : IncreasingRootedTree where
  order := n + 1
  positive := Nat.succ_pos n
  parent _ := ⟨0, Nat.succ_pos n⟩
  root_parent := rfl
  parent_decreases _ hi := Nat.pos_of_ne_zero hi

def IncreasingRootedTree.rootBranches (T : IncreasingRootedTree) : Prop :=
  ∃ i j : Fin T.order, i.val ≠ 0 ∧ j.val ≠ 0 ∧ i ≠ j ∧
    (T.parent i).val = 0 ∧ (T.parent j).val = 0

theorem rooted_path_does_not_branch (n : ℕ) : ¬ (rootedPath n).rootBranches := by
  rintro ⟨i,j,hi,hj,hij,hpi,hpj⟩
  change i.val - 1 = 0 at hpi
  change j.val - 1 = 0 at hpj
  apply hij
  apply Fin.ext
  omega

theorem rooted_star_three_branches : (rootedStar 2).rootBranches := by
  refine ⟨⟨1,by norm_num [rootedStar]⟩,⟨2,by norm_num [rootedStar]⟩,?_,?_,?_,rfl,rfl⟩
  · norm_num
  · norm_num
  · intro he
    have hv := congrArg Fin.val he
    norm_num at hv

/-- The number of nonroot vertices of a Borel-distributed positive total size. -/
def positiveBorelIndexPMF : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (borelCoefficient (n + 1)), by
    apply ENNReal.summable.hasSum_iff.mpr
    have h := borel_coefficients_summable.hasSum
    rw [← hasSum_nat_add_iff' 1] at h
    simp only [Finset.sum_range_one, borel_coefficient_zero, sub_zero,
      borel_coefficients_sum_one] at h
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => borel_coefficient_nonnegative (n + 1))
      h.summable, h.tsum_eq, ENNReal.ofReal_one]⟩

theorem positive_borel_index_apply (n : ℕ) :
    positiveBorelIndexPMF n = ENNReal.ofReal (borelCoefficient (n + 1)) := rfl

theorem positive_borel_index_size : positiveBorelIndexPMF.map (fun n => n + 1) = borelPMF := by
  apply PMF.ext
  intro n
  cases n with
  | zero => simp [PMF.map_apply, borel_pmf_apply, borel_coefficient_zero]
  | succ n =>
    rw [PMF.map_apply]
    have he (a : ℕ) : n + 1 = a + 1 ↔ n = a := by omega
    simp only [he]
    rw [tsum_eq_single n]
    · simp [positive_borel_index_apply, borel_pmf_apply]
    · intro a ha
      simp [Ne.symm ha]

def borelPathLaw : PMF IncreasingRootedTree := positiveBorelIndexPMF.map rootedPath

def borelStarLaw : PMF IncreasingRootedTree := positiveBorelIndexPMF.map rootedStar

theorem borel_path_size_law : borelPathLaw.map IncreasingRootedTree.order = borelPMF := by
  rw [borelPathLaw, PMF.map_comp]
  exact positive_borel_index_size

theorem borel_star_size_law : borelStarLaw.map IncreasingRootedTree.order = borelPMF := by
  rw [borelStarLaw, PMF.map_comp]
  exact positive_borel_index_size

theorem borel_tree_laws_distinct : borelPathLaw ≠ borelStarLaw := by
  intro he
  have hs : rootedStar 2 ∈ borelStarLaw.support := by
    rw [borelStarLaw, PMF.support_map]
    refine ⟨2,?_,rfl⟩
    rw [PMF.mem_support_iff, positive_borel_index_apply]
    exact (ENNReal.ofReal_pos.mpr (borel_coefficient_positive 2)).ne'
  rw [← he, borelPathLaw, PMF.support_map] at hs
  rcases hs with ⟨n,_,hn⟩
  have hb := rooted_star_three_branches
  rw [← hn] at hb
  exact rooted_path_does_not_branch n hb

/-- Equal complete Borel total-size laws do not determine a random finite rooted tree. -/
theorem borel_size_does_not_identify_random_tree :
    ∃ μ ν : PMF IncreasingRootedTree,
      μ.map IncreasingRootedTree.order = borelPMF ∧
      ν.map IncreasingRootedTree.order = borelPMF ∧ μ ≠ ν :=
  ⟨borelPathLaw, borelStarLaw, borel_path_size_law, borel_star_size_law, borel_tree_laws_distinct⟩

end
end Sigma
