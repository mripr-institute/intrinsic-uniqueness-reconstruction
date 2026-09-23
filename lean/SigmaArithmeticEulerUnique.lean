import SigmaArithmeticEulerRecovery
import SigmaArithmeticEulerErase
import Mathlib.Data.Set.Card

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology BigOperators

/-- Exactly the input category of B4: numerical generators above one, positive
integer multiplicities, and a positive convergent Euler product on a terminal
ray. Countability, local finiteness and reconstruction are not fields. -/
structure RealEulerPresentation where
  generators : Set ℝ
  multiplicity : generators → ℕ
  product : ℝ → ℝ
  above_one : ∀ q ∈ generators, 1 < q
  positive_multiplicity : ∀ q, 0 < multiplicity q
  convergence : ∃ S : ℝ, ∀ s, S ≤ s → 0 < product s ∧
    HasProd (fun q : generators => realEulerFactor q (multiplicity q) s) (product s)

namespace RealEulerPresentation

open scoped Classical in
def multiplicityAt (P : RealEulerPresentation) (x : ℝ) : ℕ :=
  if hx : x ∈ P.generators then P.multiplicity ⟨x, hx⟩ else 0

theorem eventually_product (P : RealEulerPresentation) :
    ∀ᶠ s : ℝ in atTop, 0 < s ∧ 0 < P.product s ∧
      HasProd (fun q : P.generators => realEulerFactor q (P.multiplicity q) s) (P.product s) := by
  obtain ⟨S, hS⟩ := P.convergence
  filter_upwards [eventually_ge_atTop (max S 1)] with s hs
  exact ⟨lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hs),
    hS s ((le_max_left _ _).trans hs)⟩

theorem finite_below (P : RealEulerPresentation) (x : ℝ) : (P.generators ∩ Iic x).Finite := by
  obtain ⟨s, hs, hpos, hprod⟩ := P.eventually_product.exists
  exact real_euler_generators_bounded_finite P.above_one P.positive_multiplicity hs hpos hprod x

theorem nonempty_of_same_tail (P R : RealEulerPresentation)
    (h : ∀ᶠ s : ℝ in atTop, P.product s = R.product s)
    (hP : P.generators.Nonempty) : R.generators.Nonempty := by
  by_contra hn
  have he : R.generators = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  obtain ⟨s, hsP, hsR, hs⟩ := (P.eventually_product.and (R.eventually_product.and h)).exists
  have hp := real_euler_product_gt_one P.above_one P.positive_multiplicity
    hsP.1 hsP.2.1 hsP.2.2 hP
  have hr := (real_euler_product_eq_one_iff_empty R.above_one R.positive_multiplicity
    hsR.1 hsR.2.1 hsR.2.2).mpr he
  linarith

/-- The same terminal-ray function determines the same first generator and
its entire integer multiplicity in any two presentations. -/
theorem same_tail_least (P R : RealEulerPresentation)
    (h : ∀ᶠ s : ℝ in atTop, P.product s = R.product s)
    (hP : P.generators.Nonempty) :
    ∃ a : P.generators, ∃ b : R.generators,
      (∀ q : P.generators, (a : ℝ) ≤ q) ∧
      (∀ q : R.generators, (b : ℝ) ≤ q) ∧
      (a : ℝ) = b ∧ P.multiplicity a = R.multiplicity b := by
  obtain ⟨a, ha, hla, hma⟩ := real_euler_multiset_recovery_limits
    P.above_one P.positive_multiplicity hP P.convergence
  obtain ⟨b, hb, hlb, hmb⟩ := real_euler_multiset_recovery_limits
    R.above_one R.positive_multiplicity (P.nonempty_of_same_tail R h hP) R.convergence
  have hab : (a : ℝ) = b := tendsto_nhds_unique
    (hla.congr' (h.mono fun s hs => by rw [hs])) hlb
  have hm : (P.multiplicity a : ℝ) = R.multiplicity b := tendsto_nhds_unique
    (hma.congr' (h.mono fun s hs => by rw [hs, hab])) hmb
  exact ⟨a, b, ha, hb, hab, Nat.cast_injective hm⟩

/-- The remaining presentation uses the same numerical generators and weights,
with just the specified entire factor deleted. Its convergence is proved. -/
def erase (P : RealEulerPresentation) (a : P.generators) : RealEulerPresentation where
  generators := P.generators \ {(a : ℝ)}
  multiplicity := realEulerEraseMultiplicity P.multiplicity a
  product := fun s => P.product s / realEulerFactor a (P.multiplicity a) s
  above_one := fun q hq => P.above_one q hq.1
  positive_multiplicity := real_euler_erase_multiplicity_pos P.positive_multiplicity a
  convergence := real_euler_remove_generator_terminal_convergence P.above_one P.convergence a

theorem erase_multiplicityAt (P : RealEulerPresentation) (a : P.generators) (x : ℝ)
    (hx : x ≠ (a : ℝ)) : (P.erase a).multiplicityAt x = P.multiplicityAt x := by
  classical
  by_cases hmem : x ∈ P.generators
  · simp [multiplicityAt, erase, realEulerEraseMultiplicity, hmem, hx]
  · simp [multiplicityAt, erase, hmem]

theorem multiplicityAt_of_mem (P : RealEulerPresentation) (a : P.generators) :
    P.multiplicityAt a = P.multiplicity a := by
  simp [multiplicityAt, a.property]

theorem multiplicityAt_eq_zero (P : RealEulerPresentation) (x : ℝ) (hx : x ∉ P.generators) :
    P.multiplicityAt x = 0 := by simp [multiplicityAt, hx]

/-- Full numerical multiset uniqueness, not merely uniqueness of the smallest
factor. Induction counts only the finitely many original generators below the
tested value; deleting common least factors therefore reaches every value. -/
theorem multiplicityAt_eq_of_same_tail (P R : RealEulerPresentation)
    (h : ∀ᶠ s : ℝ in atTop, P.product s = R.product s) (x : ℝ) :
    P.multiplicityAt x = R.multiplicityAt x := by
  classical
  have aux : ∀ N : ℕ, ∀ P R : RealEulerPresentation,
      (∀ᶠ s : ℝ in atTop, P.product s = R.product s) →
      (P.generators ∩ Iic x).ncard = N → P.multiplicityAt x = R.multiplicityAt x := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro P R htail hcard
      by_cases hP : P.generators.Nonempty
      · obtain ⟨a,b,ha,hb,hab,hm⟩ := P.same_tail_least R htail hP
        by_cases hax : (a : ℝ) ≤ x
        · by_cases heq : x = (a : ℝ)
          · subst x
            rw [P.multiplicityAt_of_mem a, hab, R.multiplicityAt_of_mem b, hm]
          · have hcard' : ((P.erase a).generators ∩ Iic x).ncard < N := by
              rw [← hcard]
              exact real_euler_erase_bounded_ncard_lt a.property hax (P.finite_below x)
            have htail' : ∀ᶠ s : ℝ in atTop, (P.erase a).product s = (R.erase b).product s := by
              filter_upwards [htail] with s hs
              change P.product s / realEulerFactor a (P.multiplicity a) s =
                R.product s / realEulerFactor b (R.multiplicity b) s
              rw [hs, hab, hm]
            have hh := ih _ hcard' (P.erase a) (R.erase b) htail' rfl
            rw [P.erase_multiplicityAt a x heq,
              R.erase_multiplicityAt b x (by rwa [← hab])] at hh
            exact hh
        · have hp : x ∉ P.generators := by
            intro hx
            exact hax (ha ⟨x, hx⟩)
          have hr : x ∉ R.generators := by
            intro hx
            apply hax
            rw [hab]
            exact hb ⟨x,hx⟩
          rw [P.multiplicityAt_eq_zero x hp, R.multiplicityAt_eq_zero x hr]
      · have hnR : ¬ R.generators.Nonempty := fun hR =>
          hP (R.nonempty_of_same_tail P (htail.mono fun _ hs => hs.symm) hR)
        have hxP : x ∉ P.generators := fun hx => hP ⟨x,hx⟩
        have hxR : x ∉ R.generators := fun hx => hnR ⟨x,hx⟩
        rw [P.multiplicityAt_eq_zero x hxP, R.multiplicityAt_eq_zero x hxR]
  exact aux _ P R h rfl

theorem generators_eq_of_same_tail (P R : RealEulerPresentation)
    (h : ∀ᶠ s : ℝ in atTop, P.product s = R.product s) : P.generators = R.generators := by
  classical
  ext x
  have he := P.multiplicityAt_eq_of_same_tail R h x
  by_cases hp : x ∈ P.generators <;> by_cases hr : x ∈ R.generators
  · simp [hp, hr]
  · simp only [multiplicityAt, dif_pos hp, dif_neg hr] at he
    exact False.elim ((ne_of_gt (P.positive_multiplicity ⟨x,hp⟩)) he)
  · simp only [multiplicityAt, dif_neg hp, dif_pos hr] at he
    exact False.elim ((ne_of_gt (R.positive_multiplicity ⟨x,hr⟩)) he.symm)
  · simp [hp, hr]

end RealEulerPresentation

open scoped Classical in
/-- Reconstruct the numerical multiplicity function from terminal-ray product
data. The choice is among raw convergent presentations; uniqueness is proved
above, so no recovered generator or multiplicity is an input assumption. -/
def realEulerReconstruction (Z : ℝ → ℝ) : ℝ → ℕ :=
  if h : ∃ P : RealEulerPresentation, ∀ᶠ s : ℝ in atTop, P.product s = Z s then
    (Classical.choose h).multiplicityAt
  else fun _ => 0

theorem real_euler_reconstruction_left_inverse (P : RealEulerPresentation)
    (Z : ℝ → ℝ) (hZ : ∀ᶠ s : ℝ in atTop, P.product s = Z s) :
    realEulerReconstruction Z = P.multiplicityAt := by
  classical
  have hex : ∃ R : RealEulerPresentation, ∀ᶠ s : ℝ in atTop, R.product s = Z s := ⟨P,hZ⟩
  rw [realEulerReconstruction, dif_pos hex]
  funext x
  apply RealEulerPresentation.multiplicityAt_eq_of_same_tail
  filter_upwards [Classical.choose_spec hex, hZ] with s hs ht
  exact hs.trans ht.symm

theorem real_euler_reconstruction_generators (P : RealEulerPresentation)
    (Z : ℝ → ℝ) (hZ : ∀ᶠ s : ℝ in atTop, P.product s = Z s) :
    {q : ℝ | 0 < realEulerReconstruction Z q} = P.generators := by
  classical
  rw [real_euler_reconstruction_left_inverse P Z hZ]
  ext q
  by_cases hq : q ∈ P.generators
  · simp [RealEulerPresentation.multiplicityAt, hq, P.positive_multiplicity ⟨q,hq⟩]
  · simp [RealEulerPresentation.multiplicityAt, hq]

end
end Sigma
