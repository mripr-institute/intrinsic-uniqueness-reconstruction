import SigmaArithmeticDivisors

namespace Sigma
noncomputable section
open scoped BigOperators

/-- The finite Cartesian product of the exponent intervals on the prime support. -/
def FactorBox (s : Multiset Nat.Primes) :=
  ∀ p : s.toFinset, Fin (s.count p.val+1)

def factorsFromBox (s : Multiset Nat.Primes) (v : FactorBox s) : Multiset Nat.Primes :=
  ∑ p : s.toFinset, Multiset.replicate (v p).val p.val

theorem count_factors_from_box (s : Multiset Nat.Primes) (v : FactorBox s)
    (p : s.toFinset) : (factorsFromBox s v).count p.val = (v p).val := by
  unfold factorsFromBox
  rw [Multiset.count_sum']
  calc
    _ = (Multiset.replicate (v p).val p.val).count p.val := by
      apply Finset.sum_eq_single p
      · intro q _ hq
        have hne : q.val ≠ p.val := fun h => hq (Subtype.ext h)
        simp [Multiset.count_replicate, hne]
      · simp
    _ = _ := by simp

theorem count_factors_from_box_outside (s : Multiset Nat.Primes) (v : FactorBox s)
    (p : Nat.Primes) (hp : p ∉ s.toFinset) : (factorsFromBox s v).count p=0 := by
  unfold factorsFromBox
  rw [Multiset.count_sum']
  apply Finset.sum_eq_zero
  intro q _
  have hne : p ≠ q.val := fun h => hp (h ▸ q.property)
  simp [Multiset.count_replicate, Ne.symm hne]

theorem factors_from_box_le (s : Multiset Nat.Primes) (v : FactorBox s) :
    factorsFromBox s v ≤ s := by
  apply Multiset.le_iff_count.mpr
  intro p
  by_cases hp : p ∈ s.toFinset
  · rw [count_factors_from_box s v ⟨p,hp⟩]
    exact Nat.le_of_lt_succ (v ⟨p,hp⟩).isLt
  · rw [count_factors_from_box_outside s v p hp]
    exact Nat.zero_le _

/-- This is an actual exponent-coordinate inverse, not only equality of cardinalities. -/
def factorBoxEquiv (s : Multiset Nat.Primes) :
    {t : Multiset Nat.Primes // t ≤ s} ≃ FactorBox s where
  toFun t p := ⟨t.val.count p.val,
    Nat.lt_succ_of_le ((Multiset.le_iff_count.mp t.property) p.val)⟩
  invFun v := ⟨factorsFromBox s v,factors_from_box_le s v⟩
  left_inv t := by
    apply Subtype.ext
    apply Multiset.ext.mpr
    intro p
    by_cases hp : p ∈ s.toFinset
    · exact count_factors_from_box s _ ⟨p,hp⟩
    · rw [count_factors_from_box_outside s _ p hp]
      have hs : s.count p=0 := Multiset.count_eq_zero.mpr (by simpa using hp)
      have ht := (Multiset.le_iff_count.mp t.property) p
      omega
  right_inv v := by
    funext p
    exact Fin.ext (count_factors_from_box s v p)

theorem factor_box_order (s : Multiset Nat.Primes)
    (a b : {t : Multiset Nat.Primes // t ≤ s}) :
    a.val ≤ b.val ↔ ∀ p, factorBoxEquiv s a p ≤ factorBoxEquiv s b p := by
  constructor
  · intro h p
    exact (Multiset.le_iff_count.mp h) p.val
  · intro h
    apply Multiset.le_iff_count.mpr
    intro p
    by_cases hp : p ∈ s.toFinset
    · exact h ⟨p,hp⟩
    · have hs : s.count p=0 := Multiset.count_eq_zero.mpr (by simpa using hp)
      have ha := (Multiset.le_iff_count.mp a.property) p
      omega

section
variable {M : Type*} [CommMonoid M] (E : ℕ+ ≃* M)

def labelledDivisorBoxEquiv (x : M) :
    {d : M // d ∣ x} ≃ FactorBox (labelledFactors E x) :=
  (labelledDivisorEquiv E x).trans (factorBoxEquiv (labelledFactors E x))

theorem labelled_divisor_box_coordinate (x : M) (d : {d : M // d ∣ x})
    (p : (labelledFactors E x).toFinset) :
    (labelledDivisorBoxEquiv E x d p).val=labelledValuation E p.val d.val := rfl

theorem labelled_divisor_box_order (x : M) (a b : {d : M // d ∣ x}) :
    a.val ∣ b.val ↔ ∀ p, labelledDivisorBoxEquiv E x a p ≤
      labelledDivisorBoxEquiv E x b p := by
  rw [labelled_divisor_order E x, factor_box_order]
  rfl

end
end
end Sigma
