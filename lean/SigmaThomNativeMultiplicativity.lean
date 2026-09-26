import SigmaThomNativeNaturality
import Mathlib.LinearAlgebra.Multilinear.Basic

namespace Sigma
noncomputable section
open scoped BigOperators

variable {ι K H KR HR : Type*} [Fintype ι] [CommRing K] [CommRing H]
  {Ks Hs : ι → Type*} [AddCommGroup KR] [AddCommGroup HR]
  [∀ i, AddCommGroup (Ks i)] [∀ i, AddCommGroup (Hs i)]
  [Module K KR] [Module H HR] [∀ i, Module K (Ks i)] [∀ i, Module H (Hs i)]

/-- Supplied multiplicative Thom classes and multiplicative Chern character
for a finite direct-sum decomposition. The cup products are native multilinear
maps, so their scalar product law is proved rather than postulated. -/
structure NativeThomProduct (T : NativeThomContext K H KR HR)
    (S : ∀ i, NativeThomContext K H (Ks i) (Hs i)) where
  kCup : MultilinearMap K Ks KR
  hCup : MultilinearMap H Hs HR
  kClass : kCup (fun i => (S i).kClass) = T.kClass
  hClass : hCup (fun i => (S i).hClass) = T.hClass
  ch : ∀ u, T.chRelative (kCup u) = hCup (fun i => (S i).chRelative (u i))

namespace NativeThomProduct
variable {T : NativeThomContext K H KR HR} {S : ∀ i, NativeThomContext K H (Ks i) (Hs i)}

/-- The product formula follows from primitive Thom multiplicativity and
Chern character, with uniqueness supplied by the target Thom isomorphism. -/
theorem correction_product (P : NativeThomProduct T S) :
    T.correction = ∏ i, (S i).correction := by
  symm
  apply T.correction_unique
  rw [← P.kClass, P.ch]
  simp_rw [NativeThomContext.correction_comparison]
  rw [P.hCup.map_smul_univ, P.hClass]

end NativeThomProduct
end
end Sigma
