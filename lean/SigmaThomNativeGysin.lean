import SigmaThomNativeNaturality
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
Collapse and Gysin consequences of the supplied Thom context in F4. The only
compatibility assumed for the collapse maps is naturality of the Chern
character on relative classes. The pushforward comparison is derived.
-/

namespace Sigma
noncomputable section

variable {K H KR HR KY HY : Type*}
  [CommRing K] [CommRing H] [AddCommGroup KR] [AddCommGroup HR]
  [Module K KR] [Module H HR] [AddCommGroup KY] [AddCommGroup HY]

/-- Supplied compatible collapse maps, including relative or compactly
supported target groups. No pushforward comparison is a field. -/
structure NativeThomCollapse (T : NativeThomContext K H KR HR) where
  kCollapse : KR →+ KY
  hCollapse : HR →+ HY
  chTarget : KY →+ HY
  naturality : ∀ u, chTarget (kCollapse u) = hCollapse (T.chRelative u)

namespace NativeThomCollapse
variable {T : NativeThomContext K H KR HR} (C : NativeThomCollapse (KY := KY) (HY := HY) T)

/-- K-theoretic pushforward constructed by Thom then collapse. -/
def kGysin : K →+ KY := C.kCollapse.comp T.kThom.toAddMonoidHom

/-- Cohomological pushforward constructed using the same collapse. -/
def hGysin : H →+ HY := C.hCollapse.comp T.hThom.toAddMonoidHom

/-- Applying collapse to the proved Thom comparison yields the pushforward
identity on every input class. -/
theorem comparison (a : K) :
    C.chTarget (C.kGysin a) = C.hGysin (T.chBase a * T.correction) := by
  change C.chTarget (C.kCollapse (T.kThom a)) =
    C.hCollapse (T.hThom (T.chBase a * T.correction))
  rw [C.naturality, T.ch_thom]

/-- The normal-bundle form after the independently identified Thom correction
has been expressed as the inverse Todd class. -/
theorem normal_riemann_roch (tdNormal : Hˣ)
    (hNormal : T.correction = (↑tdNormal⁻¹ : H)) (a : K) :
    C.chTarget (C.kGysin a) = C.hGysin (T.chBase a * (↑tdNormal⁻¹ : H)) := by
  rw [C.comparison, hNormal]

/-- The supplied class of virtual bundles is additive, while a multiplicative
characteristic class takes values in units. Negating a virtual bundle therefore
inverts its Todd class; this sign conversion is proved by the group laws. -/
theorem virtual_tangent_riemann_roch {G : Type*} [AddCommGroup G]
    (td : Multiplicative G →* Hˣ) (normal tangent : G)
    (hTangent : tangent = -normal)
    (hNormal : T.correction = (↑(td (Multiplicative.ofAdd normal))⁻¹ : H))
    (a : K) :
    C.chTarget (C.kGysin a) =
      C.hGysin (T.chBase a * (↑(td (Multiplicative.ofAdd tangent)) : H)) := by
  rw [C.comparison, hNormal, hTangent]
  have hn : td (Multiplicative.ofAdd (-normal)) =
      (td (Multiplicative.ofAdd normal))⁻¹ := map_inv td _
  rw [hn]

/-- Stable factorization adds a trivial bundle to the negative normal bundle.
Its Todd class is one, so the stable tangent correction follows from the
homomorphism laws, with no Riemann--Roch equation as an input. -/
theorem stable_tangent_riemann_roch {G : Type*} [AddCommGroup G]
    (td : Multiplicative G →* Hˣ) (normal stable tangent : G)
    (hTangent : tangent = stable - normal)
    (hStable : td (Multiplicative.ofAdd stable) = 1)
    (hNormal : T.correction = (↑(td (Multiplicative.ofAdd normal))⁻¹ : H))
    (a : K) :
    C.chTarget (C.kGysin a) =
      C.hGysin (T.chBase a * (↑(td (Multiplicative.ofAdd tangent)) : H)) := by
  rw [C.comparison, hNormal, hTangent]
  have ht : td (Multiplicative.ofAdd (stable - normal)) =
      (td (Multiplicative.ofAdd normal))⁻¹ := by
    change td (Multiplicative.ofAdd stable / Multiplicative.ofAdd normal) = _
    rw [map_div, hStable, one_div]
  rw [ht]

end NativeThomCollapse

section NativeComposition
variable {K' H' KR' HR' KZ HZ : Type*}
  [CommRing K'] [CommRing H'] [AddCommGroup KR'] [AddCommGroup HR']
  [Module K' KR'] [Module H' HR'] [AddCommGroup KZ] [AddCommGroup HZ]

/-- Two supplied Thom-collapse factorizations satisfy the composite comparison
by their native Thom comparisons and the cohomological projection formula.
Neither individual RR identity needs to be supplied by the caller. -/
theorem native_thom_collapse_composition
    (T : NativeThomContext K H KR HR) (U : NativeThomContext K' H' KR' HR')
    (C : NativeThomCollapse (KY := K') (HY := H') T)
    (D : NativeThomCollapse (KY := KZ) (HY := HZ) U)
    (hch : C.chTarget = U.chBase.toAddMonoidHom)
    (pull : H' →+* H)
    (hProjection : ∀ x y, C.hGysin (x * pull y) = C.hGysin x * y) (a : K) :
    D.chTarget (D.kGysin (C.kGysin a)) =
      D.hGysin (C.hGysin (T.chBase a * (T.correction * pull U.correction))) := by
  rw [D.comparison]
  have hf : U.chBase (C.kGysin a) = C.hGysin (T.chBase a * T.correction) := by
    have hc := C.comparison a
    rw [hch] at hc
    exact hc
  rw [hf, ← hProjection, mul_assoc]

end NativeComposition

section Composition
variable {KX HX KZ HZ : Type*}
  [CommRing KX] [CommRing HX] [CommRing KZ] [CommRing HZ]
  [CommRing KY] [CommRing HY]

/-- The composition step in Riemann--Roch. The hypotheses are the already
proved comparisons for the two factors and the ordinary cohomological
projection formula. There is no assumption of the conclusion for the composite.
This lemma is used inductively for the supplied stable factorization. -/
theorem native_gysin_composition
    (chX : KX →+* HX) (chY : KY →+* HY) (chZ : KZ →+* HZ)
    (fK : KX →+ KY) (gK : KY →+ KZ) (fH : HX →+ HY) (gH : HY →+ HZ)
    (pull : HY →+* HX) (tdF : HX) (tdG : HY)
    (hProjection : ∀ x y, fH (x * pull y) = fH x * y)
    (hf : ∀ a, chY (fK a) = fH (chX a * tdF))
    (hg : ∀ b, chZ (gK b) = gH (chY b * tdG)) (a : KX) :
    chZ ((gK.comp fK) a) =
      (gH.comp fH) (chX a * (tdF * pull tdG)) := by
  simp only [AddMonoidHom.comp_apply]
  rw [hg, hf, ← hProjection, mul_assoc]

end Composition
end
end Sigma
